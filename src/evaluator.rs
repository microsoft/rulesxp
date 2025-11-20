use crate::Error;
use crate::MAX_EVAL_DEPTH;
use crate::ast::Value;
use crate::builtinops::{Arity, get_builtin_ops};
use crate::intooperation::{IntoOperation, IntoVariadicOperation, OperationFn};
use std::collections::HashMap;
use std::sync::Arc;

/// Environment for variable bindings
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Environment {
    bindings: HashMap<String, Value>,
    parent: Option<Box<Environment>>,
}

impl Environment {
    pub(crate) fn new() -> Self {
        Environment {
            bindings: HashMap::new(),
            parent: None,
        }
    }

    pub(crate) fn with_parent(parent: Environment) -> Self {
        Environment {
            bindings: HashMap::new(),
            parent: Some(Box::new(parent)),
        }
    }

    pub(crate) fn define(&mut self, name: String, value: Value) {
        self.bindings.insert(name, value);
    }

    pub(crate) fn get(&self, name: &str) -> Option<&Value> {
        self.bindings
            .get(name)
            .or_else(|| self.parent.as_ref().and_then(|parent| parent.get(name)))
    }

    /// Register a custom builtin function in the environment for use by Scheme/JSONLogic.
    ///
    /// This is the low-level API: it accepts a function that already
    /// works on `&[Value]` and returns `Result<Value, Error>`. Internally
    /// it is wired through the same machinery as
    /// [`Environment::register_builtin_operation`]. For most new code,
    /// prefer the typed API instead of manipulating `Value` directly.
    ///
    /// # Arguments
    /// * `name` - The name by which the function can be called
    /// * `func` - A function pointer that takes a slice of `Value` and returns a `Result`
    ///
    /// # Example
    /// ```
    /// use rulesxp::evaluator::{Environment, create_global_env};
    /// use rulesxp::ast::Value;
    /// use rulesxp::Error;
    ///
    /// fn my_custom_function(args: &[Value]) -> Result<Value, Error> {
    ///     println!("Custom function called with {} args", args.len());
    ///     Ok(Value::Unspecified)
    /// }
    ///
    /// let mut env = create_global_env();
    /// env.register_builtin_function("my-func", my_custom_function);
    /// // Now (my-func) can be called from evaluated expressions
    /// ```
    pub fn register_builtin_function(
        &mut self,
        name: &str,
        func: fn(&[Value]) -> Result<Value, Error>,
    ) {
        // Wrap the raw slice-based function into the canonical
        // `OperationFn` so it can be stored directly as a
        // `BuiltinFunction`.
        let f = func;
        let wrapped: Arc<OperationFn> = Arc::new(move |args: Vec<Value>| f(&args));

        self.bindings.insert(
            name.to_string(),
            Value::BuiltinFunction {
                id: name.to_string(),
                func: wrapped,
            },
        );
    }

    /// Register a strongly-typed Rust function as a builtin operation using
    /// automatic argument extraction and result conversion.
    ///
    /// This allows writing natural Rust functions like:
    ///
    /// ```rust,ignore
    /// fn add(a: i64, b: i64) -> i64 { a + b }
    /// let mut env = rulesxp::evaluator::create_global_env();
    /// env.register_builtin_operation("add", add);
    /// // Now (+ 2 3) and (add 2 3) both work if + also registered
    /// ```
    ///
    /// Builtins can also return `Result<R, E>` where `E: Display`:
    ///
    /// ```rust,ignore
    /// use std::fmt::Display;
    ///
    /// fn safe_div(a: i64, b: i64) -> Result<i64, &'static str> {
    ///     if b == 0 {
    ///         Err("division by zero")
    ///     } else {
    ///         Ok(a / b)
    ///     }
    /// }
    ///
    /// let mut env = rulesxp::evaluator::create_global_env();
    /// env.register_builtin_operation("safe-div", safe_div);
    /// ```
    ///
    /// Supported parameter types (initial set):
    /// - `i64` (number)
    /// - `bool` (boolean)
    /// - `&str` (borrowed string slices)
    /// - `Value` (owned access to the raw AST value)
    /// - `ValueListIterator<'_>` (iterates over elements of a list argument as `&Value`)
    /// - `NumIterator<'_>` (iterates over numeric elements of a list argument)
    /// - `BoolIterator<'_>` (iterates over boolean elements of a list argument)
    /// - `StringIterator<'_>` (iterates over string elements of a list argument)
    ///
    /// Additional scalar parameter types can be supported by adding
    /// `impl TryInto<T, Error = Error> for Value` in `ast.rs`; those
    /// automatically participate via the blanket `FromParam` impl.
    ///
    /// More advanced list-style and variadic behaviour (e.g. rest
    /// parameters spanning multiple arguments) can be expressed using
    /// the iterator-based APIs described on
    /// [`Environment::register_variadic_builtin_operation`].
    ///
    /// Supported return types:
    /// - any type `R` where `R: Into<Value>` (for example `Value`,
    ///   `i64`, `bool`, `String`, and `&str`)
    /// - `Result<R, E>` where `R: Into<Value>` and `E: Display`
    ///
    /// If you need true rest-parameter / variadic behavior (functions
    /// that see all arguments via iterators over the argument tail),
    /// use [`Environment::register_variadic_builtin_operation`] instead.
    ///
    /// Arity is enforced automatically. Conversion errors yield `TypeError`,
    /// and any `E` from a `Result<R, E>` is converted to `Error::EvalError`.
    pub fn register_builtin_operation<F, Args, R>(&mut self, name: &str, func: F)
    where
        F: IntoOperation<Args, R> + 'static,
    {
        let wrapped = func.into_operation();
        self.bindings.insert(
            name.to_string(),
            Value::BuiltinFunction {
                id: name.to_string(),
                func: wrapped,
            },
        );
    }

    /// Register a variadic builtin operation with explicit arity metadata.
    ///
    /// This is intended for functions whose Rust signature includes a
    /// "rest" parameter, expressed using iterator types from the
    /// [`crate::intooperation`] module.
    ///
    /// Examples:
    /// - rest of all arguments as values: `fn(ValueListIterator<'_>) -> R`
    /// - numeric tail: `fn(NumIterator<'_>) -> R`
    /// - fixed prefix plus numeric tail: `fn(i64, NumIterator<'_>) -> R`
    ///
    /// Fixed-arity functions should use
    /// [`Environment::register_builtin_operation`] instead.
    ///
    /// The provided [`Arity`] is used to validate the total number of
    /// arguments at call time, since minimum/maximum argument counts for
    /// variadic operations are not always derivable from the Rust type
    /// signature alone.
    pub fn register_variadic_builtin_operation<F, Args, R>(
        &mut self,
        name: &str,
        arity: Arity,
        func: F,
    ) where
        F: IntoVariadicOperation<Args, R> + 'static,
    {
        let inner = func.into_variadic_operation();
        let arity_for_closure = arity;
        let wrapped = std::sync::Arc::new(move |args: Vec<Value>| {
            arity_for_closure.validate(args.len())?;
            inner(args)
        });

        self.bindings.insert(
            name.to_string(),
            Value::BuiltinFunction {
                id: name.to_string(),
                func: wrapped,
            },
        );
    }

    /// Get all bindings in this environment and its parents
    /// Returns a Vec of (name, value) pairs sorted by name
    pub fn get_all_bindings(&self) -> Vec<(String, Value)> {
        let mut bindings = HashMap::new();

        // Start with parent bindings (so they can be overridden by local bindings)
        if let Some(parent) = &self.parent {
            for (name, value) in parent.get_all_bindings() {
                bindings.insert(name, value);
            }
        }

        // Add/override with local bindings
        for (name, value) in &self.bindings {
            bindings.insert(name.clone(), value.clone());
        }

        // Convert to sorted vector
        let mut result: Vec<_> = bindings.into_iter().collect();
        result.sort_by(|a, b| a.0.cmp(&b.0));
        result
    }
}

/// Evaluate an S-expression (public API)
pub fn eval(expr: &Value, env: &mut Environment) -> Result<Value, Error> {
    eval_with_depth_tracking(expr, env, 0)
}

/// Evaluate an S-expression with depth tracking to prevent stack overflow
fn eval_with_depth_tracking(
    expr: &Value,
    env: &mut Environment,
    depth: usize,
) -> Result<Value, Error> {
    if depth >= MAX_EVAL_DEPTH {
        return Err(Error::EvalError(format!(
            "Evaluation depth limit exceeded (max: {MAX_EVAL_DEPTH})"
        )));
    }
    match expr {
        // Self-evaluating forms (empty lists are NOT self-evaluating for strict semantics)
        Value::Number(_)
        | Value::String(_)
        | Value::Bool(_)
        | Value::BuiltinFunction { .. }
        | Value::Function { .. }
        | Value::Unspecified => Ok(expr.clone()),

        // Variable lookup
        Value::Symbol(name) => env
            .get(name)
            .cloned()
            .ok_or_else(|| Error::UnboundVariable(name.clone())),

        // PrecompiledOp evaluation (optimized path for builtin operations and special forms)
        // This is where special forms are actually handled - they are converted to PrecompiledOps
        // during parsing since they are syntax structures, not dynamic function calls.
        // Note: Arity is already validated at parse time, so no runtime checking needed
        Value::PrecompiledOp { op, args, .. } => {
            use crate::builtinops::OpKind;
            match &op.op_kind {
                OpKind::Function(f) => {
                    // Evaluate all arguments using helper function with depth tracking
                    let evaluated_args = eval_args(args, env, depth)?;
                    // Apply the function (arity already validated at parse time)
                    f(&evaluated_args)
                }
                OpKind::SpecialForm(special_form) => {
                    // Special forms are syntax structures handled here after being converted
                    // to PrecompiledOps during parsing. They get unevaluated arguments.
                    // (arity already validated at parse time)
                    // Note: Special forms handle their own depth tracking via eval_with_depth_tracking calls
                    special_form(args, env, depth)
                }
            }
        }

        // List evaluation (function application or special forms)
        Value::List(elements) => {
            eval_list(elements, env, depth).map_err(|err| add_context(err, expr))
        }
    }
}

/// Helper function to add expression context to errors
fn add_context(error: Error, expr: &Value) -> Error {
    let context = format!("while evaluating: {expr}");
    match error {
        Error::EvalError(msg) => Error::EvalError(format!("{msg}\n  Context: {context}")),
        Error::TypeError(msg) => Error::TypeError(format!("{msg}\n  Context: {context}")),
        // Don't add context to parse errors, unbound variables, or arity errors (they have their own context)
        other => other,
    }
}

/// Helper function to evaluate a list of argument expressions with depth tracking
fn eval_args(args: &[Value], env: &mut Environment, depth: usize) -> Result<Vec<Value>, Error> {
    args.iter()
        .map(|arg| eval_with_depth_tracking(arg, env, depth + 1))
        .collect()
}

/// Evaluate a list expression (function application)
///
/// Note: Both builtin functions and special forms are converted to PrecompiledOps
/// during parsing for optimization. Special forms are syntax structures that cannot
/// be dynamically generated, while builtin functions benefit from pre-validation.
/// All PrecompiledOps are handled in the main eval() function. Therefore, eval_list()
/// only needs to handle dynamic function application cases.
///
/// If the PrecompiledOps optimization were removed, special forms would need
/// special handling here. Builtin functions are added to the environment and
/// can be called dynamically through normal symbol lookup and function application.
fn eval_list(elements: &[Value], env: &mut Environment, depth: usize) -> Result<Value, Error> {
    // Note: Dynamic calls (not PrecompiledOps) still need runtime arity checking
    match elements {
        [] => Err(Error::EvalError("Cannot evaluate empty list".to_owned())),

        // Function application: evaluate function expression, then apply to arguments
        // Note: If PrecompiledOps optimization were removed, we would need to check for
        // special forms here before function application (builtin functions work via symbol lookup)
        [func_expr, arg_exprs @ ..] => {
            // Evaluate the function with depth tracking
            let func = eval_with_depth_tracking(func_expr, env, depth + 1)?;

            // Evaluate the arguments with depth tracking
            let args = eval_args(arg_exprs, env, depth + 1)?;

            // Apply the function
            match &func {
                // Dynamic function calls
                Value::BuiltinFunction { func, .. } => func(args),
                Value::Function {
                    params,
                    body,
                    env: closure_env,
                } => {
                    if params.len() != args.len() {
                        return Err(Error::arity_error(params.len(), args.len()));
                    }

                    // Create new environment with closure environment as parent
                    let mut new_env = Environment::with_parent(closure_env.clone());

                    // Bind parameters to arguments
                    for (param, arg) in params.iter().zip(args.iter()) {
                        new_env.define(param.clone(), arg.clone());
                    }

                    // Evaluate body with depth tracking and context
                    eval_with_depth_tracking(body, &mut new_env, depth + 1).map_err(|err| match err
                    {
                        Error::EvalError(msg) => {
                            Error::EvalError(format!("{msg}\n  In lambda: {body}"))
                        }
                        Error::TypeError(msg) => {
                            Error::TypeError(format!("{msg}\n  In lambda: {body}"))
                        }
                        other => other,
                    })
                }
                _ => Err(Error::TypeError(format!(
                    "Cannot apply non-function: {func}"
                ))),
            }
        }
    }
}

/// Evaluate quote special form
pub(crate) fn eval_quote(
    args: &[Value],
    _env: &mut Environment,
    _depth: usize,
) -> Result<Value, Error> {
    match args {
        [expr] => Ok(expr.clone()), // Quote content is already unoptimized during parsing
        _ => Err(Error::arity_error(1, args.len())),
    }
}

/// Evaluate define special form
pub(crate) fn eval_define(
    args: &[Value],
    env: &mut Environment,
    depth: usize,
) -> Result<Value, Error> {
    match args {
        [Value::Symbol(name), expr] => {
            let value = eval_with_depth_tracking(expr, env, depth + 1)?;
            env.define(name.clone(), value);
            Ok(Value::Unspecified)
        }
        [_, _] => Err(Error::TypeError("define requires a symbol".to_owned())),
        _ => Err(Error::arity_error(2, args.len())),
    }
}

/// Evaluate if special form
pub(crate) fn eval_if(args: &[Value], env: &mut Environment, depth: usize) -> Result<Value, Error> {
    match args {
        [condition_expr, then_expr, else_expr] => {
            let condition = eval_with_depth_tracking(condition_expr, env, depth + 1)?;
            match condition {
                Value::Bool(true) => eval_with_depth_tracking(then_expr, env, depth + 1),
                Value::Bool(false) => eval_with_depth_tracking(else_expr, env, depth + 1),
                _ => Err(Error::TypeError(
                    "SCHEME-JSONLOGIC-STRICT: if condition must be a boolean".to_owned(),
                )),
            }
        }
        _ => Err(Error::arity_error(3, args.len())),
    }
}

/// Evaluate lambda special form
pub(crate) fn eval_lambda(
    args: &[Value],
    env: &mut Environment,
    _depth: usize,
) -> Result<Value, Error> {
    match args {
        [Value::List(param_list), body] => {
            let mut params = Vec::new();
            for param in param_list {
                match param {
                    Value::Symbol(name) => {
                        // Check for duplicate parameter names (R7RS compliant)
                        if params.contains(name) {
                            return Err(Error::EvalError(format!(
                                "Duplicate parameter name: {name}"
                            )));
                        }
                        params.push(name.clone());
                    }
                    _ => {
                        return Err(Error::TypeError(
                            "Lambda parameters must be symbols".to_owned(),
                        ));
                    }
                }
            }

            // SCHEME-STRICT: We do not support Scheme's variadic lambda forms:
            // - (lambda args body) - where args is a symbol that collects all arguments as a list
            // - (lambda (a b . rest) body) - where rest collects remaining arguments (dot notation)
            // Our implementation only supports fixed-arity lambdas with explicit parameter lists.

            Ok(Value::Function {
                params,
                body: Box::new(body.clone()),
                env: env.clone(),
            })
        }
        [_, _] => Err(Error::TypeError(
            "Lambda parameters must be a list".to_owned(),
        )),
        _ => Err(Error::arity_error(2, args.len())),
    }
}

/// Check if a value is obviously non-boolean (before evaluation)
/// This catches literals and some obvious cases, but can't check function call results
fn is_obviously_non_boolean(value: &Value) -> bool {
    match value {
        Value::Number(_) | Value::String(_) | Value::Unspecified => true, // Obviously non-boolean
        Value::Bool(_)
        | Value::List(_)
        | Value::PrecompiledOp { .. }
        | Value::Symbol(_)
        | Value::BuiltinFunction { .. }
        | Value::Function { .. } => false, // Boolean, or could be function calls/variables that return booleans
    }
}

macro_rules! boolean_logic_op {
    ($name:ident, $op_name:expr, $short_circuit:literal, $default:literal) => {
        pub(crate) fn $name(
            args: &[Value],
            env: &mut Environment,
            depth: usize,
        ) -> Result<Value, Error> {
            // SCHEME-STRICT: Require at least 1 argument (Scheme R7RS allows 0 args, returns #t)
            if args.is_empty() {
                return Err(Error::arity_error(1, 0));
            }

            // First pass: check for obviously non-boolean arguments before evaluation, so that short-circuit evaluation doesn't hide gross errors
            for arg in args.iter() {
                if is_obviously_non_boolean(arg) {
                    return Err(Error::TypeError(
                        concat!(
                            "SCHEME-JSONLOGIC-STRICT: '",
                            $op_name,
                            "' requires boolean arguments (no truthiness)"
                        )
                        .to_string(),
                    ));
                }
            }

            // Second pass: evaluate and short-circuit
            for arg in args.iter() {
                let result = eval_with_depth_tracking(arg, env, depth + 1)?;
                match result {
                    Value::Bool($short_circuit) => return Ok(Value::Bool($short_circuit)),
                    Value::Bool(_) => continue,
                    _ => {
                        return Err(Error::TypeError(
                            concat!(
                                "SCHEME-JSONLOGIC-STRICT: '",
                                $op_name,
                                "' requires boolean arguments (no truthiness)"
                            )
                            .to_string(),
                        ));
                    }
                }
            }

            Ok(Value::Bool($default))
        }
    };
}

// Generate boolean logic functions
boolean_logic_op!(eval_and, "and", false, true);
boolean_logic_op!(eval_or, "or", true, false);

/// Create a global environment with built-in functions
pub fn create_global_env() -> Environment {
    let mut env = Environment::new();

    // Add all regular functions from the registry
    for builtin_op in get_builtin_ops() {
        if let crate::builtinops::OpKind::Function(func) = &builtin_op.op_kind {
            // Use BuiltinFunction for environment bindings (dynamic calls through symbols)
            let f = *func;
            env.define(
                builtin_op.scheme_id.to_owned(),
                Value::BuiltinFunction {
                    id: builtin_op.scheme_id.to_owned(),
                    func: Arc::new(move |args: Vec<Value>| f(&args)),
                },
            );
        }
    }

    env
}

#[cfg(all(test, feature = "scheme"))]
#[expect(clippy::unwrap_used)] // test code OK
mod tests {
    use super::*;
    use crate::Error;
    use crate::ast::{nil, sym, val};
    use crate::intooperation::{NumIterator, NumRest, ValueListIterator, ValuesRest};
    use crate::scheme::parse_scheme;

    #[test]
    fn test_register_builtin_operation_add() {
        fn add(a: i64, b: i64) -> i64 {
            a + b
        }
        let mut env = create_global_env();
        env.register_builtin_operation::<_, (i64, i64), i64>("add2", add);
        let expr = parse_scheme("(add2 7 5)").unwrap();
        let result = eval(&expr, &mut env).unwrap();
        assert_eq!(result, Value::Number(12));
    }

    #[test]
    fn test_register_builtin_operation_zero_arg() {
        fn forty_two() -> i64 {
            42
        }

        let mut env = create_global_env();
        env.register_builtin_operation::<_, (), i64>("forty-two", forty_two);

        let expr = parse_scheme("(forty-two)").unwrap();
        let result = eval(&expr, &mut env).unwrap();
        assert_eq!(result, Value::Number(42));
    }

    #[test]
    fn test_register_builtin_operation_result_builtin() {
        fn safe_div(a: i64, b: i64) -> Result<i64, &'static str> {
            if b == 0 {
                Err("division by zero")
            } else {
                Ok(a / b)
            }
        }

        let mut env = create_global_env();
        // Functions returning Result<_, E> are supported via IntoResult.
        // Explicit type annotations on the registration help type inference
        // in builds that enable all targets.
        env.register_builtin_operation::<_, (i64, i64), i64>("safe-div", safe_div);

        // Success case
        let expr_ok = parse_scheme("(safe-div 6 3)").unwrap();
        let result_ok = eval(&expr_ok, &mut env).unwrap();
        assert_eq!(result_ok, Value::Number(2));

        // Error case: division by zero surfaces as EvalError containing the message
        let expr_err = parse_scheme("(safe-div 1 0)").unwrap();
        let err = eval(&expr_err, &mut env).unwrap_err();
        let msg = format!("{err}");
        assert!(msg.contains("division by zero"));
    }

    #[test]
    fn test_register_builtin_operation_list_numeric_iterator_param() {
        fn sum_list(nums: NumIterator<'_>) -> i64 {
            nums.sum()
        }

        let mut env = create_global_env();
        env.register_builtin_operation::<_, (NumIterator<'static>,), i64>("sum-list", sum_list);

        let expr = parse_scheme("(sum-list (list 1 2 3 4))").unwrap();
        let result = eval(&expr, &mut env).unwrap();
        assert_eq!(result, Value::Number(10));
    }

    #[test]
    fn test_register_builtin_operation_with_rest_values() {
        fn first_and_rest_count(mut args: ValueListIterator<'_>) -> Result<Value, Error> {
            let first = match args.next() {
                Some(Value::Number(n)) => *n,
                Some(_) => return Err(Error::TypeError("first argument must be a number".into())),
                None => return Err(Error::arity_error(1, 0)),
            };

            let rest_count = args.count() as i64;

            Ok(Value::List(vec![
                Value::Number(first),
                Value::Number(rest_count),
            ]))
        }

        let mut env = create_global_env();
        env.register_variadic_builtin_operation::<_, (ValuesRest,), Value>(
            "first-rest-count",
            Arity::AtLeast(1),
            first_and_rest_count,
        );

        let expr = parse_scheme("(first-rest-count 42 \"x\" #t 7)").unwrap();
        let result = eval(&expr, &mut env).unwrap();
        assert_eq!(
            result,
            Value::List(vec![Value::Number(42), Value::Number(3)])
        );
    }

    #[test]
    fn test_register_builtin_operation_varargs_borrowed_values_all() {
        fn count_numbers(args: ValueListIterator<'_>) -> Result<Value, Error> {
            let count = args.filter(|v| matches!(v, Value::Number(_))).count() as i64;

            Ok(Value::Number(count))
        }

        let mut env = create_global_env();
        env.register_variadic_builtin_operation::<_, (ValuesRest,), Value>(
            "count-numbers",
            Arity::AtLeast(0),
            count_numbers,
        );

        let expr = parse_scheme("(count-numbers 1 \"x\" 2 #t 3)").unwrap();
        let result = eval(&expr, &mut env).unwrap();
        assert_eq!(result, Value::Number(3));
    }

    #[test]
    fn test_register_builtin_operation_varargs_all_i64() {
        fn sum_all(nums: NumIterator<'_>) -> i64 {
            nums.sum::<i64>()
        }

        let mut env = create_global_env();
        env.register_variadic_builtin_operation::<_, (NumRest,), i64>(
            "sum-varargs-all",
            Arity::AtLeast(0),
            sum_all,
        );

        let expr = parse_scheme("(sum-varargs-all 1 2 3 4)").unwrap();
        let result = eval(&expr, &mut env).unwrap();
        assert_eq!(result, Value::Number(10));
    }

    #[test]
    fn test_register_builtin_operation_varargs_fixed_plus_rest() {
        fn weighted_sum(weight: i64, nums: NumIterator<'_>) -> i64 {
            weight * nums.sum::<i64>()
        }

        let mut env = create_global_env();
        env.register_variadic_builtin_operation::<_, (i64, NumRest), i64>(
            "weighted-sum",
            Arity::AtLeast(1),
            weighted_sum,
        );

        let expr = parse_scheme("(weighted-sum 2 1 2 3)").unwrap();
        let result = eval(&expr, &mut env).unwrap();
        assert_eq!(result, Value::Number(12));
    }

    #[test]
    fn test_register_variadic_builtin_operation_with_explicit_arity() {
        fn sum_all(nums: NumIterator<'_>) -> i64 {
            nums.sum::<i64>()
        }

        let mut env = create_global_env();
        env.register_variadic_builtin_operation::<_, (NumRest,), i64>(
            "sum-all-min1",
            Arity::AtLeast(1),
            sum_all,
        );

        // Valid call: three numeric arguments.
        let expr_ok = parse_scheme("(sum-all-min1 1 2 3)").unwrap();
        let result_ok = eval(&expr_ok, &mut env).unwrap();
        assert_eq!(result_ok, Value::Number(6));

        // Invalid call: zero arguments should fail Arity::AtLeast(1).
        let expr_err = parse_scheme("(sum-all-min1)").unwrap();
        let err = eval(&expr_err, &mut env).unwrap_err();
        match err {
            crate::Error::ArityError { .. } => {}
            other => panic!("expected ArityError, got {other:?}"),
        }
    }

    #[test]
    fn test_builtin_comparison_dynamic_uses_typed_mechanism() {
        let mut env = create_global_env();

        // Dynamic higher-order use of a builtin comparison: the `>`
        // operator is passed as a value and called with three
        // arguments. This exercises dynamic builtin calls through
        // the environment using the shared builtin registry.
        let expr = parse_scheme("((lambda (op a b c) (op a b c)) > 9 6 2)").unwrap();
        let result = eval(&expr, &mut env).unwrap();
        assert_eq!(result, Value::Bool(true));

        let expr_false = parse_scheme("((lambda (op a b c) (op a b c)) > 9 6 7)").unwrap();
        let result_false = eval(&expr_false, &mut env).unwrap();
        assert_eq!(result_false, Value::Bool(false));
    }

    /// Test result variants for comprehensive testing
    #[derive(Debug)]
    enum TestResult {
        EvalResult(Value),           // Evaluation should succeed with this value
        SpecificError(&'static str), // Evaluation should fail with error containing this string
        Error,                       // Evaluation should fail (any error)
    }
    use TestResult::*;

    /// Test environment containing test cases that share state
    struct TestEnvironment(Vec<(&'static str, TestResult)>);

    /// Micro-helper for success cases in comprehensive tests
    fn success<T: Into<Value>>(value: T) -> TestResult {
        EvalResult(val(value))
    }

    /// Macro for setup expressions that return Unspecified (like define)
    macro_rules! test_setup {
        ($expr:expr) => {
            ($expr, EvalResult(Value::Unspecified))
        };
    }

    /// Run tests in isolated environments with shared state
    fn run_tests_in_environment(test_environments: Vec<TestEnvironment>) {
        for (env_idx, TestEnvironment(test_cases)) in test_environments.iter().enumerate() {
            let mut env = create_global_env();

            // Run test cases in this environment using shared logic
            for (test_idx, (input, expected)) in test_cases.iter().enumerate() {
                let test_id = format!("Environment #{} test #{}", env_idx + 1, test_idx + 1);
                execute_test_case(input, expected, &mut env, &test_id);
            }
        }
    }

    /// Execute a single test case with detailed error reporting
    fn execute_test_case(input: &str, expected: &TestResult, env: &mut Environment, test_id: &str) {
        let expr = match parse_scheme(input) {
            Ok(expr) => expr,
            Err(parse_err) => {
                panic!("{test_id}: unexpected parse error for '{input}': {parse_err:?}");
            }
        };

        match (eval(&expr, env), expected) {
            (Ok(actual), EvalResult(expected_val)) => {
                // Special handling for Unspecified values - they should match type but not equality
                match (&actual, expected_val) {
                    (Value::Unspecified, Value::Unspecified) => {} // Both unspecified - OK
                    _ => {
                        assert!(
                            !(actual != *expected_val),
                            "{test_id}: expected {expected_val:?}, got {actual:?}"
                        );
                    }
                }
            }

            (Err(_), Error) => {} // Expected generic error
            (Err(e), SpecificError(expected_text)) => {
                let error_msg = format!("{e}");
                assert!(
                    error_msg.contains(expected_text),
                    "{test_id}: error should contain '{expected_text}', got: {error_msg}"
                );
            }
            (Ok(actual), Error) => {
                panic!("{test_id}: expected error, got {actual:?}");
            }
            (Ok(actual), SpecificError(expected_text)) => {
                panic!("{test_id}: expected error containing '{expected_text}', got {actual:?}");
            }
            (Err(err), EvalResult(expected_val)) => {
                panic!("{test_id}: expected {expected_val:?}, got error {err:?}");
            }
        }
    }

    /// Simplified test runner with specific error message support
    fn run_comprehensive_tests(test_cases: Vec<(&str, TestResult)>) {
        for (i, (input, expected)) in test_cases.iter().enumerate() {
            let mut env = create_global_env();
            let test_id = format!("#{}", i + 1);
            execute_test_case(input, expected, &mut env, &test_id);
        }
    }

    #[test]
    #[expect(clippy::too_many_lines)] // Comprehensive test coverage is intentionally thorough
    fn test_comprehensive_operations_data_driven() {
        let test_cases = vec![
            // === SELF-EVALUATING FORMS ===
            // Numbers
            ("42", success(42)),
            ("-271", success(-271)),
            ("0", success(0)),
            ("9223372036854775807", success(i64::MAX)),
            ("-9223372036854775808", success(i64::MIN)),
            // Booleans
            ("#t", success(true)),
            ("#f", success(false)),
            // Strings
            ("\"hello\"", success("hello")),
            ("\"hello world\"", success("hello world")),
            ("\"\"", success("")),
            ("\"with\\\"quotes\"", success("with\"quotes")),
            // === ARITHMETIC OPERATIONS ===
            // Addition (allows 0 arguments - returns 0)
            ("(+ 1 2 3)", success(6)),
            ("(+ 0)", success(0)),
            ("(+ 42)", success(42)),
            ("(+ -5 10)", success(5)),
            ("(+)", success(0)), // Addition with no args returns 0
            // Subtraction (requires at least 1 argument)
            ("(- 10 3 2)", success(5)),
            ("(- 10)", success(-10)), // Unary negation
            ("(- 0)", success(0)),
            ("(- -5)", success(5)),
            ("(- 100 50 25)", success(25)),
            // Multiplication (requires at least 1 argument)
            ("(* 2 3 4)", success(24)),
            ("(* 0 100)", success(0)),
            ("(* 1)", success(1)),
            ("(* -2 3)", success(-6)),
            ("(* 7)", success(7)), // Single argument returns itself
            // Mixed operations with nested expressions
            ("(+ (* 2 3) (- 8 2))", success(12)),
            ("(* (+ 1 2) (- 5 2))", success(9)),
            ("(- (+ 10 5) (* 2 3))", success(9)),
            // Arithmetic overflow errors
            ("(+ 9223372036854775807 1)", Error), // i64::MAX + 1
            ("(- -9223372036854775808)", Error),  // -(i64::MIN)
            ("(- -9223372036854775808 1)", Error), // i64::MIN - 1
            ("(* 4611686018427387904 2)", Error), // (i64::MAX/2 + 1) * 2
            // === EQUALITY AND COMPARISON OPERATIONS ===
            // Numeric equality (spec-compliant - only accepts numbers)
            ("(= 5 5)", success(true)),
            ("(= 5 6)", success(false)),
            ("(= 0 0)", success(true)),
            ("(= -1 -1)", success(true)),
            ("(= 100 200)", success(false)),
            // = rejects non-numbers (type errors)
            ("(= \"hello\" \"hello\")", Error),
            ("(= #t #t)", Error),
            ("(= #f #f)", Error),
            // General equality with equal? (works for all types)
            ("(equal? 5 5)", success(true)),
            ("(equal? 5 6)", success(false)),
            ("(equal? \"hello\" \"hello\")", success(true)),
            ("(equal? \"hello\" \"world\")", success(false)),
            ("(equal? #t #t)", success(true)),
            ("(equal? #t #f)", success(false)),
            ("(equal? #f #f)", success(true)),
            // Numeric comparison operators
            ("(< 3 5)", success(true)),
            ("(< 5 3)", success(false)),
            ("(< 0 1)", success(true)),
            ("(< -5 -3)", success(true)),
            ("(> 5 3)", success(true)),
            ("(> 3 5)", success(false)),
            ("(> 1 0)", success(true)),
            ("(> -3 -5)", success(true)),
            ("(<= 3 5)", success(true)),
            ("(<= 5 5)", success(true)),
            ("(<= 5 3)", success(false)),
            ("(<= 0 0)", success(true)),
            ("(>= 5 3)", success(true)),
            ("(>= 5 5)", success(true)),
            ("(>= 3 5)", success(false)),
            ("(>= 0 0)", success(true)),
            // === QUOTE OPERATIONS ===
            // Longhand quote syntax
            ("(quote hello)", success(sym("hello"))),
            ("(quote foo)", success(sym("foo"))),
            ("(quote (1 2 3))", success([1, 2, 3])),
            ("(quote (+ 1 2))", success([sym("+"), val(1), val(2)])),
            ("(quote (a b c))", success([sym("a"), sym("b"), sym("c")])),
            ("(quote ())", success(nil())), // Empty list (nil)
            // Shorthand quote syntax
            ("'hello", success(sym("hello"))),
            ("'(1 2 3)", success([1, 2, 3])),
            ("'(+ 1 2)", success([sym("+"), val(1), val(2)])),
            ("'()", success(nil())), // Empty list (nil) via shorthand
            ("'42", success(42)),
            ("'#t", success(true)),
            // Nested quotes
            ("'(quote x)", success([sym("quote"), sym("x")])),
            ("''x", success([sym("quote"), sym("x")])),
            // === DYNAMIC FUNCTION CALLS IN OPERATOR POSITION ===
            // Test that expressions in operator position are evaluated correctly
            ("((if #t + *) 2 3)", success(5)), // + was chosen, 2 + 3 = 5
            ("((if #f + *) 2 3)", success(6)), // * was chosen, 2 * 3 = 6
            // Test lambda in operator position
            ("((lambda (x) (* x x)) 4)", success(16)), // 4 * 4 = 16
            // === LIST OPERATIONS ===
            // Basic list access
            ("(car (list 1 2 3))", success(1)),
            ("(car (list \"first\" \"second\"))", success("first")),
            ("(cdr (list 1 2 3))", success([2, 3])),
            ("(cdr (list \"a\" \"b\" \"c\"))", success(["b", "c"])),
            // List construction
            ("(cons 1 (list 2 3))", success([1, 2, 3])),
            ("(cons \"x\" (list \"y\" \"z\"))", success(["x", "y", "z"])),
            ("(list)", success(nil())),
            ("(list 1)", success([1])),
            ("(list 1 2 3 4)", success([1, 2, 3, 4])),
            // === NIL REPRESENTATION AND OPERATIONS ===
            // Test strict evaluation semantics: () is NOT self-evaluating
            // This is a very common Scheme extension, but we're trying to be minimalist to the spec
            ("()", Error), // Empty list cannot be evaluated.
            // null? predicate tests
            ("(null? '())", success(true)),
            ("(null? (list))", success(true)),
            ("(null? (quote ()))", success(true)),
            ("(null? 42)", success(false)),
            ("(null? #f)", success(false)),
            // cons with nil (additional cases beyond basic list construction)
            ("(cons 1 '())", success([1])),
            ("(cons 'a (cons 'b '()))", success([sym("a"), sym("b")])),
            // Lambda with empty parameter list
            ("((lambda () 42))", success(42)),
            // === STRING OPERATIONS ===
            // Basic string concatenation
            ("(string-append)", success("")),
            ("(string-append \"hello\")", success("hello")),
            (
                "(string-append \"hello\" \" \" \"world\")",
                success("hello world"),
            ),
            ("(string-append \"\" \"test\" \"\")", success("test")),
            ("(string-append 42)", Error),
            ("(string-append \"hello\" 123)", Error),
            ("(string-append #t \"world\")", Error),
            // === MATH OPERATIONS - MAX/MIN ===
            // Basic max operations
            ("(max 5)", success(5)),
            ("(max 1 2 3)", success(3)),
            ("(max 3 1 2)", success(3)),
            ("(max -5 -1 -10)", success(-1)),
            // Basic min operations
            ("(min 5)", success(5)),
            ("(min 1 2 3)", success(1)),
            ("(min 3 1 2)", success(1)),
            ("(min -5 -1 -10)", success(-10)),
            // Error cases - non-number arguments
            ("(max \"hello\")", Error),
            ("(min #t)", Error),
            ("(max 1 \"hello\")", Error),
            ("(min 1 #t)", Error),
            // === CONDITIONAL OPERATIONS ===
            // Basic if expressions
            ("(if #t 1 2)", success(1)),
            ("(if #f 1 2)", success(2)),
            ("(if #t \"yes\" \"no\")", success("yes")),
            ("(if #f \"yes\" \"no\")", success("no")),
            // if with computed conditions
            ("(if (> 5 3) \"greater\" \"lesser\")", success("greater")),
            ("(if (< 5 3) \"greater\" \"lesser\")", success("lesser")),
            ("(if (equal? 1 1) 42 0)", success(42)),
            // SCHEME-JSONLOGIC-STRICT: if condition must be a boolean (rejects truthy/falsy)
            ("(if 0 1 2)", Error),
            ("(if 42 1 2)", Error),
            ("(if () 1 2)", Error),
            ("(if \"hello\" 1 2)", Error),
            ("(if '() 1 2)", Error), // nil as condition should error
            ("(if #f 42 '())", success(nil())), // if returning nil is valid
            // Note: Arity errors are now caught at parse time - see scheme.rs tests
            // === BOOLEAN LOGIC OPERATIONS ===
            // and operator - SCHEME-STRICT: Require at least 1 argument (Scheme R7RS allows 0 args, returns #t)
            ("(and #t)", success(true)),
            ("(and #f)", success(false)),
            ("(and #t #t)", success(true)),
            ("(and #t #f)", success(false)),
            ("(and #f #t)", success(false)),
            ("(and #t #t #t)", success(true)),
            ("(and #t #t #f)", success(false)),
            // and errors - SCHEME-JSONLOGIC-STRICT: and requires boolean arguments
            // Note: Arity errors are now caught at parse time - see scheme.rs tests
            ("(and 1 2 3)", Error),  // rejects non-booleans
            ("(and 1 #f 3)", Error), // rejects non-booleans
            // or operator - SCHEME-STRICT: Require at least 1 argument (Scheme R7RS allows 0 args, returns #f)
            ("(or #t)", success(true)),
            ("(or #f)", success(false)),
            ("(or #t #f)", success(true)),
            ("(or #f #t)", success(true)),
            ("(or #f #f)", success(false)),
            ("(or #f #f #t)", success(true)),
            ("(or #f #f #f)", success(false)),
            // or errors - SCHEME-JSONLOGIC-STRICT: or requires boolean arguments
            // Note: Arity errors are now caught at parse time - see scheme.rs tests
            ("(or #f 2 3)", Error), // rejects non-booleans
            ("(or 1 2 3)", Error),  // rejects non-booleans
            // not operator (requires exactly 1 boolean argument)
            ("(not #t)", success(false)),
            ("(not #f)", success(true)),
            // not errors - SCHEME-JSONLOGIC-STRICT: not requires boolean arguments
            ("(not ())", Error),        // rejects non-booleans
            ("(not 0)", Error),         // rejects non-booleans
            ("(not 42)", Error),        // rejects non-booleans
            ("(not \"hello\")", Error), // rejects non-booleans
            // Complex boolean expressions
            ("(and (or #f #t) (not #f))", success(true)),
            ("(or (and #f #t) (not #f))", success(true)),
            ("(not (and #t #f))", success(true)),
            ("(and (> 5 3) (< 2 4))", success(true)),
            ("(or (= 1 2) (= 2 2))", success(true)),
            // Short-circuit evaluation - undefined variables not evaluated due to short-circuit
            ("(and #f undefined-var)", success(false)), // should not evaluate undefined-var
            ("(or #t undefined-var)", success(true)),   // should not evaluate undefined-var
            // === STRICT EVALUATION SEMANTICS ===
            // SCHEME-STRICT: Empty list () is NOT self-evaluating (must be quoted)
            // This is stricter than standard Scheme but more predictable
            ("()", Error), // Empty list should error when evaluated directly
            // SCHEME-STRICT: if condition must be boolean (rejects truthy/falsy including nil)
            ("(if '() 1 2)", Error), // nil as condition should error
            // null? function works with quoted empty lists
            ("(null? '())", success(true)),
            ("(null? (list 1))", success(false)),
            // === ERROR FUNCTION OPERATIONS ===
            // Test error with string message
            (
                "(error \"Something went wrong\")",
                SpecificError("Something went wrong"),
            ),
            // Test error with symbol message
            ("(error oops)", SpecificError("oops")),
            // Test error with number message
            ("(error 42)", SpecificError("42")),
            // Test error with multiple arguments
            (
                "(error \"Error:\" 42 \"occurred\")",
                SpecificError("Error: 42 occurred"),
            ),
            // Test error with no arguments
            ("(error)", SpecificError("Error")),
            // === ERROR PROPAGATION AND HANDLING ===
            // Test undefined variable errors
            ("undefined-var", Error),
            // Test type errors propagate through calls
            ("(not 42)", SpecificError("boolean argument")), // Type error with specific message
            ("(car \"not-a-list\")", Error),                 // Type error
            // Test errors in nested expressions
            ("(+ 1 (car \"not-a-list\"))", Error),
            ("(if (not 42) 1 2)", Error),
            // Test lambda parameter errors
            ("(lambda (x x) x)", Error),           // Duplicate params
            ("(lambda \"not-a-list\" 42)", Error), // Invalid params
            // Test define errors
            ("(define 123 42)", Error),            // Invalid var name
            ("(define \"not-symbol\" 42)", Error), // Invalid var name
            // === ERROR CASES ===
            // Unbound variables
            (
                "undefined-var",
                SpecificError("Unbound variable: undefined-var"),
            ),
            // set! special form test - not implemented in this interpreter
            // This Environment model uses immutable bindings where variables are looked up
            // by traversing the environment chain, but mutation would require mutable references
            // throughout the chain. If set! were supported this design would need revisiting
            ("(set! x 42)", SpecificError("Unbound variable: set!")), // Unsupported special forms appear as unbound variables
            // Type errors
            (
                "(+ 1 \"hello\")",
                SpecificError("Type error: + requires numbers"),
            ),
        ];

        run_comprehensive_tests(test_cases);

        // === ENVIRONMENT-SENSITIVE TESTS ===
        // Tests that require shared state between expressions in the same environment
        let environment_test_cases = vec![
            // === DEFINE AND LOOKUP ===
            // Basic variable definition and lookup
            TestEnvironment(vec![
                test_setup!("(define x 42)"), // Define variable
                ("x", success(42)),           // Should be able to lookup defined variable
                ("y", Error),                 // Undefined variable should error
            ]),
            // === DEFINE AND VARIABLES ===
            // Variable redefinition and usage in expressions
            TestEnvironment(vec![
                // Define a variable
                test_setup!("(define x 42)"),
                ("x", success(42)),
                // Use variable in expressions
                ("(+ x 8)", success(50)),
                // Redefine variable
                test_setup!("(define x 100)"),
                ("x", success(100)),
            ]),
            // === BUILTIN FUNCTIONS VIA DYNAMIC SYMBOL LOOKUP ===
            // Builtin functions called dynamically through symbols
            TestEnvironment(vec![
                // Store a reference to + in a variable, then call it
                test_setup!("(define my-add +)"),
                ("(my-add 10 20)", success(30)),
                // Store reference to equal? and call it
                test_setup!("(define my-eq equal?)"),
                ("(my-eq 5 5)", success(true)),
            ]),
            // === LAMBDA FUNCTIONS VIA EVAL_LIST (Test 1) ===
            // Test immediate lambda call
            TestEnvironment(vec![("((lambda (x y) (+ x y)) 3 4)", success(7))]),
            // === LAMBDA FUNCTIONS VIA EVAL_LIST (Test 2) ===
            // Test lambda definition and call
            TestEnvironment(vec![
                test_setup!("(define add-one (lambda (x) (+ x 1)))"),
                ("(add-one 42)", success(43)),
            ]),
            // === DEFINE WITH VARIOUS VALUE TYPES ===
            // Test defining and retrieving different types
            TestEnvironment(vec![
                // Define numbers, booleans, strings
                test_setup!("(define x 42)"),
                test_setup!("(define flag #t)"),
                test_setup!("(define name \"test\")"),
                // Verify they can be retrieved
                ("x", success(42)),
                ("flag", success(true)),
                ("name", success("test")),
                // Define and retrieve builtin functions (test that it's a BuiltinFunction)
                test_setup!("(define my-plus +)"),
            ]),
            // === NESTED EVALUATION PATHS ===
            // Test deeply nested expressions that exercise multiple evaluation paths
            TestEnvironment(vec![
                test_setup!("(define square (lambda (x) (* x x)))"), // Define helper function
                // This expression exercises multiple evaluation paths:
                // - if (special form via PrecompiledOp)
                // - > (builtin via PrecompiledOp)
                // - square (lambda via dynamic call)
                // - + (builtin via PrecompiledOp)
                ("(if (> 5 3) (square (+ 2 1)) 0)", success(9)), // (+ 2 1) = 3, square(3) = 9
            ]),
            // === SELF EVALUATING FORMS ===
            // BuiltinFunction and Function are self-evaluating (test with environment)
            TestEnvironment(vec![
                test_setup!("(define f +)"),
                // Note: We can't easily test the type in data-driven approach,
                // but we can verify it behaves correctly as a function
                ("(f 2 3)", success(5)),
            ]),
            // === IMPOSSIBLE PRECOMPILED OP IN EVAL_LIST ===
            // This test documents that PrecompiledOp can never reach eval_list
            TestEnvironment(vec![
                // Set up dynamic builtin reference and lambda function
                test_setup!("(define add +)"),
                test_setup!("(define sq (lambda (x) (* x x)))"),
                // 1. Direct builtin calls (via PrecompiledOp in main eval)
                ("(+ 1 2)", success(3)),
                // 2. Dynamic builtin calls (via BuiltinFunction in eval_list)
                ("(add 1 2)", success(3)),
                // 3. Lambda calls (via Function in eval_list)
                ("(sq 3)", success(9)),
                // 4. Complex nested calls - still no PrecompiledOp in eval_list
                ("((lambda (f x) (f x x)) + 5)", success(10)), // f=+, x=5, so (+ 5 5) = 10
                ("((lambda (g y) (g y)) sq 6)", success(36)),  // g=sq, y=6, so (sq 6) = 36
                // 5. Higher-order function combinations
                ("((lambda (op a b) (op a b)) * 3 4)", success(12)), // op=*, a=3, b=4
                ("((lambda (fn) (fn 7)) sq)", success(49)),          // fn=sq, so (sq 7) = 49
            ]),
            // === HIGHER ORDER FUNCTIONS ===
            // Define a function that takes another function as argument
            TestEnvironment(vec![
                test_setup!("(define twice (lambda (f x) (f (f x))))"),
                test_setup!("(define inc (lambda (x) (+ x 1)))"),
                ("(twice inc 5)", success(7)),
            ]),
            // === LEXICAL SCOPING ===
            // Test that lambda captures its environment and parameter shadowing
            TestEnvironment(vec![
                // Test that lambda captures its environment
                test_setup!("(define x 10)"),
                test_setup!("(define make-adder (lambda (n) (lambda (x) (+ x n))))"),
                test_setup!("(define add5 (make-adder 5))"),
                ("(add5 3)", success(8)),
                // Test parameter shadowing
                test_setup!("(define f (lambda (x) (lambda (x) (* x 2))))"),
                test_setup!("(define g (f 10))"),
                ("(g 3)", success(6)),
            ]),
            // === LAMBDA AND DEFINE EDGE CASES ===
            // Test lambda with various parameter patterns
            TestEnvironment(vec![
                test_setup!("(define id (lambda (x) x))"),
                ("(id 42)", success(42)),
                // Test lambda with multiple parameters
                test_setup!("(define add3 (lambda (a b c) (+ a b c)))"),
                ("(add3 1 2 3)", success(6)),
                // Test lambda with no parameters
                test_setup!("(define const42 (lambda () 42))"),
                ("(const42)", success(42)),
                // Test closures capture environment
                test_setup!("(define x 10)"),
                test_setup!("(define add-x (lambda (y) (+ x y)))"),
                ("(add-x 5)", success(15)),
                // Test nested lambdas (higher-order functions)
                test_setup!("(define make-adder (lambda (n) (lambda (x) (+ n x))))"),
                test_setup!("(define add5 (make-adder 5))"),
                ("(add5 3)", success(8)),
                // Test lambda arity checking
                ("(id)", Error),     // Too few args
                ("(id 1 2)", Error), // Too many args
                // Test define with function values
                test_setup!("(define plus +)"),
                ("(plus 2 3)", success(5)),
                // Test redefining variables
                test_setup!("(define y 100)"),
                ("y", success(100)),
                test_setup!("(define y 200)"),
                ("y", success(200)),
            ]),
            // === ENVIRONMENT SCOPING EDGE CASES (Test 1) ===
            // Global vs local scope (parameter shadowing)
            TestEnvironment(vec![
                test_setup!("(define x 1)"),
                test_setup!("(define f (lambda (x) (+ x 10)))"), // parameter x shadows global x
                ("(f 5)", success(15)), // uses parameter x=5, not global x=1
                ("x", success(1)),      // global x unchanged
                ("(f x)", success(11)), // uses global x=1 as argument: 1+10=11
            ]),
            // === ENVIRONMENT SCOPING EDGE CASES (Test 2) ===
            // Closure behavior with variable redefinition
            TestEnvironment(vec![
                test_setup!("(define y 100)"),
                test_setup!("(define g (lambda () y))"), // closure captures y=100
                test_setup!("(define y 200)"),           // redefine y to 200
                // This implementation uses lexical scoping - closures see binding at definition time
                ("(g)", success(100)), // closure still sees original y=100
                ("y", success(200)),   // global y is now 200
            ]),
            // === ENVIRONMENT SCOPING EDGE CASES (Test 3) ===
            // Nested function definitions (higher-order functions)
            TestEnvironment(vec![
                test_setup!("(define outer (lambda (a) (lambda (b) (+ a b))))"),
                test_setup!("(define add10 (outer 10))"), // creates a function that adds 10
                ("(add10 5)", success(15)),               // 10 + 5 = 15
                ("(add10 25)", success(35)),              // 10 + 25 = 35
                ("((outer 3) 7)", success(10)),           // direct call: 3 + 7 = 10
            ]),
            // === LAMBDA AND FUNCTION CALLS (Test 1) ===
            // Test valid lambda definitions and calls
            TestEnvironment(vec![
                // Define a simple lambda
                test_setup!("(define square (lambda (x) (* x x)))"),
                ("(square 5)", success(25)),
                // Lambda with multiple parameters
                test_setup!("(define add (lambda (a b) (+ a b)))"),
                ("(add 3 4)", success(7)),
                // Lambda with no parameters
                test_setup!("(define get-answer (lambda () 42))"),
                ("(get-answer)", success(42)),
            ]),
            // === LAMBDA AND FUNCTION CALLS (Test 2) ===
            // Test error cases for lambda (each in separate environment to avoid interference)
            TestEnvironment(vec![
                // Duplicate parameter names should be rejected
                ("(lambda (x x) (+ x x))", Error),
                ("(lambda (a b a) (* a b))", Error),
                // Variadic lambda forms should be rejected (we only support fixed-arity)
                ("(lambda args (+ 1 2))", Error), // Symbol parameter list
                // Non-symbol parameters should be rejected
                ("(lambda (1 2) (+ 1 2))", Error),
                ("(lambda (\"x\" y) (+ x y))", Error),
            ]),
            // === COMPLEX EXPRESSIONS (Test 1) ===
            // Test complex nested expression in isolation
            TestEnvironment(vec![(
                "(((lambda (x) (lambda (y) (+ x y))) 10) 5)",
                success(15),
            )]),
            // === COMPLEX EXPRESSIONS (Test 2) ===
            // Test list processing functions
            TestEnvironment(vec![
                // Simple list processing (non-recursive version)
                test_setup!("(define first (lambda (lst) (car lst)))"),
                ("(first (list 1 2 3 4))", success(1)),
                // Test list construction and access
                test_setup!("(define make-pair (lambda (a b) (list a b)))"),
                test_setup!("(define get-first (lambda (pair) (car pair)))"),
                test_setup!("(define get-second (lambda (pair) (car (cdr pair))))"),
                test_setup!("(define my-pair (make-pair 42 \"hello\"))"),
                ("(get-first my-pair)", success(42)),
                ("(get-second my-pair)", success("hello")),
            ]),
        ];

        run_tests_in_environment(environment_test_cases);
    }

    // Additional type check that can't be done data-driven
    #[test]
    fn test_builtin_function_self_evaluation() {
        let mut env = create_global_env();
        eval(&parse_scheme("(define f +)").unwrap(), &mut env).unwrap();
        let result = eval(&parse_scheme("f").unwrap(), &mut env).unwrap();
        match result {
            Value::BuiltinFunction { .. } => {} // Self-evaluating
            _ => panic!("Expected BuiltinFunction to be self-evaluating"),
        }
    }

    #[test]
    fn test_recursive_functions() {
        // This test demonstrates the current limitation: recursive functions fail
        // because the function name is not yet bound when the lambda body is created.
        // In a full Scheme implementation with letrec semantics, these should work.

        let recursive_test_cases = vec![
            // === SINGLE RECURSIVE FUNCTIONS (Currently Failing) ===
            TestEnvironment(vec![
                // Simple factorial function - should fail because 'factorial' is unbound in lambda body
                test_setup!(
                    "(define factorial (lambda (n) (if (= n 0) 1 (* n (factorial (- n 1))))))"
                ),
                (
                    "(factorial 5)",
                    SpecificError("Unbound variable: factorial"),
                ), // Current limitation
            ]),
            // === MUTUALLY RECURSIVE FUNCTIONS (Currently Failing) ===
            TestEnvironment(vec![
                // Even/odd mutual recursion - fails because functions can't see each other during definition
                test_setup!("(define is-even (lambda (n) (if (= n 0) #t (is-odd (- n 1)))))"),
                test_setup!("(define is-odd (lambda (n) (if (= n 0) #f (is-even (- n 1)))))"),
                ("(is-even 4)", SpecificError("Unbound variable: is-odd")), // is-even tries to call is-odd but it's not visible
                ("(is-odd 3)", SpecificError("Unbound variable: is-odd")), // is-odd -> is-even -> is-odd, but is-odd not visible in is-even
            ]),
            // === EDGE CASES FOR RECURSION ===
            TestEnvironment(vec![
                // Self-referencing lambda in complex expression
                test_setup!(
                    "(define countdown (lambda (n) (if (<= n 0) (list) (cons n (countdown (- n 1))))))"
                ),
                (
                    "(countdown 3)",
                    SpecificError("Unbound variable: countdown"),
                ), // Current limitation
            ]),
            TestEnvironment(vec![
                // Indirect self-reference through higher-order function
                test_setup!("(define apply-self (lambda (f x) (f x)))"),
                test_setup!(
                    "(define factorial-indirect (lambda (n) (if (= n 0) 1 (* n (apply-self factorial-indirect (- n 1))))))"
                ),
                (
                    "(factorial-indirect 3)",
                    SpecificError("Unbound variable: factorial-indirect"),
                ), // Current limitation
            ]),
            // === EDGE CASES THAT ACTUALLY WORK (Recursion Workarounds) ===
            TestEnvironment(vec![
                // Self-application trick (Y combinator style) - this actually works!
                test_setup!("(define self-apply (lambda (f x) (f f x)))"),
                test_setup!(
                    "(define factorial-trick (lambda (self n) (if (= n 0) 1 (* n (self self (- n 1))))))"
                ),
                ("(self-apply factorial-trick 5)", success(120)), // Works by passing function to itself
            ]),
            TestEnvironment(vec![
                // Higher-order function recursion maker - this also works!
                test_setup!("(define make-recursive (lambda (f) (lambda (x) ((f f) x))))"),
                test_setup!(
                    "(define fib-maker (lambda (self) (lambda (n) (if (< n 2) n (+ ((self self) (- n 1)) ((self self) (- n 2)))))))"
                ),
                test_setup!("(define fib (make-recursive fib-maker))"),
                ("(fib 6)", success(8)), // Fibonacci works through self-application
            ]),
            TestEnvironment(vec![
                // Countdown using self-application - redefine helper for this environment
                test_setup!("(define make-recursive (lambda (f) (lambda (x) ((f f) x))))"),
                test_setup!(
                    "(define countdown-maker (lambda (self) (lambda (n) (if (<= n 0) (list) (cons n ((self self) (- n 1)))))))"
                ),
                test_setup!("(define countdown (make-recursive countdown-maker))"),
                ("(countdown 3)", success([3, 2, 1])), // Recursive list building works
            ]),
            TestEnvironment(vec![
                // Mutual recursion simulation - alternating even/odd through single recursive function
                test_setup!(
                    "(define parity-maker (lambda (self) (lambda (n is-even) (if (= n 0) is-even ((self self) (- n 1) (not is-even))))))"
                ),
                test_setup!("(define check-parity (parity-maker parity-maker))"),
                ("(check-parity 4 #t)", success(true)), // 4 is even
                ("(check-parity 3 #t)", success(false)), // 3 is not even
                ("(check-parity 3 #f)", success(true)), // 3 is odd
            ]),
        ];

        // Run all the recursive function tests that demonstrate current limitations
        // and successful workarounds
        run_tests_in_environment(recursive_test_cases);
    }

    #[test]
    fn test_evaluation_depth_limit() {
        let depth_test_environments = vec![TestEnvironment(vec![
            // Define the deep recursion helper function
            test_setup!(
                "(define make-deep (lambda (self depth) (if (= depth 0) 42 (+ 1 (self self (- depth 1))))))"
            ),
            // Test that shallow depth works
            ("(make-deep make-deep 10)", success(52)), // 42 + 10
            // Test that deep evaluation is caught - use a value that should exceed MAX_EVAL_DEPTH
            // Each recursive call increases depth through function calls and if statements
            ("(make-deep make-deep 1000)", SpecificError("depth")),
        ])];

        run_tests_in_environment(depth_test_environments);
    }
}
