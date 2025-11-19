use crate::Error;
use crate::ast::Value;
use std::fmt::Display;
use std::sync::Arc;

/// Canonical erased builtin function type used by the evaluator.
///
/// Builtins receive ownership of their argument vector, enabling
/// implementations that consume or rearrange arguments if desired.
pub type OperationFn = dyn Fn(Vec<Value>) -> Result<Value, Error> + Send + Sync;

// =====================================================================
// Internal machinery for fixed-arity argument conversion
//
// All `unsafe` in this crate is deliberately confined to this module.
// The only primitive is `widen_slice_lifetime`, which is used by the
// `FromParam` implementations for slice parameters and by the
// variadic "rest" machinery for slice-like parameters. See the docs
// on that function and on `FromParam` for the full safety argument
// and the limitations in Rust's current type system that force this
// design.
// =====================================================================

mod sealed {
    //! Types that may be used as builtin parameters via `FromParam`.
    //!
    //! This `Sealed` trait prevents code outside this module from
    //! implementing `FromParam`, which keeps the safety invariants
    //! around `widen_slice_lifetime` local and auditable.
    //!
    //! To add a new builtin parameter type, you must:
    //! - add it here, and
    //! - add a matching `FromParam` implementation in this module.
    //!
    //! Slice-like types must be carefully reviewed, as they typically
    //! rely on `widen_slice_lifetime` and its safety invariants.

    pub trait Sealed {}

    impl Sealed for &super::Value {}
    impl Sealed for i64 {}
    impl Sealed for bool {}
    impl Sealed for &str {}
    impl Sealed for &[i64] {}
    impl Sealed for &[bool] {}
    impl Sealed for &[&str] {}
    impl Sealed for &[super::Value] {}
}

/// Core trait used by the fixed-arity adapters to turn `Value` nodes
/// into strongly-typed parameters.
///
/// This trait is **internal** to this module and sealed; the set of
/// supported parameter types is fixed to those we explicitly impl it
/// for above in `sealed`.
///
/// For example, a builtin like
/// `fn sum(first: i64, rest: &[i64]) -> Result<i64, Error>`
/// will be invoked via `FromParam` implementations for `i64` and
/// `&[i64]`.
///
/// The associated `Storage<'a>` type gives each parameter kind a place
/// to put temporary data (typically a `Vec<T>` for slice parameters).
/// The `Param<'a>` family then describes the parameter type as seen by
/// the builtin function for a given lifetime `'a` of the underlying
/// AST `Value`s.
///
/// ### Why is there `unsafe` here?
///
/// For scalar parameters (`i64`, `bool`, `&str`, `&Value`) the
/// implementation is entirely safe. For slice parameters like
/// `&[i64]`, `&[bool]`, and `&[&str]` we must populate a `Vec<T>` and
/// then hand the builtin a slice `&[T]` that appears to live for
/// `Param<'a>`'s lifetime. In reality the slice is only valid for the
/// duration of the adapter's stack frame that owns the `Vec<T>`.
///
/// The fixed-arity adapters call `FromParam::from_arg` inside a
/// function that immediately invokes the builtin and then drops all
/// `Storage` values before returning. Expressing "this reference is
/// valid only for the body of this call" is not something Rust's
/// current type system can do in a reusable trait, so we use a small
/// `unsafe` helper to widen the slice lifetime while **relying on the
/// calling pattern** to keep things sound.
///
/// Concretely, Rust today lacks:
/// - a way to express an "intersection" lifetime like
///   `min('vec, 'a)` for data borrowed from both a local `Vec<T>` and
///   the input `&'a Value`;
/// - the ability to state, in the trait, that `Param<'a>` values
///   cannot outlive the specific adapter call that created them,
///   even though the adapter is used under a higher-ranked
///   `for<'a>` bound;
/// - a safe standard-library abstraction that captures this
///   "stack-bounded borrow from scratch space" pattern for slices.
///
/// Instead, we:
/// - keep `FromParam` sealed and internal to this module;
/// - centralise the `unsafe` in `widen_slice_lifetime` with a detailed
///   `# Safety` explanation; and
/// - structure the fixed-arity adapters so that `Param<'a>` is never
///   stored or allowed to escape the call to the builtin.
pub(crate) trait FromParam: sealed::Sealed {
    /// Per-call scratch space, scoped to the lifetime of the argument
    /// values. For scalar parameters this is typically `()`; for slices
    /// it is usually a `Vec<T>` that we borrow from.
    type Storage<'a>: Default;

    /// The parameter type as seen by the builtin for a given lifetime
    /// of the underlying AST values.
    type Param<'a>;

    /// Convert a single AST argument into this parameter type.
    fn from_arg<'a>(
        value: &'a Value,
        storage: &mut Self::Storage<'a>,
    ) -> Result<Self::Param<'a>, Error>;
}

impl FromParam for &Value {
    type Storage<'a> = ();
    type Param<'a> = &'a Value;

    fn from_arg<'a>(
        value: &'a Value,
        _storage: &mut Self::Storage<'a>,
    ) -> Result<Self::Param<'a>, Error> {
        Ok(value)
    }
}

impl FromParam for i64 {
    type Storage<'a> = ();
    type Param<'a> = i64;

    fn from_arg<'a>(
        value: &'a Value,
        _storage: &mut Self::Storage<'a>,
    ) -> Result<Self::Param<'a>, Error> {
        if let Value::Number(n) = value {
            Ok(*n)
        } else {
            Err(Error::TypeError("expected number".into()))
        }
    }
}

impl FromParam for bool {
    type Storage<'a> = ();
    type Param<'a> = bool;

    fn from_arg<'a>(
        value: &'a Value,
        _storage: &mut Self::Storage<'a>,
    ) -> Result<Self::Param<'a>, Error> {
        if let Value::Bool(b) = value {
            Ok(*b)
        } else {
            Err(Error::TypeError("expected boolean".into()))
        }
    }
}

impl FromParam for &str {
    type Storage<'a> = ();
    type Param<'a> = &'a str;

    fn from_arg<'a>(
        value: &'a Value,
        _storage: &mut Self::Storage<'a>,
    ) -> Result<Self::Param<'a>, Error> {
        if let Value::String(s) = value {
            Ok(s.as_str())
        } else {
            Err(Error::TypeError("expected string".into()))
        }
    }
}

/// Widen the lifetime of a slice to match the higher-ranked lifetime
/// used by the fixed-arity adapters.
///
/// This function is the **only** place `unsafe` is used in the
/// argument-conversion machinery. It is private to this module and is
/// only called from `FromParam` and variadic rest-parameter
/// implementations for slice-like parameters.
///
/// # Safety
///
/// - The caller must ensure that the returned reference does not
///   outlive the stack frame that owns the backing storage of
///   `slice` (typically a local `Vec<T>`).
/// - In this module, that guarantee is provided by the fixed-arity
///   `IntoOperation` implementations: they allocate all `Storage`
///   values as locals, call `FromParam::from_arg` to create
///   `Param<'a>` values, immediately invoke the builtin `F`, and then
///   drop all `Storage` before returning.
/// - `Param<'a>` values are never stored in the returned
///   `OperationFn` closure or in any other longer-lived structure;
///   they are passed directly to the builtin and then discarded.
///
/// Rust's type system cannot currently express this "stack-bounded
/// borrow through a trait" pattern in a fully safe way, because the
/// trait uses a higher-ranked lifetime `for<'a>` while the actual
/// borrow from the local `Vec<T>` is tied to a particular call frame.
/// The combination of sealing, centralising this helper, and the
/// structure of the fixed-arity adapters is what makes this sound.
fn widen_slice_lifetime<'short, 'long, T>(slice: &'short [T]) -> &'long [T] {
    // SAFETY: Callers in this module uphold the safety contract above
    // by never letting the returned reference escape the adapter call
    // that owns the backing storage.
    unsafe { &*(slice as *const [T]) }
}

/// Typed list parameters for fixed-arity functions: a single
/// `Value::List` argument converted to a slice of elements.
impl FromParam for &[i64] {
    type Storage<'a> = Vec<i64>;
    type Param<'a> = &'a [i64];

    fn from_arg<'a>(
        value: &'a Value,
        storage: &mut Self::Storage<'a>,
    ) -> Result<Self::Param<'a>, Error> {
        storage.clear();
        let items = match value {
            Value::List(items) => items,
            _ => return Err(Error::TypeError("expected list".into())),
        };

        for item in items {
            match item {
                Value::Number(n) => storage.push(*n),
                _ => return Err(Error::TypeError("expected number in list".into())),
            }
        }

        let slice: &[i64] = storage.as_slice();
        let slice: &'a [i64] = widen_slice_lifetime(slice);
        Ok(slice)
    }
}

impl FromParam for &[bool] {
    type Storage<'a> = Vec<bool>;
    type Param<'a> = &'a [bool];

    fn from_arg<'a>(
        value: &'a Value,
        storage: &mut Self::Storage<'a>,
    ) -> Result<Self::Param<'a>, Error> {
        storage.clear();
        let items = match value {
            Value::List(items) => items,
            _ => return Err(Error::TypeError("expected list".into())),
        };

        for item in items {
            match item {
                Value::Bool(b) => storage.push(*b),
                _ => return Err(Error::TypeError("expected boolean in list".into())),
            }
        }

        let slice: &[bool] = storage.as_slice();
        let slice: &'a [bool] = widen_slice_lifetime(slice);
        Ok(slice)
    }
}

impl FromParam for &[&str] {
    type Storage<'a> = Vec<&'a str>;
    type Param<'a> = &'a [&'a str];

    fn from_arg<'a>(
        value: &'a Value,
        storage: &mut Self::Storage<'a>,
    ) -> Result<Self::Param<'a>, Error> {
        storage.clear();
        let items = match value {
            Value::List(items) => items,
            _ => return Err(Error::TypeError("expected list".into())),
        };

        for item in items {
            match item {
                Value::String(s) => storage.push(s.as_str()),
                _ => return Err(Error::TypeError("expected string in list".into())),
            }
        }

        let slice: &[&str] = storage.as_slice();
        let slice: &'a [&'a str] = widen_slice_lifetime(slice);
        Ok(slice)
    }
}

impl FromParam for &[Value] {
    type Storage<'a> = ();
    type Param<'a> = &'a [Value];

    fn from_arg<'a>(
        value: &'a Value,
        _storage: &mut Self::Storage<'a>,
    ) -> Result<Self::Param<'a>, Error> {
        if let Value::List(items) = value {
            Ok(items.as_slice())
        } else {
            Err(Error::TypeError("expected list".into()))
        }
    }
}

/// Convert strongly-typed Rust results into AST values.
pub trait IntoValue {
    fn into_value(self) -> Value;
}

impl IntoValue for Value {
    fn into_value(self) -> Value {
        self
    }
}

impl IntoValue for i64 {
    fn into_value(self) -> Value {
        Value::Number(self)
    }
}

impl IntoValue for bool {
    fn into_value(self) -> Value {
        Value::Bool(self)
    }
}

impl IntoValue for String {
    fn into_value(self) -> Value {
        Value::String(self)
    }
}

impl IntoValue for &str {
    fn into_value(self) -> Value {
        Value::String(self.to_owned())
    }
}

/// Normalize both plain values and `Result`-returning functions into `Result<T, Error>`.
pub trait IntoResult<T> {
    fn into_result(self) -> Result<T, Error>;
}

impl<T> IntoResult<T> for T
where
    T: IntoValue,
{
    fn into_result(self) -> Result<T, Error> {
        Ok(self)
    }
}

impl<T, E> IntoResult<T> for Result<T, E>
where
    E: Display,
{
    fn into_result(self) -> Result<T, Error> {
        self.map_err(|e| Error::EvalError(e.to_string()))
    }
}

/// Marker type for variadic "rest" parameters.
///
/// `Rest<T>` is a thin newtype over `Vec<T>` that behaves like a
/// slice via `Deref`/`AsRef`. Variadic adapters simply build a fresh
/// `Vec<T>` for the rest arguments and pass it to the user function;
/// no unsafe code or lifetime juggling is required.
#[derive(Debug, Clone)]
pub struct Rest<T> {
    items: Vec<T>,
}

impl<T> Rest<T> {
    pub(crate) fn new(items: Vec<T>) -> Self {
        Rest { items }
    }

    /// Borrow the rest arguments as a slice.
    pub fn as_slice(&self) -> &[T] {
        &self.items
    }

    /// Consume the wrapper and return the owned vector of rest
    /// arguments.
    pub fn into_vec(self) -> Vec<T> {
        self.items
    }
}

impl<T> std::ops::Deref for Rest<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.items
    }
}

impl<T> AsRef<[T]> for Rest<T> {
    fn as_ref(&self) -> &[T] {
        &self.items
    }
}

/// Internal trait used by the variadic adapters to convert the tail
/// of the argument list into a typed rest parameter.
///
/// The associated `Param<'a>` type is generic over the lifetime of the
/// underlying argument slice. Implementations for owned element types
/// (`Rest<i64>`, `Rest<bool>`) allocate a fresh `Vec<T>`; borrowed
/// variants like `Rest<&str>` borrow directly from the `Value`s.
trait FromRestParam {
    type Param<'a>;

    fn from_rest<'a>(values: &'a [Value]) -> Result<Self::Param<'a>, Error>;
}

/// Convert a strongly-typed Rust function or closure into the erased
/// [`OperationFn`], parameterized by an argument tuple type.
pub trait IntoOperation<Args, R> {
    fn into_operation(self) -> Arc<OperationFn>;
}

/// Marker trait for fixed-arity operations (no rest parameters).
///
/// Implemented for Rust functions and closures whose arguments are
/// drawn from types implementing [`FromParam`]. This is a thin wrapper
/// over [`IntoOperation`] so that the evaluator API can distinguish
/// fixed-arity from variadic registrations.
pub trait IntoFixedOperation<Args, R>: IntoOperation<Args, R> {}

impl<F, Args, R> IntoFixedOperation<Args, R> for F where F: IntoOperation<Args, R> {}

/// Trait for operations registered via the variadic API.
///
/// Implemented for functions whose Rust signature includes a variadic
/// "rest" parameter, expressed using the [`Rest`] marker type in the
/// last position of the argument tuple.
pub trait IntoVariadicOperation<Args, R> {
    fn into_variadic_operation(self) -> Arc<OperationFn>;
}

// =====================================================================
// Variadic helpers used by Rest-based adapters
// =====================================================================

// --- `FromRestParam` implementations for supported rest element types ---

// Numeric rest parameter: collects all numeric arguments into an owned
// `Vec<i64>` for convenient processing.
impl FromRestParam for Rest<i64> {
    type Param<'a> = Rest<i64>;

    fn from_rest<'a>(values: &'a [Value]) -> Result<Self::Param<'a>, Error> {
        let mut nums: Vec<i64> = Vec::new();

        for v in values {
            match v {
                Value::Number(n) => nums.push(*n),
                _ => return Err(Error::TypeError("expected number".into())),
            }
        }

        Ok(Rest::new(nums))
    }
}

// Boolean rest parameter: collects all boolean arguments into an owned
// `Vec<bool>`.
impl FromRestParam for Rest<bool> {
    type Param<'a> = Rest<bool>;

    fn from_rest<'a>(values: &'a [Value]) -> Result<Self::Param<'a>, Error> {
        let mut bools: Vec<bool> = Vec::new();

        for v in values {
            match v {
                Value::Bool(b) => bools.push(*b),
                _ => return Err(Error::TypeError("expected boolean".into())),
            }
        }

        Ok(Rest::new(bools))
    }
}
// Borrowed string rest parameter: builds a `Rest<&str>` borrowing string
// slices directly from the argument values.
impl FromRestParam for Rest<&str> {
    type Param<'a> = Rest<&'a str>;

    fn from_rest<'a>(values: &'a [Value]) -> Result<Self::Param<'a>, Error> {
        let mut items: Vec<&'a str> = Vec::new();

        for v in values {
            match v {
                Value::String(s) => items.push(s.as_str()),
                _ => return Err(Error::TypeError("expected string".into())),
            }
        }

        Ok(Rest::new(items))
    }
}

// --- 0-arg prefix: functions that see all args as the rest parameter ---

// Specialised implementation for `Rest<Value>` that **consumes** the
// incoming `Vec<Value>` without cloning. This is the most direct and
// allocation-free way to expose variadic arguments when the builtin is
// happy to own the `Value`s.
impl<F, FR, R> IntoVariadicOperation<(Rest<Value>,), R> for F
where
    F: Fn(Rest<Value>) -> FR + Send + Sync + 'static,
    FR: IntoResult<R> + 'static,
    R: IntoValue + 'static,
{
    fn into_variadic_operation(self) -> Arc<OperationFn> {
        Arc::new(move |args: Vec<Value>| {
            (|| {
                let rest_param = Rest::new(args);
                let result: FR = (self)(rest_param);
                let value: R = result.into_result()?;
                Ok(value.into_value())
            })()
        })
    }
}

// Generic implementation for rest-only functions using element types
// such as `Rest<i64>`, `Rest<bool>`, or `Rest<&str>`, built from a
// borrowed slice of the argument `Value`s via `FromRestParam`.
impl<F, FR, R, RestT> IntoVariadicOperation<(RestT,), R> for F
where
    RestT: FromRestParam,
    F: for<'a> Fn(<RestT as FromRestParam>::Param<'a>) -> FR + Send + Sync + 'static,
    FR: IntoResult<R> + 'static,
    R: IntoValue + 'static,
{
    fn into_variadic_operation(self) -> Arc<OperationFn> {
        Arc::new(move |args: Vec<Value>| {
            (|| {
                let rest_param = <RestT as FromRestParam>::from_rest(&args[..])?;
                let result: FR = (self)(rest_param);
                let value: R = result.into_result()?;
                Ok(value.into_value())
            })()
        })
    }
}

/// Helper macro to implement `IntoVariadicOperation` for functions with a fixed
/// prefix followed by a `Rest<_>` parameter in the last position.
///
/// The fixed prefix is handled via `FromParam` in exactly the same way
/// as the non-variadic adapters. The rest parameter is constructed via
/// `FromRestParam` from the remaining arguments.
macro_rules! impl_into_variadic_operation_for_prefix_and_rest {
    ($prefix:expr, $( $idx:tt => $v:ident, $p:ident : $A:ident ),+ ) => {
        impl<F, FR, R, RestT, $( $A ),+> IntoVariadicOperation<($( $A, )+ RestT,), R> for F
        where
            RestT: FromRestParam,
            $( $A: FromParam, )+
            F: for<'a> Fn(
                    $( <$A as FromParam>::Param<'a> ),+,
                    <RestT as FromRestParam>::Param<'a>,
                ) -> FR
                + Send
                + Sync
                + 'static,
            FR: IntoResult<R> + 'static,
            R: IntoValue + 'static,
        {
            fn into_variadic_operation(self) -> Arc<OperationFn> {
                Arc::new(move |args: Vec<Value>| {
                    match &args[..] {
                        [ $( $v ),+, rest @ .. ] => {
                            (|| {
                                let mut prefix_storage: (
                                    $( <$A as FromParam>::Storage<'_>, )+
                                ) = Default::default();

                                $(
                                    let $p: <$A as FromParam>::Param<'_> =
                                        <$A as FromParam>::from_arg(
                                            $v,
                                            &mut prefix_storage.$idx,
                                        )?;
                                )+

                                let rest_param = <RestT as FromRestParam>::from_rest(rest)?;

                                let result: FR = (self)( $( $p ),+, rest_param );
                                let value: R = result.into_result()?;
                                Ok(value.into_value())
                            })()
                        }
                        _ => Err(Error::arity_error($prefix, args.len())),
                    }
                })
            }
        }
    };
}

impl_into_variadic_operation_for_prefix_and_rest!(1, 0 => v0, p0: A1);
impl_into_variadic_operation_for_prefix_and_rest!(2, 0 => v0, p0: A1, 1 => v1, p1: A2);
impl_into_variadic_operation_for_prefix_and_rest!(3, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3);
impl_into_variadic_operation_for_prefix_and_rest!(4, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3, 3 => v3, p3: A4);
impl_into_variadic_operation_for_prefix_and_rest!(5, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3, 3 => v3, p3: A4, 4 => v4, p4: A5);
impl_into_variadic_operation_for_prefix_and_rest!(6, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3, 3 => v3, p3: A4, 4 => v4, p4: A5, 5 => v5, p5: A6);
impl_into_variadic_operation_for_prefix_and_rest!(7, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3, 3 => v3, p3: A4, 4 => v4, p4: A5, 5 => v5, p5: A6, 6 => v6, p6: A7);

/// Specialised prefix+rest implementations for `Rest<Value>` that
/// **consume** the incoming `Vec<Value>` tail without cloning. These
/// mirror the generic `impl_into_variadic_operation_for_prefix_and_rest`
/// macros but use `Vec::split_off` to move the rest arguments into a
/// fresh `Vec<Value>` that backs the `Rest<Value>` parameter.
macro_rules! impl_into_variadic_operation_for_prefix_and_rest_value {
    ($prefix:expr, $( $idx:tt => $v:ident, $p:ident : $A:ident ),+ ) => {
        impl<F, FR, R, $( $A ),+> IntoVariadicOperation<($( $A, )+ Rest<Value>,), R> for F
        where
            $( $A: FromParam, )+
            F: for<'a> Fn(
                    $( <$A as FromParam>::Param<'a> ),+,
                    Rest<Value>,
                ) -> FR
                + Send
                + Sync
                + 'static,
            FR: IntoResult<R> + 'static,
            R: IntoValue + 'static,
        {
            fn into_variadic_operation(self) -> Arc<OperationFn> {
                Arc::new(move |mut args: Vec<Value>| {
                    if args.len() < $prefix {
                        return Err(Error::arity_error($prefix, args.len()));
                    }

                    // Move the tail values into a fresh Vec backing
                    // the `Rest<Value>` parameter, leaving the prefix
                    // values in-place for `FromParam` to borrow from.
                    let rest_values = args.split_off($prefix);

                    match &args[..] {
                        [ $( $v ),+ ] => {
                            (|| {
                                let mut prefix_storage: (
                                    $( <$A as FromParam>::Storage<'_>, )+
                                ) = Default::default();

                                $(
                                    let $p: <$A as FromParam>::Param<'_> =
                                        <$A as FromParam>::from_arg(
                                            $v,
                                            &mut prefix_storage.$idx,
                                        )?;
                                )+

                                let rest_param = Rest::new(rest_values);
                                let result: FR = (self)( $( $p ),+, rest_param );
                                let value: R = result.into_result()?;
                                Ok(value.into_value())
                            })()
                        }
                        _ => Err(Error::arity_error($prefix, args.len())),
                    }
                })
            }
        }
    };
}

impl_into_variadic_operation_for_prefix_and_rest_value!(1, 0 => v0, p0: A1);
impl_into_variadic_operation_for_prefix_and_rest_value!(2, 0 => v0, p0: A1, 1 => v1, p1: A2);
impl_into_variadic_operation_for_prefix_and_rest_value!(3, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3);
impl_into_variadic_operation_for_prefix_and_rest_value!(4, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3, 3 => v3, p3: A4);
impl_into_variadic_operation_for_prefix_and_rest_value!(5, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3, 3 => v3, p3: A4, 4 => v4, p4: A5);
impl_into_variadic_operation_for_prefix_and_rest_value!(6, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3, 3 => v3, p3: A4, 4 => v4, p4: A5, 5 => v5, p5: A6);
impl_into_variadic_operation_for_prefix_and_rest_value!(7, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3, 3 => v3, p3: A4, 4 => v4, p4: A5, 5 => v5, p5: A6, 6 => v6, p6: A7);

// =====================================================================
// Fixed-arity adapters
// =====================================================================

/// Helper macro to implement `IntoOperation` for functions of various
/// arities using pattern matching on the argument slice.
///
/// This macro preserves the safety invariants relied upon by
/// `FromParam` and `widen_slice_lifetime` by:
/// - allocating all `Storage` values as locals inside the adapter;
/// - calling `FromParam::from_arg` to build `Param<'_>` for each
///   argument;
/// - immediately invoking the builtin function `F` with those
///   parameters; and
/// - dropping all storage before returning.
///
/// It also avoids the cascade of `get/expect` indexing by matching on
/// `&args[..]` to perform arity checking and destructuring in one
/// place.
///
/// This macro is the only place `FromParam::from_arg` is used for
/// fixed-arity builtins, so its structure (local storage tuple plus
/// immediate call) is part of the safety contract described on
/// `widen_slice_lifetime`.
macro_rules! impl_into_operation_for_arity {
    ($arity:expr, $( $idx:tt => $v:ident, $p:ident : $A:ident ),+ ) => {
        impl<F, FR, R, $( $A ),+> IntoOperation<($( $A, )+), R> for F
        where
            F: for<'a> Fn( $( <$A as FromParam>::Param<'a> ),+ ) -> FR
                + Send
                + Sync
                + 'static,
            FR: IntoResult<R> + 'static,
            R: IntoValue + 'static,
            $( $A: FromParam, )+
        {
            fn into_operation(self) -> Arc<OperationFn> {
                Arc::new(move |args: Vec<Value>| {
                    match &args[..] {
                        [ $( $v ),+ ] => {
                            (|| {
                                // Tuple of per-argument storage; for arity 1 this is a 1-tuple
                                // `(<A1 as FromParam>::Storage<'_>,)`.
                                let mut storage: (
                                    $( <$A as FromParam>::Storage<'_>, )+
                                ) = Default::default();

                                $(
                                    let $p: <$A as FromParam>::Param<'_> =
                                        <$A as FromParam>::from_arg(
                                            $v,
                                            &mut storage.$idx,
                                        )?;
                                )+

                                let result: FR = (self)( $( $p ),+ );
                                let value: R = result.into_result()?;
                                Ok(value.into_value())
                            })()
                        }
                        _ => Err(Error::arity_error($arity, args.len())),
                    }
                })
            }
        }
    };
}

// 0-arg functions / closures
impl<F, FR, R> IntoOperation<(), R> for F
where
    F: Fn() -> FR + Send + Sync + 'static,
    FR: IntoResult<R> + 'static,
    R: IntoValue + 'static,
{
    fn into_operation(self) -> Arc<OperationFn> {
        Arc::new(move |args: Vec<Value>| {
            if !args.is_empty() {
                return Err(Error::arity_error(0, args.len()));
            }

            let result: FR = (self)();
            let value: R = result.into_result()?;
            Ok(value.into_value())
        })
    }
}

impl_into_operation_for_arity!(1, 0 => v0, p0: A1);
impl_into_operation_for_arity!(2, 0 => v0, p0: A1, 1 => v1, p1: A2);
impl_into_operation_for_arity!(3, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3);
impl_into_operation_for_arity!(4, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3, 3 => v3, p3: A4);
impl_into_operation_for_arity!(5, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3, 3 => v3, p3: A4, 4 => v4, p4: A5);
impl_into_operation_for_arity!(6, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3, 3 => v3, p3: A4, 4 => v4, p4: A5, 5 => v5, p5: A6);
impl_into_operation_for_arity!(7, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3, 3 => v3, p3: A4, 4 => v4, p4: A5, 5 => v5, p5: A6, 6 => v6, p6: A7);
impl_into_operation_for_arity!(8, 0 => v0, p0: A1, 1 => v1, p1: A2, 2 => v2, p2: A3, 3 => v3, p3: A4, 4 => v4, p4: A5, 5 => v5, p5: A6, 6 => v6, p6: A7, 7 => v7, p7: A8);
