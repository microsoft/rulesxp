use crate::Error;
use crate::ast::Value;
use std::fmt::Display;
use std::iter::FusedIterator;
use std::sync::Arc;

/// Canonical erased builtin function type used by the evaluator.
///
/// Builtins receive ownership of their argument vector, enabling
/// implementations that consume or rearrange arguments if desired.
pub type OperationFn = dyn Fn(Vec<Value>) -> Result<Value, Error> + Send + Sync;

// =====================================================================
// Internal machinery for fixed-arity argument conversion
//
// This module defines `FromParam`, which is used by the fixed-arity
// adapters to turn AST `Value` nodes into strongly-typed Rust
// parameters. All conversions are implemented here so that the
// supported parameter types are easy to audit.
// =====================================================================

/// Core trait used by the fixed-arity adapters to turn `Value` nodes
/// into strongly-typed parameters.
///
/// The associated `Param<'a>` type is the parameter type as seen by
/// the builtin for a given lifetime of the local `Value` slots used
/// during argument conversion.
pub(crate) trait FromParam {
    /// The parameter type as seen by the builtin for a given lifetime
    /// of the underlying AST values.
    type Param<'a>;

    /// Convert a single AST argument into this parameter type.
    ///
    /// Implementations may either borrow from the provided `Value`
    /// (for types such as `&str` and the borrowed iterators), or
    /// consume it by value (for `Value` itself).
    fn from_arg<'a>(value: &'a mut Value) -> Result<Self::Param<'a>, Error>;
}

impl FromParam for Value {
    type Param<'a> = Value;

    fn from_arg<'a>(value: &'a mut Value) -> Result<Self::Param<'a>, Error> {
        // Move the `Value` out so that builtin functions can consume
        // owned payloads (such as strings or lists) without cloning.
        Ok(std::mem::replace(value, Value::Unspecified))
    }
}

// Blanket implementation for by-value primitive parameters that can be
// obtained from a `Value` via the standard `TryInto` trait. This covers
// types such as `i64` and `bool` for which we provide
// `impl TryInto<T> for Value` in `ast.rs`.
impl<T> FromParam for T
where
    Value: std::convert::TryInto<T, Error = Error>,
{
    type Param<'a> = T;

    fn from_arg<'a>(value: &'a mut Value) -> Result<Self::Param<'a>, Error> {
        let owned = std::mem::replace(value, Value::Unspecified);
        <Value as std::convert::TryInto<T>>::try_into(owned)
    }
}

impl FromParam for &str {
    type Param<'a> = &'a str;

    fn from_arg<'a>(value: &'a mut Value) -> Result<Self::Param<'a>, Error> {
        if let Value::String(s) = value {
            Ok(s.as_str())
        } else {
            Err(Error::TypeError("expected string".into()))
        }
    }
}

// No slice-based `FromParam` implementations are provided in the
// iterator-based design. If a builtin needs to work with lists or
// rest-style arguments it should use the iterator-based parameters
// defined below instead.

// =====================================================================
// FromParam support for iterator parameters (list arguments)
// =====================================================================

impl<'b> FromParam for ValueListIterator<'b> {
    type Param<'a> = ValueListIterator<'a>;

    fn from_arg<'a>(value: &'a mut Value) -> Result<Self::Param<'a>, Error> {
        if let Value::List(items) = value {
            Ok(ValueListIterator::new(items.as_slice()))
        } else {
            Err(Error::TypeError("expected list".into()))
        }
    }
}

impl<'b> FromParam for NumIterator<'b> {
    type Param<'a> = NumIterator<'a>;

    fn from_arg<'a>(value: &'a mut Value) -> Result<Self::Param<'a>, Error> {
        if let Value::List(items) = value {
            NumIterator::new(items.as_slice())
        } else {
            Err(Error::TypeError("expected list".into()))
        }
    }
}

impl<'b> FromParam for BoolIterator<'b> {
    type Param<'a> = BoolIterator<'a>;

    fn from_arg<'a>(value: &'a mut Value) -> Result<Self::Param<'a>, Error> {
        if let Value::List(items) = value {
            BoolIterator::new(items.as_slice())
        } else {
            Err(Error::TypeError("expected list".into()))
        }
    }
}

impl<'b> FromParam for StringIterator<'b> {
    type Param<'a> = StringIterator<'a>;

    fn from_arg<'a>(value: &'a mut Value) -> Result<Self::Param<'a>, Error> {
        if let Value::List(items) = value {
            StringIterator::new(items.as_slice())
        } else {
            Err(Error::TypeError("expected list".into()))
        }
    }
}

/// Normalize both plain values and `Result`-returning functions into `Result<T, Error>`.
pub trait IntoResult<T> {
    fn into_result(self) -> Result<T, Error>;
}

impl<T> IntoResult<T> for T {
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

// =====================================================================
// Iterator-based parameter types
// =====================================================================

/// Borrowed iterator over a sequence of AST `Value` references.
///
/// This is the shared base type for all list/sequence-parameter
/// iterators. Typed iterators such as [`NumIterator`], [`BoolIterator`]
/// and [`StringIterator`] wrap this to provide element-level typing.
#[derive(Debug, Clone, Copy)]
pub struct ValueListIterator<'a> {
    values: &'a [Value],
    index: usize,
}

impl<'a> ValueListIterator<'a> {
    pub(crate) fn new(values: &'a [Value]) -> Self {
        ValueListIterator { values, index: 0 }
    }
}

impl<'a> Iterator for ValueListIterator<'a> {
    type Item = &'a Value;

    fn next(&mut self) -> Option<Self::Item> {
        let v = self.values.get(self.index)?;
        self.index += 1;
        Some(v)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.values.len().saturating_sub(self.index);
        (remaining, Some(remaining))
    }
}

impl<'a> ExactSizeIterator for ValueListIterator<'a> {}
impl<'a> FusedIterator for ValueListIterator<'a> {}

/// Borrowed iterator over numeric arguments, performing type checking
/// as elements are pulled. Internally this wraps a [`ValueListIterator`]
/// and narrows each element to `i64`.
#[derive(Debug, Clone, Copy)]
pub struct NumIterator<'a> {
    inner: ValueListIterator<'a>,
}

impl<'a> NumIterator<'a> {
    /// Build a numeric iterator over the provided values, performing a
    /// single upfront type check that all elements are numbers.
    pub(crate) fn new(values: &'a [Value]) -> Result<Self, Error> {
        for v in values {
            if !matches!(v, Value::Number(_)) {
                return Err(Error::TypeError("expected number".into()));
            }
        }

        Ok(NumIterator {
            inner: ValueListIterator::new(values),
        })
    }
}

impl<'a> Iterator for NumIterator<'a> {
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        let v = self.inner.next()?;

        if let Value::Number(n) = v {
            Some(*n)
        } else {
            // `new` guarantees all elements are numbers.
            debug_assert!(false, "NumIterator saw non-number after construction");
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a> ExactSizeIterator for NumIterator<'a> {}
impl<'a> FusedIterator for NumIterator<'a> {}

/// Borrowed iterator over boolean arguments, performing type checking
/// as elements are pulled. Internally this wraps a
/// [`ValueListIterator`] and narrows each element to `bool`.
#[derive(Debug, Clone, Copy)]
pub struct BoolIterator<'a> {
    inner: ValueListIterator<'a>,
}

impl<'a> BoolIterator<'a> {
    /// Build a boolean iterator over the provided values, performing a
    /// single upfront type check that all elements are booleans.
    pub(crate) fn new(values: &'a [Value]) -> Result<Self, Error> {
        for v in values {
            if !matches!(v, Value::Bool(_)) {
                return Err(Error::TypeError("expected boolean".into()));
            }
        }

        Ok(BoolIterator {
            inner: ValueListIterator::new(values),
        })
    }
}

impl<'a> Iterator for BoolIterator<'a> {
    type Item = bool;

    fn next(&mut self) -> Option<Self::Item> {
        let v = self.inner.next()?;

        if let Value::Bool(b) = v {
            Some(*b)
        } else {
            // `new` guarantees all elements are booleans.
            debug_assert!(false, "BoolIterator saw non-boolean after construction");
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a> ExactSizeIterator for BoolIterator<'a> {}
impl<'a> FusedIterator for BoolIterator<'a> {}

/// Borrowed iterator over string arguments, performing type checking
/// as elements are pulled. Internally this wraps a
/// [`ValueListIterator`] and narrows each element to `&str`.
#[derive(Debug, Clone, Copy)]
pub struct StringIterator<'a> {
    inner: ValueListIterator<'a>,
}

impl<'a> StringIterator<'a> {
    /// Build a string iterator over the provided values, performing a
    /// single upfront type check that all elements are strings.
    pub(crate) fn new(values: &'a [Value]) -> Result<Self, Error> {
        for v in values {
            if !matches!(v, Value::String(_)) {
                return Err(Error::TypeError("expected string".into()));
            }
        }

        Ok(StringIterator {
            inner: ValueListIterator::new(values),
        })
    }
}

impl<'a> Iterator for StringIterator<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        let v = self.inner.next()?;

        if let Value::String(s) = v {
            Some(s.as_str())
        } else {
            // `new` guarantees all elements are strings.
            debug_assert!(false, "StringIterator saw non-string after construction");
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a> ExactSizeIterator for StringIterator<'a> {}
impl<'a> FusedIterator for StringIterator<'a> {}

// =====================================================================
// Rest-parameter support for variadic operations
// =====================================================================

/// Core trait used to construct rest-parameter values from a slice of
/// AST arguments.
///
/// The associated `Param<'a>` is the type actually seen by the builtin
/// function for a given lifetime of the underlying value slice.
pub(crate) trait FromRest {
    type Param<'a>;

    fn from_rest<'a>(slice: &'a [Value]) -> Result<Self::Param<'a>, Error>;
}

impl FromRest for ValueListIterator<'static> {
    type Param<'a> = ValueListIterator<'a>;

    fn from_rest<'a>(slice: &'a [Value]) -> Result<Self::Param<'a>, Error> {
        Ok(ValueListIterator::new(slice))
    }
}

impl FromRest for NumIterator<'static> {
    type Param<'a> = NumIterator<'a>;

    fn from_rest<'a>(slice: &'a [Value]) -> Result<Self::Param<'a>, Error> {
        NumIterator::new(slice)
    }
}

impl FromRest for BoolIterator<'static> {
    type Param<'a> = BoolIterator<'a>;

    fn from_rest<'a>(slice: &'a [Value]) -> Result<Self::Param<'a>, Error> {
        BoolIterator::new(slice)
    }
}

impl FromRest for StringIterator<'static> {
    type Param<'a> = StringIterator<'a>;

    fn from_rest<'a>(slice: &'a [Value]) -> Result<Self::Param<'a>, Error> {
        StringIterator::new(slice)
    }
}

/// Marker type used in `Args` tuples to indicate that a parameter
/// position is populated from the variadic "rest" arguments using
/// [`FromRest`].
#[derive(Debug, Clone, Copy)]
pub struct Rest<I>(std::marker::PhantomData<I>);

// Convenience aliases for common rest-parameter iterator types used in
// tests and documentation. These are only used at the type level; the
// actual parameters seen by builtin functions are the lifetime-
// parameterised iterator types above.
pub type ValuesRest = Rest<ValueListIterator<'static>>;
pub type NumRest = Rest<NumIterator<'static>>;
pub type BoolRest = Rest<BoolIterator<'static>>;
pub type StringRest = Rest<StringIterator<'static>>;

/// Convert a strongly-typed Rust function or closure into the erased
/// [`OperationFn`], parameterized by an argument tuple type.
pub trait IntoOperation<Args, R> {
    fn into_operation(self) -> Arc<OperationFn>;
}

/// Trait for operations registered via the variadic API.
///
/// Implemented for functions whose Rust signature includes a variadic
/// "rest" parameter, expressed using the iterator types defined in
/// this module (`ValueListIterator<'a>`, `NumIterator<'a>`,
/// `BoolIterator<'a>`, or `StringIterator<'a>`), optionally after a
/// fixed prefix of `FromParam` parameters.
pub trait IntoVariadicOperation<Args, R> {
    fn into_variadic_operation(self) -> Arc<OperationFn>;
}

// =====================================================================
// Variadic adapters using iterator-based rest parameters
// =====================================================================

/// Adapter for functions whose Rust signature consists only of a rest
/// parameter expressed via one of the iterator types in this module
/// (e.g. `ValueListIterator<'a>`, `NumIterator<'a>`, etc.).
impl<F, FR, R, I> IntoVariadicOperation<(Rest<I>,), R> for F
where
    I: FromRest,
    F: for<'a> Fn(<I as FromRest>::Param<'a>) -> FR + Send + Sync + 'static,
    FR: IntoResult<R> + 'static,
    R: Into<Value> + 'static,
{
    fn into_variadic_operation(self) -> Arc<OperationFn> {
        Arc::new(move |args: Vec<Value>| {
            let rest_param: <I as FromRest>::Param<'_> = <I as FromRest>::from_rest(&args[..])?;
            let result: FR = (self)(rest_param);
            let value: R = result.into_result()?;
            Ok(value.into())
        })
    }
}

/// Helper macro to implement `IntoVariadicOperation` for functions with
/// a fixed prefix of `FromParam` parameters followed by a single rest
/// parameter expressed using one of the iterator types in this module.
macro_rules! impl_into_variadic_operation_for_prefix_and_rest {
    ($prefix:expr, $( $v:ident, $p:ident : $A:ident ),+ ) => {
        impl<F, FR, R, I, $( $A ),+> IntoVariadicOperation<( $( $A, )+ Rest<I>, ), R> for F
        where
            I: FromRest,
            $( $A: FromParam, )+
            F: for<'a> Fn(
                    $( <$A as FromParam>::Param<'a> ),+,
                    <I as FromRest>::Param<'a>,
                ) -> FR
                + Send
                + Sync
                + 'static,
            FR: IntoResult<R> + 'static,
            R: Into<Value> + 'static,
        {
            fn into_variadic_operation(self) -> Arc<OperationFn> {
                Arc::new(move |mut args: Vec<Value>| {
                    let len = args.len();
                    match args.as_mut_slice() {
                        &mut [ $( ref mut $v ),+, ref mut rest @ .. ] => {
                            $(
                                let $p: <$A as FromParam>::Param<'_> =
                                    <$A as FromParam>::from_arg($v)?;
                            )+

                            let rest_param: <I as FromRest>::Param<'_> =
                                <I as FromRest>::from_rest(&*rest)?;

                            let result: FR = (self)( $( $p ),+, rest_param );
                            let value: R = result.into_result()?;
                            Ok(value.into())
                        }
                        _ => Err(Error::arity_error($prefix, len)),
                    }
                })
            }
        }
    };
}

impl_into_variadic_operation_for_prefix_and_rest!(1, v0, p0: A1);
impl_into_variadic_operation_for_prefix_and_rest!(2, v0, p0: A1, v1, p1: A2);
impl_into_variadic_operation_for_prefix_and_rest!(3, v0, p0: A1, v1, p1: A2, v2, p2: A3);
impl_into_variadic_operation_for_prefix_and_rest!(4, v0, p0: A1, v1, p1: A2, v2, p2: A3, v3, p3: A4);
impl_into_variadic_operation_for_prefix_and_rest!(5, v0, p0: A1, v1, p1: A2, v2, p2: A3, v3, p3: A4, v4, p4: A5);
impl_into_variadic_operation_for_prefix_and_rest!(6, v0, p0: A1, v1, p1: A2, v2, p2: A3, v3, p3: A4, v4, p4: A5, v5, p5: A6);
impl_into_variadic_operation_for_prefix_and_rest!(7, v0, p0: A1, v1, p1: A2, v2, p2: A3, v3, p3: A4, v4, p4: A5, v5, p5: A6, v6, p6: A7);

// =====================================================================
// Fixed-arity adapters
// =====================================================================

/// Helper macro to implement `IntoOperation` for functions of various
/// arities.
///
/// It performs arity checking up front, then destructures the owned
/// `Vec<Value>` into local `Value` slots so that `FromParam` can either
/// borrow from or consume each argument as needed before invoking the
/// builtin function.
macro_rules! impl_into_operation_for_arity {
    ($arity:expr, $( $v:ident, $p:ident : $A:ident ),+ ) => {
        impl<F, FR, R, $( $A ),+> IntoOperation<( $( $A, )+ ), R> for F
        where
            F: for<'a> Fn( $( <$A as FromParam>::Param<'a> ),+ ) -> FR
                + Send
                + Sync
                + 'static,
            FR: IntoResult<R> + 'static,
            R: Into<Value> + 'static,
            $( $A: FromParam, )+
        {
            fn into_operation(self) -> Arc<OperationFn> {
                Arc::new(move |mut args: Vec<Value>| {
                    let len = args.len();
                    match args.as_mut_slice() {
                        &mut [ $( ref mut $v ),+ ] => {
                            $(
                                let $p: <$A as FromParam>::Param<'_> =
                                    <$A as FromParam>::from_arg($v)?;
                            )+

                            let result: FR = (self)( $( $p ),+ );
                            let value: R = result.into_result()?;
                            Ok(value.into())
                        }
                        _ => Err(Error::arity_error($arity, len)),
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
    R: Into<Value> + 'static,
{
    fn into_operation(self) -> Arc<OperationFn> {
        Arc::new(move |args: Vec<Value>| {
            if !args.is_empty() {
                return Err(Error::arity_error(0, args.len()));
            }

            let result: FR = (self)();
            let value: R = result.into_result()?;
            Ok(value.into())
        })
    }
}

impl_into_operation_for_arity!(1, v0, p0: A1);
impl_into_operation_for_arity!(2, v0, p0: A1, v1, p1: A2);
impl_into_operation_for_arity!(3, v0, p0: A1, v1, p1: A2, v2, p2: A3);
impl_into_operation_for_arity!(4, v0, p0: A1, v1, p1: A2, v2, p2: A3, v3, p3: A4);
impl_into_operation_for_arity!(5, v0, p0: A1, v1, p1: A2, v2, p2: A3, v3, p3: A4, v4, p4: A5);
impl_into_operation_for_arity!(6, v0, p0: A1, v1, p1: A2, v2, p2: A3, v3, p3: A4, v4, p4: A5, v5, p5: A6);
impl_into_operation_for_arity!(7, v0, p0: A1, v1, p1: A2, v2, p2: A3, v3, p3: A4, v4, p4: A5, v5, p5: A6, v6, p6: A7);
impl_into_operation_for_arity!(8, v0, p0: A1, v1, p1: A2, v2, p2: A3, v3, p3: A4, v4, p4: A5, v5, p5: A6, v6, p6: A7, v7, p7: A8);
