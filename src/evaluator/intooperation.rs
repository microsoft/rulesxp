use crate::Error;
use crate::ast::Value;
use std::iter::FusedIterator;
use std::marker::PhantomData;
use std::sync::Arc;

// NOTE: This module is internal plumbing for the evaluator.
// It defines the adapter layer that turns strongly-typed Rust
// functions into the erased `OperationFn` used at runtime.
//
// External users should interact with `Environment` and the
// registration APIs in `evaluator.rs`; this module is kept
// crate-private but retains rich comments for maintainers.

/// Canonical erased builtin function type used by the evaluator.
///
/// Builtins receive ownership of their argument vector, enabling
/// implementations that consume or rearrange arguments if desired.
pub(crate) type OperationFn = dyn Fn(Vec<Value>) -> Result<Value, Error> + Send + Sync;

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

impl<'b, K> FromParam for TypedValueIter<'b, K>
where
    K: ValueElementKind,
{
    type Param<'a> = TypedValueIter<'a, K>;

    fn from_arg<'a>(value: &'a mut Value) -> Result<Self::Param<'a>, Error> {
        if let Value::List(items) = value {
            TypedValueIter::<K>::new(items.as_slice())
        } else {
            Err(Error::TypeError("expected list".into()))
        }
    }
}

// =====================================================================
// Generic typed iterator built on top of the standard slice iterator
// =====================================================================

/// Marker trait describing how to view a `Value` slice as a typed
/// iterator. Implementations perform any necessary upfront validation
/// and map each `Value` to the element type.
#[doc(hidden)]
pub trait ValueElementKind {
    type Item<'a>;

    fn precheck(slice: &[Value]) -> Result<(), Error>;
    fn project<'a>(v: &'a Value) -> Self::Item<'a>;
}

/// Generic iterator over a list of `Value`s, parameterized by a
/// [`ValueElementKind`] that determines the element type and
/// validation.
#[doc(hidden)]
pub struct TypedValueIter<'a, K: ValueElementKind> {
    inner: std::slice::Iter<'a, Value>,
    _marker: PhantomData<K>,
}

impl<'a, K> TypedValueIter<'a, K>
where
    K: ValueElementKind,
{
    pub(crate) fn new(values: &'a [Value]) -> Result<Self, Error> {
        K::precheck(values)?;
        Ok(TypedValueIter {
            inner: values.iter(),
            _marker: PhantomData,
        })
    }
}

impl<'a, K> Iterator for TypedValueIter<'a, K>
where
    K: ValueElementKind,
{
    type Item = K::Item<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let v = self.inner.next()?;
        Some(K::project(v))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a, K> ExactSizeIterator for TypedValueIter<'a, K> where K: ValueElementKind {}
impl<'a, K> FusedIterator for TypedValueIter<'a, K> where K: ValueElementKind {}

// Concrete element kinds and their iterator aliases

/// Element kind that views each `Value` as a borrowed reference,
/// used for iterating over raw AST values.
#[doc(hidden)]
pub struct ValueKind;

impl ValueElementKind for ValueKind {
    type Item<'a> = &'a Value;

    fn precheck(_slice: &[Value]) -> Result<(), Error> {
        Ok(())
    }

    fn project<'a>(v: &'a Value) -> Self::Item<'a> {
        v
    }
}

#[doc(hidden)]
pub struct NumberKind;

impl ValueElementKind for NumberKind {
    type Item<'a> = i64;

    fn precheck(slice: &[Value]) -> Result<(), Error> {
        for v in slice {
            if !matches!(v, Value::Number(_)) {
                return Err(Error::TypeError("expected number".into()));
            }
        }
        Ok(())
    }

    fn project<'a>(v: &'a Value) -> Self::Item<'a> {
        if let Value::Number(n) = v {
            *n
        } else {
            debug_assert!(false, "NumberKind::project saw non-number after precheck");
            unreachable!("NumberKind invariant violated")
        }
    }
}

#[doc(hidden)]
pub struct BoolKind;

impl ValueElementKind for BoolKind {
    type Item<'a> = bool;

    fn precheck(slice: &[Value]) -> Result<(), Error> {
        for v in slice {
            if !matches!(v, Value::Bool(_)) {
                return Err(Error::TypeError("expected boolean".into()));
            }
        }
        Ok(())
    }

    fn project<'a>(v: &'a Value) -> Self::Item<'a> {
        if let Value::Bool(b) = v {
            *b
        } else {
            debug_assert!(false, "BoolKind::project saw non-boolean after precheck");
            unreachable!("BoolKind invariant violated")
        }
    }
}

#[doc(hidden)]
pub struct StringKind;

impl ValueElementKind for StringKind {
    type Item<'a> = &'a str;

    fn precheck(slice: &[Value]) -> Result<(), Error> {
        for v in slice {
            if !matches!(v, Value::String(_)) {
                return Err(Error::TypeError("expected string".into()));
            }
        }
        Ok(())
    }

    fn project<'a>(v: &'a Value) -> Self::Item<'a> {
        if let Value::String(s) = v {
            s.as_str()
        } else {
            debug_assert!(false, "StringKind::project saw non-string after precheck");
            unreachable!("StringKind invariant violated")
        }
    }
}

/// Borrowed iterator over a sequence of AST `Value` references.
///
/// This is the shared base type for all list/sequence-parameter
/// iterators. Typed iterators such as [`NumIter`], [`BoolIter`]
/// and [`StringIter`] are specializations that provide
/// element-level typing.
pub type ValueIter<'a> = TypedValueIter<'a, ValueKind>;

/// Borrowed iterator over numeric arguments, performing type checking
/// as elements are pulled. Internally this is a specialization of
/// [`TypedValueIter`] that narrows each element to `i64`.
pub type NumIter<'a> = TypedValueIter<'a, NumberKind>;

/// Borrowed iterator over boolean arguments, performing type checking
/// as elements are pulled. Internally this is a specialization of
/// [`TypedValueIter`] that narrows each element to `bool`.
pub type BoolIter<'a> = TypedValueIter<'a, BoolKind>;

/// Borrowed iterator over string arguments, performing type checking
/// as elements are pulled. Internally this is a specialization of
/// [`TypedValueIter`] that narrows each element to `&str`.
pub type StringIter<'a> = TypedValueIter<'a, StringKind>;

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

impl<K> FromRest for TypedValueIter<'static, K>
where
    K: ValueElementKind,
{
    type Param<'a> = TypedValueIter<'a, K>;

    fn from_rest<'a>(slice: &'a [Value]) -> Result<Self::Param<'a>, Error> {
        TypedValueIter::<K>::new(slice)
    }
}

// =====================================================================
// Return-type adaptation for builtin functions
// =====================================================================

/// Internal trait that normalizes builtin return types to the
/// canonical `Result<Value, Error>` expected by the evaluator.
///
/// Builtins typically return either `Result<Value, Error>` directly
/// or `Result<T, Error>` for some `T` that implements `Into<Value>`.
pub(crate) trait IntoValueResult {
    fn into_value_result(self) -> Result<Value, Error>;
}

impl<T> IntoValueResult for Result<T, Error>
where
    T: Into<Value>,
{
    fn into_value_result(self) -> Result<Value, Error> {
        self.map(Into::into)
    }
}

impl<T> IntoValueResult for T
where
    T: Into<Value>,
{
    fn into_value_result(self) -> Result<Value, Error> {
        Ok(self.into())
    }
}

/// Public trait for converting strongly-typed Rust functions or
/// closures into the erased [`OperationFn`], parameterized by an
/// argument tuple type.
///
/// Builtins implemented via this trait may return any type `R` that
/// implements [`IntoValueResult`], typically `Result<Value, Error>`
/// or `Result<T, Error>` where `T: Into<Value>`.
pub(crate) trait IntoOperation<Args> {
    fn into_operation(self) -> Arc<OperationFn>;
}

/// Trait for operations registered via the variadic API.
///
/// Implemented for functions whose Rust signature includes a variadic
/// "rest" parameter, expressed using the iterator types defined in
/// this module (`ValueIter<'a>`, `NumIter<'a>`,
/// `BoolIter<'a>`, or `StringIter<'a>`), optionally after a
/// fixed prefix of `FromParam` parameters.
pub(crate) trait IntoVariadicOperation<Args> {
    fn into_variadic_operation(self) -> Arc<OperationFn>;
}

// =====================================================================
// Variadic adapters using iterator-based rest parameters
// =====================================================================

/// Adapter for functions whose Rust signature consists only of a rest
/// parameter expressed via one of the iterator types in this module
/// (e.g. `ValueIter<'a>`, `NumIter<'a>`, etc.).
impl<F, I, R> IntoVariadicOperation<(I,)> for F
where
    I: FromRest,
    F: for<'a> Fn(<I as FromRest>::Param<'a>) -> R + Send + Sync + 'static,
    R: IntoValueResult,
{
    fn into_variadic_operation(self) -> Arc<OperationFn> {
        Arc::new(move |args: Vec<Value>| {
            let rest_param: <I as FromRest>::Param<'_> = <I as FromRest>::from_rest(&args[..])?;
            let result: R = (self)(rest_param);
            result.into_value_result()
        })
    }
}

/// Helper macro to implement `IntoVariadicOperation` for functions
/// with a fixed prefix of `FromParam` parameters followed by a single
/// rest parameter expressed using one of the iterator types in this
/// module.
macro_rules! impl_into_variadic_operation_for_prefix_and_rest {
    ($prefix:expr, $( $v:ident, $p:ident : $A:ident ),+ ) => {
        impl<F, I, R, $( $A ),+> IntoVariadicOperation<( $( $A, )+ I, )> for F
        where
            I: FromRest,
            $( $A: FromParam, )+
            F: for<'a> Fn(
                    $( <$A as FromParam>::Param<'a> ),+,
                    <I as FromRest>::Param<'a>,
                ) -> R
                + Send
                + Sync
                + 'static,
            R: IntoValueResult,
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

                            let result: R = (self)( $( $p ),+, rest_param );
                            result.into_value_result()
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
        impl<F, R, $( $A ),+> IntoOperation<( $( $A, )+ )> for F
        where
            F: for<'a> Fn( $( <$A as FromParam>::Param<'a> ),+ ) -> R
                + Send
                + Sync
                + 'static,
            $( $A: FromParam, )+
            R: IntoValueResult,
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

                            let result: R = (self)( $( $p ),+ );
                            result.into_value_result()
                        }
                        _ => Err(Error::arity_error($arity, len)),
                    }
                })
            }
        }
    };
}

// 0-arg functions / closures
impl<F, R> IntoOperation<()> for F
where
    F: Fn() -> R + Send + Sync + 'static,
    R: IntoValueResult,
{
    fn into_operation(self) -> Arc<OperationFn> {
        Arc::new(move |args: Vec<Value>| {
            if !args.is_empty() {
                return Err(Error::arity_error(0, args.len()));
            }

            let result: R = (self)();
            result.into_value_result()
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
