//! This crate provides the boolean algebra based types [`True`] and [`False] as enum values.
//! They serve a similar purpose as the built-in primitive boolean types `true` and  `false`
//! respectively (but are not interchangeable).
//!
//! [`True`]: enum.Boolean.html#variant.True
//! [`False`]: enum.Boolean.html#variant.False

#![no_std]

#[cfg(feature = "has_alloc")]
extern crate alloc;

use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};
use core::str::FromStr;

#[cfg(global_values)]
#[allow(non_upper_case_globals)]
pub static True: Boolean = Boolean::True;

#[cfg(global_values)]
#[allow(non_upper_case_globals)]
pub static False: Boolean = Boolean::False;

/// Enum with two possible values: `True` or `False` which represent the [`logical`]
/// values `true` and `false` respectively.
///
/// [`logical`]: https://en.wikipedia.org/wiki/Boolean_algebra
#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub enum Boolean {
    False,
    True,
}

impl Boolean {
    /// Creates a `Boolean` based on the given primitive `bool`.
    /// If the value is `true`, it will return `Boolean::True` and
    /// if the value is`false` will return `Boolean::False`
    pub fn new(value: bool) -> Self {
        if value {
            Self::True
        } else {
            Self::False
        }
    }

    /// The logical [`and`] operation.
    ///
    /// Truth table:
    ///
    /// | self | rhs | output |
    /// |------|-----|--------|
    /// | [`True`]  | [`True`]  | [`True`]  |
    /// | [`True`]  | [`False`] | [`False`] |
    /// | [`False`] | [`True`]  | [`False`] |
    /// | [`False`] | [`False`] | [`False`] |
    ///
    ///
    /// [`True`]: enum.Boolean.html#variant.True
    /// [`False`]: enum.Boolean.html#variant.False
    /// [`and`]: https://en.wikipedia.org/wiki/Boolean_algebra#Operations
    #[inline]
    pub fn and<R: Into<Self>>(self, rhs: R) -> Self {
        let rhs = rhs.into();
        if self == Self::False || rhs == Self::False {
            Self::False
        } else {
            Self::True
        }
    }

    /// The logical [`or`] operation.
    ///
    /// Truth table:
    ///
    /// | self | rhs | output |
    /// |------|-----|--------|
    /// | [`True`]  | [`True`]  | [`True`]  |
    /// | [`True`]  | [`False`] | [`True`]  |
    /// | [`False`] | [`True`]  | [`True`]  |
    /// | [`False`] | [`False`] | [`False`] |
    ///
    ///
    /// [`True`]: enum.Boolean.html#variant.True
    /// [`False`]: enum.Boolean.html#variant.False
    /// [`or`]: https://en.wikipedia.org/wiki/Boolean_algebra#Operations
    #[inline]
    pub fn or<R: Into<Self>>(self, rhs: R) -> Self {
        let rhs = rhs.into();
        if self != Self::False || rhs != Self::False {
            Self::True
        } else {
            Self::False
        }
    }

    /// The logical [`not`] operation.
    ///
    /// Truth table:
    ///
    /// | self | output |
    /// |------|--------|
    /// | [`True`]  | [`False`]  |
    /// | [`False`]  | [`True`]  |
    ///
    ///
    /// [`True`]: enum.Boolean.html#variant.True
    /// [`False`]: enum.Boolean.html#variant.False
    /// [`not`]: https://en.wikipedia.org/wiki/Boolean_algebra#Operations
    #[inline]
    pub fn not(self) -> Self {
        if self == Self::True {
            Self::False
        } else {
            Self::True
        }
    }

    /// The logical [`implication`] operation.
    ///
    /// Truth table:
    ///
    /// | self | rhs | output |
    /// |------|-----|--------|
    /// | [`True`]  | [`True`]  | [`True`]  |
    /// | [`True`]  | [`False`] | [`False`] |
    /// | [`False`] | [`True`]  | [`True`] |
    /// | [`False`] | [`False`] | [`True`] |
    ///
    ///
    /// [`True`]: enum.Boolean.html#variant.True
    /// [`False`]: enum.Boolean.html#variant.False
    /// [`xor`]: https://en.wikipedia.org/wiki/Boolean_algebra#Operations
    #[inline]
    pub fn implication<R: Into<Self>>(self, rhs: R) -> Self {
        let rhs = rhs.into();
        match (self, rhs) {
            (Self::True, Self::False) => Self::False,
            _ => Self::True,
        }
    }

    /// The logical [`xor`] operation.
    ///
    /// Truth table:
    ///
    /// | self | rhs | output |
    /// |------|-----|--------|
    /// | [`True`]  | [`True`]  | [`False`]  |
    /// | [`True`]  | [`False`] | [`True`] |
    /// | [`False`] | [`True`]  | [`True`] |
    /// | [`False`] | [`False`] | [`False`] |
    ///
    ///
    /// [`True`]: enum.Boolean.html#variant.True
    /// [`False`]: enum.Boolean.html#variant.False
    /// [`xor`]: https://en.wikipedia.org/wiki/Boolean_algebra#Operations
    #[inline]
    pub fn xor<R: Into<Self>>(self, rhs: R) -> Self {
        let rhs = rhs.into();
        match (self, rhs) {
            (Self::True, Self::False) | (Self::False, Self::True) => Self::True,
            _ => Self::False,
        }
    }

    /// The logical [`equivalence`] operation.
    ///
    /// Truth table:
    ///
    /// | self | rhs | output |
    /// |------|-----|--------|
    /// | [`True`]  | [`True`]  | [`True`]  |
    /// | [`True`]  | [`False`] | [`False`] |
    /// | [`False`] | [`True`]  | [`False`] |
    /// | [`False`] | [`False`] | [`True`] |
    ///
    ///
    /// [`True`]: enum.Boolean.html#variant.True
    /// [`False`]: enum.Boolean.html#variant.False
    /// [`equivalence`]: https://en.wikipedia.org/wiki/Boolean_algebra#Operations
    #[inline]
    pub fn equivalence<R: Into<Self>>(self, rhs: R) -> Self {
        let rhs = rhs.into();
        match (self, rhs) {
            (Self::True, Self::True) | (Self::False, Self::False) => Self::True,
            _ => Self::False,
        }
    }

    pub fn is_true(self) -> bool {
        self == Self::True
    }

    pub fn is_false(self) -> bool {
        self == Self::False
    }

    // For primitive bool, this function is currently nightly only.
    pub fn then_some<T>(self, then: T) -> Option<T> {
        if self == Self::True {
            Some(then)
        } else {
            None
        }
    }

    // For primitive bool, this function is currently nightly only.
    pub fn then<T>(self, f: impl FnOnce() -> T) -> Option<T> {
        if self == Self::True {
            Some(f())
        } else {
            None
        }
    }
}

impl From<bool> for Boolean {
    fn from(item: bool) -> Self {
        if item {
            Self::True
        } else {
            Self::False
        }
    }
}

impl From<Boolean> for bool {
    fn from(item: Boolean) -> Self {
        match item {
            Boolean::True => true,
            Boolean::False => false,
        }
    }
}

impl From<&Boolean> for bool {
    fn from(item: &Boolean) -> Self {
        match item {
            Boolean::True => true,
            Boolean::False => false,
        }
    }
}

impl From<&mut Boolean> for bool {
    fn from(item: &mut Boolean) -> Self {
        match item {
            Boolean::True => true,
            Boolean::False => false,
        }
    }
}

// Macro which delegates implementation of essential functions to their
// matching bool implementation (until a fast path implementation is available).
macro_rules! delegated_impl {
    ($fn_ident:ident, $lhs:expr, $rhs:expr) => {
        b!($lhs).$fn_ident(b!($rhs)).into()
    };
}

impl Not for Boolean {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Boolean::True => Boolean::False,
            Boolean::False => Boolean::True,
        }
    }
}

impl BitAnd for Boolean {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        delegated_impl!(bitand, self, rhs)
    }
}

impl BitAndAssign for Boolean {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = self.bitand(rhs);
    }
}

impl BitOr for Boolean {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        delegated_impl!(bitor, self, rhs)
    }
}

impl BitOrAssign for Boolean {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = self.bitor(rhs);
    }
}

impl BitXor for Boolean {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        delegated_impl!(bitxor, self, rhs)
    }
}

impl BitXorAssign for Boolean {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = self.bitxor(rhs);
    }
}

/// The default for [`Boolean`] is [`False`].
///
/// [`Boolean`]: enum.Boolean.html
/// [`False`]: enum.Boolean.html#variant.False
impl Default for Boolean {
    fn default() -> Self {
        Self::False
    }
}

impl FromStr for Boolean {
    type Err = BooleanError;

    /// Important: if the crate has the alloc crate is available and the 'has_alloc' feature is enabled,
    /// it allows for a "true" or "false" value with any casing (e.g. "True" or "trUE" are equivalent to "true").
    /// If the feature 'has_alloc' is set to false, only the values "true", "True", "TRUE", "false",
    /// "False" and "FALSE" will be accepted as valid inputs.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        #[cfg(feature = "has_alloc")]
        {
            match s.to_ascii_lowercase().as_str() {
                "true" => Ok(Self::True),
                "false" => Ok(Self::False),
                _ => Err(BooleanError::UnableToConvertFromStr),
            }
        }

        #[cfg(not(feature = "has_alloc"))]
        {
            match s {
                "true" | "True" | "TRUE" => Ok(Self::True),
                "false" | "False" | "FALSE" => Ok(Self::False),
                _ => Err(BooleanError::UnableToConvertFromStr),
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BooleanError {
    UnableToConvertFromStr,
}

impl core::fmt::Display for BooleanError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::UnableToConvertFromStr => f.write_str(
                r#"Unable to convert given string to a Boolean (expected value "true" or "false")"#,
            ),
        }
    }
}

/// Transforms a value with type [`Bool`] into the equivalent value with the primitive type [`bool`].
///
/// Equivalent to calling `Into::<bool>::into` on a [`Bool`] value.
///
/// Example:
/// ```
/// # use ::bool::{b, Boolean};
/// if b!(Boolean::True) {
///     println!("Always true :)!");
/// }
/// ```
///
/// [`Boolean`]: enum.Boolean.html
/// [`bool`]: https://doc.rust-lang.org/core/primitive.bool.html
#[macro_export]
macro_rules! b {
    ($cond:expr) => {{
        Into::<bool>::into($cond)
    }};
}

#[cfg(test)]
mod tests {
    use super::*;
    use parameterized::ide;
    use parameterized::parameterized as pm;

    mod new {
        use super::*;

        ide!();

        #[pm(input = {
            true,
            false,
        }, expected = {
            Boolean::True,
            Boolean::False,
        })]
        fn test_cases(input: bool, expected: Boolean) {
            let instance = Boolean::new(input);
            assert_eq!(instance, expected);
        }
    }

    macro_rules! test_logical_operation {
         {$op:ident,
            $expected1:expr,
            $expected2:expr,
            $expected3:expr,
            $expected4:expr
        } => {
            mod $op {
                use super::*;

                ide!();

                #[pm(lhs = {
                    Boolean::False,
                    Boolean::False,
                    Boolean::True,
                    Boolean::True,
                }, rhs = {
                    Boolean::False,
                    Boolean::True,
                    Boolean::False,
                    Boolean::True,
                }, expected = {
                    $expected1,
                    $expected2,
                    $expected3,
                    $expected4,
                })]
                fn test_cases(lhs: Boolean, rhs: Boolean, expected: Boolean) {
                    assert_eq!(lhs.$op(rhs), expected);
                }
            }
        };
    }

    mod logical_operations {
        use super::*;

        test_logical_operation! {and,
            Boolean::False,
            Boolean::False,
            Boolean::False,
            Boolean::True
        }

        test_logical_operation! {or,
            Boolean::False,
            Boolean::True,
            Boolean::True,
            Boolean::True
        }

        test_logical_operation! {implication,
            Boolean::True,
            Boolean::True,
            Boolean::False,
            Boolean::True
        }

        test_logical_operation! {xor,
            Boolean::False,
            Boolean::True,
            Boolean::True,
            Boolean::False
        }

        test_logical_operation! {equivalence,
            Boolean::True,
            Boolean::False,
            Boolean::False,
            Boolean::True
        }
    }

    mod logical_not {
        use super::*;

        ide!();

        #[pm(lhs = {
            Boolean::True,
            Boolean::False,
        }, expected = {
            Boolean::False,
            Boolean::True,
        })]
        fn test_cases(lhs: Boolean, expected: Boolean) {
            assert_eq!(lhs.not(), expected);
        }
    }

    #[allow(non_snake_case)]
    mod from_bool_for_Bool {
        use super::*;

        ide!();

        #[pm(input = {
            true,
            false,
        }, expected = {
            Boolean::True,
            Boolean::False,
        })]
        fn test_cases(input: bool, expected: Boolean) {
            let instance: Boolean = From::from(input);
            assert_eq!(instance, expected);
        }
    }

    #[allow(non_snake_case)]
    mod from_Bool_for_bool {
        use super::*;

        ide!();

        #[pm(input = {
            Boolean::True,
            Boolean::False,
        }, expected = {
            true,
            false,
        })]
        fn test_cases(input: Boolean, expected: bool) {
            let instance: bool = From::from(input);
            assert_eq!(instance, expected);
        }
    }

    mod size {
        use super::*;

        #[test]
        fn native_bool() {
            assert_eq!(core::mem::size_of::<bool>(), 1)
        }

        #[test]
        fn native_bool_value() {
            assert_eq!(core::mem::size_of_val(&true), 1);
            assert_eq!(core::mem::size_of_val(&false), 1);
        }

        #[test]
        #[allow(non_snake_case)]
        fn crate_Bool() {
            assert_eq!(core::mem::size_of::<Boolean>(), 1)
        }

        #[test]
        #[allow(non_snake_case)]
        fn crate_Bool_value() {
            assert_eq!(core::mem::size_of_val(&Boolean::True), 1);
            assert_eq!(core::mem::size_of_val(&Boolean::False), 1);
        }
    }

    #[cfg(global_values)]
    mod globals_for_usability {
        use super::*;

        ide!();

        #[pm(input = {
            True,
            False,
        }, expected = {
            Boolean::True,
            Boolean::False,
        })]
        fn test_cases(input: Boolean, expected: Boolean) {
            assert_eq!(input, expected);
        }
    }

    #[test]
    fn macro_cond() {
        let condition = Boolean::False;

        let out = if b!(condition) { 1 } else { 0 };

        assert_eq!(out, 0);
    }

    macro_rules! test_operator {
         {$name:tt, $op:tt,
            $expected1:expr,
            $expected2:expr,
            $expected3:expr,
            $expected4:expr
        } => {
            mod $name {
                use super::*;

                ide!();

                #[pm(lhs = {
                    Boolean::False,
                    Boolean::False,
                    Boolean::True,
                    Boolean::True,
                }, rhs = {
                    Boolean::False,
                    Boolean::True,
                    Boolean::False,
                    Boolean::True,
                }, expected = {
                    $expected1,
                    $expected2,
                    $expected3,
                    $expected4,
                })]
                fn test_cases(lhs: Boolean, rhs: Boolean, expected: Boolean) {
                    assert_eq!(lhs.$name(rhs), expected);
                    assert_eq!(lhs $op rhs, expected);
                }
            }
        };
    }

    mod operators {
        use super::*;

        test_operator! {bitand, &,
            Boolean::False,
            Boolean::False,
            Boolean::False,
            Boolean::True
        }

        test_operator! {bitor, |,
            Boolean::False,
            Boolean::True,
            Boolean::True,
            Boolean::True
        }

        test_operator! {bitxor, ^,
            Boolean::False,
            Boolean::True,
            Boolean::True,
            Boolean::False
        }
    }

    macro_rules! test_operator_assign {
         {$name:tt, $op:tt,
            $expected1:expr,
            $expected2:expr,
            $expected3:expr,
            $expected4:expr
        } => {
            mod $name {
                use super::*;

                ide!();

                #[pm(lhs = {
                    Boolean::False,
                    Boolean::False,
                    Boolean::True,
                    Boolean::True,
                }, rhs = {
                    Boolean::False,
                    Boolean::True,
                    Boolean::False,
                    Boolean::True,
                }, expected = {
                    $expected1,
                    $expected2,
                    $expected3,
                    $expected4,
                })]
                fn test_cases(lhs: Boolean, rhs: Boolean, expected: Boolean) {
                    let mut a = lhs;
                    a.$name(rhs);

                    let mut b = lhs;
                    b $op rhs;

                    assert_eq!(a, expected);
                    assert_eq!(b, expected);
                }
            }
        };
    }

    mod operators_assign {
        use super::*;

        test_operator_assign! {bitand_assign, &=,
            Boolean::False,
            Boolean::False,
            Boolean::False,
            Boolean::True
        }

        test_operator_assign! {bitor_assign, |=,
            Boolean::False,
            Boolean::True,
            Boolean::True,
            Boolean::True
        }

        test_operator_assign! {bitxor_assign, ^=,
            Boolean::False,
            Boolean::True,
            Boolean::True,
            Boolean::False
        }
    }

    mod ordering {
        use super::*;

        #[test]
        fn test_case() {
            let crate_t = Boolean::True;
            let crate_f = Boolean::False;
            let primitive_t = true;
            let primitive_f = false;

            assert_eq!(crate_t.cmp(&crate_t), primitive_t.cmp(&primitive_t));
            assert_eq!(crate_t.cmp(&crate_f), primitive_t.cmp(&primitive_f));
            assert_eq!(crate_f.cmp(&crate_t), primitive_f.cmp(&primitive_t));
            assert_eq!(crate_f.cmp(&crate_f), primitive_f.cmp(&primitive_f));
        }
    }

    mod laws {
        use super::*;

        ide!();

        #[pm(lhs = {
            Boolean::False,
            Boolean::False,
            Boolean::True,
            Boolean::True,
        }, rhs = {
            Boolean::False,
            Boolean::True,
            Boolean::False,
            Boolean::True,
        })]
        fn de_morgan(lhs: Boolean, rhs: Boolean) {
            assert_eq!(lhs.not().and(rhs.not()), (lhs.or(rhs)).not());

            assert_eq!(lhs.not().or(rhs.not()), (lhs.and(rhs)).not());
        }
    }

    mod is_bool {
        use super::*;

        #[test]
        fn is_bool() {
            assert_eq!(Boolean::True.is_true(), true);
            assert_eq!(Boolean::True.is_false(), false);
            assert_eq!(Boolean::False.is_true(), false);
            assert_eq!(Boolean::False.is_false(), true);
        }
    }

    mod then_option {
        use super::*;

        #[test]
        fn then_some() {
            assert_eq!(Boolean::True.then_some(1u8), Some(1u8));
            assert_eq!(Boolean::False.then_some(1u8), None);
        }

        #[test]
        fn then() {
            assert_eq!(Boolean::True.then(|| 1u8), Some(1u8));
            assert_eq!(Boolean::False.then(|| 1u8), None);
        }
    }

    mod from_str {
        use super::*;

        ide!();

        #[cfg(feature = "has_alloc")]
        const EXPECTED_RARE_CASE_FALSE: Result<Boolean, BooleanError> = Ok(Boolean::False);

        #[cfg(not(feature = "has_alloc"))]
        const EXPECTED_RARE_CASE_FALSE: Result<Boolean, BooleanError> =
            Err(BooleanError::UnableToConvertFromStr);

        #[cfg(feature = "has_alloc")]
        const EXPECTED_RARE_CASE_TRUE: Result<Boolean, BooleanError> = Ok(Boolean::True);

        #[cfg(not(feature = "has_alloc"))]
        const EXPECTED_RARE_CASE_TRUE: Result<Boolean, BooleanError> =
            Err(BooleanError::UnableToConvertFromStr);

        #[pm(input = {
            "true",
            "True",
            "TRUE",
            "false",
            "False",
            "FALSE",
            "falsE",
            "trUE",
            "",
            "❤",
        }, expected = {
            Ok(Boolean::True),
            Ok(Boolean::True),
            Ok(Boolean::True),
            Ok(Boolean::False),
            Ok(Boolean::False),
            Ok(Boolean::False),
            EXPECTED_RARE_CASE_FALSE,
            EXPECTED_RARE_CASE_TRUE,
            Err(BooleanError::UnableToConvertFromStr),
            Err(BooleanError::UnableToConvertFromStr),
        })]
        fn from_str_test(input: &str, expected: Result<Boolean, BooleanError>) {
            assert_eq!(FromStr::from_str(input), expected);
        }
    }
}
