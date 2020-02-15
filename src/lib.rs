#![no_std]

use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};

#[cfg(global_values)]
#[allow(non_upper_case_globals)]
pub static True: Bool = Bool::True;

#[cfg(global_values)]
#[allow(non_upper_case_globals)]
pub static False: Bool = Bool::False;

/// Enum with two possible values: `True` or `False` which represent the [`logical`]
/// values `true` and `false` respectively.
///
/// [`logical`]: https://en.wikipedia.org/wiki/Boolean_algebra
#[derive(Debug, Copy, Clone, PartialEq, Eq, Ord, PartialOrd)]
pub enum Bool {
    False,
    True,
}

impl Bool {
    /// Creates a `Bool` dependent on the given primitive `bool`.
    /// If the value is `true`, it will return `Bool::True` and
    /// if the value is`false` will return `Bool::False`
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
    /// [`True`]: enum.Bool.html#variant.True
    /// [`False`]: enum.Bool.html#variant.False
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
    /// [`True`]: enum.Bool.html#variant.True
    /// [`False`]: enum.Bool.html#variant.False
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
    /// [`True`]: enum.Bool.html#variant.True
    /// [`False`]: enum.Bool.html#variant.False
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
    /// [`True`]: enum.Bool.html#variant.True
    /// [`False`]: enum.Bool.html#variant.False
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
    /// [`True`]: enum.Bool.html#variant.True
    /// [`False`]: enum.Bool.html#variant.False
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
    /// [`True`]: enum.Bool.html#variant.True
    /// [`False`]: enum.Bool.html#variant.False
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

impl From<bool> for Bool {
    fn from(item: bool) -> Self {
        if item {
            Self::True
        } else {
            Self::False
        }
    }
}

impl From<Bool> for bool {
    fn from(item: Bool) -> Self {
        match item {
            Bool::True => true,
            Bool::False => false,
        }
    }
}

impl From<&Bool> for bool {
    fn from(item: &Bool) -> Self {
        match item {
            Bool::True => true,
            Bool::False => false,
        }
    }
}

impl From<&mut Bool> for bool {
    fn from(item: &mut Bool) -> Self {
        match item {
            Bool::True => true,
            Bool::False => false,
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

impl Not for Bool {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Bool::True => Bool::False,
            Bool::False => Bool::True,
        }
    }
}

impl BitAnd for Bool {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        delegated_impl!(bitand, self, rhs)
    }
}

impl BitAndAssign for Bool {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = self.bitand(rhs);
    }
}

impl BitOr for Bool {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        delegated_impl!(bitor, self, rhs)
    }
}

impl BitOrAssign for Bool {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = self.bitor(rhs);
    }
}

impl BitXor for Bool {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        delegated_impl!(bitxor, self, rhs)
    }
}

impl BitXorAssign for Bool {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = self.bitxor(rhs);
    }
}

/// The default for [`Bool`] is [`False`].
///
/// [`Bool`]: enum.Bool.html
/// [`False`]: enum.Bool.html#variant.False
impl Default for Bool {
    fn default() -> Self {
        Self::False
    }
}

/// Transforms a value with type [`Bool`] into the equivalent value with the primitive type [`bool`].
///
/// Equivalent to calling `Into::<bool>::into` on a [`Bool`] value.
///
/// Example:
/// ```
/// # use ::bool::{b, Bool};
/// if b!(Bool::True) {
///     println!("Always true :)!");
/// }
/// ```
///
/// [`Bool`]: enum.Bool.html
/// [`bool`]: https://doc.rust-lang.org/std/primitive.bool.html
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
        Bool::True,
        Bool::False,
        })]
        fn test_cases(input: bool, expected: Bool) {
            let instance = Bool::new(input);
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
                    Bool::False,
                    Bool::False,
                    Bool::True,
                    Bool::True,
                }, rhs = {
                    Bool::False,
                    Bool::True,
                    Bool::False,
                    Bool::True,
                }, expected = {
                    $expected1,
                    $expected2,
                    $expected3,
                    $expected4,
                })]
                fn test_cases(lhs: Bool, rhs: Bool, expected: Bool) {
                    assert_eq!(lhs.$op(rhs), expected);
                }
            }
        };
    }

    mod logical_operations {
        use super::*;

        test_logical_operation! {and,
            Bool::False,
            Bool::False,
            Bool::False,
            Bool::True
        }

        test_logical_operation! {or,
            Bool::False,
            Bool::True,
            Bool::True,
            Bool::True
        }

        test_logical_operation! {implication,
            Bool::True,
            Bool::True,
            Bool::False,
            Bool::True
        }

        test_logical_operation! {xor,
            Bool::False,
            Bool::True,
            Bool::True,
            Bool::False
        }

        test_logical_operation! {equivalence,
            Bool::True,
            Bool::False,
            Bool::False,
            Bool::True
        }
    }

    mod logical_not {
        use super::*;

        ide!();

        #[pm(lhs = {
        Bool::True,
        Bool::False,
        }, expected = {
        Bool::False,
        Bool::True,
        })]
        fn test_cases(lhs: Bool, expected: Bool) {
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
        Bool::True,
        Bool::False,
        })]
        fn test_cases(input: bool, expected: Bool) {
            let instance: Bool = From::from(input);
            assert_eq!(instance, expected);
        }
    }

    #[allow(non_snake_case)]
    mod from_Bool_for_bool {
        use super::*;

        ide!();

        #[pm(input = {
        Bool::True,
        Bool::False,
        }, expected = {
        true,
        false,
        })]
        fn test_cases(input: Bool, expected: bool) {
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
            assert_eq!(core::mem::size_of::<Bool>(), 1)
        }

        #[test]
        #[allow(non_snake_case)]
        fn crate_Bool_value() {
            assert_eq!(core::mem::size_of_val(&Bool::True), 1);
            assert_eq!(core::mem::size_of_val(&Bool::False), 1);
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
        Bool::True,
        Bool::False,
        })]
        fn test_cases(input: Bool, expected: Bool) {
            assert_eq!(input, expected);
        }
    }

    #[test]
    fn macro_cond() {
        let condition = Bool::False;

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
                    Bool::False,
                    Bool::False,
                    Bool::True,
                    Bool::True,
                }, rhs = {
                    Bool::False,
                    Bool::True,
                    Bool::False,
                    Bool::True,
                }, expected = {
                    $expected1,
                    $expected2,
                    $expected3,
                    $expected4,
                })]
                fn test_cases(lhs: Bool, rhs: Bool, expected: Bool) {
                    assert_eq!(lhs.$name(rhs), expected);
                    assert_eq!(lhs $op rhs, expected);
                }
            }
        };
    }

    mod operators {
        use super::*;

        test_operator! {bitand, &,
            Bool::False,
            Bool::False,
            Bool::False,
            Bool::True
        }

        test_operator! {bitor, |,
            Bool::False,
            Bool::True,
            Bool::True,
            Bool::True
        }

        test_operator! {bitxor, ^,
            Bool::False,
            Bool::True,
            Bool::True,
            Bool::False
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
                    Bool::False,
                    Bool::False,
                    Bool::True,
                    Bool::True,
                }, rhs = {
                    Bool::False,
                    Bool::True,
                    Bool::False,
                    Bool::True,
                }, expected = {
                    $expected1,
                    $expected2,
                    $expected3,
                    $expected4,
                })]
                fn test_cases(lhs: Bool, rhs: Bool, expected: Bool) {
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
            Bool::False,
            Bool::False,
            Bool::False,
            Bool::True
        }

        test_operator_assign! {bitor_assign, |=,
            Bool::False,
            Bool::True,
            Bool::True,
            Bool::True
        }

        test_operator_assign! {bitxor_assign, ^=,
            Bool::False,
            Bool::True,
            Bool::True,
            Bool::False
        }
    }

    mod ordering {
        use super::*;

        #[test]
        fn test_case() {
            let crate_t = Bool::True;
            let crate_f = Bool::False;
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
            Bool::False,
            Bool::False,
            Bool::True,
            Bool::True,
        }, rhs = {
            Bool::False,
            Bool::True,
            Bool::False,
            Bool::True,
        })]
        fn de_morgan(lhs: Bool, rhs: Bool) {
            assert_eq!(lhs.not().and(rhs.not()), (lhs.or(rhs)).not());

            assert_eq!(lhs.not().or(rhs.not()), (lhs.and(rhs)).not());
        }
    }

    mod is_bool {
        use super::*;

        #[test]
        fn is_bool() {
            assert_eq!(Bool::True.is_true(), true);
            assert_eq!(Bool::True.is_false(), false);
            assert_eq!(Bool::False.is_true(), false);
            assert_eq!(Bool::False.is_false(), true);
        }
    }

    mod then_option {
        use super::*;

        #[test]
        fn then_some() {
            assert_eq!(Bool::True.then_some(1u8), Some(1u8));
            assert_eq!(Bool::False.then_some(1u8), None);
        }

        #[test]
        fn then() {
            assert_eq!(Bool::True.then(|| 1u8), Some(1u8));
            assert_eq!(Bool::False.then(|| 1u8), None);
        }
    }
}
