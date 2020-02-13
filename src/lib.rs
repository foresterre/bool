#![crate_type = "lib"]
#![no_std]

use core::ops::{BitAnd, BitAndAssign};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Bool {
    True,
    False,
}

impl Bool {
    pub fn new(value: bool) -> Self {
        if value {
            Self::True
        } else {
            Self::False
        }
    }

    /// Logical and.
    ///
    /// Truth table where T represents `True` and F represents `False`:
    ///
    /// |------------|---------
    /// | self | rhs | return |
    /// |------------|---------
    /// | F    | F   | F      |
    /// | F    | T   | F      |
    /// | T    | F   | F      |
    /// | T    | T   | T      |
    /// |------------|--------|
    ///
    /// // TODO fix doc links
    /// [`True`]: enum.bool.True
    /// [`False`]: enum.Bool.False
    #[inline]
    pub fn logical_and<R: Into<Self>>(self, rhs: R) -> Self {
        let rhs = rhs.into();
        if self == Self::False || rhs == Self::False {
            Self::False
        } else {
            Self::True
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

impl From<&mut Bool> for bool {
    fn from(item: &mut Bool) -> Self {
        match item {
            Bool::True => true,
            Bool::False => false,
        }
    }
}

// TODO
impl BitAnd for Bool {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Into::<bool>::into(self)
            .bitand(Into::<bool>::into(rhs))
            .into()
    }
}

// TODO
impl BitAndAssign for Bool {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = (b!(*self).bitand(b!(rhs))).into();
    }
}

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

    mod logical_and {
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
            Bool::False,
            Bool::False,
            Bool::False,
            Bool::True,
        })]
        fn test_cases(lhs: Bool, rhs: Bool, expected: Bool) {
            assert_eq!(lhs.logical_and(rhs), expected);
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

    #[allow(non_snake_case)]
    mod size {
        use super::*;

        #[test]
        fn native_bool() {
            assert_eq!(core::mem::size_of::<bool>(), 1)
        }

        #[test]
        #[allow(non_snake_case)]
        fn crate_Bool() {
            assert_eq!(core::mem::size_of::<Bool>(), 1)
        }
    }

    #[test]
    fn macro_cond() {
        let condition = Bool::False;

        let out = if b!(condition) { 1 } else { 0 };

        assert_eq!(out, 0);
    }
}
