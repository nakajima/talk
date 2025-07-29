#[macro_export]
macro_rules! impl_option_eq {
    ($t:ty) => {
        // T == Option<T>
        impl ::core::cmp::PartialEq<Option<$t>> for $t
        where
            $t: ::core::cmp::PartialEq,
        {
            #[inline]
            fn eq(&self, rhs: &Option<$t>) -> bool {
                matches!(rhs, Some(v) if v == self)
            }
        }

        // Option<T> == T
        impl ::core::cmp::PartialEq<$t> for Option<$t>
        where
            $t: ::core::cmp::PartialEq,
        {
            #[inline]
            fn eq(&self, rhs: &$t) -> bool {
                matches!(self, Some(v) if v == rhs)
            }
        }
    };
}
