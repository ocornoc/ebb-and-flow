macro_rules! move_from_ref_reqs {
    ($($move:tt = $scalar:ident $(where F: $req0:ident $(+ $reqs:ident)*)? => $assign:tt ; $move_fn:ident := $assign_fn:ident),* $(,)?) => {
        $(
            impl<F: $($req0 $(+ $reqs)*)?> $assign<$scalar<F>> for $scalar<F> {
                #[inline]
                fn $assign_fn(&mut self, rhs: $scalar<F>) {
                    self.$assign_fn(&rhs);
                }
            }

            impl<F: $($req0 $(+ $reqs)*)?> $move<&$scalar<F>> for $scalar<F> {
                type Output = $scalar<F>;

                #[inline]
                fn $move_fn(mut self, rhs: &$scalar<F>) -> $scalar<F> {
                    self.$assign_fn(rhs);
                    self
                }
            }

            impl<F: $($req0 $(+ $reqs)*)?> $move<$scalar<F>> for $scalar<F> {
                type Output = $scalar<F>;

                #[inline]
                fn $move_fn(mut self, rhs: $scalar<F>) -> $scalar<F> {
                    self.$assign_fn(rhs);
                    self
                }
            }

            impl<F: $($req0 $(+ $reqs)*)?> $move<$scalar<F>> for &$scalar<F> {
                type Output = $scalar<F>;

                #[inline]
                fn $move_fn(self, mut rhs: $scalar<F>) -> $scalar<F> {
                    rhs.$assign_fn(self);
                    rhs
                }
            }
        )*
    };
}

macro_rules! all_from_scalar {
    ($($move:tt = $scalar:ident where F: $req0:ident $(+ $reqs:ident)* => $assign:tt ; $move_fn:ident := $assign_fn:ident),* $(,)?) => {
        $(
            impl<F: $req0 $(+ $reqs)*> $assign<&$scalar<F>> for $scalar<F> {
                #[inline]
                fn $assign_fn(&mut self, rhs: &$scalar<F>) {
                    self.0.$assign_fn(&rhs.0);
                }
            }

            move_from_ref_reqs!($move = $scalar where F: $req0 $(+ $reqs)* => $assign ; $move_fn := $assign_fn);
        )*
    };
    ($($move:tt = $scalar:ident => $assign:tt ; $move_fn:ident := $assign_fn:ident),* $(,)?) => {
        $(
            all_from_scalar!($move = $scalar where F: BitViewSized => $assign ; $move_fn := $assign_fn);
        )*
    };
}

pub mod anf;
pub use anf::{AlgebraicNormalForm, Anf};
pub mod assignment;
pub use assignment::VectorAssignment;
mod tree;
use tree::SparseTree;
pub mod tt;
pub use tt::TruthTable;

pub type Variable = u16;
