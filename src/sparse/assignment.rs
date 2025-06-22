use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};
use bitvec::array::BitArray;
use bitvec::view::BitViewSized;
use super::Variable;

type Fundamental = u64;
const FUNDAMENTAL_ARRAY_BITS: usize = 384;
const FUNDAMENTAL_ARRAY_LEN: usize = FUNDAMENTAL_ARRAY_BITS / Fundamental::BITS as usize;

type MintermRepr<F> = BitArray<F>;
pub type AesMinterm = VectorAssignment<[Fundamental; FUNDAMENTAL_ARRAY_LEN]>;

#[derive(Debug, Clone, Copy)]
pub struct VectorAssignment<F: BitViewSized>(pub(super) MintermRepr<F>);

impl<F: BitViewSized> VectorAssignment<F> {
    pub const fn none() -> Self {
        VectorAssignment(MintermRepr::ZERO)
    }

    pub fn all() -> Self {
        !Self::none()
    }

    pub fn is_subset_of(&self, mask: &Self) -> bool {
        mask.is_superset_of(self)
    }

    pub fn is_superset_of(&self, other: &Self) -> bool {
        self.0.contains(&other.0)
    }

    pub fn contains(&self, variable: Variable) -> bool {
        self.0.get(variable as usize).is_some_and(|entry| *entry)
    }

    pub fn live_variables(&self) -> usize {
        self.0.count_ones()
    }

    pub fn set(&mut self, variable: Variable, value: bool) {
        self.0.set(variable as usize, value)
    }

    pub fn replace(&mut self, variable: Variable, value: bool) -> bool {
        self.0.replace(variable as usize, value)
    }

    pub fn remove(&mut self, variable: Variable) -> bool {
        self.replace(variable, false)
    }

    /// Create an assignment with only one variable set.
    ///
    /// ```
    /// # use ebb_and_flow::sparse::{Variable, VectorAssignment};
    /// # for variable in 0..(u8::BITS * 4) as Variable {
    /// // Using the singular constructor.
    /// let singular = VectorAssignment::<[u8; 4]>::singular(variable);
    /// // Create the equivalent assignment manually.
    /// let mut one_set = VectorAssignment::none();
    /// one_set.set(variable, true);
    /// assert_eq!(singular, one_set);
    /// # }
    /// ```
    pub fn singular(variable: Variable) -> Self {
        let mut out = VectorAssignment::none();
        out.set(variable, true);
        out
    }

    pub fn swap_variables(&mut self, v1: Variable, v2: Variable) {
        self.0.swap(v1 as usize, v2 as usize)
    }

    /// Iterate over the set variables in the assignment.
    ///
    /// ```
    /// # use ebb_and_flow::sparse::{Variable, VectorAssignment};
    /// // Empty assignments have no set variables.
    /// assert_eq!(VectorAssignment::<[u16; 2]>::none().iter_ones().count(), 0);
    /// // Singular assignments have one set variables.
    /// # for variable in 0..(u16::BITS * 2) as Variable {
    /// assert_eq!(VectorAssignment::<[u16; 2]>::singular(variable).iter_ones().count(), 1);
    /// # }
    /// // All-one assignments have as many variables set as the backing storage has bits.
    /// assert_eq!(VectorAssignment::<[u16; 2]>::all().iter_ones().count(), u16::BITS as usize * 2);
    /// ```
    pub fn iter_ones(&self) -> impl ExactSizeIterator<Item = Variable> {
        self.0.iter_ones().map(|index| index as Variable)
    }
}

impl<F: BitViewSized> Default for VectorAssignment<F> {
    fn default() -> Self {
        Self::none()
    }
}

impl<F: BitViewSized> Not for VectorAssignment<F> {
    type Output = Self;

    #[inline]
    fn not(self) -> Self {
        VectorAssignment(!self.0)
    }
}

impl<F: BitViewSized> PartialEq for VectorAssignment<F> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    #[inline]
    fn ne(&self, other: &Self) -> bool {
        self.0 != other.0
    }
}

impl<F: BitViewSized> Eq for VectorAssignment<F> {}

impl<F: BitViewSized> PartialOrd for VectorAssignment<F> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(&other.0)
    }

    #[inline]
    fn lt(&self, other: &Self) -> bool {
        self.0.lt(&other.0)
    }

    #[inline]
    fn le(&self, other: &Self) -> bool {
        self.0.le(&other.0)
    }

    #[inline]
    fn gt(&self, other: &Self) -> bool {
        self.0.gt(&other.0)
    }

    #[inline]
    fn ge(&self, other: &Self) -> bool {
        self.0.ge(&other.0)
    }
}

impl<F: BitViewSized> Ord for VectorAssignment<F> {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }

    #[inline]
    fn max(self, other: Self) -> Self {
        VectorAssignment(self.0.max(other.0))
    }

    #[inline]
    fn min(self, other: Self) -> Self {
        VectorAssignment(self.0.min(other.0))
    }

    #[inline]
    fn clamp(self, min: Self, max: Self) -> Self {
        VectorAssignment(self.0.clamp(min.0, max.0))
    }
}

all_from_scalar! {
    BitAnd = VectorAssignment => BitAndAssign; bitand := bitand_assign,
    BitOr = VectorAssignment => BitOrAssign; bitor := bitor_assign,
    BitXor = VectorAssignment => BitXorAssign; bitxor := bitxor_assign,
}
