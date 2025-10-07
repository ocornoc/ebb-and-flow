use std::fmt::{Debug, Display};
use std::iter::FusedIterator;
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};
use bitvec::array::BitArray;
use bitvec::view::BitViewSized;
use super::Variable;

type Fundamental = u64;
const FUNDAMENTAL_ARRAY_BITS: usize = 384;
const FUNDAMENTAL_ARRAY_LEN: usize = FUNDAMENTAL_ARRAY_BITS / Fundamental::BITS as usize;

type MintermRepr<F> = BitArray<F>;
pub type AesMinterm = VectorAssignment<[Fundamental; FUNDAMENTAL_ARRAY_LEN]>;

#[derive(Clone, Copy)]
pub struct VectorAssignment<F: BitViewSized>(pub(super) MintermRepr<F>);

impl<F: BitViewSized> VectorAssignment<F> {
    /// Create an assignment with no variables.
    ///
    /// This often represents a constant term "1". For example, the expression x ⊕ xy ⊕ z may be
    /// represented with assignments `[001, 011, 100]`. Negating the entire multinomial gives
    /// 1 ⊕ x ⊕ xy ⊕ z, or `[000, 001, 011, 100]`
    pub const fn none() -> Self {
        VectorAssignment(MintermRepr::ZERO)
    }

    /// Create an assignment with all variables set.
    pub fn all() -> Self {
        !Self::none()
    }

    /// Returns true iff every bit set in `self` is also set in `mask`.
    ///
    /// The relation "X is a subset of Y" (X ⊑ Y) respects "X is lexicographically ordered before
    /// or equal to Y" (X ≤ Y); in other words, X ⊑ Y implies X ≤ Y. This implication is not an
    /// equivalence: to see this, consider the assignments x (`01`), xy (`11`), and y (`10`). We can
    /// see x ⊏ xy, y ⊏ xy, and x < y, but it is not true that x ⊑ y and thus {x, y} forms an
    /// antichain under (⊏).
    ///
    /// See also the dual order [`is_superset_of`](Self::is_superset_of).
    pub fn is_subset_of(&self, mask: &Self) -> bool {
        mask.is_superset_of(self)
    }

    /// Returns true iff every bit set in `other` is also set in `self`.
    ///
    /// The relation "X is a superset of Y" (X ⊒ Y) respects "X is lexicographically ordered after
    /// or equal to Y" (X ⊒ Y); in other words, X ⊒ Y implies X ≥ Y. See the documentation of
    /// [`is_subset_of`](Self::is_subset_of) for a counterexample to equivalence.
    ///
    /// See also the dual order [`is_subset_of`](Self::is_subset_of).
    pub fn is_superset_of(&self, other: &Self) -> bool {
        other.iter_ones().all(|variable| self.contains(variable))
    }

    /// Returns true iff the assignment contains the given variable.
    ///
    /// ### Panics
    ///
    /// This function does not panic (unless the associated call to `F` does). When given a variable
    /// out-of-bounds, this simply returns false.
    pub fn contains(&self, variable: Variable) -> bool {
        self.0.get(variable as usize).is_some_and(|entry| *entry)
    }

    pub fn intersects(&self, other: &Self) -> bool {
        self.0.iter().zip(other.0.iter()).any(|(lhs, rhs)| *lhs && *rhs)
    }

    pub fn is_disjoint(&self, other: &Self) -> bool {
        !self.intersects(other)
    }

    /// Return the number of "live" (contained) variables in the assignment.
    pub fn count_live_variables(&self) -> usize {
        self.0.count_ones()
    }

    /// Set a specific variable to true (contained) or false (not contained) within the assignment.
    pub fn set(&mut self, variable: Variable, value: bool) {
        self.0.set(variable as usize, value)
    }

    /// Insert a variable to the assignment.
    pub fn insert(&mut self, variable: Variable) {
        self.set(variable, true);
    }

    /// Set a specific variable to true (contained) or false (not contained) within the assignment,
    /// returning whether the variable was previously contained or not.
    pub fn replace(&mut self, variable: Variable, value: bool) -> bool {
        self.0.replace(variable as usize, value)
    }

    /// Remove a specific variable from the assignment, returning true iff the variable was actually
    /// removed (i.e., the variable was previously contained).
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
    /// one_set.insert(variable);
    /// assert_eq!(singular, one_set);
    /// # }
    /// ```
    pub fn singular(variable: Variable) -> Self {
        let mut out = VectorAssignment::none();
        out.insert(variable);
        out
    }

    /// Swap the membership of one variable to another.
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

    pub fn clear(&mut self) {
        *self = Self::none();
    }

    pub fn is_singular(&self) -> bool {
        let leading_zeros = self.0.leading_zeros();
        let trailing_zeros = self.0.trailing_zeros();
        self.0.len() == leading_zeros + trailing_zeros + 1
    }
}

impl<F: BitViewSized> Debug for VectorAssignment<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.count_live_variables() == 0 {
            write!(f, "1")
        } else {
            for variable in self.iter_ones() {
                write!(f, "x{variable}")?;
            }
            Ok(())
        }
    }
}

impl<F: BitViewSized> Display for VectorAssignment<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Debug::fmt(self, f)
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

impl<F: BitViewSized> From<F> for VectorAssignment<F> {
    fn from(value: F) -> Self {
        VectorAssignment(BitArray::new(value))
    }
}

all_from_scalar! {
    BitAnd = VectorAssignment => BitAndAssign; bitand := bitand_assign,
    BitOr = VectorAssignment => BitOrAssign; bitor := bitor_assign,
    BitXor = VectorAssignment => BitXorAssign; bitxor := bitxor_assign,
}

#[derive(Debug, Default, PartialEq, Eq)]
enum AndNotIterState {
    #[default]
    NoSubsetsReturnedYet,
    ReturnedFirstSubset,
}

pub struct AndNotIter<F: BitViewSized + Clone> {
    pub(super) negated_mask: VectorAssignment<F>,
    pub(super) unconditional: VectorAssignment<F>,
    next_subset_of_negated: VectorAssignment<F>,
    state: AndNotIterState,
}

impl<F: BitViewSized + Clone> AndNotIter<F> {
    pub fn new(
        negated_mask: VectorAssignment<F>,
        unconditional: VectorAssignment<F>,
    ) -> Self {
        assert!(negated_mask.is_disjoint(&unconditional));
        AndNotIter {
            negated_mask,
            unconditional,
            next_subset_of_negated: VectorAssignment::none(),
            state: AndNotIterState::default(),
        }
    }

    fn step(&mut self) -> VectorAssignment<F> {
        // We will end up returning the current subset before modifying it, so clone it now.
        let original_subset = self.next_subset_of_negated.clone();
        // We will store the next subset in self.next_subset_of_negated. We clear it so it can be
        // used as the output of (original_subset + !self.negated_mask + 1) & self.negated_mask.
        // (original_subset + !self.negated_mask + 1) & self.negated_mask is equivalent to the
        // classic bit-twiddling version of sub-bitmask enumeration (s - m) & m.
        self.next_subset_of_negated.clear();
        let mut carry = true;
        let next_subset_bits = self.next_subset_of_negated.0.iter_mut();
        let original_subset_bits = original_subset.0.iter();
        let negated_mask_bits = self.negated_mask.0.iter();
        let bit_triples = next_subset_bits.zip(original_subset_bits).zip(negated_mask_bits);
        // Perform a ripple-carry addition with the carry bit initially set to true to give
        // next_subset := original_subset + !self.negated_mask + 1
        for ((mut next_bit, original_bit), mask_bit) in bit_triples {
            // We must negate the mask bit because we're trying to add !self.negated_mask.
            let (original_bit, mask_bit) = (*original_bit, !*mask_bit);
            *next_bit = original_bit ^ mask_bit ^ carry;
            carry = ((original_bit ^ mask_bit) & carry) | (original_bit & mask_bit);
        }
        // If we still have the carry bit set after the addition,
        if carry {
            // ... then we've overflowed the backing bit storage. We'll clear the next subset
            // entirely, which will get detected as a cycle by self.state at the top of the function
            // and will end the iteration.
            self.next_subset_of_negated.clear();
        } else {
            // Otherwise, it's possible that we've still carried the addition into bits no longer
            // in self.negated_mask. By performing this AND, we remove those bits. This will
            // effectively clear self.next_subset_of_negated in that case.
            self.next_subset_of_negated &= &self.negated_mask;
        }
        original_subset | &self.unconditional
    }
}

impl<F: BitViewSized + Clone> Debug for AndNotIter<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f
            .debug_struct("AndNotIter")
            .field("negated_mask", &self.negated_mask)
            .field("unconditional", &self.unconditional)
            .field("next_subset_of_negated", &self.next_subset_of_negated)
            .field("state", &self.state)
            .finish()
    }
}

impl<F: BitViewSized + Clone> Iterator for AndNotIter<F> {
    type Item = VectorAssignment<F>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.state {
            // If we haven't returned any subsets yet, then this is the first. This special step
            // ensures we always return at least one subset: the empty subset. The assignment will
            // consist of just the unconditional bits when returned.
            AndNotIterState::NoSubsetsReturnedYet => {
                self.state = AndNotIterState::ReturnedFirstSubset;
                Some(self.step())
            },
            // If we've returned at least one subset already and the next subset to return is the
            // empty set, then we've looped back around to the start and thus we're done. This is a
            // fixed pointed of this iterator and thus, if this branch is reached, it will be fused.
            _ if self.next_subset_of_negated == VectorAssignment::none() => None,
            // If we've returned at least one subset already and we haven't looped back around, then
            // there are more subsets to return.
            AndNotIterState::ReturnedFirstSubset => Some(self.step()),
        }
    }
}

impl<F: BitViewSized + Clone> FusedIterator for AndNotIter<F> {}
