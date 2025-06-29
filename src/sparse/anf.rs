use std::fmt::{Debug, Display};
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};
use bitvec::view::BitViewSized;
use super::{assignment::AndNotIter, SparseTree, Variable, VectorAssignment};

/// A function f : GF\[2]ⁿ -> GF\[2] stored as the summands of the algebraic normal form of f.
///
/// Every function f : GF\[2]ⁿ -> GF\[2] can be represented by ⨁ S ⊆ {0, 1}ⁿ, φ(f, S) xˢ where 
/// the Mobius transformation φ(f, S) := ⨁ T ≼ S, f(xˢ). We use a sparse representation of the set
/// of vector assignments (inputs) of f that evaluate φ(f, S) to 1, defined as
/// Summands(f) := { S | φ(f, S) = 1 }.
#[derive(Clone, PartialEq, Eq)]
pub struct AlgebraicNormalForm<F: BitViewSized>(SparseTree<F>);

pub type Anf<F> = AlgebraicNormalForm<F>;

impl<F: BitViewSized> AlgebraicNormalForm<F> {
    pub fn variables(&self) -> Variable {
        self.0.variables
    }

    pub fn empty(variables: Variable) -> Self {
        AlgebraicNormalForm(SparseTree::empty(variables))
    }

    pub fn insert(&mut self, summand: VectorAssignment<F>) -> bool {
        self.0.insert(summand)
    }

    pub fn contains(&self, summand: &VectorAssignment<F>) -> bool {
        self.0.contains(summand)
    }

    pub fn remove(&mut self, summand: &VectorAssignment<F>) -> bool {
        self.0.remove(summand)
    }

    #[inline]
    pub fn modify_summand(
        &mut self,
        summand: VectorAssignment<F>,
        f: impl FnOnce(bool) -> bool,
    ) -> bool {
        // optimize to use feat(btree_set_entry) when stabilized
        if f(self.contains(&summand)) {
            self.insert(summand)
        } else {
            self.remove(&summand)
        }
    }

    pub fn set_summand(&mut self, summand: VectorAssignment<F>, present: bool) -> bool {
        // optimize to use feat(btree_set_entry) when stabilized
        if present {
            self.insert(summand)
        } else {
            self.remove(&summand)
        }
    }

    pub fn evaluate(&self, assignment: &VectorAssignment<F>) -> bool {
        self
            .0
            .heap
            .range(..=assignment)
            .filter(|other| assignment.is_superset_of(other))
            .count() % 2 == 1
    }

    pub fn count_live_variables(&self) -> usize {
        self.0.count_live_variables()
    }

    pub fn iter_summands(&self) -> <&SparseTree<F> as IntoIterator>::IntoIter {
        self.0.iter()
    }
}

impl<F: BitViewSized + Clone> AlgebraicNormalForm<F> {
    pub fn flip(&mut self, summand: &VectorAssignment<F>) -> bool {
        self.0.flip(summand)
    }

    pub fn from_summands(
        variables: Variable,
        summands: impl IntoIterator<Item = VectorAssignment<F>>,
    ) -> Self {
        let mut new = Self::empty(variables);
        for summand in summands {
            new.flip(&summand);
        }
        new
    }

    #[must_use]
    pub fn swap_variables(&self, v1: Variable, v2: Variable) -> Self {
        AlgebraicNormalForm(self.0.swap_variables(v1, v2))
    }

    #[must_use]
    pub fn substitute_variable(&self, variable: Variable, replacement: &VectorAssignment<F>) -> Self {
        Self::from_summands(self.variables(), self.into_iter().cloned().map(|mut assignment| {
            if assignment.remove(variable) {
                assignment ^= replacement;
            }
            assignment
        }))
    }

    pub fn union(&mut self, other: &Self) {
        self.0.heap.extend(other.iter_summands().cloned());
    }

    pub fn unioned(mut self, other: &Self) -> Self {
        self.union(other);
        self
    }

    /// Given a [boolean vector function](AlgebraicNormalForm) f(x), return g(x) := !f(x).
    pub fn not_assign(&mut self) {
        // g(x) := !f(x) = 1 ⊕ f(x)
        // Adding 1 to f(x) is equal to toggling 1's assignment. 1's assignment is equal to the
        // empty assignment, e.g. is an always-true constant.
        self.flip(&VectorAssignment::none());
    }

    /// Take the partial derivative of self(x) with respect to a given variable.
    ///
    /// ```
    /// # use ebb_and_flow::sparse::{Anf, Variable, VectorAssignment};
    /// let f = Anf::from_summands(5, [
    ///     [0b00000_u8].into(),
    ///     [0b00010].into(),
    ///     [0b00100].into(),
    ///     [0b11000].into(),
    ///     [0b11101].into(),
    /// ]);
    /// assert_eq!(f.partial_derivative(0), Anf::from_summands(5, [
    ///     [0b11100_u8].into(),
    /// ]));
    /// assert_eq!(f.partial_derivative(1), Anf::from_summands(5, [
    ///     [0b00000_u8].into(),
    /// ]));
    /// assert_eq!(f.partial_derivative(2), Anf::from_summands(5, [
    ///     [0b00000_u8].into(),
    ///     [0b11001].into(),
    /// ]));
    /// assert_eq!(f.partial_derivative(3), Anf::from_summands(5, [
    ///     [0b10000_u8].into(),
    ///     [0b10101].into(),
    /// ]));
    /// assert_eq!(f.partial_derivative(4), Anf::from_summands(5, [
    ///     [0b01000_u8].into(),
    ///     [0b01101].into(),
    /// ]));
    /// ```
    pub fn partial_derivative(&self, wrt: Variable) -> Self {
        self.directional_derivative(&VectorAssignment::singular(wrt))
    }

    #[inline]
    fn directional_derivative_iter<'iter>(
        &'iter self,
        direction: &'iter VectorAssignment<F>,
    ) -> impl Iterator<Item = VectorAssignment<F>> + 'iter {
        self
            .iter_summands()
            .filter(|summand| summand.intersects(direction))
            .flat_map(move |summand| {
                let negated_mask = summand.clone() & direction;
                let unconditional = !direction.clone() & summand;
                AndNotIter::new(negated_mask, unconditional)
            })
    }

    pub fn directional_derivative(&self, direction: &VectorAssignment<F>) -> Self {
        // The minterms of the multilinear function self(x ⊕ direction)
        let summands_with_shifted_input = self.directional_derivative_iter(direction);
        // Derivative wrt direction := filtered(x) ⊕ filtered(x ⊕ direction), where filtered(x) is
        // self(x) with all summands disjoint from direction removed.
        Anf::from_summands(
            self.variables(),
            self
                .iter_summands()
                .filter(|summand| summand.intersects(direction))
                .cloned()
                .chain(summands_with_shifted_input),
        )
    }

    pub fn homogeneity(&self) -> Self {
        Anf::from_summands(
            self.variables(),
            (0..self.variables())
                .into_iter()
                .flat_map(|variable| {
                    self.partial_derivative(variable) & VectorAssignment::singular(variable)
                }),
        )
    }

    /// Get the divergence of self(x).
    ///
    /// ```
    /// # use ebb_and_flow::sparse::{Anf, Variable, VectorAssignment};
    /// let f = Anf::from_summands(5, [
    ///     [0b00000_u8].into(),
    ///     [0b00010].into(),
    ///     [0b00100].into(),
    ///     [0b11000].into(),
    ///     [0b11101].into(),
    /// ]);
    /// assert_eq!(f.divergence(), Anf::from_summands(5, [
    ///     [0b01000_u8].into(),
    ///     [0b10000].into(),
    ///     [0b11100].into(),
    ///     [0b01101].into(),
    ///     [0b10101].into(),
    ///     [0b11001].into(),
    /// ]));
    /// ```
    pub fn divergence(&self) -> Self {
        Anf::from_summands(
            self.variables(),
            (0..self.variables())
                .into_iter()
                .flat_map(|variable| self.partial_derivative(variable)),
        )
    }
}

impl<F: BitViewSized + Clone> AddAssign<&Anf<F>> for Anf<F> {
    fn add_assign(&mut self, rhs: &Anf<F>) {
        BitXorAssign::bitxor_assign(self, rhs);
    }
}

impl<F: BitViewSized + Clone> BitAndAssign<&Anf<F>> for Anf<F> {
    /// Return `lhs & rhs` as a new ANF.
    ///
    /// Given the algebraic normal form of functions l(x), r(x) : GF\[2]ⁿ -> GF\[2], stored as
    /// [Summands](Anf)(l) and [Summands](Anf)(r), this returns out(x) := l(x) & r(x) as
    /// Summands(l & r) = { (left | right) | (left, right) ∈ l x r }. Using (left | right) instead
    /// of (left & right) may be unintuitive but is correct as (left | right) represents an
    /// assignment where all assignments in left and all assignments in right must be
    /// simultaneously true. This is calculated as a bitwise or of their representations to give us left ∧ right.
    fn bitand_assign(&mut self, rhs: &Anf<F>) {
        assert_eq!(self.variables(), rhs.variables());
        let mut new = Anf::empty(self.variables());
        for left in self.iter_summands() {
            for right in rhs.iter_summands() {
                // For every element in the Cartesian product lhs x rhs, we should sum it to the new
                // vector, e.g. toggle its entry bit. We use .insert() as an optimization here
                // because the iterators are strictly increasing, so we don't have to worry about
                // duplicates. In other words, insertion is only correct because every pair here is
                // unique.
                new.insert(left.clone() | right);
            }
        }
        *self = new;
    }
}

impl<F: BitViewSized + Clone> BitOrAssign<&Anf<F>> for Anf<F> {
    /// Return `lhs | rhs` as a new ANF.
    ///
    /// Given the algebraic normal form of functions l(x), r(x) : GF\[2]ⁿ -> GF\[2], stored as
    /// [Summands](Anf)(l) and [Summands](Anf)(r), this returns out(x) := l(x) | r(x) as
    /// Summands(l | r) = { (left | right) | left, right ∈ l ∪ r }.
    fn bitor_assign(&mut self, rhs: &Anf<F>) {
        assert_eq!(self.variables(), rhs.variables());
        let mut new = Anf::empty(self.variables());
        for left in self.0.heap.union(&rhs.0.heap) {
            for right in self.0.heap.union(&rhs.0.heap) {
                // For every element in the Cartesian product (lhs ∪ rhs) x (lhs ∪ rhs), we should
                // sum it to the new vector, e.g. toggle its entry bit. We use .insert() as an
                // optimization here because the iterators are strictly increasing, so we don't have
                // to worry about duplicates. In other words, insertion is only correct because
                // every pair here is unique.
                new.insert(left.clone() | right);
            }
        }
        *self = new;
    }
}

impl<F: BitViewSized + Clone> BitXorAssign<&Anf<F>> for Anf<F> {
    /// Return `lhs ⊕ rhs` as a new ANF.
    ///
    /// Given the algebraic normal form of functions l(x), r(x) : GF\[2]ⁿ -> GF\[2], stored as
    /// [Summands](Anf)(l) and [Summands](Anf)(r), this returns out(x) := l(x) ⊕ r(x) as
    /// Summands(l ⊕ r) = Summands(l) △ Summands(r).
    fn bitxor_assign(&mut self, rhs: &Anf<F>) {
        assert_eq!(self.variables(), rhs.variables());
        // Naively, we should make some empty ANF called "new" and iterate as follows:
        // for assignment in self.0.heap.symmetric_difference(&rhs.0.heap) {
        //     new.insert(summand);
        // }
        // But we can save the allocation and re-use self by just toggling every element in self by
        // its containment in rhs. If it's not in rhs, it's the same as self's value. If it is in
        // rhs, then we must toggle its entry.
        for summand in rhs.iter_summands() {
            self.flip(summand);
        }
    }
}

move_from_ref_reqs! {
    Add = Anf where F: BitViewSized + Clone => AddAssign; add := add_assign,
    BitAnd = Anf where F: BitViewSized + Clone => BitAndAssign; bitand := bitand_assign,
    BitOr = Anf where F: BitViewSized + Clone => BitOrAssign; bitor := bitor_assign,
    BitXor = Anf where F: BitViewSized + Clone => BitXorAssign; bitxor := bitxor_assign,
}

impl<F: BitViewSized + Clone> BitAndAssign<&VectorAssignment<F>> for Anf<F> {
    fn bitand_assign(&mut self, rhs: &VectorAssignment<F>) {
        *self = Self::from_summands(
            self.variables(),
            self
                .iter_summands()
                .cloned()
                .map(|summand| summand | rhs),
        );
    }
}

impl<F: BitViewSized + Clone> BitAndAssign<VectorAssignment<F>> for Anf<F> {
    fn bitand_assign(&mut self, rhs: VectorAssignment<F>) {
        *self &= &rhs;
    }
}

impl<F: BitViewSized + Clone> BitAnd<&VectorAssignment<F>> for Anf<F> {
    type Output = Self;

    fn bitand(mut self, rhs: &VectorAssignment<F>) -> Self {
        self &= rhs;
        self
    }
}

impl<F: BitViewSized + Clone> BitAnd<VectorAssignment<F>> for Anf<F> {
    type Output = Self;

    fn bitand(mut self, rhs: VectorAssignment<F>) -> Self {
        self &= rhs;
        self
    }
}

impl<F: BitViewSized> IntoIterator for Anf<F> {
    type Item = VectorAssignment<F>;
    type IntoIter = <SparseTree<F> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.heap.into_iter()
    }
}

impl<'a, F: BitViewSized> IntoIterator for &'a Anf<F> {
    type Item = &'a VectorAssignment<F>;
    type IntoIter = <&'a SparseTree<F> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        (&self.0.heap).into_iter()
    }
}

impl<F: BitViewSized + Clone> Not for Anf<F> {
    type Output = Self;

    fn not(mut self) -> Self {
        self.not_assign();
        self
    }
}

impl<F: BitViewSized> Debug for Anf<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut first = true;
        for summand in self.iter_summands() {
            if first {
                first = false;
                write!(f, "{summand}")?;
            } else {
                write!(f, " ⊕ {summand}")?;
            }
        }
        Ok(())
    }
}

impl<F: BitViewSized> Display for Anf<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}
