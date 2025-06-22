use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};
use bitvec::view::BitViewSized;
use super::{SparseTree, Variable, VectorAssignment};

/// A function f : GF\[2]ⁿ -> GF\[2] stored as the summands of the algebraic normal form of f.
///
/// Every function f : GF\[2]ⁿ -> GF\[2] can be represented by ⨂ S ⊆ {0, 1}ⁿ, φ(f, S) xˢ where 
/// the Mobius transformation φ(f, S) := ⨂ T ≼ S, f(xˢ). We use a sparse representation of the set
/// of vector assignments (inputs) of f that evaluate φ(f, S) to 1, defined as
/// Summands(f) := { S | φ(f, S) = 1 }.
#[derive(Clone)]
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
}

impl<F: BitViewSized + Clone> AlgebraicNormalForm<F> {
    pub fn live_variables(&self) -> usize {
        self.0.live_variables()
    }

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

    pub fn iter_summands(&self) -> <&SparseTree<F> as IntoIterator>::IntoIter {
        self.0.iter()
    }

    pub fn union(&mut self, other: &Self) {
        self.0.heap.extend(other.iter_summands().cloned());
    }

    pub fn unioned(mut self, other: &Self) -> Self {
        self.union(other);
        self
    }

    pub fn negate(&mut self) {
        self.flip(&VectorAssignment::none());
    }

    pub fn partial_derivative(&self, wrt: Variable) -> Self {
        let variables = self.variables();
        let summands = self.into_iter().cloned().filter_map(|mut assignment| {
            if assignment.remove(wrt) && assignment.live_variables() == 0 {
                None
            } else {
                Some(assignment)
            }
        });
        Self::from_summands(variables, summands)
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
                new.flip(&(left.clone() | right));
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
                new.flip(&(left.clone() | right));
            }
        }
        *self = new;
    }
}

impl<F: BitViewSized + Clone> BitXorAssign<&Anf<F>> for Anf<F> {
    /// Return `lhs ^ rhs` as a new ANF.
    ///
    /// Given the algebraic normal form of functions l(x), r(x) : GF\[2]ⁿ -> GF\[2], stored as
    /// [Summands](Anf)(l) and [Summands](Anf)(r), this returns out(x) := l(x) ^ r(x) as
    /// Summands(l ^ r) = Summands(l) △ Summands(r).
    fn bitxor_assign(&mut self, rhs: &Anf<F>) {
        assert_eq!(self.variables(), rhs.variables());
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
        self.negate();
        self
    }
}
