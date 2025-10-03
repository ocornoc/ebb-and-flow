use std::fmt::{Debug, Display};
use std::iter::FusedIterator;
use std::ops::{Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Mul, MulAssign, Not};
use bitvec::view::BitViewSized;
use super::{assignment::AndNotIter, SparseTree, Variable, VectorAssignment};

/// A function f : GF\[2]ⁿ -> GF\[2] stored as the summands of the algebraic normal form of f.
///
/// Every function f : GF\[2]ⁿ -> GF\[2] can be represented by ⨁ S ⊆ {0, 1}ⁿ, φ(f, S) xˢ where 
/// the Mobius transformation φ(f, S) := ⨁ T ≼ S, f(xˢ). We use a sparse representation of the set
/// of minterms of f that evaluate φ(f, S) to 1, defined as Summands(f) := { S | φ(f, S) = 1 }.
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

    #[inline]
    pub fn iter_summands(&self) -> <&SparseTree<F> as IntoIterator>::IntoIter {
        self.0.iter()
    }

    #[inline]
    fn iter_intersecting_aux<'iter>(
        &'iter self,
        intersectant: &'_ VectorAssignment<F>,
    ) -> Intersecting<
        'iter,
        F,
        impl FnMut(&'_ &'iter VectorAssignment<F>) -> bool,
    > {
        self.iter_summands().filter(|summand| summand.intersects(intersectant))
    }

    #[inline]
    pub fn iter_intersecting<'iter>(
        &'iter self,
        intersectant: &'_ VectorAssignment<F>,
    ) -> impl FusedIterator<Item = &'iter VectorAssignment<F>> {
        self.iter_intersecting_aux(intersectant)
    }
}

type Intersecting<'iter, F, Fn> = std::iter::Filter<
    <&'iter SparseTree<F> as IntoIterator>::IntoIter,
    Fn,
>;

type TranslatedInput<'iter, F, Fn1, Fn2> = std::iter::FlatMap<
    Intersecting<'iter, F, Fn1>,
    AndNotIter<F>,
    Fn2,
>;

impl<F: BitViewSized + Clone> AlgebraicNormalForm<F> {
    pub fn one(variables: Variable) -> Self {
        !Anf::empty(variables)
    }

    pub fn toggle(&mut self, summand: &VectorAssignment<F>) {
        self.0.toggle(summand);
    }

    /// Define a multilinear function by the summands it contains.
    ///
    /// Every function f : GF\[2]ⁿ -> GF\[2] is a multilinear function. This constructor provides a
    /// convenient way to create the algebraic normal form representation of f with an iterator over
    /// its summands. If an iterator output is repeated, this function does *not* remove the entry
    /// from the algebraic normal form and simply keeps the original entry as-is; thus, this
    /// constructor is *not* the same as summing many terms. For a function that represents summing
    /// many terms, see [`Anf::from_summands`].
    ///
    /// ```
    /// # use ebb_and_flow::sparse::{Anf, VectorAssignment};
    /// let f = Anf::from_iter(5, [
    ///     0b00000_u64.into(),
    ///     0b00001_u64.into(),
    ///     0b00100_u64.into(),
    ///     0b01101_u64.into(),
    ///     0b10001_u64.into(), // This element is inserted twice...
    ///     0b10001_u64.into(), // but should remain in the ANF.
    ///     0b11000_u64.into(),
    /// ]);
    /// // 6 instead of 7 because the duplicated term is only inserted once.
    /// assert_eq!(f.iter_summands().count(), 6);
    /// let g = Anf::from_iter(5, [
    ///     0b00000_u64.into(),
    ///     0b00001_u64.into(),
    ///     0b00100_u64.into(),
    ///     0b01101_u64.into(),
    ///     0b10001_u64.into(), // Here, we only insert it once.
    ///     0b11000_u64.into(),
    /// ]);
    /// assert_eq!(f, g);
    /// ```
    pub fn from_iter(
        variables: Variable,
        iter: impl IntoIterator<Item = VectorAssignment<F>>,
    ) -> Self {
        let mut new = Self::empty(variables);
        new.0.heap.extend(iter);
        new
    }

    /// Define a multilinear function by summing many [terms](VectorAssignment).
    ///
    /// Every function f : GF\[2]ⁿ -> GF\[2] is a multilinear function. This constructor provides a
    /// convenient way to create the algebraic normal form representation of f with an iterator over
    /// its summands. If an iterator output is repeated, this function *does* remove the entry
    /// from the algebraic normal form; thus, this constructor is equivalent to summing many terms.
    /// For a function that will not toggle duplicated iterator outputs, see  [`Anf::from_iter`].
    ///
    /// ```
    /// # use ebb_and_flow::sparse::{Anf, VectorAssignment};
    /// let f = Anf::from_summands(5, [
    ///     0b00000_u64.into(),
    ///     0b00001_u64.into(),
    ///     0b00100_u64.into(),
    ///     0b01101_u64.into(),
    ///     0b10001_u64.into(), // This element is summed twice...
    ///     0b10001_u64.into(), // and thus will be removed (x + x = 0 in GF[2]).
    ///     0b11000_u64.into(), // This element is summed thrice...
    ///     0b11000_u64.into(), // and thus will end up being contained in the ANF.
    ///     0b11000_u64.into(), // (x + x + x = 0 + x = x in GF[2])
    /// ]);
    /// // 5 instead of 9 because the duplicated term ends up not present while the triplicated term
    /// // will be present only once.
    /// assert_eq!(f.iter_summands().count(), 5);
    /// let g = Anf::from_summands(5, [
    ///     0b00000_u64.into(),
    ///     0b00001_u64.into(),
    ///     0b00100_u64.into(),
    ///     0b01101_u64.into(),
    ///     // We skip 0b10001_u64.into().
    ///     0b11000_u64.into(), // We keep this entry once.
    /// ]);
    /// assert_eq!(f, g);
    /// ```
    pub fn from_summands(
        variables: Variable,
        summands: impl IntoIterator<Item = VectorAssignment<F>>,
    ) -> Self {
        let mut new = Self::empty(variables);
        for summand in summands {
            new.toggle(&summand);
        }
        new
    }

    /// Swap all occurences of one variable with another, and vice versa.
    #[must_use]
    pub fn swap_variables(&self, v1: Variable, v2: Variable) -> Self {
        AlgebraicNormalForm(self.0.swap_variables(v1, v2))
    }

    /// Replace every occurence of a variable in the support of self with the product of other
    /// variables.
    ///
    /// This is a special case of [`substitute_subterm`](Anf::substitute_subterm) where the subterm
    /// is the singular vector containing the variable.
    ///
    /// If the variable being subtituted is also present in the replacement minterm, then that
    /// variable will remain in the minterm instead of being removed.
    #[must_use]
    pub fn substitute_variable(&self, variable: Variable, replacement: &VectorAssignment<F>) -> Self {
        Self::from_iter(self.variables(), self.into_iter().cloned().map(|mut assignment| {
            if assignment.remove(variable) {
                assignment |= replacement;
            }
            assignment
        }))
    }

    /// Iterate over the union of the supports of self(x) and other(x).
    #[inline]
    pub fn union_iter<'iter>(
        &'iter self,
        other: &'iter Self,
    ) -> impl FusedIterator<Item = &'iter VectorAssignment<F>> {
        debug_assert_eq!(self.variables(), other.variables());
        self.0.heap.union(&other.0.heap)
    }

    /// Calculate the function with support equal to the union of the supports of self(x) and
    /// other(x).
    pub fn union(mut self, other: &Self) -> Self {
        self.union_assign(other);
        self
    }

    /// Assign self to the [union](Anf::union) between self(x) and other(x).
    pub fn union_assign(&mut self, other: &Self) {
        self.0.heap.extend(other.iter_summands().cloned());
    }

    /// Iterate over the intersection of the supports of self(x) and other(x).
    #[inline]
    pub fn intersection_iter<'iter>(
        &'iter self,
        other: &'iter Self,
    ) -> impl FusedIterator<Item = &'iter VectorAssignment<F>> {
        debug_assert_eq!(self.variables(), other.variables());
        self.0.heap.intersection(&other.0.heap)
    }

    /// Calculate the function with support equal to the intersection of the supports of self(x) and
    /// other(x).
    pub fn intersection(mut self, other: &Self) -> Self {
        self.intersect_assign(other);
        self
    }

    /// Assign self to the [intersection](Anf::intersection) between self(x) and other(x).
    pub fn intersect_assign(&mut self, other: &Self) {
        *self = Anf::from_summands(self.variables(), self.intersection_iter(other).cloned());
    }

    /// Given a [boolean vector function](AlgebraicNormalForm) f(x), update f(x) in-place with
    /// definition g(x) := !f(x) = 1 ⊕ f(x).
    pub fn not_assign(&mut self) {
        // Adding 1 to f(x) is equal to toggling 1's assignment. 1's assignment is equal to the
        // empty assignment, e.g. is an always-true constant.
        self.toggle(&VectorAssignment::none());
    }

    /// Calculate the partial derivative of self(x) with respect to a given variable.
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
    fn with_translated_input_iter_aux<'iter>(
        &'iter self,
        direction: &'iter VectorAssignment<F>,
    ) -> TranslatedInput<
        'iter,
        F,
        impl FnMut(&'_ &'iter VectorAssignment<F>) -> bool,
        impl FnMut(&'iter VectorAssignment<F>) -> AndNotIter<F>,
    > {
        self
            .iter_intersecting_aux(direction)
            .flat_map(move |summand| {
                let negated_mask = summand.clone() & direction;
                let unconditional = !direction.clone() & summand;
                AndNotIter::new(negated_mask, unconditional)
            })
    }

    #[inline]
    pub fn with_translated_input_iter<'iter>(
        &'iter self,
        direction: &'iter VectorAssignment<F>,
    ) -> impl FusedIterator<Item = VectorAssignment<F>> {
        self.with_translated_input_iter_aux(direction)
    }

    /// Calculate the derivative of self(x) in a particular direction.
    ///
    /// The direction chooses which variables are *not* considered constant when taking the
    /// derivative. The total derivative of self is a special case of this function where the
    /// direction vector is all ones. The partial derivative of self with respect to variable `v`
    /// is a special case where the direction vector is one-hot at `v`.
    pub fn directional_derivative(&self, direction: &VectorAssignment<F>) -> Self {
        // The minterms of the multilinear function self(x ⊕ direction)
        let summands_with_shifted_input = self.with_translated_input_iter(direction);
        // Derivative wrt direction := filtered(x) ⊕ filtered(x ⊕ direction), where filtered(x) is
        // self(x) with all summands disjoint from direction removed.
        Anf::from_summands(
            self.variables(),
            self
                .iter_intersecting(direction)
                .cloned()
                .chain(summands_with_shifted_input),
        )
    }

    /// Calculate the homogeneity of self(x).
    ///
    /// The homogeneity differential operator is defined as the sum of every variable multiplied by
    /// the partial derivative of `self` with respect to that variable.
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

    /// Calculate the divergence of self(x), which is the sum of all of its partial derivatives.
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
    /// Addition for algebraic normal forms interpreted as functions in the vector space of
    /// GF\[2]ⁿ -> GF\[2].
    ///
    /// Given that this is definitionally equal to XORing two algebraic normal forms, see the
    /// documentation at `AlgebraicNormalForm<F>::xor_assign`.
    fn add_assign(&mut self, rhs: &Anf<F>) {
        BitXorAssign::bitxor_assign(self, rhs);
    }
}

impl<F: BitViewSized + Clone> MulAssign<&Anf<F>> for Anf<F> {
    /// Multiplication for algebraic normal forms interpreted as functions in the vector space of
    /// GF\[2]ⁿ -> GF\[2].
    ///
    /// Given that this is definitionally equal to ANDing two algebraic normal forms, see the
    /// documentation at `AlgebraicNormalForm<F>::and_assign`.
    fn mul_assign(&mut self, rhs: &Anf<F>) {
        BitAndAssign::bitand_assign(self, rhs);
    }
}

impl<F: BitViewSized + Clone> BitAndAssign<&Anf<F>> for Anf<F> {
    /// Return lhs & rhs in algebraic normal form.
    ///
    /// Given the algebraic normal form of functions l(x), r(x) : GF\[2]ⁿ -> GF\[2], stored as
    /// [Summands](Anf)(l) and [Summands](Anf)(r), this returns out(x) := l(x) & r(x) as
    /// Summands(l & r) = { (left | right) | (left, right) ∈ l x r }. Using (left | right) instead
    /// of (left & right) may be unintuitive but is correct as (left | right) represents an
    /// assignment where all assignments in left and all assignments in right must be simultaneously
    /// true. This is calculated as a bitwise or of their representations to give us left ∧ right.
    ///
    /// ```
    /// # use ebb_and_flow::sparse::{Anf, Variable, VectorAssignment};
    /// // (0 : Anf<F>) & (0 : Anf<F>) == (0 : Anf<F>)
    /// assert_eq!(Anf::<[u32; 1]>::empty(8) & Anf::empty(8), Anf::empty(8));
    ///
    /// # const VARIABLES: Variable = 3;
    /// let number_of_scalars = 1_u32.checked_shl(VARIABLES as u32).unwrap();
    /// let number_of_anfs = 1_u32.checked_shl(number_of_scalars).unwrap();
    /// let zero = Anf::<[u32; 1]>::empty(VARIABLES);
    /// let one = Anf::<[u32; 1]>::one(VARIABLES);
    /// for mut anf_code in 0..number_of_anfs {
    ///     let mut anf = Anf::empty(VARIABLES);
    ///     while anf_code > 0 {
    ///         anf.insert([anf_code & (number_of_scalars - 1)].into());
    ///         anf_code >>= VARIABLES as u32;
    ///     }
    ///     // Any element v : Anf<F> aka GF[2]ⁿ -> GF[2] multiplied by zero is zero.
    ///     assert_eq!(zero.clone() & &anf, zero);
    ///     // Any element v : Anf<F> aka GF[2]ⁿ -> GF[2] multiplied by one is itself.
    ///     assert_eq!(one.clone() & &anf, anf);
    /// }
    /// ```
    fn bitand_assign(&mut self, rhs: &Anf<F>) {
        assert_eq!(self.variables(), rhs.variables());
        let mut new = Anf::empty(self.variables());
        for left in self.iter_summands() {
            for right in rhs.iter_summands() {
                // For every pair (left, right) in the Cartesian product lhs x rhs, insert the
                // variable representing "all of left and all of right necessary at once",
                // represented by BitOring the variable assignment bits.
                new.insert(left.clone() | right);
            }
        }
        *self = new;
    }
}

impl<F: BitViewSized + Clone> BitOrAssign<&Anf<F>> for Anf<F> {
    /// Return lhs | rhs in algebraic normal form.
    ///
    /// Given the algebraic normal form of functions l(x), r(x) : GF\[2]ⁿ -> GF\[2], stored as
    /// [Summands](Anf)(l) and [Summands](Anf)(r), this returns out(x) := l(x) | r(x) as
    /// Summands(l | r) = { (left | right) | left, right ∈ l ∪ r }.
    ///
    /// ```
    /// # use ebb_and_flow::sparse::{Anf, Variable, VectorAssignment};
    /// // (0 : Anf<F>) | (0 : Anf<F>) == (0 : Anf<F>)
    /// assert_eq!(Anf::<[u32; 1]>::empty(8) | Anf::empty(8), Anf::empty(8));
    ///
    /// # const VARIABLES: Variable = 4;
    /// let number_of_scalars = 1_u32.checked_shl(VARIABLES as u32).unwrap();
    /// let number_of_anfs = 1_u32.checked_shl(number_of_scalars).unwrap();
    /// let zero = Anf::<[u32; 1]>::empty(VARIABLES);
    /// for mut anf_code in 0..number_of_anfs {
    ///     let mut anf = Anf::empty(VARIABLES);
    ///     while anf_code > 0 {
    ///         anf.insert([anf_code & (number_of_scalars - 1)].into());
    ///         anf_code >>= VARIABLES as u32;
    ///     }
    ///     // (0 : Anf<F>) | (v : Anf<F>) == v.
    ///     assert_eq!(zero.clone() | &anf, anf, "zero OR anf == anf");
    /// }          
    /// ```
    fn bitor_assign(&mut self, rhs: &Anf<F>) {
        assert_eq!(self.variables(), rhs.variables());
        let mut new = self.clone().union(rhs);
        for left in self.intersection_iter(rhs) {
            new.0.heap.extend(rhs.clone() & left);
        }
        *self = new;
    }
}

impl<F: BitViewSized + Clone> BitXorAssign<&Anf<F>> for Anf<F> {
    /// Return lhs ⊕ rhs in algebraic normal form.
    ///
    /// Given the algebraic normal form of functions l(x), r(x) : GF\[2]ⁿ -> GF\[2], stored as
    /// [Summands](Anf)(l) and [Summands](Anf)(r), this returns out(x) := l(x) ⊕ r(x) as
    /// Summands(l ⊕ r) = Summands(l) △ Summands(r).
    ///
    /// ```
    /// # use ebb_and_flow::sparse::{Anf, Variable, VectorAssignment};
    /// // (0 : Anf<F>) ⊕ (0 : Anf<F>) == (0 : Anf<F>)
    /// assert_eq!(Anf::<[u32; 1]>::empty(8) & Anf::empty(8), Anf::empty(8));
    ///
    /// # const VARIABLES: Variable = 3;
    /// let number_of_scalars = 1_u32.checked_shl(VARIABLES as u32).unwrap();
    /// let number_of_anfs = 1_u32.checked_shl(number_of_scalars).unwrap();
    /// let zero = Anf::<[u32; 1]>::empty(VARIABLES);
    /// let one = Anf::<[u32; 1]>::one(VARIABLES);
    /// for mut anf_code in 0..number_of_anfs {
    ///     let mut anf = Anf::empty(VARIABLES);
    ///     while anf_code > 0 {
    ///         anf.insert([anf_code & (number_of_scalars - 1)].into());
    ///         anf_code >>= VARIABLES as u32;
    ///     }
    ///     // Any element v : Anf<F> aka GF[2]ⁿ -> 2 plus zero is itself.
    ///     assert_eq!(zero.clone() ^ &anf, anf);
    ///     // Any element v : Anf<F> aka GF[2]ⁿ -> 2 plus one is not itself.
    ///     assert_ne!(one.clone() ^ &anf, anf);
    ///     // Any element v : Anf<F> aka GF[2]ⁿ -> 2 plus one plus one is itself.
    ///     assert_eq!(one.clone() ^ &anf ^ one.clone(), anf);
    ///     for mut rhs_anf_code in 0..number_of_anfs {
    ///         let mut rhs_anf = Anf::empty(VARIABLES);
    ///         while rhs_anf_code > 0 {
    ///             rhs_anf.insert([rhs_anf_code & (number_of_scalars - 1)].into());
    ///             rhs_anf_code >>= VARIABLES as u32;
    ///         }
    ///         // Bitxor is commutative.
    ///         assert_eq!(anf.clone() ^ &rhs_anf, rhs_anf ^ anf.clone());
    ///     }
    /// }
    /// ```
    fn bitxor_assign(&mut self, rhs: &Anf<F>) {
        assert_eq!(self.variables(), rhs.variables());
        // Naively, we should make some empty Anf called "new" and iterate as follows:
        // for assignment in self.0.heap.symmetric_difference(&rhs.0.heap) {
        //     new.insert(summand);
        // }
        // But we can save the allocation and re-use self by just toggling every element in self by
        // its containment in rhs. If it's not in rhs, it's the same as self's value. If it is in
        // rhs, then we must toggle its entry.
        for summand in rhs.iter_summands() {
            self.toggle(summand);
        }
    }
}

move_from_ref_reqs! {
    Add = Anf where F: BitViewSized + Clone => AddAssign; add := add_assign,
    BitAnd = Anf where F: BitViewSized + Clone => BitAndAssign; bitand := bitand_assign,
    BitOr = Anf where F: BitViewSized + Clone => BitOrAssign; bitor := bitor_assign,
    BitXor = Anf where F: BitViewSized + Clone => BitXorAssign; bitxor := bitxor_assign,
    Mul = Anf where F: BitViewSized + Clone => MulAssign; mul := mul_assign,
}

impl<F: BitViewSized + Clone> BitAndAssign<&VectorAssignment<F>> for Anf<F> {
    /// Returns lhs & rhs as a new algebraic normal form.
    ///
    /// ```
    /// # use ebb_and_flow::sparse::{Anf, Variable, VectorAssignment};
    /// // (0 : Anf<F>) & (0 : VectorAssignment<F>) == (0 : Anf<F>)
    /// assert_eq!(Anf::<[u32; 1]>::empty(8) & VectorAssignment::none(), Anf::empty(8));
    ///
    /// # const VARIABLES: Variable = 4;
    /// let number_of_scalars = 1_u32.checked_shl(VARIABLES as u32).unwrap();
    /// let number_of_anfs = 1_u32.checked_shl(number_of_scalars).unwrap();
    /// let true_scalar = VectorAssignment::none();
    /// let zero_anf = Anf::<[u32; 1]>::empty(VARIABLES);
    /// for mut anf_code in 0..number_of_anfs {
    ///     // (v : Anf<F>) & (1 : GF[2]ⁿ) == v
    ///     let mut v = Anf::empty(VARIABLES);
    ///     while anf_code > 0 {
    ///         v.insert([anf_code & (number_of_scalars - 1)].into());
    ///         anf_code >>= VARIABLES as u32;
    ///     }
    ///     assert_eq!(v.clone() & &true_scalar, v);
    /// }
    /// for scalar in 0..number_of_scalars {
    ///     // (0 : Anf<F>) & (s : GF[2]ⁿ) == (0 : Anf<F>)
    ///     let s = Anf::from_summands(VARIABLES, [[scalar].into()]);
    ///     assert_eq!(zero_anf.clone() & VectorAssignment::default(), zero_anf);
    /// }
    /// ```
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

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.heap.into_iter()
    }
}

impl<'a, F: BitViewSized> IntoIterator for &'a Anf<F> {
    type Item = &'a VectorAssignment<F>;
    type IntoIter = <&'a SparseTree<F> as IntoIterator>::IntoIter;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_summands()
    }
}

impl<F: BitViewSized + Clone> Not for Anf<F> {
    type Output = Self;

    /// Calculate the logical negation of this boolean vector function.
    ///
    ///  ```
    /// # use ebb_and_flow::sparse::{Anf, Variable, VectorAssignment};
    /// # const VARIABLES: Variable = 4;
    /// let number_of_scalars = 1_u32.checked_shl(VARIABLES as u32).unwrap();
    /// let number_of_anfs = 1_u32.checked_shl(number_of_scalars).unwrap();
    /// let zero = Anf::<[u32; 1]>::empty(VARIABLES);
    /// let one = !zero.clone();
    /// assert_eq!(one, Anf::one(VARIABLES), "!0 == 1");
    /// assert_ne!(zero, one, "0 =/= !0");
    /// assert_eq!(zero, !one.clone(), "!!0 == 0");
    /// ```
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
        if first {
            write!(f, "0")
        } else {
            Ok(())
        }
    }
}

impl<F: BitViewSized> Display for Anf<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}
