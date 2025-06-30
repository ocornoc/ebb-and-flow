use std::collections::BTreeSet;
use bitvec::view::BitViewSized;
use super::{Variable, VectorAssignment};

#[derive(Clone)]
pub struct SparseTree<F: BitViewSized> {
    pub variables: Variable,
    pub mask: Box<VectorAssignment<F>>,
    pub heap: BTreeSet<VectorAssignment<F>>,
}

impl<F: BitViewSized> SparseTree<F> {
    fn make_mask(variables: Variable) -> Box<VectorAssignment<F>> {
        let mut assignment = Box::new(VectorAssignment::none());
        assert!(variables as usize <= assignment.0.len());
        for mut mask_bit in assignment.0.iter_mut().take(variables as usize) {
            *mask_bit = true;
        }
        assignment
    }

    pub fn empty(variables: Variable) -> Self {
        SparseTree {
            variables,
            mask: Self::make_mask(variables),
            heap: BTreeSet::new(),
        }
    }

    /// Inserts a new element in to the sparse tree.
    ///
    /// Returns `true` when the assignment was newly inserted; i.e., it was not a member of the tree
    /// before this call.
    pub fn insert(&mut self, assignment: VectorAssignment<F>) -> bool {
        debug_assert!(
            assignment.is_subset_of(&self.mask),
            "Assignment {assignment} referenced invalid variables, thus cannot be inserted",
        );
        self.heap.insert(assignment)
    }

    pub fn remove(&mut self, assignment: &VectorAssignment<F>) -> bool {
        debug_assert!(
            assignment.is_subset_of(&self.mask),
            "Assignment {assignment} referenced invalid variables, thus cannot be removed",
        );
        self.heap.remove(assignment)
    }

    pub fn contains(&self, assignment: &VectorAssignment<F>) -> bool {
        debug_assert!(
            assignment.is_subset_of(&self.mask),
            "Assignment {assignment} referenced invalid variables, thus cannot check containment",
        );
        self.heap.contains(assignment)
    }

    pub fn iter(&self) -> <&SparseTree<F> as IntoIterator>::IntoIter {
        self.into_iter()
    }

    pub fn from_iter(
        variables: Variable,
        assignments: impl IntoIterator<Item = VectorAssignment<F>>,
    ) -> Self {
        SparseTree {
            heap: BTreeSet::from_iter(assignments),
            ..Self::empty(variables)
        }
    }

    fn reduce_or(&self) -> VectorAssignment<F> {
        self
            .iter()
            .fold(VectorAssignment::none(), |acc, assignment| acc | assignment)
    }

    pub fn count_live_variables(&self) -> usize {
        self.reduce_or().count_live_variables()
    }
}

impl<F: BitViewSized + Clone> SparseTree<F> {
    pub fn flip(&mut self, assignment: &VectorAssignment<F>) -> bool {
        if self.insert(assignment.clone()) {
            true
        } else {
            self.remove(assignment)
        }
    }

    #[must_use]
    pub fn swap_variables(&self, mut v1: Variable, mut v2: Variable) -> Self {
        // swapping a variable with itself is a no-op so exit early
        if v1 == v2 {
            return self.clone();
        }
        // v1 != v2 so set v1 to minimum and v2 to maximum, thus v1 < v2
        (v1, v2) = (v1.min(v2), v1.max(v2));
        // first possible assignment containing v1 is the bit vector with only v1 set
        let first_v1_possible = VectorAssignment::singular(v1);
        // assignments in [0, first_v1_possible) contain neither v1 nor v2 and will be unaffected
        let mut out = Self::from_iter(
            self.variables,
            self.heap.range(..&first_v1_possible).cloned(),
        );
        // assignments >= first_v1_possible may contain v1 or may contain v2 (as v1 < v2), so we
        // swap the variables without checking for containment to reduce branches
        for mut assignment in self.heap.range(&first_v1_possible..).cloned() {
            assignment.swap_variables(v1, v2);
            out.insert(assignment);
        }
        out
    }
}

impl<'tree, F: BitViewSized> IntoIterator for SparseTree<F> {
    type Item = VectorAssignment<F>;
    type IntoIter = std::collections::btree_set::IntoIter<VectorAssignment<F>>;

    fn into_iter(self) -> Self::IntoIter {
        self.heap.into_iter()
    }
}

impl<'tree, F: BitViewSized> IntoIterator for &'tree SparseTree<F> {
    type Item = &'tree VectorAssignment<F>;
    type IntoIter = std::collections::btree_set::Iter<'tree, VectorAssignment<F>>;

    fn into_iter(self) -> Self::IntoIter {
        (&self.heap).into_iter()
    }
}

impl<F: BitViewSized> PartialEq for SparseTree<F> {
    fn eq(&self, other: &Self) -> bool {
        self.heap == other.heap
    }

    fn ne(&self, other: &Self) -> bool {
        self.heap != other.heap
    }
}

impl<F: BitViewSized> Eq for SparseTree<F> {}
