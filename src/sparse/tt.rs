use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};
use bitvec::view::BitViewSized;
use super::{SparseTree, Variable, VectorAssignment};

pub struct TruthTable<F: BitViewSized>(pub(super) SparseTree<F>);

impl<F: BitViewSized> TruthTable<F> {
    pub fn variables(&self) -> Variable {
        self.0.variables
    }
}

impl<F: BitViewSized> TruthTable<F> {
    pub fn empty(variables: Variable) -> Self {
        TruthTable(SparseTree::empty(variables))
    }

    pub fn insert(&mut self, assignment: VectorAssignment<F>) -> bool {
        self.0.insert(assignment)
    }

    pub fn remove(&mut self, assignment: &VectorAssignment<F>) -> bool {
        self.0.remove(assignment)
    }

    pub fn evaluate(&self, assignment: &VectorAssignment<F>) -> bool {
        self.0.contains(assignment)
    }

    #[inline]
    pub fn modify_assignment(
        &mut self,
        assignment: VectorAssignment<F>,
        f: impl FnOnce(bool) -> bool,
    ) -> bool {
        // optimize to use feat(btree_set_entry) when stabilized
        if f(self.0.heap.contains(&assignment)) {
            self.insert(assignment)
        } else {
            self.remove(&assignment)
        }
    }

    pub fn set_assignment(&mut self, assignment: VectorAssignment<F>, present: bool) -> bool {
        self.modify_assignment(assignment, |_| present)
    }

    pub fn count_live_variables(&self) -> usize {
        self.0.count_live_variables()
    }
}

impl<F: BitViewSized + Clone> TruthTable<F> {
    pub fn toggle(&mut self, assignment: &VectorAssignment<F>) {
        self.0.toggle(assignment);
    }

    #[must_use]
    pub fn swap_variables(&self, v1: Variable, v2: Variable) -> Self {
        TruthTable(self.0.swap_variables(v1, v2))
    }
}

impl<F: BitViewSized> BitAndAssign<&TruthTable<F>> for TruthTable<F> {
    fn bitand_assign(&mut self, rhs: &TruthTable<F>) {
        self.0.heap.retain(|assignment| rhs.0.contains(assignment));
    }
}

impl<F: BitViewSized + Clone> BitOrAssign<&TruthTable<F>> for TruthTable<F> {
    fn bitor_assign(&mut self, rhs: &TruthTable<F>) {
        self.0.heap.extend(rhs.0.iter().cloned());
    }
}

impl<F: BitViewSized> BitOrAssign for TruthTable<F> {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0.heap.extend(rhs.0.heap);
    }
}

impl<F: BitViewSized + Clone> BitOr<&TruthTable<F>> for TruthTable<F> {
    type Output = Self;

    fn bitor(mut self, rhs: &Self) -> Self {
        self.bitor_assign(rhs);
        self
    }
}

impl<F: BitViewSized + Clone> BitOr<TruthTable<F>> for &TruthTable<F> {
    type Output = TruthTable<F>;

    fn bitor(self, rhs: TruthTable<F>) -> TruthTable<F> {
        rhs | self
    }
}

impl<F: BitViewSized> BitOr for TruthTable<F> {
    type Output = Self;

    fn bitor(mut self, rhs: Self) -> Self {
        self.bitor_assign(rhs);
        self
    }
}

impl<F: BitViewSized + Clone> BitXorAssign<&TruthTable<F>> for TruthTable<F> {
    fn bitxor_assign(&mut self, rhs: &TruthTable<F>) {
        for assignment in rhs.0.iter() {
            self.0.toggle(assignment);
        }
    }
}

move_from_ref_reqs! {
    BitAnd = TruthTable where F: BitViewSized => BitAndAssign; bitand := bitand_assign,
    BitXor = TruthTable where F: BitViewSized + Clone => BitXorAssign; bitxor := bitxor_assign,
}
