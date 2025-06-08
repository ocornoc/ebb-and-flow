use std::collections::BTreeSet;
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};

use bitvec::array::BitArray;
use bitvec::view::BitViewSized;

type Fundamental = u64;
const FUNDAMENTAL_ARRAY_LEN: usize = 384 / (Fundamental::BITS / u8::BITS) as usize;

type MintermRepr<F> = BitArray<F>;
type AesMinterm = VectorAssignment<[Fundamental; FUNDAMENTAL_ARRAY_LEN]>;

#[derive(Debug, Clone)]
struct VectorAssignment<F: BitViewSized>(MintermRepr<F>);

impl<F: BitViewSized> VectorAssignment<F> {
    pub fn none() -> Self {
        VectorAssignment(MintermRepr::ZERO)
    }

    pub fn is_subset_of(&self, mask: &Self) -> bool {
        self.0.contains(&mask.0)
    }
}

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

all_from_scalar! {
    BitAnd = VectorAssignment => BitAndAssign; bitand := bitand_assign,
    BitOr = VectorAssignment => BitOrAssign; bitor := bitor_assign,
    BitXor = VectorAssignment => BitXorAssign; bitxor := bitxor_assign,
}

impl<F: BitViewSized> Not for VectorAssignment<F> {
    type Output = Self;

    #[inline]
    fn not(self) -> Self {
        VectorAssignment(!self.0)
    }
}

impl<F: BitViewSized + PartialEq> PartialEq for VectorAssignment<F> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    #[inline]
    fn ne(&self, other: &Self) -> bool {
        self.0 != other.0
    }
}

impl<F: BitViewSized + Eq> Eq for VectorAssignment<F> {}

impl<F: BitViewSized + PartialOrd> PartialOrd for VectorAssignment<F> {
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

impl<F: BitViewSized + Ord> Ord for VectorAssignment<F> {
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

type Variable = u16;

struct SparseTree<F: BitViewSized> {
    variables: Variable,
    mask: Box<VectorAssignment<F>>,
    heap: BTreeSet<VectorAssignment<F>>,
}

impl<F: BitViewSized + Ord> SparseTree<F> {
    fn make_mask(variables: Variable) -> Box<VectorAssignment<F>> {
        let mut assignment = Box::new(VectorAssignment::none());
        assert!(1 << variables <= assignment.0.len());
        for mut mask_bit in assignment.0.iter_mut().take(variables as usize) {
            *mask_bit = true;
        }
        assignment
    }

    fn empty(variables: Variable) -> Self {
        SparseTree {
            variables,
            mask: Self::make_mask(variables),
            heap: BTreeSet::new(),
        }
    }

    fn push(&mut self, assignment: VectorAssignment<F>) {
        debug_assert!(assignment.is_subset_of(&self.mask));
        self.heap.insert(assignment);
    }

    fn remove(&mut self, assignment: &VectorAssignment<F>) {
        debug_assert!(assignment.is_subset_of(&self.mask));
        self.heap.remove(assignment);
    }

    fn contains(&self, assignment: &VectorAssignment<F>) -> bool {
        debug_assert!(assignment.is_subset_of(&self.mask));
        self.heap.contains(assignment)
    }

    fn iter(&self) -> <&SparseTree<F> as IntoIterator>::IntoIter {
        self.into_iter()
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

impl<F: BitViewSized + Ord> BitAndAssign<&SparseTree<F>> for SparseTree<F> {
    fn bitand_assign(&mut self, rhs: &SparseTree<F>) {
        self.heap.retain(|assignment| rhs.contains(assignment));
    }
}

impl<F: BitViewSized + Ord + Clone> BitOrAssign<&SparseTree<F>> for SparseTree<F> {
    fn bitor_assign(&mut self, rhs: &SparseTree<F>) {
        self.heap.extend(rhs.into_iter().cloned());
    }
}

impl<F: BitViewSized + Ord> BitOrAssign for SparseTree<F> {
    fn bitor_assign(&mut self, rhs: Self) {
        self.heap.extend(rhs.heap);
    }
}

impl<F: BitViewSized + Ord + Clone> BitOr<&SparseTree<F>> for SparseTree<F> {
    type Output = Self;

    fn bitor(mut self, rhs: &Self) -> Self {
        self.bitor_assign(rhs);
        self
    }
}

impl<F: BitViewSized + Ord + Clone> BitOr<SparseTree<F>> for &SparseTree<F> {
    type Output = SparseTree<F>;

    fn bitor(self, rhs: SparseTree<F>) -> SparseTree<F> {
        rhs | self
    }
}

impl<F: BitViewSized + Ord> BitOr for SparseTree<F> {
    type Output = Self;

    fn bitor(mut self, rhs: Self) -> Self {
        self.bitor_assign(rhs);
        self
    }
}

impl<F: BitViewSized + Ord> BitXorAssign<&SparseTree<F>> for SparseTree<F> {
    fn bitxor_assign(&mut self, rhs: &SparseTree<F>) {
        for assignment in rhs.iter() {
            if self.heap.contains(assignment) {
                self.remove(assignment);
            }
        }
    }
}

move_from_ref_reqs! {
    BitAnd = SparseTree where F: BitViewSized + Ord => BitAndAssign; bitand := bitand_assign,
    BitXor = SparseTree where F: BitViewSized + Ord => BitXorAssign; bitxor := bitxor_assign,
}

pub struct TruthTable<F: BitViewSized>(SparseTree<F>);

all_from_scalar!(
    BitAnd = TruthTable where F: BitViewSized + Ord => BitAndAssign; bitand := bitand_assign,
    BitOr = TruthTable where F: BitViewSized + Ord + Clone => BitOrAssign; bitor := bitor_assign,
    BitXor = TruthTable where F: BitViewSized + Ord => BitXorAssign; bitxor := bitxor_assign,
);

pub struct AlgebraicNormalForm<F: BitViewSized>(SparseTree<F>);

pub type Anf<F> = AlgebraicNormalForm<F>;

impl<F: BitViewSized + Ord + Clone> BitAndAssign<&Anf<F>> for Anf<F> {
    fn bitand_assign(&mut self, rhs: &Anf<F>) {
        assert_eq!(self.0.variables, rhs.0.variables);
        let mut new = AlgebraicNormalForm(SparseTree::empty(self.0.variables));
        for left in self.0.heap.iter() {
            for right in rhs.0.heap.iter() {
                new.0.push(left.clone() | right);
            }
        }
        *self = new;
    }
}

fn bitor_assign_except_rhs<F: BitViewSized + Ord + Clone>(lhs: &mut Anf<F>, rhs: &Anf<F>) {
    assert_eq!(lhs.0.variables, rhs.0.variables);
    let mut new = AlgebraicNormalForm(SparseTree::empty(lhs.0.variables));
    for left in lhs.0.heap.iter() {
        for right in rhs.0.heap.difference(&lhs.0.heap) {
            new.0.push(left.clone() | right);
        }
    }
    lhs.0.heap.append(&mut new.0.heap);
}

impl<F: BitViewSized + Ord + Clone> BitOrAssign<&Anf<F>> for Anf<F> {
    fn bitor_assign(&mut self, rhs: &Anf<F>) {
        bitor_assign_except_rhs(self, rhs);
        self.0.heap.extend(rhs.0.iter().cloned());
    }
}

impl<F: BitViewSized + Ord + Clone> BitOrAssign<Anf<F>> for Anf<F> {
    fn bitor_assign(&mut self, mut rhs: Anf<F>) {
        bitor_assign_except_rhs(self, &rhs);
        self.0.heap.append(&mut rhs.0.heap);
    }
}

impl<F: BitViewSized + Ord + Clone> BitOr<Anf<F>> for Anf<F> {
    type Output = Self;

    fn bitor(mut self, rhs: Anf<F>) -> Self {
        self |= rhs;
        self
    }
}

impl<F: BitViewSized + Ord + Clone> BitOr<&Anf<F>> for Anf<F> {
    type Output = Self;

    fn bitor(mut self, rhs: &Anf<F>) -> Self {
        self |= rhs;
        self
    }
}

impl<F: BitViewSized + Ord + Clone> BitOr<Anf<F>> for &Anf<F> {
    type Output = Anf<F>;

    fn bitor(self, rhs: Anf<F>) -> Anf<F> {
        rhs | self
    }
}

move_from_ref_reqs! {
    BitAnd = Anf where F: BitViewSized + Ord + Clone => BitAndAssign; bitand := bitand_assign,
}

all_from_scalar! {
    BitXor = Anf where F: BitViewSized + Ord => BitXorAssign; bitxor := bitxor_assign,
}
