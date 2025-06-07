use std::ops::SubAssign;
use std::ops::{AddAssign, BitAndAssign, BitOrAssign, BitXorAssign, MulAssign};
use bitvec::array::BitArray;
use bitvec::order::Lsb0;
use bitvec::vec::BitVec;

#[derive(Debug)]
struct TimeEstimator {
    start: std::time::Instant,
    next_report: usize,
    final_assignment: usize,
}

impl TimeEstimator {
    fn new(vars: usize) -> Self {
        TimeEstimator {
            // report once we've toggled the (variables-1)th variable, or the 16th variable
            // whichever is first
            next_report: 1,
            final_assignment: (1_usize << vars).saturating_sub(1),
            start: std::time::Instant::now(),
        }
    }

    #[cold]
    #[inline(never)]
    #[allow(unused)]
    fn make_report(&mut self, assignment: usize) {
        let average = assignment as f64 / self.start.elapsed().as_secs_f64();
        let remaining = (self.final_assignment - assignment) as f64 / average;
        self.next_report <<= 1;
        let remaining_next_report = (self.next_report - assignment) as f64 / average;
        eprintln!(
            "\
            reached {} bits ({average:.1}/s, \
            remaining={remaining:.1}s, \
            next report in {remaining_next_report:.1}s)",
            assignment.max(1).ilog2()
        );
    }

    #[inline]
    #[allow(unused)]
    fn report_if_ready(&mut self, assignment: usize) {
        if assignment >= self.next_report {
            self.make_report(assignment);
        }
    }

    #[inline]
    fn report(&mut self, assignment: usize) {
        #[cfg(feature = "timer")]
        self.report_if_ready(assignment);
        #[cfg(not(feature = "timer"))]
        let _ = assignment;
    }
}

/// Create an all-zero [`BitVec`] of a given length.
fn empty_xor_ands(vars: usize) -> BitVec<usize> {
    let capacity = 1_usize.checked_shl(vars as u32).unwrap().div_ceil(usize::BITS as usize);
    std::iter::repeat_n(0_usize, capacity).collect()
}

fn fill_bit_vec(vars: usize, f: impl FnMut(usize) -> bool) -> BitVec<usize> {
    (0..(1 << vars)).into_iter().map(f).collect()
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct TruthTable {
    pub(super) bit_rep: BitVec<usize>,
}

impl TruthTable {
    pub fn zeros(vars: usize) -> Self {
        TruthTable {
            bit_rep: empty_xor_ands(vars),
        }
    }

    pub fn count_variables(&self) -> usize {
        self.bit_rep.len().ilog2() as usize
    }

    /// Map assignments to the truth table, given as n variables and assignments encoded as {0, 1}ⁿ.
    pub fn from_assignments(vars: usize, f: impl FnMut(usize) -> bool) -> Self {
        TruthTable {
            bit_rep: fill_bit_vec(vars, f),
        }
    }

    pub fn from_anf(vars: usize, mut anf: XorAnds) -> Self {
        anf.zhegalkin_transform_inplace(vars);
        TruthTable {
            bit_rep: anf.bit_rep,
        }
    }

    pub fn to_anf(self, vars: usize) -> XorAnds {
        XorAnds::from_truth_table(vars, self)
    }

    pub fn fill_anf(&self, vars: usize, anf: &mut XorAnds) {
        anf.bit_rep.copy_from_bitslice(&self.bit_rep);
        anf.zhegalkin_transform_inplace(vars);
    }

    pub fn fill_from(&mut self, vars: usize, anf: &XorAnds) {
        anf.fill_truth_table(vars, self);
    }

    /// The weight of a boolean vector function f : GF\[2]ⁿ -> GF\[2], denoted "wt(f)", is the
    /// cardinality of f's support.
    ///
    /// This is, equivalently, the number of 1 bits in f's truth table.
    pub fn weight(&self) -> usize {
        self.bit_rep.count_ones()
    }

    pub fn is_balanced(&self) -> bool {
        self.weight() == self.bit_rep.len() >> 1
    }

    pub fn hamming_dist(&self, other: &Self) -> usize {
        debug_assert_eq!(self.bit_rep.len(), other.bit_rep.len());
        self.bit_rep.iter().zip(other.bit_rep.iter()).filter(|(l, r)| *l != *r).count()
    }

    #[must_use]
    pub fn directional_derivative(&self, direction: usize) -> Self {
        debug_assert!(direction < self.bit_rep.len());
        Self::from_assignments(
            self.count_variables(),
            |assignment| self.bit_rep[assignment] ^ self.bit_rep[assignment ^ direction],
        )
    }

    #[must_use]
    pub fn gradient(&self) -> impl ExactSizeIterator<Item = Self> {
        (0..self.count_variables())
            .into_iter()
            .map(|bit| self.directional_derivative(1 << bit))
    }

    #[must_use]
    pub fn divergence(&self) -> Self {
        let mut div = TruthTable::zeros(self.count_variables());
        for var in 0..self.count_variables() {
            div ^= &self.directional_derivative(1 << var);
        }
        div
    }

    #[must_use]
    pub fn homogeneity(&self) -> Self {
        let mut hom = TruthTable::zeros(self.count_variables());
        for var in 0..self.count_variables() {
            hom ^= &Self::from_assignments(
                self.count_variables(),
                |assignment| {
                    let deriv = self.bit_rep[assignment] ^ self.bit_rep[assignment ^ (1 << var)];
                    (assignment & (1 << var)) != 0 && deriv
                },
            );
        }
        hom
    }
}

impl BitAndAssign<&TruthTable> for TruthTable {
    fn bitand_assign(&mut self, rhs: &TruthTable) {
        *self.bit_rep &= &rhs.bit_rep;
    }
}

impl BitOrAssign<&TruthTable> for TruthTable {
    fn bitor_assign(&mut self, rhs: &TruthTable) {
        *self.bit_rep |= &rhs.bit_rep;
    }
}

impl BitXorAssign<&TruthTable> for TruthTable {
    fn bitxor_assign(&mut self, rhs: &TruthTable) {
        *self.bit_rep ^= &rhs.bit_rep;
    }
}

fn zhegalkin_transform_inplace(bit_rep: &mut BitVec<usize>, vars: usize) {
    debug_assert_eq!(bit_rep.len(), 1 << vars);
    let mut estimator = TimeEstimator::new(vars);
    for assignment in 0..(1 << vars) {
        estimator.report(assignment);
        let mut result = false;
        let mut subset = 0;
        while subset < assignment {
            result ^= unsafe {
                *bit_rep.get_unchecked(subset)
            };
            subset = (subset | !assignment).wrapping_add(1) & assignment;
        }
        unsafe {
            *bit_rep.get_unchecked_mut(assignment) ^= result;
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct XorAnds {
    pub(super) bit_rep: BitVec<usize>,
}

impl XorAnds {
    pub fn zeros(vars: usize) -> Self {
        XorAnds {
            bit_rep: empty_xor_ands(vars),
        }
    }

    fn zhegalkin_transform_inplace(&mut self, vars: usize) {
        zhegalkin_transform_inplace(&mut self.bit_rep, vars);
    }

    fn zhegalkin_transform(&mut self, vars: usize) {
        let mut estimator = TimeEstimator::new(vars);
        self.bit_rep = TruthTable::from_assignments(vars, |assignment| {
            estimator.report(assignment);
            let index = assignment / usize::BITS as usize;
            let mut carry = 0;
            for entry in self.bit_rep.as_raw_mut_slice().iter_mut().rev().skip(index) {
                let new_carry = *entry & 0b1;
                *entry ^= (*entry >> 1) ^ (carry << (usize::BITS - 1));
                carry = new_carry;
            }
            carry != 0
        }).bit_rep;
    }

    /// Transform from the truth table form, given n variables and assignments encoded as {0, 1}ⁿ.
    pub fn from_assignments(vars: usize, f: impl FnMut(usize) -> bool) -> Self {
        Self::from_truth_table(vars, TruthTable::from_assignments(vars, f))
    }

    pub fn from_truth_table(vars: usize, truth_table: TruthTable) -> Self {
        let mut xor_ands = XorAnds {
            bit_rep: truth_table.bit_rep,
        };
        xor_ands.zhegalkin_transform_inplace(vars);
        xor_ands
    }

    pub fn to_truth_table(self, vars: usize) -> TruthTable {
        TruthTable::from_anf(vars, self)
    }

    pub fn fill_truth_table(&self, vars: usize, truth_table: &mut TruthTable) {
        truth_table.bit_rep.copy_from_bitslice(&self.bit_rep);
        zhegalkin_transform_inplace(&mut truth_table.bit_rep, vars);
    }

    pub fn fill_from(&mut self, vars: usize, truth_table: &TruthTable) {
        truth_table.fill_anf(vars, self);
    }
}

impl AddAssign<&XorAnds> for XorAnds {
    /// Addition for GF\[2]ⁿ is componentwise XOR.
    fn add_assign(&mut self, rhs: &XorAnds) {
        *self ^= rhs;
    }
}

impl BitXorAssign<&XorAnds> for XorAnds {
    fn bitxor_assign(&mut self, rhs: &XorAnds) {
        *self.bit_rep ^= &rhs.bit_rep;
    }
}

impl BitAndAssign<&XorAnds> for XorAnds {
    /// Componentwise AND, aka the Hadamard product.
    fn bitand_assign(&mut self, rhs: &XorAnds) {
        *self.bit_rep &= &rhs.bit_rep;
    }
}

impl MulAssign<&XorAnds> for XorAnds {
    /// Multiplication for GF\[2]ⁿ is componentwise AND, aka the Hadamard product.
    fn mul_assign(&mut self, rhs: &XorAnds) {
        *self &= rhs;
    }
}

impl SubAssign<&XorAnds> for XorAnds {
    /// Subtraction for GF\[2]ⁿ is componentwise XOR.
    fn sub_assign(&mut self, rhs: &XorAnds) {
        *self += rhs;
    }
}

impl std::fmt::LowerHex for XorAnds {
    /// Write the digits starting at the constant a₀₀... ∈ {0, 1} of ⊕ S ⊆ {0, 1}^n, aₛxˢ.
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:x}", self.bit_rep)
    }
}

impl std::fmt::UpperHex for XorAnds {
    /// Write the digits starting at the constant a₀₀... ∈ {0, 1} of ⊕ S ⊆ {0, 1}^n, aₛxˢ.
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:X}", self.bit_rep)
    }
}

impl std::fmt::Binary for XorAnds {
    /// Write the digits starting at the constant a₀₀... ∈ {0, 1} of ⊕ S ⊆ {0, 1}^n, aₛxˢ.
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:b}", self.bit_rep)
    }
}

impl std::fmt::Display for XorAnds {
    /// Write the table as the multilinear form, ⊕ S ⊆ {0, 1}^n, aₛxˢ.
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut first_minterm = true;
        for subset in self.bit_rep.iter_ones() {
            if subset == 0 {
                write!(f, "1")?;
                first_minterm = false;
                continue;
            } else if first_minterm {
                first_minterm = false;
            } else {
                write!(f, " ⊕ ")?;
            }
            for var in BitArray::<_, Lsb0>::new([subset]).iter_ones() {
                write!(f, "x{var}")?;
            }
        }
        if first_minterm {
            write!(f, "0")
        } else {
            Ok(())
        }
    }
}
