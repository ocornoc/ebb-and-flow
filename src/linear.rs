use std::ops::BitXorAssign;

use bitvec::array::BitArray;
use bitvec::order::LocalBits;
use bitvec::vec::BitVec;

#[derive(Debug)]
/// Makes 
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

/// Transform an assignment into a word index and its respective bit.
#[inline]
fn assignment_to_index_offset(assignment: usize) -> (usize, u8) {
    (assignment / usize::BITS as usize, (assignment % usize::BITS as usize) as u8)
}

/// Create an all-zero [`BitVec`] of a given length.
fn empty_xor_ands(vars: usize) -> BitVec<usize> {
    let capacity = 1_usize.checked_shl(vars as u32).unwrap().div_ceil(usize::BITS as usize);
    std::iter::repeat_n(0_usize, capacity).collect()
}

fn fill_truth_table(vars: usize, f: impl FnMut(usize) -> bool) -> BitVec<usize> {
    (0..(1 << vars)).into_iter().map(f).collect()
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct TruthTable {
    pub bit_rep: BitVec<usize>,
}

impl TruthTable {
    pub fn zeros(vars: usize) -> Self {
        TruthTable {
            bit_rep: empty_xor_ands(vars),
        }
    }

    /// Map assignments to the truth table, given as n variables and assignments encoded as {0, 1}ⁿ.
    pub fn from_assignments(vars: usize, f: impl FnMut(usize) -> bool) -> Self {
        TruthTable {
            bit_rep: fill_truth_table(vars, f),
        }
    }
}

impl BitXorAssign<&TruthTable> for TruthTable {
    fn bitxor_assign(&mut self, rhs: &TruthTable) {
        *self.bit_rep ^= &rhs.bit_rep;
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct XorAnds {
    pub bit_rep: BitVec<usize>,
}

impl XorAnds {
    pub fn zeros(vars: usize) -> Self {
        XorAnds {
            bit_rep: empty_xor_ands(vars),
        }
    }

    fn transform_to_zhegalkin_inplace(&mut self, vars: usize) {
        let mut estimator = TimeEstimator::new(vars);
        for assignment in 0..(1 << vars) {
            estimator.report(assignment);
            let mut result = false;
            let mut subset = 0;
            while subset < assignment {
                result ^= unsafe {
                    *self.bit_rep.get_unchecked(subset)
                };
                subset = (subset | !assignment).wrapping_add(1) & assignment;
            }
            unsafe {
                *self.bit_rep.get_unchecked_mut(assignment) ^= result;
            }
        }
    }

    fn transform_to_zhegalkin(&mut self, vars: usize) {
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
        xor_ands.transform_to_zhegalkin_inplace(vars);
        xor_ands
    }

    /*
    pub fn derivative(&mut self) {
        let variables = self.bit_rep.len().trailing_zeros() + 1;
    }
    */
}

impl BitXorAssign<&XorAnds> for XorAnds {
    fn bitxor_assign(&mut self, rhs: &XorAnds) {
        *self.bit_rep ^= &rhs.bit_rep;
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
            for var in BitArray::<_, LocalBits>::new([subset]).iter_ones() {
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
