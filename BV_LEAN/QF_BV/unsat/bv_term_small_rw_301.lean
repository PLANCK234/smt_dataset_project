/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_301.smt2
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.ExactConditions
import LEMMAS_learned.BitVec.Shift.Characterization
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvshl_eq_bvlshr_bvlshr_of_lt_or_le (x y z : BitVec n)
    (h : y.toNat < 2 ^ z.toNat ∨ n * 2 ^ z.toNat ≤ y.toNat) :
    bvshl x (bvlshr y z) = bvlshr x (bvlshr y z) := by
  apply (bvshl_eq_bvlshr_forall_iff _).mpr _ x
  rw [toNat_bvlshr]
  rcases h with h | h
  · exact Or.inl (Nat.div_eq_of_lt h)
  · exact Or.inr ((Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr h)

def bv_term_small_rw_301 : Prop :=
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvlshr s (bvmul s s))) = (bvlshr s (bvlshr s (bvmul s s)))

theorem bv_term_small_rw_301_counterexample : ¬ bv_term_small_rw_301 := by
  intro h
  have hbad : ¬ ((bvshl (literal 2 3) (bvlshr (literal 2 3) (bvmul (literal 2 3) (literal 2 3)))) = (bvlshr (literal 2 3) (bvlshr (literal 2 3) (bvmul (literal 2 3) (literal 2 3))))) := by decide
  exact hbad (h 2 (literal 2 3) (literal 2 0))

theorem bv_term_small_rw_301_restricted
    (n : Nat) (s t : BitVec n)
    (h : s.toNat < 2 ^ ((s.toNat * s.toNat) % 2 ^ n) ∨
      n * 2 ^ ((s.toNat * s.toNat) % 2 ^ n) ≤ s.toNat) :
    (bvshl s (bvlshr s (bvmul s s))) = (bvlshr s (bvlshr s (bvmul s s))) := by
  apply bvshl_eq_bvlshr_bvlshr_of_lt_or_le
  simpa only [toNat_bvmul] using h

theorem bv_term_small_rw_301_counterexample_width10 :
    bvshl (literal 10 515)
        (bvlshr (literal 10 515) (bvmul (literal 10 515) (literal 10 515))) ≠
      bvlshr (literal 10 515)
        (bvlshr (literal 10 515) (bvmul (literal 10 515) (literal 10 515))) := by decide

/- Analysis:
The effective count is q=s.toNat/2^r, with r the square residue. Equality can hold for q in 1..n-1 (e.g. n=6, s=34), so the exact condition is ShiftBalanced; the width condition enumerates square roots of small residues.
Exact conditions: `_iff` per input, `_width_iff` per width; see ../EXACT_CONDITIONS.md.
-/

theorem bv_term_small_rw_301_iff (n : Nat) (s t : BitVec n) :
    ((bvshl s (bvlshr s (bvmul s s))) = (bvlshr s (bvlshr s (bvmul s s)))) ↔
      ShiftBalanced n s.toNat (s.toNat / 2 ^ ((s.toNat * s.toNat) % 2 ^ n)) := by
  simpa only [ShiftBalanced, toNat_bvlshr, toNat_bvmul] using
    (bvshl_eq_bvlshr_iff_dvd s (bvlshr s (bvmul s s)))

theorem bv_term_small_rw_301_width_iff (n : Nat) :
    (∀ s t : BitVec n, (bvshl s (bvlshr s (bvmul s s))) = (bvlshr s (bvlshr s (bvmul s s)))) ↔
      SquareWidth301 n := by
  have hpoint : (∀ s t : BitVec n, (bvshl s (bvlshr s (bvmul s s))) = (bvlshr s (bvlshr s (bvmul s s)))) ↔
      ∀ s t : BitVec n, ShiftBalanced n s.toNat (s.toNat / 2 ^ ((s.toNat * s.toNat) % 2 ^ n)) := by
    constructor
    · intro h s t; exact (bv_term_small_rw_301_iff n s t).mp (h s t)
    · intro h s t; exact (bv_term_small_rw_301_iff n s t).mpr (h s t)
  rw [hpoint]
  rw [forall_bitvec_toNat_iff (n := n) (fun a d => ShiftBalanced n a (a / 2 ^ ((a * a) % 2 ^ n)))]
  constructor
  · intro h r hr a ha he
    have hc := h a ha 0 (Nat.two_pow_pos n)
    simpa only [he] using hc
  · intro h a ha d hd
    by_cases hr : (a * a) % 2 ^ n < n
    · exact h _ hr a ha rfl
    · have hp : 2 ^ n ≤ 2 ^ ((a * a) % 2 ^ n) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le ha hp)]
      exact shiftBalanced_zero n a

end BV.QF_BV.Unsat
