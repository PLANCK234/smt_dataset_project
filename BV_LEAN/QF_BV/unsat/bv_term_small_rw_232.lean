/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_232.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (neg_eq_zero_iff)

private theorem bvlshr_bvneg_bvshl_self (x y : BitVec n) :
    bvlshr x (bvneg (bvshl y x)) = bvlshr x (bvshl y x) := by
  rw [← bvshl_bvneg, bvlshr_bvshl_self_eq_ite, bvlshr_bvshl_self_eq_ite,
    bvshl_bvneg]
  simp only [bvneg, literal, neg_eq_zero_iff]

theorem bv_term_small_rw_232 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvneg (bvshl s s))) = (bvlshr s (bvshl s s)) := by
  intro n s t
  simp only [bvlshr_bvneg_bvshl_self]

end BV.QF_BV.Unsat
