/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1358.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1358 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvlshr s t) (bvor s t)) = (literal n 0) := by
  intro n s t
  apply bvlshr_eq_zero_of_le
  rw [toNat_bvlshr, toNat_bvor]
  exact Nat.le_trans (Nat.div_le_self _ _) SMT.Nat.left_le_or

end BV.QF_BV.Unsat
