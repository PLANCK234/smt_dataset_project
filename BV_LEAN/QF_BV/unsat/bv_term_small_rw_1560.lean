/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1560.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvlshr_self (x y : BitVec n) :
    bvlshr (bvlshr x y) x = literal n 0 := by
  apply bvlshr_eq_zero_of_le
  rw [toNat_bvlshr]
  exact Nat.div_le_self _ _

theorem bv_term_small_rw_1560 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvand (bvlshr s t) t) s) = (literal n 0) := by
  intro n s t
  simp only [bvand_comm, bvlshr_bvand, bvlshr_bvlshr_self,
      bvand_zero]

end BV.QF_BV.Unsat
