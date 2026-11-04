/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1132.smt2
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

theorem bv_term_small_rw_1132 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor t (bvlshr (bvlshr t s) t)) = (bvadd (bvlshr s s) t) := by
  intro n s t
  simp only [bvlshr_bvlshr_self, bvor_zero, bvlshr_self, bvadd_comm,
      bvadd_zero]

end BV.QF_BV.Unsat
