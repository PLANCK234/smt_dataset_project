/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_320.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_self_bvadd_bvlshr (x y : BitVec n) : bvlshr x (bvadd x (bvlshr y x)) = literal n 0 := by
  apply bvlshr_eq_zero_of_le
  rw [toNat_bvadd_bvlshr]
  omega

theorem bv_term_small_rw_320 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvadd s (bvlshr t s))) = (literal n 0) := by
  intro n s t
  simp only [bvlshr_self_bvadd_bvlshr]

end BV.QF_BV.Unsat
