/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1362.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvmul_bvlshr_swap (x y : BitVec n) :
    bvmul (bvlshr x y) (bvlshr y x) = literal n 0 := by
  rcases bvlshr_eq_zero_or x y with h | h <;> rw [h] <;> simp [bvmul, literal]

theorem bv_term_small_rw_1362 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvmul (bvlshr s t) (bvlshr t s)) = (literal n 0) := by
  intro n s t
  simp only [bvmul_bvlshr_swap]

end BV.QF_BV.Unsat
