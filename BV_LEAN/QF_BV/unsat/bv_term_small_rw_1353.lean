/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1353.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvlshr_bvlshr_bvnot (x y : BitVec n) :
    bvlshr (bvlshr x y) (bvnot y) = literal n 0 := by
  rcases large_or_bvnot_large y with h | h
  · rw [bvlshr_large x y h]; simp [bvlshr, literal]
  · exact bvlshr_large _ _ h

theorem bv_term_small_rw_1353 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvlshr s t) (bvnot t)) = (literal n 0) := by
  intro n s t
  simp only [bvlshr_bvlshr_bvnot]

end BV.QF_BV.Unsat
