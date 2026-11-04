/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1276.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Bitwise

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvadd_bvadd_bvnot (x y : BitVec n) :
    bvadd (bvadd x y) (bvnot y) = bvnot (bvneg x) := by
  rw [bvadd_assoc, bvadd_bvnot, bvadd_bvnot_zero]

theorem bv_term_small_rw_1276 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd (bvadd s t) (bvnot t)) = (bvnot (bvneg s)) := by
  intro n s t
  exact bvadd_bvadd_bvnot s t

end BV.QF_BV.Unsat
