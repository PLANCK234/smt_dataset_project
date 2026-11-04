/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_338.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Arithmetic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvadd_bvor_bvnot (x y : BitVec n) :
    bvadd x (bvor y (bvnot x)) = bvnot (bvneg (bvand x y)) := by
  have hx := bvadd_bvnot x
  have hp := bvadd_bvand_bvnot (bvnot x) y
  rw [bvnot_bvnot, bvand_comm] at hp
  rw [bvor_comm y, ← hp, ← bvadd_assoc, hx, bvadd_comm, bvadd_bvnot_zero]

theorem bv_term_small_rw_338 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd s (bvor t (bvnot s))) = (bvnot (bvneg (bvand s t))) := by
  intro n s t
  simp only [bvadd_bvor_bvnot]

end BV.QF_BV.Unsat
