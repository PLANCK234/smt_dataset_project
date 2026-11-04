/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1228.smt2
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

private theorem bvadd_bvnot_bvor_cancel (x y : BitVec n) :
    bvadd (bvnot x) (bvor x y) = bvadd y (bvnot (bvand x y)) := by
  rw [← bvadd_bvand_bvnot x y, ← bvadd_assoc, bvadd_comm (bvnot x) x,
    bvadd_bvnot, bvadd_comm (bvnot (literal n 0)), bvadd_bvnot_zero,
    bvnot_bvand, bvadd_bvor_bvnot]

theorem bv_term_small_rw_1228 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd (bvnot s) (bvor s t)) = (bvadd t (bvnot (bvand s t))) := by
  intro n s t
  simp only [bvadd_bvnot_bvor_cancel, bvnot_bvand, bvadd_bvor_bvnot]

end BV.QF_BV.Unsat
