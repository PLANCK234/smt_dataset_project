/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_248.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Arithmetic

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvadd_bvnot_bvor (x y : BitVec n) :
    bvadd x (bvnot (bvor x y)) = bvor x (bvnot y) := by
  rw [bvnot_bvor, bvand_comm, bvadd_bvand_bvnot]

theorem bv_term_small_rw_248 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvadd s (bvnot (bvor s t))) = (bvor s (bvnot t)) := by
  intro n s t
  exact bvadd_bvnot_bvor s t

end BV.QF_BV.Unsat
