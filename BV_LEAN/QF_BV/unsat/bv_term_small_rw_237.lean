/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_237.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvor_bvnot_bvshl_self (x y : BitVec n) :
    bvor x (bvnot (bvshl y x)) = bvnot (bvshl y x) :=
  bvor_bvnot_of_bvand_eq_zero x _ (bvand_bvshl_self x y)

theorem bv_term_small_rw_237 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor s (bvnot (bvshl s s))) = (bvnot (bvshl s s)) := by
  intro n s t
  simp only [bvor_bvnot_bvshl_self]

end BV.QF_BV.Unsat
