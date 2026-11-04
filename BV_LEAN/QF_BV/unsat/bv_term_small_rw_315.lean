/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_315.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvand_bvshl_bvor_left (x y z : BitVec n) :
    bvand x (bvshl y (bvor x z)) = literal n 0 := by
  apply bvand_bvshl_eq_zero_of_lt
  exact Nat.lt_of_le_of_lt SMT.Nat.left_le_or Nat.lt_two_pow_self

theorem bv_term_small_rw_315 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand s (bvshl s (bvor s t))) = (literal n 0) := by
  intro n s t
  simp only [bvand_bvshl_bvor_left]

end BV.QF_BV.Unsat
