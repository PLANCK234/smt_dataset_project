/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_236.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec
open _root_.BitVec (toNat)

private theorem bvand_bvnot_bvshl_self (x y : BitVec n) :
    bvand x (bvnot (bvshl y x)) = x :=
  bvand_bvnot_of_bvand_eq_zero x _ (bvand_bvshl_self x y)

private theorem bvlshr_bvnot_bvshl_self (x y : BitVec n) :
    bvlshr x (bvnot (bvshl y x)) = literal n 0 := by
  apply bvlshr_eq_zero_of_le
  have h := congrArg toNat (bvand_bvnot_bvshl_self x y)
  rw [toNat_bvand] at h
  rw [← h]
  exact SMT.Nat.and_le_right

theorem bv_term_small_rw_236 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvnot (bvshl s s))) = (literal n 0) := by
  intro n s t
  simp only [bvlshr_bvnot_bvshl_self]

end BV.QF_BV.Unsat
