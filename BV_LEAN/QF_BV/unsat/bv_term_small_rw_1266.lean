/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1266.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvand_bvlshr_bvshl (x y z : BitVec n) :
    bvand (bvlshr x y) (bvshl z x) = literal n 0 := by
  apply bvand_bvshl_eq_zero_of_lt
  rw [toNat_bvlshr]
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) Nat.lt_two_pow_self

theorem bv_term_small_rw_1266 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor (bvshl s s) (bvlshr s t)) = (bvadd (bvshl s s) (bvlshr s t)) := by
  intro n s t
  simp only [bvand_comm, bvand_bvlshr_bvshl, bvor_eq_bvadd_of_bvand_eq_zero,
      bvadd_comm]

end BV.QF_BV.Unsat
