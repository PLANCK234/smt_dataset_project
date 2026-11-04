/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_771.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvand_bvmul_bvshl_self (x y z : BitVec n) :
    bvand x (bvmul y (bvshl z x)) = literal n 0 := by
  rw [← bvshl_bvmul, bvand_bvshl_self]

theorem bv_term_small_rw_771 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvand s (bvmul (bvshl t s) t)) = (literal n 0) := by
  intro n s t
  simp only [bvmul_comm, bvand_bvmul_bvshl_self]

end BV.QF_BV.Unsat
