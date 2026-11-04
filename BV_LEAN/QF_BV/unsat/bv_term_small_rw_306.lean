/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_306.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Basic
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvor_bvmul_bvshl_self (x y z : BitVec n) :
    bvor x (bvmul y (bvshl z x)) = bvadd x (bvmul y (bvshl z x)) := by
  rw [← bvshl_bvmul, bvor_bvshl_self]

theorem bv_term_small_rw_306 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvor s (bvmul s (bvshl s s))) = (bvadd s (bvmul s (bvshl s s))) := by
  intro n s t
  simp only [bvor_bvmul_bvshl_self]

end BV.QF_BV.Unsat
