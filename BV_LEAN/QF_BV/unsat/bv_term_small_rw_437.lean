/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_437.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Bitwise
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvand_bvor_absorb_right (x y : BitVec n) : bvand x (bvor y x) = x := by
  rw [bvor_comm, bvand_bvor_absorb]

theorem bv_term_small_rw_437 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvand t (bvor s t))) = (bvshl s t) := by
  intro n s t
  simp only [bvand_bvor_absorb_right]

end BV.QF_BV.Unsat
