/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_428.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Bitwise
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

private theorem bvor_bvand_absorb_right (x y : BitVec n) : bvor x (bvand y x) = x := by
  rw [bvand_comm, bvor_bvand_absorb]

theorem bv_term_small_rw_428 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr s (bvor t (bvand s t))) = (bvlshr s t) := by
  intro n s t
  simp only [bvor_bvand_absorb_right]

end BV.QF_BV.Unsat
