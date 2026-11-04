/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1361.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Bounds
import SMT.BitVec.Lemmas

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1361 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvlshr s t) (bvshl s t)) = (bvlshr s (bvadd t (bvshl s t))) := by
  intro n s t
  simp only [bvand_bvshl_self, bvlshr_bvlshr_of_bvand_eq_zero]

end BV.QF_BV.Unsat
