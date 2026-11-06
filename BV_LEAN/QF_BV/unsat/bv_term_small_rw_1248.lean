/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: BV/QF_BV/unsat/bv-term-small-rw_1248.smt2
Original status: unknown; proved UNSAT.
License: CC BY 4.0
-/
import BV_LEAN.QF_BV.UnsatSupport

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat
open SMT.BitVec
open Learned.BitVec

theorem bv_term_small_rw_1248 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvmul s s) (bvshl s s)) = (bvmul s (bvlshr s (bvshl s s))) := by
  intro n s t
  exact square_right_shift_by_left_shift s s

end BV.QF_BV.Unsat
