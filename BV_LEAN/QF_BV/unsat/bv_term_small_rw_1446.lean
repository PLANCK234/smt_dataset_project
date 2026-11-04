/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_1446.smt2
License: CC BY 4.0
-/
import SMT.BitVec.Lemmas

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 200000

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec

theorem bv_term_small_rw_1446 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvlshr (bvlshr s (bvmul s s)) t) = (bvlshr (bvlshr s t) (bvmul s s)) := by
  intro n s t
  first
  | (simp [bvadd, bvmul, bvneg, bvnot, bvand, bvor, bvlshr, bvshl_eq_shiftLeft, literal]; grind)
  | (ext i h; simp [bvadd, bvmul, bvneg, bvnot, bvand, bvor, bvlshr, bvshl_eq_shiftLeft, literal]; grind)

end BV.QF_BV.Unsat
