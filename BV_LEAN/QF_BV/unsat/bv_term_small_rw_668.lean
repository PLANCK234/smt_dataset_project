/-
Source: SMT-LIB Benchmark Library
Benchmark family: 20190311-bv-term-small-rw-Noetzli
Original file: bv-term-small-rw_668.smt2
License: CC BY 4.0
-/
import LEMMAS_learned.BitVec.Shift.Self

set_option linter.unusedVariables false

namespace BV.QF_BV.Unsat

open SMT.BitVec
open Learned.BitVec

/-
Proof sketch:
Let b = (~t) << t. If b = 0 both counts are zero and the result is s.
Otherwise let a = t.toNat. If n ≤ 2^a, divisibility gives b.toNat ≥ 2^a ≥ n.
If 2^a < n, then (a+1)*2^a ≤ 2^(n-1) and b.toNat = 2^n-(a+1)*2^a,
which is at least half the range, hence ≥ n. So both shifts are zero.
-/

theorem bv_term_small_rw_668 :
    ∀ (n : Nat) (s t : BitVec n),
      (bvshl s (bvshl (bvnot t) t)) = (bvlshr s (bvshl (bvnot t) t)) := by
  intro n s t
  by_cases hb : bvshl (bvnot t) t = literal n 0
  · rw [hb, bvshl_zero, bvlshr_zero]
  · have h := width_le_toNat_bvshl_bvnot_self t hb
    rw [bvshl_large _ _ h, bvlshr_large _ _ h]

end BV.QF_BV.Unsat
