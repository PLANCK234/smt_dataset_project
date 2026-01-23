-- `small_bv_problems/bv-term-small-rw_1446.smt2`
import Mathlib.Data.Num.Bitwise
import Reap

open BitVec

variable {n : Nat}

def bv_lshr := fun (a b : BitVec n) => BitVec.ofNat n (a.toNat / (2 ^ b.toNat))
def bv_mul := fun (a b : BitVec n) => a * b

theorem nat_div_div_commutative (x y z : Nat) : x / y / z = x / z / y := by
  simp only [Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem s_less_than_m (s m : Nat) (H : s < m) : s % m = s :=
  Nat.mod_eq_of_lt H

theorem s_less_than_m_div_d (s m d : Nat) (H : s < m) : s/d < m := by
  -- use s/d ≤ s and then s < m
  have h1 : s / d ≤ s := by simp [Nat.div_le_self]
  exact Nat.lt_of_le_of_lt h1 H

/- For any natural number $n$, the function $\text{toNat} :
  \text{BitVec}\, n \to \mathbb{N}$ that converts a bitvector of length $n$ to its natural number
   representation is injective. That is, for any bitvectors $x, y : \text{BitVec}\, n$,
   if $\text{toNat}(x) = \text{toNat}(y)$, then $x = y$. -/
theorem toNat_injective {n : Nat} : Function.Injective (BitVec.toNat : BitVec n → _)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

 -- x >> y >> z == x >> z >> y
theorem bv_lshr_comm (x y z : BitVec n) :
  bv_lshr (bv_lshr x y) z = bv_lshr (bv_lshr x z) y := by
  -- Reduce equality of bitvectors to equality of their `toNat` values
  apply toNat_injective
-- Unfold `bv_lshr` and compute `toNat` of `ofNat`; this becomes an arithmetic goal
  simp only [bv_lshr, BitVec.toNat_ofNat]
  have h0 : x.toNat < 2^n := by simpa using x.toFin.isLt
  -- bounds after one division
  have h1y : x.toNat / 2 ^ y.toNat < 2^n :=
    s_less_than_m_div_d x.toNat (2^n) (2 ^ y.toNat) h0
  have h1z : x.toNat / 2 ^ z.toNat < 2^n :=
    s_less_than_m_div_d x.toNat (2^n) (2 ^ z.toNat) h0
  -- remove the inner `% 2^n` on both sides
  have hy_inner :
      x.toNat / 2 ^ y.toNat % 2 ^ n
    = x.toNat / 2 ^ y.toNat :=
    s_less_than_m _ _ h1y
  have hz_inner :
      x.toNat / 2 ^ z.toNat % 2 ^ n
    = x.toNat / 2 ^ z.toNat :=
    s_less_than_m _ _ h1z
  -- rewrite the goal using these equalities
  -- goal becomes:
  --   (x.toNat / 2 ^ y.toNat / 2 ^ z.toNat) % 2 ^ n
  -- = (x.toNat / 2 ^ z.toNat / 2 ^ y.toNat) % 2 ^ n
  have hcomm_mod :
      (x.toNat / 2 ^ y.toNat / 2 ^ z.toNat) % 2 ^ n
    = (x.toNat / 2 ^ z.toNat / 2 ^ y.toNat) % 2 ^ n :=
    -- apply nat_div_div_commutative and then reduce modulo 2^n
    congrArg (fun t => t % 2 ^ n)
      (nat_div_div_commutative x.toNat (2 ^ y.toNat) (2 ^ z.toNat))
  simpa [hy_inner, hz_inner] using hcomm_mod
theorem bv_term_small_rw_1446 (s t : BitVec n) :
    bv_lshr (bv_lshr s (bv_mul s s)) t =
    bv_lshr (bv_lshr s t) (bv_mul s s) := by
  rw [bv_lshr_comm]
