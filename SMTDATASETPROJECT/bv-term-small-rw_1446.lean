-- a case from `small_bv_problems/bv-term-small-rw_1446.smt2`

open BitVec

variable {n : Nat}

def bv_lshr := λ (a b : BitVec n) => BitVec.ofNat n (a.toNat / (2 ^ b.toNat))
def bv_mul := λ (a b : BitVec n) => a * b

theorem nat_div_div_commutative (x y z : Nat) : x / y / z = x / z / y :=
  calc
    x / y / z = x / (y * z) := Nat.div_div_eq_div_mul _ _ _
    _         = x / (z * y) := by simp [Nat.mul_comm]
    _         = x / z / y   := by
                  -- rewrite the other side the same way, then flip equality
                  simp [Nat.div_div_eq_div_mul]

theorem s_less_than_m (s m : Nat) (H: s<m) : s%m = s :=
  Nat.mod_eq_of_lt H

theorem s_less_than_m_div_d (s m d : Nat) (H:s<m) : s/d < m := by
  -- use s/d ≤ s and then s < m
  have h1 : s / d ≤ s := by simp [Nat.div_le_self]
  exact Nat.lt_of_le_of_lt h1 H

 -- x >> y >> z == x >> z >> y
theorem bv_lshr_comm (x y z : BitVec n) :
  bv_lshr (bv_lshr x y) z = bv_lshr (bv_lshr x z) y := by
  -- unfold the definition of bv_lshr
  unfold bv_lshr
  -- reduce equality on BitVecs to equality on Nat
  apply BitVec.eq_of_toNat_eq
  -- toNat (ofNat k) = k % 2^n
  simp [BitVec.toNat_ofNat]

  -- Now the goal is:
  --   ((x.toNat / 2 ^ y.toNat) % 2 ^ n / 2 ^ z.toNat) % 2 ^ n
  -- = ((x.toNat / 2 ^ z.toNat) % 2 ^ n / 2 ^ y.toNat) % 2 ^ n

  -- bound x.toNat, so that we can later remove `% 2^n` using s_less_than_m
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

 -- (assert (not (= (bvlshr (bvlshr s (bvmul s s)) t) (bvlshr (bvlshr s t) (bvmul s s))))) is UNSAT
 -- s >> (s*s) >> t == s >> t >> (s*s)
theorem bv_lshr_comm_example (s t : BitVec n) :
    bv_lshr (bv_lshr s (bv_mul s s)) t =
    bv_lshr (bv_lshr s t) (bv_mul s s) := by
    exact bv_lshr_comm s (bv_mul s s) t
