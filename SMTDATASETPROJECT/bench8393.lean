import Mathlib.Data.Num.Bitwise
import Mathlib.Data.PNat.Basic
import Reap

/--
SMT:
(assert (and true (= T1_125521 (_ bv115 8)) (not (= T1_125521 (_ bv0 8)))))
-/
def φ (T1_125521 : BitVec 8) : Prop :=
  True ∧ (T1_125521 = BitVec.ofNat 8 115) ∧ (T1_125521 ≠ BitVec.ofNat 8 0)

-- Corresponds to `:status sat`
theorem bench8393 : ∃ T1_125521 : BitVec 8, φ T1_125521 := by
  refine ⟨BitVec.ofNat 8 115, ?_⟩
  constructor
  · trivial
  constructor
  · rfl
  · -- 115 ≠ 0 as 8-bit bitvectors
    decide

section

variable (n : ℕ) (npos : 0 < n)

theorem bench8393' {npos : 0 < n} : ∃ a : BitVec n, True ∧ (a = BitVec.ofNat n 115) ∧
  (a ≠ BitVec.ofNat n 0) := by
  refine ⟨BitVec.ofNat n 115, ?_⟩
  constructor
  · trivial
  constructor
  · rfl
  intro h
  -- turn BitVec equality into Nat equality via `toNat`
  have hNat :
      (BitVec.toNat (115#n)) = (BitVec.toNat (0#n)) := by
    simpa using congrArg BitVec.toNat h
  -- `toNat (k#w)` is `k % 2^w`, so this becomes a modular equation
  have hmod : 115 % 2^n = 0 := by
    simpa [BitVec.toNat_ofNat] using hNat
  -- from `a % m = 0` we get `m ∣ a`
  have hdiv : 2^n ∣ 115 :=
    Nat.dvd_of_mod_eq_zero hmod
  -- since n : ℕ+ , we have (↑n : Nat) > 0, so it's a successor
  obtain ⟨m⟩ : ∃ m, n = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt npos)
  -- 2 divides 2^(m+1) = 2^m * 2
  have h2pow : 2 ∣ 2^(m.succ) := by
    -- goal: 2 ∣ 2^m * 2
    exact Dvd.intro_left (Nat.pow 2 m) rfl
  -- thus 2 ∣ 115, contradiction (since 115 is odd)
  have h2 : 2 ∣ 115 := by exact Nat.dvd_of_pow_dvd npos hdiv
  have hnot : ¬ 2 ∣ 115 := by decide
  exact hnot h2

def φ' (T1_125521 : BitVec n) : Prop :=
  True ∧ (T1_125521 = BitVec.ofNat n 115) ∧ (T1_125521 ≠ BitVec.ofNat n 0)

theorem bench8393'' {npos : 0 < n} : ∃ T1_125521 : BitVec n, φ' n T1_125521 := by
  refine ⟨BitVec.ofNat n 115, ?_⟩
  constructor
  · trivial
  constructor
  · rfl
  intro h
  -- turn BitVec equality into Nat equality via `toNat`
  have hNat :
      (BitVec.toNat (115#n)) = (BitVec.toNat (0#n)) := by
    simpa using congrArg BitVec.toNat h
  -- `toNat (k#w)` is `k % 2^w`, so this becomes a modular equation
  have hmod : 115 % 2^n = 0 := by
    simpa [BitVec.toNat_ofNat] using hNat
  -- from `a % m = 0` we get `m ∣ a`
  have hdiv : 2^n ∣ 115 :=
    Nat.dvd_of_mod_eq_zero hmod
  -- since n : ℕ+ , we have (↑n : Nat) > 0, so it's a successor
  obtain ⟨m⟩ : ∃ m, n = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt npos)
  -- 2 divides 2^(m+1) = 2^m * 2
  have h2pow : 2 ∣ 2^(m.succ) := by
    -- goal: 2 ∣ 2^m * 2
    exact Dvd.intro_left (Nat.pow 2 m) rfl
  -- thus 2 ∣ 115, contradiction (since 115 is odd)
  have h2 : 2 ∣ 115 := by exact Nat.dvd_of_pow_dvd npos hdiv
  have hnot : ¬ 2 ∣ 115 := by decide
  exact hnot h2
