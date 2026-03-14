/-
Copyright (c) 2026 Tang Guofu
Released under MIT license.
Authors: Tang Guofu
-/

import Std
import Init.Data.BitVec.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Num.Bitwise
import Mathlib.Data.Bool.Basic

namespace SMT

/-
(concat (_ BitVec i) (_ BitVec j) (_ BitVec m))
  - concatenation of bitvectors of size i and j to get a new bitvector of
    size m, where m = i + j
-/
@[expose, simp]
def concat {i j : Nat} (x : BitVec i) (y : BitVec j) : BitVec (i + j) := BitVec.append x y

/-
((_ extract i j) (_ BitVec m) (_ BitVec n))
  - extraction of bits i down to j from a bitvector of size m to yield a
    new bitvector of size n, where n = i - j + 1
-/
@[expose, simp]
def extract {m : Nat} (i j : Nat) (x : BitVec m) : BitVec (i - j + 1) := BitVec.extractLsb i j x

@[expose, simp]
def bvconst (x : Nat) (n : Nat) : BitVec n :=
  BitVec.ofNat n x

@[expose, simp] def bvzero {m : Nat} : BitVec m := BitVec.ofNat m 0

@[expose, simp]
def msb {m : Nat} (s : BitVec m) : BitVec 1 :=
   BitVec.ofNat 1 (s.toNat / 2^(m - 1))

@[expose, simp] def msb0 {m : Nat} (s : BitVec m) : Bool := msb (m := m) s = BitVec.ofNat 1 0
@[expose, simp] def msb1 {m : Nat} (s : BitVec m) : Bool := msb (m := m) s = BitVec.ofNat 1 1

@[expose, simp] def bvnot {m : Nat} (x : BitVec m) : BitVec m := BitVec.not x
@[expose, simp] def bvand {m : Nat} (x y : BitVec m) : BitVec m := BitVec.and x y
@[expose, simp] def bvor  {m : Nat} (x y : BitVec m) : BitVec m := BitVec.or x y
@[expose, simp] def bvneg {m : Nat} (x : BitVec m) : BitVec m := BitVec.neg x
@[expose, simp] def bvabs {m : Nat} (x : BitVec m) : BitVec m :=
  if msb x = (0 : BitVec 1) then x else bvneg x
@[expose, simp] def bvadd {m : Nat} (x y : BitVec m) : BitVec m := x + y
@[expose, simp] def bvmul {m : Nat} (x y : BitVec m) : BitVec m := BitVec.mul x y
@[expose, simp] def bvudiv {m : Nat} (x y : BitVec m) : BitVec m := BitVec.smtUDiv x y
@[expose, simp] def bvurem {m : Nat} (x y : BitVec m) : BitVec m := BitVec.umod x y
@[expose, simp] def bvshl {m : Nat} (x y : BitVec m) : BitVec m := x <<< y
@[expose, simp] def bvlshr {m : Nat} (x y : BitVec m) : BitVec m := x >>> y

@[expose, simp] def bvult {m : Nat} (x y : BitVec m) : Bool := BitVec.ult x y
@[expose, simp] def bvnego {m : Nat} (x : BitVec m) : Bool := BitVec.negOverflow x
@[expose, simp] def bvuaddo {m : Nat} (x y : BitVec m) : Bool := BitVec.uaddOverflow x y
@[expose, simp] def bvsaddo {m : Nat} (x y : BitVec m) : Bool := BitVec.saddOverflow x y
@[expose, simp] def bvumulo {m : Nat} (x y : BitVec m) : Bool := BitVec.umulOverflow x y
@[expose, simp] def bvsmulo {m : Nat} (x y : BitVec m) : Bool := BitVec.smulOverflow x y

@[expose, simp] def ubv_to_int {m : Nat} (x : BitVec m) : Int := x.toNat
@[expose, simp] def sbv_to_int {m : Nat} (x : BitVec m) : Int := x.toInt
@[expose, simp] def int_to_bv (m : Nat) (x : Int) : BitVec m := BitVec.ofInt m x
@[expose, simp] def bvnand {m : Nat} (x y : BitVec m) : BitVec m := ~~~(x &&& y)
@[expose, simp] def bvnand' {m : Nat} (x y : BitVec m) : BitVec m := bvnot (bvand x y)
@[expose, simp] def bvnor {m : Nat} (x y : BitVec m) : BitVec m := ~~~(x ||| y)
@[expose, simp] def bvnor' {m : Nat} (x y : BitVec m) : BitVec m := bvnot (bvor x y)

/-
bvxor [s1 s2 ... sn] = (bvxor' (bvxor' s1 s2) ... sn)
-/

@[expose, simp]
def bvxor {m : Nat} : List (BitVec m) → BitVec m
| []      => 0
| x :: xs => xs.foldl (fun acc y => acc ^^^ y) x
@[expose, simp] def bvxor' {m : Nat} (x y : BitVec m) : BitVec m := x ^^^ y
@[expose, simp] def bvxor'' {m : Nat} (x y : BitVec m) : BitVec m := bvor (bvand x (bvnot y)) (bvand (bvnot x) y)
@[expose, simp] def bvxnor {m : Nat} (x y : BitVec m) : BitVec m := ~~~(x ^^^ y)
@[expose, simp] def bvxnor' {m : Nat} (x y : BitVec m) : BitVec m := bvor (bvand x y) (bvand (bvnot x) (bvnot y))
@[expose, simp] def bvcomp {m : Nat} (x y : BitVec m) : BitVec 1 := if x = y then BitVec.ofNat 1 1 else BitVec.ofNat 1 0

@[expose, simp]
def bvcomp' : {m : Nat} → BitVec m → BitVec m → BitVec 1
  | 0, _, _ => 1
  | 1, s, t => bvxnor s t
  | m+2, s, t =>
      let hi_s : BitVec 1 := BitVec.ofNat 1 (s.toNat / 2^(m + 1))
      let hi_t : BitVec 1 := BitVec.ofNat 1 (t.toNat / 2^(m + 1))
      let lo_s : BitVec (m+1) := extract m 0 s
      let lo_t : BitVec (m+1) := extract m 0 t
      bvand (bvxnor hi_s hi_t) (bvcomp lo_s lo_t)

@[expose, simp] def bvsub {m : Nat} (x y : BitVec m) : BitVec m := x - y
@[expose, simp] def bvsub' {m : Nat} (x y : BitVec m) : BitVec m := bvadd x (bvneg y)
@[expose, simp] def bvsdiv {m : Nat} (x y : BitVec m) : BitVec m := BitVec.smtSDiv x y

@[expose, simp]
def bvsdiv' {m : Nat} (s t : BitVec m) : BitVec m :=
  let msb_s : BitVec 1 := msb s
  let msb_t : BitVec 1 := msb t
  if msb_s = (0 : BitVec 1) ∧ msb_t = (0 : BitVec 1) then
    bvudiv s t
  else if msb_s = (1 : BitVec 1) ∧ msb_t = (0 : BitVec 1) then
    bvneg (bvudiv (bvneg s) t)
  else if msb_s = (0 : BitVec 1) ∧ msb_t = (1 : BitVec 1) then
    bvneg (bvudiv s (bvneg t))
  else
    bvudiv (bvneg s) (bvneg t)

@[expose, simp] def bvsrem {m : Nat} (x y : BitVec m) : BitVec m := BitVec.srem x y

@[expose, simp]
def bvsrem' {m : Nat} (s t : BitVec m) : BitVec m :=
  let msb_s := msb s
  let msb_t := msb t
  if msb_s = (0 : BitVec 1) ∧ msb_t = (0 : BitVec 1) then
    bvurem s t
  else if msb_s = (1 : BitVec 1) ∧ msb_t = (0 : BitVec 1) then
    bvneg (bvurem (bvneg s) t)
  else if msb_s = (0 : BitVec 1) ∧ msb_t = (1 : BitVec 1) then
    bvurem s (bvneg t)
  else
    bvneg (bvurem (bvneg s) (bvneg t))

@[expose, simp] def bvsmod {m : Nat} (x y : BitVec m) : BitVec m := BitVec.smod x y

@[expose, simp]
def bvsmod' {m : Nat} (s t : BitVec m) : BitVec m :=
  let msb_s := msb s
  let msb_t := msb t
  let abs_s := bvabs s
  let abs_t := bvabs t
  let u := bvurem abs_s abs_t
  if u = (0 : BitVec m) then
    u
  else if msb_s = (0 : BitVec 1) ∧ msb_t = (0 : BitVec 1) then
    u
  else if msb_s = (1 : BitVec 1) ∧ msb_t = (0 : BitVec 1) then
    bvadd (bvneg u) t
  else if msb_s = (0 : BitVec 1) ∧ msb_t = (1 : BitVec 1) then
    bvadd u t
  else
    bvneg u

@[expose, simp] def bvashr {m : Nat} (x y : BitVec m) : BitVec m := BitVec.sshiftRight x y.toNat
@[expose, simp] def bvashr' {m : Nat} (x y : BitVec m) : BitVec m :=
  if msb x = bvconst 0 1
  then bvlshr x y
  else bvnot (bvlshr (bvnot x) y)

@[expose, simp] def bvusubo {m : Nat} (x y : BitVec m) : Bool := BitVec.usubOverflow x y
@[expose, simp] def bvusubo' {m : Nat} (x y : BitVec m) : Bool := bvult x y

@[expose, simp] def bvssubo {m : Nat} (x y : BitVec m) : Bool := BitVec.ssubOverflow x y

@[expose, simp] def bvsdivo {m : Nat} (x y : BitVec m) : Bool := BitVec.sdivOverflow x y


@[expose, simp]
def re_peat {m : Nat} (i : Nat) (x : BitVec m) : BitVec (m * i) :=
  match i with
  | 0 => 1
  | 1 => by
    simpa using x
  | n + 2 =>
      have : m * (n + 1) + m = m * (n + 2) := by exact Eq.symm (Nat.mul_succ m (n + 1))
      cast
        (by rw [this])
        (concat (re_peat (n + 1) x) x)

@[expose, simp] def zero_extend {m : Nat} (i : Nat) (x : BitVec m) : BitVec (m + i) :=
  BitVec.setWidth (m + i) x
@[expose, simp] def zero_extend' {m : Nat} (i : Nat) (x : BitVec m) : BitVec (i + m) :=
  concat (BitVec.ofNat i 0) x

@[expose, simp] def sign_extend {m : Nat} (i : Nat) (x : BitVec m) : BitVec (m + i) :=
  BitVec.signExtend (m + i) x
@[expose, simp] def sign_extend' {m : Nat} (i : Nat) (x : BitVec m) : BitVec (m + i) :=
  .ofInt (m + i) x.toInt

theorem zero_extend_eq_zero_extend' {m : Nat} (i : Nat) (x : BitVec m) :
  zero_extend i x = (zero_extend' i x).cast (by exact Nat.add_comm i m) := by
  simp only [zero_extend, zero_extend', concat, BitVec.append_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_cast, BitVec.toNat_append, BitVec.toNat_ofNat,
    Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  apply Nat.mod_eq_of_lt
  have hx : x.toNat < 2 ^ m := by
    exact x.isLt
  have hpow : 2 ^ m ≤ 2 ^ (m + i) := by
    apply Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    simp only [Nat.le_add_right]
  exact lt_of_lt_of_le hx hpow

theorem sign_extend_eq_sign_extend' {m : Nat} (i : Nat) (x : BitVec m) :
  sign_extend i x = sign_extend' i x := by
  simp only [sign_extend, sign_extend']
  unfold BitVec.signExtend
  rfl

@[expose, simp] def rotate_left {m : Nat} (i : Nat) (x : BitVec m) : BitVec m := BitVec.rotateLeft x i
@[expose, simp]
def rotate_left' {m : Nat} (i : Nat) (x : BitVec m) : BitVec m :=
  if h : m = 0 then
    x
  else
    let k := i % m
    if hk : k = 0 then
      x
    else
        have hm : 0 < m := by exact Nat.zero_lt_of_ne_zero h
        have hmk : m > k := by
          apply Nat.mod_lt i hm
        have hmk' : k ≤ m := by
          exact Nat.le_of_succ_le hmk
        have : m - k + k = m := by
          exact Nat.sub_add_cancel hmk'
        cast
        (by simp only [this])
        (concat
          (BitVec.ofNat (m - k) x.toNat)
          (BitVec.ofNat k (x.toNat / 2^(m - k))))

@[expose, simp] def rotate_right {m : Nat} (i : Nat) (x : BitVec m) : BitVec m := BitVec.rotateRight x i

@[expose, simp]
def rotate_right' {m : Nat} (i : Nat) (x : BitVec m) : BitVec m :=
  if h : m = 0 then
    x
  else
    let k := i % m
    if hk : k = 0 then
      x
    else
        have hm : 0 < m := by exact Nat.zero_lt_of_ne_zero h
        have hmk : m > k := by
          apply Nat.mod_lt i hm
        have hmk' : k ≤ m := by
          exact Nat.le_of_succ_le hmk
        have : k + (m - k) = m := by
          exact Nat.add_sub_of_le hmk'
      cast
        (by simp only [this])
        (concat
          (BitVec.ofNat k (x.toNat % 2^k))
          (BitVec.ofNat (m - k) (x.toNat / 2^k)))

theorem rotate_left_eq_rotate_left' {m : Nat} (i : Nat) (x : BitVec m) :
  rotate_left i x = rotate_left' i x := by
  unfold rotate_left rotate_left' BitVec.rotateLeft BitVec.rotateLeftAux
  simp only [concat, BitVec.ofNat_toNat, BitVec.append_eq, dite_eq_ite]
  by_cases hm : m = 0
  · subst hm
    simp only [Nat.mod_zero, Nat.zero_le, BitVec.shiftLeft_eq_zero, Nat.sub_eq_zero_of_le,
      BitVec.ushiftRight_zero, BitVec.zero_or, ↓reduceDIte]
  have hm' : m ≠ 0 := hm
  by_cases hmod : i % m = 0
  have hshl : x <<< (i % m) = x := by simp only [hmod, BitVec.shiftLeft_zero]
  have hshr : x >>> (m - i % m) = 0 := by
    rw [hmod]
    simp only [Nat.sub_zero, BitVec.ofNat_eq_ofNat]
    apply BitVec.eq_of_toNat_eq
    have h : x.toNat < 2^m := by exact BitVec.isLt x
    sorry
  sorry
  sorry


theorem rotate_right_eq_rotate_right' {m : Nat} (i : Nat) (x : BitVec m) :
  rotate_right i x = rotate_right' i x := by
  sorry

@[expose, simp] def bvule {m : Nat} (x y : BitVec m) : Bool := BitVec.ule x y
@[expose, simp] def bvugt {m : Nat} (x y : BitVec m) : Bool := x.toNat > y.toNat
@[expose, simp] def bvuge {m : Nat} (x y : BitVec m) : Bool := x.toNat ≥ y.toNat

@[expose, simp] def bvslt {m : Nat} (x y : BitVec m) : Bool := BitVec.slt x y
@[expose, simp] def bvslt' {m : Nat} (s t : BitVec m) : Bool :=
  (msb s = bvconst 1 1 ∧
   msb t = bvconst 0 1)
  ∨
  (extract (m - 1) (m - 1) s =
   extract (m - 1) (m - 1) t ∧
   bvult s t)

@[expose, simp] def bvsle {m : Nat} (x y : BitVec m) : Bool := BitVec.sle x y
@[expose, simp] def bvsle' {m : Nat} (s t : BitVec m) : Bool :=
  (msb s = bvconst 1 1 ∧
   msb t = bvconst 0 1)
  ∨
  (extract (m - 1) (m - 1) s =
   extract (m - 1) (m - 1) t ∧
   bvule s t)

@[expose, simp] def bvsgt {m : Nat} (x y : BitVec m) : Bool := x.toInt > y.toInt
@[expose, simp] def bvsgt' {m : Nat} (x y : BitVec m) : Bool := bvslt y x
@[expose, simp] def bvsge {m : Nat} (x y : BitVec m) : Bool := x.toInt ≥ y.toInt
@[expose, simp] def bvsge' {m : Nat} (x y : BitVec m) : Bool := bvsle y x
@[expose, simp] def bvule' {m : Nat} (x y : BitVec m) : Bool := (bvult x y) ∨ (x = y)
@[expose, simp] def bvugt' {m : Nat} (x y : BitVec m) : Bool := bvult y x
@[expose, simp] def bvuge' {m : Nat} (x y : BitVec m) : Bool := (bvult y x) ∨ (x = y)

@[expose, simp] def bvssubo' {m : Nat} (x y : BitVec m) : Bool :=
  if (bvnego y) then
    (bvsge x (bvconst 0 m))
  else
    bvsaddo x (bvneg y)

@[expose, simp] def bvsdivo' {m : Nat} (x y : BitVec m) : Bool :=
  (bvnego x) ∧ (y = (bvnot (bvconst 0 m)))

/-
    For all terms s,t of sort (_ BitVec m), where 0 < m,

    (bvnand s t) abbreviates (bvnot (bvand s t))
    (bvnor s t) abbreviates (bvnot (bvor s t))
    (bvxor s t) abbreviates (bvor (bvand s (bvnot t)) (bvand (bvnot s) t))
    (bvxnor s t) abbreviates (bvor (bvand s t) (bvand (bvnot s) (bvnot t)))
    (bvcomp s t) abbreviates (bvxnor s t) if m = 1, and
       (bvand (bvxnor ((_ extract |m-1| |m-1|) s) ((_ extract |m-1| |m-1|) t))
              (bvcomp ((_ extract |m-2| 0) s) ((_ extract |m-2| 0) t))) otherwise.

    Additionally, bvxor is left associative, so:

    (bvxor s_1 s_2 ... s_n) abbreviates (bvxor (bvxor s_1 s_2 ...) s_n), and

    so in lean, we write bvxor [s_1, s_2, ..., s_n]
-/
theorem bvxor_eq_bvxor' {m : Nat} (s t : BitVec m) :
  bvxor [s, t] = bvxor' s t := by simp only [bvxor, List.foldl_cons, List.foldl_nil, bvxor']


theorem bvnand_eq_bvnand' {m : Nat} (s t : BitVec m) :
  bvnand s t = bvnand' s t := by simp only [bvnand, bvnand', bvnot, bvand, BitVec.and_eq,
    BitVec.not_eq]

theorem bvnor_eq_bvnor' {m : Nat} (s t : BitVec m) :
  bvnor s t = bvnor' s t := by simp only [bvnor, bvnor', bvnot, bvor, BitVec.or_eq, BitVec.not_eq]

theorem bvxor'_eq_bvxor'' {m : Nat} (s t : BitVec m) :
  bvxor' s t = bvxor'' s t := by
  unfold bvxor' bvxor''
  simp only [bvor, bvand, bvnot]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  cases hs : s.getLsbD i <;> cases ht : t.getLsbD i <;> simp [hs, ht]

theorem bvxnor_eq_bvxnor' {m : Nat} (s t : BitVec m) :
    bvxnor s t = bvxnor' s t := by
  unfold bvxnor bvxnor'
  simp only [bvor, bvand, bvnot]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  cases hs : s.getLsbD i <;> cases ht : t.getLsbD i <;> simp [hs, ht]

lemma bvcomp_eq_one_bit (s t : BitVec 1) :
    (if s = t then 1#1 else 0#1) = ~~~(s ^^^ t) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [Nat.lt_one_iff, BitVec.getLsbD_not, BitVec.getLsbD_xor]
  intro hi
  subst i
  simp only [Nat.lt_add_one, BitVec.getLsbD_eq_getElem, decide_true, Bool.true_and]
  cases s using BitVec.casesOn
  cases t using BitVec.casesOn
  bv_decide

lemma ite_and_to_bvand (P Q : Bool) [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1#1 : BitVec 1) else 0#1) =
      (if P then 1#1 else 0#1) &&& (if Q then 1#1 else 0#1) := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

lemma eq_iff_hi_lo_eq {k : Nat} (s t : BitVec (k + 2)) :
    s = t ↔
      BitVec.extractLsb (k + 1) (k + 1) s =
        BitVec.extractLsb (k + 1) (k + 1) t
      ∧
      BitVec.extractLsb k 0 s =
        BitVec.extractLsb k 0 t := by
  simp only [Nat.sub_zero]
  constructor
  · intro h
    subst h
    simp only [and_self]
  intro h
  rcases h with ⟨hhi, hlo⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i
  by_cases hi : i = k + 1
  · subst hi
    simp only [Nat.lt_add_one, BitVec.getLsbD_eq_getElem, forall_const]
    have h0 := congrArg (fun x => x[0]) hhi
    simpa using h0
  intro hlt
  have hik : i < k + 1 := by
    exact lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) hi
  have h := congrArg (fun x => x.getLsbD i) hlo
  simpa [(Nat.le_of_lt_succ hik)] using h

lemma eq_of_high_low_eq {k : Nat} {s t : BitVec (k + 2)}
    (hhi : BitVec.extractLsb (k + 1) (k + 1) s = BitVec.extractLsb (k + 1) (k + 1) t)
    (hlo : BitVec.extractLsb k 0 s = BitVec.extractLsb k 0 t) :
    s = t := by
  simp only [eq_iff_hi_lo_eq, Nat.sub_zero]
  exact And.symm ⟨hlo, hhi⟩

lemma cast_allOnes_trans (n m : Nat) (h : n = m) : BitVec.cast h (BitVec.allOnes n) = BitVec.allOnes m := by
  subst h
  exact BitVec.cast_eq (Eq.refl n) (BitVec.allOnes n)

lemma BitVec_cast_inj {m n : Nat} (h : m = n) {x y : BitVec m} :
    BitVec.cast h x = BitVec.cast h y -> x = y := by
  intro hxy
  cases h
  simpa using hxy

theorem bvcomp_eq_bvcomp' {m : Nat} (s t : BitVec m) :
    bvcomp s t = bvcomp' s t := by
  simp only [bvcomp, bvcomp', BitVec.ofNat_eq_ofNat, bvxnor, bvand, extract]
  cases m with
    | zero =>
      simp only [ite_eq_left_iff, BitVec.zero_eq_one_iff, Nat.succ_ne_self, imp_false,
        Decidable.not_not]
      exact BitVec.eq_of_getMsbD_eq fun i ↦ congrFun rfl
    | succ m =>
      cases m with
      | zero =>
        simp only [Nat.reduceAdd]
        exact bvcomp_eq_one_bit s t
      | succ k =>
          by_cases h : s = t
          · subst h
            simp only [↓reduceIte, BitVec.xor_self, BitVec.not_zero]
            simp only [BitVec.reduceAllOnes, BitVec.and_self]
          simp only [h]
          simp only [↓reduceIte]
          have hsplit :
              BitVec.extractLsb (k + 1) (k + 1) s ≠ BitVec.extractLsb (k + 1) (k + 1) t ∨
              BitVec.extractLsb k 0 s ≠ BitVec.extractLsb k 0 t := by
            by_contra hneg
            push_neg at hneg
            rcases hneg with ⟨hhi, hlo⟩
            apply h
            apply eq_of_high_low_eq hhi hlo
          rcases hsplit with hhi | hlo
          · have hk : k + 1 - (k + 1) + 1 = 1 := by simp only [Nat.sub_self, zero_add]
            have hs :
                (BitVec.extractLsb (k + 1) (k + 1) s).cast (by simp only [hk])
               = BitVec.ofNat 1 (s.toNat / 2 ^ (k + 1)) := by
              unfold BitVec.extractLsb BitVec.extractLsb'
              simp only [BitVec.cast_ofNat]
              have : s.toNat >>> (k + 1) = s.toNat / 2 ^ (k + 1) := by
                exact Nat.shiftRight_eq_div_pow s.toNat (k + 1)
              exact BitVec.eq_of_toNat_eq (congrArg BitVec.toNat (congrArg (BitVec.ofNat 1) this))
            have ht :
                (BitVec.extractLsb (k + 1) (k + 1) t).cast (by simp only [hk])
               = BitVec.ofNat 1 (t.toNat / 2 ^ (k + 1)) := by
              unfold BitVec.extractLsb BitVec.extractLsb'
              simp only [BitVec.cast_ofNat]
              have : t.toNat >>> (k + 1) = t.toNat / 2 ^ (k + 1) := by
                exact Nat.shiftRight_eq_div_pow t.toNat (k + 1)
              exact BitVec.eq_of_toNat_eq (congrArg BitVec.toNat (congrArg (BitVec.ofNat 1) this))
            have hneq :
                BitVec.ofNat 1 (s.toNat / 2 ^ (k + 1)) ≠
                BitVec.ofNat 1 (t.toNat / 2 ^ (k + 1)) := by
              rw [← hs, ← ht]
              change BitVec.cast hk (BitVec.extractLsb (k + 1) (k + 1) s) ≠ BitVec.cast hk (BitVec.extractLsb (k + 1) (k + 1) t)
              intro hcast
              apply hhi
              apply BitVec_cast_inj hk hcast
            have hxor :
                (BitVec.ofNat 1 (s.toNat / 2 ^ (k + 1)) ^^^
                BitVec.ofNat 1 (t.toNat / 2 ^ (k + 1))) = 1#1 := by
              bv_decide
            rw [hxor]
            simp only [BitVec.reduceNot, BitVec.zero_and]
          have hback :
              (if BitVec.extractLsb k 0 s = BitVec.extractLsb k 0 t then 1#1 else 0#1)
              = 0#1 := by
            simp only [Nat.sub_zero, hlo, ↓reduceIte]
          rw [hback]
          simp only [BitVec.and_zero]

theorem bvsub_eq_bvsub' {m : Nat} (s t : BitVec m) :
   bvsub s t = bvsub' s t := by
  unfold bvsub bvsub'
  simp only [bvadd, bvneg]
  exact BitVec.sub_eq_add_neg s t

theorem bvsdiv_eq_bvsdiv' {m : Nat} (hm : 0 < m) (s t : BitVec m) :
    bvsdiv s t = bvsdiv' s t := by
  unfold bvsdiv bvsdiv' BitVec.smtSDiv msb BitVec.msb
  simp only [BitVec.neg_eq, BitVec.ofNat_eq_ofNat, bvudiv, bvneg]
  have hs_msb :
      BitVec.ofNat 1 (s.toNat / 2 ^ (m - 1)) =
      (if s.getMsbD 0 then 1#1 else 0#1) := by
    unfold BitVec.getMsbD BitVec.getLsbD
    simp only [Nat.sub_zero, Bool.and_eq_true, decide_eq_true_eq]
    sorry
  have ht_msb :
      BitVec.ofNat 1 (t.toNat / 2 ^ (m - 1)) =
      (if t.getMsbD 0 then 1#1 else 0#1) := by
    sorry
  rw [hs_msb, ht_msb]
  cases hs : s.getMsbD 0 <;> cases ht : t.getMsbD 0
  simp only [Bool.false_eq_true, ↓reduceIte, and_self]
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.msb_one, decide_true,
    BitVec.ne_zero_of_msb_true, and_false, BitVec.zero_eq_one_iff, one_ne_zero, and_self]
  simp only [↓reduceIte, BitVec.msb_one, decide_true, BitVec.ne_zero_of_msb_true,
    Bool.false_eq_true, and_true, and_self]
  simp only [↓reduceIte, BitVec.msb_one, decide_true, BitVec.ne_zero_of_msb_true, and_self,
    and_false, and_true]

theorem bvsrem_eq_bvsrem' {m : Nat} (hm : 0 < m) (s t : BitVec m) :
    bvsrem s t = bvsrem' s t := by
  sorry

theorem bvsmod_eq_bvsmod' {m : Nat} (hm : 0 < m) (s t : BitVec m) :
    bvsmod s t = bvsmod' s t := by
  sorry

theorem bvule_eq_bvule' {m : Nat} (s t : BitVec m) :
    bvule s t ↔ bvule' s t := by
  unfold bvule bvule'
  simp only [bvult]
  unfold BitVec.ult
  constructor
  · intro h
    have h' : s.toNat ≤ t.toNat := by exact of_decide_eq_true h
    have hlt_or_eq : s.toNat < t.toNat ∨ s.toNat = t.toNat := by
      exact Nat.lt_or_eq_of_le h'
    cases hlt_or_eq with
    | inl hlt =>
      simp only [decide_eq_true_eq, Bool.decide_or, Bool.or_eq_true]
      exact Or.intro_left (s = t) hlt
    | inr heq =>
      simp only [decide_eq_true_eq, Bool.decide_or, Bool.or_eq_true]
      have : s = t := by exact BitVec.eq_of_toNat_eq heq
      simp only [this, lt_self_iff_false, or_true]
  intro h
  simp only [decide_eq_true_eq, Bool.decide_or, Bool.or_eq_true] at h
  cases h with
    | inl hlt =>
      sorry
    | inr heq =>
      rw [heq]
      sorry

theorem bvugt_eq_bvugt' {m : Nat} (s t : BitVec m) :
    bvugt s t ↔ bvugt' s t := by
  unfold bvugt bvugt' bvult BitVec.ult
  simp only [gt_iff_lt, decide_eq_true_eq]

theorem bvuge_eq_bvuge' {m : Nat} (s t : BitVec m) :
    bvuge s t ↔ bvuge' s t := by
  unfold bvuge bvuge' bvult BitVec.ult
  simp only [ge_iff_le, decide_eq_true_eq]
  apply Iff.symm
  constructor
  · intro h
    apply Nat.le_iff_lt_or_eq.mpr
    cases h with
    | inl hlt =>
      left
      simpa using (decide_eq_true_eq.mpr hlt)
    | inr heq =>
      right
      exact BitVec.toNat_inj.mpr (id (Eq.symm heq))
  intro h
  apply Nat.le_iff_lt_or_eq.mp at h
  cases h with
  | inl hlt =>
    exact Or.intro_left (s = t) hlt
  | inr heq =>
    right
    apply BitVec.eq_of_toNat_eq
    exact Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd (id (Eq.symm heq))) m)

theorem bvslt_eq_bvslt' {m : Nat} (s t : BitVec m) :
    bvslt s t ↔ bvslt' s t := by
  simp only [bvslt, decide_eq_true_eq, bvslt', msb, bvconst, extract, bvult, Bool.decide_or,
    Bool.decide_and, Bool.decide_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  sorry

theorem bvsle_eq_bvsle' {m : Nat} (s t : BitVec m) :
    bvsle s t ↔ bvsle' s t := by
  simp only [bvsle, decide_eq_true_eq, bvsle', msb, bvconst, extract, bvule, Bool.decide_or,
    Bool.decide_and, Bool.or_eq_true, Bool.and_eq_true]
  sorry

theorem bvsgt_eq_bvsgt' {m : Nat} (s t : BitVec m) :
  bvsgt s t ↔ bvsgt' s t := by
  sorry

theorem bvsge_eq_bvsge' {m : Nat} (s t : BitVec m) :
  bvsge s t ↔ bvsge' s t := by
  sorry

theorem bvusubo_eq_bvusubo' {m : Nat} (s t : BitVec m) :
  bvusubo s t ↔ bvusubo' s t := by
  sorry

theorem bvssubo_eq_bvssubo' {m : Nat} (s t : BitVec m) :
  bvssubo s t ↔ bvssubo' s t := by
  sorry

theorem bvsdivo_eq_bvsdivo' {m : Nat} (s t : BitVec m) :
  bvsdivo s t ↔ bvsdivo' s t := by
  sorry

theorem bvashr_eq_bvashr' {m : Nat} (s t : BitVec m) :
  bvashr s t = bvashr' s t := by
  sorry

theorem re_peat_1_eq_self {m : Nat} (s : BitVec m) :
  (re_peat 1 s).cast (by simp only [mul_one]) = s := by
  simp only [re_peat, eq_mpr_eq_cast]
  have h1 : m * 1 = m := by simp only [mul_one]
  have h2 : BitVec m = BitVec (m * 1) := by simp only [mul_one]
  change BitVec.cast h1 (cast h2 s) = s
  sorry

theorem zero_extend_0_eq_self {m : Nat} (s : BitVec m) :
  zero_extend 0 s = s := by
  simp only [Nat.add_zero, zero_extend, BitVec.setWidth_eq]

theorem sign_extend_0_eq_self {m : Nat} (s : BitVec m) :
  sign_extend 0 s = s := by
  simp only [Nat.add_zero, sign_extend, BitVec.signExtend_eq]

theorem rotate_left_0_eq_self {m : Nat} (s : BitVec m) :
  rotate_left 0 s = s := by
  simp only [rotate_left]
  unfold BitVec.rotateLeft BitVec.rotateLeftAux
  simp only [Nat.zero_mod, BitVec.shiftLeft_zero, Nat.sub_zero]
  have hshift : s >>> m = (0 : BitVec m) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod]
    have hs : s.toNat < 2 ^ m := by
      exact s.isLt
    exact Nat.shiftRight_eq_zero s.toNat m hs
  simp only [hshift, BitVec.ofNat_eq_ofNat, BitVec.or_zero]

theorem rotate_right_0_eq_self {m : Nat} (s : BitVec m) :
  rotate_right 0 s = s := by
  simp only [rotate_right]
  unfold BitVec.rotateRight BitVec.rotateRightAux
  simp only [Nat.zero_mod, BitVec.ushiftRight_zero, Nat.sub_zero, le_refl, BitVec.shiftLeft_eq_zero,
    BitVec.or_zero]

end SMT
