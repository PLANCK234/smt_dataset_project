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

@[expose, simp]
def re_peat {m : Nat} (i : Nat) (x : BitVec m) : BitVec (m * i) :=
  match i with
  | 0 => 1
  | 1 => x.cast (by simp only [mul_one])
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

@[expose, simp] def bvule {m : Nat} (x y : BitVec m) : Bool := BitVec.ule x y
@[expose, simp] def bvule' {m : Nat} (x y : BitVec m) : Bool := (bvult x y) ∨ (x = y)

@[expose, simp] def bvugt {m : Nat} (x y : BitVec m) : Bool := x.toNat > y.toNat
@[expose, simp] def bvugt' {m : Nat} (x y : BitVec m) : Bool := bvult y x

@[expose, simp] def bvuge {m : Nat} (x y : BitVec m) : Bool := x.toNat ≥ y.toNat
@[expose, simp] def bvuge' {m : Nat} (x y : BitVec m) : Bool := (bvult y x) ∨ (x = y)

@[expose, simp] def bvslt {m : Nat} (x y : BitVec m) : Bool := BitVec.slt x y
@[expose, simp] def bvslt' {m : Nat} (s t : BitVec m) : Bool :=
  (msb s = bvconst 1 1 ∧
   msb t = bvconst 0 1)
  ∨
  (msb s =
   msb t ∧
   bvult s t)

@[expose, simp] def bvsle {m : Nat} (x y : BitVec m) : Bool := BitVec.sle x y
@[expose, simp] def bvsle' {m : Nat} (s t : BitVec m) : Bool :=
  (msb s = bvconst 1 1 ∧
   msb t = bvconst 0 1)
  ∨
  (msb s =
   msb t ∧
   bvule s t)

@[expose, simp] def bvsgt {m : Nat} (x y : BitVec m) : Bool := x.toInt > y.toInt
@[expose, simp] def bvsgt' {m : Nat} (x y : BitVec m) : Bool := bvslt y x

@[expose, simp] def bvsge {m : Nat} (x y : BitVec m) : Bool := x.toInt ≥ y.toInt
@[expose, simp] def bvsge' {m : Nat} (x y : BitVec m) : Bool := bvsle y x

@[expose, simp] def bvssubo {m : Nat} (x y : BitVec m) : Bool := BitVec.ssubOverflow x y
@[expose, simp] def bvssubo' {m : Nat} (x y : BitVec m) : Bool :=
  if (bvnego y) then
    (bvsge x (bvconst 0 m))
  else
    bvsaddo x (bvneg y)

@[expose, simp] def bvsdivo {m : Nat} (x y : BitVec m) : Bool := BitVec.sdivOverflow x y
@[expose, simp] def bvsdivo' {m : Nat} (x y : BitVec m) : Bool :=
  (bvnego x) ∧ (y = (bvnot (bvconst 0 m)))

/- The following section presents a proof of equivalence between the
SMT-LIB expressions and their counterparts in the Lean library. -/

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
 -- simpa using h0
    exact
      Eq.mp
        (congr
          (congrArg Eq
            (Eq.trans
              (BitVec.getElem_extract
                (of_eq_true
                  (Eq.trans
                    (congrArg (LT.lt 0)
                      (Eq.trans (congrArg (fun x ↦ x + 1) (Nat.sub_self (k + 1))) (zero_add 1)))
                    (Nat.lt_add_one._simp_1 0))))
              (congrArg s.getLsbD (add_zero (k + 1)))))
          (Eq.trans
            (BitVec.getElem_extract
              (of_eq_true
                (Eq.trans
                  (congrArg (LT.lt 0)
                    (Eq.trans (congrArg (fun x ↦ x + 1) (Nat.sub_self (k + 1))) (zero_add 1)))
                  (Nat.lt_add_one._simp_1 0))))
            (congrArg t.getLsbD (add_zero (k + 1)))))
        h0
  intro hlt
  have hik : i < k + 1 := by
    exact lt_of_le_of_ne (Nat.lt_succ_iff.mp hlt) hi
  have h := congrArg (fun x => x.getLsbD i) hlo
--simpa [(Nat.le_of_lt_succ hik)] using h
  exact
    Eq.mp
      (congr
        (congrArg Eq
          (Eq.trans (BitVec.getLsbD_extract k 0 s i)
            (Eq.trans
              (congr
                (congrArg and
                  (Eq.trans
                    (Decidable.decide.congr_simp (i ≤ k - 0) True (eq_true (Nat.le_of_lt_succ hik)))
                    (decide_true instDecidableTrue)))
                (congrArg s.getLsbD (zero_add i)))
              (Bool.true_and (s.getLsbD i)))))
        (Eq.trans (BitVec.getLsbD_extract k 0 t i)
          (Eq.trans
            (congr
              (congrArg and
                (Eq.trans
                  (Decidable.decide.congr_simp (i ≤ k - 0) True (eq_true (Nat.le_of_lt_succ hik)))
                  (decide_true instDecidableTrue)))
              (congrArg t.getLsbD (zero_add i)))
            (Bool.true_and (t.getLsbD i)))))
      h

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
  exact BitVec.eq_of_toNat_eq (congrArg BitVec.toNat hxy)

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
            simp only [BitVec.reduceAllOnes, BitVec.and_eq, BitVec.and_self]
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
          · have hk : k + 1 - (k + 1) + 1 = 1 := by
              simp only [Nat.sub_self, zero_add]
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
            simp only [BitVec.reduceNot, BitVec.and_eq, BitVec.zero_and]
          have hback :
              (if BitVec.extractLsb k 0 s = BitVec.extractLsb k 0 t then 1#1 else 0#1)
              = 0#1 := by
            simp only [Nat.sub_zero, hlo, ↓reduceIte]
          rw [hback]
          simp only [BitVec.and_eq, BitVec.and_zero]

theorem bvsub_eq_bvsub' {m : Nat} (s t : BitVec m) :
   bvsub s t = bvsub' s t := by
  unfold bvsub bvsub'
  simp only [bvadd, bvneg]
  exact BitVec.sub_eq_add_neg s t

lemma ofNat_div_pow_pred_eq_msb
    {m : Nat} (x : BitVec m) :
    BitVec.ofNat 1 (x.toNat / 2 ^ (m - 1)) =
      (if x.getMsbD 0 then 1#1 else 0#1) := by
  by_cases h0 : m = 0
  subst h0
  cases x
  simp only [BitVec.toNat_ofFin, Nat.pow_zero, Fin.val_eq_zero, Nat.zero_le, Nat.sub_eq_zero_of_le,
    pow_zero, Nat.div_one, le_refl, BitVec.getMsbD_of_ge, Bool.false_eq_true, ↓reduceIte]
  have hm : 0 < m := by exact Nat.zero_lt_of_ne_zero h0
  cases h : x.getMsbD 0
  simp only [Bool.false_eq_true, ↓reduceIte]
  · have h1 : x.toNat < 2 ^ (m - 1) := by
      exact BitVec.toNat_lt_of_msb_false h
    have h2 : x.toNat / 2 ^ (m - 1) = 0 := by
      exact Nat.div_eq_of_lt h1
    exact
      Eq.symm
        (BitVec.eq_of_toNat_eq
          (congrArg BitVec.toNat
            (congrArg (BitVec.ofNat 1) (id (Eq.symm h2)))))
  · have h3 : 2 ^ (m - 1) ≤ x.toNat := by
      exact BitVec.le_toNat_of_msb_true h
    have h4 : x.toNat < 2 ^ m := by
      exact BitVec.isLt x
    have h_pos : 0 < 2 ^ (m - 1) := by
      exact Nat.two_pow_pos (m - 1)
    have h5 : 1 ≤ x.toNat / 2 ^ (m - 1) := by
      exact (Nat.one_le_div_iff h_pos).mpr h3
    have m_notzero : m ≠ 0 := by
      exact Nat.ne_zero_of_lt hm
    have heq : 2 ^ m = 2 * 2 ^ (m - 1) := by
      apply Eq.symm
      exact mul_pow_sub_one m_notzero 2
    have h4' : x.toNat < 2 * 2 ^ (m - 1) := by
      exact Nat.lt_of_lt_of_eq h4 heq
    have h6 : x.toNat / 2 ^ (m - 1) < 2 := by
      exact (Nat.div_lt_iff_lt_mul h_pos).mpr h4'
    have h_final : x.toNat / 2 ^ (m - 1) = 1 := by
      exact Nat.eq_of_le_of_lt_succ h5 h6
    exact
      Eq.symm
        (BitVec.eq_of_toNat_eq
          (congrArg BitVec.toNat
            (congrArg (BitVec.ofNat 1) (id (Eq.symm h_final)))))

theorem msb_eq_if_bool {m : Nat} (s : BitVec m) :
    msb s = (if BitVec.msb s then 1#1 else 0#1) := by
  unfold msb
  simp only [BitVec.msb]
  exact ofNat_div_pow_pred_eq_msb s

theorem bvsdiv_eq_bvsdiv' {m : Nat} (s t : BitVec m) :
    bvsdiv s t = bvsdiv' s t := by
  unfold bvsdiv bvsdiv' BitVec.smtSDiv msb BitVec.msb
  simp only [BitVec.neg_eq, BitVec.ofNat_eq_ofNat, bvudiv, bvneg]
  have hs_msb :
      BitVec.ofNat 1 (s.toNat / 2 ^ (m - 1)) =
      (if s.getMsbD 0 then 1#1 else 0#1) := by
    exact ofNat_div_pow_pred_eq_msb s
  have ht_msb :
      BitVec.ofNat 1 (t.toNat / 2 ^ (m - 1)) =
      (if t.getMsbD 0 then 1#1 else 0#1) := by
    exact ofNat_div_pow_pred_eq_msb t
  rw [hs_msb, ht_msb]
  cases hs : s.getMsbD 0 <;> cases ht : t.getMsbD 0
  simp only [Bool.false_eq_true, ↓reduceIte, and_self]
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.msb_one, decide_true,
    BitVec.ne_zero_of_msb_true, and_false, BitVec.zero_eq_one_iff, one_ne_zero, and_self]
  simp only [↓reduceIte, BitVec.msb_one, decide_true, BitVec.ne_zero_of_msb_true,
    Bool.false_eq_true, and_true, and_self]
  simp only [↓reduceIte, BitVec.msb_one, decide_true, BitVec.ne_zero_of_msb_true, and_self,
    and_false, and_true]

theorem sub_eq_add_neg_comm {m : Nat} (a b : BitVec m) : a - b = -b + a := by
  rw [@BitVec.sub_eq_add_neg]
  rw [@BitVec.add_comm]

theorem bvsrem_eq_bvsrem' {m : Nat} (s t : BitVec m) :
    bvsrem s t = bvsrem' s t := by
  unfold bvsrem bvsrem' BitVec.srem msb BitVec.msb
  simp only [BitVec.umod_eq, BitVec.neg_eq, BitVec.ofNat_eq_ofNat, bvurem, bvneg]
  have hs_msb :
      BitVec.ofNat 1 (s.toNat / 2 ^ (m - 1)) =
      (if s.getMsbD 0 then 1#1 else 0#1) := by
    exact ofNat_div_pow_pred_eq_msb s
  have ht_msb :
      BitVec.ofNat 1 (t.toNat / 2 ^ (m - 1)) =
      (if t.getMsbD 0 then 1#1 else 0#1) := by
    exact ofNat_div_pow_pred_eq_msb t
  rw [hs_msb, ht_msb]
  cases hs : s.getMsbD 0 <;> cases ht : t.getMsbD 0
  simp only [Bool.false_eq_true, ↓reduceIte, and_self]
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.msb_one, decide_true,
    BitVec.ne_zero_of_msb_true, and_false, BitVec.zero_eq_one_iff, one_ne_zero, and_self]
  simp only [↓reduceIte, BitVec.msb_one, decide_true, BitVec.ne_zero_of_msb_true,
    Bool.false_eq_true, and_true, and_self]
  simp only [↓reduceIte, BitVec.msb_one, decide_true, BitVec.ne_zero_of_msb_true, and_self,
    and_false, and_true]

theorem bvsmod_eq_bvsmod' {m : Nat} (s t : BitVec m) :
    bvsmod s t = bvsmod' s t := by
  unfold bvsmod bvsmod' BitVec.smod msb BitVec.msb
  simp only [BitVec.umod_eq, BitVec.neg_eq, BitVec.zero_eq, BitVec.add_eq, BitVec.sub_eq, bvurem,
    bvabs, msb, BitVec.ofNat_eq_ofNat, bvneg, bvadd]
  have hs_msb :
      BitVec.ofNat 1 (s.toNat / 2 ^ (m - 1)) =
      (if s.getMsbD 0 then 1#1 else 0#1) := by
    exact ofNat_div_pow_pred_eq_msb s
  have ht_msb :
      BitVec.ofNat 1 (t.toNat / 2 ^ (m - 1)) =
      (if t.getMsbD 0 then 1#1 else 0#1) := by
    exact ofNat_div_pow_pred_eq_msb t
  rw [hs_msb, ht_msb]
  cases hs : s.getMsbD 0 <;> cases ht : t.getMsbD 0
  simp only [Bool.false_eq_true, ↓reduceIte, and_self, ite_self]
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.msb_one, decide_true,
    BitVec.ne_zero_of_msb_true, and_false, BitVec.zero_eq_one_iff, one_ne_zero, and_self]
  simp only [↓reduceIte, BitVec.msb_one, decide_true, BitVec.ne_zero_of_msb_true,
    Bool.false_eq_true, and_true, and_self]
  split_ifs
  exact BitVec_cast_inj rfl rfl
  exact sub_eq_add_neg_comm t (-s % t)
  simp only [↓reduceIte, BitVec.msb_one, decide_true, BitVec.ne_zero_of_msb_true, and_self,
    and_false, and_true, right_eq_ite_iff]
  intro h
  rw [h]
  simp only [BitVec.neg_zero]

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
      unfold BitVec.ule
      simp only [decide_eq_true_eq]
      exact Nat.le_of_succ_le hlt
    | inr heq =>
      rw [heq]
      unfold BitVec.ule
      simp only [le_refl, decide_true]

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
      exact BitVec.lt_def.mp hlt
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

theorem toInt_eq_toNat_of_getMsbD_eq_false
    {m : Nat} (x : BitVec m) (h : x.getMsbD 0 = false) :
    x.toInt = x.toNat := by
  unfold BitVec.toInt
  simp only [Int.natCast_pow, Int.cast_ofNat_Int, ite_eq_left_iff, not_lt, sub_eq_self]
  intro h'
  have : 2 * x.toNat < 2 ^ m := by
    exact BitVec.msb_eq_false_iff_two_mul_lt.mp h
  exfalso
  have : 2 ^ m < 2 ^ m := by exact Nat.lt_of_le_of_lt h' this
  exact (lt_self_iff_false (2 ^ m)).mp this

theorem toInt_eq_toNat_sub_twoPow_of_getMsbD_eq_true
    {m : Nat} (x : BitVec m) (h : x.getMsbD 0 = true) :
    x.toInt = (x.toNat : Int) - (2 ^ m : Nat) := by
  unfold BitVec.toInt
  simp only [Int.natCast_pow, Int.cast_ofNat_Int, ite_eq_right_iff]
  intro h'
  have : 2 ^ m ≤ 2 * x.toNat := by exact BitVec.msb_eq_true_iff_two_mul_ge.mp h
  exfalso
  have : 2 ^ m < 2 ^ m := by exact Nat.lt_of_le_of_lt this h'
  exact (lt_self_iff_false (2 ^ m)).mp this

theorem msb_if_encode_eq {m : Nat} (s t : BitVec m) :
    (if s.getMsbD 0 = true then 1#1 else 0#1) =
    (if t.getMsbD 0 = true then 1#1 else 0#1) ↔
    s.getMsbD 0 = t.getMsbD 0 := by
  by_cases hs : s.getMsbD 0 = true <;>
  by_cases ht : t.getMsbD 0 = true <;>
  simp only [hs, ↓reduceIte, ht]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.msb_one, decide_true,
    BitVec.ne_zero_of_msb_true, Bool.true_eq_false]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.zero_eq_one_iff, one_ne_zero]

theorem toInt_lt_of_msb_true_false
    {m : ℕ} (s t : BitVec m)
    (h : s.getMsbD 0 = true ∧ t.getMsbD 0 = false) :
    s.toInt < t.toInt := by
  by_cases h0 : m = 0
  exfalso
  obtain ⟨hs1, _⟩ := h
  have hs : s.getMsbD 0 = false := by exact BitVec.getMsbD_of_zero_length h0 s
  rw [hs] at hs1
  exact (Bool.eq_not_self false).mp hs1
  have hm : 0 < m := by exact Nat.zero_lt_of_ne_zero h0
  obtain ⟨hs, ht⟩ := h
  have hs_neg : s.toInt < 0 := by exact BitVec.toInt_neg_of_msb_true hs
  have ht_nonneg : 0 ≤ t.toInt := by exact BitVec.toInt_nonneg_of_msb_false ht
  exact lt_of_lt_of_le hs_neg ht_nonneg

theorem toInt_lt_of_msb_true_false'
    {m : ℕ} (s t : BitVec m)
    (h :
      ((if s.getMsbD 0 = true then 1#1 else 0#1) = 1#1) ∧ (if t.getMsbD 0 = true then 1#1 else 0#1) = 0#1 ) :
    s.toInt < t.toInt := by
  simp only [ite_eq_left_iff, Bool.not_eq_true, BitVec.zero_eq_one_iff, one_ne_zero, imp_false,
    Bool.not_eq_false, ite_eq_right_iff, BitVec.msb_one, decide_true,
    BitVec.ne_zero_of_msb_true] at h
  exact toInt_lt_of_msb_true_false s t h

theorem toNat_lt_iff_toInt_lt_of_same_msb
    {m : Nat} (s t : BitVec m)
    (hmsb : s.getMsbD 0 = t.getMsbD 0) :
    s.toNat < t.toNat ↔ s.toInt < t.toInt := by
  by_cases hs : s.getMsbD 0 = false
  · have ht : t.getMsbD 0 = false := by
    --simpa [hs] using hmsb
      exact
        Eq.mp (Eq.trans (congrArg (fun x ↦ x = t.getMsbD 0) hs) (Bool.false_eq (t.getMsbD 0))) hmsb
    rw [toInt_eq_toNat_of_getMsbD_eq_false s hs,
        toInt_eq_toNat_of_getMsbD_eq_false t ht]
    exact_mod_cast Iff.rfl
  · have hs' : s.getMsbD 0 = true := by
      cases h : s.getMsbD 0 <;> simp_all
    have ht : t.getMsbD 0 = true := by
    --simpa [hs'] using hmsb
      exact
        Eq.mp (Eq.trans (congrArg (fun x ↦ x = t.getMsbD 0) hs') (Bool.true_eq (t.getMsbD 0))) hmsb
    rw [toInt_eq_toNat_sub_twoPow_of_getMsbD_eq_true s hs',
        toInt_eq_toNat_sub_twoPow_of_getMsbD_eq_true t ht]
    constructor
    · intro hlt
      have hlt' : (s.toNat : Int) < (t.toNat : Int) := by
        exact cast (Eq.symm Int.ofNat_lt._simp_1) hlt
      exact Int.sub_lt_sub_right_iff.mpr hlt'
    · intro hlt
      have hlt' : (s.toNat : Int) < (t.toNat : Int) := by
        exact Int.sub_lt_sub_right_iff.mp hlt
      exact cast Int.ofNat_lt._simp_1 hlt'

theorem toNat_le_iff_toInt_le_of_same_msb
    {m : Nat} (s t : BitVec m)
    (hmsb : s.getMsbD 0 = t.getMsbD 0) :
    s.toNat ≤  t.toNat ↔ s.toInt ≤ t.toInt := by
  by_cases hs : s.getMsbD 0 = false
  · have ht : t.getMsbD 0 = false := by
    --simpa [hs] using hmsb
      exact
        Eq.mp (Eq.trans (congrArg (fun x ↦ x = t.getMsbD 0) hs) (Bool.false_eq (t.getMsbD 0))) hmsb
    rw [toInt_eq_toNat_of_getMsbD_eq_false s hs,
        toInt_eq_toNat_of_getMsbD_eq_false t ht]
    exact_mod_cast Iff.rfl
  · have hs' : s.getMsbD 0 = true := by
      cases h : s.getMsbD 0 <;> simp_all
    have ht : t.getMsbD 0 = true := by
    --simpa [hs'] using hmsb
      exact
        Eq.mp (Eq.trans (congrArg (fun x ↦ x = t.getMsbD 0) hs') (Bool.true_eq (t.getMsbD 0))) hmsb
    rw [toInt_eq_toNat_sub_twoPow_of_getMsbD_eq_true s hs',
        toInt_eq_toNat_sub_twoPow_of_getMsbD_eq_true t ht]
    constructor
    · intro hlt
      have hlt' : (s.toNat : Int) ≤  (t.toNat : Int) := by
        exact cast (Eq.symm Int.ofNat_le._simp_1) hlt
      exact Int.sub_le_sub_right hlt' ↑(2 ^ m)
    · intro hlt
      have hlt' : (s.toNat : Int) ≤  (t.toNat : Int) := by
        exact Int.le_of_sub_le_sub_right hlt
      exact Int.ofNat_le.mp hlt'

theorem bvslt_eq_bvslt' {m : Nat} (s t : BitVec m) :
    bvslt s t ↔ bvslt' s t := by
  unfold bvslt bvslt' BitVec.slt
  simp only [decide_eq_true_eq, msb, bvconst, bvult, Bool.decide_or, Bool.decide_and,
    Bool.decide_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  apply Iff.symm
  constructor
  · intro h
    cases h with
    | inl hlt =>
      rw [ofNat_div_pow_pred_eq_msb s, ofNat_div_pow_pred_eq_msb t] at hlt
      exact toInt_lt_of_msb_true_false' s t hlt
    | inr heq =>
      unfold BitVec.ult at heq
      obtain ⟨h1, h2⟩ := heq
      simp only [decide_eq_true_eq] at h2
      apply (toNat_lt_iff_toInt_lt_of_same_msb s t ?_).mp h2
      have hs :
          BitVec.ofNat 1 (s.toNat / 2 ^ (m - 1)) =
            (if s.getMsbD 0 then 1#1 else 0#1) := by
        exact ofNat_div_pow_pred_eq_msb s
      have ht :
          BitVec.ofNat 1 (t.toNat / 2 ^ (m - 1)) =
            (if t.getMsbD 0 then 1#1 else 0#1) := by
        exact ofNat_div_pow_pred_eq_msb t
      rw [hs, ht] at h1
      exact (msb_if_encode_eq s t).mp h1
  intro h
  rw [ofNat_div_pow_pred_eq_msb s, ofNat_div_pow_pred_eq_msb t]
  unfold BitVec.ult
  simp only [ite_eq_left_iff, Bool.not_eq_true, BitVec.zero_eq_one_iff, one_ne_zero, imp_false,
    Bool.not_eq_false, ite_eq_right_iff, BitVec.msb_one, decide_true, BitVec.ne_zero_of_msb_true,
    decide_eq_true_eq]
  rw [msb_if_encode_eq]
  by_cases hs : s.getMsbD 0 = true
  · by_cases ht : t.getMsbD 0 = true
    · right
      constructor
      · exact hs.trans ht.symm
      · rw [toInt_eq_toNat_sub_twoPow_of_getMsbD_eq_true s hs, toInt_eq_toNat_sub_twoPow_of_getMsbD_eq_true t ht] at h
        simp only [Int.natCast_pow, Int.cast_ofNat_Int, Int.sub_lt_sub_right_iff, Int.ofNat_lt] at h
        exact h
    · left
      constructor
      · exact hs
      · exact Eq.symm ((fun {a b} ↦ Bool.not_not_eq.mp) fun a ↦ ht (id (Eq.symm a)))
  · have hs' : s.getMsbD 0 = false := by
      cases hmsb : s.getMsbD 0 <;> simp [hmsb] at hs ⊢
    by_cases ht : t.getMsbD 0 = true
    · exfalso
      rw [toInt_eq_toNat_of_getMsbD_eq_false s hs',
          toInt_eq_toNat_sub_twoPow_of_getMsbD_eq_true t ht] at h
      have hnonneg : (0 : Int) ≤ s.toInt := by
        rw [toInt_eq_toNat_of_getMsbD_eq_false s hs']
        exact Int.natCast_nonneg s.toNat
      have hneg : t.toInt < 0 := by
        rw [toInt_eq_toNat_sub_twoPow_of_getMsbD_eq_true t ht]
        have htlt : t.toNat < 2^m := by
          exact t.toFin.isLt
        simp only [Int.natCast_pow, Int.cast_ofNat_Int, gt_iff_lt]
        have hle : (t.toNat : Int) < (2 ^ m : Nat) := by
          exact cast (Eq.symm Int.ofNat_lt._simp_1) htlt
        exact Int.sub_neg_of_lt hle
      have hs_nonneg : (0 : Int) ≤ s.toNat := by
        simp only [Int.natCast_nonneg]
      have hs_lt_zero : (s.toNat : Int) < 0 := by
        have ht_rhs_neg : (t.toNat : Int) - (2 ^ m : Int) < 0 := by
          have : t.toNat < 2 ^ m := by
            exact t.toFin.isLt
          have : (t.toNat : Int) < (2 ^ m : Int) := by exact Int.lt_toNat.mp this
          exact Int.sub_neg_of_lt this
        exact Int.lt_trans h ht_rhs_neg
      exact (Int.negSucc_not_nonneg s.toNat).mp hs_lt_zero
    · have ht' : t.getMsbD 0 = false := by
        cases hmsb : t.getMsbD 0 <;> simp [hmsb] at ht ⊢
      right
      constructor
      · exact hs'.trans ht'.symm
      · rw [toInt_eq_toNat_of_getMsbD_eq_false s hs',
            toInt_eq_toNat_of_getMsbD_eq_false t ht'] at h
        exact cast Int.ofNat_lt._simp_1 h

theorem bvsle_eq_bvsle' {m : Nat} (s t : BitVec m) :
    bvsle s t ↔ bvsle' s t := by
  unfold bvsle bvsle' BitVec.sle
  simp only [decide_eq_true_eq, msb, bvconst, bvule, Bool.decide_or, Bool.decide_and,
    Bool.decide_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  rw [ofNat_div_pow_pred_eq_msb s, ofNat_div_pow_pred_eq_msb t, msb_if_encode_eq]
  apply Iff.symm
  constructor
  · intro h
    cases h with
    | inl hlt =>
      have : s.toInt < t.toInt := by exact toInt_lt_of_msb_true_false' s t hlt
      exact Int.le_of_lt this
    | inr heq =>
      unfold BitVec.ult at heq
      obtain ⟨h1, h2⟩ := heq
      unfold BitVec.ule at h2
      simp only [decide_eq_true_eq] at h2
      exact (toNat_le_iff_toInt_le_of_same_msb s t h1).mp h2
  intro h
  unfold BitVec.ule
  simp only [ite_eq_left_iff, Bool.not_eq_true, BitVec.zero_eq_one_iff, one_ne_zero, imp_false,
    Bool.not_eq_false, ite_eq_right_iff, BitVec.msb_one, decide_true, BitVec.ne_zero_of_msb_true,
    decide_eq_true_eq]
  by_cases hs : s.getMsbD 0 = true
  · by_cases ht : t.getMsbD 0 = true
    · right
      constructor
      · exact hs.trans ht.symm
      · rw [toInt_eq_toNat_sub_twoPow_of_getMsbD_eq_true s hs, toInt_eq_toNat_sub_twoPow_of_getMsbD_eq_true t ht] at h
        simp only [Int.natCast_pow, Int.cast_ofNat_Int, Int.sub_le_sub_right_iff, Int.ofNat_le] at h
        exact h
    · left
      constructor
      · exact hs
      · exact Eq.symm ((fun {a b} ↦ Bool.not_not_eq.mp) fun a ↦ ht (id (Eq.symm a)))
  · have hs' : s.getMsbD 0 = false := by
      cases hmsb : s.getMsbD 0 <;> simp [hmsb] at hs ⊢
    by_cases ht : t.getMsbD 0 = true
    · exfalso
      rw [toInt_eq_toNat_of_getMsbD_eq_false s hs',
          toInt_eq_toNat_sub_twoPow_of_getMsbD_eq_true t ht] at h
      have hnonneg : (0 : Int) ≤ s.toInt := by
        rw [toInt_eq_toNat_of_getMsbD_eq_false s hs']
        exact Int.natCast_nonneg s.toNat
      have hneg : t.toInt < 0 := by
        rw [toInt_eq_toNat_sub_twoPow_of_getMsbD_eq_true t ht]
        have htlt : t.toNat < 2^m := by
          exact t.toFin.isLt
        simp only [Int.natCast_pow, Int.cast_ofNat_Int, gt_iff_lt]
        have hle : (t.toNat : Int) < (2 ^ m : Nat) := by
          exact cast (Eq.symm Int.ofNat_lt._simp_1) htlt
        exact Int.sub_neg_of_lt hle
      have hs_nonneg : (0 : Int) ≤ s.toNat := by
        simp only [Int.natCast_nonneg]
      have hs_lt_zero : (s.toNat : Int) < 0 := by
        have ht_rhs_neg : (t.toNat : Int) - (2 ^ m : Int) < 0 := by
          have : t.toNat < 2 ^ m := by
            exact t.toFin.isLt
          have : (t.toNat : Int) < (2 ^ m : Int) := by exact Int.lt_toNat.mp this
          exact Int.sub_neg_of_lt this
        exact Int.lt_of_le_of_lt h ht_rhs_neg
      exact (Int.negSucc_not_nonneg s.toNat).mp hs_lt_zero
    · have ht' : t.getMsbD 0 = false := by
        cases hmsb : t.getMsbD 0 <;> simp [hmsb] at ht ⊢
      right
      constructor
      · exact hs'.trans ht'.symm
      · rw [toInt_eq_toNat_of_getMsbD_eq_false s hs',
            toInt_eq_toNat_of_getMsbD_eq_false t ht'] at h
        exact Int.ofNat_le.mp h

theorem bvsgt_eq_bvslt
    {m : Nat} (s t : BitVec m) :
    bvsgt s t ↔ bvslt t s := by
  rfl

lemma msb_encode_eq_one_iff
    {m : Nat} (x : BitVec m) :
    BitVec.ofNat 1 (x.toNat / 2 ^ (m - 1)) = 1#1 ↔ x.getMsbD 0 = true := by
  constructor
  intro h
  have : 2^(m-1) < x.toNat := by sorry
  sorry
  intro h
  have : 2^(m-1) < x.toNat := by sorry
  sorry




lemma msb_encode_eq_zero_iff
    {m : Nat} (x : BitVec m) (hm : 0 < m) :
    BitVec.ofNat 1 (x.toNat / 2 ^ (m - 1)) = 0#1 ↔ x.getMsbD 0 = false := by
  sorry

lemma msb_encode_eq_iff
    {m : Nat} (x y : BitVec m) (hm : 0 < m) :
    BitVec.ofNat 1 (x.toNat / 2 ^ (m - 1)) =
      BitVec.ofNat 1 (y.toNat / 2 ^ (m - 1)) ↔
    x.getMsbD 0 = y.getMsbD 0 := by
  sorry

theorem toInt_lt_iff
    {m : Nat} (hm : 0 < m) (x y : BitVec m) :
    x.toInt < y.toInt ↔
      (x.getMsbD 0 = true ∧ y.getMsbD 0 = false) ∨
      (x.getMsbD 0 = y.getMsbD 0 ∧ x.toNat < y.toNat) := by
  sorry

theorem bvsgt'_eq_bvslt'
    {m : Nat} (s t : BitVec m) :
    bvsgt' s t ↔ bvslt' t s := by
  unfold bvsgt' bvslt' bvslt BitVec.slt
  simp only [decide_eq_true_eq, msb, bvconst, bvult, Bool.decide_or, Bool.decide_and,
    Bool.decide_eq_true, Bool.or_eq_true, Bool.and_eq_true]
  apply Iff.symm
  constructor
  rw [toInt_lt_iff hm t s]
  constructor
  · intro h
    rcases h with h | h
    · rcases h with ⟨ht1, hs0⟩
      left
      constructor
      · exact (msb_encode_eq_one_iff t hm).mp ht1
      · exact (msb_encode_eq_zero_iff s hm).mp hs0
    · rcases h with ⟨hmsb, hult⟩
      right
      constructor
      · exact (msb_encode_eq_iff t s hm).mp hmsb
      · exact (ult_eq_true_iff t s).mp hult
  · intro h
    rcases h with h | h
    · rcases h with ⟨ht, hs⟩
      left
      constructor
      · exact (msb_encode_eq_one_iff t hm).mpr ht
      · exact (msb_encode_eq_zero_iff s hm).mpr hs
    · rcases h with ⟨hmsb, hlt⟩
      right
      constructor
      · exact (msb_encode_eq_iff t s hm).mpr hmsb
      · exact (ult_eq_true_iff t s).mpr hlt








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
  unfold bvashr bvashr' BitVec.sshiftRight msb
  simp only [bvconst, bvlshr, BitVec.ushiftRight_eq', bvnot, BitVec.not_eq]
  sorry

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

theorem re_peat_1_eq_self {m : Nat} (s : BitVec m) :
  (re_peat 1 s).cast (by simp only [mul_one]) = s := by
  simp only [re_peat, BitVec.cast_cast, BitVec.cast_eq]

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
