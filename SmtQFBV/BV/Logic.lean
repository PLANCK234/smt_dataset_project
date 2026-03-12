import Std
import Mathlib.Data.Num.Bitwise

namespace SMT
/-
(concat (_ BitVec i) (_ BitVec j) (_ BitVec m))
  - concatenation of bitvectors of size i and j to get a new bitvector of
    size m, where m = i + j
-/
@[simp]
def concat {i j : Nat} (x : BitVec i) (y : BitVec j) : BitVec (i + j) := BitVec.append x y

/-
((_ extract i j) (_ BitVec m) (_ BitVec n))
  - extraction of bits i down to j from a bitvector of size m to yield a
    new bitvector of size n, where n = i - j + 1
-/
@[simp]
def extract {m : Nat} (i j : Nat) (x : BitVec m) : BitVec (i - j + 1) := BitVec.extractLsb i j x

@[simp]
def bvnot {m : Nat} (x : BitVec m) : BitVec m := ~~~x
@[simp]
def bvand {m : Nat} (x y : BitVec m) : BitVec m := x &&& y
@[simp]
def bvor  {m : Nat} (x y : BitVec m) : BitVec m := x ||| y
@[simp]
def bvneg {m : Nat} (x : BitVec m) : BitVec m := -x
@[simp]
def bvadd {m : Nat} (x y : BitVec m) : BitVec m := x + y
@[simp]
def bvmul {m : Nat} (x y : BitVec m) : BitVec m := x * y
@[simp]
def bvudiv {m : Nat} (x y : BitVec m) : BitVec m := BitVec.smtUDiv x y
@[simp]
def bvurem {m : Nat} (x y : BitVec m) : BitVec m := BitVec.umod x y
@[simp]
def bvshl {m : Nat} (x y : BitVec m) : BitVec m := x <<< y
@[simp]
def bvlshr {m : Nat} (x y : BitVec m) : BitVec m := x >>> y

@[simp]
def bvult {m : Nat} (x y : BitVec m) : Prop := BitVec.ult x y
@[simp]
def bvnego {m : Nat} (x : BitVec m) : Prop := x ≠ 0
@[simp]
def bvuaddo {m : Nat} (x y : BitVec m) : Prop := BitVec.uaddOverflow x y
@[simp]
def bvsaddo {m : Nat} (x y : BitVec m) : Prop := BitVec.saddOverflow x y
@[simp]
def bvumulo {m : Nat} (x y : BitVec m) : Prop := BitVec.umulOverflow x y
@[simp]
def bvsmulo {m : Nat} (x y : BitVec m) : Prop := BitVec.smulOverflow x y

@[simp]
def ubv_to_int {m : Nat} (x : BitVec m) : Int := x.toNat
@[simp]
def sbv_to_int {m : Nat} (x : BitVec m) : Int := x.toInt
@[simp]
def int_to_bv (m : Nat) (x : Int) : BitVec m := BitVec.ofInt m x

@[simp]
def bvnand {m : Nat} (x y : BitVec m) : BitVec m := ~~~(x &&& y)
@[simp]
def bvnor {m : Nat} (x y : BitVec m) : BitVec m := ~~~(x ||| y)
@[simp]
def bvxor {m : Nat} (x y : BitVec m) : BitVec m := x ^^^ y
@[simp]
def bvxnor {m : Nat} (x y : BitVec m) : BitVec m := ~~~(x ^^^ y)
@[simp]
def bvcomp {m : Nat} (x y : BitVec m) : BitVec 1 := if x = y then BitVec.ofNat 1 1 else BitVec.ofNat 1 0
@[simp]
def bvsub {m : Nat} (x y : BitVec m) : BitVec m := x - y
@[simp]
def bvsdiv {m : Nat} (x y : BitVec m) : BitVec m := BitVec.sdiv x y
@[simp]
def bvsrem {m : Nat} (x y : BitVec m) : BitVec m := BitVec.srem x y
@[simp]
def bvsmod {m : Nat} (x y : BitVec m) : BitVec m := BitVec.smod x y
@[simp]
def bvashr {m : Nat} (x y : BitVec m) : BitVec m := BitVec.sshiftRight x y.toNat

@[simp]
def bvusubo {m : Nat} (x y : BitVec m) : Prop := x.toNat < y.toNat
@[simp]
def bvssubo {m : Nat} (x y : BitVec m) : Prop :=
  let sx := x.toInt
  let sy := y.toInt
  let r  := sx - sy
  let min : Int := -(2 : Int) ^ (m - 1)
  let max : Int := (2 : Int) ^ (m - 1) - 1
  r < min ∨ r > max
@[simp]
def bvsdivo {m : Nat} (x y : BitVec m) : Prop :=
  x.toInt = -(2 : Int) ^ (m - 1) ∧ y.toInt = -1

@[simp]
def re_peat {m : Nat} (i : Nat) (hi : i ≥ 1) (x : BitVec m) : BitVec (i * m) :=
  match i with
  | 0 => False.elim (by omega)
  | 1 => by
      simpa
  | n + 2 =>
      cast
        (by rw [← Nat.add_one_mul])
        (concat (re_peat (n + 1) (by omega) x) x)

@[simp]
def zero_extend {m : Nat} (i : Nat) (x : BitVec m) : BitVec (m + i) :=
  cast (by simp [Nat.add_comm]) (concat (BitVec.ofNat i 0) x)

@[simp]
def sign_extend {m : Nat} (i : Nat) (x : BitVec m) : BitVec (m + i) :=
  .ofInt (m + i) x.toInt

@[simp]
def rotate_left {m : Nat} (i : Nat) (x : BitVec m) : BitVec m :=
  if h : m = 0 then
    cast (by simp [h]) x
  else
    let k := i % m
    if hk : k = 0 then
      x
    else
      cast
        (by simp?
        )
        (concat
          (extract (m - k - 1) 0 x)
          (extract (m - 1) (m - k) x))

@[simp]
def rotate_right {m : Nat} (i : Nat) (x : BitVec m) : BitVec m :=
  if h : m = 0 then
    cast (by simp [h]) x
  else
    let k := i % m
    if hk : k = 0 then
      x
    else
      cast
        (by sorry)
        (concat
          (extract (k - 1) 0 x)
          (extract (m - 1) k x))

@[simp]
def bvule {m : Nat} (x y : BitVec m) : Prop := x.toNat ≤ y.toNat
@[simp]
def bvugt {m : Nat} (x y : BitVec m) : Prop := x.toNat > y.toNat
@[simp]
def bvuge {m : Nat} (x y : BitVec m) : Prop := x.toNat ≥ y.toNat

@[simp]
def bvslt {m : Nat} (x y : BitVec m) : Prop := x.toInt < y.toInt
@[simp]
def bvsle {m : Nat} (x y : BitVec m) : Prop := x.toInt ≤ y.toInt
@[simp]
def bvsgt {m : Nat} (x y : BitVec m) : Prop := x.toInt > y.toInt
@[simp]
def bvsge {m : Nat} (x y : BitVec m) : Prop := x.toInt ≥ y.toInt

@[simp]
def bvconst (x : Nat) (n : Nat) : BitVec n :=
  BitVec.ofNat n x

@[simp]
def bvzero {m : Nat} : BitVec m := BitVec.ofNat m 0

@[simp]
def msb {m : Nat} (s : BitVec m) : BitVec 1 :=
  (extract (m - 1) (m - 1) s).cast (by simp)

@[simp]
def msb0 {m : Nat} (s : BitVec m) : Prop := msb (m := m) s = BitVec.ofNat 1 0
@[simp]
def msb1 {m : Nat} (s : BitVec m) : Prop := msb (m := m) s = BitVec.ofNat 1 1


end SMT


example (m i : ℕ) (x : BitVec m) (h : ¬m = 0) (k : ℕ := i % m) (hk : ¬k = 0) :
  m - k - 1 + 1 + (m - 1 - (m - k) + 1) = m := by
