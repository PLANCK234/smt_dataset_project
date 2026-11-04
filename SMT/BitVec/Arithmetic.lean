module
prelude

public import SMT.BitVec.Basic

@[expose] public section

namespace SMT.BitVec

/-- SMT `bvneg`: N_n(-U(x)). Negating the signed minimum preserves its bit pattern. -/
abbrev bvneg {n : Nat} (x : _root_.BitVec n) : _root_.BitVec n := -x
/-- SMT `bvadd`: N_n(U(x)+U(y)); overflow wraps modulo 2^n. -/
abbrev bvadd {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := x + y
/-- SMT `bvsub`: N_n(U(x)-U(y)); underflow wraps modulo 2^n. -/
abbrev bvsub {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := x - y
/-- SMT `bvmul`: N_n(U(x)*U(y)); overflow wraps modulo 2^n. -/
abbrev bvmul {n : Nat} (x y : _root_.BitVec n) : _root_.BitVec n := x * y

end SMT.BitVec
