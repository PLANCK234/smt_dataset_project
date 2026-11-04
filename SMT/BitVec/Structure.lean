module
prelude

public import SMT.BitVec.Basic

@[expose] public section

namespace SMT.BitVec

/-- SMT `concat`: x supplies high bits, y low bits, with U(result)=U(x)*2^n+U(y).
Uses Lean append (Lean's differently named concat appends only one Bool). -/
abbrev concat {m n : Nat} (x : _root_.BitVec m) (y : _root_.BitVec n) :
    _root_.BitVec (m + n) := x ++ y
/-- SMT `(_ extract hi lo)`: U(result)=floor(U(x)/2^lo) mod 2^(hi-lo+1).
The frontend checks lo ≤ hi < n; the resulting width is hi-lo+1. -/
abbrev extract (hi lo : Nat) {n : Nat} (x : _root_.BitVec n) :
    _root_.BitVec (hi - lo + 1) := x.extractLsb hi lo
/-- SMT `(_ zero_extend extra)`: adds extra high zero bits, preserving U(x).
The result width is n+extra; zero extra bits is the identity. -/
abbrev zeroExtend (extra : Nat) {n : Nat} (x : _root_.BitVec n) :
    _root_.BitVec (n + extra) := x.setWidth (n + extra)
/-- SMT `(_ sign_extend extra)`: adds extra copies of the sign bit, preserving S(x).
The result width is n+extra and the SMT domain requires n > 0. -/
abbrev signExtend (extra : Nat) {n : Nat} (x : _root_.BitVec n) :
    _root_.BitVec (n + extra) := x.signExtend (n + extra)
/-- SMT `(_ repeat count)`: concatenates count copies of x; bit i is x[i mod n].
The source requires count > 0. The public result type uses n*count, equal to count*n. -/
abbrev «repeat» (count : Nat) {n : Nat} (x : _root_.BitVec n) :
    _root_.BitVec (n * count) := x.replicate count
/-- SMT `(_ rotate_left count)`: output bit i is input bit (i+n-count%n)%n.
Counts are natural numeral indices, periodic modulo the positive width n. -/
abbrev rotateLeft (count : Nat) {n : Nat} (x : _root_.BitVec n) :
    _root_.BitVec n := x.rotateLeft count
/-- SMT `(_ rotate_right count)`: output bit i is input bit (i+count%n)%n.
Counts are natural numeral indices, periodic modulo the positive width n. -/
abbrev rotateRight (count : Nat) {n : Nat} (x : _root_.BitVec n) :
    _root_.BitVec n := x.rotateRight count

/-- PBV `(pextract hi lo x)`: U(result)=floor(U(x)/2^lo) mod 2^(hi-lo+1).
The argument order follows the PBV benchmark syntax. Indices may be symbolic;
the valid source domain requires 0 ≤ lo ≤ hi < n. Lean Nat represents the
nonnegative indices, and the semantic theorem records the remaining bounds. -/
abbrev pextract (hi lo : Nat) {n : Nat} (x : _root_.BitVec n) :
    _root_.BitVec (hi - lo + 1) := extract hi lo x
/-- PBV `(pzero_extend extra x)`: adds extra high zero bits, preserving U(x).
The result width is n+extra, not extra. The source requires n > 0 and extra ≥ 0;
the symbolic extra argument is represented by Lean Nat. -/
abbrev pzero_extend (extra : Nat) {n : Nat} (x : _root_.BitVec n) :
    _root_.BitVec (n + extra) := zeroExtend extra x
/-- PBV `(psign_extend extra x)`: adds extra copies of the sign bit, preserving S(x).
The result width is n+extra, not extra. The source requires n > 0 and extra ≥ 0;
the symbolic extra argument is represented by Lean Nat. -/
abbrev psign_extend (extra : Nat) {n : Nat} (x : _root_.BitVec n) :
    _root_.BitVec (n + extra) := signExtend extra x

end SMT.BitVec
