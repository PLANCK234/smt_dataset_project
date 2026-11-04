module
prelude

public import Init.Data.BitVec.Basic

@[expose] public section

namespace SMT.BitVec

/-- SMT binary, hexadecimal, or indexed decimal literal with checked width n > 0:
returns the bit pattern of v modulo 2^n. The frontend additionally checks indexed
decimal literals satisfy v < 2^n and derives binary/hex widths from all digits. -/
abbrev literal (n v : Nat) : _root_.BitVec n := _root_.BitVec.ofNat n v

end SMT.BitVec
