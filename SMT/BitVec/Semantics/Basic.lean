module
prelude

public import SMT.BitVec.Model
public import SMT.BitVec.Basic
public import Init.Data.BitVec.Lemmas

/-! Basic semantic contracts, split from SMT.BitVec.Semantics.
Public theorem names and statements are preserved. -/
@[expose] public section

namespace SMT.BitVec

theorem literal_semantics (n v : Nat) : toUnsigned (literal n v) = v % 2 ^ n := rfl

end SMT.BitVec
