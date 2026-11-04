/-
Copyright (c) 2023-2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0; see THIRD_PARTY_LICENSES/Apache-2.0.txt.
Adapted from Lean v4.34.1, Init/Data/BitVec/Lemmas.lean.
Changes: statements use the SMT public API; proof dependencies remain in Init.
The exact upstream declarations are recorded in upstream.json.
-/
module
prelude

public import SMT.BitVec.Conversion
public import Init.Data.BitVec.Lemmas
public import SMT.BitVec.Semantics.Conversion

@[expose] public section

namespace SMT.BitVec


theorem int_to_pbv_unsigned_roundtrip (x : _root_.BitVec n) : int_to_pbv n (ubv_to_int x) = x := by
  simp [int_to_pbv, int_to_bv, ubv_to_int]
theorem int_to_pbv_signed_roundtrip (x : _root_.BitVec n) : int_to_pbv n (sbv_to_int x) = x :=
  _root_.BitVec.ofInt_toInt

end SMT.BitVec
