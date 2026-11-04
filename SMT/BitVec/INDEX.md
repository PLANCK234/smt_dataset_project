# BV / PBV 运算索引

全部 51 个当前公开运算及其数学桥接。命名空间均为 `SMT.BitVec`。
符号宽度使用、依赖和来源规范见 [UPSTREAM.md](../../UPSTREAM.md)。

Bool 结果的桥接名通常为 `*_toNat`；BV 结果为 `toNat_*`。
有符号运算通过 `signedValue` 使用 Int，不会丢弃符号。

## Basic

按需导入 `SMT.BitVec.ToNat.Basic`。

| 运算 | 桥接定理 |
| --- | --- |
| [`literal`](Basic.lean) | [`toNat_literal`](ToNat/Basic.lean) |

## Arithmetic

按需导入 `SMT.BitVec.ToNat.Arithmetic`。

| 运算 | 桥接定理 |
| --- | --- |
| [`bvneg`](Arithmetic.lean) | [`toNat_bvneg`](ToNat/Arithmetic.lean) |
| [`bvadd`](Arithmetic.lean) | [`toNat_bvadd`](ToNat/Arithmetic.lean) |
| [`bvsub`](Arithmetic.lean) | [`toNat_bvsub`](ToNat/Arithmetic.lean) |
| [`bvmul`](Arithmetic.lean) | [`toNat_bvmul`](ToNat/Arithmetic.lean) |

## Bitwise

按需导入 `SMT.BitVec.ToNat.Bitwise`。

| 运算 | 桥接定理 |
| --- | --- |
| [`bvnot`](Bitwise.lean) | [`toNat_bvnot`](ToNat/Bitwise.lean) |
| [`bvand`](Bitwise.lean) | [`toNat_bvand`](ToNat/Bitwise.lean) |
| [`bvor`](Bitwise.lean) | [`toNat_bvor`](ToNat/Bitwise.lean) |
| [`bvxor`](Bitwise.lean) | [`toNat_bvxor`](ToNat/Bitwise.lean) |
| [`bvnand`](Bitwise.lean) | [`toNat_bvnand`](ToNat/Bitwise.lean) |
| [`bvnor`](Bitwise.lean) | [`toNat_bvnor`](ToNat/Bitwise.lean) |
| [`bvxnor`](Bitwise.lean) | [`toNat_bvxnor`](ToNat/Bitwise.lean) |
| [`bvcomp`](Bitwise.lean) | [`toNat_bvcomp`](ToNat/Bitwise.lean) |

## Division

按需导入 `SMT.BitVec.ToNat.Division`。

| 运算 | 桥接定理 |
| --- | --- |
| [`bvudiv`](Division.lean) | [`toNat_bvudiv`](ToNat/Division.lean) |
| [`bvurem`](Division.lean) | [`toNat_bvurem`](ToNat/Division.lean) |
| [`bvsdiv`](Division.lean) | [`toNat_bvsdiv`](ToNat/Division.lean) |
| [`bvsrem`](Division.lean) | [`toNat_bvsrem`](ToNat/Division.lean) |
| [`bvsmod`](Division.lean) | [`toNat_bvsmod`](ToNat/Division.lean) |

## Shift

按需导入 `SMT.BitVec.ToNat.Shift`。

| 运算 | 桥接定理 |
| --- | --- |
| [`bvshl`](Shift.lean) | [`toNat_bvshl`](ToNat/Shift.lean) |
| [`bvlshr`](Shift.lean) | [`toNat_bvlshr`](ToNat/Shift.lean) |
| [`bvashr`](Shift.lean) | [`toNat_bvashr`](ToNat/Shift.lean) |

## Structure

按需导入 `SMT.BitVec.ToNat.Structure`。

| 运算 | 桥接定理 |
| --- | --- |
| [`concat`](Structure.lean) | [`toNat_concat`](ToNat/Structure.lean) |
| [`extract`](Structure.lean) | [`toNat_extract`](ToNat/Structure.lean) |
| [`zeroExtend`](Structure.lean) | [`toNat_zeroExtend`](ToNat/Structure.lean) |
| [`signExtend`](Structure.lean) | [`toNat_signExtend`](ToNat/Structure.lean) |
| [`repeat`](Structure.lean) | [`toNat_repeat`](ToNat/Structure.lean) |
| [`rotateLeft`](Structure.lean) | [`toNat_rotateLeft`](ToNat/Structure.lean) |
| [`rotateRight`](Structure.lean) | [`toNat_rotateRight`](ToNat/Structure.lean) |
| [`pextract`](Structure.lean) | [`toNat_pextract`](ToNat/Structure.lean) |
| [`pzero_extend`](Structure.lean) | [`toNat_pzero_extend`](ToNat/Structure.lean) |
| [`psign_extend`](Structure.lean) | [`toNat_psign_extend`](ToNat/Structure.lean) |

## Comparison

按需导入 `SMT.BitVec.ToNat.Comparison`。

| 运算 | 桥接定理 |
| --- | --- |
| [`bvult`](Comparison.lean) | [`bvult_toNat`](ToNat/Comparison.lean) |
| [`bvule`](Comparison.lean) | [`bvule_toNat`](ToNat/Comparison.lean) |
| [`bvugt`](Comparison.lean) | [`bvugt_toNat`](ToNat/Comparison.lean) |
| [`bvuge`](Comparison.lean) | [`bvuge_toNat`](ToNat/Comparison.lean) |
| [`bvslt`](Comparison.lean) | [`bvslt_toNat`](ToNat/Comparison.lean) |
| [`bvsle`](Comparison.lean) | [`bvsle_toNat`](ToNat/Comparison.lean) |
| [`bvsgt`](Comparison.lean) | [`bvsgt_toNat`](ToNat/Comparison.lean) |
| [`bvsge`](Comparison.lean) | [`bvsge_toNat`](ToNat/Comparison.lean) |

## Overflow

按需导入 `SMT.BitVec.ToNat.Overflow`。

| 运算 | 桥接定理 |
| --- | --- |
| [`bvnego`](Overflow.lean) | [`bvnego_toNat`](ToNat/Overflow.lean) |
| [`bvuaddo`](Overflow.lean) | [`bvuaddo_toNat`](ToNat/Overflow.lean) |
| [`bvsaddo`](Overflow.lean) | [`bvsaddo_toNat`](ToNat/Overflow.lean) |
| [`bvusubo`](Overflow.lean) | [`bvusubo_toNat`](ToNat/Overflow.lean) |
| [`bvssubo`](Overflow.lean) | [`bvssubo_toNat`](ToNat/Overflow.lean) |
| [`bvumulo`](Overflow.lean) | [`bvumulo_toNat`](ToNat/Overflow.lean) |
| [`bvsmulo`](Overflow.lean) | [`bvsmulo_toNat`](ToNat/Overflow.lean) |
| [`bvsdivo`](Overflow.lean) | [`bvsdivo_toNat`](ToNat/Overflow.lean) |

## Conversion

按需导入 `SMT.BitVec.ToNat.Conversion`。

| 运算 | 桥接定理 |
| --- | --- |
| [`ubv_to_int`](Conversion.lean) | [`ubv_to_int_toNat`](ToNat/Conversion.lean) |
| [`sbv_to_int`](Conversion.lean) | [`sbv_to_int_toNat`](ToNat/Conversion.lean) |
| [`int_to_bv`](Conversion.lean) | [`toNat_int_to_bv`](ToNat/Conversion.lean) |
| [`int_to_pbv`](Conversion.lean) | [`toNat_int_to_pbv`](ToNat/Conversion.lean) |

## 重写规则

按需 import 以下模块，使用 `rw` 或 `simp only`。

### [Rewrite.Arithmetic](Rewrite/Arithmetic.lean)

`bvadd_comm`, `bvadd_assoc`, `bvmul_comm`, `bvmul_assoc`, `bvadd_zero`, `zero_bvadd`, `bvmul_zero`, `zero_bvmul`, `bvmul_one`, `one_bvmul`, `bvsub_zero`, `bvsub_self`, `bvneg_bvneg`, `bvadd_bvneg`, `bvsub_eq_bvadd_bvneg`, `bvadd_bvsub_cancel`, `bvmul_bvadd`, `bvadd_bvmul`

### [Rewrite.Bitwise](Rewrite/Bitwise.lean)

`bvand_comm`, `bvand_assoc`, `bvor_comm`, `bvor_assoc`, `bvxor_comm`, `bvxor_assoc`, `bvand_self`, `bvor_self`, `bvxor_self`, `bvand_zero`, `bvor_zero`, `bvxor_zero`, `bvnot_bvnot`, `bvand_bvnot`, `bvnot_bvand`, `bvnot_bvor`, `bvand_bvor`, `bvnand_eq`, `bvnor_eq`, `bvxnor_eq`, `bvcomp_self`

### [Rewrite.Comparison](Rewrite/Comparison.lean)

`bvult_self`, `bvugt_self`, `bvslt_self`, `bvsgt_self`, `bvule_self`, `bvuge_self`, `bvsle_self`, `bvsge_self`, `bvugt_eq`, `bvuge_eq`, `bvsgt_eq`, `bvsge_eq`

### [Rewrite.Conversion](Rewrite/Conversion.lean)

`int_to_pbv_unsigned_roundtrip`, `int_to_pbv_signed_roundtrip`

### [Rewrite.Division](Rewrite/Division.lean)

`bvudiv_one`, `bvurem_one`, `bvurem_self`, `bvsrem_self`, `bvsmod_self`

### [Rewrite.Shift](Rewrite/Shift.lean)

`bvshl_zero`, `bvshl_large`, `bvlshr_zero`, `bvashr_zero`, `bvshl_bvand`, `bvshl_bvor`, `bvshl_bvxor`

### [Rewrite.Structure](Rewrite/Structure.lean)

`zeroExtend_zero`, `signExtend_zero`, `pzero_extend_zero`, `psign_extend_zero`, `zeroExtend_bvand`, `signExtend_bvand`, `zeroExtend_bvor`, `signExtend_bvor`, `zeroExtend_bvxor`, `signExtend_bvxor`

## Nat 辅助库

Nat 位测试、位运算、掩码和数值辅助定理见 [SMT.Nat 索引](../Nat/INDEX.md)。
