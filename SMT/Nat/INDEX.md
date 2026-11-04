# SMT.Nat 声明索引

所有声明都在 `SMT.Nat` 命名空间。每个文件可单独 import；
模块依赖和来源说明见 [UPSTREAM.md](../../UPSTREAM.md)。

## [And](And.lean)

`import SMT.Nat.And`

| 声明 | 种类 |
| --- | --- |
| `testBit_and` | theorem |
| `and_self` | theorem |
| `and_comm` | theorem |
| `and_assoc` | theorem |
| `and_lt_two_pow` | theorem |
| `and_two_pow_sub_one_eq_mod` | theorem |
| `and_two_pow_sub_one_of_lt_two_pow` | theorem |
| `and_mod_two_eq_one` | theorem |
| `and_div_two_pow` | theorem |
| `and_div_two` | theorem |
| `and_mod_two_pow` | theorem |

## [Arithmetic](Arithmetic.lean)

`import SMT.Nat.Arithmetic`

| 声明 | 种类 |
| --- | --- |
| `testBit_two_pow_mul_add` | theorem |
| `testBit_two_pow_mul` | theorem |
| `testBit_mul_two_pow` | theorem |
| `two_pow_add_eq_or_of_lt` | theorem |
| `or_two_pow_eq_add_of_lt` | theorem |

## [Basic](Basic.lean)

`import SMT.Nat.Basic`

| 声明 | 种类 |
| --- | --- |
| `two_pow_succ_sub_succ_div_two` | theorem |
| `two_pow_succ_sub_one_div_two` | theorem |
| `two_mul_sub_one` | theorem |
| `div2Induction` | def |
| `zero_and` | theorem |
| `and_zero` | theorem |
| `one_and_eq_mod_two` | theorem |
| `and_one_is_mod` | theorem |

## [Bitwise](Bitwise.lean)

`import SMT.Nat.Bitwise`

| 声明 | 种类 |
| --- | --- |
| `testBit_bitwise` | theorem |
| `eq_0_of_lt_one` | theorem |
| `eq_0_of_lt` | theorem |
| `zero_lt_pow` | theorem |
| `div_two_le_of_lt_two` | theorem |
| `bitwise_lt_two_pow` | theorem |
| `bitwise_div_two_pow` | theorem |
| `bitwise_mod_two_pow` | theorem |

## [Mathlib](Mathlib.lean)

`import SMT.Nat.Mathlib`

| 声明 | 种类 |
| --- | --- |
| `bitwise_zero_left` | theorem |
| `bitwise_zero_right` | theorem |
| `bitwise_zero` | theorem |
| `testBit_lor` | theorem |
| `testBit_land` | theorem |
| `zero_of_testBit_eq_false` | theorem |
| `testBit_eq_false_of_lt` | theorem |
| `lor_comm` | theorem |
| `land_comm` | theorem |
| `land_assoc` | theorem |
| `lor_assoc` | theorem |
| `and_two_pow` | theorem |
| `two_pow_and` | theorem |
| `shiftLeft_lt` | theorem |
| `append_lt` | theorem |
| `xor_mod_two_eq` | theorem |
| `div2` | def |
| `bodd` | def |
| `ldiff` | def |
| `div2_val` | theorem |
| `div2_zero` | theorem |
| `div2_one` | theorem |
| `div2_two` | theorem |
| `bodd_zero` | theorem |
| `bodd_one` | theorem |
| `bodd_two` | theorem |
| `mod_two_of_bodd` | theorem |
| `bodd_succ` | theorem |
| `bodd_add` | theorem |
| `bodd_mul` | theorem |
| `bodd_add_div2` | theorem |
| `testBit_ldiff` | theorem |

## [Modular](Modular.lean)

`import SMT.Nat.Modular`

| 声明 | 种类 |
| --- | --- |
| `truncate` | abbrev |
| `mask` | abbrev |
| `truncate_lt` | theorem |
| `truncate_of_lt` | theorem |
| `truncate_idem` | theorem |
| `truncate_add` | theorem |
| `truncate_mul` | theorem |
| `and_mask` | theorem |
| `truncate_truncate` | theorem |
| `truncate_sub_of_le` | theorem |

## [Or](Or.lean)

`import SMT.Nat.Or`

| 声明 | 种类 |
| --- | --- |
| `zero_or` | theorem |
| `or_zero` | theorem |
| `testBit_or` | theorem |
| `or_self` | theorem |
| `or_comm` | theorem |
| `or_assoc` | theorem |
| `and_or_distrib_left` | theorem |
| `and_or_distrib_right` | theorem |
| `or_and_distrib_left` | theorem |
| `or_and_distrib_right` | theorem |
| `or_lt_two_pow` | theorem |
| `or_mod_two_eq_one` | theorem |
| `or_div_two_pow` | theorem |
| `or_div_two` | theorem |
| `or_mod_two_pow` | theorem |
| `or_eq_zero_iff` | theorem |
| `or_pos_iff` | theorem |

## [Order](Order.lean)

`import SMT.Nat.Order`

| 声明 | 种类 |
| --- | --- |
| `le_of_testBit` | theorem |
| `and_le_left` | theorem |
| `and_le_right` | theorem |
| `left_le_or` | theorem |
| `right_le_or` | theorem |

## [Shift](Shift.lean)

`import SMT.Nat.Shift`

| 声明 | 种类 |
| --- | --- |
| `testBit_shiftLeft` | theorem |
| `testBit_shiftRight` | theorem |
| `shiftLeft_mod_two_eq_one` | theorem |
| `bitwise_mul_two_pow` | theorem |
| `shiftLeft_bitwise_distrib` | theorem |
| `shiftLeft_and_distrib` | theorem |
| `shiftLeft_or_distrib` | theorem |
| `shiftLeft_xor_distrib` | theorem |
| `decide_shiftRight_mod_two_eq_one` | theorem |
| `shiftRight_bitwise_distrib` | theorem |
| `shiftRight_and_distrib` | theorem |
| `shiftRight_or_distrib` | theorem |
| `shiftRight_xor_distrib` | theorem |
| `mod_two_pow_shiftLeft_mod_two_pow` | theorem |
| `le_shiftLeft` | theorem |
| `lt_of_shiftLeft_lt` | theorem |
| `shiftLeft_add_eq_or_of_lt` | theorem |
| `shiftLeft_eq_zero_iff` | theorem |
| `shiftLeft_pos_iff` | theorem |

## [TestBit](TestBit.lean)

`import SMT.Nat.TestBit`

| 声明 | 种类 |
| --- | --- |
| `zero_testBit` | theorem |
| `testBit_zero` | theorem |
| `mod_two_eq_one_iff_testBit_zero` | theorem |
| `mod_two_eq_zero_iff_testBit_zero` | theorem |
| `testBit_succ` | theorem |
| `testBit_add_one` | theorem |
| `testBit_add` | theorem |
| `testBit_div_two` | theorem |
| `testBit_div_two_pow` | theorem |
| `testBit_eq_decide_div_mod_eq` | theorem |
| `toNat_testBit` | theorem |
| `exists_testBit_of_ne_zero` | theorem |
| `exists_testBit_ne_of_ne` | theorem |
| `eq_of_testBit_eq` | theorem |
| `eq_iff_testBit_eq` | theorem |
| `exists_ge_and_testBit_of_ge_two_pow` | theorem |
| `ge_two_pow_of_testBit` | theorem |
| `testBit_lt_two_pow` | theorem |
| `testBit_of_two_pow_le_and_two_pow_add_one_gt` | theorem |
| `lt_pow_two_of_testBit` | theorem |
| `testBit_log2` | theorem |
| `succ_mod_two` | theorem |
| `testBit_succ_zero` | theorem |
| `testBit_two_pow_add_eq` | theorem |
| `testBit_mul_two_pow_add_eq` | theorem |
| `testBit_two_pow_add_gt` | theorem |
| `testBit_mod_two_pow` | theorem |
| `testBit_one_zero` | theorem |
| `not_decide_mod_two_eq_one` | theorem |
| `testBit_two_pow_sub_succ` | theorem |
| `testBit_two_pow_sub_one` | theorem |
| `testBit_bool_toNat` | theorem |
| `testBit_one_eq_true_iff_self_eq_zero` | theorem |
| `testBit_two_pow` | theorem |
| `testBit_two_pow_self` | theorem |
| `testBit_two_pow_of_ne` | theorem |
| `two_pow_sub_one_mod_two` | theorem |
| `mod_two_pos_mod_two_eq_one` | theorem |

## [Xor](Xor.lean)

`import SMT.Nat.Xor`

| 声明 | 种类 |
| --- | --- |
| `testBit_xor` | theorem |
| `zero_xor` | theorem |
| `xor_zero` | theorem |
| `xor_self` | theorem |
| `xor_comm` | theorem |
| `xor_assoc` | theorem |
| `xor_lt_two_pow` | theorem |
| `and_xor_distrib_right` | theorem |
| `and_xor_distrib_left` | theorem |
| `xor_mod_two_eq_one` | theorem |
| `xor_div_two_pow` | theorem |
| `xor_div_two` | theorem |
| `xor_mod_two_pow` | theorem |
