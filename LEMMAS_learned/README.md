# 学习得到的数学引理

94 条通用引理按数学对象与运算主题组织。命名空间是 `Learned.Nat`、`Learned.BitVec`，运算仍使用 `SMT.BitVec` 的定义。
只依赖原始 `SMT` 与 Lean Init；不导入 benchmark，不向原始库回写声明。

## 模块

可按需 `import LEMMAS_learned.<下表主题>`，或使用 `LEMMAS_learned.Nat`、`LEMMAS_learned.BitVec` 汇总入口。

| 主题 | 内容 | 引理数 |
| --- | --- | ---: |
| [BitVec.Arithmetic](BitVec/Arithmetic.lean) | AND/OR 分解、掩码减法、最低有效位 | 7 |
| [BitVec.Bitwise](BitVec/Bitwise.lean) | 补码、吸收律、不相交位的无进位算术 | 12 |
| [BitVec.Shift.Basic](BitVec/Shift/Basic.lean) | 移位分配律、清零条件、低高位分离与往返掩码 | 22 |
| [BitVec.Shift.Bounds](BitVec/Shift/Bounds.lean) | 整除性、数值界、组合移位及无回绕加法 | 13 |
| [BitVec.Shift.Carry](BitVec/Shift/Carry.lean) | 低位不受高位加法影响；倍增与进位掩码 | 9 |
| [BitVec.Shift.Characterization](BitVec/Shift/Characterization.lean) | 逐输入左右移位整除充要条件、掩码对偶、最高位障碍 | 3 |
| [BitVec.Shift.Conditions](BitVec/Shift/Conditions.lean) | 清零整除判据、统一左右移位条件、条件掩码规律 | 9 |
| [BitVec.Shift.Quotient](BitVec/Shift/Quotient.lean) | 右移商的取反/取负界和全 1 掩码移位界 | 5 |
| [BitVec.Shift.Self](BitVec/Shift/Self.lean) | 自移位的取负和补码结果的位宽下界 | 2 |
| [Nat.Bitwise](Nat/Bitwise.lean) | 无进位 OR=加法；低位掩码只依赖对应模余数 | 2 |
| [Nat.Div](Nat/Div.lean) | 二幂除法的商界；整除减法的商 | 3 |
| [Nat.Mod](Nat/Mod.lean) | 指定余数与减去余数后的整除等价 | 1 |
| [Nat.Pow](Nat/Pow.lean) | 线性、平方与二次幂的上下界 | 5 |
| [Nat.Shift](Nat/Shift.lean) | 二幂位宽下，自移位非零的整除界 | 1 |

## 保留标准

保留可独立表述的代数规律、数值界、位掩码性质和精确充要条件，以及这些规律共用的辅助引理。引用次数不是唯一标准：一个只用过一次的通用整除等价仍值得保留。

已检查此前写回的 191 条引理：94 条保留；89 条仅为特定嵌套表达式服务，其证明放回使用它们的 benchmark，作为文件内私有辅助步骤；8 条未使用、可由通用规则立即推出的推论删除。
例如第 234 条的最终等式留在其 benchmark 中，通用的 `width_le_toNat_bvneg_bvshl_self` 下界留在 `Shift.Self`。
纯 Nat 的 `two_mul_le_two_pow` 从 BV 移位文件归入 `Nat.Pow`。

新引理应先说明独立数学内容与适用边界，包含零位宽时需在证明中覆盖。专用重写组合留在 benchmark；不因一个证明需要一句 `rw` 就扩充公开 API。
文件头与 `upstream.json` 标注本地推导及固定上游依据，详情见 [来源规范](../UPSTREAM.md)。
