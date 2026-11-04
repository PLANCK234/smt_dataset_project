# 数学库的来源、语义与依赖

`SMT/` 保存基础库：51 个 BV/PBV 运算的数学契约、`toNat` 桥接、基础重写，以及抽取到本地的 Nat 位运算证明。`LEMMAS_learned/` 保存独立命名空间下的本地推导，基础库不反向依赖它。
Mathlib 的选定证明已抽取、改写到本地；构建不安装或 import Mathlib、Batteries。Lean 的类型、算术及证明设施来自固定工具链的 `Init`。

## 入口与使用

- [BV 运算索引](SMT/BitVec/INDEX.md)：`SMT.BitVec.Semantics`、`SMT.BitVec.ToNat`、`SMT.BitVec.Rewrite` 按运算类别拆分；`SMT.BitVec.Lemmas` 是基础数学汇总入口。
- [Nat 索引](SMT/Nat/INDEX.md)：二进制归纳、位测试、AND/OR/XOR、移位、顺序和模运算。`SMT.Nat.Mathlib` 是本地文件名。
- [学习库](LEMMAS_learned/README.md)：位掩码、无进位算术、数值界、移位整除及充要条件；按需导入对应主题。

```lean
import LEMMAS_learned.BitVec.Shift.Conditions

example (x y : BitVec n) :
    SMT.BitVec.bvshl x y = SMT.BitVec.literal n 0 ↔
      2 ^ n ∣ x.toNat * 2 ^ y.toNat :=
  Learned.BitVec.bvshl_eq_zero_iff_dvd x y
```

BV 的交换律和桥接等式不自动注册为全局 `[simp]`；用 `rw [...]` 或 `simp only [...]` 选择方向。
Nat 抽取定理保留适用的 `[simp]`、`[grind]` 属性。`SMT.Normalize` 的归一化属性和 `SMT.QFBV` 的 SAT 战术是可选入口，数学模块不加载 SAT 引擎。

## 数学语义边界

- 无符号运算保留模 `2^n`；BV 减法不是 Nat 的截断减法，取反有有限位宽。
- 有符号比较、除余、溢出通过 `signedValue : Int` 表达；负结果先取模再转 Nat。
- `bvudiv`、`bvsdiv` 保留 SMT 除零行为；`bvsrem` 使用 `Int.tmod`，`bvsmod` 使用 `Int.fmod`。算术右移保留符号填充。
- 移位量使用全部无符号数值，旋转量按宽度取模。Lean 的 `BitVec 0` 合法；定理仅在明确声明时要求正宽度或合法下标。

PBV 的四个接口沿用原始参数顺序：`int_to_pbv n z`、`pextract hi lo x`、`pzero_extend extra x`、`psign_extend extra x`。
它们分别表示整数模 `2^n`、除以 `2^lo` 后保留 `hi-lo+1` 位、零扩展、符号扩展；`extra` 表示增加的位数。
有效 PBV 语义要求正宽度、非负扩展量及 `lo ≤ hi < n`。源文件的 Int 宽度约束必须先证明再转成 Nat，尤其不能直接把整数减法替换为 Nat 截断减法。
无条件总函数等式不声称 SMT-LIB 允许零宽度或非法提取范围。词表中的变量、注释、命令不作为新运算。

## 固定来源与标注

| 上游 | 固定版本 / commit | 抽取或适配范围 |
| --- | --- | --- |
| [Lean](https://github.com/leanprover/lean4/tree/5045d0056413266e57c625dcd7c365b10e377c52) | v4.34.1 / `5045d0056413266e57c625dcd7c365b10e377c52` | Init BV API 适配、Nat 位运算证明拆分 |
| [Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612) | v4.34.1 / `d13f23b723b8a846827a245b89c10fc7d3f11612` | BV 单射性与 Nat 数值、位运算定理 |

不整体引入 Mathlib 的 CommRing、ZMod、列表二进制表示和泛型代数层。抽取证明改为本地命名空间及 Init 证明设施；不是上游全部 BitVec 定理的镜像。

文件头区分上游适配与本地推导。[upstream.json](upstream.json) 记录固定 revision、源文件 SHA-256、声明及行号。
学习库条目标记为本地推导；`upstream` 列的是可识别的上游依据，不表示整个证明是逐字复制。
原始版权和作者信息保存在 [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md)，完整许可证在 [Apache-2.0.txt](THIRD_PARTY_LICENSES/Apache-2.0.txt)。

## 维护

`lake-manifest.json` 的外部 packages 为空。数学模块使用 `module`、`prelude` 和显式小模块导入。
`audit_library.py` 检查运算覆盖、来源索引、工具链哈希、分层依赖和编译后公理；它报告真实 import 闭包，不声称形式化证明了全局最小依赖。

更新声明位置或来源索引时，提供固定版本的 Mathlib 源文件目录：

```sh
python3 scripts/update_upstream.py --mathlib-source /path/to/pinned-mathlib
```

此命令校验已有源文件哈希，更新索引和 notices，不安装依赖、不修改数学证明。
