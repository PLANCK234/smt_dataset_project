# 19 条规则的充要条件

每个反例规则文件包含两个双向定理：

- `bv_term_small_rw_ID_iff`：给定 n、s、t 时，原等式 **当且仅当** 输入条件成立。
- `bv_term_small_rw_ID_width_iff`：给定 n 时，原等式对 **所有 s、t** 成立 **当且仅当** 位宽条件成立。

共 38 条 `↔`，均证明了正反两个方向，没有用之前的充分条件冒充必要条件。
文件位于 `unsat/bv_term_small_rw_ID.lean`。原反例和有用的充分条件推论也保留。

**量词必须区分**：例如 `n≠1` 是 1246 对所有输入成立的精确位宽条件；
对于一个给定输入，`n=1,s=0` 仍成立。因此同一文件的输入条件与位宽条件并不相同。

## 记号与四个输入谓词

令 `P=2^n`、`a=s.toNat`、`d=t.toNat`，总有 `0≤a,d<P`。
所有下标从最低位的 0 开始，`&` 表示自然数按位与。

1. **完整的左右移位相等条件**：

   `E_n(a,q) :⇔ 2^(n+q) ∣ ((2^(2q)-1)*a + (a mod 2^q))`。

   对应 Lean 的 `ShiftBalanced n a q`。这个条件包括 q=0、q≥n，
   也包括中间移位量下仍相等的特殊位模式，不能删掉后一类。

2. **取反内层不只剩最高位**：

   `H_n(v) :⇔ (v*2^(P-1-v) mod P) ≠ 2^(n-1)`。

   对应 `ComplementAdmissible n v`。n=0 时指数 n-1 按 Nat 截断为 0；此时 H 恒真。

3. **自移位不落入坏区间**：

   `D_n(v) :⇔ v=0 ∨ n≤v ∨ P ∤ v*2^v`。

   对应 `SelfShiftAdmissible n v`。

4. **交叉移位不产生重叠**：令 `b=x*2^y mod P`，

   `K_n(x,y) :⇔ b=0 ∨ (y & floor(x/2^b))=0`。

   对应 `CrossAdmissible n x y`。当 b≠0 时，它要求 y 的每个为 1 的第 j 位，
   都不能同时遇到 x 中为 1 的第 b+j 位；超过位宽的位视为零。
   此条件允许部分截断，不要求 x*2^y<P。

谓词和公共辅助证明在 [ExactConditions.lean](ExactConditions.lean)。

## 逐条输入级充要条件

下表每一行均对应原文件中的 `_iff`，不是只保证一个方向的假设。

| 规则 | 原等式成立的充要条件 | 对原条件的判断 |
| --- | --- | --- |
| [223](unsat/bv_term_small_rw_223.lean) | `(n≠1 ∨ a≠1) ∧ (n≠2 ∨ a≠2)` | 原位宽条件只对“所有输入”精确；固定输入还须保留小位宽的好值 |
| [238](unsat/bv_term_small_rw_238.lean) | `n≠2 ∨ a≠1` | n=2 只有 a=1 失败 |
| [270](unsat/bv_term_small_rw_270.lean) | `n≠2 ∨ d≠1 ∨ a<2` | n=2,d=1 时由外层右移是否为零决定 |
| [271](unsat/bv_term_small_rw_271.lean) | `n≠2 ∨ d≠1 ∨ a mod 2=0` | n=2,d=1 时由 a 是否为偶数决定 |
| [296](unsat/bv_term_small_rw_296.lean) | `H_n(a)` | 原操作数条件确实充要 |
| [298](unsat/bv_term_small_rw_298.lean) | `H_n(a)` | 原操作数条件确实充要 |
| [301](unsat/bv_term_small_rw_301.lean) | `E_n(a, floor(a/2^r))`，`r=a² mod P` | 原“移位量为零或至少为宽度”仅充分，漏掉位模式 |
| [379](unsat/bv_term_small_rw_379.lean) | `a=0 ∨ H_n(d)` | 原条件漏掉外层 s=0 |
| [380](unsat/bv_term_small_rw_380.lean) | `a=0 ∨ H_n(d)` | 原条件漏掉外层 s=0 |
| [458](unsat/bv_term_small_rw_458.lean) | `K_n(a,d)` | 原“全部截断或不截断”仅充分 |
| [473](unsat/bv_term_small_rw_473.lean) | `K_n(d,a)` | 原“全部截断或不截断”仅充分 |
| [477](unsat/bv_term_small_rw_477.lean) | `E_n(a, floor(d/2^r))`，`r=d² mod P` | 原条件只在固定 t、要求所有 s 时充要；固定 s 时仍会漏值 |
| [522](unsat/bv_term_small_rw_522.lean) | `P ∤ d*2^d ∨ E_n(a,d)` | 原自移位条件只在要求所有外层 s 时充要 |
| [669](unsat/bv_term_small_rw_669.lean) | `D_n(a)` | 原操作数条件确实充要 |
| [670](unsat/bv_term_small_rw_670.lean) | `D_n(a)` | 原操作数条件确实充要 |
| [719](unsat/bv_term_small_rw_719.lean) | `a=0 ∨ P ∤ a*2^a ∨ P ∣ d*2^a` | 原条件仅充分，遗漏了 t 的移位也为零的情况 |
| [1101](unsat/bv_term_small_rw_1101.lean) | `K_n(a,d)` | 与 458 的精确条件相同 |
| [1246](unsat/bv_term_small_rw_1246.lean) | `n≠1 ∨ a=0` | 唯一坏输入是 n=1,a=1 |
| [1343](unsat/bv_term_small_rw_1343.lean) | `K_n(d,a)` | 与 473 的精确条件相同 |

几个能否定旧条件必要性的例子：

- 301：n=6,a=34，平方余数 r=4，有效移位量 q=2，左右均为 8；旧区间条件为假。
- 379/380：n=1,a=0,d=1，原等式成立，但旧 H 条件为假。
- 458：n=3,a=6,d=1，内层部分截断成 4，原等式仍成立。
- 719：n=3,a=2,d=0，原等式成立，但旧 D 条件为假。

## 只依赖位宽的完整分类

用 `ν₂(v)` 表示正整数 v 中因子 2 的个数。以下谓词没有自由的 s、t：

- **T(n)**：不存在 `1≤e≤n` 满足 `e+ν₂(e)=n`。
- **S(n)**：不存在 `1≤v<n` 满足 `v+ν₂(v)≥n`。
  等价地，不存在 `1≤j<n` 满足 `n≡j (mod 2^j)`。
- **C(n)**：对每个 `d≥1` 且 `2^d<n`，令 `r=n mod 2^d`；
  d 的任何为 1 的第 j 位都不满足 `j<r≤d+j`。
- 令 `R(n,r)={v | 0≤v<P, v²≡r (mod P)}`。
  **Q₃₀₁(n)**：对每个 `0≤r<n` 及 `v∈R(n,r)`，成立 `E_n(v,floor(v/2^r))`。
- **Q₄₇₇(n)**：对每个 `0≤r<n`，`R(n,r)` 与区间 `[2^r,n*2^r)` 不相交。

这里的“完整”指充要的可判定数论条件，不表示它一定能简化成一个位宽下界或一个等差数列。
平方两条没有假设 Q₃₀₁ 与 Q₄₇₇ 相等；它们分别保留其必要条件。

| 规则 | 对所有 s、t 成立 **当且仅当** | Lean `_width_iff` 中的算术谓词 |
| --- | --- | --- |
| 223 | `n=0 ∨ n≥3` | 同左 |
| 238 | `n≠2` | 同左 |
| 270 | `n≠2` | 同左 |
| 271 | `n≠2` | 同左 |
| 296 | T(n) | `ComplementWidth n` |
| 298 | T(n) | `ComplementWidth n` |
| 301 | Q₃₀₁(n) | `SquareWidth301 n` |
| 379 | T(n) | `ComplementWidth n` |
| 380 | T(n) | `ComplementWidth n` |
| 458 | C(n) | `CrossWidth n` |
| 473 | C(n) | `CrossWidth n` |
| 477 | Q₄₇₇(n) | `SquareWidth477 n` |
| 522 | S(n) | `SelfShiftWidth n` |
| 669 | S(n) | `SelfShiftWidth n` |
| 670 | S(n) | `SelfShiftWidth n` |
| 719 | S(n) | `SelfShiftWidth n` |
| 1101 | C(n) | `CrossWidth n` |
| 1246 | `n≠1` | 同左 |
| 1343 | C(n) | `CrossWidth n` |

**形式化边界**：19 个 `_width_iff` 已证明与右栏算术谓词双向等价。
`ComplementWidth` 使用“所有合法 v 都满足 H”的余数形式，`SelfShiftWidth` 使用整除形式，
`CrossWidth` 使用“所有合法 x,y 都满足 K”的形式。
下面给出它们进一步化为 T、S、C 的数学双向推导；
ν₂ 形式以及 C 的消去 x 量词步骤尚未单独写成 Lean 等价定理。Q₃₀₁、Q₄₇₇ 的模根形式已直接出现在 Lean 命题中。

### T(n) 的正反方向

取内层变量 x，设 `A=x<<~x`、`B=x<<-x`。已证明 A、B 各自为零或至少为位宽，且 B=2A mod P。
唯一导致零/非零状态不同的图案是 `A=P/2`；此时 B=0。

x=0 时没有坏图案。x非零时令 `e=P-x.toNat>0`，则

`A ≡ -e*2^(e-1) (mod P)`。

模 P 的值恰为 P/2，当且仅当这个乘积中因子 2 的个数恰为 n-1，
也就是 `ν₂(e)+e-1=n-1`，即 `e+ν₂(e)=n`。这也自动给出 e≤n。

- 没有这样的 e，所有内层输入的 H 都成立，所以四条规则均成立。
- 存在这样的 e，取 x=P-e；此值合法且非零。296/298 取 s=x；379/380 取 t=x,s=1。
  坏内层使一侧清零、另一侧保留非零 s，构成反例。

n=0 时范围为空，且唯一字为零，所以没有边界遗漏。
例如 T(12)、T(24) 都真；“位宽必须为 2 的幂”不是必要条件。

### S(n) 的正反方向

对于 `0<v<n`，自移位为零恰当 `P∣v*2^v`，即 `v+ν₂(v)≥n`。
令 j=n-v，得到 `2^j∣v=n-j`，即 `n≡j (mod 2^j)`。

- 排除这些 v 后，669、670 已由输入级充要条件成立；522 的有效移位量只能为 0 或至少 n。
  719 在自移位非零时两侧为零，v≥n 时两个内层移位均零，v=0 也成立。
- 若存在坏 v，669/670 直接取 s=v；522 取 t=v,s=1，此时左右移位量为 v∈(0,n)，故不同。
  719 取 s=v,t=1：s<<s=0，而 `(s|1)<<s=2^v≠0`，左侧零、右侧 s。

所以四条规则的整个位宽分类完全相同。S(12)、S(24) 为真，进一步否定了幂位宽的必要性。

### C(n) 的正反方向：把全字枚举化成位宽余数的位检查

四条规则共同的精确输入条件是 K；473/1343 只是交换 x、y。
令 y 的值为 d，`b=x*2^d mod P`。
b=0 恒成立；b≥n 也不会相交，因此只需研究 `0<b<n`。

b是 `2^d` 的正倍数，故 `2^d<n`。d=0 时掩码本身为零，所以 d≥1。
令 `u=x mod 2^(n-d)`，有 `b=u*2^d`，因而 u≤b<2^b。
这说明 x 低 n-d 位中的任何 1，都无法与从第 b 位开始的移位结果相遇。
失败只能来自高位：d 的某个为 1 的第 j 位满足

`n-d ≤ b+j < n`。

因为 `j<d` 且 `2*d≤2^d`，这个 b 必须是小于 n 的最大正 `2^d` 倍数。
设 `r=n mod 2^d`。r=0 时不存在上述相交；r>0 时 b=n-r，
上述不等式恰为 `j<r≤d+j`，得到 C(n) 的必要性。

反过来，如果 d、j 满足这个坏模式，构造

```
b = n-r
u = b / 2^d
x = u + 2^(b+j)
y = d
```

有 `0<b<n`、`n-d≤b+j<n`，所以 x<P，且 x<<y=b；
高位加项被内层左移截断，却与外层掩码在 b+j 位相交，故 K 为假。
458/1101 取 `(s,t)=(x,y)`；473/1343 取 `(s,t)=(y,x)`，即得四条反例。

这同时给出充分性、必要性和反例生成方法，排除了“只有实验观察”的问题。
例如 C(12) 假（d=3,r=4,j=1），但 C(24) 真。

### 平方两条：为什么必须保留模根和位模式

令 `r=v² mod P`、`q=floor(v/2^r)`。
若 r≥n，则 v<P≤2^r，从而 q=0，因此只需研究 r<n 的平方模根。

固定 q 时，对于给定外层值 a，左右移位相等的精确条件是 E。
证明令 `e=2^q`、`ρ=a mod e`，把等式乘 e 后得到

`a*e² mod (P*e) = a-ρ`。

`0≤a-ρ<P*e`，因此恰好等价于

`P*e ∣ (e²-1)*a+ρ`，

即 E。这一整除等价已在 `Learned.BitVec.bvshl_eq_bvlshr_iff_dvd` 中形式化。

- 301 的外层与内层是同一个值 v，故必须检查每个平方模根自身是否满足 E，得到 Q₃₀₁。
  例如 n=6,v=34,q=2 满足 E，不能因为 0<q<n 就错误排除它。
- 477 的外层值独立、且要求所有外层输入成立。
  此时 q=0 或 q≥n 是充要条件：如果 0<q<n，取外层 s=1，左为 2^q、右为 0。
  于是禁区恰为 `2^r≤v<n*2^r`，得到 Q₄₇₇。

因此 Q₃₀₁、Q₄₇₇ 都是只依赖 n 的平方同余根条件，而不是重新假设原 BV 等式成立。
它们可通过逐位提升模根精确判断，无须遍历全部 2^n 个字。
r=0 时正根至少为 `2^ceil(n/2)≥n`，有效移位量 q=v 已足够清空字，因此程序可跳过这一类。

## 可执行分类与验证

[分类程序](../../scripts/classify_refuted_widths.py) 实现 T/S/C 与平方模根判据；对坏位宽构造具体 s、t 并检查原等式两侧不同。

```sh
python3 scripts/classify_refuted_widths.py --widths 8 12 16 24 32 64
python3 scripts/classify_refuted_widths.py --max-width 128 --verify-small 7
```

`--verify-small 7` 穷举位宽 0..7 的 21845 对输入，对照 19 个输入谓词、原等式、位宽分类及模根。
有限范围核对检查程序实现；任意位宽结论的形式化范围以上文说明为准。不保存可随时重算的分类 CSV。

平方两条在 8 位失败：301 取 s=62，左右为 240、7；477 取 s=1,t=62，左右为 8、0。
32 位通过模根判据，64 位不通过，程序可输出具体见证。

共享算术谓词位于 [ExactConditions.lean](ExactConditions.lean)；通用整除判据位于
[学习库 Shift.Characterization](../../LEMMAS_learned/BitVec/Shift/Characterization.lean)。
`audit_qfbv_proofs.py` 直接发现并检查全部公开 benchmark 定理，包含 38 个双向证明，不依赖手工 CSV 清单。
