-- a case from `small_bv_problems/bv-term-small-rw_1446.smt2`

设

$$
n \in \mathbb{N}, \quad n > 0
$$

定义 **(n) 位位向量集合**：

$$
\mathrm{BV}_n := {, x \in \mathbb{N} \mid 0 \le x < 2^n ,}.
$$

对于任意

$$
x \in \mathrm{BV}_n
$$

定义其对应的自然数值

$$
\operatorname{val}(x) = x.
$$

即将位向量视为区间

$$
[0,2^n)
$$

中的整数。


**位向量运算定义**

1. **位向量乘法**

定义函数

$$
\operatorname{bvmul} : \mathrm{BV}_n \times \mathrm{BV}_n \to \mathrm{BV}_n
$$

为

$$
\operatorname{bvmul}(a,b) = (a \cdot b) \bmod 2^n .
$$

2. **逻辑右移（logical shift right）**

定义函数

$$
\operatorname{bvlshr} :
\mathrm{BV}_n \times \mathrm{BV}_n
\to
\mathrm{BV}_n
$$

为

$$
\operatorname{bvlshr}(a,b) =
\left\lfloor
\frac{a}{2^{b}}
\right\rfloor
\bmod 2^n .
$$

其中

$$
a,b \in \mathrm{BV}_n
$$

且

$$
2^b
$$

表示自然数指数。


>使用自然数表示时，逻辑右移等价为
>
>$$
\operatorname{bvlshr}(a,b) = (a \div 2^b) \bmod 2^n .
$$

**位移交换定理**

**定理（逻辑右移交换性）**

设

$$
n \in \mathbb{N}, \quad n>0
$$

且

$$
x,y,z \in \mathrm{BV}_n .
$$

则成立

$$
\operatorname{bvlshr}(\operatorname{bvlshr}(x,y),z) = \operatorname{bvlshr}(\operatorname{bvlshr}(x,z),y).
$$

