# Maths in Lean: Multilinear Map

mathlib 中多线性代数的形式化以 `MultilinearMap` 类型为核心。该类型涵盖了所有参数均为线性的映射。这种结构为张量和行列式等奠定了基础。

## 研究内容

* **`Mathlib.LinearAlgebra.Multilinear.Basic`**

定义了 `MultilinearMap`，即多线性映射空间。它包含一些基本性质，例如跨坐标的可加性（`map_add_univ`）和可乘性（`map_smul_univ`），以及（`map_piecewise_add`）。


## Main Definitions

### 1. Multilinear Maps
中心结构是 `MultilinearMap R M₁ M₂`。与教科书中的标准符号 $f: M_1 \times \dots \times M_n \to M_2$ 不同，mathlib 将其定义在一个依值函数 `M₁ : ι → Type*` 上，允许值域按索引 `i` 变化。

```lean
structure MultilinearMap (R : Type uR) {ι : Type uι} (M₁ : ι → Type v₁) (M₂ : Type v₂)
  [Semiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [∀ i, Module R (M₁ i)] [Module R M₂] where
  /-- The underlying multivariate function. -/
  toFun : (∀ i, M₁ i) → M₂
  /-- Additivity in every argument. -/
  map_update_add' : ∀ [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i),
    toFun (update m i (x + y)) = toFun (update m i x) + toFun (update m i y)
  /-- Scalar compatibility in every argument. -/
  map_update_smul' : ∀ [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i),
    toFun (update m i (c • x)) = c • toFun (update m i x)
```
**主要特性：**

* **实现方式：** 它封装了一个函数 `toFun : (∀ i, M₁ i) → M₂`（依赖函数空间），而不是一个基于乘积类型的函数。

* **线性性：** 线性性通过 `Function.update` 实现，即在保持其他坐标不变的情况下，修改第 i 个坐标。

* **结构：** `MultilinearMap` 构成一个 `R` 模块。

## Main Theorems

### 1. 零向量在多重线性映射下的像是零 (`map_zero`)
即：$f(\vec{0}) = 0$。
```lean
theorem map_zero [Nonempty ι] : f 0 = 0 := by
  obtain ⟨i, _⟩ : ∃ i : ι, i ∈ Set.univ := Set.exists_mem_of_nonempty ι
  exact map_coord_zero f i rfl
```
**定理含义**

*   **输入**: `f 0`。这里的 `0` 代表**零向量**（即所有的分量都是 0，是一个函数 `fun i => 0`）。
*   **输出**: `0`。这是目标空间 $M_2$ 中的零元素。
*   **前提**: `[Nonempty ι]`。这非常关键，它要求索引集合 $\iota$ **非空**（即至少有一个输入变量）。

**自然语言表述**：
> 只要多重线性映射至少有一个参数（即不是 0 元运算），那么当所有输入都为 0 时，出结果必定为 0。

### 2.  多线性映射的有限子集展开定理
 ``` lean
theorem map_piecewise_add [DecidableEq ι] (m m' : ∀ i, M₁ i) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s ∈ t.powerset, f (s.piecewise m m') := by
```
（t.piecewise a b）指的是在t上是a，在其余分量是b的向量
```lean
  revert m'
  refine Finset.induction_on t (by simp) ?_
  intro i t hit Hrec m'
```
  这里对应于自然语言证明中的对t的大小进行归纳
```lean
  have A : (insert i t).piecewise (m + m') m' = update (t.piecewise (m + m') m') i (m i + m' i) :=
    t.piecewise_insert _ _ _ 
  have B : update (t.piecewise (m + m') m') i (m' i) = t.piecewise (m + m') m' := by 
    ext j
    by_cases h : j = i
    · rw [h]
      simp [hit]
    · simp [h]
  let m'' := update m' i (m i)
  have C : update (t.piecewise (m + m') m') i (m i) = t.piecewise (m + m'') m'' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [m'', hit]
    · by_cases h' : j ∈ t <;> simp [m'', h, h']
```
引入新的变量m''，将要计算n+1位相加的问题转换成计算n位相加的问题和已知的1位相加的定理（map_update_add）
``` lean
  rw [A, f.map_update_add, B, C, Finset.sum_powerset_insert hit, Hrec, Hrec, add_comm (_ : M₂)]
  congr 1
  refine Finset.sum_congr rfl fun s hs => ?_
  have : (insert i s).piecewise m m' = s.piecewise m m'' := by
    ext j
    by_cases h : j = i
    · rw [h]
      simp [m'', Finset.notMem_of_mem_powerset_of_notMem hs hit]
    · by_cases h' : j ∈ s <;> simp [m'', h, h']
  rw [this]
```
## 缺失/待证明定理说明

### 未证明定理：代数同态下的行列式不变性

#### 定理代码

```lean
-- TODO：证明当 f 是矩阵代数的代数同态时，(f x).det = x.det
-- （使用Skolem-Noether定理）
proof_wanted Matrix.det_map' {K m F : Type*} [Field K] [Fintype m] [DecidableEq m]
    [FunLike F (Matrix m m K) (Matrix m m K)] [AlgHomClass F K _ _] (f : F) (x : Matrix m m K) :
    (f x).det = x.det
```

#### 自然语言叙述

设 `K` 是一个域，`m` 是一个有限类型（表示矩阵的维数），`F` 是从矩阵代数 `Matrix m m K` 到自身的 `K`-代数同态类。对于任意这样的代数同态 `f` 和任意矩阵 `x`，都有 `f(x)` 的行列式等于 `x` 的行列式。

换句话说：矩阵代数的任何代数自同态都保持行列式不变。
