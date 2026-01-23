# Maths in Lean : 实数理论的关键构造与接口

## 简介

实数在 `Mathlib` 中主要在 `Mathlib.Data.Real` 中实现，采用的是基于 Cauchy 列的定义，写在 `Mathlib.Data.Real.Basic` 中。文件中写道，选用 Cauchy 列定义是因为证明交换环等代数性质更方便，而关于实数的其他性质则在该目录下剩余文件, 该目录下部分文件为

-   `Archimedean.lean`: 有关 Archimedean 性质
-   `Basic.lean`: 实数的构造 (核心文件)
-   `CompleteField.lean`: 证明了实数没有非平凡环自同态
-   `ConjExponents.lean`: 给出了 Holder 共轭的定义和简单性质
-   `Embedding.lean`: 证明了 Archimedean 有序加法群可以嵌入到 `ℝ` 中
-   `ENatENNReal`: 给出了 `ℕ∞` 到 `ℝ≥0∞` 的类型提升
-   `Pointwise.lean`: 对实数集的逐点操作相关
-   `Sign.lean`: 符号 `sign` 函数
-   `Sqrt.lean`: 平方根和 Cauchy-Schwarz 不等式相关


## Cauchy 列

Cauchy 列在 `Mathlib.Algebra.Order.CauSeq.Basic` 中定义，完备化在 `Mathlib.Algebra.Order.CauSeq.Completion` 中定义。

### Basic.lean

#### IsCauSeq

```lean
def IsCauSeq {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {β : Type*} [Ring β] (abv : β → α) (f : ℕ → β) :
    Prop :=
  ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j - f i) < ε
```

`IsCauSeq` 用来判断一个序列 `f : ℕ → β` 是否是 Cauchy 列，其中 `β` 是环。此处的 Cauchy 列定义和通常教科书上的定义有略微区别。`IsCauSeq` 还需指定采用的绝对值函数 `abv : β → α` 来衡量距离，其中 `α` 需要满足一些良好的性质, 通常为 `ℚ` 或 `ℝ`。例如在构造实数时，`abv` 采用的是 `abs : ℚ → ℚ`。

这个定义蕴含教科书定义的定理为

```lean
theorem cauchy₂ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ j ≥ i, ∀ k ≥ i, abv (f j - f k) < ε := by
  refine (hf _ (half_pos ε0)).imp fun i hi j ij k ik => ?_
  rw [← add_halves ε]
  refine lt_of_le_of_lt (abv_sub_le abv _ _ _) (add_lt_add (hi _ ij) ?_)
  rw [abv_sub abv]; exact hi _ ik
```

check: `IsCauSeq.cauchy₂.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv] {f : ℕ → β} (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) :
  ∃ i, ∀ j ≥ i, ∀ k ≥ i, abv (f j - f k) < ε`

这个定理接受 `hf : IsCauSeq abv f`，给出 `f` 是（教科书定义）的 Cauchy 列

可以证明 Cauchy 列的有界性, 在加法，乘法，取负号下仍然是 Cauchy 列，常数列是 Cauchy 列等基本性质：

```lean
-- 接受 IsCauSeq 的证据，返回证明：存在界 r
lemma bounded (hf : IsCauSeq abv f) : ∃ r, ∀ i, abv (f i) < r := by
  obtain ⟨i, h⟩ := hf _ zero_lt_one
  set R : ℕ → α := @Nat.rec (fun _ => α) (abv (f 0)) fun i c => max c (abv (f i.succ)) with hR
  have : ∀ i, ∀ j ≤ i, abv (f j) ≤ R i := by
    refine Nat.rec (by simp [hR]) ?_
    rintro i hi j (rfl | hj)
    · simp [R]
    · exact (hi j hj).trans (le_max_left _ _)
  refine ⟨R i + 1, fun j ↦ ?_⟩
  obtain hji | hij := le_total j i
  · exact (this i _ hji).trans_lt (lt_add_one _)
  · simpa using (abv_add abv _ _).trans_lt <| add_lt_add_of_le_of_lt (this i _ le_rfl) (h _ hij)

-- 类似上面
lemma bounded' (hf : IsCauSeq abv f) (x : α) : ∃ r > x, ∀ i, abv (f i) < r :=
  let ⟨r, h⟩ := hf.bounded
  ⟨max r (x + 1), (lt_add_one x).trans_le (le_max_right _ _),
    fun i ↦ (h i).trans_le (le_max_left _ _)⟩

-- 接受 x，返回证明：恒输出 x 的常序列 IsCauSeq
lemma const (x : β) : IsCauSeq abv fun _ ↦ x :=
  fun ε ε0 ↦ ⟨0, fun j _ => by simpa [abv_zero] using ε0⟩

-- 接受 f 和 g 的 IsCauSeq 的证据，返回证明：f + g 是 CauSeq
theorem add (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq abv (f + g) := fun _ ε0 =>
  let ⟨_, δ0, Hδ⟩ := rat_add_continuous_lemma abv ε0
  let ⟨i, H⟩ := exists_forall_ge_and (hf.cauchy₃ δ0) (hg.cauchy₃ δ0)
  ⟨i, fun _ ij =>
    let ⟨H₁, H₂⟩ := H _ le_rfl
    Hδ (H₁ _ ij) (H₂ _ ij)⟩

-- 接受 f 和 g 的 IsCauSeq 的证据，返回证明：f * g 是 CauSeq
lemma mul (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq abv (f * g) := fun _ ε0 =>
  let ⟨_, _, hF⟩ := hf.bounded' 0
  let ⟨_, _, hG⟩ := hg.bounded' 0
  let ⟨_, δ0, Hδ⟩ := rat_mul_continuous_lemma abv ε0
  let ⟨i, H⟩ := exists_forall_ge_and (hf.cauchy₃ δ0) (hg.cauchy₃ δ0)
  ⟨i, fun j ij =>
    let ⟨H₁, H₂⟩ := H _ le_rfl
    Hδ (hF j) (hG i) (H₁ _ ij) (H₂ _ ij)⟩

-- (-f) 是 CauSeq 当且仅当 f 是 Causeq
@[simp] lemma _root_.isCauSeq_neg : IsCauSeq abv (-f) ↔ IsCauSeq abv f := by
  simp only [IsCauSeq, Pi.neg_apply, ← neg_sub', abv_neg]
```

#### CauSeq 的定义

`CauSeq` 的定义直接使用子类型的方式，利用 `IsCauSeq` 定义。

```lean
def CauSeq {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (β : Type*) [Ring β] (abv : β → α) : Type _ :=
  { f : ℕ → β // IsCauSeq abv f }
```

#### CauSeq 的运算

```lean
instance : Add (CauSeq β abv) :=
  ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩
instance : Mul (CauSeq β abv) := ⟨fun f g ↦ ⟨f * g, f.2.mul g.2⟩⟩
instance : Neg (CauSeq β abv) := ⟨fun f ↦ ⟨-f, f.2.neg⟩⟩
```

记得 `CauSeq` 是一个子类型，构造其元素需要 `val` 和 `property`, 后者为 `IsCauSeq` 的证明。例如在上述代码的 `Add` 中：
- `val` 是 `f + g`，或者说是 `↑f + ↑g`，也即从 `CauSeq β abv` 转换到其 `val : ℕ → β`。在 Lean 语言中 `ℕ → β` 自动配备环结构，所以可以直接写加号, 乘号负号同理.
- `property` 是 `f.2.add g.2`，就是利用 `f` 和 `g` 是 Cauchy 列的事实/证明给出 `f + g` 是 Cauchy 列的证明, 利用上面提到的 `IsCauSeq` 的基本性质.

```lean
instance : Zero (CauSeq β abv) :=
  ⟨const 0⟩

instance : One (CauSeq β abv) :=
  ⟨const 1⟩
```

其中 `const` 的定义为

```lean
/-- The constant Cauchy sequence. -/
def const (x : β) : CauSeq β abv := ⟨fun _ ↦ x, IsCauSeq.const _⟩
```

还有更多运算：

```lean
instance : Sub (CauSeq β abv) :=
  ⟨fun f g => ofEq (f + -g) (fun x => f x - g x) fun i => by simp [sub_eq_add_neg]⟩
instance : SMul G (CauSeq β abv) :=
  ⟨fun a f => (ofEq (const (a • (1 : β)) * f) (a • (f : ℕ → β))) fun _ => smul_one_mul _ _⟩
instance : Pow (CauSeq β abv) ℕ :=
  ⟨fun f n =>
    (ofEq (npowRec n f) fun i => f i ^ n) <| by induction n <;> simp [*, npowRec, pow_succ]⟩
```

减法是先说明 `f + -g` 和 `(fun x => f x - g x)` 每个点都相同, **注意前一列是 `CauSeq` 而后一列是 `ℕ → β`**，然后利用前者是 Cauchy 列即得，其中 `ofEq` 函数用于根据两个序列每个点都相同, 并且一个列 Cauchy 来构造另一个列的 `CauSeq`.

```lean
/-- Given a Cauchy sequence `f`, create a Cauchy sequence from a sequence `g` with
the same values as `f`. -/
def ofEq (f : CauSeq β abv) (g : ℕ → β) (e : ∀ i, f i = g i) : CauSeq β abv :=
  ⟨g, fun ε => by rw [show g = f from (funext e).symm]; exact f.cauchy⟩
```
标量乘法也是类似的利用 `ofEq` 和一般乘法来证明。证明幂则是利用了归纳法，其中 `npowRec` 由如下代码归纳定义：

```lean
/--
The fundamental power operation in a monoid.
`npowRec n a = a*a*...*a` n times.
This function should not be used directly; it is often used to implement a `Pow M Nat` instance,
but end users should use the `a ^ n` notation instead.
-/
@[expose]
def npowRec [One M] [Mul M] : Nat → M → M
  | 0, _ => 1
  | n + 1, a => npowRec n a * a
```

定义逆元看上去很简单，但是需要先证明逆序列确实是 Cauchy 列：

```lean
theorem inv_aux {f : CauSeq β abv} (hf : ¬LimZero f) :
    ∀ ε > 0, ∃ i, ∀ j ≥ i, abv ((f j)⁻¹ - (f i)⁻¹) < ε
  | _, ε0 =>
    let ⟨_, K0, HK⟩ := abv_pos_of_not_limZero hf
    let ⟨_, δ0, Hδ⟩ := rat_inv_continuous_lemma abv ε0 K0
    let ⟨i, H⟩ := exists_forall_ge_and HK (f.cauchy₃ δ0)
    ⟨i, fun _ ij =>
      let ⟨iK, H'⟩ := H _ le_rfl
      Hδ (H _ ij).1 iK (H' _ ij)⟩
```

check: `CauSeq.inv_aux.{u_1, u_2} {α : Type u_1} {β : Type u_2} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv] {f : CauSeq β abv} (hf : ¬f.LimZero) (ε : α) :
  ε > 0 → ∃ i, ∀ j ≥ i, abv ((↑f j)⁻¹ - (↑f i)⁻¹) < ε`

也即给定 f 不趋于零，以及一个 ε : α，并且 ε > 0，证明 f 的逐项取逆序列是 Cauchy 列。

证明的思路是，因为 `f` 不趋于零，所以最终 `f` 绝对值有正下界（`HK : ∃ i, ∀ j ≥ i, w✝ ≤ abv (↑f j)`），虽然这个下界的具体值被舍弃掉了（`K0` 是其大于零的证明）。然后利用倒数（刨去原点的一个邻域之后）的一致连续性，让倒数差可以被差控制住（`Hδ : ∀ {a b : β}, w✝¹ ≤ abv a → w✝¹ ≤ abv b → abv (a - b) < w✝ → abv (a⁻¹ - b⁻¹) < x✝`，其中 `w✝¹` 是刚刚的正下界，`x✝` 是题目中的 `ε`）。为了将倒数差控制住，既需要控制差（`f.cauchy₃ δ0`），也需要控制下界（`HK`），所以应用 `exists_forall_ge_and` 可以一起控制住这两个东西（把两者的“大 N”取 max 就可以一起控制了），这样得到的“大 N”就是 `i`，这正是我们想要的。

于是就可以愉快地定义逆元了：

```lean
/-- Given a Cauchy sequence `f` with nonzero limit, create a Cauchy sequence with values equal to
the inverses of the values of `f`. -/
def inv (f : CauSeq β abv) (hf : ¬LimZero f) : CauSeq β abv :=
  ⟨_, inv_aux hf⟩
```

#### CauSeq.LimZero & CauSeq.equiv


`CauSeq.LimZero` 接受一个 Cauchy 列 `f`，返回“`f`趋于零”这个命题。 

```lean
/-- `LimZero f` holds when `f` approaches 0. -/
def LimZero {abv : β → α} (f : CauSeq β abv) : Prop :=
  ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j) < ε
```

`CauSeq.equiv` 在所有 (ℕ → β, abv) Cauchy 列上定义了一个等价关系，两个 Cauchy 列等价当且仅当其差趋于零。

```lean
instance equiv : Setoid (CauSeq β abv) :=
  ⟨fun f g => LimZero (f - g),
    ⟨fun f => by simp [zero_limZero],
    fun f ε hε => by simpa using neg_limZero f ε hε,
    fun fg gh => by simpa using add_limZero fg gh⟩⟩
```

可以看到等价关系在 Lean 语言中的实现为 `Setoid`，具体如下

```lean
/--
A setoid is a type with a distinguished equivalence relation, denoted `≈`.

The `Quotient` type constructor requires a `Setoid` instance.
-/
class Setoid (α : Sort u) where
  /-- `x ≈ y` is the distinguished equivalence relation of a setoid. -/
  r : α → α → Prop
  /-- The relation `x ≈ y` is an equivalence relation. -/
  iseqv : Equivalence r
```

在 equiv 的定义中，`r` 为 `fun f g => LimZero (f - g)`，接受两个 Cauchy 列，返回“其差趋于零”这个命题。后面则是关系 `r` 是等价关系的证明，包括自反性、对称性和传递性。

#### CauSeq 的序结构

定义序结构首先要是定义什么是正的。

```lean
/-- The entries of a positive Cauchy sequence eventually have a positive lower bound. -/
def Pos (f : CauSeq α abs) : Prop :=
  ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ f j
```

这里有个三分定理（全序性质），表明一个 Cauchy 列 `f` 要么是正的，要么趋于零，要么其相反列是正的。

check: `∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStrictOrderedRing α] (f : CauSeq α abs),
  f.Pos ∨ f.LimZero ∨ (-f).Pos`

```lean
theorem trichotomy (f : CauSeq α abs) : Pos f ∨ LimZero f ∨ Pos (-f) := by
  -- 先处理趋于零的情况
  rcases Classical.em (LimZero f) with h | h
  · simp [*]
  simp only [false_or, h] -- 现在 h 是 ¬f.LimZero 的证据
  rcases abv_pos_of_not_limZero h with ⟨K, K0, hK⟩ -- 绝对值是正 Cauchy 列
  rcases exists_forall_ge_and hK (f.cauchy₃ K0) with ⟨i, hi⟩ -- 找到 i，使得 f i 绝对值大于等于 K （根据 f 是正 Cauchy 列）并且 i 后面的尾项的差小于 K（Cauchy 列性质）
  -- 此时只要知道了 f i 是正是负就可以知道原序列的正负了
  refine (le_total 0 (f i)).imp ?_ ?_ <;>
    refine fun h => ⟨K, K0, i, fun j ij => ?_⟩ <;>
    have := (hi _ ij).1 <;>
    obtain ⟨h₁, h₂⟩ := hi _ le_rfl
  · rwa [abs_of_nonneg] at this
    rw [abs_of_nonneg h] at h₁
    exact
      (le_add_iff_nonneg_right _).1
        (le_trans h₁ <| neg_le_sub_iff_le_add'.1 <| le_of_lt (abs_lt.1 <| h₂ _ ij).1)
  · rwa [abs_of_nonpos] at this
    rw [abs_of_nonpos h] at h₁
    rw [← sub_le_sub_iff_right, zero_sub]
    exact le_trans (le_of_lt (abs_lt.1 <| h₂ _ ij).2) h₁
```

于是就可以定义序了：`f < g` 当且仅当 `g - f` 是正的，`f <= g` 当且仅当 `f < g` 或 `f` 等价于 `g`。

```lean
instance : LT (CauSeq α abs) :=
  ⟨fun f g => Pos (g - f)⟩

instance : LE (CauSeq α abs) :=
  ⟨fun f g => f < g ∨ f ≈ g⟩
```

Cauchy 列还定义了 Max 和 Min（用于实数的格结构）为逐项取 Max / Min。

```lean
instance : Max (CauSeq α abs) :=
  ⟨fun f g =>
    ⟨f ⊔ g, fun _ ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun _ H _ ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_sup_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩
instance : Min (CauSeq α abs) :=
  ⟨fun f g =>
    ⟨f ⊓ g, fun _ ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun _ H _ ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_inf_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩
```

其定义方式与加法、乘法类似，而 Max / Min 保 Cauchy 则是利用 sup, inf 的连续性证明的。


### 完备化

#### 定义

```lean
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

-- TODO: rename this to `CauSeq.Completion` instead of `CauSeq.Completion.Cauchy`.
/-- The Cauchy completion of a ring with absolute value. -/
def Cauchy :=
  @Quotient (CauSeq _ abv) CauSeq.equiv
```

其中 Cauchy 的类型完整写的话是

`CauSeq.Completion.Cauchy.{u_1, u_2} {α : Type u_1} [Field α] [LinearOrder α] [IsStrictOrderedRing α] {β : Type u_2} [Ring β] (abv : β → α) [IsAbsoluteValue abv] : Type u_2`

完备化的定义为所有 `CauSeq _ abv`（所有 `abv` 意义下的 Cauchy 列）商掉等价关系 `CauSeq.equiv`。

#### 完备化上的运算

```lean
/-- The map from the original ring into the Cauchy completion. -/
def ofRat (x : β) : Cauchy abv :=
  mk (const abv x)

instance : Zero (Cauchy abv) :=
  ⟨ofRat 0⟩

instance : One (Cauchy abv) :=
  ⟨ofRat 1⟩
```

其中 `ofRat` 用于将原来的环（在实数构造中就是 `ℚ`）自然的嵌入到完备化后的商结构中。

类似地完备化后也有

```lean
instance : Add (Cauchy abv) :=
  ⟨(Quotient.map₂ (· + ·)) fun _ _ hf _ _ hg => add_equiv_add hf hg⟩
instance : Neg (Cauchy abv) :=
  ⟨(Quotient.map Neg.neg) fun _ _ hf => neg_equiv_neg hf⟩
instance : Mul (Cauchy abv) :=
  ⟨(Quotient.map₂ (· * ·)) fun _ _ hf _ _ hg => mul_equiv_mul hf hg⟩
instance : Sub (Cauchy abv) :=
  ⟨(Quotient.map₂ Sub.sub) fun _ _ hf _ _ hg => sub_equiv_sub hf hg⟩
instance {γ : Type*} [SMul γ β] [IsScalarTower γ β β] : SMul γ (Cauchy abv) :=
  ⟨fun c => (Quotient.map (c • ·)) fun _ _ hf => smul_equiv_smul _ hf⟩
instance : Pow (Cauchy abv) ℕ :=
  ⟨fun x n => Quotient.map (· ^ n) (fun _ _ hf => pow_equiv_pow hf _) x⟩
```

但是新构造出来的函数需要证明无关于代表元，所以需要用 Quotient.map 和 Quotient.map₂（分别用于一元函数和二元函数）

```lean
/-- Map a function `f : α → β` that sends equivalent elements to equivalent elements
to a function `Quotient sa → Quotient sb`. Useful to define unary operations on quotients. -/
protected def map (f : α → β) (h : ∀ ⦃a b : α⦄, a ≈ b → f a ≈ f b) : Quotient sa → Quotient sb :=
  Quot.map f h
/-- Map a function `f : α → β → γ` that sends equivalent elements to equivalent elements
to a function `f : Quotient sa → Quotient sb → Quotient sc`.
Useful to define binary operations on quotients. -/
protected def map₂ (f : α → β → γ)
    (h : ∀ ⦃a₁ a₂⦄, a₁ ≈ a₂ → ∀ ⦃b₁ b₂⦄, b₁ ≈ b₂ → f a₁ b₁ ≈ f a₂ b₂) :
    Quotient sa → Quotient sb → Quotient sc :=
  Quotient.lift₂ (fun x y ↦ ⟦f x y⟧) fun _ _ _ _ h₁ h₂ ↦ Quot.sound <| h h₁ h₂
```

定义逆元：

```lean
open Classical in
noncomputable instance : Inv (Cauchy abv) :=
  ⟨fun x =>
    (Quotient.liftOn x fun f => mk <| if h : LimZero f then 0 else inv f h) fun f g fg => by
      have := limZero_congr fg
      by_cases hf : LimZero f
      · simp [hf, this.1 hf]
      · have hg := mt this.2 hf
        simp only [hf, dite_false, hg]
        have If : mk (inv f hf) * mk f = 1 := mk_eq.2 (inv_mul_cancel hf)
        have Ig : mk (inv g hg) * mk g = 1 := mk_eq.2 (inv_mul_cancel hg)
        have Ig' : mk g * mk (inv g hg) = 1 := mk_eq.2 (mul_inv_cancel hg)
        rw [mk_eq.2 fg, ← Ig] at If
        rw [← mul_one (mk (inv f hf)), ← Ig', ← mul_assoc, If, mul_assoc, Ig', mul_one]⟩
```

其中 
- `liftOn` 类似于 `map`，但是 `liftOn` 只有定义域是商结构，而 `map` 中定义域和目标域都是商结构。
- `mk` 是 Cauchy 列到商结构的自然映射

这里被提升的函数是 `fun f => mk <| if h : Liero f then 0 else inv f h`，其含义为，如果 `f` 趋于零，则定义其逆为零序列，否则为逆序列（这里使用了 `CauSeq` 的 `inv`）。这个判断不是直觉主义的。后面则给出了无关于代表元的证明，其中 `f g fg` 分别为两个 Cauchy 列和其等价的证明。


## 实数的构造

实数的构造直接使用 `CauSeq.Completion.Cauchy` 进行构造，其绝对值函数就是 `abs : ℚ → ℚ`。

```lean
/-- The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational
numbers. -/
structure Real where ofCauchy ::
  /-- The underlying Cauchy completion -/
  cauchy : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)
```

也就是 `Real` 是只有一个属性的结构体。

### 实数的域结构

此处使用 `⟨⟩` 符号来从 `Real` 中提取 Cauchy 列等价类，可以看到实数的运算就是其 Cauchy 列等价类的运算。

```lean
private irreducible_def zero : ℝ :=
  ⟨0⟩

private irreducible_def one : ℝ :=
  ⟨1⟩

private irreducible_def add : ℝ → ℝ → ℝ
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

private irreducible_def neg : ℝ → ℝ
  | ⟨a⟩ => ⟨-a⟩

private irreducible_def mul : ℝ → ℝ → ℝ
  | ⟨a⟩, ⟨b⟩ => ⟨a * b⟩

private noncomputable irreducible_def inv' : ℝ → ℝ
  | ⟨a⟩ => ⟨a⁻¹⟩

instance : Zero ℝ :=
  ⟨zero⟩

instance : One ℝ :=
  ⟨one⟩

instance : Add ℝ :=
  ⟨add⟩

instance : Neg ℝ :=
  ⟨neg⟩

instance : Mul ℝ :=
  ⟨mul⟩

instance : Sub ℝ :=
  ⟨fun a b => a + -b⟩

noncomputable instance : Inv ℝ :=
  ⟨inv'⟩
```

于是实数上面就有环结构了：

```lean
instance commRing : CommRing ℝ where
  natCast n := ⟨n⟩
  intCast z := ⟨z⟩
  npow := @npowRec ℝ ⟨1⟩ ⟨(· * ·)⟩
  nsmul := @nsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩
  zsmul := @zsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩ ⟨@Neg.neg ℝ _⟩ (@nsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩)
  add_zero a := by apply ext_cauchy; simp [cauchy_add, cauchy_zero]
  zero_add a := by apply ext_cauchy; simp [cauchy_add, cauchy_zero]
  add_comm a b := by apply ext_cauchy; simp only [cauchy_add, add_comm]
  add_assoc a b c := by apply ext_cauchy; simp only [cauchy_add, add_assoc]
  mul_zero a := by apply ext_cauchy; simp [cauchy_mul, cauchy_zero]
  zero_mul a := by apply ext_cauchy; simp [cauchy_mul, cauchy_zero]
  mul_one a := by apply ext_cauchy; simp [cauchy_mul, cauchy_one]
  one_mul a := by apply ext_cauchy; simp [cauchy_mul, cauchy_one]
  mul_comm a b := by apply ext_cauchy; simp only [cauchy_mul, mul_comm]
  mul_assoc a b c := by apply ext_cauchy; simp only [cauchy_mul, mul_assoc]
  left_distrib a b c := by apply ext_cauchy; simp only [cauchy_add, cauchy_mul, mul_add]
  right_distrib a b c := by apply ext_cauchy; simp only [cauchy_add, cauchy_mul, add_mul]
  neg_add_cancel a := by apply ext_cauchy; simp [cauchy_add, cauchy_neg, cauchy_zero]
  natCast_zero := by apply ext_cauchy; simp [cauchy_zero]
  natCast_succ n := by apply ext_cauchy; simp [cauchy_one, cauchy_add]
  intCast_negSucc z := by apply ext_cauchy; simp [cauchy_neg, cauchy_natCast]
```

其中 `ext_cauchy` 只是

```lean
theorem ext_cauchy_iff : ∀ {x y : Real}, x = y ↔ x.cauchy = y.cauchy
  | ⟨a⟩, ⟨b⟩ => by rw [ofCauchy.injEq]

theorem ext_cauchy {x y : Real} : x.cauchy = y.cauchy → x = y :=
  ext_cauchy_iff.2
```

然后是域结构：

```lean
noncomputable instance instField : Field ℝ where
  mul_inv_cancel := by
    rintro ⟨a⟩ h
    rw [mul_comm]
    simp only [← ofCauchy_inv, ← ofCauchy_mul, ← ofCauchy_one, ← ofCauchy_zero,
      Ne, ofCauchy.injEq] at *
    exact CauSeq.Completion.inv_mul_cancel h
  inv_zero := by simp [← ofCauchy_zero, ← ofCauchy_inv]
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
  nnratCast_def q := by
    rw [← ofCauchy_nnratCast, NNRat.cast_def, ofCauchy_div, ofCauchy_natCast, ofCauchy_natCast]
  ratCast_def q := by
    rw [← ofCauchy_ratCast, Rat.cast_def, ofCauchy_div, ofCauchy_natCast, ofCauchy_intCast]
```

### 实数的格结构

实数上的序和上下确界是这样定义的：

```lean
private irreducible_def lt : ℝ → ℝ → Prop
  | ⟨x⟩, ⟨y⟩ =>
    (Quotient.liftOn₂ x y (· < ·)) fun _ _ _ _ hf hg =>
      propext <|
        ⟨fun h => lt_of_eq_of_lt (Setoid.symm hf) (lt_of_lt_of_eq h hg), fun h =>
          lt_of_eq_of_lt hf (lt_of_lt_of_eq h (Setoid.symm hg))⟩
instance : LT ℝ :=
  ⟨lt⟩
private irreducible_def le (x y : ℝ) : Prop :=
  x < y ∨ x = y
instance : LE ℝ :=
  ⟨le⟩
private irreducible_def sup : ℝ → ℝ → ℝ
  | ⟨x⟩, ⟨y⟩ => ⟨Quotient.map₂ (· ⊔ ·) (fun _ _ hx _ _ hy => sup_equiv_sup hx hy) x y⟩
instance : Max ℝ :=
  ⟨sup⟩
private irreducible_def inf : ℝ → ℝ → ℝ
  | ⟨x⟩, ⟨y⟩ => ⟨Quotient.map₂ (· ⊓ ·) (fun _ _ hx _ _ hy => inf_equiv_inf hx hy) x y⟩
instance : Min ℝ :=
  ⟨inf⟩
```

类似于完备化中的加减乘除，这里也需要使用 `Quotient` 的 `liftOn₂` 和 `map₂` 相关函数来构造商映射。

有个定理将会反复用到：如果一个实数上的性质对所有从 Cauchy 列 mk 出来的实数都成立，那么对所有实数也成立（~~好像是废话？~~）

```lean
@[elab_as_elim]
protected theorem ind_mk {C : Real → Prop} (x : Real) (h : ∀ y, C (mk y)) : C x := by
  obtain ⟨x⟩ := x
  induction x using Quot.induction_on
  exact h _
```

关于序有以下定理，可以将对实数的比较化为对 Cauchy 列的比较（**注意很多被标记了 simp，所以后面证明的时候可能隐式地使用了这些定理**）

```lean
theorem lt_cauchy {f g} : (⟨⟦f⟧⟩ : ℝ) < ⟨⟦g⟧⟩ ↔ f < g :=
  show lt _ _ ↔ _ by rw [lt_def]; rfl

@[simp]
theorem mk_lt {f g : CauSeq ℚ abs} : mk f < mk g ↔ f < g :=
  lt_cauchy

@[simp]
theorem mk_pos {f : CauSeq ℚ abs} : 0 < mk f ↔ Pos f := by
  rw [← mk_zero, mk_lt]
  exact iff_of_eq (congr_arg Pos (sub_zero f))

@[simp]
theorem mk_le {f g : CauSeq ℚ abs} : mk f ≤ mk g ↔ f ≤ g := by
  simp only [le_def', mk_lt, mk_eq]; rfl
```

从而关于实数的性质可以用关于 Cauchy 列的性质证明：

```lean
instance partialOrder : PartialOrder ℝ where
  lt_iff_le_not_ge a b := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa using lt_iff_le_not_ge
  le_refl a := by
    induction a using Real.ind_mk
    rw [mk_le]
  le_trans a b c := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simpa using le_trans
  le_antisymm a b := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa [mk_eq] using CauSeq.le_antisymm

instance : DistribLattice ℝ where
  sup := (· ⊔ ·)
  le_sup_left := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    dsimp only; rw [← mk_sup, mk_le]
    exact CauSeq.le_sup_left
  le_sup_right := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    dsimp only; rw [← mk_sup, mk_le]
    exact CauSeq.le_sup_right
  sup_le := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simp_rw [← mk_sup, mk_le]
    exact CauSeq.sup_le
  inf := (· ⊓ ·)
  inf_le_left := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    dsimp only; rw [← mk_inf, mk_le]
    exact CauSeq.inf_le_left
  inf_le_right := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    dsimp only; rw [← mk_inf, mk_le]
    exact CauSeq.inf_le_right
  le_inf := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simp_rw [← mk_inf, mk_le]
    exact CauSeq.le_inf
  le_sup_inf := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    apply Eq.le
    simp only [← mk_sup, ← mk_inf]
    exact congr_arg mk (CauSeq.sup_inf_distrib_left ..).symm
```


## 实数的 Archimedean.lean 选讲

### 实数的 Archimedean 性质

首先 Archimedean 的定义是

```lean
/-- An ordered additive commutative monoid is called `Archimedean` if for any two elements `x`, `y`
such that `0 < y`, there exists a natural number `n` such that `x ≤ n • y`. -/
class Archimedean (M) [AddCommMonoid M] [PartialOrder M] : Prop where
  /-- For any two elements `x`, `y` such that `0 < y`, there exists a natural number `n`
  such that `x ≤ n • y`. -/
  arch : ∀ (x : M) {y : M}, 0 < y → ∃ n : ℕ, x ≤ n • y
```

关于 Archimedean 有如下定理

```lean
theorem archimedean_iff_rat_le : Archimedean K ↔ ∀ x : K, ∃ q : ℚ, x ≤ q :=
  archimedean_iff_rat_lt.trans
    ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
      let ⟨n, h⟩ := H x
      ⟨n + 1, lt_of_le_of_lt h (Rat.cast_lt.2 (lt_add_one _))⟩⟩
```

check: `∀ {K : Type u_4} [inst : Field K] [inst_1 : LinearOrder K] [IsStrictOrderedRing K],
  Archimedean K ↔ ∀ (x : K), ∃ q, x ≤ ↑q`

这个定理表明对于一个 `[Field K] [LinearOrder K] [IsStrictOrderedRing K]`，`K` 是 Archimedean 的当且仅当对任意 K 中的 x，存在有理数 q 使得 x ≤ q。

接下来的 instance 表明实数的确 Archimedean：

```lean
instance instArchimedean : Archimedean ℝ :=
  archimedean_iff_rat_le.2 fun x =>
    Real.ind_mk x fun f =>
      let ⟨M, _, H⟩ := f.bounded' 0
      ⟨M, mk_le_of_forall_le ⟨0, fun i _ => Rat.cast_le.2 <| le_of_lt (abs_lt.1 (H i)).2⟩⟩
noncomputable instance : FloorRing ℝ :=
  Archimedean.floorRing _
```

### 确界定理

这是 `Lean` 中与 “界” 相关的核心定义：

```lean
variable {α : Type*} [LE α]

/-- The set of upper bounds of a set. -/
def upperBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → a ≤ x }

/-- The set of lower bounds of a set. -/
def lowerBounds (s : Set α) : Set α :=
  { x | ∀ ⦃a⦄, a ∈ s → x ≤ a }

/-- A set is bounded above if there exists an upper bound. -/
def BddAbove (s : Set α) :=
  (upperBounds s).Nonempty

/-- A set is bounded below if there exists a lower bound. -/
def BddBelow (s : Set α) :=
  (lowerBounds s).Nonempty

/-- `a` is a least element of a set `s`; for a partial order, it is unique if exists. -/
def IsLeast (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ lowerBounds s

/-- `a` is a greatest element of a set `s`; for a partial order, it is unique if exists. -/
def IsGreatest (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ a ∈ upperBounds s

/-- `a` is a least upper bound of a set `s`; for a partial order, it is unique if exists. -/
def IsLUB (s : Set α) : α → Prop :=
  IsLeast (upperBounds s)

/-- `a` is a greatest lower bound of a set `s`; for a partial order, it is unique if exists. -/
def IsGLB (s : Set α) : α → Prop :=
  IsGreatest (lowerBounds s)
```

确界定理表明对任意 `s : Set ℝ`，如果 `s` 非空并且 `s` 有上界，则存在 `x` 使得 `x` 是 `s` 的上确界。
check: `∀ {s : Set ℝ}, s.Nonempty → BddAbove s → ∃ x, IsLUB s x`

证明的主要思路是对于每个 `d : ℕ`，考虑 `{ m : ℤ | ∃ y ∈ s, (m : ℝ) ≤ y * d }` 中最大者，也即将集合 `s` 逐点乘上 `d` 之后近似的上界。称这个函数为 `f`。`f d` 除以 `d` 之后就是对 `s` 的上界的一个精度为 `1 / d` 的有理数近似。这个 Cauchy 列（`f n / n`）即为所求。

```lean
theorem exists_isLUB (hne : s.Nonempty) (hbdd : BddAbove s) : ∃ x, IsLUB s x := by
  rcases hne, hbdd with ⟨⟨L, hL⟩, ⟨U, hU⟩⟩ -- L 是 s 中的某个元素，U 是 s 的一个上界
  have : ∀ d : ℕ, BddAbove { m : ℤ | ∃ y ∈ s, (m : ℝ) ≤ y * d } := by
    obtain ⟨k, hk⟩ := exists_int_gt U
    refine fun d => ⟨k * d, fun z h => ?_⟩
    rcases h with ⟨y, yS, hy⟩
    refine Int.cast_le.1 (hy.trans ?_)
    push_cast
    exact mul_le_mul_of_nonneg_right ((hU yS).trans hk.le) d.cast_nonneg
  choose f hf using fun d : ℕ => 
  -- exists_greatest_of_bdd 用于对一个谓词 P，给定 P 真的集合有上界，且 P 真的集合非空，说明 P 真的集合有最大元
  -- Int.exists_greatest_of_bdd {P : ℤ → Prop} (Hbdd : ∃ b, ∀ (z : ℤ), P z → z ≤ b) (Hinh : ∃ z, P z) : ∃ ub, P ub ∧ ∀ (z : ℤ), P z → z ≤ ub
    Int.exists_greatest_of_bdd (this d) ⟨⌊L * d⌋, L, hL, Int.floor_le _⟩ -- 第一个参数是刚 have 的，P m 就是 ∃ y ∈ s, (m : ℝ) ≤ y * d
  -- 证明 f n / n 不比 s 的所有元素都大
  have hf₁ : ∀ n > 0, ∃ y ∈ s, ((f n / n : ℚ) : ℝ) ≤ y := fun n n0 =>
    let ⟨y, yS, hy⟩ := (hf n).1
    ⟨y, yS, by simpa using (div_le_iff₀ (Nat.cast_pos.2 n0 : (_ : ℝ) < _)).2 hy⟩
  -- 证明 f n / n 在 1 / n 精度下是上界
  have hf₂ : ∀ n > 0, ∀ y ∈ s, (y - ((n : ℕ) : ℝ)⁻¹) < (f n / n : ℚ) := by
    intro n n0 y yS
    have := (Int.sub_one_lt_floor _).trans_le (Int.cast_le.2 <| (hf n).2 _ ⟨y, yS, Int.floor_le _⟩)
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, gt_iff_lt]
    rwa [lt_div_iff₀ (Nat.cast_pos.2 n0 : (_ : ℝ) < _), sub_mul, inv_mul_cancel₀]
    exact ne_of_gt (Nat.cast_pos.2 n0)
  -- 证明 f n / n IsCauSeq
  have hg : IsCauSeq abs (fun n => f n / n : ℕ → ℚ) := by
    intro ε ε0
    suffices ∀ j ≥ ⌈ε⁻¹⌉₊, ∀ k ≥ ⌈ε⁻¹⌉₊, (f j / j - f k / k : ℚ) < ε by
      refine ⟨_, fun j ij => abs_lt.2 ⟨?_, this _ ij _ le_rfl⟩⟩
      rw [neg_lt, neg_sub]
      exact this _ le_rfl _ ij
    intro j ij k ik
    replace ij := le_trans (Nat.le_ceil _) (Nat.cast_le.2 ij)
    replace ik := le_trans (Nat.le_ceil _) (Nat.cast_le.2 ik)
    have j0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ij)
    have k0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ik)
    rcases hf₁ _ j0 with ⟨y, yS, hy⟩
    refine lt_of_lt_of_le ((Rat.cast_lt (K := ℝ)).1 ?_) ((inv_le_comm₀ ε0 (Nat.cast_pos.2 k0)).1 ik)
    simpa using sub_lt_iff_lt_add'.2 (lt_of_le_of_lt hy <| sub_lt_iff_lt_add.1 <| hf₂ _ k0 _ yS)
  -- 直接用 f n / n 定义一个 CauSeq 出来
  let g : CauSeq ℚ abs := ⟨fun n => f n / n, hg⟩ -- 记得 CauSeq 是一个子类型，由 val 和 property 组成
  refine ⟨mk g, ⟨fun x xS => ?_, fun y h => ?_⟩⟩ -- 记得结论是 ∃ x, IsLUB s x，其中 mk g 用于填入 x，第一个函数用于证明其确实是上界，第二个函数用于证明最小上界
  -- 假设：xS : x ∈ s；目标：x ≤ mk g
  -- le_of_forall_lt_imp_le_of_dense.{u_2} {α : Type u_2} [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α} (h : ∀ a < a₂, a ≤ a₁) : a₂ ≤ a₁
  · refine le_of_forall_lt_imp_le_of_dense fun z xz => ?_ 
    obtain ⟨K, hK⟩ := exists_nat_gt (x - z)⁻¹ -- (x - z)⁻¹ < ↑K，或者用自然语言说，1/K < x - z
    -- 新假设：z < x；新目标：z ≤ mk g
    refine le_mk_of_forall_le ⟨K, fun n nK => ?_⟩
    -- 只需证明对 n ≥ K，序列 g 的第 n 项大于等于 z，这几乎就是 hf₂
    replace xz := sub_pos.2 xz
    replace hK := hK.le.trans (Nat.cast_le.2 nK)
    have n0 : 0 < n := Nat.cast_pos.1 ((inv_pos.2 xz).trans_le hK)
    refine le_trans ?_ (hf₂ _ n0 _ xS).le
    rwa [le_sub_comm, inv_le_comm₀ (Nat.cast_pos.2 n0 : (_ : ℝ) < _) xz]
  -- 假设：y ∈ upperBounds s；目标：mk g ≤ y
  · exact
      mk_le_of_forall_le 
        -- 目标现在是 ∃ i, ∀ j ≥ i, ↑(↑g j) ≤ y
        ⟨1, fun n n1 =>
          let ⟨x, xS, hx⟩ := hf₁ _ n1
          le_trans hx (h xS)⟩
```