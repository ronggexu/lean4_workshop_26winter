# hw1 group_3

## 整环中的除法理论 (PID/UFD/ED) 在 Mathlib 中的形式化

### 目录位置与核心文件

该分支内容跨越了 `Mathlib/Algebra/` 和 `Mathlib/RingTheory/` 目录。其中`EuclideanDomain` 作为基础结构位于 `Algebra`，而 PID 和 UFD 位于 `RingTheory`。

**主线入口文件：**

1. `Mathlib/Algebra/EuclideanDomain/Basic.lean` - 欧几里得整环定义与基础性质 (Bézout 等)
2. `Mathlib/RingTheory/PrincipalIdealDomain.lean` - PID 理论
3. `Mathlib/RingTheory/UniqueFactorizationDomain.lean` - UFD 理论
4. `Mathlib/RingTheory/DedekindDomain/Basic.lean` - Dedekind 整环 (包含 PID 是 Dedekind 环的证明)
5. `Mathlib/RingTheory/Polynomial/GaussLemma.lean` - 高斯引理与多项式环的 UFD 性质

### 主要定义

#### 1. **EuclideanDomain** (欧几里得整环)

**基本概念**：

一个 `欧几里得整环R` 是一个具有除法和余数运算的非平凡交换环，满足 `b * (a / b) + a % b = a`。
通常来说，欧几里得整环的定义包含一个赋值函数 `R → ℕ`。Mathlib则使用良基关系 `r`，满足 `r (a % b) b` ，这推广了赋值函数。

```lean
class EuclideanDomain (R : Type u) extends CommRing R, Nontrivial R where
```

定义 `R` 上的除法函数（记作 `/`），满足性质 `b * (a / b) + a % b = a`，其中 `%` 表示取余运算。
  
```lean  
protected quotient : R → R → R
```

约定除以零的结果应始终为零。

```lean  
protected quotient_zero : ∀ a, quotient a 0 = 0
```

定义 `R` 上的余数函数（记作 `%`），满足性质 `b * (a / b) + a % b = a`，其中 `/` 表示求商运算。
  
```lean
protected remainder : R → R → R
```

联系除法函数与余数函数的性质。这使得我们能够计算最大公约数（GCD）和最小公倍数（LCM）。

```lean  
protected quotient_mul_add_remainder_eq : ∀ a b, b * quotient a b + remainder a b = a
```
  
定义 `R` 上的良基关系，满足 `r (a % b) b`。这确保最大公约数（GCD）算法总是能够终止。

```lean
protected r : R → R → Prop
r_wellFounded : WellFounded r
protected remainder_lt : ∀ (a) {b}, b ≠ 0 → r (remainder a b) b
```

`r`的额外约束。

```lean
mul_left_not_lt : ∀ (a) {b}, b ≠ 0 → ¬r (a * b) a
```

**基本性质**：

记号`≺`：

```lean
local infixl: " ≺ " => EuclideanDomain.r
```

取余：

```lean
theorem mod_eq_sub_mul_div {R : Type*} [EuclideanDomain R] (a b : R) : a % b = a - b * (a / b) :=
  calc
    a % b = b * (a / b) + a % b - b * (a / b) := (add_sub_cancel_left _ _).symm
    _ = a - b * (a / b) := by rw [div_add_mod]
```

整除：

```lean
theorem val_dvd_le : ∀ a b : R, b ∣ a → a ≠ 0 → ¬a ≺ b
  | _, b, ⟨d, rfl⟩, ha => mul_left_not_lt b (mt (by rintro rfl; exact mul_zero _) ha)
```

**备注**：

- 位于 `Mathlib.Algebra.EuclideanDomain`。
- 关键实例：`instance Int.euclideanDomain: EuclideanDomain ℤ`（整数环是欧几里得整环） 和 `instance Field.toEuclideanDomain{K : Type u_1} [Field K] : EuclideanDomain K`（域是欧几里得整环）。

#### 2. **PrincipalIdealRing** (主理想环) 和 **PID**

**定义方式**
对于主理想整环（PID），应当（组合）使用 [IsDomain R] 和 [IsPrincipalIdealRing R]。Mathlib 中并没有对 PID 的显式（统一）定义。

```lean
class IsPrincipalIdealRing (R : Type u) [CommRing R] : Prop where
  /-- 所有理想都是主理想 -/
  principal : ∀ (I : Ideal R), I.IsPrincipal
```

**关键接口**：
-生成元接口：对于一个主理想 S，Mathlib 提供了构造性接口来提取其生成元：
-- 如果 S 是主理想，则可以通过下式获取其生成元 g

```lean
g = Submodule.IsPrincipal.generator S
```

`Submodule.IsPrincipal` 接口：提供生成元 `generator` 和证明 `mem_iff_generator_mem`

**结构说明**：

- 格结构 (Lattice Structure) ：在 PID 中，理想构成了一个 complete_lattice。由于每个理想都是主理想，理想的交 I ⊓ J 和和 I + J 分别对应于生成元的最小公倍数（LCM）和最大公约数（GCD）生成的理想。

#### 3. **UniqueFactorizationMonoid** (唯一分解幺半群) 和 **UFD**

**定义方式**
UFD的定义继承自UFM，而UFM又继承自WfDvdMonoid（良基整除幺半群）

```lean

/-- WfDvdMonoid 的定义 -/
abbrev WfDvdMonoid (α : Type*) [CommMonoidWithZero α] : Prop :=
  IsWellFounded α DvdNotUnit
  /-- 这保证了任何分解过程都会终止，但不保证分解的存在性 -/

/-- UFM 的定义 -/
class UniqueFactorizationMonoid (α : Type*) [CommMonoidWithZero α] : Prop
    extends IsCancelMulZero α, IsWellFounded α DvdNotUnit where
    /-- 对乘法消去律 + 零乘性质、以及 WfDvdMonoid 的继承 -/
  protected irreducible_iff_prime : ∀ {a : α}, Irreducible a ↔ Prime a
  /-- UFM 的本质特征：不可约元 ↔ 素元 -/

/-- Mathlib4中没有单独的 UFD 类，而在实际使用过程中，可以这样构造 -/
structure UniqueFactorizationDomain (R : Type u) [CommRing R] [IsDomain R] extends
    UniqueFactorizationMonoid R : Prop
    /-- 即在 UFM 的基础上验证交换环和整环的性质 -/

```

**和常用定义的比较**
UFM 通过严格整除关系以及不可约元和素元的等价性定义，但这等价于我们更熟悉的定义：

- 每个非零元素可以唯一地表示为不可约因子的多重集，其中唯一性仅在相伴元素的意义下成立。
- 每个非零元素可以非唯一地表示为素因子的多重集。

而在lean中，有 UFM 满足这两个性质的定理以及证明：

```lean
/-- 非零元素可以唯一地表示为不可约因子的多重集 -/
theorem factors_unique {f g : Multiset α} (hf : ∀ x ∈ f, Irreducible x)
    (hg : ∀ x ∈ g, Irreducible x) (h : f.prod ~ᵤ g.prod) : Multiset.Rel Associated f g :=
  prime_factors_unique (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hf x hx))
    (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hg x hx)) h

/-- UFM 等价于非零元素可以非唯一地表示为素因子的多重集 -/
theorem UniqueFactorizationMonoid.iff_exists_prime_factors [CommMonoidWithZero α]
    [IsCancelMulZero α] :
    UniqueFactorizationMonoid α ↔
      ∀ a : α, a ≠ 0 → ∃ f : Multiset α, (∀ b ∈ f, Prime b) ∧ f.prod ~ᵤ a :=
  ⟨fun h => @UniqueFactorizationMonoid.exists_prime_factors _ _ h,
    UniqueFactorizationMonoid.of_exists_prime_factors⟩
```

### 主要定理

#### 定理 1: **包含关系链 (ED ⇒ PID ⇒ UFD)**

- **ED ⇒ PID**: `EuclideanDomain.to_principal_ideal_domain`
- 位于 `mathlib4/Mathlib/RingTheory/PrincipalIdealDomain.lean`。

```lean
instance (priority := 100) EuclideanDomain.to_principal_ideal_domain : IsPrincipalIdealRing R where
  principal S := by classical exact
    ⟨if h : { x : R | x ∈ S ∧ x ≠ 0 }.Nonempty then
        have wf : WellFounded (EuclideanDomain.r : R → R → Prop) := EuclideanDomain.r_wellFounded
        have hmin : WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h ∈ S ∧
            WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h ≠ 0 :=
          WellFounded.min_mem wf { x : R | x ∈ S ∧ x ≠ 0 } h
        ⟨WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h,
          Submodule.ext fun x => ⟨fun hx =>
            div_add_mod x (WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h) ▸
              (Ideal.mem_span_singleton.2 <| dvd_add (dvd_mul_right _ _) <| by
                have : x % WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h ∉
                    { x : R | x ∈ S ∧ x ≠ 0 } :=
                  fun h₁ => WellFounded.not_lt_min wf _ h h₁ (mod_lt x hmin.2)
                have : x % WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h = 0 := by
                  simp only [not_and_or, Set.mem_setOf_eq, not_ne_iff] at this
                  exact this.neg_resolve_left <| (mod_mem_iff hmin.1).2 hx
                simp [*]),
              fun hx =>
                let ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hx
                hy.symm ▸ S.mul_mem_right _ hmin.1⟩⟩
      else ⟨0, Submodule.ext fun a => by
            rw [← @Submodule.bot_coe R R _ _ _, span_eq, Submodule.mem_bot]
            exact ⟨fun haS => by_contra fun ha0 => h ⟨a, ⟨haS, ha0⟩⟩,
              fun h₁ => h₁.symm ▸ S.zero_mem⟩⟩⟩
```

**对应自然语言**：
`“对于任意欧几里得整环 R，它是一个主理想环。”`
**第一步**：处理`非零理想`

```lean
if h : { x : R | x ∈ S ∧ x ≠ 0 }.Nonempty then
```

如果理想 S 包含非零元素（即 S 不是零理想）
**第二步**：选取`生成元`

```lean
WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h
```

从 S 的所有非零元素中，选取一个**最小**的元素（这里的“最小”是按照欧几里得整环中的良序关系来比较的）
**第三步**：证明这个最小元素生成整个理想
设选取的最小元素为 `a`，需要证明 `S = (a)`（即由 a 生成的主理想）
**一方面**证明 `(a) ⊆ S`：

- 因为 a ∈ S，所以 a 的所有倍数都在 S 中（理想对乘法封闭）

**另一方面**证明 `S ⊆ (a)`：
对任意 x ∈ S：

1. 用 a 除 x：`x = q * a + r`（带余除法）
2. 余数 r 满足：r = 0 或 φ(r) < φ(a)（φ 是欧几里得函数）
3. 由于 r = x - q*a  ∈ S（因为 x ∈ S，q*a ∈ S）
4. 如果 r ≠ 0，则 r 是 S 中比 a 更小的非零元素，这与 a 的最小性矛盾
5. 因此 r = 0，所以 x = q*a ∈ (a)

**第四步**：处理`零理想`的情况

```lean
else ⟨0, ...⟩
```

- 如果 S 不包含非零元素（即 S 是零理想）
- 那么 S = (0)，显然也是主理想

**综上，**
我们证明了欧几里得整环是主理想整环。
在 Lean 中，这个证明被实现为一个`类型类实例`（priority := 100 表示高优先级），意味着在 Lean 中，只要一个环被声明为欧几里得整环，系统会自动知道它也是主理想环。

- **PID ⇒ UFD**: `PrincipalIdealDomain.toUniqueFactorizationDomain`
- 位于 `Mathlib/RingTheory/PrincipalIdealDomain.lean`。

```lean
instance (priority := 100) to_uniqueFactorizationMonoid : UniqueFactorizationMonoid R :=
  { (IsNoetherianRing.wfDvdMonoid : WfDvdMonoid R) with
    irreducible_iff_prime := irreducible_iff_prime }
-- 类型：PrincipalIdealDomain R → UniqueFactorizationDomain R
```

**对应自然语言**: 主理想整环 (PID) 是唯一分解整环 (UFD)。证明：PID 是诺特环 ⇒ 存在因子分解；PID 中不可约元生成极大理想 ⇒ 不可约元是素元。

#### 定理 2: **是UFD的Dedekind Domain是PID**

```lean
theorem IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid
    (R : Type*) [CommRing R] [IsDedekindDomain R] [UniqueFactorizationMonoid R] :
    IsPrincipalIdealRing R := by
  refine .of_prime_ne_bot fun P hp hp₀ ↦ ?_
  obtain ⟨x, hx₁, hx₂⟩ := hp.exists_mem_prime_of_ne_bot hp₀
  suffices Ideal.span {x} = P from this ▸ inferInstance
  have := (Ideal.span_singleton_prime hx₂.ne_zero).mpr hx₂
  exact (Ring.DimensionLeOne.prime_le_prime_iff_eq (by aesop)).mp <|
    P.span_singleton_le_iff_mem.mpr hx₁
--类型：∀ (R : Type u_2) [inst : CommRing R] [inst_1 : IsDedekindDomain R] [UniqueFactorizationMonoid R], IsPrincipalIdealRing R
```

**对应自然语言**: 任何是一个唯一分解整环 (UFD) 的 Dedekind 整环必定是一个主理想整环 (PID)。

#### 定理 3: **UFD 中的 Gauss 引理**

实际上， Mathlib 中并没有直接给出 UFD 中的 Gauss 引理，而是在 NormalizedGCDMonoid （归一化GCD幺半群）中。但是 NormalizedGCDMonoid 包含 UFD 。

```lean

/-- Gauss 引理内容及其证明 -/
variable [NormalizedGCDMonoid R]
noncomputable instance (priority := 100) normalizedGcdMonoid : NormalizedGCDMonoid R[X] :=
  letI := Classical.decEq R
  normalizedGCDMonoidOfExistsLCM fun p q => by
    rcases exists_primitive_lcm_of_isPrimitive p.isPrimitive_primPart
        q.isPrimitive_primPart with
      ⟨r, rprim, hr⟩
    refine ⟨C (lcm p.content q.content) * r, fun s => ?_⟩
    by_cases hs : s = 0
    · simp [hs]
    by_cases hpq : C (lcm p.content q.content) = 0
    · rw [C_eq_zero, lcm_eq_zero_iff, content_eq_zero_iff, content_eq_zero_iff] at hpq
      rcases hpq with (hpq | hpq) <;> simp [hpq, hs]
    iterate 3 rw [dvd_iff_content_dvd_content_and_primPart_dvd_primPart hs]
    nontriviality R
    rw [content_mul, rprim.content_eq_one, mul_one, content_C, normalize_lcm, lcm_dvd_iff,
      primPart_mul (mul_ne_zero hpq rprim.ne_zero), rprim.primPart_eq,
      (isUnit_primPart_C (lcm p.content q.content)).mul_left_dvd, ← hr s.primPart]
    tauto

```

**对应自然语言**：对于NormalizedGCDMonoid R，多项式环R[X]是NormalizedGCDMonoid。

#### 定理 4: **Bézout 定理（PID 版本）**

```lean
theorem exists_gcd_eq_mul_add_mul (a b : R) : ∃ x y, gcd a b = a * x + b * y := by
  rw [← gcd_dvd_iff_exists]
--类型: ∀ {R : Type u} [inst : CommRing R] [IsBezout R] [inst_2 : IsDomain R] [inst_3 : GCDMonoid R] (a b : R),
  ∃ x y, gcd a b = a * x + b * y
```

**对应自然语言**：在 PID 中，任意两个元素 a, b 的最大公因子可以表示为它们的线性组合。特殊地，在欧几里得整环中可以通过扩展欧几里得算法显式计算。

### 形式化中的细微差别：构造性与经典逻辑 (Constructive vs Classical Logic)

在纸笔数学中，我们通常认为“欧几里得整环是主理想整环”是理所当然的，且很少区分两者的计算性质。但在 Lean 的形式化中，**EuclideanDomain (ED)** 和 **PrincipalIdealRing (PID)** 代表了两种截然不同的数学范式：前者侧重于**计算 (Computation)**，后者侧重于**存在性 (Existence)**。

#### 1. EuclideanDomain：数据与算法 (Data & Algorithms)

`EuclideanDomain` 是一个携带**数据 (Data)** 的类型类。
当我们在 Lean 中声明 `[EuclideanDomain R]` 时，我们不仅断言该环性质成立，还必须显式提供计算除法和余数的**函数**：

- `div : R → R → R` (`/`)
- `mod : R → R → R` (`%`)

**构造性特征**：
由于提供了具体的函数实现，Mathlib 中的 `EuclideanDomain` 能够生成可执行代码。这意味着：

- 最大公约数 `gcd a b` 是通过欧几里得算法**计算**出来的。
- 贝祖等式（Bézout's identity）中的系数 `x, y` 是通过扩展欧几里得算法**构造**出来的。
- 这一切在逻辑上通常是可判定的（Decidable）和可计算的（Computable）。

#### 2. PrincipalIdealRing：命题与选择 (Propositions & Choice)

相比之下，`IsPrincipalIdealRing` 是一个**命题 (Prop)** 类。
它的定义核心在于存在量词 `∃`：

```lean
principal : ∀ (I : Ideal R), I.IsPrincipal
-- 其中 I.IsPrincipal 定义为 ∃ g, I = span {g}
```

### 尚未形式化的部分 / TODO

虽然核心理论已完成，但以下特定方向仍有待补充：

1. **非欧几里得 PID 的具体反例构造**：
    - 虽然理论上已知 $\mathbb{Z}[(1+\sqrt{-19})/2]$ 是 PID 但不是 ED，但 Mathlib 中可能缺乏针对该特定环“不是 ED”的直接断言证明（即证明不存在满足条件的 `r` 函数）。  
2. **高效的可计算性 (Computability)**：
    - 目前的 `UniqueFactorizationDomain` 侧重于存在性证明（使用 `Classical.choice`）。
    - 对于具体环（如 `ℤ[X]`）的高效分解算法（如 Berlekamp 算法或 Zassenhaus 算法）尚未完全集成到核心库的默认实例中。
3. **类域论 (Class Field Theory) 的深层连接**：
    - 理想类群 (Class Group) 的计算与 PID 判定（类数为 1 $\iff$ PID）已形式化，但针对具体数域的类数计算自动化工具（Tactic）仍在开发中。
