Group 4: 程俊尧，张杰涵，褚天澄，张博山
---
# Urysohn's Metrization Theorem

## T0, T1, T2, T3, T4空间

### T0空间 T0 Spaces
T0空间：一个拓扑空间X被称为是T0的，当且仅当∀x, y ∈ X, ∃x的邻域U不包含y或者y的邻域V不包含x。

然而lean中没有按照如上的传统定义，而是采用了如下方法：

首先定义“两个点不可分离”：在拓扑空间X中，点x,y被称为不可分离的，当且仅当任意含有x的开集都包含y，且任意包含y的开集都包含x。

然后定义T0空间：一个拓扑空间X被称为T0的，当且仅当X中不存在不可分离的两点。

位置：Mathlib.Topology.Separation
文件：Basic.lean

```lean
class T0Space (X : Type u) [TopologicalSpace X] : Prop where
  t0 : ∀ ⦃x y : X⦄, Inseparable x y → x = y
```

### T1空间 T1 Spaces
T1空间：一个拓扑空间X被称为是T1的，当且仅当∀x, y ∈ X且x≠y，∃x的邻域U不包含y，同时∃y的邻域V不包含x。

lean中并未直接采用上述“双向邻域分离”的传统定义，而是采用了如下更简洁的等价刻画：

我们有这个基本定理：拓扑空间X是T1的，当且仅当X中的每个单点集都是闭集）。

由此定义T1空间：一个拓扑空间X被称为T1的，当且仅当对X中任意一点x，由x构成的单点集{x}是闭集。

位置：Mathlib.Topology.Separation
文件：Basic.lean

```lean
class T1Space(X : Type u) [TopologicalSpace X] : Prop where
  t1 (x : X) : IsClosed {x}
```

## T2空间 T2 Spaces
T2空间（豪斯多夫空间）：一个拓扑空间X被称为是T2的，当且仅当∀x, y ∈ X且x≠y，存在x的邻域U和y的邻域V，满足U与V不相交（U ∩ V = ∅）。

lean中直接采用了这一核心的“不相交开邻域分离”定义。

位置：Mathlib.Topology.Separation
文件：Hausdorff.lean

```lean
class T2Space(X : Type u) [TopologicalSpace X] : Prop where
  t2 : Pairwise fun (x y : X) => ∃ (u : Set X) (v : Set X), IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ Disjoint u v
```

## 正则空间 Regular Spaces
正则空间：一个拓扑空间 X 被称为是正则的，当且仅当对任意闭集 s 和不在 s 中的点 a，存在不相交的开集 U 和 V，使得 s⊆U 且 a∈V。

lean 中没有直接采用 “存在不相交开集分离闭集与点” 的直观表述，而是基于滤子（Filter）的不交性来刻画，具体设计如下：
首先明确核心等价性质：拓扑空间 X 是正则的，当且仅当对任意闭集 s 和点 a∉s，闭集 s 的邻域滤子（𝓝ˢ s）与点 a 的邻域滤子（𝓝 a）是不交的（Disjoint）。

然后定义正则空间：一个拓扑空间 X 被称为正则的，当且仅当对 X 中任意闭集 s 和点 a∉s，s 的邻域滤子与 a 的邻域滤子满足不交性。

位置：Mathlib.Topology.Separation
文件：Regular.lean

```lean
class RegularSpace(X : Type u) [TopologicalSpace X] : Prop where
  regular {s : Set X} {a : X} : IsClosed s → a ∉ s → Disjoint (nhdsSet s) (nhds a)
```

### T3空间 T3 Spaces
T3空间：一个拓扑空间X被称为是T3的，当且仅当X既是T0空间，又是正则空间（Regular Space）。等价的直观定义为：X是T1空间且正则（因T3空间可推导为T1，进而满足T0），即对任意闭集s和不在s中的点a，存在不相交的开集分离s与a，且任意不同点可被单向邻域分离。

lean中定义 T3 空间：一个拓扑空间 X 被称为 T3 的，当且仅当 X 同时满足 T0 空间的 “不可分离点必相等” 公理，以及正则空间的 “闭集与点的邻域滤子不交” 公理。

位置：Mathlib.Topology.Separation
文件：Regular.lean

```lean
class T3Space(X : Type u) [TopologicalSpace X] extends T0Space X, RegularSpace X : Prop where
  t0 ⦃x y : X⦄ : Inseparable x y → x = y
  regular {s : Set X} {a : X} : IsClosed s → a ∉ s → Disjoint (nhdsSet s) (nhds a)
```

### 正规空间 Normal Space
正规空间：一个拓扑空间X被称为是正规的，当且仅当对任意两个不相交的闭集s和t，存在不相交的开集U和V，使得s⊆U且t⊆V。

lean中以“不交闭集存在分离邻域”为核心，通过谓词组合刻画正规空间，具体设计如下：

首先明确核心分离性质：拓扑空间X是正规的，当且仅当对X中任意两个闭集s、t，若s与t不交，则存在满足`SeparatedNhds s t`的开邻域。

然后定义正规空间：一个拓扑空间X被称为正规的，当且仅当对X中任意闭集s和t，若s∩t=∅，则s和t拥有分离的邻域。

位置：Mathlib.Topology.Separation
文件：Regular.lean

```lean
class NormalSpace(X : Type u) [TopologicalSpace X] : Prop where
  normal (s t : Set X) : IsClosed s → IsClosed t → Disjoint s t → SeparatedNhds s t
```
### T4空间 T4 Spaces
T4空间：一个拓扑空间X被称为是T4的，当且仅当X既是T1空间，又是正规空间（Normal Space）。等价的直观定义为：X中任意两个不相交的闭集可被不相交的开邻域分离，且任意单点集都是闭集。

lean中通过「继承T1空间和正规空间」的方式定义T4空间，直接复用两类空间的核心公理，无额外新增条件，具体设计如下：

首先明确核心构成：T4空间是T1空间与正规空间的结合，继承了T1空间“单点集为闭集”和正规空间“不交闭集可被开邻域分离”的全部性质。

然后定义T4空间：一个拓扑空间X被称为T4的，当且仅当X同时满足T1空间的单点闭集公理，以及正规空间的不交闭集分离邻域公理。

位置：Mathlib.Topology.Separation
文件：Regular.lean

```lean
class T4Space(X : Type u) [TopologicalSpace X] extends T1Space X, NormalSpace X : Prop where
  t1 (x : X) : IsClosed {x}
  normal (s t : Set X) : IsClosed s → IsClosed t → Disjoint s t → SeparatedNhds s t
```


## Pseudometric spaces

Distance is a real function of two variables.
It is defined in Lean as following:
`Mathlib.Topology.MetricSpace.Pseudo.Defs`
```lean
class Dist (α : Type*) where
  /-- Distance between two points -/
  dist : α → α → ℝ
```

A pseudometric space $(X, d)$ is a set $X$ together with a real-valued function $d:X \times X \longrightarrow \mathbb{R}$, called a pseudometric, such that for every $x, y, z \in X$,
+ Non-negative: $d(x,y) \geq 0$ and $d(x,x) = 0$
+ Symmetry: $d(x,y) = d(y,x)$
+ Triangle Inequality: $d(x,z) \leq d(x,y) + d(y,z)$

Unlike a metric space, points in a pseudometric space need not be distinguishable; that is, one may have $d(x,y) = 0$ even though $x \neq y$.
The definition of pseudometric spaces in Lean is as following:
`Mathlib.Topology.MetricSpace.Pseudo.Defs`
```lean
class PseudoMetricSpace (α : Type u) : Type u extends Dist α where
  dist_self : ∀ x : α, dist x x = 0
  dist_comm : ∀ x y : α, dist x y = dist y x
  dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z
  ...
```

## Metric spaces

Metric space is a pseudometric space with all $d(x,y) > 0$ whenever $x \neq y$.
`Mathlib.Topology.MetricSpace.Defs`
```lean
class MetricSpace (α : Type u) : Type u extends PseudoMetricSpace α where
  eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y
```

For instance, $\mathbb{R}$ is a metric space.
`Mathlib.Topology.MetricSpace.Basic`
```lean
/-- Instantiate the reals as a metric space. -/
instance Real.metricSpace : MetricSpace ℝ := .ofT0PseudoMetricSpace ℝ
```

Two metric space structures are the same if they have the same distance function.
`Mathlib.Topology.MetricSpace.Defs`
```lean
theorem MetricSpace.ext {α : Type*} {m m' : MetricSpace α} (h : m.toDist = m'.toDist) :
    m = m' := by
  cases m; cases m'; congr; ext1; assumption
```

The following constructs a metric space structure whose underlying topological space structure (definitionally) agrees which a pre-existing topology which is compatible with a given distance function.
`Mathlib.Topology.MetricSpace.Defs`
```lean
def MetricSpace.ofDistTopology {α : Type u} [TopologicalSpace α] (dist : α → α → ℝ)
    (dist_self : ∀ x : α, dist x x = 0) (dist_comm : ∀ x y : α, dist x y = dist y x)
    (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
    (H : ∀ s : Set α, IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, dist x y < ε → y ∈ s)
    (eq_of_dist_eq_zero : ∀ x y : α, dist x y = 0 → x = y) : MetricSpace α :=
  { PseudoMetricSpace.ofDistTopology dist dist_self dist_comm dist_triangle H with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero _ _ }
```

Following are some theorems concerning the relationship between $d(x,y) = 0$ and $x = y$.
`Mathlib.Topology.MetricSpace.Defs`
```
variable {γ : Type w} [MetricSpace γ]
theorem eq_of_dist_eq_zero {x y : γ} : dist x y = 0 → x = y := MetricSpace.eq_of_dist_eq_zero
theorem dist_eq_zero {x y : γ} : dist x y = 0 ↔ x = y := by sorry
theorem zero_eq_dist {x y : γ} : 0 = dist x y ↔ x = y := by sorry
theorem dist_ne_zero {x y : γ} : dist x y ≠ 0 ↔ x ≠ y := by sorry
theorem dist_le_zero {x y : γ} : dist x y ≤ 0 ↔ x = y := by sorry
theorem dist_pos {x y : γ} : 0 < dist x y ↔ x ≠ y := by sorry
theorem eq_of_forall_dist_le {x y : γ} (h : ∀ ε > 0, dist x y ≤ ε) : x = y := by sorry
...
```

## Bolzano-Weierstrass Theorem

Here are two versions of Bolzano-Weierstrass Theorem: In a proper metric space (e.g. $ℝ^n$), every bounded sequence has a converging subsequence.
The first version assumes only that the sequence is frequently in some bounded set.
`Mathlib.Topology.MetricSpace.Sequences`
```lean
variable {X : Type*} [PseudoMetricSpace X]
variable [ProperSpace X] {s : Set X}
theorem tendsto_subseq_of_frequently_bounded (hs : IsBounded s) {x : ℕ → X}
    (hx : ∃ᶠ n in atTop, x n ∈ s) :
    ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  have hcs : IsSeqCompact (closure s) := hs.isCompact_closure.isSeqCompact
  have hu' : ∃ᶠ n in atTop, x n ∈ closure s := hx.mono fun _n hn => subset_closure hn
  hcs.subseq_of_frequently_in hu'
```

The second version needs that the sequence is always in the bounded set.
`Mathlib.Topology.MetricSpace.Sequences`
```lean
theorem tendsto_subseq_of_bounded (hs : IsBounded s) {x : ℕ → X} (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  tendsto_subseq_of_frequently_bounded hs <| Frequently.of_forall hx
```

## Bases for topologies

`Mathlib.Topology.Bases`

A topological basis on a topological space `t` is a collection of sets,
such that all open sets can be generated as unions of these sets, without the need to take
finite intersections of them.

* `Implementation`: Mathlib divides the definition of a basis of a topology space into three propositions:

```lean
structure IsTopologicalBasis (s : Set (Set α)) : Prop where

  /-- For every point `x`, the set of `t ∈ s` such that `x ∈ t` is directed downwards. -/

  exists_subset_inter : ∀ t₁ ∈ s, ∀ t₂ ∈ s, ∀ x ∈ t₁ ∩ t₂, ∃ t₃ ∈ s, x ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂

  /-- The sets from `s` cover the whole space. -/

  sUnion_eq : ⋃₀ s = univ

  /-- The topology is generated by sets from `s`. -/

  eq_generateFrom : t = generateFrom s
```

* `notation`: 
```lean
{s : Set (Set α)}, IsTopologicalBasis s
```

## Separable Space

`Mathlib.Topology.Bases`

* `Implementation`: A separable space is one with a countable dense subset:

```lean
@[mk_iff] class SeparableSpace : Prop where

  /-- There exists a countable dense set. -/

  exists_countable_dense : ∃ s : Set α, s.Countable ∧ Dense s
```

* `notation`: 
```lean
[SeparableSpace α]
```

## First-Countable

`Mathlib.Topology.Bases` `Mathlib.Order.Filter.CountablyGenerated` `Mathlib.Order.Filter.Defs` `Mathlib.Order.Filter.Basic`

* `Implementation`: A first-countable space is one in which every point has a countable neighborhood basis:

```lean
class _root_.FirstCountableTopology : Prop where
  /-- The filter `𝓝 a` is countably generated for all points `a`. -/
  nhds_generated_countable : ∀ a : α, (𝓝 a).IsCountablyGenerated

class IsCountablyGenerated (f : Filter α) : Prop where
  /-- There exists a countable set that generates the filter. -/
  out : ∃ s : Set (Set α), s.Countable ∧ f = generate s

structure Filter (α : Type*) where
  /-- The set of sets that belong to the filter. -/
  sets : Set (Set α)
  /-- The set `Set.univ` belongs to any filter. -/
  univ_sets : Set.univ ∈ sets
  /-- If a set belongs to a filter, then its superset belongs to the filter as well. -/
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  /-- If two sets belong to a filter, then their intersection belongs to the filter as well. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets

def generate (g : Set (Set α)) : Filter α where
  sets := {s | GenerateSets g s}
  univ_sets := GenerateSets.univ
  sets_of_superset := GenerateSets.superset
  inter_sets := GenerateSets.inter

inductive GenerateSets (g : Set (Set α)) : Set α → Prop
  | basic {s : Set α} : s ∈ g → GenerateSets g s
  | univ : GenerateSets g univ
  | superset {s t : Set α} : GenerateSets g s → s ⊆ t → GenerateSets g t
  | inter {s t : Set α} : GenerateSets g s → GenerateSets g t → GenerateSets g (s ∩ t)
```

* `key point`: Filters can well characterize various properties of neighborhoods

* `notation`:
```lean
[FirstCountableTopology α]
```

## Second-Countable

`Mathlib.Topology.Bases`

* `Implementation`: A second-countable space is one with a countable basis:

```lean
class _root_.SecondCountableTopology : Prop where

  /-- There exists a countable set of sets that generates the topology. -/

  is_open_generated_countable : ∃ b : Set (Set α), b.Countable ∧ t = TopologicalSpace.generateFrom b
```

* `notation`:
```lean
[SecondCountableTopology α]
```

## Lindelof

`Mathlib.Topology.Separation.Regular`

For any topological space `X` (of universe level u1) that is both regular and second-countable, `X` is a normal space.

```lean
NormalSpace.of_regularSpace_secondCountableTopology.{u_1} {X : Type u_1} [TopologicalSpace X] [RegularSpace X]
  [SecondCountableTopology X] : NormalSpace X
```

## Urysohn's Lemma

`Mathlib.Topology.UrysohnsLemma`

`X` is a topological space that is normal, and any two disjoint closed subsets s and t of X, there exists a continuous function f: `X`→`R` such that: 
* f equals 0 on the subset s (i.e., f(x)=0 for all x∈s);
* f equals 1 on the subset t (i.e., f(x)=1 for all x∈t);
* Every value of f lies within the closed interval [0,1] (i.e., 0≤f(x)≤1 for all x∈X).

```lean
exists_continuous_zero_one_of_isClosed.{u_1} {X : Type u_1} [TopologicalSpace X] [NormalSpace X] {s t : Set X}
  (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
  ∃ f, Set.EqOn (⇑f) 0 s ∧ Set.EqOn (⇑f) 1 t ∧ ∀ (x : X), f x ∈ Set.Icc 0 1
```


## Metrizable Space and Urysohn Metrization Theorem
position: ``Mathlib.Topology.ContinuousMap.Bounded``

file: ``Basic.lean``

position: ``Mathlib.Topology.Metrizable``

file: ``Basic.lean`` ``Urysohn.lean``

### Main Definition
- Bounded, continuous function space $l^{\infty}$

```lean
structure BoundedContinuousFunction (α : Type u) (β : Type v) [TopologicalSpace α]
    [PseudoMetricSpace β] : Type max u v extends ContinuousMap α β where
  map_bounded' : ∃ C, ∀ x y, dist (toFun x) (toFun y) ≤ C
```

`α →ᵇ β` is the type of bounded continuous functions `α → β` from a topological space to a metric space.

When possible, instead of parametrizing results over `(f : α →ᵇ β)`,
you should parametrize over `(F : Type*) [BoundedContinuousMapClass F α β] (f : F)`.

When you extend this structure, make sure to extend `BoundedContinuousMapClass`. 

- Metrizable space

```lean
class MetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop extends
    PseudoMetrizableSpace X, T0Space X

attribute [instance 100] MetrizableSpace.toT0Space
attribute [instance 100] MetrizableSpace.toPseudoMetrizableSpace

instance (priority := 100) PseudoMetrizableSpace.toMetrizableSpace
    [T0Space X] [h : PseudoMetrizableSpace X] : MetrizableSpace X where

instance (priority := 100) t2Space_of_metrizableSpace [MetrizableSpace X] : T2Space X :=
  letI : UniformSpace X := pseudoMetrizableSpaceUniformity X
  inferInstance

instance metrizableSpace_prod [MetrizableSpace X] [MetrizableSpace Y] :
    MetrizableSpace (X × Y) where
```


### Main theorems
- $C_2, T_3 \Rightarrow$ embedding $l^{\infty}$
```lean
variable (X : Type*) [TopologicalSpace X] [T3Space X] [SecondCountableTopology X]

theorem exists_embedding_l_infty : ∃ f : X → ℕ →ᵇ ℝ, IsEmbedding f :=
  let ⟨f, hf⟩ := exists_isInducing_l_infty X; ⟨f, hf.isEmbedding⟩

instance (priority := 90) metrizableSpace_of_t3_secondCountable : MetrizableSpace X :=
  let ⟨_, hf⟩ := exists_embedding_l_infty X
  hf.metrizableSpace
```
```lean
#check exists_embedding_l_infty     -- ⊢ ∀ (X : Type u_1) [inst : TopologicalSpace X] [T3Space X] [SecondCountableTopology X], ∃ f, Topology.IsEmbedding f
```

A T₃ topological space with second countable topology can be embedded into `l^∞ = ℕ →ᵇ ℝ`. 

*Urysohn's metrization theorem* (Tychonoff's version): a T₃ topological space with second
countable topology `X` is metrizable, i.e., there exists a metric space structure that generates the same topology.

- topology space embedding metrizable space, then it is also metrizable space.

```lean
theorem _root_.Topology.IsEmbedding.metrizableSpace [MetrizableSpace Y] {f : X → Y}
    (hf : IsEmbedding f) : MetrizableSpace X where
  toPseudoMetrizableSpace := hf.toIsInducing.pseudoMetrizableSpace
  toT0Space := hf.t0Space
```
```lean
#check _root_.Topology.IsEmbedding.metrizableSpace 
-- Topology.IsEmbedding.metrizableSpace.{u_2, u_3} {X : Type u_2} {Y : Type u_3} [TopologicalSpace X] [TopologicalSpace Y] [MetrizableSpace Y] {f : X → Y} (hf : Topology.IsEmbedding f) : MetrizableSpace X
```

- If s is a pseudo metrizable space and s is separable, then s is $C_2$ space.
```lean
theorem IsSeparable.secondCountableTopology [PseudoMetrizableSpace X] {s : Set X}
    (hs : IsSeparable s) : SecondCountableTopology s :=
  let ⟨u, hu, hs⟩ := hs
  have := hu.to_subtype
  have : SeparableSpace (closure u) :=
    ⟨Set.range (u.inclusion subset_closure), Set.countable_range (u.inclusion subset_closure),
      Subtype.dense_iff.2 <| by rw [← Set.range_comp, Set.val_comp_inclusion, Subtype.range_coe]⟩
  let := pseudoMetrizableSpaceUniformity (closure u)
  have := pseudoMetrizableSpaceUniformity_countably_generated (closure u)
  have := secondCountable_of_separable (closure u)
  (Topology.IsEmbedding.inclusion hs).secondCountableTopology
```
```lean
#check IsSeparable.secondCountableTopology
-- TopologicalSpace.IsSeparable.secondCountableTopology.{u_2} {X : Type u_2} [TopologicalSpace X] [PseudoMetrizableSpace X] {s : Set X} (hs : TopologicalSpace.IsSeparable s) : SecondCountableTopology ↑s
```