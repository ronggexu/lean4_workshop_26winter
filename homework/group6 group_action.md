# Maths in Lean: Group Actions

## 1. Introduction
The theory of group actions (`MulAction` and `AddAction`) in mathlib provides a comprehensive framework for groups and monoids acting on sets. This domain bridges algebra and geometry. While the core typeclasses are defined in `Mathlib.GroupTheory.GroupAction.Defs`, the theory is fully developed across a hierarchy of files involving orbits, stabilizers, and quotient structures.

## 2. File Organization
The following "core" modules form a linear chain of imports.

*   `Mathlib.GroupTheory.GroupAction.Defs`: Core typeclasses like `MulAction` and `AddAction`.
*   `Mathlib.GroupTheory.GroupAction.Basic`: Geometric and algebraic structures arising from actions (Orbits, Stabilizers, Fixed Points).
*   `Mathlib.GroupTheory.GroupAction.Quotient`: Advanced theorems relating orbits to quotient groups, including the Orbit-Stabilizer theorem and Burnside's Lemma.

> **Note:** The library uses the `to_additive` attribute extensively. Theorems proved for multiplicative actions (`•`) are automatically translated to additive actions (`+ᵥ`), saving significant code duplication.

## 3. Main Definitions and Structures

### The Action Class
The fundamental class is `MulAction M α`, which extends `SMul`. It requires `one_smul` and `mul_smul`.

*   **Notation**: The standard notation is `•` (`\smul`) for multiplicative actions.

### Orbits
For an action of `M` on `α`, the orbit of `a` is the set of elements reachable from `a`.

```lean
variable {G α : Type*} [Group G] [MulAction G α]
def properOrbit (a : α) : Set α :=
  Set.range (fun g : G => g • a)
```

*   **Implementation Note**: It is implemented as the `range` of the action map.
*   **Structure**: Since `orbit` returns a `Set α`, it inherits all set-theoretic operations (union, intersection, etc.).
*   **Orbit Relation**: `MulAction.orbitRel M α` is defined as a `Setoid α`. This **instance** allows us to form the quotient type `orbitRel.Quotient M α` (the space of orbits).

### Stabilizers
The stabilizer of an element `a` is the set of group elements fixing `a`.

```lean
def MulAction.stabilizer(G : Type u_1) {α : Type u_2} [Group G] [MulAction G α] (a : α) : Subgroup G
```

*   **Key Structure/Instance**: The stabilizer is defined as a **`Subgroup G`**. This is crucial because it automatically provides a **`Group` instance** for the stabilizer, allowing us to talk about its order, subgroups, and quotients.

### Fixed Points
The set of elements fixed by the entire group.

```lean
def fixedPoints (M : Type*) (α : Type*) [Monoid M] [MulAction M α] : Set α :=
  { x : α | ∀ m : M, m • x = x }
```



### Quotient Action

An interesting definition found in the `Quotient` file is the `QuotientAction` class.

```lean
class MulAction.QuotientAction {α : Type u}  (β : Type v)  [Group α]  [Monoid β]  [MulAction β α] (H : Subgroup α) : Prop
```

*   **Purpose**: This `Prop`-valued typeclass ensures that an action descends to a quotient group. It formalizes the "well-definedness" check required when defining operations on quotient structures.

## 4. Main Theorems

Mathlib covers both structural properties and counting theorems.

### Basic Properties (Transitivity & Conjugation)

**Transitivity as a Quotient Property:**
An action is transitive if and only if there is exactly one orbit.

```lean
#check (MulAction.pretransitive_iff_subsingleton_quotient (G := G) (α := α) :
  MulAction.IsPretransitive G α ↔ Subsingleton (MulAction.orbitRel.Quotient G α))
```

**Conjugate Stabilizers:**
Stabilizers of points in the same orbit are conjugate subgroups.

```lean
#check (MulAction.stabilizer_smul_eq_stabilizer_map_conj (G := G) (a := α) :
  ∀ (g : G) (a : α), MulAction.stabilizer G (g • a) = (MulAction.stabilizer G a).map (MulAut.conj g).toMonoidHom)
```
*   **Correspondence**: $Stab(g \cdot a) = g \cdot Stab(a) \cdot g^{-1}$.

### The Orbit-Stabilizer Theorem
This theorem appears in two forms in `Mathlib.GroupTheory.GroupAction.Quotient`.

**1. Structural Bijection:**
There is a canonical equivalence between the orbit of `b` and the quotient of the group by the stabilizer of `b`.

```lean
noncomputable def noncomputable def orbitEquivQuotientStabilizer (b : α) :
  MulAction.orbit G b ≃ G ⧸ MulAction.stabilizer G b :=
  MulAction.orbitEquivQuotientStabilizer G b
```
*   **Correspondence**: $\text{Orb}(b) \cong G / \text{Stab}(b)$.

**2. Cardinality Formula:**
For finite groups, the product of the sizes equals the group order.

```lean
#check (MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := G) :
  ∀ (b : α) [Fintype (MulAction.orbit G b)] [Fintype (MulAction.stabilizer G b)],
  Fintype.card (MulAction.orbit G b) * Fintype.card (MulAction.stabilizer G b) = Fintype.card G)
```
*   **Correspondence**: $|O_b| \cdot |G_b| = |G|$.

### Burnside's Lemma
The number of orbits is the average number of fixed points.

```lean
#check (MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (G := G) (α := α) :
  (∑ a : G, Fintype.card (MulAction.fixedBy α a)) =
  Fintype.card (MulAction.orbitRel.Quotient G α) * Fintype.card G)
```
*   **Correspondence**: $\sum_{g \in G} |X^g| = |X/G| \cdot |G|$.



## TODO

**Additivize Iwasawa Theory**: The current file is specific to multiplicative groups. The `to_additive` attribute is not applied. The technical blocker is that it requires additivizing `commutator` (the derived subgroup), which lives in the root namespace and complicates the automatic translation.

```lean
theorem MulAction.IwasawaStructure.commutator_le 
  {M : Type u_1}  [Group M]  {α : Type u_2}  [MulAction M α]
  (IwaS : IwasawaStructure M α)  [IsQuasiPreprimitive M α]  (N : Subgroup M)  [nN : N.Normal]  (hNX : fixedPoints (↥N) α ≠ Set.univ) :
commutator M ≤ N
```
The Iwasawa criterion : If a quasiprimitive action of a group G on X has an Iwasawa structure, then any normal subgroup that acts nontrivially contains the group of commutators.
```lean
theorem MulAction.IwasawaStructure.isSimpleGroup 
  {M : Type u_1}  [Group M]  {α : Type u_2}  [MulAction M α] [Nontrivial M]  
  (is_perfect : commutator M = ⊤)  [IsQuasiPreprimitive M α] (IwaS : IwasawaStructure M α)  (is_faithful : FaithfulSMul M α) : 
IsSimpleGroup M
```

The Iwasawa criterion for simplicity.