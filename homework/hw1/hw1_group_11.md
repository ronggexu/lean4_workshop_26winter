---
tags:
  - lean
  - group_theory
---
# Theory of Permutation Groups and Symmetric Groups

## Equivalance between types

The permutation group is defined as the natural group structure endowed on bijections between sets. In Mathlib, it is implemented as the type `Equiv.Perm` consisting of all bijections on a given type.  
Its group structure is provided by the instance `Equiv.Perm.permGroup`, ensuring that the constructed type `Equiv.Perm` has a group structure. The relevant content is mainly located in `Mathlib/Logic/Equiv/Defs`. First is the implementation of the basic type constructor `Equiv`.
```
-- Simplified code
structure Equiv (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  left_inv : LeftInverse invFun toFun
  right_inv : RightInverse invFun toFun
```
A equivalance of types `α ≃ β` is the type of functions from `α → β` with a two-sided inverse.  In Lean, you should NOT use `e.invFun` directly. Use the coercion of `e.symm` instead. Similarly, you should NOT use `e.toFun(x)` directly. Use the coercion of `e(x)` instead.
Then we can construct `Equiv.Perm` 
```
abbrev Equiv.Perm (α : Sort*) :=
  Equiv α α
```
In Mathlib, the symmetric group `Equiv.Perm α` is endowed with a rich hierarchy of structures and interfaces. Here are the key ones:
```
-- Basic Group Structure
instance permGroup : Group (Perm α) where
  mul_assoc _ _ _ := (trans_assoc _ _ _).symm
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm
  npow n f := f ^ n
  npow_succ _ _ := coe_fn_injective <| Function.iterate_succ _ _
  zpow := zpowRec fun n f ↦ f ^ n
  zpow_succ' _ _ := coe_fn_injective <| Function.iterate_succ _ _
-- Defined in Mathlib/GroupTheory/Perm/Basic.lean
```
This provides:
- Multiplication: composition of permutations (`Equiv.trans`)
- Identity: the identity permutation (`Equiv.refl`)
- Inverse: the inverse permutation (`Equiv.symm`)
- Group axioms: associativity, identity laws, inverse laws
In Mathlib, the implementations of structures and interfaces for finite permutation groups follow the **exact same patterns** as for general abstract groups.
For example, the set of subgroups `Subgroup (Equiv.Perm α)` forms a complete lattice the same as other groups. 
In Mathlib4, the symmetric group `Equiv.Perm α` on a finite type `α` is endowed with several specific structures that leverage finiteness.
For a finite type `α`, the permutation group `Equiv.Perm α` is itself a finite type. This is because a permutation is a bijection from `α` to `α`, and there are only finitely many such bijections when `α` is finite, thus we can construct the instance as follow.
```
instance [Fintype α] [DecidableEq α] : Fintype (Perm α) :=
  Fintype.ofEquiv (α ≃ α) (by rfl)
```
In finite case, there is an important theorem. It allows we to compute the order (cardinality) of the symmetric group on a finite set of size `n` , which everyone knows, `n!` 
```
-- Basic Formula
theorem card_perm [Fintype α] [DecidableEq α] :
  Fintype.card (Perm α) = (Fintype.card α)! :=
  calc
    Fintype.card (Perm α) = Fintype.card (α ≃ α) := rfl
    _ = (Fintype.card α)! := Fintype.card_equiv α α

-- Specific to case Fin n 
theorem card_fin (n : ℕ) : 
  Fintype.card (Perm (Fin n)) = n ! := by
  simp [Fintype.card_perm]
```
We conclude some interfaces/instances of `Equiv.Perm` as follow.
- `Equiv.Perm.fintype` - Finite type instance for permutations of a finite type.
- `Equiv.Perm.permGroup` - Alternative group instance name for permutations (often used in group theory contexts).
- `Equiv.Perm.sign` - The sign (or parity) of a permutation, defined for finite types.
- `Equiv.Perm.signHomomorphism` - The group homomorphism from permutations to {±1} mapping to the sign.
- `Equiv.Perm.subtypePerm` - Constructs a permutation on a subtype from a permutation preserving that subtype.
- `Equiv.Perm.extendDomain` - Extends a permutation on α to a permutation on β given an embedding α ↪ β.
- `Equiv.Perm.permCongr` - Transports permutations across a type equivalence α ≃ β.
- `Equiv.Perm.mul_apply` - Lemma stating how permutation multiplication (composition) acts on elements.
## Cycle 

Cyclic permutation is defined as a `Prop` .  In Mathlib, the relevant content is mainly located in `Mathlib/GroupTheory/Perm/Cycle`. 
Mathlib starts the theory of cycles in permutations by some implementations, here are the key ones.
```
-- In Mathlib/GroupTheory/Perm/Cycle/Basic.lean
def IsCycle (f : Perm β) : Prop :=
  ∃ x, f x ≠ x ∧ ∀ ⦃y⦄, f y ≠ y → ∃ i : ℤ, (f ^ i) x = y
```
`Equiv.Perm.IsCycle` means `f` is a cycle if any two nonfixed points of `f` are related by repeated applications of `f`, and `f` is not the identity. And there is a very similar implementation `Equiv.Perm.IsCycleOn`. 
```
def IsCycleOn (f : Perm α) (s : Set α) : Prop :=
  Set.BijOn f s s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → f.SameCycle x y
```
`Equiv.Perm.IsCycle` and `Equiv.Perm.IsCycleOn` are different in three ways: 
 - `IsCycle` is about the entire type while `IsCycleOn` is restricted to a set.
 - `IsCycle` forbids the identity while `IsCycleOn` allows it (if `s` is a subsingleton).
 - `IsCycleOn` forbids fixed points on `s` (if `s` is nontrivial), while `IsCycle` allows them.
 Matlib has defined cycleType as multisets over natural numbers, which as follow.
```
-- In Mathlib/GroupTheory/Perm/Cycle/Type.lean
def cycleType (σ : Perm α) : Multiset ℕ :=
  (σ.cycleFactorsFinset.val.map (fun c => (c.support.card : ℕ))).sort (· ≤ ·)
```
And there is a important theorem states that the cycle type is same after conjugate.
```
theorem cycleType_conj (σ π : Perm α) : cycleType (π * σ * π⁻¹) = cycleType σ
```
Also, Matlib provides a interface for working with 3-cycle, it will be use later in some lemma in the `alternatingGroup` content.
```
def IsThreeCycle [DecidableEq α] (σ : Perm α) : Prop :=
  σ.cycleType = {3}
```
Obviously, 3-cycles are cycles too. 


## 单群
单群定义：非平凡群且正规子群是平凡或本身
```lean
/-- A `Group` is simple when it has exactly two normal `Subgroup`s. -/
@[mk_iff]
class IsSimpleGroup : Prop extends Nontrivial G where
  /-- Any normal subgroup is either `⊥` or `⊤` -/
  eq_bot_or_eq_top_of_normal : ∀ H : Subgroup G, H.Normal → H = ⊥ ∨ H = ⊤
```
反过来的定义
```lean
@[to_additive]
theorem Subgroup.Normal.eq_bot_or_eq_top [IsSimpleGroup G] {H : Subgroup G} (Hn : H.Normal) :
    H = ⊥ ∨ H = ⊤ :=
  IsSimpleGroup.eq_bot_or_eq_top_of_normal H Hn
```
放到子群里的定义
```lean
@[to_additive]
protected lemma Subgroup.isSimpleGroup_iff {H : Subgroup G} :
    IsSimpleGroup ↥H ↔ H ≠ ⊥ ∧ ∀ H' ≤ H, (H'.subgroupOf H).Normal → H' = ⊥ ∨ H' = H := by
  rw [isSimpleGroup_iff, H.nontrivial_iff_ne_bot, Subgroup.forall]
  simp +contextual [disjoint_of_le_iff_left_eq_bot, LE.le.ge_iff_eq]
```
格只有两个元素
```lean
@[to_additive]
instance {C : Type*} [CommGroup C] [IsSimpleGroup C] : IsSimpleOrder (Subgroup C) :=
  ⟨fun H => H.normal_of_comm.eq_bot_or_eq_top⟩
```
单群映射进非平凡群的满射得到值域是单群
证明为考虑值域的正规子群 原像也是正规子群 满射得到逆映射是单射 考虑平凡和整个像的原像即可
```lean
@[to_additive]
theorem isSimpleGroup_of_surjective {H : Type*} [Group H] [IsSimpleGroup G] [Nontrivial H]
    (f : G →* H) (hf : Function.Surjective f) : IsSimpleGroup H :=
  ⟨fun H iH => by
    refine (iH.comap f).eq_bot_or_eq_top.imp (fun h => ?_) fun h => ?_
    · rw [← map_bot f, ← h, map_comap_eq_self_of_surjective hf]
    · rw [← comap_top f] at h
      exact comap_injective hf h⟩
```
和单群同构的群也是单群
```lean
@[to_additive]
lemma _root_.MulEquiv.isSimpleGroup {H : Type*} [Group H] [IsSimpleGroup H] (e : G ≃* H) :
    IsSimpleGroup G :=
  haveI : Nontrivial G := e.toEquiv.nontrivial
  isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective
```
```lean
@[to_additive]
lemma _root_.MulEquiv.isSimpleGroup_congr {H : Type*} [Group H] (e : G ≃* H) :
    IsSimpleGroup G ↔ IsSimpleGroup H where
  mp _ := e.symm.isSimpleGroup
  mpr _ := e.isSimpleGroup
```


## The simplicity of alternating groups

The alternating group is realized as the kernel of the sign map from the permutation group.
```lean
variable (α : Type*) [Fintype α] [DecidableEq α]

def alternatingGroup : Subgroup (Perm α) :=

  sign.ker
```
The `length` is the length of a list, and in our case it is interpreted as the number of cycles in a permutation.
With this, we have equivalent descriptions of the alternating group:
```lean
theorem prod_list_swap_mem_alternatingGroup_iff_even_length {l : List (Perm α)} (hl : ∀ g ∈ l, IsSwap g) : l.prod ∈ alternatingGroup α ↔ Even l.length := by
  rw [mem_alternatingGroup, sign_prod_list_swap hl, neg_one_pow_eq_one_iff_even]
  decide
```
This says the elements in the alternating group are of even length.
```lean
theorem eq_alternatingGroup_of_index_eq_two {G : Subgroup (Equiv.Perm α)} (hG : G.index = 2) : G = alternatingGroup α := sorry
```
This says the alternating group is the unique subgroup of the permutation group of index $2$.
An important result of the alternating groups is, $A_n (n \geq 5)$ is a simple group. For this, we need to prove the following things: 
- The 3-cycles generate $A_n$.
- All the 3-cycles are conjugate in $A_n$.
- Any nontrivial normal subgroup of $A_n$ contains a 3-cycle.
In Mathlib, the first two points are formalized (`Equiv.Perm.closure_three_cycles_eq_alternating`, `alternatingGroup.isThreeCycle_isConj`). For the third point, it is only treated in the case $n=5$. In general, the proof by cases is much more complicated. The result is:
```lean
instance isSimpleGroup_five : IsSimpleGroup (alternatingGroup (Fin 5))
```
Moreover, the center of the alternating group is trivial:
```lean
theorem center_eq_bot (hα4 : 4 ≤ Nat.card α) : Subgroup.center (alternatingGroup α) = ⊥ := by sorry
```

## To do

- Complete the proof that $A_n $ is a simple group for $n \geq 5$.
- There is a missing famous theorem, Cayley's theorem: every finite group $G$ is isomorphic to a subgroup of the symmetric group $S_n$.