import Mathlib

open IsLocalRing


/-- Nakayama's Lemma (Stacks 10.20.1 (6)) (Tag 00DV):
A module map is surjective if it is surjective modulo the Jacobson radical.
Let R be a commutative ring and let M and N be modules over R.
Let f: N →  M be an R-linear map. Suppose that:
1). The module M is finitely generated over R.
2). There exists an ideal I of R that is contained in the
Jacobson radical of R (i.e., I is contained in every maximal ideal of R).
3). The induced map to the quotient, bar{f}: N →  M/IM, is surjective.
Then, the original map f: N →  M is surjective. -/
lemma nakayama_surjective_of_quotient {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : N →ₗ[R] M) (hM : Module.Finite R M)
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    (h_surj : Function.Surjective (Submodule.Quotient.mk (p := I • (⊤ : Submodule R M)) ∘ f)) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top]
  -- From h_surj, we know that mkQ ∘ f is surjective
  -- This means the range of (mkQ ∘ f) is ⊤ in the quotient
  -- Therefore (range f) maps to ⊤ in the quotient
  -- This means range f + I•⊤ = ⊤
  have h_range_sup : LinearMap.range f ⊔ I • ⊤ = ⊤ := by
    -- Show that every element of M is in range f + I•⊤
    rw [eq_top_iff]
    intro m _
    -- Use surjectivity to find a preimage
    obtain ⟨n, hn⟩ := h_surj (Submodule.Quotient.mk m)
    simp only [Function.comp_apply] at hn
    -- hn says that mk (f n) = mk m, so m - f n ∈ I•⊤
    have h_diff : m - f n ∈ I • (⊤ : Submodule R M) := by
      have : f n - m ∈ I • (⊤ : Submodule R M) := by
        rw [Submodule.Quotient.eq] at hn
        exact hn
      simpa using Submodule.neg_mem _ this
    -- Therefore m = f n + (m - f n) ∈ range f + I•⊤
    rw [Submodule.mem_sup]
    use f n, ⟨n, rfl⟩, m - f n, h_diff
    simp
  -- Now apply Nakayama's lemma
  -- We have ⊤ = range f + I•⊤, and I ≤ jacobson ⊥
  -- By Nakayama, ⊤ ≤ range f
  have h_top_fg : (⊤ : Submodule R M).FG := Module.Finite.fg_top
  have h_top_le : (⊤ : Submodule R M) ≤ LinearMap.range f := by
    -- Apply Nakayama: since ⊤ = range f ⊔ I•⊤, we have ⊤ ≤ range f ⊔ I•⊤
    -- And by Nakayama's lemma, this implies ⊤ ≤ range f
    have h_le_sup : (⊤ : Submodule R M) ≤ LinearMap.range f ⊔ I • (⊤ : Submodule R M) := by
      rw [h_range_sup]
    exact Submodule.le_of_le_smul_of_le_jacobson_bot h_top_fg hI h_le_sup
  exact le_antisymm le_top h_top_le

/-- Equality of Maximal Ideals from Cotangent Surjectivity.
Let f: A → B be a local homomorphism between two local rings
A and B. Let mA and mB denote the unique maximal ideals of
A and B, respectively. Suppose that:
1).The maximal ideal mB is finitely generated as an ideal (or
equivalently, as a B-module).
2).The map induced by f from the maximal ideal of A to the
cotangent space of B is surjective. That is, the map
mA → mB/(mB)^2 is surjective.
Then, the extension of mA to B is equal to mB. That is,
(mA)B = mB. -/
lemma mAB_eq_mB_of_cotangent_surj {A B : Type*}
[CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (h_mB_fg : (maximalIdeal B).FG)
    (h_cot_surj : Function.Surjective (fun (x : maximalIdeal A) =>
      Ideal.Quotient.mk (maximalIdeal B ^ 2) (algebraMap A B x))) :
    (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
  let mA := IsLocalRing.maximalIdeal A
  let mB := IsLocalRing.maximalIdeal B
  -- 1. First prove mA B ⊆ mB (this is a property of local homomorphisms)
  have h_le : mA.map (algebraMap A B) ≤ mB := by
    rw [Ideal.map_le_iff_le_comap]
    -- Use the local homomorphism property: comap mB = mA
    have := (IsLocalRing.local_hom_TFAE (algebraMap A B)).out 0 4
    exact le_of_eq (this.mp inferInstance).symm
  -- 2. Construct the inclusion map f: mA B → mB
  let f : mA.map (algebraMap A B) →ₗ[B] mB := Submodule.inclusion h_le
  -- 3. Use Nakayama's lemma to prove f is surjective
  -- We view mB as a B-module, and take the ideal I to be mB
  have h_surj_f : Function.Surjective f := by
    -- Apply the first lemma
    apply nakayama_surjective_of_quotient f (Module.Finite.iff_fg.mpr h_mB_fg) mB
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    -- Verify the surjectivity condition modulo I•M (i.e. mB^2)
    -- Goal: prove for any y ∈ mB, there exists x ∈ mA B such that f(x) ≡ y (mod mB^2)
    intro y_quot
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y_quot
    -- Use the cotangent space surjectivity assumption (h_cot_surj)
    -- Note: h_cot_surj is about B/mB^2, we need to restrict it to mB
    obtain ⟨a, ha⟩ := h_cot_surj (Ideal.Quotient.mk (mB ^ 2) y)
    -- Construct the preimage: a is an element of mA, mapping to mA B
    let x : mA.map (algebraMap A B) := ⟨algebraMap A B a, Ideal.mem_map_of_mem _ a.property⟩
    use x
    -- Verify the congruence relation
    simp only [Function.comp_apply]
    rw [Submodule.Quotient.eq]
    -- Below we prove: f(x) - y ∈ mB • (⊤ : Submodule B mB)
    rw [Submodule.mem_smul_top_iff]
    -- Now the goal is: (f x - y : B) ∈ mB • mB = mB^2
    have hfx : (f x : B) = algebraMap A B a := by simp [f, Submodule.inclusion, x]
    -- Simplify coercion
    change (f x : B) - (y : B) ∈ mB • mB
    rw [hfx, Ideal.smul_eq_mul]
    -- ha says exactly that algebraMap a - y ∈ mB^2
    have : algebraMap A B a - ↑y ∈ mB ^ 2 := Ideal.Quotient.eq.mp ha
    rw [sq] at this
    exact this
  -- 4. Since the inclusion map is surjective, the two sets are equal
  refine le_antisymm h_le (fun b hb => ?_)
  obtain ⟨s, hs⟩ := h_surj_f ⟨b, hb⟩
  -- hs: f s = ⟨b, hb⟩ means (s : B) = b
  have : (s : B) = b := by
    have heq := congr_arg (fun (x : mB) => (x : B)) hs
    simpa [f, Submodule.inclusion] using heq
  rw [← this]
  exact s.property

/-- In a local ring, the Jacobson radical is the unique maximal ideal. -/
lemma maximalIdeal_eq_jacobson (R : Type*) [CommRing R] [IsLocalRing R] :
    Ideal.jacobson (⊥ : Ideal R) = maximalIdeal R := by
  exact IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top

/-- The image of an ideal I under an algebra map is equal to
the scalar product of I and the entire codomain. -/
lemma map_eq_smul_top {R S : Type*} [CommRing R] [CommRing S]
 [Algebra R S] (I : Ideal R) :
    (I.map (algebraMap R S)).restrictScalars R = I • (⊤ : Submodule R S) := by
    ext
    simp

/-- If two submodules are equal, surjectivity onto their quotients is equivalent. -/
lemma Function.surjective_quotient_mk_iff_of_eq {R M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] {p q : Submodule R M} (f : N → M) (h : p = q) :
    Function.Surjective (Submodule.Quotient.mk (p := p) ∘ f) ↔
    Function.Surjective (Submodule.Quotient.mk (p := q) ∘ f) := by
  cases h; rfl

/-- Stacks Project Lemma 10.20.3 (Tag 0E8M):
Let f : A → B be a local homomorphism of local rings. Assume:
(1) B is finite as an A-module.
(2) The maximal ideal of B is finitely generated.
(3) f induces an isomorphism on residue fields (surjectivity is enough).
(4) The map on cotangent spaces m_A / m_A^2 → m_B / m_B^2 is surjective.
Then f is surjective. -/
theorem stacks_0E8M {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
 [IsLocalRing B] [Algebra A B] [h_local : IsLocalHom (algebraMap A B)]
    (h_finite : Module.Finite A B)
    (h_mB_fg : (maximalIdeal B).FG)
    (h_res_surj : Function.Surjective (ResidueField.map (algebraMap A B)))
    (h_cot_surj : Function.Surjective (fun (x : maximalIdeal A) =>
      Ideal.Quotient.mk (maximalIdeal B ^ 2) (algebraMap A B x))) :
    Function.Surjective (algebraMap A B) := by
  let mA := maximalIdeal A
  let mB := maximalIdeal B
  let f_ring := algebraMap A B
  let f_lin := Algebra.linearMap A B
  -- Step 1: Show f(mA)B = mB as ideals of B
  have h_mAB_eq_mB := mAB_eq_mB_of_cotangent_surj h_mB_fg h_cot_surj
  -- Step 2: Show f is surjective using Nakayama's Lemma
  apply nakayama_surjective_of_quotient f_lin h_finite mA
  · -- Prove mA is the Jacobson radical of A
    rw [maximalIdeal_eq_jacobson A]
  · -- Show surjectivity on the quotient A → B/(mA B) as A-modules
    -- First, establish that mA • ⊤ = mB (viewed as A-modules)
    have h_sub_eq : mA • (⊤ : Submodule A B) = mB.restrictScalars A := by
      rw [← map_eq_smul_top mA]
      rw [h_mAB_eq_mB]
    -- Switch the quotient target from (mA • ⊤) to mB (as A-module)
    rw [Function.surjective_quotient_mk_iff_of_eq f_lin h_sub_eq]
    -- Factoring: A → B → B/mB is the same as A → A/mA → B/mB
    have h_factor : (Submodule.Quotient.mk (p := mB.restrictScalars A) ∘ f_lin) =
      (ResidueField.map f_ring) ∘ (Ideal.Quotient.mk mA) := by
      ext x
      rfl -- True by definition of ResidueField.map
    rw [h_factor]
    -- Surjectivity follows from the surjectivity of the residue field map (Assumption 3)
    exact h_res_surj.comp (Ideal.Quotient.mk mA).surjective
