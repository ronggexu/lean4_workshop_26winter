import Mathlib

--lemma 1
-- Natural isomorphism: S^{-1}(N / IN) ≅ (S^{-1}N) / I(S^{-1}N)
open Localization LocalizedModule

variable {R : Type*} [CommRing R]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable (I : Ideal R) (S : Submonoid R)

lemma localization_quotient_module_iso :
  Nonempty (LocalizedModule S (N ⧸ (I • ⊤ : Submodule R N)) ≃ₗ[Localization S]
    (LocalizedModule S N ⧸
      (I.map (algebraMap R (Localization S)) • ⊤ :
        Submodule (Localization S) (LocalizedModule S N)))) := by
  -- Strategy: prove the equality of submodules, then use quotEquivOfEq
  -- Submodule.localized S (I • ⊤) = I.map(algebraMap) • ⊤
  have h : Submodule.localized S (I • ⊤ : Submodule R N) =
           (I.map (algebraMap R (Localization S)) • ⊤ :
            Submodule (Localization S) (LocalizedModule S N)) := by
    -- Use the fact that localized' of a smul is the smul of localized'
    rw [Submodule.localized, Submodule.localized'_smul]
    -- Now we need to show that I.localized' = I.map(algebraMap) and localized' ⊤ = ⊤
    congr 1
    · -- I.localized' = I.map(algebraMap)
      exact Ideal.localized'_eq_map (Localization S) S I
    · -- localized' ⊤ = ⊤
      exact Submodule.localized'_top (Localization S) S (LocalizedModule.mkLinearMap S N)
  exact ⟨(localizedQuotientEquiv S (I • ⊤)).symm.trans
    (Submodule.quotEquivOfEq _ _ h)⟩

-- Lemma 2: Vanishing of Finitely Generated Modules
-- Let N be a finitely generated R-module. If S⁻¹N = 0, then there exists
-- an element s ∈ S such that the localization at the powers of s vanishes: Nₛ = 0
lemma vanishing_finitely_generated_module
  {R : Type*} [CommRing R]
  (S : Submonoid R)
  (N : Type*) [AddCommGroup N] [Module R N]
  (hfg : Module.Finite R N)
  (h_vanish : Subsingleton (LocalizedModule S N)) :
  ∃ s : S, ∀ n : N, ∃ k : ℕ, (s.val ^ k) • n = 0 := by
  -- Since N is finitely generated, get a finite generating set
  obtain ⟨generators, hgen⟩ := hfg.fg_top
  classical
  -- The localization is subsingleton, so each element of N is annihilated by some element of S
  have h_sub : ∀ m : N, ∃ r ∈ S, r • m = 0 :=
    LocalizedModule.subsingleton_iff.mp h_vanish
  -- For each generator, choose an element of S that annihilates it
  choose f hf_mem hf_annihilates using fun g : generators => h_sub g.val
  -- Take the product of all these elements
  let s_val := generators.attach.prod (fun g => f g)
  have s_mem : s_val ∈ S := by
    apply Submonoid.prod_mem
    intros _ _
    exact hf_mem _
  let s : S := ⟨s_val, s_mem⟩
  use s
  intro n
  -- Write n as a linear combination of generators
  have hn : n ∈ Submodule.span R (generators : Set N) := by rw [hgen]; trivial
  -- Use induction on the span
  refine Submodule.span_induction (p := fun x _ => ∃ k : ℕ, (↑s ^ k) • x = 0) ?_ ?_ ?_ ?_ hn
  · intro g hg
    use 1
    simp only [pow_one]
    have mem_attach : ⟨g, hg⟩ ∈ generators.attach := Finset.mem_attach _ _
    have hdvd : f ⟨g, hg⟩ ∣ s_val := Finset.dvd_prod_of_mem f mem_attach
    obtain ⟨c, hc⟩ := hdvd
    change s_val • g = 0
    rw [hc, mul_smul, smul_comm, hf_annihilates ⟨g, hg⟩, smul_zero]
  · -- Zero case
    use 0
    simp
  · -- Addition case
    intro x y _ _ ⟨kx, hx⟩ ⟨ky, hy⟩
    use max kx ky
    have hkx : kx ≤ max kx ky := le_max_left kx ky
    have hky : ky ≤ max kx ky := le_max_right kx ky
    obtain ⟨dx, hdx⟩ := Nat.exists_eq_add_of_le hkx
    obtain ⟨dy, hdy⟩ := Nat.exists_eq_add_of_le hky
    rw [smul_add]
    have hx' : s ^ max kx ky • x = 0 := by
      rw [hdx, pow_add, mul_smul]
      rw [smul_comm, hx, smul_zero]
    have hy' : s ^ max kx ky • y = 0 := by
      rw [hdy, pow_add, mul_smul]
      rw [smul_comm, hy, smul_zero]
    rw [hx', hy', add_zero]
  · -- Scalar multiplication case
    intro a x _ ⟨k, hx⟩
    use k
    rw [smul_comm, hx, smul_zero]

open Submodule

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (I : Ideal R)

lemma generalized_nakayama (N : Submodule R M) (hN : N.FG) (h_eq : N ≤ I • N) :
    ∃ r : R, r - 1 ∈ I ∧ ∀ n ∈ N, r • n = (0 : M) := by
  exact Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hN h_eq

--lemma 4
lemma composition_of_localizations
  (R : Type*) [CommRing R]
  (I : Ideal R)
  (S : Submonoid R)
  (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N]
  (s : R) (hs : s ∈ S)
  (h : ∀ n : LocalizedModule (Submonoid.powers s) N,
        ∃ a ∈ I, ∃ t : ℕ, (algebraMap R (Localization (Submonoid.powers s)) a) • n = 0) :
  ∃ (a : R) (ha : a ∈ I) (k : ℕ) (hk : k ≥ 1),
    Subsingleton (LocalizedModule (Submonoid.powers (s^k + a)) N) := by
  sorry

--theorem
variable (R : Type*) [CommRing R]
variable (S : Submonoid R)
variable (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]

open Localization LocalizedModule
theorem localization_generator_lifting_sum
  {n : ℕ} (x : Fin n → M)
  (h_gen : ∀ (m : LocalizedModule S (M ⧸ (I • ⊤ : Submodule R M))),
    ∃ (c : Fin n → Localization S),
      m = ∑ i, c i • LocalizedModule.mk (Submodule.Quotient.mk (x i)) 1) :
  ∃ (s : R) (hs : s ∈ S) (a : R) (ha : a ∈ I),
∀ (m : LocalizedModule (Submonoid.powers (s + a)) M),
      ∃ (c : Fin n → Localization.Away (s + a)),
        m = ∑ i, c i • LocalizedModule.mk (x i) 1 :=
sorry
