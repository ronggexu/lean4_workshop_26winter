import Mathlib

open Algebra Function

-- Lemma 6.1
/-- A commutative ring which is of finite type over a Noetherian base ring is itself
Noetherian.-/
theorem isNoetherian_of_finiteType (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] (hR : IsNoetherianRing R) (hA : Algebra.FiniteType R A) :
    IsNoetherianRing A := by
  -- Use the definition of finite type: there exists a finite set of generators s
  obtain ⟨s, hs⟩ := hA
  -- Construct the evaluation map from polynomials on s to A
  let f : MvPolynomial s R →ₐ[R] A := MvPolynomial.aeval (fun x : s => (x : A))
  -- Show that this map is surjective
  have hf : Surjective f := by
    rw [← AlgHom.range_eq_top, ← hs, ← Algebra.adjoin_range_eq_range_aeval]
    simp
  -- Ensure the Noetherian instance for R is available
  haveI : IsNoetherianRing R := hR
  -- Hilbert's Basis Theorem: MvPolynomial on a finite type over a Noetherian ring is
  -- Noetherian
  haveI : IsNoetherianRing (MvPolynomial s R) := inferInstance
  -- The homomorphic image of a Noetherian ring is Noetherian
  exact isNoetherianRing_of_surjective (MvPolynomial s R) A f.toRingHom hf

/-- A localization of a Noetherian commutative ring is again Noetherian.-/
theorem isNoetherian_of_localization (R : Type*) [CommRing R]
  (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]
  (hR : IsNoetherianRing R) :
  IsNoetherianRing S := by-- Apply the standard theorem: Localization of a Noetherian ring is Noetherian
  exact IsLocalization.isNoetherianRing M S hR


open Algebra

-- Lemma 6.3
/-- Any algebra of finite type over a field is Noetherian.-/
theorem finiteType_algebra_over_field_is_Noetherian
  (K A : Type*) [Field K] [CommRing A] [Algebra K A]
  (hA : Algebra.FiniteType K A) :
  IsNoetherianRing A := by-- Add the FiniteType hypothesis to the typeclass inference system
  haveI := hA-- Apply the theorem that a finite type algebra over a Noetherian ring is Noetherian-- (Fields are automatically instances of IsNoetherianRing)
  exact Algebra.FiniteType.isNoetherianRing K A

/-- Any algebra of finite type over ℤ is Noetherian.-/
theorem finiteType_algebra_over_int_is_Noetherian
  (A : Type*) [CommRing A] [Algebra ℤ A]
  (hA : Algebra.FiniteType ℤ A) :
  IsNoetherianRing A := by-- Add the FiniteType hypothesis to the typeclass inference system
  haveI := hA-- Apply the theorem that a finite type algebra over a Noetherian ring is Noetherian-- (ℤ is automatically an instance of IsNoetherianRing)
  exact Algebra.FiniteType.isNoetherianRing ℤ A

open scoped Classical

variable (R : Type*) [CommRing R] [IsNoetherianRing R]

-- Lemma 6.4
/-- 1 ￿ Any finite `R`‑module is of finite presentation.-/
theorem finiteModule_finitePresentation {M : Type*} [AddCommGroup M] [Module R M]
  (hM : Module.Finite R M) :
  Module.FinitePresentation R M := by
  haveI := hM
  exact Module.finitePresentation_of_finite R M

theorem submodule_of_finite_is_finite {M : Type*} [AddCommGroup M] [Module R M]
  (hM : Module.Finite R M) (N : Submodule R M) :
  Module.Finite R N := by
  haveI := hM-- Since R is Noetherian and M is Finite, M is a Noetherian module.
  -- This instance is provided by `isNoetherian_of_isNoetherianRing_of_finite`.
  haveI : IsNoetherian R M := isNoetherian_of_isNoetherianRing_of_finite R M-- In a Noetherian module, every submodule is finitely generated.
  have hN_fg : N.FG := IsNoetherian.noetherian N-- A finitely generated submodule is a Finite module.
  rw [Module.Finite.iff_fg]
  exact hN_fg

/-- 3 ￿ Any algebra of finite type over a Noetherian ring `R` is of finite
presentation.-/
theorem finiteType_algebra_finitePresentation {A : Type*} [CommRing A] [Algebra R A]
  (hA : Algebra.FiniteType R A) :
  Algebra.FinitePresentation R A := by
  haveI := hA-- Use the library theorem stating FiniteType ￿ FinitePresentation over Noetherian rings
  exact (Algebra.FinitePresentation.of_finiteType (R := R) (A := A)).mp hA

open Algebra
open scoped TensorProduct
set_option diagnostics true

-- Lemma 6.7
/--Let R → S be a ring map. Let R → R′ be of finite type. If S is Noetherian, then the base
change S′ = R′ ⊗R S is Noetherian.-/
theorem isNoetherianRing_baseChange_of_finiteType
  {R S R' : Type*} [CommRing R] [CommRing S] [CommRing R']
  [Algebra R S] [Algebra R R']
  (hfinite : Algebra.FiniteType R R')
  [IsNoetherianRing S] :
  IsNoetherianRing (R' ⊗[R] S) := by
  have finite_type_of_S_S' : Algebra.FiniteType S (S ⊗[R] R') := by
    exact Algebra.FiniteType.baseChange S
  have Noetherian_of_S' : IsNoetherianRing (S ⊗[R] R') := by
    apply isNoetherian_of_finiteType S (S ⊗[R] R') _ finite_type_of_S_S'
    infer_instance
  have e : S ⊗[R] R' ≃+* R' ⊗[R] S := (Algebra.TensorProduct.comm R S R').toRingEquiv
  have Noetherian_of_S'_ : IsNoetherianRing (R' ⊗[R] S) := by
    apply isNoetherianRing_of_ringEquiv (S ⊗[R] R') e
  exact Noetherian_of_S'_

-- Lemma 6.8
variable {k : Type*} [Field k]

def fractionSubfield (K : Type*) [Field K] (R : Subring K) [IsDomain R] : Subfield K where
  carrier := {x | ∃ (r : R) (s : R) (hs : s ≠ 0), (r : K) * (((s : R) : K)⁻¹) = x}
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨r₁, s₁, hs₁_ne, h₁⟩
    rcases hb with ⟨r₂, s₂, hs₂_ne, h₂⟩
    refine ⟨⟨r₁.1 * r₂.1, R.mul_mem r₁.2 r₂.2⟩,
            ⟨s₁.1 * s₂.1, R.mul_mem s₁.2 s₂.2⟩,
            mul_ne_zero hs₁_ne hs₂_ne, ?_⟩
    have h_s1_ne_zero : (s₁ : K) ≠ 0 := Subtype.coe_ne_coe.mpr hs₁_ne
    have h_s2_ne_zero : (s₂ : K) ≠ 0 := Subtype.coe_ne_coe.mpr hs₂_ne
    calc
      (↑(⟨r₁.1 * r₂.1, _⟩ : R) : K) * (((⟨s₁.1 * s₂.1, _⟩ : R) : K))⁻¹
          = ((r₁ : K) * (r₂ : K)) * (((s₁ : K) * (s₂ : K))⁻¹) := by
        simp
      _ = ((r₁ : K) * (r₂ : K)) * ((s₁ : K)⁻¹ * (s₂ : K)⁻¹) := by
        rw [mul_inv]
      _ = (r₁ : K) * (s₁ : K)⁻¹ * ((r₂ : K) * (s₂ : K)⁻¹) := by
        ring
      _ = a * b := by rw [h₁, h₂]
  one_mem' := by
    refine ⟨⟨1, R.one_mem⟩, ⟨1, R.one_mem⟩, one_ne_zero, ?_⟩
    simp
  add_mem' := by
    intro a b ha hb
    rcases ha with ⟨r₁, s₁, hs₁_ne, h₁⟩
    rcases hb with ⟨r₂, s₂, hs₂_ne, h₂⟩
    refine ⟨⟨r₁.1 * s₂.1 + r₂.1 * s₁.1,
             R.add_mem (R.mul_mem r₁.2 s₂.2) (R.mul_mem r₂.2 s₁.2)⟩,
            ⟨s₁.1 * s₂.1, R.mul_mem s₁.2 s₂.2⟩,
            mul_ne_zero hs₁_ne hs₂_ne, ?_⟩
    have h_s1_ne_zero : (s₁ : K) ≠ 0 := Subtype.coe_ne_coe.mpr hs₁_ne
    have h_s2_ne_zero : (s₂ : K) ≠ 0 := Subtype.coe_ne_coe.mpr hs₂_ne
    calc
      (↑(⟨r₁.1 * s₂.1 + r₂.1 * s₁.1, _⟩ : R) : K) * (((⟨s₁.1 * s₂.1, _⟩ : R) : K))⁻¹
          = ((r₁ : K) * (s₂ : K) + (r₂ : K) * (s₁ : K)) * (((s₁ : K) * (s₂ : K))⁻¹) := by
        simp
      _ = ((r₁ : K) * (s₂ : K) + (r₂ : K) * (s₁ : K)) * ((s₁ : K)⁻¹ * (s₂ : K)⁻¹) := by
        rw [mul_inv]
      _ = ((r₁ : K) * (s₂ : K)) * ((s₁ : K)⁻¹ * (s₂ : K)⁻¹) +
          ((r₂ : K) * (s₁ : K)) * ((s₁ : K)⁻¹ * (s₂ : K)⁻¹) := by
        ring
      _ = (r₁ : K) * (s₁ : K)⁻¹ + (r₂ : K) * (s₂ : K)⁻¹ := by
        field_simp [h_s1_ne_zero, h_s2_ne_zero]
      _ = a + b := by rw [h₁, h₂]
  zero_mem' := by
    refine ⟨⟨0, R.zero_mem⟩, ⟨1, R.one_mem⟩, one_ne_zero, ?_⟩
    simp
  neg_mem' := by
    intro x hx
    rcases hx with ⟨r, s, hs_ne, h⟩
    refine ⟨⟨-r.1, R.neg_mem r.2⟩, s, hs_ne, ?_⟩
    simp [h]
  inv_mem' := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0, inv_zero]
      exact (by
        refine ⟨⟨0, R.zero_mem⟩, ⟨1, R.one_mem⟩, one_ne_zero, ?_⟩
        simp : (0 : K) ∈ {x | ∃ (r : R) (s : R) (hs : s ≠ 0), (r : K) * (((s : R) : K)⁻¹) = x})
    · rcases hx with ⟨r, s, hs_ne, h⟩
      have hr_ne : (r : K) ≠ 0 := by
        intro hr
        rw [hr, zero_mul] at h
        exact hx0 h.symm
      have hr_ne' : r ≠ 0 := Subtype.coe_ne_coe.mp hr_ne
      refine ⟨s, r, hr_ne', ?_⟩
      calc
        (s : K) * (((r : R) : K))⁻¹ = ((r : K) * ((s : R) : K)⁻¹)⁻¹ := by
          field_simp [hr_ne, Subtype.coe_ne_coe.mpr hs_ne]
        _ = x⁻¹ := by rw [h]

theorem exists_fg_algebra_with_fraction_field_geom1 {k K : Type*} [Field k] [Field K] [Algebra k K] (h : (⊤ : IntermediateField k K).FG) :
∃ (B : Subalgebra k K), B.FG ∧ fractionSubfield K B.toSubring = (⊤ : Subfield K) := by
  obtain ⟨S, hS⟩ := h
  let B : Subalgebra k K := Algebra.adjoin k S
  have hB_fg : B.FG := Subalgebra.fg_adjoin_finset S
  refine ⟨B, hB_fg, ?_⟩

  -- 我们需要证明 fractionSubfield K B = K
  -- 根据包含关系：一方面 fractionSubfield K B ≤ K 是显然的
  -- 另一方面，我们需要证明 K ≤ fractionSubfield K B

  -- 首先，S 中的元素都在 fractionSubfield K B 中
  have hS_sub : (S : Set K) ⊆ (fractionSubfield K B.toSubring : Set K) := by
      intro x hx
      have hx_B : x ∈ B := Algebra.subset_adjoin hx
      -- x 可以表示为 x/1 ∈ fractionSubfield K B.toSubring
      exact ⟨⟨x, hx_B⟩, ⟨1, B.one_mem⟩, one_ne_zero, by simp⟩

  -- 由于 fractionSubfield K B 是 K 的子域，且包含 S
  -- 根据 IntermediateField.adjoin 的定义，它是最小的包含 S 的中间域
  -- 将 fractionSubfield 提升为 IntermediateField
  let F : IntermediateField k K :=
    { fractionSubfield K B.toSubring with
      algebraMap_mem' := fun r => by
        -- 证明 algebraMap k K r 在 fractionSubfield 中
        have h_mem : algebraMap k K r ∈ B := by
          exact Subalgebra.algebraMap_mem B r
        refine ⟨⟨algebraMap k K r, h_mem⟩, ⟨1, B.one_mem⟩, one_ne_zero, ?_⟩
        simp }

  -- 现在 S ⊆ F
  have hS_sub_F : (S : Set K) ⊆ (F : Set K) := hS_sub

  -- 由于 F 是包含 S 的中间域，而 IntermediateField.adjoin k S 是最小的这样的中间域
  have h_adjoin_le_F : IntermediateField.adjoin k S ≤ F :=
    IntermediateField.adjoin_le_iff.mpr hS_sub_F

  -- 由假设 hS: IntermediateField.adjoin k S = ⊤
  rw [hS] at h_adjoin_le_F

  -- 因此 F = ⊤
  have h_F_top : F = ⊤ :=
    le_antisymm (le_top) h_adjoin_le_F

  -- 最后，从 F = ⊤ 推出 fractionSubfield K B.toSubring = K
  -- 因此 fractionSubfield K B.toSubring = ⊤ (作为 Subfield K)
  apply Subfield.ext
  intro x
  constructor
  · intro hx
    exact Subfield.mem_top x
  · intro hx
    have : x ∈ (F : Set K) := by
      rw [h_F_top, IntermediateField.coe_top]
      trivial
    exact this

theorem ne_zero_mem_nonZeroDivisors_of_subring {K : Type*} [Field K] (R : Subring K) (s : R) (hs_ne : s ≠ 0) :
  s ∈ nonZeroDivisors R := by
  rw [mem_nonZeroDivisors_iff]
  constructor
  · intro a ha
    -- 从 s * a = 0 和 s ≠ 0 推出 a = 0
    have : (s : K) * (a : K) = 0 := congrArg Subtype.val ha
    have hs_ne_K : (s : K) ≠ 0 := Subtype.coe_ne_coe.mpr hs_ne
    have ha_zero : (a : K) = 0 :=
      (mul_eq_zero.mp this).resolve_left hs_ne_K
    exact Subtype.ext ha_zero
  · intro a ha
    -- 从 a * s = 0 和 s ≠ 0 推出 a = 0
    have : (a : K) * (s : K) = 0 := congrArg Subtype.val ha
    have hs_ne_K : (s : K) ≠ 0 := Subtype.coe_ne_coe.mpr hs_ne
    have ha_zero : (a : K) = 0 :=
      (mul_eq_zero.mp this).resolve_right hs_ne_K
    exact Subtype.ext ha_zero

theorem fractionSubfield_eq_top_iff_isLocalization {K : Type*} [Field K] (R : Subring K)
    (h : fractionSubfield K R = (⊤ : Subfield K)) : IsFractionRing R K := by
  --IsFractionRing R K = IsLocalization (nonZeroDivisors R) K
  -- 使用 IsLocalization 的特征定理
  refine ⟨?_, ?_, ?_⟩

  -- 条件1: nonZeroDivisors R 中的元素映射为 K 中的单位
  · intro s
    have h_mem_iff := mem_nonZeroDivisors_iff.mp s.property
    have hs_ne : (s.val : K) ≠ 0 := by
      intro hzero
      have h1 : s.val * (1 : R) = 0 := by
        ext
        simp [hzero]
      have h2 := h_mem_iff.1 (1 : R) h1
      simp at h2
    exact ⟨
      { val := (s.val : K)
        inv := (s.val : K)⁻¹
        val_inv := by field_simp [hs_ne]
        inv_val := by field_simp [hs_ne] },
      rfl
    ⟩

  -- 条件2: 满射性 - 每个 K 中的元素可以写成 r/s 形式
  · intro x
    have hx : x ∈ fractionSubfield K R := by
      rw [h]
      trivial
    rcases hx with ⟨r, s, hs_ne, h⟩
    -- 证明 s ∈ nonZeroDivisors R
    have hs_mem : s ∈ nonZeroDivisors R := by
      apply ne_zero_mem_nonZeroDivisors_of_subring R (s : R) hs_ne

    refine ⟨(r, ⟨s, hs_mem⟩), ?_⟩
    -- 需要证明: x * algebraMap R K s = algebraMap R K r
    -- 但我们有 h: (r : K) * ((s : R) : K)⁻¹ = x

    have hs_ne_K : (s : K) ≠ 0 := by
      intro h
      apply hs_ne
      exact Subtype.ext h

    calc
      x * algebraMap R K s = x * (s : K) := by rfl
      _ = ((r : K) * ((s : K))⁻¹) * (s : K) := by rw [h]
      _ = (r : K) * (((s : K))⁻¹ * (s : K)) := by ring
      _ = (r : K) * 1 := by field_simp [Subtype.coe_ne_coe.mpr hs_ne]
      _ = (r : K) := by simp
      _ = algebraMap R K r := by rfl

  -- 条件3: 等式等价条件
  · intro a b h
    -- h : algebraMap R K a = algebraMap R K b
    -- 由于 R → K 是单射（已在条件1中证明），所以 a = b
    have : a = b := Subtype.coe_injective h
    -- 那么取 c = 1 ∈ nonZeroDivisors R
    refine ⟨⟨1, ?_⟩, by simp [this]⟩
    -- 证明 1 ∈ nonZeroDivisors R
    apply ne_zero_mem_nonZeroDivisors_of_subring R (1 : R) one_ne_zero

theorem exists_fg_subalgebra_with_fraction_field {k K : Type*} [Field k] [Field K] [Algebra k K] (h : (⊤ : IntermediateField k K).FG) :
∃ (B : Subalgebra k K), B.FG ∧ IsFractionRing B.toSubring K := by
  have ⟨B, hB_fg, h_frac⟩ := exists_fg_algebra_with_fraction_field_geom1 h
  use B, hB_fg
  apply fractionSubfield_eq_top_iff_isLocalization B.toSubring h_frac

--exists_fg_algebra_with_fraction_field_geom1

theorem tensorProduct_isNoetherian
  {R K : Type*} [CommRing R] [Algebra k R] [IsNoetherianRing R]
  [Field K] [Algebra k K] (hk : (⊤ : IntermediateField k K).FG) :
  IsNoetherianRing (K ⊗[k] R) := by
  obtain ⟨B, hB_fg, hB_frac⟩ := exists_fg_subalgebra_with_fraction_field hk

  let S : Submonoid B := nonZeroDivisors B

  letI : IsLocalization S K := hB_frac

  have K_localiz : K ≃ₐ[B] Localization S := by
    exact IsLocalization.algEquiv S K (Localization S)

  have hB_fintype : Algebra.FiniteType k B := by
    rw[Subalgebra.fg_iff_finiteType]  at hB_fg
    exact hB_fg

  have B_tensor_is_noetherian : IsNoetherianRing (B ⊗[k] R) := by
    apply isNoetherianRing_baseChange_of_finiteType hB_fintype

  let S' := S.map (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] R)

  letI : Algebra R (B ⊗[k] R) := Algebra.TensorProduct.includeRight.toAlgebra

  let φ : R →+* Localization S' :=
    (algebraMap (B ⊗[k] R) (Localization S')).comp
      (Algebra.TensorProduct.includeRight : R →ₐ[k] B ⊗[k] R)
  letI : Algebra R (K ⊗[k] R) := Algebra.TensorProduct.includeRight.toAlgebra

  have tensor_localiz : K ⊗[k] R ≃ₐ[R] Localization S' := by
    sorry
  haveI := B_tensor_is_noetherian
  -- 使用 isNoetherianRing_of_ringEquiv 的正确方式
  have localiz_noetherian : IsNoetherianRing (Localization S') :=
    IsLocalization.isNoetherianRing S' (Localization S') B_tensor_is_noetherian
  exact isNoetherianRing_of_ringEquiv (Localization S') tensor_localiz.symm.toRingEquiv






def Submonoid.restrict {M N : Type*} [CommMonoid M] [CommMonoid N] (f : M →* N)
    (S : Submonoid M) : Submonoid N :=
  S.map f

theorem isLocalization_of_localization_tensor {k K : Type*} [Field k] [Field K] [Algebra k K]
    (B : Subalgebra k K) (S : Submonoid B) (R : Type*) [CommRing R] [Algebra k R]
    (S' : Submonoid (B ⊗[k] R))
    (hS' : S' = Submonoid.restrict
      (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] R).toMonoidHom S) :
    IsLocalization S' (K ⊗[k] R) := by
