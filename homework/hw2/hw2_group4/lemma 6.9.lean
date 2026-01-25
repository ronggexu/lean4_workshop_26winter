-- import Mathlib.RingTheory.Localization.AtPrime.Basic
-- import Mathlib.RingTheory.Localization.Away.Basic
-- import Mathlib.RingTheory.Localization.Basic
-- import Mathlib.RingTheory.Localization.Defs
-- import Mathlib.RingTheory.Ideal.Lattice
-- import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib

open Localization

section

variable (R : Type _) [CommRing R] (p : Ideal R) [p.IsPrime]

theorem powers_le_comap_primeCompl {f : R} (hf_not_mem : f ∉ p) :
    Submonoid.powers f ≤ Submonoid.comap (RingHom.id R) p.primeCompl := by
  intro x hx
  -- hx : x ∈ Submonoid.powers f
  rcases hx with ⟨n, rfl⟩
  -- 目标：f^n ∈ Submonoid.comap (RingHom.id R) p.primeCompl
  -- 即 (RingHom.id R) (f^n) ∈ p.primeCompl
  -- 由于 RingHom.id R 是恒等映射，等价于 f^n ∈ p.primeCompl
  -- p.primeCompl 的定义是 {x | x ∉ p}
  simp only [Submonoid.mem_comap, RingHom.id_apply, Ideal.mem_primeCompl_iff]
  -- 现在目标：f^n ∉ p
  intro h  -- 假设 f^n ∈ p
  have hp : p.IsPrime := inferInstance
  -- 因为 p 是素理想，所以 f ∈ p
  exact hf_not_mem (hp.mem_of_pow_mem n h)

noncomputable def awayOneEquiv : Localization.Away (1 : R) ≃ₐ[R] R :=
  -- IsLocalization.algEquiv (Submonoid.powers 1) R
  (IsLocalization.atOne R (Localization.Away (1 : R))).symm

theorem exists_f_not_mem_prime_of_domain [IsDomain R] :
    ∃ (f : R) (hf : f ∉ p), Function.Injective
       ((IsLocalization.map (Localization.AtPrime p) (RingHom.id R)
        (powers_le_comap_primeCompl R p hf)) :
        Localization (Submonoid.powers f) →+* Localization.AtPrime p) := by
  -- 1. 证明 1 ∉ p
  have h_1_not_mem : 1 ∉ p := by
    intro h1  -- 反证法
    have hp : p.IsPrime := inferInstance
    -- 因为 p 是素理想且 1 ∈ p，则 p = ⊤
    have h_top : p = ⊤ := p.eq_top_iff_one.mpr h1
    -- 但已知 p.IsPrime 意味着 p ≠ ⊤，矛盾
    exact hp.ne_top h_top
  -- 2. 取 f = 1转化为证明R_1 → R_p 是单射
  refine ⟨1, h_1_not_mem, ?_⟩
  let φ : Localization.Away (1 : R) →+* Localization.AtPrime p :=
    IsLocalization.map  (Localization.AtPrime p)
                        (RingHom.id R) (powers_le_comap_primeCompl R p h_1_not_mem)
  -- 3. 取 x, y 证明 φ x = φ y
  intro x y h
  -- 4. 引理：R → R_p 是单射
  have hinj : Function.Injective (algebraMap R (Localization.AtPrime p)) :=
    IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
  -- 5. 引理：φ 是R1 → R 和 R → R_p 的复合
  have h_comp : φ = (algebraMap R (Localization.AtPrime p)).comp (awayOneEquiv R).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (1 : R))
    ext r
    calc
      φ (algebraMap R (Localization.Away (1 : R)) r)
          = algebraMap R (Localization.AtPrime p) r := by
            simp [φ, IsLocalization.map_eq]
      _ = (algebraMap R (Localization.AtPrime p))
            ((awayOneEquiv R) (algebraMap R (Localization.Away (1 : R)) r)) := by
            simp [awayOneEquiv, IsLocalization.atOne]
      _ = ((algebraMap R (Localization.AtPrime p)).comp (awayOneEquiv R).toRingHom)
            (algebraMap R (Localization.Away (1 : R)) r) := by
            rfl
  -- 6. 引理：直接计算复合的映射是单射
  have h' : ((algebraMap R (Localization.AtPrime p)).comp (awayOneEquiv R).toRingHom) x =
            ((algebraMap R (Localization.AtPrime p)).comp (awayOneEquiv R).toRingHom) y := by
    calc
      ((algebraMap R (Localization.AtPrime p)).comp (awayOneEquiv R).toRingHom) x
          = φ x := by rw [h_comp]
      _ = φ y := h
      _ = ((algebraMap R (Localization.AtPrime p)).comp (awayOneEquiv R).toRingHom) y := by
        rw [h_comp]
  exact (awayOneEquiv R).injective (hinj h')

end

section

#check Set.not_nonempty_iff_eq_empty

variable (R : Type _) [CommRing R] [IsNoetherianRing R]
variable (p : Ideal R) [hp : p.IsPrime]

theorem exists_f_not_mem_prime_injective_localization_noetherian :
    ∃ (f : R) (hf : f ∉ p), Function.Injective
       ((IsLocalization.map (Localization.AtPrime p) (RingHom.id R)
        (powers_le_comap_primeCompl R p hf)) :
        Localization (Submonoid.powers f) →+* Localization.AtPrime p) := by
  -- 定义同态 φ : R → R_p 的核 I
  let φ : R →+* Localization.AtPrime p := algebraMap R (Localization.AtPrime p)
  let I : Ideal R := RingHom.ker φ
  -- R 是诺特环，所以 I 是有限生成的
  have hI_fg : I.FG := IsNoetherian.noetherian I
  rcases hI_fg with ⟨s, hs⟩
  -- 如果 I = 0，取 f = 1
  by_cases hI_zero : I = ⊥
  · have one_nin_p : 1 ∉ p := by
      intro h1  -- 反证法
      have hp : p.IsPrime := inferInstance
      -- 因为 p 是素理想且 1 ∈ p，则 p = ⊤
      have h_top : p = ⊤ := p.eq_top_iff_one.mpr h1
      -- 但已知 p.IsPrime 意味着 p ≠ ⊤，矛盾
      exact hp.ne_top h_top
    refine ⟨1, one_nin_p, ?_⟩
    · -- 当 I = 0 时，R → R_p 已经是单射
      rw [RingHom.injective_iff_ker_eq_bot]
      set φ : R →+* Localization.AtPrime p := algebraMap R (Localization.AtPrime p) with φ_def
      -- have h_map_eq : ((IsLocalization.map (Localization.AtPrime p) (RingHom.id R)
      --     (powers_le_comap_primeCompl R p one_nin_p)) :
      --     Localization (Submonoid.powers (1 : R)) →+* Localization.AtPrime p) =
      --     (algebraMap R (Localization.AtPrime p)).comp
      --     (algebraMap (Localization (Submonoid.powers (1 : R))) R) := by
      --   sorry
      let ψ : Localization (Submonoid.powers (1 : R)) →+* Localization.AtPrime p :=
        IsLocalization.map (Localization.AtPrime p) (RingHom.id R)
            (powers_le_comap_primeCompl R p one_nin_p)
      set ψ := (IsLocalization.map (Localization.AtPrime p) (RingHom.id R)
          (powers_le_comap_primeCompl R p one_nin_p) :
          Localization (Submonoid.powers (1 : R)) →+* Localization.AtPrime p) with hψ_def
      -- 首先证明 Localization (powers 1) ≅ R
      have h_iso : Localization (Submonoid.powers (1 : R)) ≃ₐ[R] R := by sorry

      have hψ_eq : ψ = φ.comp (h_iso : Localization (Submonoid.powers (1 : R)) →+* R) := by
        sorry
        -- ext x
        -- simp [ψ, h_iso, IsLocalization.map_apply]

      -- 重写目标
      rw [hψ_eq]

      -- 计算复合映射的核
      rw [RingHom.ker]

      -- 由于 h_iso.symm 是同构，其核为 ⊥
      have h_ker_iso : RingHom.ker (h_iso : Localization (Submonoid.powers (1 : R)) →+* R) = ⊥ := by
        sorry
        -- exact RingHom.ker_eq_bot_of_injective h_iso.symm.injective

      rw [RingHom.ker] at h_ker_iso
      calc
        Ideal.comap (φ.comp h_iso) ⊥
            = Ideal.comap h_iso (Ideal.comap φ ⊥) := by
          rw [← Ideal.comap_comap]
          rfl
        _ = Ideal.comap h_iso (RingHom.ker φ) := by rw [RingHom.ker_eq_comap_bot]
        _ = Ideal.comap h_iso I := rfl
        _ = Ideal.comap h_iso ⊥ := by rw [hI_zero]
        _ = ⊥ := h_ker_iso
      -- rw [h_ker_iso, Ideal.map_bot, sup_bot_eq]

      -- -- 现在需要证明：φ⁻¹'(⊥) = ⊥
      -- -- 但 φ 是单射（ker φ = ⊥），所以 φ⁻¹'(⊥) = ⊥
      -- rw [show RingHom.ker φ = ⊥ from hI_zero]
      -- rfl

  -- I ≠ 0，s 非空
  have hs_nonempty : s.Nonempty := by
    by_contra h_not_nonempty
    have : s = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      have : s.Nonempty := ⟨x, hx⟩
      exact h_not_nonempty this
    rw [this, Finset.coe_empty, Ideal.span_empty] at hs
    have : I = ⊥ := by
      rw [hs]
    exact hI_zero this
  -- 步骤3：对每个 a ∈ s，存在 u ∉ p 使得 u * a = 0
  have h_for_gens : ∀ a ∈ s, ∃ (u : R), u ∉ p ∧ u * a = 0 := by
    intro a ha
    have ha_I : a ∈ I := by
      rw [← hs]
      exact Ideal.subset_span (by simpa using ha)
    rw [RingHom.mem_ker] at ha_I
    have h := (IsLocalization.map_eq_zero_iff (M := p.primeCompl)
        (S := Localization.AtPrime p) (r := a)).mp ha_I
    rcases h with ⟨⟨u, hu⟩, hu_eq⟩
    exact ⟨u, hu, hu_eq⟩

  -- 步骤4：取 f 为所有 u 的乘积
  -- 将 s 转换为 Finset
  -- let s_fin : Finset R := s.toFinite.toFinset
  -- have hs_fin : (s_fin : Set R) = s := by simp
  have hs_fin : (s : Set R).Finite := Finset.finite_toSet s

  -- 选择函数：为每个 a 选择一个 u
  choose u hu_not_mem hu_mul_eq_zero using h_for_gens

  -- 定义 f = ∏_{a ∈ s} u a
  let f : R := ∏ a ∈ s.attach, u a.1 a.2

  -- 证明 f ∉ p
  have hf_not_mem : f ∉ p := by
    intro h
    dsimp [f] at h
    -- 因为 p 是素理想，存在某个 u a ∈ p
    have h2 := (hp.prod_mem_iff (s := s.attach) (x := fun a => u a.1 a.2)).mp h
    rcases h2 with ⟨x, hx⟩
    exact (hu_not_mem x.1 x.2) hx.2

  -- 证明对于所有 a ∈ s，有 f * a = 0
  have h_f_mul_a_eq_zero : ∀ a ∈ s, f * a = 0 := by
    intro a ha
    -- have ha_fin : a ∈ s := by
    --   simpa [hs_fin] using ha
    -- f 包含 u a 作为因子
    -- have : (u a ha) ∣ f := Finset.dvd_prod_of_mem (f := λ x => u x.1 x.2) (s := s.attach)  ha
    have : (u a ha) ∣ f := by
      have ha_attach : (⟨a, ha⟩ : {x // x ∈ s}) ∈ s.attach := by
        simp
      -- 使用 dvd_prod_of_mem
      exact Finset.dvd_prod_of_mem (fun (x : {x // x ∈ s}) => u x.1 x.2) ha_attach
    rcases this with ⟨k, hk⟩
    rw [mul_comm] at hk
    rw [hk, mul_assoc, hu_mul_eq_zero a ha, mul_zero]

  have h_f_mul_a_eq_zero_for_all_a_in_I : ∀ a ∈ I, f * a = 0 := by
    intro a ha
    rw [← hs] at ha
    have ha' : a ∈ Submodule.span R (s : Set R) := ha

    refine Submodule.span_induction
      (mem := fun x hx => ?_)        -- 第一个参数：生成元的情况
      (zero := ?_)                   -- 第二个参数：零元的情况
      (add := fun x y hx hy hx_val hy_val => ?_)  -- 第三个参数：加法的情况
      (smul := fun r x hx hx_val => ?_)          -- 第四个参数：标量乘法的情况
      (hx := ha')                   -- 最后一个参数：a ∈ span s 的假设

    · -- mem: 对于所有 x ∈ s，有 f * x = 0
      have : x ∈ s := hx
      exact h_f_mul_a_eq_zero x this

    · -- zero: f * 0 = 0
      simp

    · -- add: 如果 f * x = 0 且 f * y = 0，则 f * (x + y) = 0
      simp [mul_add, hx_val, hy_val]

    · -- smul: 如果 f * x = 0，则对于任意 r : R，有 f * (r • x) = 0
      -- 在环 R 作为自身的模中，r • x = r * x
      calc
        f * (r • x) = f * (r * x) := rfl
        _ = (f * r) * x := by ring
        _ = (r * f) * x := by rw [mul_comm f r]
        _ = r * (f * x) := by ring
        _ = r * 0 := by rw [hx_val]
        _ = 0 := by simp

  -- 证明映射是单射
  refine ⟨f, hf_not_mem, ?_⟩
  intro x y hxy
  -- 详细证明需要更多局部化理论
  -- 定义映射 ψ : Localization.Away f → Localization.AtPrime p
  let ψ : Localization (Submonoid.powers f) →+* Localization.AtPrime p :=
    IsLocalization.map (Localization.AtPrime p) (RingHom.id R)
        (powers_le_comap_primeCompl R p hf_not_mem)
  set ψ := (IsLocalization.map (Localization.AtPrime p) (RingHom.id R)
      (powers_le_comap_primeCompl R p hf_not_mem) :
      Localization (Submonoid.powers f) →+* Localization.AtPrime p) with hψ_def

  -- 步骤1: 证明 ψ 是单射等价于 ker ψ = 0
  -- 在Lean中，Function.Injective 已经直接对应单射

  -- 步骤2-4: 证明 ψ 是单射
  -- 由于 Localization.Away f 中的元素可以表示为 (a, f^k) 的形式
  -- 我们只需要考虑形如 mk' a (f^k) 的元素
  -- 首先证明对于任意 a : R, k : ℕ，如果 ψ(mk' a (f^k)) = 0，则 mk' a (f^k) = 0

  have h_f_pw_k_in_Rf (k : ℕ): f^k ∈ Submonoid.powers f := ⟨k, by simp⟩
  have h_zero : ∀ (a : R) (k : ℕ),
      ψ (IsLocalization.mk' (Localization.Away f) a ⟨f^k, h_f_pw_k_in_Rf k⟩) = 0 →
      IsLocalization.mk' (Localization.Away f) a ⟨f^k, h_f_pw_k_in_Rf k⟩ = 0 := by
    intro a k h
    -- ψ(mk' a (f^k)) = 0
    -- 根据局部化映射的定义，ψ(mk' a (f^k)) = mk' (RingHom.id R a) (f^k) = mk' a (f^k) 在 R_p 中
    -- 但更准确地说，ψ(mk' a (f^k)) = a / f^k 在 R_p 中
    -- h 表示 a/f^k = 0 在 R_p 中

    -- 这意味着存在 u ∉ p 使得 u * a = 0
    -- 由于 f ∉ p 且 p 是素理想，f^k ∉ p
    have h_fk_not_mem : f^k ∉ p := by
      intro hfk
      exact hf_not_mem (hp.mem_of_pow_mem k hfk)

    -- 现在可以使用 map_mk'
    have h_mk : ψ (IsLocalization.mk' (Localization.Away f) a ⟨f^k, h_f_pw_k_in_Rf k⟩) =
                IsLocalization.mk' (Localization.AtPrime p) a ⟨f^k, h_fk_not_mem⟩ :=
      IsLocalization.map_mk' (powers_le_comap_primeCompl R p hf_not_mem) a ⟨f^k, h_f_pw_k_in_Rf k⟩

    -- simp [h_mk] at h
    rw [h_mk] at h

    -- 现在 h: IsLocalization.mk' (Localization.AtPrime p) a ⟨f^k, ...⟩ = 0

    -- 使用 mk'_eq_zero_iff
    let y : p.primeCompl := ⟨f^k, powers_le_comap_primeCompl R p hf_not_mem (h_f_pw_k_in_Rf k)⟩
    rcases (IsLocalization.mk'_eq_zero_iff (M := p.primeCompl)
            (S := Localization.AtPrime p) a y).mp h with ⟨v, hv⟩

    -- a 在 R_p 中的像为0，所以 a ∈ ker φ = I
    have ha_I : a ∈ I := by
      rw [RingHom.mem_ker]
      -- exact h_zero_in_Rp
      rw [IsLocalization.map_eq_zero_iff (M := p.primeCompl) (S := Localization.AtPrime p) a]
      exact ⟨v, hv⟩

    -- 由假设，f * a = 0
    have h_fa : f * a = 0 := h_f_mul_a_eq_zero_for_all_a_in_I a ha_I

    -- 在 R_f 中，由于 f 可逆，a = 0
    -- 具体来说：mk' a (f^k) = mk' (f * a) (f^(k+1)) = mk' 0 (f^(k+1)) = 0
    -- calc
    --   IsLocalization.mk' (Localization.Away f) a ⟨f^k, ⟨k, rfl⟩⟩
    --       = IsLocalization.mk' (Localization.Away f) (f * a) ⟨f^(k+1), ⟨k+1, by ring⟩⟩ := by
    --         rw [IsLocalization.mk'_eq_iff_eq]
    --         simp [pow_succ]
    --   _ = IsLocalization.mk' (Localization.Away f) 0 ⟨f^(k+1), ⟨k+1, by ring⟩⟩ := by rw [h_fa]
    --   _ = 0 := by simp
    rw [IsLocalization.mk'_eq_zero_iff]
    let f' : ↥(Submonoid.powers f) := ⟨f, 1, by simp⟩
    let h_fa' : f' * a = 0 := by
      dsimp [f']
      exact h_fa
    exact ⟨f', h_fa'⟩
  -- 现在证明 ψ 是单射
  -- 由于 x 和 y 在 Localization.Away f 中，它们可以表示为分式
  -- 设 x = mk' a s, y = mk' b t，其中 s, t ∈ Submonoid.powers f

  rcases IsLocalization.mk'_surjective (Submonoid.powers f) x with ⟨⟨a, ma⟩, hx⟩
  rcases ma with ⟨ma_val, k, h_f_pw_k_eq_ma_val⟩
  rcases IsLocalization.mk'_surjective (Submonoid.powers f) y with ⟨⟨b, mb⟩, hy⟩
  rcases mb with ⟨mb_val, l, h_f_pw_l_eq_mb_val⟩

  have hx' : x = IsLocalization.mk' (Localization.Away f) a ⟨f^k, h_f_pw_k_in_Rf k⟩ := by
    rw [← hx]
    -- 现在需要证明：mk' a ⟨ma_val, ha_proof⟩ = mk' a ⟨f^k, h_f_pw_k_in_Rf k⟩
    apply IsLocalization.mk'_eq_of_eq
    -- 需要证明：某个等式成立
    simp [h_f_pw_k_eq_ma_val]
  have hy' : y = IsLocalization.mk' (Localization.Away f) b ⟨f^l, h_f_pw_k_in_Rf l⟩ := by
    rw [← hy]
    -- 现在需要证明：mk' a ⟨ma_val, ha_proof⟩ = mk' a ⟨f^k, h_f_pw_k_in_Rf k⟩
    apply IsLocalization.mk'_eq_of_eq
    -- 需要证明：某个等式成立
    simp [h_f_pw_l_eq_mb_val]

  rw [hx', hy'] at hxy
  -- 现在 x = mk' a (f^k), y = mk' b (f^l)
  -- hxy: ψ(mk' a (f^k)) = ψ(mk' b (f^l))

  -- 等价于 ψ(mk' a (f^k) - mk' b (f^l)) = 0
  have h_diff_zero : ψ (IsLocalization.mk' (Localization.Away f) a ⟨f^k, h_f_pw_k_in_Rf k⟩ -
                      IsLocalization.mk' (Localization.Away f) b ⟨f^l, h_f_pw_k_in_Rf l⟩) = 0 := by
    rw [RingHom.map_sub, hxy, sub_self]

  -- 将差写成单个分式
  have h_diff_eq : IsLocalization.mk' (Localization.Away f) a ⟨f^k, h_f_pw_k_in_Rf k⟩ -
                  IsLocalization.mk' (Localization.Away f) b ⟨f^l, h_f_pw_k_in_Rf l⟩ =
                  IsLocalization.mk' (Localization.Away f) (a * f^l - b * f^k)
                  ⟨f^(k+l), h_f_pw_k_in_Rf (k+l)⟩ := by
    rw [← IsLocalization.mk'_sub]
    simp [pow_add]

  rw [h_diff_eq] at h_diff_zero

  -- 应用 h_zero 引理
  have h_mk_zero : IsLocalization.mk' (Localization.Away f) (a * f^l - b * f^k)
      ⟨f^(k+l), h_f_pw_k_in_Rf (k+l)⟩ = 0 :=
    h_zero (a * f^l - b * f^k) (k+l) h_diff_zero

  -- 这意味着在 R_f 中 mk' (a * f^l - b * f^k) (f^(k+l)) = 0
  -- 所以 mk' a (f^k) = mk' b (f^l)
  rw [h_mk_zero, ← hx', ← hy'] at h_diff_eq
  -- 实际上，我们已经有 x - y = 0，所以 x = y
  exact sub_eq_zero.mp h_diff_eq

#check IsLocalization.mk'
#check IsLocalization.map_mk'
#check IsLocalization.mk'_eq_zero_iff
#check IsLocalization.map_eq_zero_iff
