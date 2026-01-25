import Mathlib

open Algebra
open Module
set_option linter.style.longLine false

variable {R : Type*} [CommRing R]
variable (S S' : Submonoid R)
variable {M : Type*} [AddCommGroup M] [Module R M]


namespace DoubleLocalization

-- 引理：S ⊔ S' 中的元素在 M_S_S' 上作用是可逆的 -祁柏睿负责部分
noncomputable def f_11 : S → (LocalizedModule S' M) × S → LocalizedModule S (LocalizedModule S' M) :=
  fun s1 (sm1, s2) =>  LocalizedModule.mk sm1 (s1 * s2)
lemma calcu_1 (s1 : S) (x : (LocalizedModule S' M) × S) : f_11 S S' s1 x = LocalizedModule.mk (x.1) (s1 * x.2) := by
 rfl
theorem well_defined_1 (saa : S) (x y : (LocalizedModule S' M) × S) (h : LocalizedModule.r S (LocalizedModule S' M) x y) : f_11 S S' saa x = f_11 S S' saa y := by
  rw[calcu_1]
  rw[calcu_1]
  refine LocalizedModule.mk_eq.mpr ?_
  obtain ⟨t, ht⟩ := h
  use t
  rw[mul_smul , mul_smul , ← mul_smul , mul_comm , mul_smul , ←mul_smul]
  nth_rw 2 [← mul_smul]
  nth_rw 2 [mul_comm]
  rw[mul_smul , mul_smul]
  rw[ht]
noncomputable def f_1 : (s1 : S) → LocalizedModule S (LocalizedModule S' M) → LocalizedModule S (LocalizedModule S' M) :=
  fun s1 m1 => Quotient.lift (f_11 S S' s1) (well_defined_1 S S' s1) m1
lemma calcu1 (s1 s : S) (m : LocalizedModule S' M) : f_1  S S' s1 (LocalizedModule.mk m s) = (LocalizedModule.mk m (s * s1)) := by
  have A : f_1  S S' s1 (LocalizedModule.mk m s) = f_11 S S' s1 (m , s) := by rfl --名字里是1不是l
  rw[A]
  rw[calcu_1]
  have B : (m , s).1 = m := by rfl
  have C : (m , s).2 = s := by rfl
  rw[B]
  rw[C]
  rw[mul_comm]
noncomputable def f_22 : S' → M × S' → (LocalizedModule S' M) :=
  fun s1' (m , s') => LocalizedModule.mk m (s' * s1')
theorem well_defined_22 (saa : S') (x y : M × S') (h : LocalizedModule.r S' M x y) : f_22 S' saa x = f_22 S' saa y := by
  rw[f_22]
  rw[f_22]
  refine LocalizedModule.mk_eq.mpr ?_
  obtain ⟨h , hy⟩ := h
  use h
  rw[mul_comm]
  nth_rw 2 [mul_comm]
  rw[mul_smul , ←mul_smul , mul_comm , mul_smul , mul_smul]
  nth_rw 3 [←mul_smul]
  rw[mul_comm , mul_smul]
  rw[hy]
noncomputable def f_21 : S' → LocalizedModule S' M →  (LocalizedModule S' M) :=
  fun s' m => Quotient.lift (f_22 S' s') (well_defined_22 S' s') m
noncomputable def f_20 : S' →  (LocalizedModule S' M)  ×  S→ LocalizedModule S (LocalizedModule S' M) :=
 fun s' (m , s) => LocalizedModule.mk (f_21 S' s' m) s
theorem calcu_21 (saa : S') (s : S') (m : M) : f_21 S' saa (LocalizedModule.mk m s) = LocalizedModule.mk m (s * saa) := by
  rfl
theorem well_defined_20 (saa : S') (x y : (LocalizedModule S' M) × S) (h : LocalizedModule.r S (LocalizedModule S' M) x y)
 : f_20 S S' saa x = f_20 S S' saa y := by
  rw[f_20 , f_20]
  refine LocalizedModule.mk_eq.mpr ?_
  obtain ⟨h , hy⟩ := h
  revert hy
  refine Quotient.inductionOn x.1 ?_
  intro ⟨m1 , s1⟩
  refine Quotient.inductionOn y.1 ?_
  intro ⟨m2 , s2⟩
  have A : ⟦(m1, s1)⟧  = LocalizedModule.mk m1 s1 := by rfl
  have B : ⟦(m2, s2)⟧  = LocalizedModule.mk m2 s2 := by rfl
  intro hy
  rw[A , B] at hy
  rw[A , B]
  rw[calcu_21 , calcu_21]
  use h
  have D :(h : R) • (y.2 : R)• LocalizedModule.mk m1 s1= LocalizedModule.mk (h • y.2 • m1) s1 := by
    rw[LocalizedModule.smul'_mk , LocalizedModule.smul'_mk]
    rfl
  have E1 :  h • y.2 • LocalizedModule.mk m1 s1 = (h :R) • (y.2 : R) • LocalizedModule.mk m1 s1 := by rfl
  have E2 :  h • x.2 • LocalizedModule.mk m2 s2 = (h :R) • (x.2 : R) • LocalizedModule.mk m2 s2 := by rfl
  have F :(h : R) • (x.2 : R)• LocalizedModule.mk m2 s2= LocalizedModule.mk (h • x.2 • m2) s2 := by
    rw[LocalizedModule.smul'_mk , LocalizedModule.smul'_mk]
    rfl
  have G :(h : R) • (y.2 : R)• LocalizedModule.mk m1 (s1 * saa) = LocalizedModule.mk (h • y.2 • m1) (s1 * saa) := by
    rw[LocalizedModule.smul'_mk , LocalizedModule.smul'_mk]
    rfl
  have H :(h : R) • (x.2 : R)• LocalizedModule.mk m2 (s2 * saa) = LocalizedModule.mk (h • x.2 • m2) (s2 * saa) := by
    rw[LocalizedModule.smul'_mk , LocalizedModule.smul'_mk]
    rfl
  have I1 :  h • y.2 • LocalizedModule.mk m1 (s1 * saa) = (h :R) • (y.2 : R) • LocalizedModule.mk m1 (s1 * saa) := by rfl
  have I2 :  h • x.2 • LocalizedModule.mk m2 (s2 * saa) = (h :R) • (x.2 : R) • LocalizedModule.mk m2 (s2 * saa) := by rfl
  rw[I1 , I2 ,G , H]
  rw[E1 , E2 , D , F] at hy
  calc
    LocalizedModule.mk (h • y.2 • m1) (s1 * saa) = (Localization.mk 1 saa) • LocalizedModule.mk (h • y.2 • m1) s1 := by
      rw[LocalizedModule.mk_smul_mk]
      rw[mul_comm]
      rw[one_smul]
    _ = (Localization.mk 1 saa) • LocalizedModule.mk (h • x.2 • m2) s2 := by rw[hy]
    _ = LocalizedModule.mk (h • x.2 • m2) (s2 * saa) := by
      rw[LocalizedModule.mk_smul_mk]
      rw[mul_comm]
      rw[one_smul]
noncomputable def f_2 : S' → LocalizedModule S (LocalizedModule S' M) → LocalizedModule S (LocalizedModule S' M) :=
  fun saa m => Quotient.lift (f_20 S S' saa ) (well_defined_20 S S' saa) m
lemma calcu_2 (saa s' : S') (s : S) (m : M) : f_2 S S' saa (LocalizedModule.mk (LocalizedModule.mk m s') s) = LocalizedModule.mk (LocalizedModule.mk m (s' * saa)) s := by
  have A : f_2 S S' saa (LocalizedModule.mk (LocalizedModule.mk m s') s) = f_20 S S' saa ((LocalizedModule.mk m s') , s) := by rfl
  rw[A]
  rfl


theorem is_unit_action_on_double_loc (t : ↥(S ⊔ S')) :
  IsUnit (LinearMap.lsmul R (LocalizedModule S (LocalizedModule S' M)) (t : R)) := by
  /-let M1 := LocalizedModule S (LocalizedModule S' M)
  have A : M1 = LocalizedModule S (LocalizedModule S' M) := by rfl-/
  have B : ∃ (s1 : S) , ∃ s2 : S' , ↑s1 • (s2 : R) = ↑t:= by
    obtain ⟨x, hx, y, hy, h_eq⟩ := Submonoid.mem_sup.mp t.property
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, h_eq⟩
  rcases B with ⟨s1 , s2 , hyp⟩
  rw[←hyp]
  have C : LinearMap.lsmul R (LocalizedModule S (LocalizedModule S' M)) ((s1 : R) • (s2 : R) )
  = LinearMap.lsmul R (LocalizedModule S (LocalizedModule S' M)) (s1 : R) ∘ LinearMap.lsmul R (LocalizedModule S (LocalizedModule S' M)) (s2 : R)
  := by
    ext x
    rw[LinearMap.lsmul_apply , LinearMap.lsmul_eq_DistribMulAction_toLinearMap , LinearMap.lsmul_eq_DistribMulAction_toLinearMap]
    simp only [smul_eq_mul, Function.comp_apply, DistribMulAction.toLinearMap_apply, map_smul]
    rw [mul_smul]
    exact smul_comm (↑s1) (↑s2) x
  have D : s1 • (s2 : R) = (s1 : R) • (s2 : R) := by rfl
  rw[D]
  suffices hyp : Function.Bijective ((LinearMap.lsmul R (LocalizedModule S (LocalizedModule S' M))) ↑s2) ∧ Function.Bijective ((LinearMap.lsmul R (LocalizedModule S (LocalizedModule S' M))) ↑s1)
  · have A : Function.Bijective (LinearMap.lsmul R (LocalizedModule S (LocalizedModule S' M)) (s1 : R) ∘ LinearMap.lsmul R (LocalizedModule S (LocalizedModule S' M)) (s2 : R)) := by
      apply Function.Bijective.comp
      · tauto
      · tauto
    rw[← C] at A
    rw[Module.End.isUnit_iff]
    exact A
  · constructor
    · rw[Function.bijective_iff_has_inverse]
      use f_2 S S' s2
      constructor
      · intro x
        simp only [LinearMap.lsmul_apply]
        refine Quotient.inductionOn x ?_
        intro ⟨m, s⟩
        have K : ⟦(m , s)⟧ = LocalizedModule.mk m s := by rfl
        rw[K]
        refine Quotient.inductionOn m ?_
        intro ⟨m , s'⟩
        have J : ⟦(m , s')⟧ = LocalizedModule.mk m s' := by rfl
        rw[J]
        have L : (s2 : R) • (LocalizedModule.mk (LocalizedModule.mk m s') s) = LocalizedModule.mk ((LocalizedModule.mk ((s2 : R) • m) s')) s := by
          rw[LocalizedModule.smul'_mk , LocalizedModule.smul'_mk ]
        rw[L]
        rw[calcu_2]
        have M : LocalizedModule.mk (↑s2 • m) (s' * s2) = LocalizedModule.mk m s' := by
          exact LocalizedModule.mk_cancel_common_right s' s2 m
        rw[← M]
        rfl
      · intro x
        simp only [LinearMap.lsmul_apply]
        refine Quotient.inductionOn x ?_
        intro ⟨m, s⟩
        have N : ⟦(m , s)⟧ = LocalizedModule.mk m s := by rfl
        rw[N]
        refine Quotient.inductionOn m ?_
        intro ⟨m , s'⟩
        have J : ⟦(m , s')⟧ = LocalizedModule.mk m s' := by rfl
        rw[J]
        rw[calcu_2]
        have L : (s2 : R) • (LocalizedModule.mk (LocalizedModule.mk m (s' * s2)) s) = LocalizedModule.mk ((LocalizedModule.mk ((s2 : R) • m) (s' * s2))) s := by
          rw[LocalizedModule.smul'_mk , LocalizedModule.smul'_mk ]
        rw[L]
        have M :LocalizedModule.mk (↑s2 • m) (s' * s2) = LocalizedModule.mk m s' := by
          exact LocalizedModule.mk_cancel_common_right s' s2 m
        rw[← M]
        rfl
    · rw[Function.bijective_iff_has_inverse]
      use f_1 S S' s1
      constructor
      · intro x
        simp only [LinearMap.lsmul_apply]
        refine Quotient.inductionOn x ?_
        intro ⟨m, s⟩
        have E : ⟦(m , s)⟧ = LocalizedModule.mk m s := by rfl
        rw[E]
        have F : (s1 : R) • LocalizedModule.mk m s =LocalizedModule.mk (s1 • m) s := by
          rw[LocalizedModule.smul'_mk]
          rfl
        rw[F]
        rw[calcu1]
        exact LocalizedModule.mk_cancel_common_right s s1 m
      · intro x
        simp only [LinearMap.lsmul_apply]
        refine Quotient.inductionOn x ?_
        intro ⟨m , s⟩
        have E : ⟦(m , s)⟧ = LocalizedModule.mk m s := by rfl
        rw[E]
        rw[calcu1]
        have F : (s1 : R) • LocalizedModule.mk m (s * s1) =LocalizedModule.mk (s1 • m) (s * s1) := by
          rw[LocalizedModule.smul'_mk]
          rfl
        rw[F]
        exact LocalizedModule.mk_cancel_common_right s s1 m

--蒲宇宸负责部分
--引理：S 中的元素在 S⁻¹M 上作用是可逆的
theorem is_unit_action (t : S) :
  IsUnit (LinearMap.lsmul R (LocalizedModule S M) t) := by
  rw [LinearMap.lsmul_eq_DistribMulAction_toLinearMap]
  change IsUnit (algebraMap R (Module.End R (LocalizedModule S M)) (t : R))
  exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S M) t
-- 针对 S 的证明（用于外层 lift）
theorem is_unit_action_on_double_1 (t : S) :
  IsUnit (LinearMap.lsmul R (LocalizedModule (S ⊔ S') M) t) := by
  have h_mem : (t : R) ∈ (S ⊔ S') := Submonoid.mem_sup_left t.prop
  let t' : ↑(S ⊔ S') := ⟨t.val, h_mem⟩
  suffices IsUnit (LinearMap.lsmul R (LocalizedModule (S ⊔ S') M) t') by
    convert this using 2
  apply is_unit_action
-- 针对 S' 的证明（用于内层 lift）
theorem is_unit_action_on_double_2 (t : S') :
  IsUnit (LinearMap.lsmul R (LocalizedModule (S ⊔ S') M) t) := by
  have h_mem : (t : R) ∈ (S ⊔ S') := Submonoid.mem_sup_right t.prop
  let t' : ↑(S ⊔ S') := ⟨t.val, h_mem⟩
  suffices IsUnit (LinearMap.lsmul R (LocalizedModule (S ⊔ S') M) t') by
    convert this using 2
  apply is_unit_action
/-- 从 S⁻¹(S'⁻¹M) 到 (SS')⁻¹M 的映射 -/
noncomputable def toCombined :
    LocalizedModule S (LocalizedModule S' M) →ₗ[R] LocalizedModule (S ⊔ S') M :=
  -- 第一步：剥离外层的 S
  LocalizedModule.lift S
    ( -- 第二步：剥离内层的 S'
      LocalizedModule.lift S'
        (LocalizedModule.mkLinearMap (S ⊔ S') M) -- 基础映射 m ↦ m/1
        (is_unit_action_on_double_2 S S' ) -- 证明 s' 在 (SS')⁻¹M 可逆
    )
    (is_unit_action_on_double_1 S S' ) -- 证明 s 在 (SS')⁻¹M 可逆
/-- 从 (SS')⁻¹M 到 S⁻¹(S'⁻¹M) 的映射 -/
noncomputable def fromCombined :
    LocalizedModule (S ⊔ S') M →ₗ[R] LocalizedModule S (LocalizedModule S' M) :=
  LocalizedModule.lift (S ⊔ S')
    ( -- 基础映射：m ↦ (m/1)/1
      LinearMap.comp (LocalizedModule.mkLinearMap S (LocalizedModule S' M)) (LocalizedModule.mkLinearMap S' M)
    )
    (is_unit_action_on_double_loc S S' ) -- 使用上面的引理1

--祁柏睿负责部分
lemma cal_from (m : M) (s : S) (s' : S') (s'' : ↥(S ⊔ S')) (h : s'' = (s : R) * s')
  : fromCombined S S'  (LocalizedModule.mk m s'')= LocalizedModule.mk (LocalizedModule.mk m s') s := by
    rw[fromCombined]
    rw[LocalizedModule.lift_mk]
    have A : LocalizedModule.mkLinearMap S' M m = LocalizedModule.mk m 1 := by rfl
    have B : (LocalizedModule.mkLinearMap S (LocalizedModule S' M) ∘ₗ LocalizedModule.mkLinearMap S' M) m
      = LocalizedModule.mkLinearMap S (LocalizedModule S' M) (LocalizedModule.mkLinearMap S' M m) := by rfl
    have C : LocalizedModule.mkLinearMap S (LocalizedModule S' M) (LocalizedModule.mk m 1)
      = LocalizedModule.mk (LocalizedModule.mk m 1) 1 := by rfl
    rw[B , A , C]
    let u := (is_unit_action_on_double_loc (M := M) S S' s'' ).unit
    let x := LocalizedModule.mk (LocalizedModule.mk m s') s
    have D : x = u⁻¹ • u • x := by simp only [inv_smul_smul]
    have E : LocalizedModule.mk (LocalizedModule.mk m s') s = x := by rfl
    have F : (is_unit_action_on_double_loc S S' s'').unit = u := by rfl
    suffices hyp : (LocalizedModule.mk (LocalizedModule.mk m (1 : S')) (1 : S))
      = (is_unit_action_on_double_loc (M := M) S S' s'' ).unit •  LocalizedModule.mk (LocalizedModule.mk m s') s
    · rw[E , F] at hyp
      rw[E , D , F , ←hyp]
      rfl
    · rw[F , E]
      have G : u • x = s'' • x := by rfl
      have F : s'' • x = (s'' : R) • x:= by rfl
      have H : (s'' : R) • x = (s : R) • (s' : R) • x := by rw[h , mul_smul]
      rw[G , F , H]
      rw[← E]
      have I : (s' : R) • LocalizedModule.mk (LocalizedModule.mk m s') s
        = LocalizedModule.mk (LocalizedModule.mk ((s' : R) • m) s') s := by
        rw[LocalizedModule.smul'_mk ,  LocalizedModule.smul'_mk]
      have J : LocalizedModule.mk ((s' : R) • m) s'= (LocalizedModule.mk  m 1)  := by
        calc
           LocalizedModule.mk ((s' : R) • m) s' =  LocalizedModule.mk ((s' : R) • m) (s' * 1) := by rw[mul_one]
           _ = LocalizedModule.mk (s' • m) (s' * 1) := by rfl
           _ = LocalizedModule.mk  m 1 := by exact LocalizedModule.mk_cancel_common_left s' 1 m
      rw[I , J]
      have K : (s : R) • (LocalizedModule.mk (LocalizedModule.mk m (1 : S')) s )
        = LocalizedModule.mk  ((s : R) • (LocalizedModule.mk m 1)) s := by
        rw[LocalizedModule.smul'_mk]
      have L : LocalizedModule.mk  ((s : R) • (LocalizedModule.mk m (1 : S'))) s
        = LocalizedModule.mk (LocalizedModule.mk m 1) 1 := by
        calc
          LocalizedModule.mk  ((s : R) • (LocalizedModule.mk m (1 : S'))) s
            = LocalizedModule.mk  ((s : R) • (LocalizedModule.mk m (1 : S'))) (s * 1) := by rw[mul_one]
          _ = LocalizedModule.mk  ((s ) • (LocalizedModule.mk m (1 : S'))) (s * 1) := by rfl
          _ = LocalizedModule.mk (LocalizedModule.mk m (1 : S')) (1 : S) := by exact LocalizedModule.mk_cancel_common_left (s : S) 1 (LocalizedModule.mk m 1)
      rw[K , L]

lemma cal_to (m : M) (s : S) (s' : S') (s'' : ↥(S ⊔ S')) (h : s'' = (s : R) * s') :
  toCombined S S'  (LocalizedModule.mk (LocalizedModule.mk m s') s) = LocalizedModule.mk m s'' := by
    rw[toCombined]
    rw[LocalizedModule.lift_mk , LocalizedModule.lift_mk]
    have : LocalizedModule.mkLinearMap (S ⊔ S') M m = LocalizedModule.mk m 1 := by rfl
    rw[this]
    let x := LocalizedModule.mk m s''
    let u_1 := (is_unit_action_on_double_2 (M := M) S S' s').unit
    let u_2 := (is_unit_action_on_double_1 (M := M) S S' s ).unit
    have A : (is_unit_action_on_double_2 (M := M) S S' s').unit = u_1 := by rfl
    have B : (is_unit_action_on_double_1 (M := M) S S' s ).unit = u_2 := by rfl
    have C : LocalizedModule.mk m s'' = x := by rfl
    rw[A , B , C]
    suffices hyp : LocalizedModule.mk m 1 = u_1 • u_2 • x
    · have D : x = u_2⁻¹ • u_1 ⁻¹ • u_1 • u_2 • x := by simp only [inv_smul_smul]
      rw[D , hyp]
      rfl
    · have E_1 : u_2 • x = s • x := by rfl
      have E : u_1 • u_2 • x = s' • s • x := by
        rw[E_1]
        rfl
      rw[E , ←C]
      have F : s' • s • LocalizedModule.mk m s'' = (s' : R) • (s : R) • LocalizedModule.mk m s'' := by rfl
      have G : (s' : R) • (s : R) • LocalizedModule.mk m s'' = LocalizedModule.mk (((s : R) * s') • m) (s'' * 1) := by
        rw[←mul_smul , LocalizedModule.smul'_mk , mul_comm , mul_one]
      have H : LocalizedModule.mk ((s'' : R) • m) (s'' * 1) = LocalizedModule.mk (s'' • m) (s'' * 1) := by rfl
      rw[F , G , ←h , H]
      exact Eq.symm (LocalizedModule.mk_cancel_common_left s'' 1 m)

/-- 主定理：建立线性同构 -/
noncomputable def iso : LocalizedModule S (LocalizedModule S' M)  ≃ₗ[R] LocalizedModule (S ⊔ S') M:=by
  apply  LinearEquiv.ofLinear ( toCombined S S'  ) ( fromCombined S S' ) (_) (_)
  · apply LinearMap.ext--徐弈负责部分
    intro x
    refine Quotient.inductionOn x ?_
    intro ⟨m_inner, s⟩
    have : ⟦(m_inner , s)⟧ = LocalizedModule.mk m_inner s := by rfl
    rw[this]
    have yinli1:(toCombined S S'  ∘ₗ fromCombined S S' ) (LocalizedModule.mk m_inner s) = toCombined S S'  (fromCombined S S'  (LocalizedModule.mk m_inner s)):=by
      rfl
    rw[yinli1]
    have yinli2: (LinearMap.id  (R := R) (LocalizedModule.mk  m_inner s)  )=LocalizedModule.mk m_inner s :=by
      simp [LinearMap.id_apply]
    rw[yinli2]
    have B : ∃ (s1 : S) , ∃ s2 : S' , ↑s1 • (s2 : R) = ↑s:= by
      obtain ⟨x, hx, y, hy, h_eq⟩ := Submonoid.mem_sup.mp s.property
      refine ⟨⟨x, hx⟩, ⟨y, hy⟩, h_eq⟩
    rcases B with ⟨s1 , s2 , hyp⟩
    have C : s1 • (s2 : R) = s1 * s2 := by rfl
    rw[C] at hyp
    · rw[cal_from S S'  m_inner s1 s2]
      · rw[cal_to]
        ·exact _root_.id (Eq.symm hyp)
      ·exact _root_.id (Eq.symm hyp)
  · apply LinearMap.ext--王贺威负责部分
    intro x
    refine Quotient.inductionOn x ?_
    intro ⟨m_inner, s⟩
    have : ⟦(m_inner , s)⟧ = LocalizedModule.mk m_inner s := by rfl
    rw[this]
    refine Quotient.inductionOn m_inner ?_
    intro ⟨m_inner', s'⟩
    have : ⟦(m_inner', s')⟧ = LocalizedModule.mk m_inner' s' := by rfl
    rw[this]
    have : (fromCombined S S' ∘ₗ toCombined S S') (LocalizedModule.mk (LocalizedModule.mk m_inner' s') s)
      = fromCombined S S' (toCombined S S' (LocalizedModule.mk (LocalizedModule.mk m_inner' s') s)) := by rfl
      -- 构造 s'' ∈ S ⊔ S'
    rw[this]
    let s'' : ↥(S ⊔ S') :=
    ⟨ (s : R) * (s' : R),
      by
        apply Submonoid.mul_mem
        · exact Submonoid.mem_sup_left s.property
        · exact Submonoid.mem_sup_right s'.property
    ⟩
    have h'' : (s'' : R) = (s : R) * (s' : R) := rfl
    rw [cal_to S S'  m_inner' s s' s'' h'']
    rw [cal_from S S'  m_inner' s s' s'' h'']
    rfl

  -- 直接展开


end DoubleLocalization
