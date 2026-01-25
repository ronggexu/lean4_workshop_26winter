import Mathlib
open Classical


-- lemma 6.10
variable {R : Type*} [CommRing R] [IsNoetherianRing R]

variable (f : R →+* R)(hf : Function.Surjective f)
def f_iter : ℕ → (R →+* R)
  | 0 => RingHom.id R  -- 0次迭代为恒等映射
  | n+1 => f.comp (f_iter n)  -- n+1次迭代 = f ∘ fⁿ

lemma f_iter_comm (f : R →+* R) (hf : Function.Surjective f) :
    ∀ i : ℕ, f.comp (f_iter f i) = (f_iter f i).comp f := by
  intro i
  induction i with
  | zero => simp [f_iter, RingHom.comp_id, RingHom.id_comp]
  | succ i ih_comm =>
    calc
      f.comp (f_iter f (i+1)) = f.comp (f.comp (f_iter f i)) := by simp [f_iter]
      _ = f.comp ((f_iter f i).comp f) := by rw [ih_comm]
      _ = (f.comp (f_iter f i)).comp f := by rw [RingHom.comp_assoc]
      _ = (f_iter f (i+1)).comp f := by simp [f_iter]

noncomputable def b (f : R →+* R)(hf : Function.Surjective f)(x : R) : ℕ → R
  | 0 => x
  | n+1 => Classical.choose (hf (b f hf x n))  -- 满射保证存在原像

def ideal_ascending_chain_condition (R : Type*) [CommRing R] : Prop :=
  ∀ (u : ℕ → Ideal R), (∀ n, u n ≤ u (n+1)) → ∃ m : ℕ, ∀ n ≥ m, u n = u m

theorem isNoetherianRing_iff_ideal_acc {R : Type*} [CommRing R] :
  IsNoetherianRing R ↔ ideal_ascending_chain_condition R := by
  constructor
  · intro hR u hu
    have hN : IsNoetherian R R :=
      (isNoetherianRing_iff (R := R)).1 hR
    have hstab :
        ∀ (f : ℕ →o Ideal R), ∃ m : ℕ, ∀ n : ℕ, m ≤ n → f m = f n :=
      (monotone_stabilizes_iff_noetherian (R := R) (M := R)).2 hN
    let f : ℕ →o Ideal R :=
      { toFun := u
        monotone' := monotone_nat_of_le_succ hu }
    rcases hstab f with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    intro n hn
    have hmn : u m = u n := hm n hn
    exact Eq.symm hmn
  · intro hacc
    have hstab :
        ∀ (f : ℕ →o Ideal R), ∃ m : ℕ, ∀ n : ℕ, m ≤ n → f m = f n := by
      intro f
      have hs : ∀ n : ℕ, f n ≤ f (n + 1) := by
        intro n
        exact f.monotone (Nat.le_succ n)
      rcases hacc f hs with ⟨m, hm⟩
      refine ⟨m, ?_⟩
      intro n hn
      have h' : f n = f m := hm n hn
      exact Eq.symm h'
    have hN : IsNoetherian R R :=
      (monotone_stabilizes_iff_noetherian (R := R) (M := R)).1 hstab
    exact (isNoetherianRing_iff (R := R)).2 hN



theorem surjective_endomorphism_of_noetherian_is_bijective
    (hf : Function.Surjective f) :
    Function.Bijective f := by
  refine' ⟨_, hf⟩
  suffices h : RingHom.ker f = ⊥ from (RingHom.injective_iff_ker_eq_bot f).mpr h
  suffices h : ∀ x, f x = 0 → x = 0 from (RingHom.ker_eq_bot_iff_eq_zero f).mpr h
  intro x hx

  /- 步骤4：构造 ker(fⁿ) 的理想升链，并验证升链性质 -/
  -- 4.1 辅助定义：ker(fⁿ) 是 R 的理想
  let ker_f_n (n : ℕ) : Ideal R := RingHom.ker (f_iter f n)
  -- 4.2 证明 ker(fⁿ) ⊆ ker(fⁿ⁺¹)（升链）
  have ker_ascending : ∀ n : ℕ, ker_f_n n ≤ ker_f_n (n+1) := by
    intro n y hy
    simp only [ker_f_n, RingHom.mem_ker] at hy ⊢
    calc
      f_iter f (n+1) y = f (f_iter f n y) := by simp [f_iter, RingHom.comp_apply]
      _ = f 0 := by rw [hy]
      _ = 0 := RingHom.map_zero f

  -- 步骤5：利用诺特环的升链条件（ACC）导出链稳定
  have hm : ∃ m : ℕ, ∀ n ≥ m, ker_f_n n = ker_f_n m := by
    -- 第一步：利用诺特环 ↔ 升链条件，推出升链条件成立
    have h_acc : ideal_ascending_chain_condition R := by
      -- 诺特环实例 → 升链条件成立（mp 是 iff 的正向推导）
      exact isNoetherianRing_iff_ideal_acc.mp (by infer_instance)
    -- 第二步：展开升链条件的定义，代入ker_f_n和递增性质
    unfold ideal_ascending_chain_condition at h_acc
    -- 升链条件对任意递增理想序列成立，此处序列是ker_f_n，递增性是ker_ascending
    exact h_acc ker_f_n ker_ascending

  -- 步骤5（续）：从已声明的 hm 中取出稳定点 m 和性质
  obtain ⟨m, hm_stable⟩ := hm

  have h_exist (a : R) : ∃ b, f b = a := hf a

  -- 步骤6：利用 f 的满射性构造逆像序列 b₀, b₁, …, bₘ


  -- 验证 f(b(k+1)) = b k
  have b_spec : ∀ n : ℕ, f (b f hf x (n+1)) = b f hf x n := by
    simp only [b]
    intro n
    apply Classical.choose_spec (hf (b f hf x n))

    -- 步骤7：计算 fᵐ(bₘ) = x，并推导 bₘ ∈ ker(fᵐ⁺¹)
  -- 7.1 先证通用辅助引理：对任意k，f_iter f k (b f hf x k) = x（避免变量重名）
  have aux_f_b : ∀ k : ℕ, f_iter f k (b f hf x k) = x := by
    intro k
    induction k with
    | zero =>  -- k=0：f_iter 0 (b x 0) = id R x = x
      simp [f_iter, b]
    | succ k ih =>  -- 归纳步：假设k成立，证k+1成立（k与hm的m无冲突）
      calc
        f_iter f (k+1) (b f hf x (k+1)) = f (f_iter f k (b f hf x (k+1))) := by
          simp [f_iter, RingHom.comp_apply]  -- 严格展开复合，无交换
        _ = f_iter f k (f (b f hf x (k+1))) := by
          rw [← RingHom.comp_apply f (f_iter f k) (b f hf x (k+1))]
          rw [f_iter_comm]
          rw [RingHom.comp_apply (f_iter f k) f (b f hf x (k+1))]
          apply hf
        _ = f_iter f k (b f hf x k) := by
          rw [b_spec k]  -- 应用b_spec：f(b(k+1))=b(k)
        _ = x := by
          exact ih  -- 归纳假设：f_iter f k (b k) = x

  have f_m_b_m : f_iter f m (b f hf x m) = x := aux_f_b m

  -- 7.2 由 hx: f x = 0，得 fᵐ⁺¹(bₘ) = f(fᵐ(bₘ)) = f x = 0
  have b_m_in_ker_f_m_succ : b f hf x m ∈ ker_f_n (m+1) := by
    simp [ker_f_n, f_iter]
    rw [f_m_b_m, hx]

  -- 7.3 由升链稳定，ker(fᵐ⁺¹) = ker(fᵐ)，故 bₘ ∈ ker(fᵐ)
  have b_m_in_ker_f_m : b f hf x m ∈ ker_f_n m := by
    rw [← hm_stable (m+1) (by linarith)]
    exact b_m_in_ker_f_m_succ

  -- 7.4 因此 fᵐ(bₘ) = 0，结合 f_m_b_m 得 x = 0
  -- 76行修复后代码
  rw [RingHom.mem_ker] at b_m_in_ker_f_m  -- 第一步：先展开核的定义
  rw [f_m_b_m] at b_m_in_ker_f_m         -- 第二步：再替换等式
  exact b_m_in_ker_f_m


-- lemma 6.5
open AlgebraicGeometry

/-- If `R` is a Noetherian ring, then the prime spectrum `Spec R`
is a Noetherian topological space. -/
theorem spec_is_NoetherianSpace (R : CommRingCat) [IsNoetherianRing R] :
TopologicalSpace.NoetherianSpace (Spec R) :=
inferInstance


-- lemma 6.6

theorem noetherian_affine_scheme_finite_genericPoints :
(Ideal.minimalPrimes (⊥ : Ideal R)).Finite := by
-- The set of minimal primes of a Noetherian ring is finite.
-- minimalPrimes R is defined as Ideal.minimalPrimes
-- We use convert to handle the definitional equality.
convert minimalPrimes.finite_of_isNoetherianRing (R := R)
