import Mathlib

/-!
# Locally Nilpotent Ideals

This file develops the theory of locally nilpotent ideals in commutative rings,
based on Stacks Project tag 0AMF. [https://stacks.math.columbia.edu/tag/0AMF]


## Main definitions

  * `Ideal.IsLocallyNilpotent`
  * `Ideal.IsLocallyNilpotent.map`
  * `isUnit_iff_isUnit_quotient`
  * `Ideal.isLocallyNilpotent_iff_isNilpotent`
  * `PrimeSpectrum_quotient_equiv`
  * `Clopens_equiv_of_equiv`
  * `idempotents_equiv_quotient`

## Contributors

  - 姜懿轩、商道轩、左浩民

-/

/-definition 10.32.1-/
def Ideal.IsLocallyNilpotent {R : Type*} [Semiring R] (I : Ideal R) : Prop :=
  ∀ x ∈ I, IsNilpotent x

/-lemma 10.32.3-/
lemma Ideal.IsLocallyNilpotent.map {R R' : Type*} [CommRing R] [CommRing R']
(f : R →+* R') {I : Ideal R} (h : I.IsLocallyNilpotent) :
(I.map f).IsLocallyNilpotent := by
  intro x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  --Case 1.y∈f(I)
  · intro y hy
    rcases hy with ⟨x,hxI,hxy⟩
    have Hx: IsNilpotent x:= h x hxI
    obtain⟨n , hn⟩:= Hx
    use n
    calc
    y^n=(f x)^n :=by rw[←hxy]
    _ = f (x^n) :=by rw[map_pow]
    _ =f 0 := by rw[hn]
    _ = 0 := map_zero f
  --Case 2.zero
  · exact IsNilpotent.zero
  --Case 3.add
  · intro a b ha hb hna hnb
    obtain⟨n , Ha⟩:=hna
    obtain⟨m , Hb⟩:=hnb
    use n+m
    have H(i:ℕ):i≥ n ∨ (n+m-i) ≥ m := by omega
    have H'(i:ℕ): a^i*b^(n+m-i) =0 := by
        specialize H i
        rcases H with H1 | H2
        · rw[pow_eq_zero_of_le H1 Ha]
          ring
        · rw[pow_eq_zero_of_le H2 Hb]
          ring
    simp [add_pow,H']
  --Case 4. mul
  · intro t a ha hna
    obtain⟨n , Ha⟩:=hna
    use n
    calc
    (t * a)^n =t ^ n * a ^ n :=by rw[mul_pow]
    _ =t ^ n * 0 :=by  rw[Ha]
    _ = 0 := by ring

/-lemma 10.32.4-/
lemma isUnit_iff_isUnit_quotient {R : Type*} [CommRing R] (I : Ideal R)
    (hI : I.IsLocallyNilpotent) (x : R) :
    IsUnit x ↔ IsUnit ((Ideal.Quotient.mk I) x) := by
  constructor
  · -- 方向 1: -> (必要性)
    intro hx
    apply IsUnit.map
    exact hx
  · -- 方向 2: <- (充分性)
    intro hx
    -- 步骤 A: 从商环取回逆元代表元
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (hx.unit.inv)
    -- 步骤 B: 建立方程 mk(x * y) = 1
    have h_map : Ideal.Quotient.mk I (x * y) = 1 := by
      rw [map_mul, hy]
      exact hx.unit.val_inv
    -- 步骤 C: 说明 1 - x*y 在理想 I 中
    have h_mem : 1 - x * y ∈ I := by
      -- 1. 构造 mk (1 - xy) = 0
      -- 已知 h_map : mk (xy) = 1
      -- 所以 mk (1 - xy) = mk 1 - mk (xy) = 1 - 1 = 0
      have h_zero : Ideal.Quotient.mk I (1 - x * y) = 0 := by
        rw [map_sub, (Ideal.Quotient.mk I).map_one, h_map, sub_self]
      -- 2. 剥离 mk
      -- 显式把右边的 0 写成 mk 0
      rw [← (Ideal.Quotient.mk I).map_zero] at h_zero
      -- 使用 Quotient.exact 去掉 mk
      replace h_zero := Quotient.exact h_zero
      -- 3. 转换
      -- h_zero 现在的类型是 " (1 - xy) ≈ 0 "
      -- 我们声明一个新的变量，显式告诉 Lean 我们要的是 " ... ∈ I "
      -- Lean 会自动识别出 I 和 I.toSubmodule 是兼容的
      have h_in_I : (1 - x * y) - 0 ∈ I := by
        exact (Submodule.quotientRel_def I).mp h_zero
      -- 4. 化简
      rw [sub_zero] at h_in_I
      exact h_in_I
    -- 步骤 D: 利用幂零性质
    -- 令 n = 1 - xy。因为 I 是局部幂零的，所以 n 是幂零元
    have h_nil : IsNilpotent (1 - x * y) := hI (1 - x * y) h_mem
    -- 引理：如果 n 幂零，则 1 - n 可逆
    -- 1 - (1 - x * y) = x * y
    -- 这里使用 IsNilpotent.isUnit_one_sub (1 - n 可逆)
    have h_unit_xy : IsUnit (1 - (1 - x * y)) := IsNilpotent.isUnit_one_sub h_nil
    -- 化简得到 xy 可逆
    rw [sub_sub_cancel] at h_unit_xy
    -- xy 可逆 => x 可逆
    exact isUnit_of_mul_isUnit_left h_unit_xy
/-
  设 I 是交换环 R 的一个局部幂零理想。则元素 x \in R 是单位元（IsUnit），当且仅当它在商环 R/I 中的像 \bar{x} 是单位元。

x \in R^\times \iff \bar{x} \in (R/I)^\times

证明：

(\Rightarrow) 必要性（显然）：
若 x 在 R 中可逆，则存在 y \in R 使得 xy = 1。
考虑典范投影 \pi: R \to R/I。由于环同态保持乘法单位元和乘积，我们有：
\pi(x)\pi(y) = \pi(xy) = \pi(1) = 1_{R/I}
因此，\bar{x} 在 R/I 中可逆。

(\Leftarrow) 充分性（核心）：
假设 \bar{x} 在 R/I 中可逆。这意味着存在 y \in R 使得 \overline{xy} = \bar{1}。
这等价于：
xy \equiv 1 \pmod I \implies 1 - xy \in I
令 a = 1 - xy。根据假设，a 属于局部幂零理想 I。
根据局部幂零理想的定义，存在一个正整数 n，使得 a^n = 0。
我们知道几何级数公式：
1 = 1 - a^n = (1-a)(1 + a + a^2 + \dots + a^{n-1})
将 a = 1 - xy 代入 1-a，得到：
1 = xy(1 + a + a^2 + \dots + a^{n-1})
令 z = y(1 + a + a^2 + \dots + a^{n-1})，则有 xz = 1。
这表明 x 在 R 中有右逆（进而因为 R 是交换环，也是左逆），即 x 是单位元。
-/



/-lemma 10.32.5-/
/-lemma exists_pow_subset_of_radical_subset {R : Type*} [CommRing R] [IsNoetherian R R]
    (I J : Ideal R) (hJ : J ≤ I.radical) : ∃ n : ℕ, J ^ n ≤ I := by
  sorry-/

/-This is already declared by Ideal.exists_pow_le_of_le_radical_of_fg_radical-/

/-corollary-/
/-这个推论意思即为在 Noetherian 环中，局部幂零和整体幂零等价.
  一方面如果整体 I^n=0，那么肯定 x^n=0 对于所有 x∈I 成立，所以局部幂零成立.
  另一方面利用上述定理，因为 I ≤ √0，所以存在 n 使得 I^n ≤ 0，即 I^n=0，所以整体幂零成立.
-/
lemma Ideal.isLocallyNilpotent_iff_isNilpotent {R : Type*} [CommRing R] [IsNoetherian R R]
    (I : Ideal R) : IsLocallyNilpotent I ↔ IsNilpotent I := by
  constructor
  · intro hI
    have h : I ≤ radical ⊥ := by
      intro x hx
      exact hI x hx
    have h' : ((⊥ : Ideal R).radical).FG := by
      apply IsNoetherian.noetherian
    have hr : ∃ k, I ^ k ≤ ⊥ :=
      exists_pow_le_of_le_radical_of_fg_radical h h'
    rcases hr with ⟨k, hk⟩
    exact ⟨k, le_bot_iff.mp hk⟩
  · intro hI x hx
    rcases hI with ⟨n, hn⟩
    have : x ^ n ∈ I ^ n := by
      apply Ideal.pow_mem_pow hx n
    rw [hn, Submodule.zero_eq_bot, Submodule.mem_bot] at this
    exact ⟨n, this⟩



/-lemma 10.32.6-/
/- 为了证明这个命题，首先我尝试了
  + PrimeSpectrum (R ⧸ I) ≃ₜ PrimeSpectrum R
  + TopologicalSpace.Clopens (PrimeSpectrum (R ⧸ I)) ≃
      TopologicalSpace.Clopens (PrimeSpectrum R)
  + { e : R // e * e = e } ≃  TopologicalSpace.Clopens (PrimeSpectrum R)
  + { e : R ⧸ I // e * e = e } ≃ TopologicalSpace.Clopens (PrimeSpectrum (R ⧸ I))
  这四步来实现。然而想要利用已有的定理 Ideal.primeSpectrumQuotientOrderIsoZeroLocus I，
  必须说明 OrderTopology (PrimeSpectrum (R ⧸ I))等，在我的能力范围和理解内似乎是无法完成的.

  在这一部分的可用的定理似乎没有那么多，为了证明前两个命题，我们还是直接构造同胚.
  这两个引理的证明比较长，且比较独立，我们将其概括为两个小 def.
-/

/-该引理用于证明 locallyNilpotent 的理想会包含于每一个素理想-/
lemma locallyNilpotent_le_prime_ideal
  {R : Type*} [CommRing R] {I : Ideal R} (hI : I.IsLocallyNilpotent)
  (P : Ideal R) (hP : P.IsPrime) :
  I ≤ P := by
      intro x hx
      rcases hI x hx with ⟨n, hn⟩
      have hxn : (x ^ n) ∈ P := by
        rw [hn]
        exact Submodule.zero_mem P
      have : x ∈ P := by
        apply Ideal.IsPrime.mem_of_pow_mem at hxn
        · exact hxn
        · exact hP
      exact this

/-引理：对于LocallyNilpotent理想，商环的素谱与原环的素谱同胚. 下面我们直接构造典范映射来证明这个同胚-/
def PrimeSpectrum_quotient_equiv
  {R : Type*} [CommRing R] (I : Ideal R) (hI : I.IsLocallyNilpotent) :
  PrimeSpectrum (R ⧸ I) ≃ₜ PrimeSpectrum R := by
  -- 定义前向映射：从 Spec(R/I) 到 Spec(R)
  -- 使用 comap，它总是将素理想映射回素理想
  let to_fun (P : PrimeSpectrum (R ⧸ I)) : PrimeSpectrum R :=
    ⟨Ideal.comap (Ideal.Quotient.mk I) P.asIdeal,
     Ideal.comap_isPrime (Ideal.Quotient.mk I) P.asIdeal⟩
  -- 定义反向映射：从 Spec(R) 到 Spec(R/I)
  -- 使用 map，这需要 I 包含在 P 中
  let inv_fun (P : PrimeSpectrum R) : PrimeSpectrum (R ⧸ I) :=
    ⟨Ideal.map (Ideal.Quotient.mk I) P.asIdeal, by
      -- 证明 map 的结果是素理想
      -- 需要证明 ker(mk I) 包含在 P.asIdeal 中
      have h_ker_le : RingHom.ker (Ideal.Quotient.mk I) ≤ P.asIdeal := by
        rw [Ideal.mk_ker] -- ker(mk I) 就是 I
        -- 使用我们之前证明的引理
        exact locallyNilpotent_le_prime_ideal hI P.asIdeal P.isPrime
      exact Ideal.map_isPrime_of_surjective (Ideal.Quotient.mk I).surjective h_ker_le⟩
  -- 构造一个 Equiv
  let equiv : PrimeSpectrum (R ⧸ I) ≃ PrimeSpectrum R := {
    toFun := to_fun,
    invFun := inv_fun,
    -- 证明 left_inv: inv_fun(to_fun(P)) = P
    left_inv := by
      intro P
      -- 展开定义
      ext1
      simp only [to_fun, inv_fun]
      -- 使用 Ideal.map_comap_of_surjective
      exact Ideal.map_comap_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective P.asIdeal,
    -- 证明 right_inv: to_fun(inv_fun(P)) = P
    right_inv := by
      intro P
      ext1
      simp only [to_fun, inv_fun]
      -- 使用 Ideal.comap_map_of_surjective
      -- 需要证明 I 包含在 P.asIdeal 中
      have h_le : I ≤ P.asIdeal := locallyNilpotent_le_prime_ideal hI P.asIdeal P.isPrime
      rw [Ideal.comap_map_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective, sup_eq_left]
      have : I = Ideal.comap (Ideal.Quotient.mk I) ⊥ := by
        ext x
        simp [Ideal.comap, Ideal.Quotient.eq_zero_iff_mem]
      rw [← this]
      exact h_le
  }
  exact {
    equiv with
    -- 证明 to_fun 是连续的
    -- to_fun 是由 comap (Ideal.Quotient.mk I) 定义的
    -- Mathlib 中有 comap 诱导的映射是连续的这一结论
    continuous_toFun := by
      -- 使用 simp 展开 to_fun 的定义
      simp only [Equiv.toFun_as_coe]
      -- PrimeSpectrum.comap_continuous 证明了由环同态的 comap 诱导的谱映射是连续的
      exact (PrimeSpectrum.comap (Ideal.Quotient.mk I)).continuous
    -- 证明 inv_fun 是连续的
    -- inv_fun 是由 map (Ideal.Quotient.mk I) 定义的
    -- Mathlib 中有 map 诱导的映射是连续的这一结论
    continuous_invFun := by
      -- 为了证明连续性，我们证明任何基本开集 basicOpen r' 的原像是开集
      apply (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R ⧸ I)).continuous_iff.mpr
      -- 现在的目标是证明对于任意 r', inv_fun⁻¹(basicOpen r') 是开集
      rintro _ ⟨r', rfl⟩
      -- r' 是 R/I 中的元素，我们可以找到它在 R 中的一个原像 r
      obtain ⟨r, hr⟩ := (Ideal.Quotient.mk I).surjective r'
      -- 我们要证明 inv_fun⁻¹(basicOpen r') 是开集
      -- 经过化简，inv_fun⁻¹(basicOpen r') = basicOpen r
      have h_preimage : inv_fun ⁻¹' (PrimeSpectrum.basicOpen r') = PrimeSpectrum.basicOpen r := by
        ext P
        let f := Ideal.Quotient.mk I
        have h_le : I ≤ P.asIdeal := locallyNilpotent_le_prime_ideal hI P.asIdeal P.isPrime
        simp only [inv_fun, Set.mem_preimage, PrimeSpectrum.mem_basicOpen,
          SetLike.mem_coe, ← hr]
        -- 目标是: (f r) ∉ Ideal.map f P.asIdeal ↔ r ∉ P.asIdeal
        -- 这等价于证明: (f r) ∈ Ideal.map f P.asIdeal ↔ r ∈ P.asIdeal
        apply Iff.not
        -- 使用 Ideal.map_mem_iff_preimage_of_surjective 来展开 map 的成员关系
        rw [Ideal.mem_map_iff_of_surjective f f.surjective]
        --rw[Ideal.mk_ker, sup_eq_left.mpr h_le]
        constructor
        · intro h
          rcases h with ⟨y, hy1, hy2⟩
          -- 根据 hy2 : f y = (Ideal.Quotient.mk I) r 所以f(y-r)=0，所以 y - r ∈ I subset P.asIdeal
          have h_sub_mem_ker : y - r ∈ RingHom.ker f := by
            rw [RingHom.mem_ker, map_sub, hy2, sub_self]
          -- ker f 就是 I
          rw [Ideal.mk_ker] at h_sub_mem_ker
          -- 因为 I 包含于 P.asIdeal (h_le), 所以 y - r ∈ P.asIdeal
          have h_sub_mem_P : y - r ∈ P.asIdeal := h_le h_sub_mem_ker
          -- P.asIdeal 是一个理想，它对减法封闭。
          -- y ∈ P.asIdeal (hy1) 且 y - r ∈ P.asIdeal, 所以 r = y - (y - r) ∈ P.asIdeal
          have hr : r = y - (y - r) := by ring
          rw [hr]
          exact Ideal.sub_mem P.asIdeal hy1 h_sub_mem_P
        · intro h
          use r
      -- basicOpen r 本身就是 Spec R 中的一个开集
      rw [h_preimage]
      exact PrimeSpectrum.isOpen_basicOpen
  }

/-证明同胚的拓扑空间的Clopen集间存在双射.直接构造-/
def Clopens_equiv_of_equiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X ≃ₜ Y) :
  TopologicalSpace.Clopens X ≃ TopologicalSpace.Clopens Y := by
  -- 构造一个 Equiv 需要提供 toFun, invFun, left_inv, right_inv
  refine {
    -- 定义从 Clopens X 到 Clopens Y 的前向映射
    -- 对于 X 中的一个闭开集 U，它的像是 f '' U
    toFun := fun U ↦ ⟨f.toEquiv '' U, by
      -- 需要证明 f '' U 也是一个闭开集
      constructor
      · exact f.isClosedMap U U.isClosed
      · exact f.isOpenMap U U.isOpen
      ⟩,
    -- 定义从 Clopens Y 到 Clopens X 的反向映射
    -- 对于 Y 中的一个闭开集 V，它的原像是 f⁻¹ '' V
    invFun := fun V ↦ ⟨f.toEquiv.symm '' V, by
      -- 同样，需要证明 f⁻¹ '' V 是 X 中的闭开集
      constructor
      · exact f.symm.isClosedMap V V.isClosed
      · exact f.symm.isOpenMap V V.isOpen
      ⟩,
    -- 证明 left_inv: invFun(toFun(U)) = U
    left_inv := fun U ↦ by
      -- 展开定义
      simp only [Homeomorph.coe_symm_toEquiv, Homeomorph.coe_toEquiv,
        TopologicalSpace.Clopens.coe_mk]
      -- f⁻¹''(f '' U) = U，因为 f 是双射 (injective)
      ext
      simp only [TopologicalSpace.Clopens.coe_mk, Set.mem_image, SetLike.mem_coe,
        exists_exists_and_eq_and, Homeomorph.symm_apply_apply, exists_eq_right],
    -- 证明 right_inv: toFun(invFun(V)) = V
    right_inv := fun V ↦ by
      -- 展开定义
      simp only [Homeomorph.coe_symm_toEquiv, Homeomorph.coe_toEquiv,
        TopologicalSpace.Clopens.coe_mk]
      -- f''(f⁻¹ '' V) = V，因为 f 是双射 (surjective)
      ext
      simp only [TopologicalSpace.Clopens.coe_mk, Set.mem_image, SetLike.mem_coe,
        exists_exists_and_eq_and, Homeomorph.apply_symm_apply, exists_eq_right]
  }
/-主定理：对于局部幂零理想 I，R 中的幂等元与商环 R ⧸ I 中的幂等元之间存在自然的双射.
首先利用mathlib里已有的定理构造幂等元和Clopen集之间的双射，然后利用上面构造的同胚映射
  PrimeSpectrum_quotient_equiv 和 Clopens_equiv_of_equiv 构造商环和原环素谱的Clopen集之间的双射，最后组合这些双射得到所需的结果.
-/
noncomputable def idempotents_equiv_quotient {R : Type*} [CommRing R] (I : Ideal R)
  (hI : I.IsLocallyNilpotent) :
  { e : R // e * e = e } ≃ { e : R ⧸ I // e * e = e } := by
  have f0 : PrimeSpectrum (R ⧸ I) ≃ₜ PrimeSpectrum R := PrimeSpectrum_quotient_equiv I hI
  have f00 :
    TopologicalSpace.Clopens (PrimeSpectrum (R ⧸ I)) ≃
      TopologicalSpace.Clopens (PrimeSpectrum R) := Clopens_equiv_of_equiv f0
  have f1 : { e : R // e * e = e } ≃  TopologicalSpace.Clopens (PrimeSpectrum R) :=
  (PrimeSpectrum.isIdempotentElemEquivClopens (R := R)).toEquiv
  have f2 : { e : R ⧸ I // e * e = e } ≃ TopologicalSpace.Clopens (PrimeSpectrum (R ⧸ I)) :=
  (PrimeSpectrum.isIdempotentElemEquivClopens (R := R ⧸ I)).toEquiv
  exact f1.trans (f00.symm.trans f2.symm)
