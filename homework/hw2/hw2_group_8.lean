import Mathlib
/-#check 1+1
section
variable (a b c : ℕ)
#check (a : ℝ)
#check  mul_comm a b
#check mul_assoc c a b
#check mul_comm a b
end
example (a b : ℝ) : a - b = a + -b := by rfl
section
variable (a b c d f e : ℝ)

#check lt_trans
#check mul_assoc
#check mul_comm
#check sub_self
#check mul_add
#check add_mul
#check add_assoc
#check two_mul

example : c * b * a = b * (a * c) := by
rw[mul_comm c b]
rw[mul_assoc b c a]
rw[mul_comm c a]



example : a * (b * c) = b * (a * c) := by
nth_rw 1 [mul_comm a (b * c)]
rw[mul_assoc]
rw[mul_comm c a]
example (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
rw[mul_assoc a b c]
rw[mul_assoc a e f]
rw[h]

example (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
rw[hyp]
rw[hyp']
rw[mul_comm b a]
apply sub_self


example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

#check add_zero
#check pow_two
#check mul_sub
#check add_sub
#check sub_sub

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

end


-- 使用 rw , 考虑结合 \verb|exact, nth_rw, have, apply 完成如下练习

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw[hyp]
  rw[hyp']
  ring

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  rw[←h]
  ring

#check add_left_cancel
example (a : ℝ) : 0 * a = 0 := by
  ring

#check neg_add_cancel_left

theorem neg_eq_of_add_eq_zero {a b : ℝ} (h : a + b = 0) : -a = b := by
  rw[←neg_add_cancel_left a b]
  rw[h]
  ring

theorem neg_neg' (a : ℝ) : - -a = a := by
  ring

#check inv_mul_cancel
#check one_mul
theorem my_mul_inv_cancel {G : Type*} [Group G] (a : G) : a * a⁻¹ = 1 := by
  rw[←one_mul (a * a⁻¹)]
  rw[←inv_mul_cancel a⁻¹]
  rw[←mul_assoc]
  nth_rw 2 [mul_assoc]
  rw[inv_mul_cancel]
  rw[mul_assoc]
  rw[one_mul]

variable {α : Type}

theorem my_add_zero {a : ℝ} (h : a = 0) : a + 0 = 0 := by
rw[h]
ring

theorem my_mul_add {a b c : ℝ} : (a + b) * c = a * c + b * c := by ring

theorem my_mul_inv {a b : ℝ} : a / b = a * b⁻¹ := by rfl

example {a b c : ℝ} : a ∣ b - c → (a ∣ b ↔ a ∣ c) := by sorry

example (s t : Set α) (x : α) : x ∈ s → x ∈ s ∪ t := by sorry

example (s t : Set α) (x : α) : x ∈ s ∪ t → x ∈ s ∨ x ∈ t := by sorry

example {a : α} {p : α → Prop} : a ∈ {x | p x} ↔ p a := by sorry

example {x a : α} {s : Set α} : x ∈ insert a s → x = a ∨ x ∈ s := by sorry

example {x : α} {a b : Set α} : x ∈ a ∩ b → x ∈ a := by sorry

example {a b : ℝ} : a ≤ b ↔ a < b ∨ a = b := by sorry

example {a b : ℤ} : a ≤ b - 1 ↔ a < b := by sorry

example {a b c : ℝ} (bc : a + b ≤ a + c) : b ≤ c := by sorry



-- 请根据以下命名猜测并陈述出定理

/-
1. mul_add 乘法分配律
2. add_sub_right_comm
3. le_of_lt_of_le
4. add_le_add
5. mem_union_of_mem_right
-/


-- tactics练习
variable (a b c d : ℝ)

#check pow_eq_zero
#check pow_two_nonneg
  -- 必须加载数学库，否则找不到 sq_nonneg/pow_eq_zero 等定理

-- 先定义你写的引理：x² ≤ 0 ⇒ x² = 0
lemma pow_two_eq_zero {x : ℝ} (h : x ^ 2 ≤ 0) : x ^ 2 = 0 := by
  apply le_antisymm  -- 用反对称性：a ≤ b ∧ b ≤ a ⇒ a = b
  · apply h          -- 第一个方向：x² ≤ 0（来自假设 h）
  · apply sq_nonneg x  -- 第二个方向：x² ≥ 0（实数平方非负，sq_nonneg 等价于 pow_two_nonneg）

-- 目标证明：x² + y² = 0 ⇒ x = 0
example {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 := by
  have hy : y ^ 2 ≥ 0 := sq_nonneg y
  have hx_le_0 : x ^ 2 ≤ 0 := by
    rw [← h]
    simp [hy]
  have hx_eq_0 : x ^ 2 = 0 := pow_two_eq_zero hx_le_0
  apply eq_zero_of_pow_eq_zero hx_eq_0




theorem aux {a b c : ℝ} : min a b + c ≤ min (a + c) (b + c) := by
  by_cases h : a ≤ b
  · rw [min_eq_left h]
    apply le_min_iff.mpr
    constructor  -- 拆分为两个子目标：a+c ≤ a+c ∧ a+c ≤ b+c
    · exact le_refl (a + c)  -- 子目标1：a+c ≤ a+c（自反性）
    · exact add_le_add h (le_refl c)  -- 子目标2：a+c ≤ b+c（加法单调性）
  · push_neg at h
    rw [min_eq_right (le_of_lt h)]  -- 替换 min a b 为 b（因为 b ≤ a）
    -- 目标变为：b + c ≤ min (a + c) (b + c)
    apply le_min_iff.mpr
    constructor
    · exact add_le_add (le_of_lt h) (le_refl c)  -- 子目标1：b+c ≤ a+c
    · exact le_refl (b + c)

-- 你可以尝试使用aux来完成这一证明
#check le_antisymm
#check add_le_add_right
#check sub_eq_add_neg
example : min a b + c = min (a + c) (b + c) := by
  by_cases h : a ≤ b
  · have h1 : a + c ≤ b + c := add_le_add_left h c
    rw [min_eq_left h]
    rw [min_eq_left h1]
  · push_neg at h
    have h2 : b + c ≤ a + c := add_le_add_left (le_of_lt h) c
    rw [min_eq_right (le_of_lt h)]
    rw [min_eq_right h2]

#check sq_nonneg
theorem fact1 : a * b * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : a ^ 2 + b ^ 2 - a * b * 2 = (a - b) ^ 2 := by ring
  nlinarith

#check pow_two_nonneg
theorem fact2 : -(a * b) * 2 ≤ a ^ 2 + b ^ 2 := by
  have h : a ^ 2 + b ^ 2 + (a * b) * 2 = (a + b) ^ 2 := by ring
  nlinarith

-- 你可以使用上面两个定理来完成这一证明
#check le_div_iff₀
example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  by_cases h : a * b ≤ 0
  · have h1 : |a * b| = - (a * b) := abs_of_nonpos h
    rw[h1]
    have h2 : (a ^ 2 + b ^ 2) / 2 + (a * b) = (a + b) ^ 2 / 2:= by ring
    nlinarith
  · push_neg at h
    have h1 : |a * b| = (a * b) := abs_of_pos h
    rw[h1]
    have h2 : (a ^ 2 + b ^ 2) / 2 - (a * b) = (a - b) ^ 2 / 2:= by ring
    nlinarith
theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := by exact abs_mul x y
    _ ≤ |x| * ε := by
      have y_le : |y| ≤ ε := le_of_lt ylt
      have x_nonneg : 0 ≤ |x| := abs_nonneg x
      exact mul_le_mul_of_nonneg_left y_le x_nonneg
    _ < 1 * ε := by
       have x_lt_1 : |x| < 1 := lt_of_lt_of_le xlt ele1
       exact mul_lt_mul_of_pos_right x_lt_1 epos
    _ = ε := one_mul ε



def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section
variable (f g : ℝ → ℝ) (a b : ℝ)


example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
intro x
have h1 : a ≤ f x := hfa x
have h2 : b ≤ g x := hgb x
exact add_le_add h1 h2

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
intro x
calc
f x * g x ≤ a * g x := mul_le_mul_of_nonneg_right (hfa x) (nng x)
_ ≤ a * b := mul_le_mul_of_nonneg_left (hgb x) nna



-- 使用calc
example (a b : ℝ) : - 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  calc
  - 2 * a * b
  = - (a + b) ^ 2 + a ^ 2 + b ^ 2 := by ring
  _ ≤ a ^ 2 + b ^ 2 := by nlinarith

example (a b c : ℝ) : a * b + a * c + b * c ≤ a * a + b * b + c * c := by
calc
a * b + a * c + b * c
= - (a - b) ^ 2 / 2- (b - c) ^ 2 / 2- (a - c) ^ 2 / 2 + a * a + b * b + c * c := by ring
_ ≤ a * a + b * b + c * c := by nlinarith

end

section GroupTheory

open Subgroup
theorem covby_top_of_index_eq_prime {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (h_idx : H.index = p) : CovBy H ⊤ := by
    constructor
    · exact Ne.lt_of_le (by
      intro x
      have h1 : H.index = 1 := by rw [x, index_top]
      rw [h_idx] at h1
      have := Nat.Prime.one_lt (Fact.out : p.Prime)
      linarith) le_top
    · intro K hK hKtop
      have hHK : H < K := hK
      have hKtop' : K ≤ ⊤ := le_top
      have h_card_mul : Nat.card H * H.index= Nat.card G := card_mul_index H
      have h_index_mul : H.index = K.index * (H.subgroupOf K).index := by
        rw [← relIndex_mul_index]
      rw [h_idx] at h_index_mul
      have h_dvd : K.index ∣ p := by

        use (H.subgroupOf K).index
      have hp : Nat.Prime p := Fact.out
      have number_of_K : K.index = 1 ∨ K.index = p := by
        exact (Nat.dvd_prime hp).mp h_dvd
      rcases number_of_K with ⟨a1,a2⟩ := by
        aesop


theorem index_eq_prime_of_covby_top (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] [Fact (IsPGroup p G)]
    {H : Subgroup G} (h_max : CovBy H ⊤) : H.index = p := by sorry

end GroupTheory-/

section Nakayamalemmas

open Submodule
variable {R : Type*} [CommRing R] (S : Submonoid R) (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]

variable (A B : Submodule R M)

lemma surjective_from_B_to_M_over_A_of_sup_eq_top {h : A ⊔ B = ⊤} :
    Function.Surjective (fun (b : B) => (A.mkQ) b) := by
  intro q
  have sur : Function.Surjective (A.mkQ) :=by
    exact Submodule.Quotient.mk_surjective A
  rcases sur q with ⟨x,quo⟩
  have : x ∈ A ⊔ B := by
   rw[h]
   exact Submodule.mem_top
  rcases Submodule.mem_sup.1 this with ⟨a, ha, b, hb, hh⟩
  refine ⟨⟨b, hb⟩, ?_⟩
  calc
    (fun (b : B) => (A.mkQ) b) ⟨b,hb⟩ = (A.mkQ) b := by rfl
    _ = (A.mkQ) (a+b) - (A.mkQ) a := by simp [map_add]
    _ = (A.mkQ) x - (A.mkQ) a := by rw[←hh]
    _ = (A.mkQ) x - 0 := by simp[ha]
    _ = q := by simp[quo]

lemma quotient_smul_eq_from_eq_sum
{N N' : Submodule R M}
{h_decomposition : N ⊔ (I • N') = ⊤} :
let Q := M ⧸ N
(⊤ : Submodule R Q) = I • ⊤ := by
  let S := I • N'
  have h_surj : Function.Surjective (fun (x : S) => N.mkQ x) := by
    apply surjective_from_B_to_M_over_A_of_sup_eq_top N S
    exact h_decomposition

  apply le_antisymm _ le_top
  intro x _
  -- 取 x 的原像 b
  rcases h_surj x with ⟨b, rfl⟩

  -- b.1 ∈ I • N'
  have hb : b.1 ∈ I • N' := b.2
  -- 显式指定归纳的谓词 p
  apply Submodule.smul_induction_on (p := fun m => N.mkQ m ∈ I • ⊤) hb
  · -- 1. 基础情况：r • n
    intro r hr n hn
    rw [map_smul]
    apply Submodule.smul_mem_smul hr
    exact Submodule.mem_top
  · -- 2. 加法情况：x + y
    -- 修正处：只引入 x, y 和两个归纳假设，共 4 个参数
    intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

/- ! ### 3. If M = N + I • N' and N' is finitely generated,
there exists f ∈ 1 + I such that f • M ⊆  N. -/
theorem nakayama_three
(N N' : Submodule R M)
{h_decomposition : N ⊔ (I • N') = ⊤}
{h_fg : Submodule.FG N'} :
 ∃ (f : R), f-1 ∈ I ∧ (∀ (m : M), f • m ∈ N) :=by
    -- 令 Q = M/N
  set Q := M ⧸ N with hQ_def
  --
  -- 从 M = N + I N' 得到自然的满同态 I N' → M/N
  let S := I • N'
  have h_surj : Function.Surjective (fun (x : S) => N.mkQ x) := by
    apply surjective_from_B_to_M_over_A_of_sup_eq_top
    exact h_decomposition
  --
  --- 证明 M/N = I (M/N)
  have h_id : (⊤ : Submodule R Q) = I • ⊤ := by
    apply le_antisymm _ le_top
    intro x _
    -- 取 x 的原像 b
    rcases h_surj x with ⟨b, rfl⟩
    --
    -- b.1 ∈ I • N'
    have hb : b.1 ∈ I • N' := b.2
    --
    -- 显式指定归纳的谓词 p
    apply Submodule.smul_induction_on (p := fun m => N.mkQ m ∈ I • ⊤) hb
    · -- 1. 基础情况：r • n
      intro r hr n hn
      rw [map_smul]
      apply Submodule.smul_mem_smul hr
      exact Submodule.mem_top
    · -- 2. 加法情况：x + y
      -- 修正处：只引入 x, y 和两个归纳假设，共 4 个参数
      intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  --
  -- 由满同态和 N' 有限生成知道 M/N 有限生成
  have hQ_fg : Submodule.FG (⊤ : Submodule R Q) := by
    -- 1. 先证明 N' ⊔ N = ⊤
    -- 因为 N ⊔ (I • N') = ⊤ 且 I • N' ⊆ N'
    have h_sup : N' ⊔ N = ⊤ := by
      rw [sup_comm] -- 变为 N ⊔ N' = ⊤
      rw [eq_top_iff, ← h_decomposition]
      apply sup_le_sup_left
      exact Submodule.smul_le_right
    --
    -- 2. 利用性质：p.map mkQ = ⊤ ↔ p ⊔ N = ⊤
    -- 这说明 N' 在商模中的像就是整个商模
    have h_map_eq_top : N'.map N.mkQ = ⊤ := by
      rw [Submodule.map_mkQ_eq_top]
      rw [sup_comm]
      exact h_sup
    --
    -- 3. N' 是 FG，所以其同态像也是 FG
    rw [← h_map_eq_top]
    -- 【修正点】使用点符号调用 map，避免参数类型解析错误
    exact h_fg.map N.mkQ
  --
  -- 4. 应用中山引理
  -- 修正：必须显式传入 (⊤ : Submodule R Q) 作为第二个参数
  obtain ⟨f, hf_mem, hf_kill⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤ hQ_fg (le_of_eq h_id)
  --
  refine ⟨f, hf_mem, ?_⟩
  intro m
  -- 1. 将 m ∈ N 转化为 Quotient.mk m = 0
  rw [← Submodule.Quotient.mk_eq_zero N]
  --
  -- 2. 切换视角为 N.mkQ 以便应用 map_smul
  change N.mkQ (f • m) = 0
  rw [map_smul]
  --
    -- 3. 利用 hf_kill : f • ⊤ = ⊥ 直接推导
  have h_in : f • N.mkQ m ∈ (⊥ : Submodule R Q) := by
    rw [Submodule.mem_bot]
    exact hf_kill (N.mkQ m) Submodule.mem_top
--
  exact h_in

/-
If x₁, …, xₙ ∈ M generate M/IM and M is finitely generated,
then there exists f ∈ 1 + I such that x₁, …, xₙ generate M_f over R_f.
-/

theorem nakayama_seven
  {n : ℕ} (x : Fin n → M)
  (h_finite : Module.Finite R M)
  (h_gen_quot : span R (Set.range (fun i => mkQ (I • ⊤ : Submodule R M) (x i))) = ⊤) :
  ∃ f : R,
    (f - 1) ∈ I ∧
    let S := Submonoid.powers f
    let R_f := Localization S
    let M_f := LocalizedModule S M
    let φ := LocalizedModule.mkLinearMap S M
    span R_f (Set.range (fun i => φ (x i))) = ⊤ :=
by
  let N := span R (Set.range x)
  --  证明 M = N + IM
  have h_M_eq : N ⊔ (I • ⊤ : Submodule R M) = ⊤ := by
    rw [eq_top_iff]
    intro m _
    have h_image_in_quotient :
      mkQ (I • ⊤ : Submodule R M) m
      ∈ span R (Set.range (fun i => mkQ (I • ⊤ : Submodule R M) (x i))) := by
      rw [h_gen_quot]
      trivial
    --  显式地将 lambda (fun i => ...) 转换为函数组合 (f ∘ x)
    --   这样 Set.range_comp 才能匹配上
    change mkQ (I • ⊤ : Submodule R M) m
    ∈ span R (Set.range (mkQ (I • ⊤ : Submodule R M) ∘ x)) at h_image_in_quotient
    --  现在可以使用 range_comp 和 map_span 了
    --    Set.range_comp: range (f ∘ g) -> f '' (range g)
    --    ← map_span:     span (f '' s) -> (span s).map f
    rw [Set.range_comp, ← map_span] at h_image_in_quotient
    rcases mem_map.mp h_image_in_quotient with ⟨n, hn, h_eq⟩

    have h_diff_mem_IM : m - n ∈ (I • ⊤ : Submodule R M) := by
      -- 使用引理将 mkQ 的相等转化为元素的差属于子模
      -- 1. 把 mkQ 展开为 Quotient.mk
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at h_eq
      -- 2. 使用商模相等的性质: [n] = [m] ↔ n - m ∈ I•⊤
      rw [Submodule.Quotient.eq'] at h_eq
      -- 3. 因为是子模，n - m ∈ I•⊤ ↔ m - n ∈ I•⊤
      rw [neg_add_eq_sub] at h_eq
      exact h_eq
    rw [← sub_add_cancel m n]
    apply Submodule.add_mem
    · exact mem_sup_right h_diff_mem_IM
    · exact mem_sup_left hn
  --  应用 Nakayama 引理的变体
  -- 我们取 N' = ⊤ (整个模 M)，因为由 h_finite 知 M 是有限生成的
  have h_fg_top : Submodule.FG (⊤ : Submodule R M) := Module.Finite.fg_top
  -- 应用定理得到 f
  obtain ⟨f, hf_mem, hf_smul_mem_N⟩
  := nakayama_three I N ⊤ (h_decomposition := h_M_eq) (h_fg := h_fg_top)
  -- 4. 开始证明 f 满足要求
  use f
  constructor
  · exact hf_mem -- 满足 f ∈ 1 + I

  -- 接下来证明生成性
  -- 定义局部化相关的变量，和定理声明保持一致
  let S := Submonoid.powers f
  let R_f := Localization S
  let M_f := LocalizedModule S M
  let φ := LocalizedModule.mkLinearMap S M

  -- 目标：span R_f (φ(x_i)) = ⊤
  rw [eq_top_iff]
  intro z _ -- 任取 z ∈ M_f

  -- 设 W 为 R_f 上由 φ(x_i) 生成的子模
  let W := span R_f (Set.range (fun i => φ (x i)))
  change z ∈ W

  -- 使用局部化模块的归纳法：z 可以写成 mk m s 的形式
  induction z using LocalizedModule.induction_on with
  | h m s =>
    -- 【修正步骤】
    -- 1. 不要 change hf_smul_mem_N。
    -- 2. 直接应用 hf_smul_mem_N m 得到 f • m ∈ N。
    -- 3. 同时利用冒号显式指定类型为 span ... (因为 N 定义为 span，所以这是合法的)
    have h_mem : f • m ∈ span R (Set.range x) := hf_smul_mem_N m

    -- 第一步：证明 φ(f • m) ∈ W
    have h_phi_fm_in_W : φ (f • m) ∈ W := by
      -- 【修正】使用 refine，将 h_mem 显式填入最后一个参数位置
      -- 前面的四个 ?_ 分别对应：1.生成元 2.零 3.加法 4.数乘
      refine Submodule.span_induction (p := fun n _ => φ n ∈ W) ?_ ?_ ?_ ?_ h_mem

      · -- 1. 生成元情况：n ∈ range x
        intro n hn
        rcases Set.mem_range.mp hn with ⟨i, rfl⟩
        -- 显式指定 R := R_f 以帮助类型推断
        apply Submodule.subset_span (R := R_f)
        exact Set.mem_range_self i

      · -- 2. 0 的情况
        exact W.zero_mem

      · -- 3. 加法封闭性
        intro a b _ _ ha hb
        rw [φ.map_add]
        exact W.add_mem ha hb

      · -- 4. 数乘封闭性 (R 作用)
        intro r n _ hn
        rw [φ.map_smul]
        -- 将 R 的数乘转化为 R_f 的数乘 (r • x = algebraMap r • x)
        -- 这样才能使用 W.smul_mem (因为 W 是 R_f 模)
        rw [← IsScalarTower.algebraMap_smul R_f r (φ n)]
        apply W.smul_mem
        exact hn
    --
    -- 先获取“它是单位元”的证明 (Prop)
    have hf_unit : IsUnit ((algebraMap R R_f) f) := by
        have h_mem : f ∈ S := Submonoid.mem_powers f
        let f_elem : S := ⟨f, h_mem⟩
        exact IsLocalization.map_units R_f f_elem

      -- 从证明中提取单位元数据 (Data, 类型为 R_fˣ)
    let f_unit := hf_unit.unit
    -- 构造等式：φ(m) = f⁻¹ • (f • φ(m))
      -- 我们需要显式地写出这个代数变换
      -- 应用这个等式
    have eq_id : φ m = (↑f_unit⁻¹ : R_f) • (algebraMap R R_f f • φ m) := by
        obtain ⟨u, hu⟩ := hf_unit
        -- f_unit 和 u 应该相同
        have : f_unit = u := by
          ext
          rw [IsUnit.unit_spec]
          rw [hu]
        rw [this, ← hu]
        simp only [smul_smul]
        rw [show ((↑u⁻¹ : R_f) * ↑u : R_f) = 1 by simp]
        simp
    --
    -- 第二步：利用 f 在 R_f 中可逆，推导出 φ(m) ∈ W
    have h_phi_m_in_W : φ m ∈ W := by
      rw [φ.map_smul] at h_phi_fm_in_W
      rw [eq_id]
      -- 因为 W 是 R_f 子模，所以乘以 f⁻¹ 仍在 W 中
      apply W.smul_mem
      exact h_phi_fm_in_W
    --现在只需从 φ m ∈ W 推导出 LocalizedModule.mk m s ∈ W ∈ W 即可
    -- ... (接在 h_phi_m_in_W 之后)

    -- s 属于 S，因此在局部化环 R_f 中是单位元
    have hs_unit : IsUnit (algebraMap R R_f s) := IsLocalization.map_units R_f s

    -- 下面证明 mk m s = s⁻¹ • φ(m)
    rw [show LocalizedModule.mk m s = (Localization.mk 1 s) • φ m by
      have: φ m = LocalizedModule.mk m 1 := by
        rfl
      rw [this]
      rw[LocalizedModule.mk_smul_mk]
      rw[mul_one,one_smul]
    ]
    -- 因为 W 是 R_f 子模，且 φ m ∈ W，所以 s⁻¹ • φ m ∈ W
    apply W.smul_mem
    exact h_phi_m_in_W

end Nakayamalemmas
section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
theorem prop_nine_general
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} (hI : IsNilpotent I) {N : Submodule R M}
    (h : I • N = N) : N = 0 := by
  obtain ⟨n, hn⟩ := hI
  have hN : ∀ k, I ^ k • N = N := by
    intro k
    induction k with
    | zero => simp
    | succ k IH =>
      calc
        I ^ (k + 1) • N = (I ^ k * I) • N := by rw [pow_succ]
        _ = I ^ k • (I • N) := by rw [mul_smul]
        _ = I ^ k • N := by rw [h]
        _ = N := IH
  have hNn := hN n
  rw [hn, zero_smul] at hNn
  exact hNn.symm
variable (A B : Submodule R M)
lemma surjective_from_B_to_M_over_A_of_sup_eq_top (h : A ⊔ B = ⊤) :
    Function.Surjective (fun (b : B) => (A.mkQ) b) := by
  intro q
  have sur : Function.Surjective (A.mkQ) :=by
    exact Submodule.Quotient.mk_surjective A
  rcases sur q with ⟨x,quo⟩
  have : x ∈ A ⊔ B := by
   rw[h]
   exact Submodule.mem_top
  rcases Submodule.mem_sup.1 this with ⟨a, ha, b, hb, hh⟩
  refine ⟨⟨b, hb⟩, ?_⟩
  calc
    (fun (b : B) => (A.mkQ) b) ⟨b,hb⟩ = (A.mkQ) b := by rfl
    _ = (A.mkQ) (a+b) - (A.mkQ) a := by simp [map_add]
    _ = (A.mkQ) x - (A.mkQ) a := by rw[←hh]
    _ = (A.mkQ) x - 0 := by simp[ha]
    _ = q := by simp[quo]
lemma quotient_smul_eq_from_eq_sum
{I : Ideal R}
(N N' : Submodule R M)
(h_decomposition : N ⊔ (I • N') = ⊤) :
let Q := M ⧸ N
(⊤ : Submodule R Q) = I • ⊤ := by
  let S := I • N'
  have h_surj : Function.Surjective (fun (x : S) => N.mkQ x) := by
    apply surjective_from_B_to_M_over_A_of_sup_eq_top N S
    exact h_decomposition
  apply le_antisymm _ le_top
  intro x _
  rcases h_surj x with ⟨b, rfl⟩
  have hb : b.1 ∈ I • N' := b.2
  apply Submodule.smul_induction_on (p := fun m => N.mkQ m ∈ I • ⊤) hb
  · intro r hr n hn
    rw [map_smul]
    apply Submodule.smul_mem_smul hr
    exact Submodule.mem_top
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
theorem prop_ten_from_nine {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} (hI : IsNilpotent I)
    {N N₀ : Submodule R M} (h_eq : (⊤ : Submodule R M) = N ⊔ I • N₀) :
    (⊤ : Submodule R M) = N := by
  let Q := M ⧸ N
  let π : M →ₗ[R] Q := Submodule.mkQ N
  have hQ_eq' : ⊤ = I • (⊤ : Submodule R Q) := by
    have h_decomp : N ⊔ I • N₀ = ⊤ := by
      rw [← h_eq]
    exact quotient_smul_eq_from_eq_sum N N₀ h_decomp
  have hQ_eq : I • (⊤ : Submodule R Q) = ⊤ := by
    nth_rw 2 [hQ_eq']
  have hQ_zero : (⊤ : Submodule R Q) = ⊥ :=
    prop_nine_general hI hQ_eq
  ext x
  simp only [Submodule.mem_top]
  constructor
  · intro hx
    have h_mkQ : N.mkQ x = 0 := by
      have : N.mkQ x ∈ (⊤ : Submodule R Q) := Submodule.mem_top
      rw [hQ_zero] at this
      exact this
    exact (Submodule.Quotient.mk_eq_zero N).mp h_mkQ
  · intro _
    trivial
theorem prop_eleven_from_nine {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} (hI : IsNilpotent I)
    {N : Type*} [AddCommGroup N] [Module R N]
    (f : N →ₗ[R] M)
    (h_map : ∀ x ∈ I • (⊤ : Submodule R N), f x ∈ I • (⊤ : Submodule R M))
    (h_surj_mod : Function.Surjective
    (Submodule.mapQ (I • (⊤ : Submodule R N)) (I • (⊤ : Submodule R M)) f h_map)) :
    Function.Surjective f := by
  let Q := M ⧸ LinearMap.range f
  let π : M →ₗ[R] Q := Submodule.mkQ (LinearMap.range f)
  let N' : Submodule R M := LinearMap.range f
  have h_decomp : ∀ m : M, ∃ (n : N) (y : M), y ∈ I • (⊤ : Submodule R M) ∧ m = f n + y := by
    intro m
    let m_bar : M ⧸ (I • (⊤ : Submodule R M)) := Submodule.Quotient.mk m
    rcases h_surj_mod m_bar with ⟨n_bar, hn⟩
    rcases Submodule.Quotient.mk_surjective _ n_bar with ⟨n, rfl⟩
    have : Submodule.mapQ (I • ⊤) (I • ⊤) f h_map (Submodule.Quotient.mk n) = m_bar := hn
    simp_rw [Submodule.mapQ_apply] at this
    have h_diff : f n - m ∈ I • (⊤ : Submodule R M) :=
      (Submodule.Quotient.eq (p := I • ⊤)).mp this
    refine ⟨n, m - f n, ?_, ?_⟩
    · have : m - f n = -(f n - m) := by abel
      rw [this]
      exact Submodule.neg_mem _ h_diff
    · simp
  have h_eq : (⊤ : Submodule R M) = LinearMap.range f ⊔ I • (⊤ : Submodule R M) := by
     refine le_antisymm ?_ (by simp)
     intro m hm
     rcases h_decomp m with ⟨n, y, hy, hm_eq⟩
     have : m ∈ LinearMap.range f ⊔ I • (⊤ : Submodule R M) := by
        rw [hm_eq]
        exact Submodule.add_mem_sup (LinearMap.mem_range_self f n) hy
     exact this
  have h_eq': LinearMap.range f ⊔ I • (⊤ : Submodule R M) = (⊤ : Submodule R M) := by
    nth_rw 2 [h_eq]
  have hQ_eq' : ⊤ = I • (⊤ : Submodule R Q) := by
    exact quotient_smul_eq_from_eq_sum N' (⊤ : Submodule R M) h_eq'
  have hQ_eq : I • (⊤ : Submodule R Q) = ⊤ := by
    nth_rw 2 [hQ_eq']
  have hQ_zero : (⊤ : Submodule R Q) = ⊥ :=
    prop_nine_general hI (by rw [hQ_eq])
  intro m
  have : π m = 0 := by
    have : π m ∈ (⊤ : Submodule R Q) := Submodule.mem_top
    rw [hQ_zero] at this
    exact ( Submodule.mem_bot R).mp this
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mp this
theorem prop_twelve_from_nine {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} (hI : IsNilpotent I)
    {A : Type*}
    (x : A → M)
    (h_gen_mod : Submodule.span R (Set.range x) ⊔ I • (⊤ : Submodule R M) = ⊤) :
    Submodule.span R (Set.range x) = ⊤ := by
  let N : Submodule R M := Submodule.span R (Set.range x)
  let N₀ : Submodule R M := ⊤
  let Q := M ⧸ N
  let π : M →ₗ[R] Q := Submodule.mkQ N
  have hQ_eq' : ⊤ = I • (⊤ : Submodule R Q) := by
    have h_decomp : N ⊔ I • N₀ = ⊤ := by
      rw [← h_gen_mod]
    exact quotient_smul_eq_from_eq_sum N N₀ h_decomp
  have hQ_eq : I • (⊤ : Submodule R Q) = ⊤ := by
    nth_rw 2 [hQ_eq']
  have hQ_zero : (⊤ : Submodule R Q) = ⊥ :=
    prop_nine_general hI (by rw [hQ_eq])
  ext m
  simp only [Submodule.mem_top, iff_true]
  have : π m = 0 := by
    have h1 : π m ∈ (⊤ : Submodule R Q) := Submodule.mem_top
    rw [hQ_zero] at h1
    simp only [Submodule.mem_bot] at h1
    exact h1
  exact (Submodule.Quotient.mk_eq_zero N).mp this
  end
