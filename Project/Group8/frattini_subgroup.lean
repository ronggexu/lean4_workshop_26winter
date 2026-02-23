import Mathlib
/--
根据定义可知,小于等于所有Coatom的子群会小于等于frattini子群.
-/
theorem le_frattini_of_le_Coatom {G : Type*} [Group G]
(H : Subgroup G)
(hle : ∀ K : Subgroup G, IsCoatom K → H ≤ K) :
    H ≤ frattini G := by
  --跟踪frattini子群的定义
  have : frattini G = Order.radical (Subgroup G) := by rfl
  rw[this]
  have :Order.radical (Subgroup G)
  = ⨅ a ∈ {H : Subgroup G | IsCoatom H}, a := by rfl
  rw[this]
  --来自aesop?
  simp_all only [Set.mem_setOf_eq, le_iInf_iff, implies_true]

/--
定理：一个子群存在一个真补子群当且仅当它不包含在frattini子群里
(我们把任意真子群包含于极大子群作为假设,不调用选择公理).
-/
theorem partial_complement_exists_iff_notin_frattini {G : Type*}
 [Group G] (H : Subgroup G) [IsCoatomic (Subgroup G)] :
    (∃ K : Subgroup G, (H ⊔ K = ⊤) ∧ (K < ⊤)) ↔ ¬(H ≤ frattini G)
     := by
  constructor
  · --左推右:如果H≤ frattini G,H⊔ K =⊤意味着frattini G⊔ K = ⊤
    --这样根据frattini subgroup的非生成性, K = ⊤,矛盾
    intro h_exists
    rcases h_exists with ⟨K, h_sup, h_lt⟩
    by_contra h_le
    have gen : K ⊔ frattini G = ⊤ := by
      order
    have : K = ⊤ := by
      exact frattini_nongenerating gen
    order
  · --右推左:如果H不包含在frattini G里,则存在一个极大子群L使得H不包含在L里
    --这样根据极大性H⊔ L = ⊤.
    intro h_not_le
    by_contra
    have a_fact : ∃ L : Subgroup G, (IsCoatom L) ∧ (¬(H ≤ L)) := by
      by_contra h_contra
      push_neg at h_contra
      have : H ≤ frattini G := by
        exact le_frattini_of_le_Coatom H h_contra
      contradiction
    rcases a_fact with ⟨L, h_coatom, h_not_le⟩
    have supeq : H ⊔ L = ⊤ := by
      rw[←IsCoatom.lt_iff h_coatom]
      order
    have : L < ⊤ := by
      exact IsCoatom.lt_top h_coatom
    have : ∃ K : Subgroup G, (H ⊔ K = ⊤) ∧ (K < ⊤) := by
      use L
    contradiction

--推论：如果frattini因子是循环的，那么原群也是循环的
theorem cyclic_of_frattini_factor_cyclic {G : Type*} [Group G]
[IsCoatomic (Subgroup G)] :
    IsCyclic (G ⧸ frattini G) → IsCyclic (G) := by
  intro h_cyclic
  --取商群生成元x以及原像g.
  rcases h_cyclic with ⟨x, hx⟩
  have : ∃ g : G, QuotientGroup.mk' (frattini G) g = x := by
    apply QuotientGroup.mk'_surjective
  rcases this with ⟨g, hg⟩
  --证明g生成的子群K与frattini子群生成G.
  let K := Subgroup.closure ({g} : Set G)
  have : K ⊔ frattini G = ⊤ := by
    ext y
    constructor
    · intro hy
      trivial
    · intro hy
      --先扔进商群,有y的像是x的幂
      obtain ⟨n, hn⟩ := hx (QuotientGroup.mk' (frattini G) y)
      have : QuotientGroup.mk' (frattini G) y = x^n := by
        rw[←hn]
      --改写表达式为yg⁻ⁿ ∈ frattini G
      have : QuotientGroup.mk' ( frattini G) (y * g^(-n)) = 1 := by
        calc
          QuotientGroup.mk' (frattini G) (y * g^(-n))
          = QuotientGroup.mk' (frattini G) y
          * QuotientGroup.mk' (frattini G) g^(-n) := by rfl
          _ = (x^n)*((QuotientGroup.mk' (frattini G) g)^(-n)) := by
            rw[this]
          _ = (x^n)*((x)^(-n)) := by rw[hg]
          _ = 1 := by group
      --从而yg⁻ⁿ ∈ frattini ≤  K ⊔ frattini G
      have : y * g^(-n) ∈ frattini G := by
        rw [← QuotientGroup.ker_mk' (frattini G), MonoidHom.mem_ker]
        exact this
      have in1: y * g^(-n) ∈ K ⊔ (frattini G) := by
        have le : (frattini G) ≤ K ⊔ (frattini G) := by
          apply le_sup_right
        apply le
        exact this
      --又g^n∈ K≤  K ⊔ frattini G
      have : g^n ∈ K := by
        rw [Subgroup.mem_closure_singleton]
        use n
      have in2: g^n ∈ K ⊔ (frattini G) := by
        have le : K ≤ K ⊔ (frattini G) := by
          apply le_sup_left
        apply le
        exact this
      --所以y ∈ K ⊔ frattini G
      have : y = (y * g^(-n)) * g^n := by group
      rw[this]
      exact Subgroup.mul_mem _ in1 in2
  --根据frattini subgroup的非生成性, K = ⊤,所以G是循环的
  have : K = ⊤ := by
    exact frattini_nongenerating this
  --结束了
  have : ⊤ = Subgroup.closure ({g} : Set G) := by
    rw[←this]
  -- 后面讲点废话把this对接到IsCyclic的定义上
  refine ⟨g, ?_⟩
  intro y
  have hy : y ∈ Subgroup.closure ({g} : Set G) := by
    rw[←this]
    trivial
  rw [Subgroup.mem_closure_singleton] at hy
  exact hy

-- 定理:(有限) p-群→ 幂零群→ 正规化子条件→ Coatom是正规子群
-- 这个只需要找找接口
theorem normal_of_Coatom_PGroup {P : Type*} [Group P] [Finite P]
  {p : ℕ} [hp : Fact (Nat.Prime p)]
  (hP : IsPGroup p P) (H : Subgroup P)
  (hMax : IsCoatom H) : H.Normal := by
  -- 注册幂零群实例
  haveI : Group.IsNilpotent P := IsPGroup.isNilpotent hP
  -- 获取正规化子条件
  have hNC : NormalizerCondition P := normalizerCondition_of_isNilpotent
  -- 利用正规化子条件证明Coatom是正规的
  exact Subgroup.NormalizerCondition.normal_of_coatom H hNC hMax

-- 定理:有限p-群的Coatom是指数p的.
theorem index_of_Coatom_PGroup {P : Type*} [Group P] [Finite P]
  {p : ℕ} [hp : Fact (Nat.Prime p)]
  (hP : IsPGroup p P) (H : Subgroup P)
  (hMax : IsCoatom H) : H.index = p := by
  --注册正规子群实例,要取商群.
  have h_normal : H.Normal := normal_of_Coatom_PGroup hP H hMax
  haveI := h_normal
  --商群的解整除P的阶=p的幂,且商群非平凡,由此,商群的阶被p整除.
  have Porder : ∃ (n : ℕ), Nat.card P = p ^ n := by
    rw [← IsPGroup.iff_card]
    exact hP
  rcases Porder with ⟨n, Porder'⟩
  have pdv: p ∣ Nat.card (P ⧸ H) := by
    have div:Nat.card (P ⧸ H) ∣ Nat.card P := by
      exact Subgroup.card_quotient_dvd_card H
    rw [Porder'] at div
    have nont: Nat.card (P ⧸ H)>1 := by
      have : H < ⊤ := IsCoatom.lt_top hMax
      have : H ≠ ⊤ := by
        exact ne_of_lt this
      have : 1< H.index := Subgroup.one_lt_index_of_ne_top this
      rw[Subgroup.index_eq_card H] at this
      exact this
    rw[Nat.dvd_prime_pow hp.out] at div
    rcases div with ⟨k, hk1,hk2⟩
    rw[hk2]
    have ntv:k≠0 := by
      by_contra h_contra
      have : Nat.card (P ⧸ H) = 1 := by
        rw[hk2,h_contra,pow_zero]
      rw[this] at nont
      contradiction
    exact dvd_pow_self p ntv
  --对商群使用sylow定理,p=p^1用来对接口
  have :p = p ^ 1 := by rw [pow_one]
  rw[this] at pdv
  have : ∃ X : Subgroup (P ⧸ H), Nat.card X = p^1
  := Sylow.exists_subgroup_card_pow_prime p pdv
  rcases this with ⟨X, hX⟩
  rw[←this] at hX
  let Q := X.comap (QuotientGroup.mk' H)
  --接下来根据对应定理得到|Q/H|=|X|=p
  --首先证明Q/H=X
  have : Subgroup.map (QuotientGroup.mk' H)
   (Subgroup.comap (QuotientGroup.mk' H) X) = X := by
    exact Subgroup.map_comap_eq_self_of_surjective
     (QuotientGroup.mk'_surjective H) X
  have : Subgroup.map (QuotientGroup.mk' H)
   (Q) = X := by
    rw[←this]
  --调用定理得到ker(π)对Q的相对指数等于|f(Q)|
  have equation: (QuotientGroup.mk' H).ker.relIndex Q
  = Nat.card ↥(Subgroup.map (QuotientGroup.mk' H) Q) := by
    exact Subgroup.relIndex_ker Q (QuotientGroup.mk' H)
  rw[this,hX] at equation
  have ker_eq: (QuotientGroup.mk' H).ker = H := by
    rw [QuotientGroup.ker_mk' H]
  rw[ker_eq] at equation
  --至此已经改写为H对Q相对指数的等于p.
  have neone : p ≠ 1 := by
    exact Nat.Prime.ne_one hp.out
  rw[←equation] at neone
  --所以Q不能≤ H
  have consequence: ¬(Q≤ H) := by
    by_contra
    rw[← Subgroup.relIndex_eq_one] at this
    contradiction
  --又H ≤ Q.
  have but: H ≤ Q := by
    rw[← (QuotientGroup.ker_mk' H)]
    exact Subgroup.ker_le_comap (QuotientGroup.mk' H) X
  have :H<Q := by order
  --根据极大性Q=⊤,所以H的指数是p.
  rw[IsCoatom.lt_iff hMax] at this
  rw[this] at equation
  rw[← Subgroup.relIndex_top_right H]
  exact equation

--定理：p-群的frattini因子是elementary abelian的
theorem frattini_factor_elementary_abelian_of_PGroup
{P : Type*} [Group P] [Finite P]
{p : ℕ} [hp : Fact (Nat.Prime p)]
(hP : IsPGroup p P) :
    (∀ g : (P ⧸ frattini P), g ^ p = 1)∧
     (IsMulCommutative (P ⧸ frattini P)) := by
  --先拿到coatomic
  haveI : IsCoatomic (Subgroup P) := Finite.to_isCoatomic
  constructor
  · intro g
    --取原像
    have : ∃ g' : P, QuotientGroup.mk' (frattini P) g' = g := by
      apply QuotientGroup.mk'_surjective
    rcases this with ⟨g', hg'⟩
    --下面证明g'^p ∈ frattini P
    --为此首先证明g'^p在所有coatom中.
    have critical: ∀ K : Subgroup P, IsCoatom K → g'^p ∈ K := by
      intro K hK
      --这样K是指数p的正规子群
      haveI : K.Normal := normal_of_Coatom_PGroup hP K hK
      have indexeqp: K.index = p := index_of_Coatom_PGroup hP K hK
      rw[← QuotientGroup.ker_mk' K]
      rw[MonoidHom.mem_ker]
      have : QuotientGroup.mk' K (g'^p) = (QuotientGroup.mk' K g')^p := by rfl
      rw[this]
        --商群的阶=p
      have : Nat.card (P ⧸ K) = p := by
        rw[← Subgroup.index_eq_card K]
        exact indexeqp
      rw[← this]
      exact pow_card_eq_one'
    --下面由此证明g'^p ∈ frattini P
    have theend: g'^p ∈ frattini P := by
      --重写定义,Gemini找接口
      have : frattini P = Order.radical (Subgroup P) := by rfl
      rw[this]
      have :Order.radical (Subgroup P)
       = ⨅ a ∈ {H : Subgroup P | IsCoatom H}, a := by rfl
      rw[this]
      simp_rw[Subgroup.mem_iInf]
      exact critical
    --g^p的像是g'^p,由此结束
    have : QuotientGroup.mk' (frattini P) (g'^p)
    = (QuotientGroup.mk' (frattini P) g')^p := by rfl
    rw[hg'] at this
    rw[← this,← MonoidHom.mem_ker, QuotientGroup.ker_mk' (frattini P)]
    exact theend
  · constructor
    constructor
    intro g h
    --仿照上面的流程
    --取原像
    have : ∃ g' : P, QuotientGroup.mk' (frattini P) g' = g := by
      apply QuotientGroup.mk'_surjective
    rcases this with ⟨g', hg'⟩
    --取原像
    have : ∃ g' : P, QuotientGroup.mk' (frattini P) g' = g := by
      apply QuotientGroup.mk'_surjective
    rcases this with ⟨g', hg'⟩
    have : ∃ h' : P, QuotientGroup.mk' (frattini P) h' = h := by
      apply QuotientGroup.mk'_surjective
    rcases this with ⟨h', hh'⟩
    --下面证明g'h'(g')^{-1}(h')^{-1} ∈ frattini P
    --为此首先证明g'h'(g')^{-1}(h')^{-1}在所有coatom中.
    have critical2: ∀ K : Subgroup P, IsCoatom K →
     g'*h'*(g')⁻¹*(h')⁻¹ ∈ K := by
      intro K hK
      --这样K是指数p的正规子群
      haveI : K.Normal := normal_of_Coatom_PGroup hP K hK
      have indexeqp: K.index = p := index_of_Coatom_PGroup hP K hK
      rw[← QuotientGroup.ker_mk' K]
      rw[MonoidHom.mem_ker]
      have : QuotientGroup.mk' K (g'*h'*(g')⁻¹*(h')⁻¹)
      = (QuotientGroup.mk' K g')*(QuotientGroup.mk' K h')
       *(QuotientGroup.mk' K g')⁻¹*(QuotientGroup.mk' K h')⁻¹ := by rfl
      rw[this]
        --商群的阶=p
      have : Nat.card (P ⧸ K) = p := by
        rw[← Subgroup.index_eq_card K]
        exact indexeqp
      have : IsCyclic (P ⧸ K) := isCyclic_of_prime_card this
      have : Std.Commutative fun (x1 x2 : (P ⧸ K)) => x1 * x2 :=
        IsCyclic.commutative
      rcases this with ⟨comm⟩
      have :
        (QuotientGroup.mk' K h')
         *(QuotientGroup.mk' K g')⁻¹
        = (QuotientGroup.mk' K g')⁻¹
         *(QuotientGroup.mk' K h') := by
           rw[comm]
      calc
         (QuotientGroup.mk' K g')*(QuotientGroup.mk' K h')
         *(QuotientGroup.mk' K g')⁻¹*(QuotientGroup.mk' K h')⁻¹
        _ = (QuotientGroup.mk' K g')*((QuotientGroup.mk' K h')
         *(QuotientGroup.mk' K g')⁻¹)*(QuotientGroup.mk' K h')⁻¹ := by group
        _ = (QuotientGroup.mk' K g')*((QuotientGroup.mk' K g')⁻¹
         *(QuotientGroup.mk' K h'))*(QuotientGroup.mk' K h')⁻¹ := by rw[this]
        _ = 1 := by group
    --g'h'(g')^{-1}(h')^{-1}于是落在frattini P里
    have theend2: g'*h'*(g')⁻¹*(h')⁻¹ ∈ frattini P := by
      --重写定义,Gemini找接口
      have : frattini P = Order.radical (Subgroup P) := by rfl
      rw[this]
      have :Order.radical (Subgroup P)
       = ⨅ a ∈ {H : Subgroup P | IsCoatom H}, a := by rfl
      rw[this]
      simp_rw[Subgroup.mem_iInf]
      exact critical2
    --g'h'(g')^{-1}(h')^{-1}的像是1,由此结束
    rw[← QuotientGroup.ker_mk' (frattini P),MonoidHom.mem_ker] at theend2
    have : QuotientGroup.mk' (frattini P) (g'*h'*(g')⁻¹*(h')⁻¹)
      = (QuotientGroup.mk' (frattini P) g')
       *(QuotientGroup.mk' (frattini P) h')
       *(QuotientGroup.mk' (frattini P) g')⁻¹
       *(QuotientGroup.mk' (frattini P) h')⁻¹ := by rfl
    rw[this,hg',hh'] at theend2
    calc
      g*h
       = (g*h*g⁻¹*h⁻¹)*(h * g) := by group
      _ = 1*(h*g) := by rw[theend2]
      _ = h*g := by rw[one_mul]

--辅助引理:对有限ZMod p模的非0元素x,存在一个coatom H不包含x
lemma exist_coatom_of_nonzero_element
{P : Type*} {p : ℕ} [AddCommGroup P] [Module (ZMod p) P] [Finite P]
 [hp : Fact (Nat.Prime p)] :
(∀ x : P,x ≠ 0 →
 (∃ H : (Submodule (ZMod p) P),(IsCoatom H)∧(x ∉ H))) := by
  intro x xnezero
  -- K=⟨x⟩
  let K := Submodule.span (ZMod p) {x}
  have xinK : x ∈ K := Submodule.mem_span_singleton_self x
  -- 补空间定理取出K的补空间M
  obtain ⟨M, h_compl⟩ := Submodule.exists_isCompl K
  use M
  constructor
  · --证M是coatom
    constructor
    · --证M≠⊤
      by_contra
      rw[this] at h_compl
      have infeq : K ⊓ ⊤ = ⊥ := h_compl.inf_eq_bot
      have : K ⊓ ⊤ = K := by order
      rw[this] at infeq
      rw[infeq] at xinK
      rw[Submodule.mem_bot] at xinK
      contradiction
    · --证M的极大性
      --设M < N,要证N=⊤
      intro N h_lt
      have h_le:M ≤ N := le_of_lt h_lt
      have h_nle:¬(N≤M) := by order
      rw[SetLike.le_def] at h_nle
      push_neg at h_nle
      --取y∈N,y∉M
      rcases h_nle with ⟨y,hy⟩
      rcases hy with ⟨hy1,hy2⟩
      have h_sup : K ⊔ M = ⊤ := h_compl.sup_eq_top
      have h_mem : y ∈ K ⊔ M := by rw [h_sup]; exact Submodule.mem_top
      --y=a+b,a∈K,b∈M⊆N,所以a∈N,又y∉M表明a≠ 0
      rcases Submodule.mem_sup.mp h_mem with ⟨a, ha, b, hb, yeqapb⟩
      have hb':b ∈ N := by
        rw[SetLike.le_def] at h_le
        exact h_le hb
      have :a=y-b := by rw[←yeqapb];abel
      have ainN: a ∈ N := by rw[this];exact N.sub_mem hy1 hb'
      have anez: a≠ 0:= by
        by_contra
        rw[this,zero_add] at yeqapb
        rw[yeqapb] at hb
        contradiction
      -- N中非零的a当然生成整个K
      rw[Submodule.mem_span_singleton] at ha
      rcases ha with ⟨r,hr⟩
      have : r ≠ 0 := by
        by_contra
        rw[this] at hr
        apply anez
        rw[←hr]
        exact Module.zero_smul x
      have : x = r⁻¹ • a := by
        rw[← hr]
        rw[← mul_smul (r⁻¹) r x]
        rw[inv_mul_cancel₀ this]
        rw[one_smul]
      have: x∈ N := by rw[this];exact N.smul_mem (r⁻¹) ainN
      have: K ≤ N := by rw[Submodule.span_singleton_le_iff_mem x N];exact this
      order
  · intro hxM
    have hxK : x ∈ K := Submodule.mem_span_singleton_self x
    obtain ⟨h_disj, _⟩ := h_compl
    have h_zero : x = 0 := Submodule.disjoint_def.mp h_disj x hxK hxM
    exact xnezero h_zero




--定理：p-群的frattini子群是平凡子群当且仅当原群是elementary abelian的
theorem frattini_eq_bot_iff_elementary_abelian_of_PGroup
{P : Type*} [Group P] [Finite P]
{p : ℕ} [hp : Fact (Nat.Prime p)]
(hP : IsPGroup p P) :
    frattini P = ⊥ ↔ ((∀ g : P, g ^ p = 1)∧(IsMulCommutative P)) := by
  constructor
  · intro h_frattini_bot
    rcases frattini_factor_elementary_abelian_of_PGroup
       hP with ⟨ele,ab⟩
    constructor
    · intro g
      have usingtheorem : (QuotientGroup.mk' (frattini P) g)^p=1 := by
        exact ele g
      have :(QuotientGroup.mk' (frattini P) g)^p
      = QuotientGroup.mk' (frattini P) (g^p) := by rfl
      rw[this] at usingtheorem
      rw[← MonoidHom.mem_ker,QuotientGroup.ker_mk' (frattini P)
      ,h_frattini_bot]
      at usingtheorem
      rw[Subgroup.mem_bot] at usingtheorem
      exact usingtheorem
    · constructor
      constructor
      intro a b
      --交换性我们看这前面的办法写
      let a' := (QuotientGroup.mk' (frattini P) a)
      let b' := (QuotientGroup.mk' (frattini P) b)
      have usingtheorem' :
       a'*b'
       = b'*a'
       := ab.is_comm.comm a' b'
      have : a'*b'*a'⁻¹*b'⁻¹=1 := by
        rw[usingtheorem']
        group
      have muleq : (QuotientGroup.mk' (frattini P) (a*b*a⁻¹*b⁻¹))
       = a'*b'*a'⁻¹*b'⁻¹ := by rfl
      have : (QuotientGroup.mk' (frattini P) (a*b*a⁻¹*b⁻¹))=1 := by
        rw[muleq]
        exact this
      rw[← MonoidHom.mem_ker, QuotientGroup.ker_mk' (frattini P),
       h_frattini_bot,Subgroup.mem_bot] at this
      calc
        a*b = (a*b*a⁻¹*b⁻¹)*b*a := by group
        _ = 1*b*a := by rw[this]
        _ = b*a := by group
  · rintro ⟨h_exp, h_comm⟩
    -- 化归为证明对于任意g≠ 1,g∉ frattini P
    rw [eq_bot_iff]
    rw[SetLike.le_def]
    intro g h_g_fra
    rw[Subgroup.mem_bot]
    by_contra h_g_ne_one
    -- (1)获得 ZMod p 模结构
    -- 利用交换性提升 P 为 CommGroup
    letI : CommGroup P :=
     { ‹Group P› with mul_comm := h_comm.is_comm.comm }
    let A := Additive P
    --pA=0← Pᵖ=e.
    have h_nsmul : ∀ x : A, p • x = 0 := by
      intro x
      exact h_exp (Additive.toMul x)
    --用AddCommGroup.zmodModule获取ZMod p模结构.
    --根据gemini的建议在这里添加了显式参数n=p,
    --这神秘地解决了后面的某个看起来毫不相关的问题.
    letI := AddCommGroup.zmodModule (n := p) h_nsmul
    -- (2) g模结构中对应x ≠ 0
    let x : A := Additive.ofMul g
    have h_x_ne_zero : x ≠ 0 := by
      intro h
      apply h_g_ne_one
      exact (Equiv.apply_eq_iff_eq Additive.ofMul).mp h
    -- (3) 根据辅助引理得到一个 coatom H_mod 不包含 x
    --注意显式指定变量p,不然会自动推断失败
    obtain ⟨H_mod, h_coatom_H_mod, h_x_not_in_H⟩ :=
     exist_coatom_of_nonzero_element (p := p) x h_x_ne_zero
    -- 将 ZMod p 模的极大子模 H_mod 转换为 P 的乘法子群 H_sub
    let H_sub : Subgroup P := H_mod.toAddSubgroup.toSubgroup
    -- 证明对应的coatom
    have h_coatom_H_sub : IsCoatom H_sub := by
      -- 展开 IsCoatom 的等价定义：不为全集 ⊤，且没有任何真超群
      --rw [isCoatom_iff] at h_coatom_H_mod ⊢
      --rcases h_coatom_H_mod with ⟨h_H_mod_ne_top, h_H_mod_max⟩
      constructor
      · -- 证明 H_sub ≠ ⊤
        intro h_top
        apply h_coatom_H_mod.ne_top
        -- 如果子群是全集，那么子模必然也是全集
        ext x
        constructor
        · intro _
          exact Submodule.mem_top
        · intro
          have h_mem : Additive.toMul x ∈ H_sub := by
            rw [h_top]
            exact Subgroup.mem_top (Additive.toMul x)
          exact h_mem
      · -- 证明极大性：若有子群 K 满足 H_sub < K，则 K = ⊤
        intro K h_lt
        -- 比 H_sub 大的子群 K 也是 ZMod p 子模 K_mod
        let K_mod : Submodule (ZMod p) A := {
          carrier := K.toAddSubgroup.carrier
          add_mem' := K.toAddSubgroup.add_mem'
          zero_mem' := K.toAddSubgroup.zero_mem'
          smul_mem' := by
            --从子群到Zmod p子模倒是代数上不完全平凡的
            intro c y hy
            -- 要证y在某个子模蕴含c•y在某个子模中,先把c提升成z∈ ℤ
            obtain ⟨z, rfl⟩ := ZMod.intCast_surjective c
            -- c•y=[z]•y=z•y
            have h_smul_eq : (z : ZMod p) • y = z • y :=
             Int.cast_smul_eq_zsmul (ZMod p) z y
            rw [h_smul_eq]
            -- 子群对整数数乘 (zsmul) 也是天然封闭的
            exact AddSubgroup.zsmul_mem K.toAddSubgroup hy z
        }
        -- 在模结构层面，我们依然有严格包含关系
        have h_mod_lt : H_mod < K_mod := h_lt
        -- 利用 H_mod 作为子模的极大性，得出 K_mod 必须是全集 ⊤
        rcases h_coatom_H_mod with ⟨_,h_H_mod2⟩
        have K_mod_eq_top: K_mod = ⊤
         := h_H_mod2 K_mod h_mod_lt
        -- 回到 K = ⊤
        apply le_antisymm
        · exact le_top
        · rw[SetLike.le_def]
          intro g _
          have hg : Additive.ofMul g ∈ K_mod := by
            rw [K_mod_eq_top]
            exact AddSubgroup.mem_top (Additive.ofMul g)
          exact hg
    -- (4) 结束证明
    have h_g_in_H_sub : g ∈ H_sub := by
      have :frattini P≤ H_sub := frattini_le_coatom h_coatom_H_sub
      apply this
      exact h_g_fra
    --  g ∈ H_sub就是x ∈ H_mod
    have h_x_in_H_mod : x ∈ H_mod := by
      -- gemini:强制 Lean 在底层展开子群和元素的 let 定义
      --，识别出它们是同一个集合
      change x ∈ H_mod at h_g_in_H_sub
      exact h_g_in_H_sub
    exact h_x_not_in_H h_x_in_H_mod

/--
The next theorem (Burnside theorem) proof is given by copilot Claude Opus 4.6.
-/
-- 辅助引理：ψ^n 在 frattini 因子上也诱导恒等映射
lemma MulAut_pow_trivial_on_frattini_factor
    {P : Type*} [Group P] (ψ : MulAut P)
    (h_id_induced : ∀ x : P, QuotientGroup.mk (s := frattini P) (ψ x)
      = QuotientGroup.mk (s := frattini P) x)
    (n : ℕ) :
    ∀ x : P, QuotientGroup.mk (s := frattini P) ((ψ ^ n) x)
      = QuotientGroup.mk (s := frattini P) x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; aesop

-- 辅助引理：自同构的不动点构成子群
def MulAut.fixedSubgroup {G : Type*} [Group G] (φ : MulAut G) : Subgroup G where
  carrier := {x : G | φ x = x}
  one_mem' := by simp
  mul_mem' := by aesop
  inv_mem' := by aesop

-- 辅助引理：q-阶自同构在 p^k 大小的陪集上有不动点（q ≠ p 素数时）
lemma exists_fixed_point_in_coset
    {P : Type*} [Group P] [Finite P] {p q : ℕ}
    [hp : Fact (Nat.Prime p)] [hq : Fact (Nat.Prime q)]
    (hP : IsPGroup p P) (hpq : p ≠ q)
    (b : MulAut P) (hb_order : orderOf b = q)
    (hb_triv : ∀ x : P, QuotientGroup.mk (s := frattini P) (b x)
      = QuotientGroup.mk (s := frattini P) x)
    (y : P ⧸ frattini P) :
    ∃ x : P, b x = x ∧ QuotientGroup.mk (s := frattini P) x = y := by
  obtain ⟨g, hg⟩ := Quotient.exists_rep y
  let Fiber := {x : P // QuotientGroup.mk (s := frattini P) x = y}
  -- b 保持纤维不变
  have h_b_preserves : ∀ x : Fiber, QuotientGroup.mk (s := frattini P) (b x.val) = y :=
    fun ⟨x, hx⟩ => by rw [hb_triv x, hx]
  let b_action : Fiber → Fiber := fun ⟨x, hx⟩ => ⟨b x, h_b_preserves ⟨x, hx⟩⟩
  -- Fiber ≃ frattini P，故 |Fiber| = p^k
  haveI : Finite (frattini P) := Subgroup.instFiniteSubtypeMem (frattini P)
  have h_equiv : Fiber ≃ (frattini P) := by
    refine {
      toFun := fun ⟨x, hx⟩ => ⟨g⁻¹ * x, ?_⟩
      invFun := fun ⟨f, hf⟩ => ⟨g * f, ?_⟩
      left_inv := fun ⟨x, hx⟩ => by group
      right_inv := fun ⟨f, hf⟩ => by group
    }
    · rw [← QuotientGroup.eq]; aesop
    · rw [← hg]; change ⟦g * f⟧ = ⟦g⟧; rw [QuotientGroup.eq]; simpa
  haveI : Finite Fiber := Finite.of_equiv _ h_equiv.symm
  have h_fiber_card : ∃ k : ℕ, Nat.card Fiber = p ^ k := by
    rw [Nat.card_congr h_equiv]
    exact (IsPGroup.iff_card (p := p)).mp (IsPGroup.to_subgroup hP (frattini P))
  have h_b_pow_iter : ∀ n : ℕ, ∀ x : Fiber,
      QuotientGroup.mk (s := frattini P) ((b ^ n) x.val) = y :=
    fun n ⟨x, hx⟩ => by rw [MulAut_pow_trivial_on_frattini_factor b hb_triv n x, hx]
  obtain ⟨k, hk⟩ := h_fiber_card
  -- q ∤ p^k
  have h_not_dvd : ¬ (q ∣ Nat.card Fiber) := by
    rw [hk]; intro h_dvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).mp
      (Nat.Prime.dvd_of_dvd_pow hq.out h_dvd)).symm
  -- 反证：假设无不动点，则所有轨道大小 = q，故 q | |Fiber|，矛盾
  by_contra! h_no_fixed
  have h_no_fixed' : ∀ x : Fiber, b x.val ≠ x.val :=
    fun ⟨x, hx⟩ h_eq => h_no_fixed x h_eq hx
  let b_perm : Equiv.Perm Fiber := {
    toFun := b_action
    invFun := fun ⟨x, hx⟩ => ⟨b⁻¹ x, by rw [← hb_triv (b⁻¹ x), MulAut.apply_inv_self, hx]⟩
    left_inv := by intro ⟨x, hx⟩; aesop
    right_inv := by intro ⟨x, hx⟩; aesop
  }
  have h_bperm_pow_q : b_perm ^ q = 1 := by
    ext ⟨x, hx⟩
    simp only [Equiv.Perm.coe_one, id_eq, Equiv.Perm.coe_pow]
    have h_iter : ∀ n : ℕ, (b_perm^[n]) ⟨x, hx⟩ = ⟨(b^n) x, h_b_pow_iter n ⟨x, hx⟩⟩ := by
      intro n; induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ', Function.comp_apply, ih]
        simp [b_perm, b_action, pow_succ']
    rw [h_iter q]; simp [← hb_order]
  -- 不动点计数：|Fiber| ≡ 0 [MOD q]，矛盾
  haveI : Fintype Fiber := Fintype.ofFinite Fiber
  haveI : Fintype (Function.fixedPoints b_perm) :=
    Set.Finite.fintype (Set.Finite.subset (Set.toFinite _) (Set.subset_univ _))
  have h_fixed_eq_zero : Fintype.card (Function.fixedPoints b_perm) = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun ⟨x, hx⟩ => h_no_fixed' x (congr_arg Subtype.val hx)⟩
  have h_mod : Fintype.card Fiber ≡ Fintype.card (Function.fixedPoints b_perm) [MOD q] := by
    classical
    let f : Function.End Fiber := ⇑b_perm
    have hf : f ^ (q ^ 1) = 1 := by
      rw [pow_one]; funext x
      have : (b_perm ^ q) x = x := by rw [h_bperm_pow_q]; rfl
      exact this
    convert Equiv.Perm.card_fixedPoints_modEq hf
  rw [h_fixed_eq_zero, Nat.modEq_zero_iff_dvd] at h_mod
  exact h_not_dvd (by rwa [Nat.card_eq_fintype_card])
/--
Burnside定理:如果一个p-群的p'-同构在frattini因子上诱导恒等映射，
那么它就是恒等映射.根据定义,p'-同构是指其阶数与p互素的同构.
-/
theorem PGroup_p'automorphism_id_of_id_on_frattini_factor
    {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact (Nat.Prime p)]
    (hP : IsPGroup p P) (ψ : MulAut P) (h_order : (orderOf ψ).Coprime p)
    (h_id_induced : ∀ x : P, QuotientGroup.mk (s := frattini P) (ψ x)
    = QuotientGroup.mk (s := frattini P) x) :
    ψ = 1 := by
  -- 反证法：假设 ψ ≠ 1
  by_contra h_ne
  have h_ord_pos : 0 < orderOf ψ := orderOf_pos ψ
  have h_ord_ne_one : orderOf ψ ≠ 1 := mt orderOf_eq_one_iff.mp h_ne
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd h_ord_ne_one
  have hq_ne_p : q ≠ p := by
    intro h_eq; rw [h_eq] at hq_dvd
    exact absurd h_order (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.out, hq_dvd, dvd_refl p⟩)
  set m := orderOf ψ / q with hm_def
  have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd h_ord_pos hq_dvd) hq_prime.pos
  have h_ord_eq : orderOf ψ = q * m := by rw [hm_def, Nat.mul_div_cancel' hq_dvd]
  set b := ψ ^ m with hb_def
  have hb_order : orderOf b = q := by
    rw [hb_def, orderOf_pow ψ, h_ord_eq]; simp [Nat.mul_div_left q hm_pos]
  haveI : Fact (Nat.Prime q) := ⟨hq_prime⟩
  have hb_triv : ∀ x : P, QuotientGroup.mk (s := frattini P) (b x)
      = QuotientGroup.mk (s := frattini P) x :=
    MulAut_pow_trivial_on_frattini_factor ψ h_id_induced m
  let C := MulAut.fixedSubgroup b
  have h_sup : C ⊔ frattini P = ⊤ := by
    rw [eq_top_iff]; intro g _
    obtain ⟨c, hc_fixed, hc_coset⟩ :=
      exists_fixed_point_in_coset hP hq_ne_p.symm b hb_order hb_triv
        (QuotientGroup.mk (s := frattini P) g)
    have h_diff : g⁻¹ * c ∈ frattini P := by
      rw [← QuotientGroup.eq]; exact hc_coset.symm
    rw [show g = c * (c⁻¹ * g) by group]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left hc_fixed)
      (Subgroup.mem_sup_right (by rw [show c⁻¹ * g = (g⁻¹ * c)⁻¹ by group]
                                  exact Subgroup.inv_mem _ h_diff))
  -- 由 frattini 非生成性，C = ⊤
  have hb_eq_one : b = 1 := by
    ext x; change x ∈ C; simp [frattini_nongenerating h_sup]
  -- 但 orderOf b = q > 1，矛盾
  apply hq_prime.one_lt.ne
  simpa [hb_eq_one, orderOf_one] using hb_order
