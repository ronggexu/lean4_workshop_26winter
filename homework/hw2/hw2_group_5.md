# Localization - Group 5
## 目标： 证明Localization部分Prop1.11
### 自然语言称述
$S$和$S'$是乘法闭集，将$S'^ {-1} M$视作一个$R$-模，则$S^{−1}(S'^{−1}M)$与$(SS')^{−1}M$同构。
### 自然语言证明
* 构造两个同态映射 $f: S^{−1}(S'^{−1}M) \rightarrow (SS')^{−1}M$ 和 $g: (SS')^{−1}M \rightarrow S^{−1}(S'^{−1}M)$，并证明他们互为逆，即$f\circ g= id $ 以及 $g\circ f=id$。
* 对于同态构造，选择使用泛性质来进行（为了方便形式化）
### lean代码结构
```lean
--3个引理-目标是验证可以使用泛性质

--引理1：S ⊔ S' 中的元素在 S^(-1)(S'^(-1)M) 上作用是可逆的
theorem is_unit_action_on_double_loc (t : ↥(S ⊔ S')) :
  IsUnit (LinearMap.lsmul R (LocalizedModule S (LocalizedModule S' M)) (t : R)) := by sorry

--引理2：S中元素在SS'^(-1)M上作用可逆
theorem is_unit_action_on_double_1 (t : S) :
  IsUnit (LinearMap.lsmul R (LocalizedModule (S ⊔ S') M) t) := by sorry

--引理3：S'中元素在SS'^(-1)M上作用可逆
theorem is_unit_action_on_double_2 (t : S') :
  IsUnit (LinearMap.lsmul R (LocalizedModule (S ⊔ S') M) t) := by sorry

--构造同态映射：使用 LocalizedModule.lift 函数

-- 从 S⁻¹(S'⁻¹M) 到 (SS')⁻¹M 的映射
noncomputable def toCombined :
    LocalizedModule S (LocalizedModule S' M) →ₗ[R] LocalizedModule (S ⊔ S') M := sorry

-- 从 (SS')⁻¹M 到 S⁻¹(S'⁻¹M) 的映射
noncomputable def fromCombined :
    LocalizedModule (S ⊔ S') M →ₗ[R] LocalizedModule S (LocalizedModule S' M) := sorry

--主定理：构造同构映射，使用 LinearEquiv.ofLinear 函数

--引理4：验证 fromCombined 函数 把 x/ss' 映到 (x/s')/s
lemma cal_from (m : M) (s : S) (s' : S') (s'' : ↥(S ⊔ S')) (h : s'' = (s : R) * s')
  : fromCombined S S'  (LocalizedModule.mk m s'')= LocalizedModule.mk (LocalizedModule.mk m s') s := by sorry

--引理5：验证 toCombined 函数 把 (x/s')/s 映到 x/ss'
lemma cal_to (m : M) (s : S) (s' : S') (s'' : ↥(S ⊔ S')) (h : s'' = (s : R) * s') :
  toCombined S S'  (LocalizedModule.mk (LocalizedModule.mk m s') s) = LocalizedModule.mk m s'' := by sorry

--构造同构（主要是证明from to = id 和 to from = id）
noncomputable def iso : LocalizedModule S (LocalizedModule S' M)  ≃ₗ[R] LocalizedModule (S ⊔ S') M := by sorry
```
