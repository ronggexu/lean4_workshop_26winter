

## 什么是幺半范畴

粗略地说, 一个**幺半范畴** (monoidal category) 是一个范畴 $\mathcal C$ 带有一个乘法 $\otimes\colon \mathcal C \times \mathcal C \to \mathcal C$ 以及结合律等条件. 例如向量空间的范畴 $\mathsf{Vect}_k$ 配备张量积 $\otimes_k$. 要严格地定义幺半范畴这个概念, 有两种途径:

1. 写出**融贯** (coherence) 数据. 结合律 $\alpha\colon (X\otimes Y)\otimes Z \overset{\simeq}{\to} X\otimes (Y\otimes Z)$ 需要满足一个融贯性, 即对任意四个对象 $X,Y,Z,W$, 结合律给出的两个同构 $((X\otimes Y)\otimes Z) \otimes W \to X\otimes (Y\otimes (Z\otimes W))$ 相等, 这称为**五边形恒等式**. 此外还有单位律需满足的融贯性等等.
2. 使用高阶范畴框架. 幺半范畴可以定义为范畴的 $2$-范畴 $\mathsf{Cat}$ 中的**幺半群** (monoid). 根据 Lawvere 理论的精神, 这就是一个保持乘积的函子 $\mathsf{Mon}_{\mathrm{ff}}^{\mathrm{op}} \to \mathsf{Cat}$, 其中 $\mathsf{Mon}_{\mathrm{ff}}$ 是有限生成自由幺半群的范畴.

注. 使用高阶范畴框架不需要手动写出融贯数据的原因是所有融贯数据实际上都打包在了 $\mathsf{Mon}_{\mathrm{ff}}^{\mathrm{op}}$ 中. (注意它是 $1$-范畴, 而目标范畴 $\mathsf{Cat}$ 是 $2$-范畴, 函子 $\mathsf{Mon}_{\mathrm{ff}}^{\mathrm{op}} \to \mathsf{Cat}$ 应视为 $2$-范畴之间的函子, 从而 $\mathsf{Mon}_{\mathrm{ff}}^{\mathrm{op}}$ 中的每个高阶态射都给出 $\mathsf{Cat}$ 中的高阶态射.)

两种途径的比较:

- 第一种途径比较具体, 容易建立在集合论基础上. 第二种途径比较抽象, 但在数学上适于推广, 例如 (在合适的 $\infty$-范畴论基础上) 可以轻易地推广为幺半 $\infty$-范畴的定义.
- Lean 定义幺半范畴使用的是第一种途径, 而现代数学 (特别是以高阶代数为基础的同伦论, 导出代数几何等数学分支) 使用的是第二种途径.

随着范畴层级增高, 手动写出所有融贯数据变得越来越不可能; 这使得 Lean 的范畴论无法适应现代数学中许多分支的需求.

**辫幺半范畴** (braided monoidal category) 是幺半范畴加上一个 "交换" 同构 $\beta_{X,Y} \colon X\otimes Y \to Y\otimes X$. 同样地, 有两种途径定义辫幺半范畴:

1. 手动写出融贯数据, 即辫结构与结合律给出的两个同构 $X\otimes (Y\otimes Z) \to (Y\otimes Z) \otimes X$ 相等, 这称为**六边形恒等式**.
2. 抽象地定义辫幺半范畴: 它就是 $2$-范畴 $\mathsf{Cat}$ 中的 $\mathbb E_2$-代数. 所谓 $\mathbb E_1$-代数就是结合代数 (幺半群), 而 $\mathbb E_2$-代数就是 $\mathbb E_1$-代数范畴中的 $\mathbb E_1$-代数,
$$
\mathsf{Alg}_{\mathbb E_2}(\mathcal C) \simeq \mathsf{Alg}_{\mathbb E_1}(\mathsf{Alg}_{\mathbb E_1}(\mathcal C)).
$$

## 幺半范畴在 Lean 中的实现

Mathlib 定义了类型类 `MonoidalCategory`, 以 `MonoidalCategoryStruct` 为基础, 即范畴带上一个幺半结构.

```
class MonoidalCategoryStruct (C : Type u) [𝒞 : Category.{v} C] where
  tensorObj : C → C → C
  whiskerLeft (X : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) : tensorObj X Y₁ ⟶ tensorObj X Y₂
  ...
  associator : ∀ X Y Z : C, tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z)
  leftUnitor : ∀ X : C, tensorObj tensorUnit X ≅ X
  ...

...

class MonoidalCategory (C : Type u) [𝒞 : Category.{v} C] extends MonoidalCategoryStruct C where
  ...
  pentagon :
    ∀ W X Y Z : C,
      (α_ W X Y).hom ▷ Z ≫ (α_ W (X ⊗ Y) Z).hom ≫ W ◁ (α_ X Y Z).hom =
        (α_ (W ⊗ X) Y Z).hom ≫ (α_ W X (Y ⊗ Z)).hom := by
    cat_disch
```

### 辫结构

`BraidedCategory` 类型类实现了辫幺半范畴, 而后扩展为对称幺半范畴 `SymmetricCategory`:
```
class BraidedCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] where
  braiding : ∀ X Y : C, X ⊗ Y ≅ Y ⊗ X
  ...
  hexagon_forward :
    ∀ X Y Z : C,
      (α_ X Y Z).hom ≫ (braiding X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
        ((braiding X Y).hom ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (braiding X Z).hom) := by
    cat_disch
  ...

...

class SymmetricCategory (C : Type u) [Category.{v} C] [MonoidalCategory.{v} C] extends
    BraidedCategory.{v} C where
  symmetry : ∀ X Y : C, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) := by cat_disch
```

可以看到, 这里对称幺半范畴比辫幺半范畴只多了一个**性质**, 而非增加了**结构**. 这同样是利用了范畴层级不高的便利 (换言之, 受到范畴层级不高的限制).

### 代数结构

幺半范畴中的幺半群:

```
class MonObj (X : C) where
  one : 𝟙_ C ⟶ X
  mul : X ⊗ X ⟶ X
  one_mul (X) : one ▷ X ≫ mul = (λ_ X).hom := by cat_disch
  ...
  mul_assoc (X) : (mul ▷ X) ≫ mul = (α_ X X X).hom ≫ (X ◁ mul) ≫ mul := by cat_disch
```

幺半范畴中的余幺半群:
```
class ComonObj (X : C) where
  counit : X ⟶ 𝟙_ C
  comul : X ⟶ X ⊗ X
  counit_comul (X) : comul ≫ counit ▷ X = (λ_ X).inv := by cat_disch
  ...
  comul_assoc (X) : comul ≫ X ◁ comul = comul ≫ (comul ▷ X) ≫ (α_ X X X).hom := by cat_disch
```

辫幺半范畴中的双幺半群:
```
class BimonObj (M : C) extends MonObj M, ComonObj M where
  mul_comul (M) : μ[M] ≫ Δ[M] = (Δ[M] ⊗ₘ Δ[M]) ≫ tensorμ M M M M ≫ (μ[M] ⊗ₘ μ[M]) := by cat_disch
  ...
```

辫幺半范畴中的 Hopf 代数:

```
class HopfObj (X : C) extends BimonObj X where
  antipode : X ⟶ X
  antipode_left (X) : Δ ≫ antipode ▷ X ≫ μ = ε ≫ η := by cat_disch
  antipode_right (X) : Δ ≫ X ◁ antipode ≫ μ = ε ≫ η := by cat_disch
```

### 幺半范畴的 Drinfeld 中心

幺半范畴的 Drinfeld 中心是一般的 $\mathbb E_1$-代数的中心的特例, 一般的 $\mathbb E_1$-代数的中心是一个 $\mathbb E_2$-代数, 但这件事 (Drinfeld 中心的辫结构) 在 Mathlib 中尚未形式化.

```
structure HalfBraiding (X : C) where
  β : ∀ U, X ⊗ U ≅ U ⊗ X
  monoidal : ...
  naturality : ...

...

def Center :=
  Σ X : C, HalfBraiding X
```
