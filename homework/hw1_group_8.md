# Maths in Lean: Inner product spaces

The theory of inner product spaces is developed in mathlib in the `Mathlib.Analysis.InnerProductSpace` directory.  
It builds upon the algebraic structures of modules and vector spaces, as well as the analytic structure of normed spaces.  
The following files form a core linear import chain for inner product spaces:

* `Mathlib.Algebra.Module.Basic` – Modules over a ring.
* `Mathlib.Analysis.Normed.Group.Basic` – Normed groups and additive norms.
* `Mathlib.Analysis.InnerProductSpace.Basic` – Definition of inner product spaces, basic properties.
* `Mathlib.Analysis.InnerProductSpace.Projection.Basic` – Orthogonal projection and related theorems.
* `Mathlib.Analysis.InnerProductSpace.PiL2` – The L² inner product space structure on finite products.
* `Mathlib.Analysis.InnerProductSpace.Adjoint` – Adjoint operators in inner product spaces.
* `Mathlib.Analysis.InnerProductSpace.Spectral` – Spectral theorem for self-adjoint operators (finite-dimensional case).
* `Mathlib.Analysis.InnerProductSpace.Dual` – The Riesz representation theorem.

### The basic typeclass

An inner product space is a vector space equipped with an inner product satisfying the usual axioms.  
In mathlib, the typeclass `InnerProductSpace 𝕜 E` is defined for a field `𝕜`  (usually `ℝ` or `ℂ`)  (typed `RCLike 𝕜`)  and an `AddCommGroup E` with a `Module 𝕜 E` structure.  
The inner product itself is given by the form  `inner 𝕜 x y` after `open scoped InnerProductSpace`.

```lean
class Inner.{u_4, u_5} (𝕜 : Type u_4) (E : Type u_5) : Type (max u_4 u_5)
number of parameters: 2
fields:
  Inner.inner : E → E → 𝕜
constructor:
  Inner.mk.{u_4, u_5} {𝕜 : Type u_4} {E : Type u_5} (inner : E → E → 𝕜) : Inner 𝕜 E

class InnerProductSpace.{u_4, u_5} (𝕜 : Type u_4) (E : Type u_5) [RCLike 𝕜] [SeminormedAddCommGroup E] :
  Type (max u_4 u_5)
number of parameters: 4
parents:
  InnerProductSpace.toNormedSpace : NormedSpace 𝕜 E
  InnerProductSpace.toInner : Inner 𝕜 E
fields:
  SMul.smul : 𝕜 → E → E
  SemigroupAction.mul_smul : ∀ (x y : 𝕜) (b : E), (x * y) • b = x • y • b
  MulAction.one_smul : ∀ (b : E), 1 • b = b
  DistribMulAction.smul_zero : ∀ (a : 𝕜), a • 0 = 0
  DistribMulAction.smul_add : ∀ (a : 𝕜) (x y : E), a • (x + y) = a • x + a • y
  Module.add_smul : ∀ (r s : 𝕜) (x : E), (r + s) • x = r • x + s • x
  Module.zero_smul : ∀ (x : E), 0 • x = 0
  NormedSpace.norm_smul_le : ∀ (a : 𝕜) (b : E), ‖a • b‖ ≤ ‖a‖ * ‖b‖
  Inner.inner : E → E → 𝕜
  InnerProductSpace.norm_sq_eq_re_inner : ∀ (x : E), ‖x‖ ^ 2 = RCLike.re (inner 𝕜 x x)
  InnerProductSpace.conj_inner_symm : ∀ (x y : E), (starRingEnd 𝕜) (inner 𝕜 y x) = inner 𝕜 x y
  InnerProductSpace.add_left : ∀ (x y z : E), inner 𝕜 (x + y) z = inner 𝕜 x z + inner 𝕜 y z
  InnerProductSpace.smul_left : ∀ (x y : E) (r : 𝕜), inner 𝕜 (r • x) y = (starRingEnd 𝕜) r * inner 𝕜 x y
constructor:
  InnerProductSpace.mk.{u_4, u_5} {𝕜 : Type u_4} {E : Type u_5} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [toNormedSpace : NormedSpace 𝕜 E] [toInner : Inner 𝕜 E]
    (norm_sq_eq_re_inner : ∀ (x : E), ‖x‖ ^ 2 = RCLike.re (inner 𝕜 x x))
    (conj_inner_symm : ∀ (x y : E), (starRingEnd 𝕜) (inner 𝕜 y x) = inner 𝕜 x y)
    (add_left : ∀ (x y z : E), inner 𝕜 (x + y) z = inner 𝕜 x z + inner 𝕜 y z)
    (smul_left : ∀ (x y : E) (r : 𝕜), inner 𝕜 (r • x) y = (starRingEnd 𝕜) r * inner 𝕜 x y) : InnerProductSpace 𝕜 E
``` 
The inner product induces a norm via `‖x‖ = sqrt (⟪x, x⟫)`, and `InnerProductSpace` is viewed as a special `NormedSpace`.

### Basic definitions
Inner product space over $\mathbb{R}$,$\mathbb{C}$ has some different behaviors in Lean.
We concentrete on some basic definition of $\mathbb{C}$-vector space,and some tricky things about them.

Creat a globol $\mathbb{C}$-vector space $U$.
```lean
section Introduction_to_Lean_InnerProductSpace

open InnerProductSpace
open scoped InnerProductSpace

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
```
The inner product `inner ℂ x y` has a more readable form `⟪x,y⟫_ℂ`.Here `_ℂ` can not be omitted.
```lean
example {x y : U}: inner ℂ x y = ⟪x,y⟫_ℂ := by rfl
```
Standard `⟪x,y⟫_ℂ` in Lean is conjugate linear with respect to the first variable and  linear with respect to the second variable.
```lean
example {x y : U} : 
  ⟪Complex.I•x,y⟫_ℂ = -Complex.I*⟪x,y⟫_ℂ  := by
  rw[inner_smul_left]
  rw[Complex.conj_I]
```
One basic thing about innerproduct space is some identity from the definition of inner product.E.g.$$\begin{align}
||x+y||^2+||x-y||^2=2(||x||^2+||y||^2) \\
\langle x,y\rangle= \frac{1}{4}\sum_{k=1}^4i^{k}||x+i^k y||^2
\end{align}$$
Unluckily there's no automatic tactic for checking those identity.One can combine several things to create a tactic himself.The following is how we do it
```lean
theorem my_nrom_sq {x : U} :
  ‖x‖^2 = ⟪x,x⟫_ℂ := by
  simp only [inner_self_eq_norm_sq_to_K, Complex.coe_algebraMap]

theorem my_change_coe (r : ℝ) (x : U) :r•x= (r:ℂ )• x := by
  rfl

theorem my_inner_conj_symm {x y : U} :
  star ⟪x,y⟫_ℂ =  ⟪y,x⟫_ℂ := by
  exact CStarModule.star_inner x y

theorem my_star {z : ℂ} :
  (starRingEnd ℂ ) z=star z := by
  rfl
```
The trivial theorems above is used to `simp[]` our expression into a unified form.Some of the proofs above are searched by `aesop?`.
Combining them with some Mathlib theorem we get
```lean
 (X) simp only [my_change_coe,my_nrom_sq, inner_add_left, 
  inner_add_right, inner_smul_left, inner_smul_right,Complex.conj_I,
  Complex.conj_ofReal]
  simp only[my_inner_conj_symm,my_star]
  ring_nf
  simp only[Complex.I_sq]
  ring
```
One can apply this,with some modification,to give proofs of innerprodect identities.

We can check some identity using the above combined tactic.
```
example {x y : U} : 
  ‖x+y‖^2 + ‖x - y‖^2 = 2*(‖x‖^2 + (‖y‖)^2) := by
  have h : (‖x+y‖^2 + ‖x - y‖^2) = 2*(‖x‖^2 + (‖y‖:ℂ)^2) :=by
    simp only [my_nrom_sq, inner_add_left, 
    inner_add_right, inner_sub_right, 
    inner_sub_left,]
    ring 
  exact_mod_cast h
```
Here `exact_mod_cast` is a tactic AI telling me to get an real identify from the complex version of it.
```
example {x y : U} : 
  ⟪x,y⟫_ℂ = 1/4*(‖x+y‖^2 - ‖x - y‖^2 
  + Complex.I*(-‖x+Complex.I•y‖^2 + ‖x - Complex.I•y‖^2))
   := by
  simp only [my_nrom_sq, inner_add_left, 
  inner_add_right, inner_smul_left, inner_smul_right,
  inner_sub_left, inner_sub_right
  ,Complex.conj_I]
  ring_nf
  simp only[Complex.I_sq]
  ring
```


### Not yet formalized / TODO

* The spectral theorem for compact self-adjoint operators on infinite-dimensional Hilbert spaces.
* The theory of reproducing kernel Hilbert spaces (RKHS).
* More advanced results on frames and Riesz bases.
* The connection between inner product spaces and Clifford algebras.
* Many concrete examples of orthogonal polynomials (Legendre, Hermite, etc.) as orthonormal families in `L²` spaces.