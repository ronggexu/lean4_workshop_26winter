import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Ideal.Operations
def Ideal.IsLocallyNilpotent {R : Type*} [Semiring R] (I : Ideal R) : Prop :=
  ∀ x ∈ I, IsNilpotent x

/-项目协助注释. 所有证明在 https://stacks.math.columbia.edu/tag/0AMF 上可以找到，或者询问 AI.-/

/-lemma 10.32.3-/
lemma Ideal.IsLocallyNilpotent.map {R R' : Type*} [CommRing R] [CommRing R']
  (f : R →+* R') {I : Ideal R} (h : I.IsLocallyNilpotent) :
  (I.map f).IsLocallyNilpotent :=
sorry

/-lemma 10.32.4-/
lemma isUnit_iff_isUnit_quotient {R : Type*} [CommRing R] (I : Ideal R)
    (hI : I.IsLocallyNilpotent) (x : R) :
    IsUnit x ↔ IsUnit ((Ideal.Quotient.mk I) x) := by sorry

/-lemma 10.32.5-/
lemma exists_pow_subset_of_radical_subset {R : Type*} [CommRing R] [IsNoetherian R R]
    (I J : Ideal R) (hJ : J ≤ I.radical) : ∃ n : ℕ, J ^ n ≤ I := by
  sorry

/-corollary-/
lemma Ideal.isLocallyNilpotent_iff_isNilpotent {R : Type*} [CommRing R] [IsNoetherian R R]
    (I : Ideal R) : IsLocallyNilpotent I ↔ IsNilpotent I := by
  sorry

/-lemma 10.32.6-/
/-However, I choose to use def instead of lemma, since the ≃ gives better results you can use-/
def idempotents_equiv_quotient {R : Type*} [CommRing R] (I : Ideal R)
    (hI : I.IsLocallyNilpotent) :
  { e : R // e * e = e } ≃ { e : R ⧸ I // e * e = e } := by
sorry
