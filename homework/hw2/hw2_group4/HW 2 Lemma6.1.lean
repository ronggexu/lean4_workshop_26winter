import Mathlib
open Algebra Function

/--褚天澄：6.1
张博山：6.2
程俊尧：6.9
张杰涵：6.10 6.5 6.6
-/

/-- A commutative ring which is of finite type over a Noetherian base ring is itself Noetherian. -/
theorem isNoetherian_of_finiteType (R A : Type*) [CommRing R] [CommRing A]
    [Algebra R A] (hR : IsNoetherianRing R) (hA : Algebra.FiniteType R A) :
    IsNoetherianRing A := by
  -- Use the definition of finite type: there exists a finite set of generators s
  obtain ⟨s, hs⟩ := hA
  -- Construct the evaluation map from polynomials on s to A
  let f : MvPolynomial s R →ₐ[R] A := MvPolynomial.aeval (fun x : s => (x : A))
  -- Show that this map is surjective
  have hf : Surjective f := by
    rw [← AlgHom.range_eq_top, ← hs, ← Algebra.adjoin_range_eq_range_aeval]
    -- Identify Set.range of the subtype inclusion with the underlying set ↑s.
    have hrange : Set.range (fun x : (↥s) => (↑x : A)) = (↑s : Set A) := by
      ext a; constructor
      · rintro ⟨x, rfl⟩; exact x.property
      · intro ha; exact ⟨⟨a, ha⟩, rfl⟩
    rw [hrange]
  -- Hilbert's Basis Theorem: MvPolynomial on a finite type over a Noetherian ring is Noetherian
  haveI : IsNoetherianRing (MvPolynomial s R) := by
    exact MvPolynomial.isNoetherianRing (σ := s) (R := R)
  -- The homomorphic image of a Noetherian ring is Noetherian
  exact isNoetherianRing_of_surjective (MvPolynomial s R) A f.toRingHom hf

/-- A localization of a Noetherian commutative ring is again Noetherian. -/
theorem isNoetherian_of_localization (R : Type*) [CommRing R]
    (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]
    (hR : IsNoetherianRing R) :
    IsNoetherianRing S := by
  -- Apply the standard theorem: Localization of a Noetherian ring is Noetherian
  exact IsLocalization.isNoetherianRing M S hR
