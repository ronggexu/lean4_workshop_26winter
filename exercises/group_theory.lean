import Mathlib

open Subgroup

/-
  Let G be a group. Let H be a subgroup of G of index p, where p is a prime.
  Then H is a maximal subgroup of G.
-/
theorem covby_top_of_index_eq_prime {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (h_idx : H.index = p) : CovBy H ⊤ := by
  sorry

/-
  Let G be a p-group. Let H be a maximal subgroup of G.
  Prove that [G : H] = p.

  Hint: Show that H is normal in G.
-/
theorem index_eq_prime_of_covby_top (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] [Fact (IsPGroup p G)]
    {H : Subgroup G} (h_max : CovBy H ⊤) : H.index = p := by
  sorry

