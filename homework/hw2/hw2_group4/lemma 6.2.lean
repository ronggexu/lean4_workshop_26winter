import Mathlib

open Classical Ideal PowerSeries Function
open scoped BigOperators

theorem noetherian_powerSeries {R : Type*} [CommRing R] [IsNoetherianRing R] :
    IsNoetherianRing (PowerSeries R) := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I /- 任取R[[x]]的理想I，需证明I有限生成 -/

  let I_d (d : ℕ) : Ideal R :=
    Ideal.span { a : R | ∃ f ∈ I, PowerSeries.coeff d f = a }

  -- 引理：升链关系I_d ⊆ I_{d+1}
  have I_d_mono : Monotone I_d := by
    intro d₁ d₂ (hd : d₁ ≤ d₂)
    rw [SetLike.le_def]
    intro a ha
    unfold I_d at ha  -- 展开I_d的定义：I_d d₁ = span {a | ∃ f ∈ I, PowerSeries.coeff d₁ f = a}
    let S := {a' : R | ∃ f ∈ I, PowerSeries.coeff d₁ f = a'}

    --先证明S就是I_d1
    have S_eq_I_d1 : S = I_d d₁ := by
      have S_is_ideal : Ideal R :=
      {
        carrier := S,
        zero_mem' := by
          use 0
          constructor
          · exact Ideal.zero_mem I
          · trivial
        add_mem' := by
          intro a b ha hb
          cases ha with | intro f hf =>
          cases hb with | intro g hg =>
          use f + g
          constructor
          · exact Ideal.add_mem I hf.1 hg.1  --证明了f+g在I中
          · rw [map_add, hf.2, hg.2]
        smul_mem' := by
          intro r a ha
          cases ha with | intro f hf =>
          let r_ps := PowerSeries.C r
          use r_ps * f
          constructor
          · exact I.mul_mem_left r_ps hf.1
          · rw [mul_comm]
            rw [PowerSeries.coeff_mul_C, hf.2]
            rw [mul_comm]
            trivial
      }
      sorry

    have key : ∃ f ∈ I, PowerSeries.coeff d₁ f = a := by
      let f : R⟦X⟧ := PowerSeries.C a * PowerSeries.X ^ d₁
      have f_mem_I : f ∈ I := by sorry
      have f_coeff : PowerSeries.coeff d₁ f = a := by
        simp [f, PowerSeries.coeff_mul_X_pow, PowerSeries.coeff_C, hd]
      exact ⟨f, f_mem_I, f_coeff⟩

    rcases key with ⟨f, f_mem_I, f_coeff_eq_a⟩

    let k := d₂ - d₁
    let Xk : R⟦X⟧ := PowerSeries.X ^ k
    let g := Xk * f

    have g_mem_I : g ∈ I := by
    --证明f * Xk ∈ I
      have h : f * Xk ∈ I := Ideal.mul_mem_right Xk I f_mem_I
    --乘法交换律，Xk * f = f * Xk → 因此g ∈ I
      rw [mul_comm] at h
      exact h

    have g_coeff_eq_a : PowerSeries.coeff d₂ g = a := by
      sorry

    unfold I_d  -- 展开I_d d₂ = span {a | ∃ f ∈ I, coeff d₂ f = a}
    have a_in_T : a ∈ {a'' : R | ∃ f ∈ I, PowerSeries.coeff d₂ f = a''} := ⟨g, g_mem_I, g_coeff_eq_a⟩

    sorry
  sorry
