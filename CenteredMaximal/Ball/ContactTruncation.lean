/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.DirectCertificate

/-!
# Contact-set estimates from obstacle truncations

A bound on each positive superlevel set passes to the full positivity set by continuity
of measure from below. This is the measure-theoretic final step in the obstacle
truncation argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace CenteredMaximal.Ball

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- Uniform bounds for every positive superlevel set imply the same bound for the
positivity set. -/
theorem contact_measure_le_of_superlevel_bounds
    (u : α → ℝ) (κ M : ℝ≥0∞)
    (h : ∀ t : ℝ, 0 < t → κ * μ {x | t ≤ u x} ≤ M) :
    κ * μ {x | 0 < u x} ≤ M := by
  let s : ℕ → Set α := fun n ↦ {x | (1 / (n + 1 : ℝ)) ≤ u x}
  have hs : Monotone s := by
    intro i j hij x hx
    exact (one_div_le_one_div_of_le
      (show (0 : ℝ) < (i + 1 : ℝ) by positivity)
      (show (i + 1 : ℝ) ≤ (j + 1 : ℝ) by exact_mod_cast Nat.add_le_add_right hij 1)).trans hx
  have hunion : (⋃ n, s n) = {x | 0 < u x} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    change (∃ n : ℕ, (1 / (n + 1 : ℝ)) ≤ u x) ↔ 0 < u x
    constructor
    · rintro ⟨n, hn⟩
      exact (show 0 < (1 / (n + 1 : ℝ)) by positivity).trans_le hn
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact ⟨n, le_of_lt hn⟩
  calc
    κ * μ {x | 0 < u x} = κ * μ (⋃ n, s n) := by rw [hunion]
    _ = κ * (⨆ n, μ (s n)) := by rw [hs.measure_iUnion]
    _ = ⨆ n, κ * μ (s n) := ENNReal.mul_iSup κ (fun n ↦ μ (s n))
    _ ≤ M := iSup_le fun n ↦ h _ (by positivity)

/-- A variational inequality tested with every upper truncation of a nonnegative
obstacle controls the measure of its positivity set. -/
theorem contact_measure_le_of_truncation_integrals [IsFiniteMeasure μ]
    (u : α → ℝ) (κ M : ℝ) (hκ : 0 ≤ κ) (hu : Measurable u)
    (hu₀ : ∀ x, 0 ≤ u x)
    (htrunc : ∀ t : ℝ, 0 < t →
      κ * ∫ x, min (u x) t ∂μ ≤ t * M) :
    ENNReal.ofReal κ * μ {x | 0 < u x} ≤ ENNReal.ofReal M := by
  apply contact_measure_le_of_superlevel_bounds μ u _ _
  intro t ht
  let A : Set α := {x | t ≤ u x}
  have hA : MeasurableSet A := measurableSet_le measurable_const hu
  have hmin : Integrable (fun x ↦ min (u x) t) μ := by
    apply Integrable.of_bound (hu.min measurable_const).aestronglyMeasurable t
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hu₀ x) ht.le)]
    exact min_le_right _ _
  have hind : Integrable (A.indicator fun _ ↦ t) μ :=
    (integrable_const t).indicator hA
  have hle : (∫ x, A.indicator (fun _ ↦ t) x ∂μ) ≤
      ∫ x, min (u x) t ∂μ := by
    apply integral_mono hind hmin
    intro x
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
      exact (le_min_iff).2 ⟨hx, le_rfl⟩
    · simp only [Set.indicator_of_notMem hx]
      exact le_min (hu₀ x) ht.le
  have hreal : κ * μ.real A ≤ M := by
    have hscaled : t * (κ * μ.real A) ≤ t * M := by
      calc
        t * (κ * μ.real A) = κ * (μ.real A * t) := by ring
        _ = κ * (∫ x, A.indicator (fun _ ↦ t) x ∂μ) := by
          rw [integral_indicator_const t hA, smul_eq_mul]
        _ ≤ κ * ∫ x, min (u x) t ∂μ := mul_le_mul_of_nonneg_left hle hκ
        _ ≤ t * M := htrunc t ht
    nlinarith
  have hconv : ENNReal.ofReal κ * μ A = ENNReal.ofReal (κ * μ.real A) := by
    rw [← ofReal_measureReal (μ := μ) (s := A), ENNReal.ofReal_mul hκ]
  exact hconv.trans_le (ENNReal.ofReal_le_ofReal hreal)

/-- The truncation variational inequality with nonnegative source data gives the
direct contact-set mass bound. -/
theorem contact_measure_le_of_variational_truncations [IsFiniteMeasure μ]
    (u f : α → ℝ) (κ : ℝ) (hκ : 0 ≤ κ) (hu : Measurable u)
    (hu₀ : ∀ x, 0 ≤ u x) (hf : Integrable f μ) (hf₀ : ∀ x, 0 ≤ f x)
    (hvariation : ∀ t : ℝ, 0 < t →
      κ * ∫ x, min (u x) t ∂μ ≤ ∫ x, f x * min (u x) t ∂μ) :
    ENNReal.ofReal κ * μ {x | 0 < u x} ≤ ENNReal.ofReal (∫ x, f x ∂μ) := by
  apply contact_measure_le_of_truncation_integrals μ u κ _ hκ hu hu₀
  intro t ht
  calc
    κ * ∫ x, min (u x) t ∂μ ≤ ∫ x, f x * min (u x) t ∂μ := hvariation t ht
    _ ≤ ∫ x, f x * t ∂μ := by
      apply integral_mono_of_nonneg
      · filter_upwards [] with x
        exact mul_nonneg (hf₀ x) (le_min (hu₀ x) ht.le)
      · exact hf.mul_const t
      · filter_upwards [] with x
        exact mul_le_mul_of_nonneg_left (min_le_right _ _) (hf₀ x)
    _ = t * ∫ x, f x ∂μ := by rw [integral_mul_const]; ring

/-- The form of the contact-set estimate used by ball obstacle certificates. -/
theorem contact_measure_le_lintegral_of_variational_truncations [IsFiniteMeasure μ]
    (u f : α → ℝ) (κ : ℝ≥0∞) (hκtop : κ ≠ ∞) (hu : Measurable u)
    (hu₀ : ∀ x, 0 ≤ u x) (hf : Integrable f μ) (hf₀ : ∀ x, 0 ≤ f x)
    (hvariation : ∀ t : ℝ, 0 < t →
      κ.toReal * ∫ x, min (u x) t ∂μ ≤ ∫ x, f x * min (u x) t ∂μ) :
    κ * μ {x | 0 < u x} ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := by
  have h := contact_measure_le_of_variational_truncations μ u f κ.toReal
    ENNReal.toReal_nonneg hu hu₀ hf hf₀ hvariation
  rw [ENNReal.ofReal_toReal hκtop] at h
  convert h using 1
  rw [← ofReal_integral_norm_eq_lintegral_enorm hf]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  exact (Real.norm_eq_abs (f x)).trans (abs_of_nonneg (hf₀ x))

end CenteredMaximal.Ball
