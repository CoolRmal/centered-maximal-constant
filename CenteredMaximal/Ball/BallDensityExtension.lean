/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.BallPenaltyLimit

/-!
# Extending local obstacle densities to the whole space

The penalized obstacle produces an `L²` density on a ball. The maximal-function certificate
uses a whole-space `ℝ≥0∞` density. Extension by zero preserves the almost-everywhere cap,
while a local contact-mass bound passes to the whole space.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped ENNReal

namespace CenteredMaximal.Ball

/-- Extend a real density by zero and view it as an extended nonnegative density. -/
def extendRestrictedDensity {X : Type*} [MeasurableSpace X]
    (s : Set X) (g : X → ℝ) : X → ℝ≥0∞ :=
  by
    classical
    exact fun x => if x ∈ s then ENNReal.ofReal (g x) else 0

/-- An almost-everywhere cap on a restricted measure passes to extension by zero. -/
theorem ae_extendRestrictedDensity_le_ofReal
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Set X) (hs : MeasurableSet s) (g : X → ℝ) (κ : ℝ)
    (hcap : ∀ᵐ x ∂(μ.restrict s), g x ≤ κ) :
    ∀ᵐ x ∂μ, extendRestrictedDensity s g x ≤ ENNReal.ofReal κ := by
  classical
  have hcap' : ∀ᵐ x ∂μ, x ∈ s → g x ≤ κ := (ae_restrict_iff' hs).mp hcap
  filter_upwards [hcap'] with x hx
  by_cases hxs : x ∈ s
  · simpa only [extendRestrictedDensity, if_pos hxs] using
      ENNReal.ofReal_le_ofReal (hx hxs)
  · simp [extendRestrictedDensity, hxs]

/-- Integrating a kernel against the zero extension is the same as integrating the local
density over its domain. -/
theorem lintegral_mul_extendRestrictedDensity
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Set X) (hs : MeasurableSet s) (g : X → ℝ)
    (W : X → ℝ≥0∞) :
    (∫⁻ x, W x * extendRestrictedDensity s g x ∂μ) =
      ∫⁻ x in s, W x * ENNReal.ofReal (g x) ∂μ := by
  classical
  rw [← lintegral_indicator hs]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp [extendRestrictedDensity, Set.indicator, hx]
  · simp [extendRestrictedDensity, Set.indicator, hx]

/-- Restricted contact mass and source mass give the whole-space contact bound. -/
theorem global_contact_bound_of_restricted
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Set X) (hs : MeasurableSet s) (u : X → ℝ)
    (f : X → ℝ≥0∞) (κ : ℝ≥0∞)
    (hlocal : κ * (μ.restrict s) {x | 0 < u x} ≤ ∫⁻ x in s, f x ∂μ) :
    κ * μ {x | x ∈ s ∧ 0 < u x} ≤ ∫⁻ x, f x ∂μ := by
  have hm : μ {x | x ∈ s ∧ 0 < u x} = (μ.restrict s) {x | 0 < u x} := by
    rw [Measure.restrict_apply' hs]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [hm]
  exact hlocal.trans (lintegral_mono' Measure.restrict_le_self le_rfl)

namespace DirichletSobolev

variable {n : ℕ}

/-- The weak `L²` cap on a ball becomes an almost-everywhere whole-space cap. -/
theorem ae_ballDensityExtension_le_cap
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (ν : L2D (ball center R)) (κ : ℝ)
    (hν : ν ≤ κ • ballUnitL2 center R) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      extendRestrictedDensity (ball center R) ν x ≤ ENNReal.ofReal κ := by
  have hlocal : ∀ᵐ x ∂(volume.restrict (ball center R)), (ν x : ℝ) ≤ κ := by
    filter_upwards [(Lp.coeFn_le ν (κ • ballUnitL2 center R)).2 hν,
      Lp.coeFn_smul κ (ballUnitL2 center R), ballUnitL2_coeFn center R]
      with x hx hsmul hunit
    simpa only [hsmul, Pi.smul_apply, smul_eq_mul, hunit, mul_one] using hx
  exact ae_extendRestrictedDensity_le_ofReal volume (ball center R) measurableSet_ball ν κ hlocal

end DirichletSobolev

end CenteredMaximal.Ball
