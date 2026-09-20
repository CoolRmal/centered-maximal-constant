/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.FracRepresentation

/-!
# The moment hypothesis for the truncated diamond base

`CenteredMaximal.Fractional.jumpMoment_fracKernel` reduces the moment hypothesis
`JumpMoment (6/5) fracKernel` to the same hypothesis for the truncated diamond base
`truncBase (6/5) (7/4)`. This file discharges it.

## Main results

* `jumpMoment_truncBase_of_lt`: `JumpMoment α (truncBase α R)` for `1 < α < 3/2` and `0 < R`;
* `jumpMoment_truncBase`: the `α = 6/5`, `R = 7/4` instance;
* `jumpMoment_fracKernel'`, `hKgen_fracKernel'`, `integrable_fracDensity_mul_min_one'`: the
  hypothesis-free forms of the three consequences isolated by `FracRepresentation`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Cauchy

open scoped ENNReal

namespace CenteredMaximal.Fractional

/-! ### Elementary lower integrals of powers -/

/-- `∫₀^c v^p dv = c^{p+1}/(p+1)` as a lower integral, for `−1 < p`. -/
private theorem lintegral_Ioc_rpow {p c : ℝ} (hp : -1 < p) (hc : 0 ≤ c) :
    ∫⁻ v in Ioc 0 c, ENNReal.ofReal (v ^ p) = ENNReal.ofReal (c ^ (p + 1) / (p + 1)) := by
  have hint : IntegrableOn (fun v : ℝ => v ^ p) (Ioc 0 c) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hc).1
      (intervalIntegral.intervalIntegrable_rpow' hp)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) c)] fun v : ℝ => v ^ p :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun v hv => Real.rpow_nonneg hv.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le hc, integral_rpow (Or.inl hp),
    Real.zero_rpow (by linarith), sub_zero]

/-- `∫_c^∞ v^p dv = −c^{p+1}/(p+1)` as a lower integral, for `p < −1` and `0 < c`. -/
private theorem lintegral_Ioi_rpow {p c : ℝ} (hp : p < -1) (hc : 0 < c) :
    ∫⁻ v in Ioi c, ENNReal.ofReal (v ^ p) = ENNReal.ofReal (-c ^ (p + 1) / (p + 1)) := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi c)] fun v : ℝ => v ^ p :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun v hv => Real.rpow_nonneg (hc.trans hv).le _
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hp hc) hnn,
    integral_Ioi_rpow_of_lt hp hc]

/-- Translating the half-line: `∫₀^∞ g(m + v) dv = ∫_m^∞ g(t) dt`. -/
private theorem lintegral_Ioi_comp_add (g : ℝ → ℝ≥0∞) (m : ℝ) :
    ∫⁻ v in Ioi 0, g (m + v) = ∫⁻ t in Ioi m, g t := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_add_left_eq_self (fun t => (Ioi m).indicator g t) m]
  refine lintegral_congr fun v => ?_
  simp [indicator_apply]

/-- `∫₀^∞ (v + m)^p dv = −m^{p+1}/(p+1)` for `p < −1` and `0 < m`. -/
private theorem lintegral_Ioi_zero_add_rpow {p m : ℝ} (hp : p < -1) (hm : 0 < m) :
    ∫⁻ v in Ioi 0, ENNReal.ofReal ((v + m) ^ p) = ENNReal.ofReal (-m ^ (p + 1) / (p + 1)) := by
  calc ∫⁻ v in Ioi 0, ENNReal.ofReal ((v + m) ^ p)
      = ∫⁻ t in Ioi m, ENNReal.ofReal (t ^ p) := by
        rw [← lintegral_Ioi_comp_add (fun t : ℝ => ENNReal.ofReal (t ^ p)) m]
        exact lintegral_congr fun v => by rw [add_comm]
    _ = _ := lintegral_Ioi_rpow hp hm

/-! ### Reduction of a plane integral to an iterated integral -/

/-- A function of `|x|` integrates to twice its integral over the positive half-line. -/
private theorem lintegral_comp_abs (h : ℝ → ℝ≥0∞) :
    ∫⁻ x, h |x| = 2 * ∫⁻ x in Ioi 0, h x := by
  rw [← lintegral_add_compl (fun x => h |x|) measurableSet_Ioi, compl_Ioi, two_mul]
  congr 1
  · exact setLIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [abs_of_pos hx]
  · calc ∫⁻ x in Iic 0, h |x| = ∫⁻ x, (Iic 0).indicator (fun x => h |x|) (-x) := by
          rw [lintegral_neg_eq_self ((Iic 0).indicator fun x => h |x|),
            lintegral_indicator measurableSet_Iic]
      _ = ∫⁻ x in Ici 0, h x := by
          rw [← lintegral_indicator measurableSet_Ici]
          refine lintegral_congr fun x => ?_
          by_cases hx : 0 ≤ x
          · simp [hx, abs_of_nonneg hx]
          · simp [hx]
      _ = ∫⁻ x in Ioi 0, h x := (setLIntegral_congr Ioi_ae_eq_Ici).symm

/-- A plane lower integral is the iterated lower integral of the two coordinates. -/
private theorem lintegral_finTwoArrow (f : ℝ → ℝ → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) :
    ∫⁻ z : Fin 2 → ℝ, f (z 0) (z 1) = ∫⁻ u, ∫⁻ v, f u v := by
  have h1 : (∫⁻ z : Fin 2 → ℝ, f (z 0) (z 1)) = ∫⁻ p : ℝ × ℝ, f p.1 p.2 := by
    rw [← (volume_preserving_finTwoArrow ℝ).map_eq, lintegral_map_equiv]
    rfl
  rw [h1]
  exact lintegral_prod _ hf.aemeasurable

/-- Tonelli on the open quadrant. -/
private theorem lintegral_Ioi_swap (f : ℝ → ℝ → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) :
    (∫⁻ a in Ioi 0, ∫⁻ b in Ioi 0, f a b) = ∫⁻ b in Ioi 0, ∫⁻ a in Ioi 0, f a b :=
  lintegral_lintegral_swap hf.aemeasurable

/-- **The plane integral of a function of the two absolute coordinates.** -/
private theorem lintegral_abs_pair (f : ℝ → ℝ → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (j : Fin 2) :
    ∫⁻ z : Fin 2 → ℝ, f |z j| |z (j + 1)| = 4 * ∫⁻ a in Ioi 0, ∫⁻ b in Ioi 0, f a b := by
  have key : ∀ g : ℝ → ℝ → ℝ≥0∞, Measurable (Function.uncurry g) →
      (∫⁻ z : Fin 2 → ℝ, g |z 0| |z 1|) = 4 * ∫⁻ a in Ioi 0, ∫⁻ b in Ioi 0, g a b := by
    intro g hg
    have h1 : (∫⁻ z : Fin 2 → ℝ, g |z 0| |z 1|) = ∫⁻ u, ∫⁻ v, g |u| |v| :=
      lintegral_finTwoArrow (fun u v => g |u| |v|)
        (hg.comp ((continuous_abs.comp continuous_fst).prodMk
          (continuous_abs.comp continuous_snd)).measurable)
    have h2 : ∀ u : ℝ, (∫⁻ v, g |u| |v|) = 2 * ∫⁻ v in Ioi 0, g |u| v := fun u =>
      lintegral_comp_abs fun v => g |u| v
    have h3 : (∫⁻ u, (fun w : ℝ => ∫⁻ v in Ioi 0, g w v) |u|)
        = 2 * ∫⁻ u in Ioi 0, ∫⁻ v in Ioi 0, g u v :=
      lintegral_comp_abs fun w => ∫⁻ v in Ioi 0, g w v
    rw [h1, lintegral_congr h2, lintegral_const_mul' 2 _ (by simp), h3]
    ring
  fin_cases j
  · simpa using key f hf
  · have hswap := lintegral_Ioi_swap f hf
    have := key (fun a b => f b a) (hf.comp measurable_swap)
    simpa [← hswap] using this

end CenteredMaximal.Fractional

end

end
