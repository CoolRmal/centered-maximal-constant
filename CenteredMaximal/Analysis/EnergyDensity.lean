/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.JumpEnergy
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Density of smooth compactly supported functions in the energy space

A measurable `u : ℝ² → ℝ` in `L¹ ∩ L²` with finite jump energy `E(u) = jumpEnergy α u`,
`0 < α < 2`, is approximated simultaneously in energy, in `L¹` and in `L²` by smooth compactly
supported functions (`exists_contDiff_hasCompactSupport_approx`). The approximant is a
mollification `ρ_δ ⋆ (χ_R u)` of a cutoff of `u`, in two steps.

* **Cutoff.** With the Lipschitz cutoff `χ_R(x) = min 1 (max (2 − ‖x‖ / R) 0)`, the jump of
  `(1 − χ_R) u` along `t e_j` is `(1 − χ_R(x + t e_j)) Δu + u(x) (χ_R(x) − χ_R(x + t e_j))`,
  whose square is dominated by `2 (Δu)² + 2 u(x)² min(t², 1)` for `R ≥ 1`. Since
  `min(t², 1) |t|^{−1−α}` is integrable on the line for `0 < α < 2`, the energy of `(1 − χ_R) u`
  tends to `0` by dominated convergence (`tendsto_jumpEnergy_sub_cutoff_mul`), and so do its
  `L^p` norms (`tendsto_eLpNorm_sub_cutoff_mul`).
* **Mollification.** For a compactly supported `v`, `ρ ⋆ v − v = ∫ ρ(h) (v(· − h) − v) dh` is an
  average of translation errors; by Cauchy–Schwarz and Tonelli, the squared `L²` norm of such an
  average is at most the average of the squared `L²` norms
  (`lintegral_enorm_integral_mul_sq_le`). The same applies to the weighted increments
  `(v(x + t e_j) − v(x)) |t|^{−(1+α)/2}` on `ℝ² × ℝ`, whose squared `L²` norms are the summands of
  the energy (`jumpEnergy_eq_sum_lintegral_enorm_sq`). Continuity of translation in `L^p`
  (`tendsto_eLpNorm_comp_sub_sub`, from the continuity of `Lp.compMeasurePreserving`) then makes
  all three errors small when the bump is supported in a small ball.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Metric Set Topology
open scoped ENNReal Convolution

namespace CenteredMaximal

/-! ### Continuity of translation in `L^p` -/

section Translation

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsAddHaarMeasure]

/-- Continuity of translation in `L^p`, `1 ≤ p < ∞`: `‖f(· − h) − f‖_p → 0` as `h → 0`, from the
joint continuity of `(f, φ) ↦ f ∘ φ` on `Lp × {measure-preserving continuous maps}`. -/
theorem tendsto_eLpNorm_comp_sub_sub {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) {f : G → ℝ}
    (hf : MemLp f p μ) :
    Tendsto (fun h : G => eLpNorm (fun x => f (x - h) - f x) p μ) (𝓝 0) (𝓝 0) := by
  haveI : Fact (1 ≤ p) := ⟨hp⟩
  -- the translations `x ↦ x − h`, as a continuous family of measure-preserving continuous maps
  let τ : G → C(G, G) := fun h => ⟨fun x => x - h, continuous_id.sub continuous_const⟩
  have hτ : Continuous τ :=
    ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.sub continuous_fst)
  have hτm : ∀ h, MeasurePreserving (τ h) μ μ := fun h => measurePreserving_sub_right μ h
  -- the translates of `f`, as a continuous curve in `L^p`
  let F : G → Lp ℝ p μ := fun h => Lp.compMeasurePreserving (τ h) (hτm h) (hf.toLp f)
  have hF : Continuous F := continuous_const.compMeasurePreservingLp hτ hτm hp'
  have hFae : ∀ h, ⇑(F h) =ᵐ[μ] fun x => f (x - h) := fun h =>
    (Lp.coeFn_compMeasurePreserving _ _).trans
      ((hτm h).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp)
  have heq : ∀ h, eLpNorm (fun x => f (x - h) - f x) p μ = eLpNorm (F h - F 0) p μ := fun h => by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (F h) (F 0), hFae h, hFae 0] with x hx hx' hx''
    rw [hx, Pi.sub_apply, hx', hx'', sub_zero]
  have key : Tendsto (fun h => ‖F h - F 0‖) (𝓝 0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hF.tendsto 0)
  simp_rw [heq]
  rw [← ENNReal.tendsto_toReal_iff (fun h => Lp.eLpNorm_ne_top (F h - F 0)) ENNReal.zero_ne_top]
  simpa [Lp.norm_def] using key

end Translation

/-- The squared `L²` norm as a Lebesgue integral. -/
theorem lintegral_enorm_sq {X : Type*} [MeasurableSpace X] {μ : Measure X} (f : X → ℝ) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = eLpNorm f 2 μ ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num [ENNReal.rpow_two]

/-! ### Averaging against a density -/

section Jensen

variable {G X : Type*} [MeasurableSpace G] [MeasurableSpace X] {μ : Measure G} {ν : Measure X}

/-- The Cauchy–Schwarz inequality `(∫ f g)² ≤ (∫ f) (∫ f g²)` for `[0, ∞]`-valued functions. -/
theorem sq_lintegral_mul_le {f g : G → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ∂μ) * ∫⁻ a, f a * g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun a => f a ^ (1 / 2 : ℝ)) (g := fun a => f a ^ (1 / 2 : ℝ) * g a)
    (hf.pow_const _) ((hf.pow_const _).mul hg)
  have e₁ : ∀ a, f a ^ (1 / 2 : ℝ) * (f a ^ (1 / 2 : ℝ) * g a) = f a * g a := fun a => by
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg (1 / 2) (1 / 2) (by norm_num) (by norm_num)]
    norm_num
  have e₂ : ∀ a, (f a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = f a := fun a => by
    rw [← ENNReal.rpow_mul]
    norm_num
  have e₃ : ∀ a, (f a ^ (1 / 2 : ℝ) * g a) ^ (2 : ℝ) = f a * g a ^ 2 := fun a => by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ENNReal.rpow_two]
    norm_num
  simp only [Pi.mul_apply, e₁, e₂, e₃] at h
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, f a * g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' h 2
    _ = _ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

variable [SFinite μ] [SFinite ν]

/-- Averaging a family `W` of functions on `X` against a density `ρ`: the `L¹` norm of the
average is at most the average of the `L¹` norms. -/
theorem lintegral_enorm_integral_mul_le {ρ : G → ℝ} (hρ : Measurable ρ) {W : G → X → ℝ}
    (hW : Measurable (Function.uncurry W)) :
    ∫⁻ x, ‖∫ h, ρ h * W h x ∂μ‖ₑ ∂ν ≤ ∫⁻ h, ‖ρ h‖ₑ * ∫⁻ x, ‖W h x‖ₑ ∂ν ∂μ := by
  calc ∫⁻ x, ‖∫ h, ρ h * W h x ∂μ‖ₑ ∂ν ≤ ∫⁻ x, ∫⁻ h, ‖ρ h‖ₑ * ‖W h x‖ₑ ∂μ ∂ν :=
        lintegral_mono fun x =>
          (enorm_integral_le_lintegral_enorm _).trans_eq (by simp only [enorm_mul])
    _ = ∫⁻ h, ∫⁻ x, ‖ρ h‖ₑ * ‖W h x‖ₑ ∂ν ∂μ :=
        lintegral_lintegral_swap
          ((hρ.enorm.comp measurable_snd).mul (hW.comp measurable_swap).enorm).aemeasurable
    _ = _ := lintegral_congr fun h => lintegral_const_mul' _ _ enorm_ne_top

/-- Averaging against a density `ρ` with `∫ ‖ρ‖ ≤ 1` does not increase the `L²` norm:
`∫ ‖∫ ρ(h) W(h, x) dh‖² dx ≤ ∫ ‖ρ(h)‖ ∫ ‖W(h, x)‖² dx dh`, by Cauchy–Schwarz in `h`. -/
theorem lintegral_enorm_integral_mul_sq_le {ρ : G → ℝ} (hρ : Measurable ρ)
    (hρ₁ : ∫⁻ h, ‖ρ h‖ₑ ∂μ ≤ 1) {W : G → X → ℝ} (hW : Measurable (Function.uncurry W)) :
    ∫⁻ x, ‖∫ h, ρ h * W h x ∂μ‖ₑ ^ 2 ∂ν ≤ ∫⁻ h, ‖ρ h‖ₑ * ∫⁻ x, ‖W h x‖ₑ ^ 2 ∂ν ∂μ := by
  calc ∫⁻ x, ‖∫ h, ρ h * W h x ∂μ‖ₑ ^ 2 ∂ν ≤ ∫⁻ x, ∫⁻ h, ‖ρ h‖ₑ * ‖W h x‖ₑ ^ 2 ∂μ ∂ν := by
        refine lintegral_mono fun x => ?_
        calc ‖∫ h, ρ h * W h x ∂μ‖ₑ ^ 2 ≤ (∫⁻ h, ‖ρ h‖ₑ * ‖W h x‖ₑ ∂μ) ^ 2 :=
              pow_le_pow_left' ((enorm_integral_le_lintegral_enorm _).trans_eq
                (by simp only [enorm_mul])) 2
          _ ≤ (∫⁻ h, ‖ρ h‖ₑ ∂μ) * ∫⁻ h, ‖ρ h‖ₑ * ‖W h x‖ₑ ^ 2 ∂μ :=
              sq_lintegral_mul_le hρ.enorm.aemeasurable
                (hW.comp (measurable_id.prodMk measurable_const)).enorm.aemeasurable
          _ ≤ 1 * ∫⁻ h, ‖ρ h‖ₑ * ‖W h x‖ₑ ^ 2 ∂μ := mul_le_mul_left hρ₁ _
          _ = _ := one_mul _
    _ = ∫⁻ h, ∫⁻ x, ‖ρ h‖ₑ * ‖W h x‖ₑ ^ 2 ∂ν ∂μ := by
        refine lintegral_lintegral_swap ?_
        exact ((hρ.enorm.comp measurable_snd).mul
          ((hW.comp measurable_swap).enorm.pow_const 2)).aemeasurable
    _ = _ := lintegral_congr fun h => lintegral_const_mul' _ _ enorm_ne_top

end Jensen

/-! ### The one-dimensional kernel `min(t², 1) |t|^{−(1+α)}` -/

/-- For `0 < α < 2` the kernel `min(t², 1) |t|^{−(1+α)}` is integrable on the line: it is
`|t|^{1−α}` near `0` and `|t|^{−(1+α)}` at infinity. -/
theorem lintegral_min_sq_one_mul_rpow_lt_top {α : ℝ} (hα : 0 < α) (hα' : α < 2) :
    ∫⁻ t : ℝ, ENNReal.ofReal (min (t ^ 2) 1 * |t| ^ (-(1 + α))) < ⊤ := by
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (min (t ^ 2) 1 * |t| ^ (-(1 + α))) with hF
  have hFeven : ∀ t, F (-t) = F t := fun t => by simp [hF]
  -- near the origin the kernel is `t^{1−α}`, integrable since `α < 2`
  have h₁ : ∫⁻ t in Icc (0 : ℝ) 1, F t < ⊤ := by
    have hint : IntegrableOn (fun t : ℝ => t ^ (1 - α)) (Icc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    refine (setLIntegral_mono (measurable_id.pow_const _).enorm fun t ht => ?_).trans_lt
      hint.hasFiniteIntegral
    rcases eq_or_lt_of_le ht.1 with rfl | ht0
    · simp [hF]
    · have : F t = ENNReal.ofReal (t ^ (1 - α)) := by
        simp only [hF]
        rw [min_eq_left (by nlinarith [ht.2] : t ^ 2 ≤ 1), abs_of_pos ht0,
          ← Real.rpow_natCast, ← Real.rpow_add ht0]
        congr 2
        push_cast
        ring
      rw [this, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  -- at infinity the kernel is `t^{−(1+α)}`, integrable since `α > 0`
  have h₂ : ∫⁻ t in Ioi (1 : ℝ), F t < ⊤ := by
    have hint : IntegrableOn (fun t : ℝ => t ^ (-(1 + α))) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine (setLIntegral_mono (measurable_id.pow_const _).enorm fun t ht => ?_).trans_lt
      hint.hasFiniteIntegral
    have ht : 1 < t := ht
    have : F t = ENNReal.ofReal (t ^ (-(1 + α))) := by
      simp only [hF]
      rw [min_eq_right (by nlinarith : 1 ≤ t ^ 2), abs_of_pos (by linarith), one_mul]
    rw [this, Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hIci : ∫⁻ t in Ici (0 : ℝ), F t < ⊤ := by
    calc ∫⁻ t in Ici (0 : ℝ), F t ≤ ∫⁻ t in Icc (0 : ℝ) 1 ∪ Ioi 1, F t :=
          lintegral_mono_set fun t ht => (le_or_gt t 1).elim (fun h => Or.inl ⟨ht, h⟩) Or.inr
      _ ≤ (∫⁻ t in Icc (0 : ℝ) 1, F t) + ∫⁻ t in Ioi 1, F t := lintegral_union_le _ _ _
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨h₁, h₂⟩
  -- the kernel is even, so the negative half line contributes the same amount
  have hIic : ∫⁻ t in Iic (0 : ℝ), F t = ∫⁻ t in Ici (0 : ℝ), F t := by
    rw [← lintegral_indicator measurableSet_Iic, ← lintegral_indicator measurableSet_Ici,
      ← lintegral_neg_eq_self ((Iic (0 : ℝ)).indicator F)]
    refine lintegral_congr fun t => ?_
    by_cases ht : 0 ≤ t
    · rw [indicator_of_mem (by simpa using ht : -t ∈ Iic (0 : ℝ)),
        indicator_of_mem (mem_Ici.2 ht), hFeven]
    · rw [indicator_of_notMem (by simpa using ht : -t ∉ Iic (0 : ℝ)),
        indicator_of_notMem (by simpa using ht : t ∉ Ici (0 : ℝ))]
  calc ∫⁻ t, F t = (∫⁻ t in Iic (0 : ℝ), F t) + ∫⁻ t in (Iic (0 : ℝ))ᶜ, F t :=
        (lintegral_add_compl F measurableSet_Iic).symm
    _ ≤ (∫⁻ t in Ici (0 : ℝ), F t) + ∫⁻ t in Ici (0 : ℝ), F t := by
        rw [hIic, compl_Iic]
        exact add_le_add le_rfl (lintegral_mono_set Ioi_subset_Ici_self)
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hIci, hIci⟩

/-! ### The Lipschitz cutoff -/

/-- The cutoff `χ_R(x) = min 1 (max (2 − ‖x‖ / R) 0)`: it is `1` on the ball of radius `R`,
vanishes outside the ball of radius `2R`, takes values in `[0, 1]` and is `R⁻¹`-Lipschitz. -/
def cutoff (R : ℝ) (x : Fin 2 → ℝ) : ℝ := min 1 (max (2 - ‖x‖ / R) 0)

/-- The cutoff is nonnegative. -/
theorem cutoff_nonneg (R : ℝ) (x : Fin 2 → ℝ) : 0 ≤ cutoff R x :=
  le_min zero_le_one (le_max_right _ _)

/-- The cutoff is at most `1`. -/
theorem cutoff_le_one (R : ℝ) (x : Fin 2 → ℝ) : cutoff R x ≤ 1 := min_le_left _ _

/-- The cutoff is `1` on the ball of radius `R`. -/
theorem cutoff_eq_one {R : ℝ} (hR : 0 < R) {x : Fin 2 → ℝ} (hx : ‖x‖ ≤ R) : cutoff R x = 1 :=
  min_eq_left (le_max_of_le_left (by linarith [(div_le_one hR).2 hx]))

/-- The cutoff vanishes outside the ball of radius `2R`. -/
theorem cutoff_eq_zero {R : ℝ} (hR : 0 < R) {x : Fin 2 → ℝ} (hx : 2 * R ≤ ‖x‖) :
    cutoff R x = 0 := by
  unfold cutoff
  rw [max_eq_right (by rw [sub_nonpos, le_div_iff₀ hR]; linarith), min_eq_right zero_le_one]

/-- The cutoff is `R⁻¹`-Lipschitz. -/
theorem abs_cutoff_sub_cutoff_le {R : ℝ} (hR : 0 < R) (x y : Fin 2 → ℝ) :
    |cutoff R x - cutoff R y| ≤ ‖x - y‖ / R := by
  unfold cutoff
  calc |min 1 (max (2 - ‖x‖ / R) 0) - min 1 (max (2 - ‖y‖ / R) 0)|
      ≤ max |1 - 1| |max (2 - ‖x‖ / R) 0 - max (2 - ‖y‖ / R) 0| :=
        abs_min_sub_min_le_max _ _ _ _
    _ ≤ |2 - ‖x‖ / R - (2 - ‖y‖ / R)| := by
        rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
        exact abs_max_sub_max_le_abs _ _ _
    _ = |‖y‖ - ‖x‖| / R := by
        rw [show 2 - ‖x‖ / R - (2 - ‖y‖ / R) = (‖y‖ - ‖x‖) / R by ring, abs_div, abs_of_pos hR]
    _ ≤ ‖x - y‖ / R := by
        rw [norm_sub_rev]
        exact div_le_div_of_nonneg_right (abs_norm_sub_norm_le _ _) hR.le

/-- Increments of the cutoff are at most `1`. -/
theorem abs_cutoff_sub_cutoff_le_one (R : ℝ) (x y : Fin 2 → ℝ) :
    |cutoff R x - cutoff R y| ≤ 1 :=
  abs_sub_le_iff.2 ⟨by linarith [cutoff_le_one R x, cutoff_nonneg R y],
    by linarith [cutoff_le_one R y, cutoff_nonneg R x]⟩

/-- For `R ≥ 1` the squared increment of `χ_R` along `t e_j` is at most `min(t², 1)`. -/
theorem sq_cutoff_sub_cutoff_le {R : ℝ} (hR : 1 ≤ R) (x : Fin 2 → ℝ) (t : ℝ) (j : Fin 2) :
    (cutoff R x - cutoff R (x + t • Pi.single j 1)) ^ 2 ≤ min (t ^ 2) 1 := by
  have h₁ : |cutoff R x - cutoff R (x + t • Pi.single j 1)| ≤ |t| := by
    refine (abs_cutoff_sub_cutoff_le (by linarith) _ _).trans ?_
    rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, Pi.norm_single, norm_one,
      mul_one]
    exact div_le_self (abs_nonneg _) hR
  rw [← sq_abs]
  refine le_min ?_ ?_
  · rw [← sq_abs t]
    exact pow_le_pow_left₀ (abs_nonneg _) h₁ 2
  · exact pow_le_one₀ (abs_nonneg _) (abs_cutoff_sub_cutoff_le_one R _ _)

/-- The cutoff is continuous. -/
theorem continuous_cutoff (R : ℝ) : Continuous (cutoff R) :=
  continuous_const.min ((continuous_const.sub (continuous_norm.div_const R)).max continuous_const)

/-- The cutoff is measurable. -/
theorem measurable_cutoff (R : ℝ) : Measurable (cutoff R) := (continuous_cutoff R).measurable

/-- The cutoff has compact support. -/
theorem hasCompactSupport_cutoff {R : ℝ} (hR : 0 < R) : HasCompactSupport (cutoff R) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Fin 2 → ℝ) (2 * R)) fun _ hx =>
    cutoff_eq_zero hR (le_of_not_ge fun h => hx (mem_closedBall_zero_iff.2 h))

/-! ### Convergence of the cutoff -/

/-- `L^p` convergence of the cutoff: `‖u − χ_R u‖_p → 0` as `R → ∞`, by dominated convergence. -/
theorem tendsto_eLpNorm_sub_cutoff_mul {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤)
    {u : (Fin 2 → ℝ) → ℝ} (hu : Measurable u) (hu' : MemLp u p volume) :
    Tendsto (fun R : ℝ => eLpNorm (fun x => u x - cutoff R x * u x) p volume) atTop (𝓝 0) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp']
  have key : Tendsto (fun R : ℝ => ∫⁻ x, ‖u x - cutoff R x * u x‖ₑ ^ p.toReal) atTop (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence (μ := volume) (l := atTop)
      (F := fun R x => ‖u x - cutoff R x * u x‖ₑ ^ p.toReal) (f := fun _ => 0)
      (fun x => ‖u x‖ₑ ^ p.toReal) ?_ ?_ ?_ ?_
    · simpa using h
    · exact Eventually.of_forall fun R =>
        (hu.sub ((measurable_cutoff R).mul hu)).enorm.pow_const _
    · refine Eventually.of_forall fun R => Eventually.of_forall fun x => ?_
      refine ENNReal.rpow_le_rpow ?_ hp0.le
      rw [show u x - cutoff R x * u x = (1 - cutoff R x) * u x by ring, enorm_mul]
      refine mul_le_of_le_one_left' ?_
      rw [Real.enorm_eq_ofReal (by linarith [cutoff_le_one R x]), ENNReal.ofReal_le_one]
      linarith [cutoff_nonneg R x]
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp hp' hu'.2).ne
    · refine Eventually.of_forall fun x => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ‖x‖, eventually_ge_atTop 1] with R hR hR1
      rw [cutoff_eq_one (by linarith) hR, one_mul, sub_self, enorm_zero,
        ENNReal.zero_rpow_of_pos hp0]
  have := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0 |>.comp key
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.2 hp0)] using this

/-- Energy convergence of the cutoff: `E((1 − χ_R) u) → 0` as `R → ∞`. The jump of
`(1 − χ_R) u` along `t e_j` is `(1 − χ_R(x + t e_j)) Δu + u(x) (χ_R(x) − χ_R(x + t e_j))`, so for
`R ≥ 1` the integrand is dominated by `2 (Δu)² |t|^{−1−α} + 2 u(x)² min(t², 1) |t|^{−1−α}`, which
is integrable, and it vanishes for large `R`; dominated convergence applies. -/
theorem tendsto_jumpEnergy_sub_cutoff_mul {α : ℝ} (hα : 0 < α) (hα' : α < 2)
    {u : (Fin 2 → ℝ) → ℝ} (hu : Measurable u) (hu₂ : MemLp u 2 volume)
    (hE : jumpEnergy α u ≠ ⊤) :
    Tendsto (fun R : ℝ => jumpEnergy α (fun x => u x - cutoff R x * u x)) atTop (𝓝 0) := by
  have hu_sq : ∫⁻ x, ENNReal.ofReal (u x ^ 2) < ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hu₂.2
    refine lt_of_eq_of_lt (lintegral_congr fun x => ?_) this
    rw [ENNReal.toReal_ofNat, ENNReal.rpow_two, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hm : Measurable fun t : ℝ => ENNReal.ofReal (min (t ^ 2) 1 * |t| ^ (-(1 + α))) :=
    (((measurable_id.pow_const 2).min measurable_const).mul
      (measurable_id.abs.pow_const _)).ennreal_ofReal
  have key : ∀ j : Fin 2, Tendsto (fun R : ℝ => ∫⁻ p : (Fin 2 → ℝ) × ℝ,
      ENNReal.ofReal ((u (p.1 + p.2 • Pi.single j 1) -
        cutoff R (p.1 + p.2 • Pi.single j 1) * u (p.1 + p.2 • Pi.single j 1) -
        (u p.1 - cutoff R p.1 * u p.1)) ^ 2 * |p.2| ^ (-(1 + α)))) atTop (𝓝 0) := by
    intro j
    have h := tendsto_lintegral_filter_of_dominated_convergence (μ := volume) (l := atTop)
      (F := fun (R : ℝ) (p : (Fin 2 → ℝ) × ℝ) =>
        ENNReal.ofReal ((u (p.1 + p.2 • Pi.single j 1) -
          cutoff R (p.1 + p.2 • Pi.single j 1) * u (p.1 + p.2 • Pi.single j 1) -
          (u p.1 - cutoff R p.1 * u p.1)) ^ 2 * |p.2| ^ (-(1 + α))))
      (f := fun _ => 0)
      (fun (p : (Fin 2 → ℝ) × ℝ) =>
        2 * ENNReal.ofReal ((u (p.1 + p.2 • Pi.single j 1) - u p.1) ^ 2 *
          |p.2| ^ (-(1 + α))) + 2 * (ENNReal.ofReal (u p.1 ^ 2) *
          ENNReal.ofReal (min (p.2 ^ 2) 1 * |p.2| ^ (-(1 + α))))) ?_ ?_ ?_ ?_
    · simpa using h
    · exact Eventually.of_forall fun R =>
        measurable_jumpIntegrand α (hu.sub ((measurable_cutoff R).mul hu)) j
    · -- the domination for `R ≥ 1`
      filter_upwards [eventually_ge_atTop 1] with R hR
      refine Eventually.of_forall fun p => ?_
      have hw : 0 ≤ |p.2| ^ (-(1 + α)) := jumpWeight_nonneg α p
      have hd := sq_cutoff_sub_cutoff_le hR p.1 p.2 j
      have hc0 : 0 ≤ 1 - cutoff R (p.1 + p.2 • Pi.single j 1) := by
        linarith [cutoff_le_one R (p.1 + p.2 • Pi.single j 1)]
      have hc1 : 1 - cutoff R (p.1 + p.2 • Pi.single j 1) ≤ 1 := by
        linarith [cutoff_nonneg R (p.1 + p.2 • Pi.single j 1)]
      calc ENNReal.ofReal ((u (p.1 + p.2 • Pi.single j 1) -
            cutoff R (p.1 + p.2 • Pi.single j 1) * u (p.1 + p.2 • Pi.single j 1) -
            (u p.1 - cutoff R p.1 * u p.1)) ^ 2 * |p.2| ^ (-(1 + α)))
          ≤ ENNReal.ofReal (2 * ((u (p.1 + p.2 • Pi.single j 1) - u p.1) ^ 2 *
              |p.2| ^ (-(1 + α))) + 2 * (u p.1 ^ 2 * (min (p.2 ^ 2) 1 * |p.2| ^ (-(1 + α))))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            rw [show u (p.1 + p.2 • Pi.single j 1) -
                cutoff R (p.1 + p.2 • Pi.single j 1) * u (p.1 + p.2 • Pi.single j 1) -
                (u p.1 - cutoff R p.1 * u p.1) =
                (1 - cutoff R (p.1 + p.2 • Pi.single j 1)) *
                  (u (p.1 + p.2 • Pi.single j 1) - u p.1) +
                u p.1 * (cutoff R p.1 - cutoff R (p.1 + p.2 • Pi.single j 1)) by ring]
            have h1 : ((1 - cutoff R (p.1 + p.2 • Pi.single j 1)) *
                (u (p.1 + p.2 • Pi.single j 1) - u p.1) +
                u p.1 * (cutoff R p.1 - cutoff R (p.1 + p.2 • Pi.single j 1))) ^ 2 ≤
                2 * (u (p.1 + p.2 • Pi.single j 1) - u p.1) ^ 2 +
                2 * (u p.1 ^ 2 * min (p.2 ^ 2) 1) := by
              have hc2 : (1 - cutoff R (p.1 + p.2 • Pi.single j 1)) ^ 2 ≤ 1 :=
                pow_le_one₀ hc0 hc1
              nlinarith [sq_nonneg ((1 - cutoff R (p.1 + p.2 • Pi.single j 1)) *
                  (u (p.1 + p.2 • Pi.single j 1) - u p.1) -
                  u p.1 * (cutoff R p.1 - cutoff R (p.1 + p.2 • Pi.single j 1))),
                mul_le_mul_of_nonneg_left hc2 (sq_nonneg (u (p.1 + p.2 • Pi.single j 1) - u p.1)),
                mul_le_mul_of_nonneg_left hd (sq_nonneg (u p.1))]
            calc _ ≤ (2 * (u (p.1 + p.2 • Pi.single j 1) - u p.1) ^ 2 +
                  2 * (u p.1 ^ 2 * min (p.2 ^ 2) 1)) * |p.2| ^ (-(1 + α)) :=
                  mul_le_mul_of_nonneg_right h1 hw
              _ = _ := by ring
        _ = _ := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (p := 2) (by norm_num),
              ENNReal.ofReal_mul (p := 2) (by norm_num),
              ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (sq_nonneg _),
              ENNReal.ofReal_ofNat]
    · -- the dominating function is integrable
      rw [lintegral_add_left ((measurable_jumpIntegrand α hu j).const_mul 2),
        lintegral_const_mul 2 (measurable_jumpIntegrand α hu j),
        lintegral_const_mul 2 (f := fun p : (Fin 2 → ℝ) × ℝ => ENNReal.ofReal (u p.1 ^ 2) *
            ENNReal.ofReal (min (p.2 ^ 2) 1 * |p.2| ^ (-(1 + α))))
          (((hu.pow_const 2).ennreal_ofReal.comp measurable_fst).mul
            (hm.comp measurable_snd)),
        Measure.volume_eq_prod, lintegral_prod_mul (hu.pow_const 2).ennreal_ofReal.aemeasurable
          hm.aemeasurable]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (lintegral_jumpIntegrand_lt_top hE j).ne, ENNReal.mul_ne_top ENNReal.ofNat_ne_top
        (ENNReal.mul_ne_top hu_sq.ne (lintegral_min_sq_one_mul_rpow_lt_top hα hα').ne)⟩
    · -- the integrand vanishes once `R` exceeds `‖x‖` and `‖x + t e_j‖`
      refine Eventually.of_forall fun p => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ‖p.1‖, eventually_ge_atTop ‖p.1 + p.2 • Pi.single j 1‖,
        eventually_ge_atTop 1] with R hR hR' hR1
      rw [cutoff_eq_one (by linarith) hR, cutoff_eq_one (by linarith) hR']
      simp
  unfold jumpEnergy
  simpa using tendsto_finsetSum Finset.univ fun j _ => key j

/-! ### The energy as a sum of squared `L²` norms -/

/-- The weighted increment `(x, t) ↦ (u(x + t e_j) − u(x)) |t|^{−(1+α)/2}`; its squared `L²`
norm on `ℝ² × ℝ` is the `j`-th summand of the jump energy. -/
def weightedJump (α : ℝ) (u : (Fin 2 → ℝ) → ℝ) (j : Fin 2) (p : (Fin 2 → ℝ) × ℝ) : ℝ :=
  (u (p.1 + p.2 • Pi.single j 1) - u p.1) * |p.2| ^ (-(1 + α) / 2)

/-- The weighted increment of a measurable function is measurable. -/
theorem measurable_weightedJump (α : ℝ) {u : (Fin 2 → ℝ) → ℝ} (hu : Measurable u) (j : Fin 2) :
    Measurable (weightedJump α u j) :=
  (measurable_jumpDiff hu j).mul (measurable_snd.abs.pow_const _)

/-- The square of the weighted increment is the integrand of the jump energy. -/
theorem sq_weightedJump (α : ℝ) (u : (Fin 2 → ℝ) → ℝ) (j : Fin 2) (p : (Fin 2 → ℝ) × ℝ) :
    weightedJump α u j p ^ 2 =
      (u (p.1 + p.2 • Pi.single j 1) - u p.1) ^ 2 * |p.2| ^ (-(1 + α)) := by
  unfold weightedJump
  rw [mul_pow, ← Real.rpow_natCast (|p.2| ^ (-(1 + α) / 2)), ← Real.rpow_mul (abs_nonneg _)]
  congr 2
  push_cast
  ring

/-- The squared `enorm` of the weighted increment is the integrand of the jump energy. -/
theorem enorm_weightedJump_sq (α : ℝ) (u : (Fin 2 → ℝ) → ℝ) (j : Fin 2)
    (p : (Fin 2 → ℝ) × ℝ) :
    ‖weightedJump α u j p‖ₑ ^ 2 =
      ENNReal.ofReal ((u (p.1 + p.2 • Pi.single j 1) - u p.1) ^ 2 * |p.2| ^ (-(1 + α))) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, sq_weightedJump]

/-- The jump energy is the sum of the squared `L²` norms of the weighted increments. -/
theorem jumpEnergy_eq_sum_lintegral_enorm_sq (α : ℝ) (u : (Fin 2 → ℝ) → ℝ) :
    jumpEnergy α u = ∑ j : Fin 2, ∫⁻ p : (Fin 2 → ℝ) × ℝ, ‖weightedJump α u j p‖ₑ ^ 2 := by
  simp only [jumpEnergy, enorm_weightedJump_sq]

/-- Translating `v` by `h` translates its weighted increments by `(h, 0)`. -/
theorem weightedJump_comp_sub (α : ℝ) (v : (Fin 2 → ℝ) → ℝ) (j : Fin 2) (h : Fin 2 → ℝ)
    (p : (Fin 2 → ℝ) × ℝ) :
    weightedJump α (fun x => v (x - h)) j p = weightedJump α v j (p - (h, 0)) := by
  simp only [weightedJump, Prod.fst_sub, Prod.snd_sub, sub_zero, add_sub_right_comm]

/-- The weighted increment is linear. -/
theorem weightedJump_sub (α : ℝ) (u v : (Fin 2 → ℝ) → ℝ) (j : Fin 2) (p : (Fin 2 → ℝ) × ℝ) :
    weightedJump α (u - v) j p = weightedJump α u j p - weightedJump α v j p := by
  simp only [weightedJump, Pi.sub_apply]
  ring

/-- A function of finite energy has square-integrable weighted increments. -/
theorem memLp_weightedJump {α : ℝ} {u : (Fin 2 → ℝ) → ℝ} (hu : Measurable u)
    (hE : jumpEnergy α u ≠ ⊤) (j : Fin 2) : MemLp (weightedJump α u j) 2 volume := by
  refine ⟨(measurable_weightedJump α hu j).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, enorm_weightedJump_sq]
  exact (lintegral_jumpIntegrand_lt_top hE j).ne

/-! ### Mollification -/

/-- Lebesgue measure on `ℝ² × ℝ` is a Haar measure; the instance is stated for `volume` so that
it is found through the defeq `volume = volume.prod volume`. -/
instance : (volume : Measure ((Fin 2 → ℝ) × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

variable (b : ContDiffBump (0 : Fin 2 → ℝ))

/-- The normalised bump is a probability density. -/
theorem lintegral_enorm_normed : ∫⁻ h, ‖b.normed volume h‖ₑ = 1 := by
  have h := ofReal_integral_eq_lintegral_ofReal (b.integrable_normed (μ := volume))
    (ae_of_all _ fun h => b.nonneg_normed h)
  rw [b.integral_normed, ENNReal.ofReal_one] at h
  rw [h]
  exact lintegral_congr fun h => Real.enorm_eq_ofReal (b.nonneg_normed h)

/-- The product of the bump with a translate of an integrable function is integrable. -/
theorem integrable_normed_mul_comp_sub {v : (Fin 2 → ℝ) → ℝ} (hv : Integrable v)
    (x : Fin 2 → ℝ) : Integrable fun h => b.normed volume h * v (x - h) := by
  obtain ⟨C, hC⟩ :=
    b.continuous_normed.bounded_above_of_compact_support
      (b.hasCompactSupport_normed (μ := volume))
  exact (hv.comp_sub_left x).bdd_mul b.continuous_normed.aestronglyMeasurable (ae_of_all _ hC)

/-- The product of the bump with a translation error of an integrable function is integrable. -/
theorem integrable_normed_mul_sub {v : (Fin 2 → ℝ) → ℝ} (hv : Integrable v) (x : Fin 2 → ℝ) :
    Integrable fun h => b.normed volume h * (v (x - h) - v x) := by
  simp_rw [mul_sub]
  exact (integrable_normed_mul_comp_sub b hv x).sub (b.integrable_normed.mul_const _)

/-- The mollification error as an average of translation errors:
`(ρ ⋆ v)(x) − v(x) = ∫ ρ(h) (v(x − h) − v(x)) dh`. -/
theorem convolution_normed_sub {v : (Fin 2 → ℝ) → ℝ} (hv : Integrable v) (x : Fin 2 → ℝ) :
    (b.normed volume ⋆ v) x - v x = ∫ h, b.normed volume h * (v (x - h) - v x) := by
  simp_rw [mul_sub]
  rw [integral_sub (integrable_normed_mul_comp_sub b hv x) (b.integrable_normed.mul_const _),
    integral_mul_const, b.integral_normed, one_mul, convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- Integrating against the bump of radius `rOut` only sees `F` on the ball of that radius. -/
theorem lintegral_enorm_normed_mul_le {F : (Fin 2 → ℝ) → ℝ≥0∞} {ε : ℝ≥0∞}
    (hF : ∀ h, ‖h‖ < b.rOut → F h ≤ ε) : ∫⁻ h, ‖b.normed volume h‖ₑ * F h ≤ ε := by
  calc ∫⁻ h, ‖b.normed volume h‖ₑ * F h ≤ ∫⁻ h, ‖b.normed volume h‖ₑ * ε := by
        refine lintegral_mono fun h => ?_
        by_cases hh : ‖h‖ < b.rOut
        · exact mul_le_mul_right (hF h hh) _
        · have : b.normed volume h = 0 := by
            rw [← Function.notMem_support, b.support_normed_eq]
            simpa [mem_ball_zero_iff] using hh
          simp [this]
    _ = ε := by
        rw [lintegral_mul_const _ b.continuous_normed.measurable.enorm, lintegral_enorm_normed,
          one_mul]

/-- `L¹` mollification error, bounded by the averaged translation error. -/
theorem lintegral_enorm_convolution_normed_sub_le {v : (Fin 2 → ℝ) → ℝ} (hv : Measurable v)
    (hv₁ : Integrable v) :
    ∫⁻ x, ‖(b.normed volume ⋆ v) x - v x‖ₑ ≤
      ∫⁻ h, ‖b.normed volume h‖ₑ * ∫⁻ x, ‖v (x - h) - v x‖ₑ := by
  simp_rw [convolution_normed_sub b hv₁]
  exact lintegral_enorm_integral_mul_le b.continuous_normed.measurable
    (W := fun h x => v (x - h) - v x)
    ((hv.comp (measurable_snd.sub measurable_fst)).sub (hv.comp measurable_snd))

/-- `L²` mollification error, bounded by the averaged translation error. -/
theorem lintegral_enorm_convolution_normed_sub_sq_le {v : (Fin 2 → ℝ) → ℝ} (hv : Measurable v)
    (hv₁ : Integrable v) :
    ∫⁻ x, ‖(b.normed volume ⋆ v) x - v x‖ₑ ^ 2 ≤
      ∫⁻ h, ‖b.normed volume h‖ₑ * ∫⁻ x, ‖v (x - h) - v x‖ₑ ^ 2 := by
  simp_rw [convolution_normed_sub b hv₁]
  exact lintegral_enorm_integral_mul_sq_le b.continuous_normed.measurable
    (lintegral_enorm_normed b).le (W := fun h x => v (x - h) - v x)
    ((hv.comp (measurable_snd.sub measurable_fst)).sub (hv.comp measurable_snd))

/-- Energy mollification error: the weighted increments of `ρ ⋆ v − v` are averages of the
translation errors of the weighted increments of `v`, so their squared `L²` norms are bounded by
the averaged squared translation errors on `ℝ² × ℝ`. -/
theorem lintegral_enorm_weightedJump_convolution_normed_sub_sq_le {α : ℝ}
    {v : (Fin 2 → ℝ) → ℝ} (hv : Measurable v) (hv₁ : Integrable v) (j : Fin 2) :
    ∫⁻ p, ‖weightedJump α (b.normed volume ⋆ v - v) j p‖ₑ ^ 2 ≤
      ∫⁻ h, ‖b.normed volume h‖ₑ *
        ∫⁻ p, ‖weightedJump α v j (p - (h, 0)) - weightedJump α v j p‖ₑ ^ 2 := by
  have key : ∀ p : (Fin 2 → ℝ) × ℝ, weightedJump α (b.normed volume ⋆ v - v) j p =
      ∫ h, b.normed volume h * (weightedJump α v j (p - (h, 0)) - weightedJump α v j p) := by
    intro p
    simp only [weightedJump, Pi.sub_apply, Prod.fst_sub, Prod.snd_sub, sub_zero]
    rw [convolution_normed_sub b hv₁, convolution_normed_sub b hv₁,
      ← integral_sub (integrable_normed_mul_sub b hv₁ _) (integrable_normed_mul_sub b hv₁ _),
      ← integral_mul_const]
    congr 1
    funext h
    rw [add_sub_right_comm]
    ring
  simp_rw [key]
  exact lintegral_enorm_integral_mul_sq_le b.continuous_normed.measurable
    (lintegral_enorm_normed b).le
    (W := fun h p => weightedJump α v j (p - (h, 0)) - weightedJump α v j p)
    (((measurable_weightedJump α hv j).comp
      (measurable_snd.sub (measurable_fst.prodMk measurable_const))).sub
      ((measurable_weightedJump α hv j).comp measurable_snd))

/-- Extracting a radius from a neighbourhood of `0` in `ℝ²`. -/
theorem exists_norm_lt_imp_of_eventually_nhds_zero {P : (Fin 2 → ℝ) → Prop}
    (h : ∀ᶠ h in 𝓝 (0 : Fin 2 → ℝ), P h) : ∃ δ > 0, ∀ h, ‖h‖ < δ → P h := by
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.1 h
  exact ⟨δ, hδ, fun h hh => hP (by rwa [dist_zero_right])⟩

/-- Mollification of a compactly supported function of finite energy in `L¹ ∩ L²`: for every
`ε > 0` there is a smooth compactly supported `φ` which is `ε`-close in energy, in `L¹` and in
`L²`. -/
theorem exists_contDiff_hasCompactSupport_approx_of_hasCompactSupport {α : ℝ}
    {v : (Fin 2 → ℝ) → ℝ} (hv : Measurable v) (hv₁ : Integrable v) (hv₂ : MemLp v 2 volume)
    (hvc : HasCompactSupport v) (hE : jumpEnergy α v ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : (Fin 2 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      jumpEnergy α (v - φ) < ENNReal.ofReal ε ∧ ∫⁻ x, ‖v x - φ x‖ₑ < ENNReal.ofReal ε ∧
      eLpNorm (v - φ) 2 volume < ENNReal.ofReal ε := by
  have hε2 : 0 < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 (by positivity)
  have hε4 : 0 < ENNReal.ofReal (ε / 4) := ENNReal.ofReal_pos.2 (by positivity)
  have hlt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε :=
    (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
  -- continuity of translation in `L¹`, in `L²`, and in `L²(ℝ² × ℝ)` for the weighted increments
  have ev₁ : ∀ᶠ h in 𝓝 (0 : Fin 2 → ℝ),
      ∫⁻ x, ‖v (x - h) - v x‖ₑ ≤ ENNReal.ofReal (ε / 2) := by
    have := tendsto_eLpNorm_comp_sub_sub le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.2 hv₁)
    simp_rw [eLpNorm_one_eq_lintegral_enorm] at this
    exact ENNReal.tendsto_nhds_zero.1 this _ hε2
  have ev₂ : ∀ᶠ h in 𝓝 (0 : Fin 2 → ℝ),
      ∫⁻ x, ‖v (x - h) - v x‖ₑ ^ 2 ≤ ENNReal.ofReal (ε / 2) ^ 2 := by
    have := ((ENNReal.continuous_pow 2).tendsto 0).comp
      (tendsto_eLpNorm_comp_sub_sub one_le_two ENNReal.ofNat_ne_top hv₂)
    rw [zero_pow two_ne_zero] at this
    have := ENNReal.tendsto_nhds_zero.1 this _ (ENNReal.pow_pos hε2 2)
    simpa [Function.comp_def, lintegral_enorm_sq] using this
  have ev₃ : ∀ᶠ h in 𝓝 (0 : Fin 2 → ℝ), ∀ j : Fin 2,
      ∫⁻ p, ‖weightedJump α v j (p - (h, 0)) - weightedJump α v j p‖ₑ ^ 2 ≤
        ENNReal.ofReal (ε / 4) := by
    refine Filter.eventually_all.2 fun j => ?_
    have h0 : Tendsto (fun h : Fin 2 → ℝ => ((h, 0) : (Fin 2 → ℝ) × ℝ)) (𝓝 0) (𝓝 0) := by
      exact (continuous_id.prodMk (continuous_const (y := (0 : ℝ)))).tendsto' 0 0 rfl
    have := ((ENNReal.continuous_pow 2).tendsto 0).comp
      ((tendsto_eLpNorm_comp_sub_sub one_le_two ENNReal.ofNat_ne_top
        (memLp_weightedJump hv hE j)).comp h0)
    rw [zero_pow two_ne_zero] at this
    have := ENNReal.tendsto_nhds_zero.1 this _ hε4
    simpa [Function.comp_def, lintegral_enorm_sq] using this
  obtain ⟨δ, hδ, hδ'⟩ := exists_norm_lt_imp_of_eventually_nhds_zero ((ev₁.and ev₂).and ev₃)
  -- the bump of radius `δ`
  let b : ContDiffBump (0 : Fin 2 → ℝ) := ⟨δ / 2, δ, by positivity, by linarith⟩
  refine ⟨b.normed volume ⋆ v, ?_, ?_, ?_, ?_, ?_⟩
  · exact b.hasCompactSupport_normed.contDiff_convolution_left _ b.contDiff_normed
      hv₁.locallyIntegrable
  · exact b.hasCompactSupport_normed.convolution _ hvc
  · rw [← jumpEnergy_neg, neg_sub, jumpEnergy_eq_sum_lintegral_enorm_sq]
    calc ∑ j : Fin 2, ∫⁻ p, ‖weightedJump α (b.normed volume ⋆ v - v) j p‖ₑ ^ 2
        ≤ ∑ j : Fin 2, ENNReal.ofReal (ε / 4) := Finset.sum_le_sum fun j _ =>
          (lintegral_enorm_weightedJump_convolution_normed_sub_sq_le b hv hv₁ j).trans
            (lintegral_enorm_normed_mul_le b fun h hh => (hδ' h hh).2 j)
      _ = ENNReal.ofReal (ε / 2) := by
          rw [Fin.sum_univ_two, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
      _ < ENNReal.ofReal ε := hlt
  · calc ∫⁻ x, ‖v x - (b.normed volume ⋆ v) x‖ₑ
        = ∫⁻ x, ‖(b.normed volume ⋆ v) x - v x‖ₑ := lintegral_congr fun x => enorm_sub_rev _ _
      _ ≤ ∫⁻ h, ‖b.normed volume h‖ₑ * ∫⁻ x, ‖v (x - h) - v x‖ₑ :=
          lintegral_enorm_convolution_normed_sub_le b hv hv₁
      _ ≤ ENNReal.ofReal (ε / 2) := lintegral_enorm_normed_mul_le b fun h hh => (hδ' h hh).1.1
      _ < ENNReal.ofReal ε := hlt
  · have h1 : eLpNorm (v - b.normed volume ⋆ v) 2 volume ^ 2 ≤ ENNReal.ofReal (ε / 2) ^ 2 := by
      rw [← lintegral_enorm_sq]
      calc ∫⁻ x, ‖(v - b.normed volume ⋆ v) x‖ₑ ^ 2
          = ∫⁻ x, ‖(b.normed volume ⋆ v) x - v x‖ₑ ^ 2 :=
            lintegral_congr fun x => by rw [Pi.sub_apply, enorm_sub_rev]
        _ ≤ _ := lintegral_enorm_convolution_normed_sub_sq_le b hv hv₁
        _ ≤ ENNReal.ofReal (ε / 2) ^ 2 :=
            lintegral_enorm_normed_mul_le b fun h hh => (hδ' h hh).1.2
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_two, ENNReal.rpow_le_rpow_iff two_pos] at h1
    exact h1.trans_lt hlt

/-! ### The density theorem -/

/-- **Density of smooth compactly supported functions**: a measurable `u ∈ L¹ ∩ L²` of finite
jump energy is approximated, simultaneously in energy, in `L¹` and in `L²`, by smooth compactly
supported functions. The approximant is a mollification `ρ_δ ⋆ (χ_R u)` of a cutoff of `u`. -/
theorem exists_contDiff_hasCompactSupport_approx {α : ℝ} (hα : 0 < α) (hα' : α < 2)
    {u : (Fin 2 → ℝ) → ℝ} (hu : Measurable u) (hu₁ : Integrable u) (hu₂ : MemLp u 2 volume)
    (hE : jumpEnergy α u ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : (Fin 2 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      jumpEnergy α (u - φ) < ENNReal.ofReal ε ∧ ∫⁻ x, ‖u x - φ x‖ₑ < ENNReal.ofReal ε ∧
      eLpNorm (u - φ) 2 volume < ENNReal.ofReal ε := by
  have hε4 : 0 < ENNReal.ofReal (ε / 4) := ENNReal.ofReal_pos.2 (by positivity)
  have hε2 : 0 < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 (by positivity)
  -- the cutoff radius
  obtain ⟨R, hR1, hRE, hR₁, hR₂⟩ : ∃ R : ℝ, 1 ≤ R ∧
      jumpEnergy α (fun x => u x - cutoff R x * u x) < ENNReal.ofReal (ε / 4) ∧
      eLpNorm (fun x => u x - cutoff R x * u x) 1 volume < ENNReal.ofReal (ε / 2) ∧
      eLpNorm (fun x => u x - cutoff R x * u x) 2 volume < ENNReal.ofReal (ε / 2) := by
    have h₁ := (tendsto_jumpEnergy_sub_cutoff_mul hα hα' hu hu₂ hE).eventually (gt_mem_nhds hε4)
    have h₂ := (tendsto_eLpNorm_sub_cutoff_mul one_ne_zero ENNReal.one_ne_top hu
      (memLp_one_iff_integrable.2 hu₁)).eventually (gt_mem_nhds hε2)
    have h₃ := (tendsto_eLpNorm_sub_cutoff_mul two_ne_zero ENNReal.ofNat_ne_top hu
      hu₂).eventually (gt_mem_nhds hε2)
    obtain ⟨R, hR⟩ := (((eventually_ge_atTop 1).and h₁).and (h₂.and h₃)).exists
    exact ⟨R, hR.1.1, hR.1.2, hR.2.1, hR.2.2⟩
  have hR : 0 < R := by linarith
  -- the cutoff `v = χ_R u` is measurable, compactly supported, in `L¹ ∩ L²`, of finite energy
  set v : (Fin 2 → ℝ) → ℝ := fun x => cutoff R x * u x with hv_def
  have hv : Measurable v := (measurable_cutoff R).mul hu
  have hcut : ∀ x, ‖cutoff R x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (cutoff_nonneg R x)]
    exact cutoff_le_one R x
  have hv₁ : Integrable v :=
    hu₁.bdd_mul (continuous_cutoff R).aestronglyMeasurable (ae_of_all _ hcut)
  have hv₂ : MemLp v 2 volume :=
    hu₂.of_le hv.aestronglyMeasurable (ae_of_all _ fun x => by
      show ‖cutoff R x * u x‖ ≤ ‖u x‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hcut x))
  have hvc : HasCompactSupport v := (hasCompactSupport_cutoff hR).mul_right
  have huv : jumpEnergy α (u - v) ≠ ⊤ := hRE.ne_top
  have hvE : jumpEnergy α v ≠ ⊤ := by
    have := jumpEnergy_add_smul_ne_top α hu hE huv (-1)
    rwa [show u + (-1 : ℝ) • (u - v) = v by
      ext x
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring] at this
  obtain ⟨φ, hφ, hφc, hφE, hφ₁, hφ₂⟩ :=
    exists_contDiff_hasCompactSupport_approx_of_hasCompactSupport hv hv₁ hv₂ hvc hvE
      (by positivity : 0 < ε / 4)
  have hφm : Measurable φ := hφ.continuous.measurable
  refine ⟨φ, hφ, hφc, ?_, ?_, ?_⟩
  · calc jumpEnergy α (u - φ) = jumpEnergy α (u - v + (v - φ)) := by rw [sub_add_sub_cancel]
      _ ≤ 2 * (jumpEnergy α (u - v) + jumpEnergy α (v - φ)) := jumpEnergy_add_le α (hu.sub hv) _
      _ < 2 * (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) :=
          ENNReal.mul_lt_mul_right two_ne_zero ENNReal.ofNat_ne_top (ENNReal.add_lt_add hRE hφE)
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
  · have hR₁' : ∫⁻ x, ‖u x - v x‖ₑ < ENNReal.ofReal (ε / 2) := by
      rw [← eLpNorm_one_eq_lintegral_enorm]
      exact hR₁
    calc ∫⁻ x, ‖u x - φ x‖ₑ ≤ (∫⁻ x, ‖u x - v x‖ₑ) + ∫⁻ x, ‖v x - φ x‖ₑ := by
          rw [← lintegral_add_left (f := fun x => ‖u x - v x‖ₑ) (hu.sub hv).enorm]
          exact lintegral_mono fun x => by
            simpa only [edist_eq_enorm_sub] using edist_triangle (u x) (v x) (φ x)
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4) := ENNReal.add_lt_add hR₁' hφ₁
      _ ≤ ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (by linarith)
  · calc eLpNorm (u - φ) 2 volume ≤ eLpNorm (u - v) 2 volume + eLpNorm (v - φ) 2 volume := by
          rw [← sub_add_sub_cancel u v φ]
          exact eLpNorm_add_le (hu.sub hv).aestronglyMeasurable
            (hv.sub hφm).aestronglyMeasurable one_le_two
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4) := ENNReal.add_lt_add hR₂ hφ₂
      _ ≤ ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (by linarith)

end CenteredMaximal
