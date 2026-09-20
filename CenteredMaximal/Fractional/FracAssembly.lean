/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Cauchy.Assembly
public import CenteredMaximal.Fractional.BaseMoment
public import CenteredMaximal.Fractional.MajorBase
public import CenteredMaximal.Fractional.SolutionModulus

/-!
# Assembling the `α = 6/5` weak type bound from the obstacle decomposition

This file is the fractional analogue of `CenteredMaximal.Cauchy.Assembly`: it turns the obstacle
decomposition of `CenteredMaximal.Obstacle.Main` at order `α = 6/5` into the weak type `(1, 1)`
bound `c₂ ≤ ½ ∫ K < 3.622` for the comparison kernel `K = fracKernel` of
`CenteredMaximal.Fractional.KernelMass`.

Everything analytic is imported. What is *not* proved here are the two finite certificates

`0 ≤ K z` for `z ≠ 0`   and   `1 ≤ K z` for `z ≠ 0` with `diamondNorm z ≤ 1`,

and two facts about the generator density `g = fracDensity = jumpGen (6/5) fracKernel`: that it is
almost everywhere nonnegative, and the `L²` moment

`∫ g(z)² min(1, ‖z‖^{16/5}) dz < ∞`.

All four enter every theorem of the last section as hypotheses.

The `L²` moment takes the place of the pointwise majorant `g ≤ A (r^{−12/5} + r^{−11/5})` that
`CenteredMaximal.Fractional.hgconv_of_jumpEnergy_six_fifths` asks for, because the density of a
*compactly supported* kernel satisfies **no** such majorant. Inside the diamond the majorant is the
right shape: there `jumpGen_truncBase` evaluates the base's generator as the closed-form multiple of
`r^{−2α} = r^{−12/5}` plus the nonnegative tail. Outside it the kernel vanishes, so at
`z = (D, ε)` with `D > 7/4` the generator is the bare pair of displaced values,

`g(D, ε) = ∑_j ∫ (K(z + t e_j) + K(z − t e_j)) |t|^{−11/5} dt`,

whose `j = 0` term is about `D^{−11/5} ∫ K(s, ε) ds`. That line integral diverges like `ε^{−1/5}` as
`ε → 0`, because the line passes at distance `ε` from the base's non-integrable `r^{−6/5}`
singularity, and nothing cancels it: for the *un*truncated diamond power the divergence is cancelled
by the first-order term of the `j = 1` direction — that cancellation is the content of
`CenteredMaximal.Fractional.DiamondConstancy` — but here `K` vanishes identically on the whole line
`{(D, ε ± t)}`, so the `j = 1` term is `0`. Hence `g(D, ε) → ∞` at fixed `D > 7/4`, while every
`A (r^{−p} + r^{−q})` stays bounded there.

The blow-up `g ≲ r^{−11/5} min(|z₀|, |z₁|)^{−1/5}` is harmless for both moments, `‖z‖^{−2/5}` being
integrable in one dimension: the first moment is in fact unconditional
(`integrable_fracDensity_mul_min_one'`), and only the second one is asked for here.
`setLIntegral_conv_ne_top_of_moments` below redoes the two-regime bound of
`CenteredMaximal.Fractional.setLIntegral_conv_ne_top` from the two moments alone.

As in the `α = 1` assembly, Lean evaluates `fracKernel 0` to a finite value, because `0 ^ (-α) = 0`
makes the diamond base vanish at the origin instead of blowing up, while
`CenteredMaximal.weakTypeConstant_two_le_of_diamond` needs `1 ≤ K z` for *every* `z` of the closed
unit diamond. The single offending point is patched: `fracComp` agrees with `fracKernel` away from
the origin and takes the value `1` there.

The density is patched too, by its positive part `fracGen = max (fracDensity ·) 0`: the transfer
`CenteredMaximal.convolution_le_of_eq_zero_fp` needs a *pointwise* nonnegative density, while only
almost everywhere nonnegativity is available. Both patches are invisible to every integral.

## Main results

* `fracComp`, `fracComp_ae_eq`, `fracComp_nonneg`, `one_le_fracComp`, `fracComp_neg`,
  `integrable_fracComp`, `integral_fracComp`, `hasCompactSupport_fracComp`: the patched kernel and
  its basic properties, in particular `∫ fracComp = ∫ fracKernel < 2 · 3.622`;
* `fracGen`, `fracGen_nonneg`, `fracGen_ae_eq`, `integrable_fracGen_mul_min_one`, `hKgen_fracComp`:
  the patched density, its Lévy moment and the merged generator representation of `fracComp`;
* `integrable_fracGen_mul_min_one_rpow`, `integrable_fracGen_sq_mul_min_one_rpow`,
  `integrable_dilate_mul_min_rpow`: the first and second moments of the patched density against
  `min(1, ‖z‖^{16/5})`, and their invariance under dilation;
* `setLIntegral_conv_ne_top_of_moments`, `hgconv_of_moments`: the joint integrability hypothesis
  `hgconv` of `CenteredMaximal.convolution_le_of_eq_zero_fp` from those two moments and finite jump
  energy, in place of a pointwise majorant on the density;
* `exists_exceptional_set_frac`: **the pointwise step.** For a bounded, nonnegative, compactly
  supported measurable obstacle `f` and a level `λ > 0`, the obstacle problem of order `6/5` with
  cap `κ = λ / ∫ K` produces an exceptional set `Ω` of measure at most `(∫ K) (∫ f) / λ` off which
  every dilation average `∫ K_s(x − y) f(y) dy` is at most `λ`, almost everywhere for each scale
  `s > 0` separately;
* `weakTypeConstant_two_le_frac`: hence `c₂ ≤ 3.622`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open CenteredMaximal.Cauchy
open scoped ENNReal

namespace CenteredMaximal.Fractional

/-! ### The patched kernel -/

/-- The comparison kernel of order `6/5` with its value at the origin patched to `1`. Lean
evaluates the diamond base to `0 - R ^ (-α) < 0` at the origin, because `0 ^ (-α) = 0`, while the
kernel is meant to be `+∞` there; the patch makes the kernel at least `1` on the *whole* unit
diamond without changing any integral. -/
def fracComp (z : Fin 2 → ℝ) : ℝ := if z = 0 then 1 else fracKernel z

@[simp]
theorem fracComp_zero : fracComp 0 = 1 :=
  if_pos rfl

theorem fracComp_of_ne {z : Fin 2 → ℝ} (hz : z ≠ 0) : fracComp z = fracKernel z :=
  if_neg hz

/-- The patch changes the kernel only at the origin, a null set. -/
theorem fracComp_ae_eq : fracComp =ᵐ[volume] fracKernel := by
  show ∀ᵐ z ∂volume, fracComp z = fracKernel z
  refine ae_iff.2 (measure_mono_null (fun z hz => ?_) (measure_singleton (0 : Fin 2 → ℝ)))
  by_contra hz₀
  exact hz (fracComp_of_ne hz₀)

theorem measurable_fracComp : Measurable fracComp :=
  Measurable.ite (measurableSet_singleton (0 : Fin 2 → ℝ)) measurable_const measurable_fracKernel

/-- The patched kernel is nonnegative everywhere, given the positivity certificate. -/
theorem fracComp_nonneg (hpos : ∀ z, z ≠ 0 → 0 ≤ fracKernel z) (z : Fin 2 → ℝ) :
    0 ≤ fracComp z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [fracComp_zero]
    norm_num
  · rw [fracComp_of_ne hz]
    exact hpos z hz

/-- The patched kernel is at least `1` on the whole closed unit diamond, the origin included. -/
theorem one_le_fracComp (hone : ∀ z, z ≠ 0 → diamondNorm z ≤ 1 → 1 ≤ fracKernel z)
    {z : Fin 2 → ℝ} (hz : diamondNorm z ≤ 1) : 1 ≤ fracComp z := by
  rcases eq_or_ne z 0 with rfl | hz₀
  · rw [fracComp_zero]
  · rw [fracComp_of_ne hz₀]
    exact hone z hz₀ hz

/-- The kernel is even: it is a function of the two absolute values (`fracKernel_abs`). -/
theorem fracKernel_neg (z : Fin 2 → ℝ) : fracKernel (-z) = fracKernel z := by
  rw [fracKernel_abs (-z), fracKernel_abs z]
  congr 1
  exact funext fun i => by simp

/-- The patched kernel is even. -/
theorem fracComp_neg (z : Fin 2 → ℝ) : fracComp (-z) = fracComp z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [neg_zero]
  · rw [fracComp_of_ne (neg_ne_zero.2 hz), fracComp_of_ne hz, fracKernel_neg]

theorem integrable_fracComp : Integrable fracComp :=
  integrable_fracKernel.congr fracComp_ae_eq.symm

/-- The patch does not change the mass of the kernel. -/
theorem integral_fracComp : ∫ z, fracComp z = ∫ z, fracKernel z :=
  integral_congr_ae fracComp_ae_eq

/-- **The mass of the patched kernel is positive**: the explicit value
`2 (3/2 · a · (7/4)^{4/5} + (∑ C)/512)` is bounded below through the fifth-root enclosure of
`(7/4)^{4/5}`. -/
theorem integral_fracComp_pos : 0 < ∫ z, fracComp z := by
  rw [integral_fracComp, integral_fracKernel, fracBaseCoeff_eq, fracCellSum_eq]
  linarith [lt_rpow_four_fifths]

/-- **The mass bound for the patched kernel**: `∫ fracComp < 2 · 3.622`. -/
theorem integral_fracComp_lt : ∫ z, fracComp z < 2 * (3622 / 1000) := by
  rw [integral_fracComp]
  exact fracKernel_mass_lt

/-- The patched kernel is supported in the Euclidean ball of radius `7/4`, which contains the
diamond of radius `7/4` since the norm is dominated by the diamond radius. -/
theorem hasCompactSupport_fracComp : HasCompactSupport fracComp := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 2 → ℝ) (7 / 4))
    fun x hx => ?_
  have hnorm : (7 : ℝ) / 4 < ‖x‖ := by
    simpa [mem_closedBall_zero_iff, not_le] using hx
  have hx₀ : x ≠ 0 := fun h => by
    rw [h, norm_zero] at hnorm
    norm_num at hnorm
  rw [fracComp_of_ne hx₀]
  exact fracKernel_eq_zero_of_le (hnorm.le.trans (norm_le_diamondNorm x))

/-- Dilations of the patched kernel are even, because scaling commutes with the reflection. -/
theorem dilate_fracComp_neg (s : ℝ) (x : Fin 2 → ℝ) :
    dilate fracComp s (-x) = dilate fracComp s x := by
  rw [dilate, dilate, smul_neg, fracComp_neg]

/-- The `s`-dilation of the patched kernel is supported in the ball of radius `7 s / 4`: outside it
the rescaled point `s⁻¹ • x` has diamond radius beyond `7/4`. -/
theorem hasCompactSupport_dilate_fracComp {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (dilate fracComp s) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 2 → ℝ) (s * (7 / 4)))
    fun x hx => ?_
  have hnorm : s * (7 / 4) < ‖x‖ := by
    simpa [mem_closedBall_zero_iff, not_le] using hx
  have h₁ : s * (7 / 4) < diamondNorm x := hnorm.trans_le (norm_le_diamondNorm x)
  have hd : (7 : ℝ) / 4 < diamondNorm (s⁻¹ • x) := by
    rw [diamondNorm_smul, abs_of_pos (inv_pos.2 hs)]
    calc (7 : ℝ) / 4 = s⁻¹ * (s * (7 / 4)) := by field_simp
      _ < s⁻¹ * diamondNorm x := mul_lt_mul_of_pos_left h₁ (inv_pos.2 hs)
  have hz₀ : s⁻¹ • x ≠ 0 := fun h => by
    rw [h, diamondNorm_eq_zero_iff.2 rfl] at hd
    norm_num at hd
  rw [dilate, fracComp_of_ne hz₀, fracKernel_eq_zero_of_le hd.le, mul_zero]

/-! ### The patched generator density -/

/-- The generator density of the comparison kernel, patched to its positive part. The transfer
`CenteredMaximal.convolution_le_of_eq_zero_fp` needs a pointwise nonnegative density, while the
certificate only gives nonnegativity almost everywhere. -/
def fracGen (z : Fin 2 → ℝ) : ℝ := max (fracDensity z) 0

theorem measurable_fracGen : Measurable fracGen :=
  measurable_fracDensity.max measurable_const

theorem fracGen_nonneg (z : Fin 2 → ℝ) : 0 ≤ fracGen z := le_max_right _ _

/-- The patch is invisible as soon as the density is almost everywhere nonnegative. -/
theorem fracGen_ae_eq (hgen : 0 ≤ᵐ[volume] fracDensity) : fracGen =ᵐ[volume] fracDensity := by
  filter_upwards [hgen] with z hz
  exact max_eq_left hz

/-- The Lévy moment of the patched density. -/
theorem integrable_fracGen_mul_min_one (hgen : 0 ≤ᵐ[volume] fracDensity) :
    Integrable fun z => fracGen z * min 1 ‖z‖ := by
  refine integrable_fracDensity_mul_min_one'.congr ?_
  filter_upwards [fracGen_ae_eq hgen] with z hz
  rw [hz]

/-- **The merged generator representation of the patched kernel**: `∫ K · A ψ = ∫ g (ψ − ψ 0)` for
the patched kernel `K = fracComp` and the patched density `g = fracGen`. -/
theorem hKgen_fracComp (hgen : 0 ≤ᵐ[volume] fracDensity) {ψ : (Fin 2 → ℝ) → ℝ}
    (hψ : IsTestFunction ψ) :
    (∫ x, fracComp x * jumpGen (6 / 5) ψ x) = ∫ y, fracGen y * (ψ y - ψ 0) := by
  have h₁ : (∫ x, fracComp x * jumpGen (6 / 5) ψ x)
      = ∫ x, fracKernel x * jumpGen (6 / 5) ψ x := by
    refine integral_congr_ae ?_
    filter_upwards [fracComp_ae_eq] with x hx
    rw [hx]
  have h₂ : (∫ y, fracDensity y * (ψ y - ψ 0)) = ∫ y, fracGen y * (ψ y - ψ 0) := by
    refine integral_congr_ae ?_
    filter_upwards [fracGen_ae_eq hgen] with y hy
    rw [hy]
  rw [h₁, hKgen_fracKernel' hψ, h₂]

/-! ### Moments of the patched density -/

/-- A truncated weight only shrinks when its exponent grows: `min(1, r^θ) ≤ min(1, r)` for `1 ≤ θ`
and `0 ≤ r`. -/
private theorem min_one_rpow_le_min_one {θ r : ℝ} (hθ : 1 ≤ θ) (hr : 0 ≤ r) :
    min 1 (r ^ θ) ≤ min 1 r := by
  have hθ0 : θ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hθ)
  rcases lt_or_ge 1 r with h | h
  · rw [min_eq_left h.le]
    exact min_le_left _ _
  · rcases eq_or_lt_of_le hr with rfl | hr0
    · rw [Real.zero_rpow hθ0]
    · refine min_le_min le_rfl ?_
      calc r ^ θ ≤ r ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hr0 h hθ
        _ = r := Real.rpow_one r

/-- **The Lévy moment of the patched density at the exponent `16/5 = 2 + α`.** The weight
`min(1, ‖z‖^{16/5})` is dominated by the weight `min(1, ‖z‖)` of the unconditional moment. -/
theorem integrable_fracGen_mul_min_one_rpow (hgen : 0 ≤ᵐ[volume] fracDensity) :
    Integrable fun z => fracGen z * min 1 (‖z‖ ^ (16 / 5 : ℝ)) := by
  refine (integrable_fracGen_mul_min_one hgen).mono'
    (measurable_fracGen.mul
      (measurable_const.min (measurable_norm.pow_const _))).aestronglyMeasurable
    (.of_forall fun z => ?_)
  have h0 : (0 : ℝ) ≤ min 1 (‖z‖ ^ (16 / 5 : ℝ)) :=
    le_min zero_le_one (Real.rpow_nonneg (norm_nonneg z) _)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (fracGen_nonneg z) h0)]
  exact mul_le_mul_of_nonneg_left (min_one_rpow_le_min_one (by norm_num) (norm_nonneg z))
    (fracGen_nonneg z)

/-- **The `L²` moment of the patched density**, inherited from the corresponding certificate for
the density itself. -/
theorem integrable_fracGen_sq_mul_min_one_rpow (hgen : 0 ≤ᵐ[volume] fracDensity)
    (hsq : Integrable fun z => fracDensity z ^ 2 * min 1 (‖z‖ ^ (16 / 5 : ℝ))) :
    Integrable fun z => fracGen z ^ 2 * min 1 (‖z‖ ^ (16 / 5 : ℝ)) := by
  refine hsq.congr ?_
  filter_upwards [fracGen_ae_eq hgen] with z hz
  rw [hz]

/-! ### Moments survive dilation -/

/-- Splitting a truncated weight: `min(1, a b) ≤ max(1, a) min(1, b)` for `b ≥ 0`. -/
private theorem min_one_mul_le {a b : ℝ} (hb : 0 ≤ b) :
    min 1 (a * b) ≤ max 1 a * min 1 b := by
  rcases le_total b 1 with h | h
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right (le_max_right 1 a) hb)
  · rw [min_eq_left h, mul_one]
    exact (min_le_left _ _).trans (le_max_left 1 a)

/-- **The moment condition at a general exponent survives dilation**, the analogue of
`CenteredMaximal.integrable_dilate_density_mul_min` for the weight `min(1, ‖z‖^θ)`: the
substitution `y = s • z` turns `∫ c g(s⁻¹ y) min(1, ‖y‖^θ) dy` into
`c s² ∫ g(z) min(1, s^θ ‖z‖^θ) dz`, and `min(1, s^θ r^θ) ≤ max(1, s^θ) min(1, r^θ)`. -/
theorem integrable_dilate_mul_min_rpow {g : (Fin 2 → ℝ) → ℝ} {s c θ : ℝ} (hs : 0 < s)
    (hθ : 0 ≤ θ) (hgm : Measurable g) (hg₀ : ∀ z, 0 ≤ g z)
    (hgmom : Integrable fun z => g z * min 1 (‖z‖ ^ θ)) :
    Integrable fun y => c * g (s⁻¹ • y) * min 1 (‖y‖ ^ θ) := by
  have hmain : Integrable fun y : Fin 2 → ℝ => g (s⁻¹ • y) * min 1 (‖y‖ ^ θ) := by
    refine (integrable_comp_smul_iff volume _ hs.ne').mp ?_
    have hm : Measurable fun z : Fin 2 → ℝ => g (s⁻¹ • s • z) :=
      hgm.comp ((measurable_const_smul s⁻¹).comp (measurable_const_smul s))
    have hc : Continuous fun z : Fin 2 → ℝ => min 1 (‖s • z‖ ^ θ) :=
      continuous_const.min ((continuous_norm.comp (continuous_const_smul s)).rpow_const
        fun _ => Or.inr hθ)
    refine (hgmom.const_mul (max 1 (s ^ θ))).mono'
      (hm.aestronglyMeasurable.mul hc.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    have h0 : (0 : ℝ) ≤ min 1 (‖s • z‖ ^ θ) :=
      le_min zero_le_one (Real.rpow_nonneg (norm_nonneg _) _)
    have hnorm : ‖s • z‖ ^ θ = s ^ θ * ‖z‖ ^ θ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, Real.mul_rpow hs.le (norm_nonneg z)]
    rw [inv_smul_smul₀ hs.ne', Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg₀ z) h0), hnorm]
    calc g z * min 1 (s ^ θ * ‖z‖ ^ θ)
        ≤ g z * (max 1 (s ^ θ) * min 1 (‖z‖ ^ θ)) :=
          mul_le_mul_of_nonneg_left
            (min_one_mul_le (Real.rpow_nonneg (norm_nonneg z) θ))
            (hg₀ z)
      _ = _ := by ring
  exact (hmain.const_mul c).congr (Filter.Eventually.of_forall fun y => by ring)

/-! ### The joint integrability hypothesis from two moments of the density -/

/-- Splitting the weight for the Cauchy–Schwarz in the difference variable: the two factors
`‖z‖^{(2+α)/2}` and `‖z‖^{−(2+α)/2}` cancel away from the origin, and at the origin both sides
vanish because `P 0 = 0`. -/
private theorem weight_split_eq (g : (Fin 2 → ℝ) → ℝ) {P : (Fin 2 → ℝ) → ℝ≥0∞}
    (hP0 : P 0 = 0) (α : ℝ) (z : Fin 2 → ℝ) :
    ENNReal.ofReal (g z) * P z
      = ENNReal.ofReal (g z) * ENNReal.ofReal (‖z‖ ^ ((2 + α) / 2)) *
        (P z * ENNReal.ofReal (‖z‖ ^ (-(2 + α) / 2))) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [hP0]
  · have hz0 : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
    have hcancel : ENNReal.ofReal (‖z‖ ^ ((2 + α) / 2)) *
        ENNReal.ofReal (‖z‖ ^ (-(2 + α) / 2)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hz0.le _), ← Real.rpow_add hz0,
        show (2 + α) / 2 + -(2 + α) / 2 = 0 by ring, Real.rpow_zero, ENNReal.ofReal_one]
    calc ENNReal.ofReal (g z) * P z
        = ENNReal.ofReal (g z) * P z *
            (ENNReal.ofReal (‖z‖ ^ ((2 + α) / 2)) *
              ENNReal.ofReal (‖z‖ ^ (-(2 + α) / 2))) := by rw [hcancel, mul_one]
      _ = _ := by ring

/-- **The two-regime bound from the two moments of the density.** This is
`CenteredMaximal.Fractional.setLIntegral_conv_ne_top` with its pointwise majorant
`g ≤ A (r^{−p} + r^{−q})` replaced by the two integral conditions the majorant is only ever used to
produce: the first moment `∫ g min(1, ‖z‖^{2+α})` and the second moment
`∫ g² min(1, ‖z‖^{2+α})` are finite. The generator density of the comparison kernel is **not**
dominated by any `A (r^{−p} + r^{−q})` — outside the support of the kernel it blows up like the
inverse fifth root of the distance to the coordinate axes, see the module docstring — while both its
moments are finite, so this form is the one that applies to it.

Near the origin, Cauchy–Schwarz in `z` against the weight `‖z‖^{±(2+α)/2}` splits the integral into
the second moment of `g` and `|K| · [u]²`, by the Cauchy–Schwarz
`sq_setLIntegral_enorm_sub_le` on `K` and the difference-variable form
`gagliardo_eq_lintegral_sqIncrement` of the energy. Away from the origin no modulus is needed: the
increment is bounded by `2 ‖u‖₁` and the weight `min(1, ‖z‖^{2+α})` is `1`, so the first moment
finishes. -/
theorem setLIntegral_conv_ne_top_of_moments {g u : (Fin 2 → ℝ) → ℝ} {α : ℝ} (hα : 0 < 2 + α)
    (hgm : Measurable g) (hg₀ : ∀ z, 0 ≤ g z)
    (hmom1 : Integrable fun z => g z * min 1 (‖z‖ ^ (2 + α)))
    (hmom2 : Integrable fun z => g z ^ 2 * min 1 (‖z‖ ^ (2 + α)))
    (hum : Measurable u) (huint : Integrable u) (hgag : gagliardo α u ≠ ⊤)
    {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) :
    ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (g z) * ∫⁻ x in K, ‖u (x - z) - u x‖ₑ ≠ ⊤ := by
  have hKvol : volume K ≠ ⊤ := hK.measure_lt_top.ne
  set P : (Fin 2 → ℝ) → ℝ≥0∞ := fun z => ∫⁻ x in K, ‖u (x - z) - u x‖ₑ with hPdef
  have hPm : Measurable P := by
    have h : Measurable fun pt : (Fin 2 → ℝ) × (Fin 2 → ℝ) => ‖u (pt.2 - pt.1) - u pt.2‖ₑ := by
      fun_prop
    exact h.lintegral_prod_right' (ν := volume.restrict K)
  have hP0 : P 0 = 0 := by simp [hPdef]
  have hmin0 : ∀ z : Fin 2 → ℝ, 0 ≤ min 1 (‖z‖ ^ (2 + α)) := fun z =>
    le_min zero_le_one (Real.rpow_nonneg (norm_nonneg z) _)
  have hm1 : ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (g z * min 1 (‖z‖ ^ (2 + α))) ≠ ⊤ :=
    ((hasFiniteIntegral_iff_ofReal
      (.of_forall fun z => mul_nonneg (hg₀ z) (hmin0 z))).1 hmom1.hasFiniteIntegral).ne
  have hm2 : ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (g z ^ 2 * min 1 (‖z‖ ^ (2 + α))) ≠ ⊤ :=
    ((hasFiniteIntegral_iff_ofReal
      (.of_forall fun z => mul_nonneg (sq_nonneg _) (hmin0 z))).1 hmom2.hasFiniteIntegral).ne
  set N : Set (Fin 2 → ℝ) := {z | ‖z‖ ≤ 1} with hNdef
  have hNm : MeasurableSet N := measurableSet_le measurable_norm measurable_const
  -- the near regime: two Cauchy–Schwarz inequalities and the Gagliardo energy
  have hnear : ∫⁻ z in N, ENNReal.ofReal (g z) * P z ≠ ⊤ := by
    have hfm : Measurable fun z : Fin 2 → ℝ =>
        ENNReal.ofReal (g z) * ENNReal.ofReal (‖z‖ ^ ((2 + α) / 2)) :=
      (ENNReal.measurable_ofReal.comp hgm).mul
        (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _))
    have hhm : Measurable fun z : Fin 2 → ℝ => P z * ENNReal.ofReal (‖z‖ ^ (-(2 + α) / 2)) :=
      hPm.mul (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _))
    have hCS := ENNReal.sq_lintegral_mul_le (μ := volume.restrict N)
      hfm.aemeasurable hhm.aemeasurable
    have hLHS : ∫⁻ z in N, ENNReal.ofReal (g z) * P z
        = ∫⁻ z in N, ENNReal.ofReal (g z) * ENNReal.ofReal (‖z‖ ^ ((2 + α) / 2)) *
            (P z * ENNReal.ofReal (‖z‖ ^ (-(2 + α) / 2))) :=
      lintegral_congr fun z => weight_split_eq g hP0 α z
    have hfin1 : ∫⁻ z in N,
        (ENNReal.ofReal (g z) * ENNReal.ofReal (‖z‖ ^ ((2 + α) / 2))) ^ 2 ≠ ⊤ := by
      refine ne_top_of_le_ne_top hm2
        ((setLIntegral_mono' hNm fun z hz => ?_).trans (setLIntegral_le_lintegral _ _))
      rcases eq_or_ne z 0 with rfl | hz0
      · rw [norm_zero, Real.zero_rpow (by linarith : (2 + α) / 2 ≠ 0)]
        simp
      · have hminz : min 1 (‖z‖ ^ (2 + α)) = ‖z‖ ^ (2 + α) :=
          min_eq_right (Real.rpow_le_one (norm_nonneg z) hz hα.le)
        rw [hminz, mul_pow, ← ENNReal.ofReal_pow (hg₀ z),
          ofReal_rpow_half_sq (norm_nonneg z) (2 + α), ← ENNReal.ofReal_mul (sq_nonneg _)]
    have hfin2 : ∫⁻ z in N, (P z * ENNReal.ofReal (‖z‖ ^ (-(2 + α) / 2))) ^ 2
        ≤ volume K * gagliardo α u := by
      calc ∫⁻ z in N, (P z * ENNReal.ofReal (‖z‖ ^ (-(2 + α) / 2))) ^ 2
          ≤ ∫⁻ z : Fin 2 → ℝ,
              volume K * (sqIncrement u z * ENNReal.ofReal (‖z‖ ^ (-(2 + α)))) := by
            refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun z => ?_)
            rw [mul_pow, ofReal_rpow_half_sq (norm_nonneg z) (-(2 + α)), ← mul_assoc]
            gcongr
            exact sq_setLIntegral_enorm_sub_le hum K z
        _ = volume K * gagliardo α u := by
            rw [gagliardo_eq_lintegral_sqIncrement hum α, lintegral_const_mul' _ _ hKvol]
    have hsq : (∫⁻ z in N, ENNReal.ofReal (g z) * P z) ^ 2 ≠ ⊤ := by
      rw [hLHS]
      exact ne_top_of_le_ne_top
        (ENNReal.mul_ne_top hfin1
          (ne_top_of_le_ne_top (ENNReal.mul_ne_top hKvol hgag) hfin2)) hCS
    exact fun h => hsq (by simp [h])
  -- the far regime: no modulus of continuity at all, just `‖u‖₁`
  have hfar : ∫⁻ z in Nᶜ, ENNReal.ofReal (g z) * P z ≠ ⊤ := by
    have hL : ∫⁻ x : Fin 2 → ℝ, ‖u x‖ₑ ≠ ⊤ :=
      (hasFiniteIntegral_iff_enorm.1 huint.hasFiniteIntegral).ne
    have hPle : ∀ z : Fin 2 → ℝ, P z ≤ 2 * ∫⁻ x : Fin 2 → ℝ, ‖u x‖ₑ := by
      intro z
      calc P z ≤ ∫⁻ x : Fin 2 → ℝ, ‖u (x - z) - u x‖ₑ := setLIntegral_le_lintegral _ _
        _ ≤ ∫⁻ x : Fin 2 → ℝ, (‖u (x - z)‖ₑ + ‖u x‖ₑ) := lintegral_mono fun _ => enorm_sub_le
        _ = (∫⁻ x : Fin 2 → ℝ, ‖u (x - z)‖ₑ) + ∫⁻ x : Fin 2 → ℝ, ‖u x‖ₑ :=
            lintegral_add_left (by fun_prop) _
        _ = 2 * ∫⁻ x : Fin 2 → ℝ, ‖u x‖ₑ := by
            rw [lintegral_sub_right_eq_self (fun x : Fin 2 → ℝ => ‖u x‖ₑ) z, two_mul]
    have hbd : ∀ z ∈ Nᶜ, ENNReal.ofReal (g z) * P z
        ≤ 2 * (∫⁻ x : Fin 2 → ℝ, ‖u x‖ₑ) *
            ENNReal.ofReal (g z * min 1 (‖z‖ ^ (2 + α))) := by
      intro z hz
      have hz1 : 1 < ‖z‖ := not_le.1 hz
      rw [min_eq_left (Real.one_le_rpow hz1.le hα.le), mul_one]
      calc ENNReal.ofReal (g z) * P z
          ≤ ENNReal.ofReal (g z) * (2 * ∫⁻ x : Fin 2 → ℝ, ‖u x‖ₑ) := by gcongr; exact hPle z
        _ = 2 * (∫⁻ x : Fin 2 → ℝ, ‖u x‖ₑ) * ENNReal.ofReal (g z) := by ring
    refine ne_of_lt (lt_of_le_of_lt (setLIntegral_mono' hNm.compl hbd)
      (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) ?_))
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) hL)]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (ENNReal.mul_ne_top (by norm_num) hL))
      (lt_top_iff_ne_top.2 hm1)
  rw [← lintegral_add_compl _ hNm]
  exact ENNReal.add_ne_top.2 ⟨hnear, hfar⟩

/-- **`hgconv` from the two moments of the density and finite jump energy.** The replacement for
`CenteredMaximal.Fractional.hgconv_of_jumpEnergy_six_fifths` that the comparison density satisfies:
the pointwise majorant is traded for the first and second moments of the density against
`min(1, ‖z‖^{2+α})`. -/
theorem hgconv_of_moments {g u : (Fin 2 → ℝ) → ℝ} {α θ : ℝ} (hα : 0 < α) (hθ : θ = 2 + α)
    (hgm : Measurable g) (hg₀ : ∀ z, 0 ≤ g z)
    (hmom1 : Integrable fun z => g z * min 1 (‖z‖ ^ θ))
    (hmom2 : Integrable fun z => g z ^ 2 * min 1 (‖z‖ ^ θ))
    (hum : Measurable u) (huint : Integrable u) (hE : jumpEnergy α u ≠ ⊤) :
    ∀ w : (Fin 2 → ℝ) → ℝ, IsTestFunction w →
      Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        g p.2 * ((u (p.1 - p.2) - u p.1) * w p.1)) (volume.prod volume) := by
  subst hθ
  have hgag : gagliardo α u ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE)
      (gagliardo_le_jumpEnergy hum hα)
  exact hgconv_of_setLIntegral_ne_top hgm hg₀ hum fun _ hK =>
    setLIntegral_conv_ne_top_of_moments (by linarith) hgm hg₀ hmom1 hmom2 hum huint hgag hK

/-! ### The pointwise step -/

/-- **The pointwise bound at every scale.** Let `f` be a bounded, nonnegative, compactly supported
measurable obstacle and `λ > 0` a level. Solving the obstacle problem of order `6/5` with cap
`κ = λ / ∫ K` produces a nonnegative `u` of finite jump energy and a density `σ ∈ [0, κ]` with
`A u = σ − f` weakly, and the contact set `Ω = {u > 0}` has measure at most
`(∫ f) / κ = (∫ K) (∫ f) / λ`. For each scale `s > 0` the dilation `K_s` again represents the
generator against the dilated density (`integral_dilate_mul_jumpGen`), whose Lévy moment is
`integrable_dilate_density_mul_min` and whose joint integrability is
`hgconv_of_jumpEnergy_six_fifths`, so `convolution_le_of_eq_zero_fp` bounds `K_s ⋆ f` by
`κ ∫ K_s = λ` at almost every point where `u` vanishes.

The obstacle problem only provides `0 ≤ u` almost everywhere, while the transfer needs it
pointwise, so `u` is replaced by its positive part; this changes neither the contact set nor any
integral, and `jumpEnergy_congr_ae` carries the energy along. -/
theorem exists_exceptional_set_frac
    (hpos : ∀ z, z ≠ 0 → 0 ≤ fracKernel z) (hgen : 0 ≤ᵐ[volume] fracDensity)
    (hsq : Integrable fun z => fracDensity z ^ 2 * min 1 (‖z‖ ^ (16 / 5 : ℝ)))
    (f : (Fin 2 → ℝ) → ℝ) (Mf b : ℝ) (hfm : Measurable f) (hf₀ : ∀ x, 0 ≤ f x)
    (hfM : ∀ x, f x ≤ Mf) (hfsupp : ∀ x, b < ‖x‖ → f x = 0) (hb : 0 < b) (lam : ℝ)
    (hlam : 0 < lam) :
    ∃ Ω : Set (Fin 2 → ℝ), MeasurableSet Ω ∧
      volume Ω ≤ ENNReal.ofReal ((∫ x, fracComp x) * (∫ x, f x) / lam) ∧
      ∀ s : ℝ, 0 < s → ∀ᵐ x, x ∉ Ω → (∫ y, dilate fracComp s (x - y) * f y) ≤ lam := by
  have hMpos : 0 < ∫ x, fracComp x := integral_fracComp_pos
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = lam / (∫ x, fracComp x) := ⟨_, rfl⟩
  have hκ : 0 < κ := by
    rw [hκdef]
    exact div_pos hlam hMpos
  -- a bounded measurable function supported in a cube is integrable
  have hfint : Integrable f := by
    have hg : Integrable ((closedBall (0 : Fin 2 → ℝ) b).indicator fun _ => Mf) volume :=
      (integrableOn_const (volume_closedBall_ne_top hb.le)).integrable_indicator
        measurableSet_closedBall
    refine hg.mono' hfm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf₀ x)]
    by_cases hx : x ∈ closedBall (0 : Fin 2 → ℝ) b
    · rw [indicator_of_mem hx]
      exact hfM x
    · rw [indicator_of_notMem hx, hfsupp x (by simpa [mem_closedBall, dist_eq_norm] using hx)]
  obtain ⟨u, σ, hum, hu₀ae, huint, hσm, hσ₀, hσκ, hσint, hweak, -, -, hvolu, hE⟩ :=
    exists_obstacle_solution (α := 6 / 5) (by norm_num) (by norm_num) hκ hfm hf₀ hfM hb hfsupp
  -- the positive part of the minimiser, nonnegative pointwise rather than almost everywhere
  obtain ⟨uPos, hupdef⟩ : ∃ v : (Fin 2 → ℝ) → ℝ, v = fun x => max (u x) 0 := ⟨_, rfl⟩
  have hupapp : ∀ x, uPos x = max (u x) 0 := fun x => by rw [hupdef]
  have hupm : Measurable uPos := by
    rw [hupdef]
    exact hum.max measurable_const
  have hup₀ : ∀ x, 0 ≤ uPos x := fun x => by
    rw [hupapp x]
    exact le_max_right _ _
  have hupeq : uPos =ᵐ[volume] u := by
    filter_upwards [hu₀ae] with x hx
    rw [hupapp x]
    exact max_eq_left hx
  have hupint : Integrable uPos := huint.congr hupeq.symm
  have hupE : jumpEnergy (6 / 5) uPos ≠ ⊤ := by
    rw [jumpEnergy_congr_ae (6 / 5) hupeq]
    exact hE
  have hupweak : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      (∫ x, uPos x * jumpGen (6 / 5) ψ x) = ∫ x, (σ x - f x) * ψ x := by
    intro ψ hψ
    have heq : (fun x => uPos x * jumpGen (6 / 5) ψ x)
        =ᵐ[volume] fun x => u x * jumpGen (6 / 5) ψ x := by
      filter_upwards [hupeq] with x hx
      rw [hx]
    exact (integral_congr_ae heq).trans (hweak ψ hψ)
  refine ⟨{x | 0 < uPos x}, measurableSet_lt measurable_const hupm, ?_, ?_⟩
  · -- the contact set is the same for `u` and for its positive part
    have hset : {x | 0 < uPos x} = {x | 0 < u x} := by
      ext x
      simp [hupapp]
    have harith : (∫ x, f x) / κ = (∫ x, fracComp x) * (∫ x, f x) / lam := by
      rw [hκdef, div_div_eq_mul_div]
      ring
    rw [hset]
    exact hvolu.trans (le_of_eq (by rw [harith]))
  · intro s hs
    -- the dilated density, its moment, its model bound and its generator identity
    have hc : (0 : ℝ) ≤ s ^ (-2 - 6 / 5 : ℝ) := Real.rpow_nonneg hs.le _
    have hgm : Measurable fun y : Fin 2 → ℝ => s ^ (-2 - 6 / 5 : ℝ) * fracGen (s⁻¹ • y) :=
      (measurable_fracGen.comp (measurable_const_smul s⁻¹)).const_mul _
    have hg₀ : ∀ y : Fin 2 → ℝ, 0 ≤ s ^ (-2 - 6 / 5 : ℝ) * fracGen (s⁻¹ • y) := fun y =>
      mul_nonneg hc (fracGen_nonneg _)
    have hgmom : Integrable fun y : Fin 2 → ℝ =>
        s ^ (-2 - 6 / 5 : ℝ) * fracGen (s⁻¹ • y) * min 1 ‖y‖ :=
      integrable_dilate_density_mul_min hs measurable_fracGen fracGen_nonneg
        (integrable_fracGen_mul_min_one hgen)
    have hmom1 : Integrable fun y : Fin 2 → ℝ =>
        s ^ (-2 - 6 / 5 : ℝ) * fracGen (s⁻¹ • y) * min 1 (‖y‖ ^ (16 / 5 : ℝ)) :=
      integrable_dilate_mul_min_rpow hs (by norm_num) measurable_fracGen fracGen_nonneg
        (integrable_fracGen_mul_min_one_rpow hgen)
    have hmom2 : Integrable fun y : Fin 2 → ℝ =>
        (s ^ (-2 - 6 / 5 : ℝ) * fracGen (s⁻¹ • y)) ^ 2 * min 1 (‖y‖ ^ (16 / 5 : ℝ)) := by
      refine (integrable_dilate_mul_min_rpow (g := fun z => fracGen z ^ 2)
        (c := (s ^ (-2 - 6 / 5 : ℝ)) ^ 2) hs (by norm_num) (measurable_fracGen.pow_const 2)
        (fun z => sq_nonneg _)
        (integrable_fracGen_sq_mul_min_one_rpow hgen hsq)).congr ?_
      exact Filter.Eventually.of_forall fun y => by ring
    have hgconv := hgconv_of_moments (α := 6 / 5) (by norm_num) (by norm_num) hgm hg₀ hmom1 hmom2
      hupm hupint hupE
    have hgen' : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
        (∫ x, dilate fracComp s x * jumpGen (6 / 5) ψ x)
          = ∫ y, s ^ (-2 - 6 / 5 : ℝ) * fracGen (s⁻¹ • y) * (ψ y - ψ 0) := fun ψ hψ =>
      integral_dilate_mul_jumpGen hs integrable_fracComp (fun _ h => hKgen_fracComp hgen h) hψ
    have hkey := convolution_le_of_eq_zero_fp (α := 6 / 5) (by norm_num) (by norm_num)
      (fun z => dilate_nonneg (fun w => fracComp_nonneg hpos w) hs z)
      (integrable_dilate integrable_fracComp hs) (dilate_fracComp_neg s)
      (hasCompactSupport_dilate_fracComp hs) hupm hupint hup₀ hσm hσint hσ₀ hσκ hfint
      hgm hg₀ hgmom hgconv hupweak hgen'
    have hlamEq : κ * (∫ y, dilate fracComp s y) = lam := by
      rw [integral_dilate_eq (fun z => fracComp_nonneg hpos z) integrable_fracComp hs, hκdef,
        div_mul_cancel₀ lam hMpos.ne']
    -- the convolution written with the kernel translated instead of the obstacle
    have hflip : ∀ x : Fin 2 → ℝ, (∫ y, dilate fracComp s y * f (x - y))
        = ∫ y, dilate fracComp s (x - y) * f y := fun x =>
      calc (∫ y, dilate fracComp s y * f (x - y))
          = ∫ y, dilate fracComp s (x - y) * f (x - (x - y)) :=
            (integral_sub_left_eq_self
              (fun y => dilate fracComp s y * f (x - y)) volume x).symm
        _ = ∫ y, dilate fracComp s (x - y) * f y :=
            integral_congr_ae (Filter.Eventually.of_forall fun y => by
              simp only [sub_sub_cancel])
    filter_upwards [hkey] with x hx hxΩ
    have hnot : ¬ (0 < uPos x) := by simpa using hxΩ
    have hux : uPos x = 0 := le_antisymm (not_lt.1 hnot) (hup₀ x)
    rw [← hflip x, ← hlamEq]
    exact hx hux

/-! ### The weak type bound -/

/-- `ofReal (2 c) / 2 = ofReal c` in `ℝ≥0∞`, in the shape produced by the diamond reduction. -/
private theorem ofReal_two_mul_div_two (c : ℝ) :
    ENNReal.ofReal (2 * c) / 2 = ENNReal.ofReal c := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_div_assoc,
    ENNReal.mul_div_cancel (by simp) (by simp)]

/-- **The weak type bound for the centred maximal operator over cubes in the plane, from the
`α = 6/5` certificate.** If the comparison kernel is nonnegative off the origin and at least `1` on
the punctured unit diamond, and if its generator density is almost everywhere nonnegative and
carries the `L²` moment `∫ g² min(1, ‖z‖^{16/5}) < ∞`, then `c₂ ≤ ½ ∫ K < 3.622`.

The pointwise step `exists_exceptional_set_frac` feeds `isKernelWeakTypeBound_of_pointwise`, which
gives the weak type bound `∫ K` for the kernel maximal operator; since `K ≥ 1` on the unit
*diamond*, `weakTypeConstant_two_le_of_diamond` halves it, and the mass bound
`fracKernel_mass_lt` closes it. -/
theorem weakTypeConstant_two_le_frac
    (hpos : ∀ z, z ≠ 0 → 0 ≤ fracKernel z)
    (hone : ∀ z, z ≠ 0 → diamondNorm z ≤ 1 → 1 ≤ fracKernel z)
    (hgen : 0 ≤ᵐ[volume] fracDensity)
    (hsq : Integrable fun z => fracDensity z ^ 2 * min 1 (‖z‖ ^ (16 / 5 : ℝ))) :
    weakTypeConstant 2 ≤ ENNReal.ofReal (3622 / 1000) := by
  have hwt : IsKernelWeakTypeBound fracComp (ENNReal.ofReal (∫ x, fracComp x)) :=
    isKernelWeakTypeBound_of_pointwise (fun z => fracComp_nonneg hpos z) integrable_fracComp
      fun g Mg c hgm hg₀ hgM hgsupp hc lam hlam =>
        exists_exceptional_set_frac hpos hgen hsq g Mg c hgm hg₀ hgM hgsupp hc lam hlam
  have h := weakTypeConstant_two_le_of_diamond integrable_fracComp
    (fun z hz => one_le_fracComp hone hz) hwt
  refine h.trans ?_
  calc ENNReal.ofReal (∫ x, fracComp x) / 2
      ≤ ENNReal.ofReal (2 * (3622 / 1000)) / 2 :=
        ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal integral_fracComp_lt.le) 2
    _ = ENNReal.ofReal (3622 / 1000) := ofReal_two_mul_div_two _

end CenteredMaximal.Fractional

end

end
