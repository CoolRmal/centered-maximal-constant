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

and the two facts about the generator density `fracDensity = jumpGen (6/5) fracKernel`, namely that
it is almost everywhere nonnegative and that it is dominated by
`A (r^{−12/5} + r^{−11/5})` away from the origin. All four enter every theorem of the last section
as hypotheses.

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
* `fracGen_le`, `dilate_density_le`: the model bound `A (r^{−12/5} + r^{−11/5})` for the patched
  density and for its dilations, the form `hgconv_of_jumpEnergy_six_fifths` consumes;
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

/-- The model bound for the patched density: the positive part only ever decreases it, and the
majorant is nonnegative. -/
theorem fracGen_le {A : ℝ} (hA : 0 ≤ A)
    (hbd : ∀ z, z ≠ 0 → fracDensity z ≤ A * (diamondNorm z ^ (-(12 / 5) : ℝ)
      + diamondNorm z ^ (-(11 / 5) : ℝ)))
    {z : Fin 2 → ℝ} (hz : z ≠ 0) :
    fracGen z ≤ A * (diamondNorm z ^ (-(12 / 5) : ℝ) + diamondNorm z ^ (-(11 / 5) : ℝ)) :=
  max_le (hbd z hz)
    (mul_nonneg hA (add_nonneg (Real.rpow_nonneg (diamondNorm_nonneg z) _)
      (Real.rpow_nonneg (diamondNorm_nonneg z) _)))

/-! ### The model bound survives dilation -/

/-- The diamond radius scales, so a negative power of it picks up a positive power of the scale. -/
private theorem diamond_rpow_inv_smul {s p : ℝ} (hs : 0 < s) (z : Fin 2 → ℝ) :
    diamondNorm (s⁻¹ • z) ^ (-p) = s ^ p * diamondNorm z ^ (-p) := by
  rw [diamondNorm_smul, abs_of_pos (inv_pos.2 hs),
    Real.mul_rpow (by positivity) (diamondNorm_nonneg z), Real.inv_rpow hs.le,
    Real.rpow_neg hs.le p, inv_inv]

/-- **The model bound survives dilation.** A density dominated by `A (r^{−12/5} + r^{−11/5})` away
from the origin is carried by `y ↦ c g (s⁻¹ • y)` into a density of the same form, with the
constant `c A max(s^{12/5}, s^{11/5})`. -/
theorem dilate_density_le {g : (Fin 2 → ℝ) → ℝ} {A s c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hs : 0 < s)
    (hg : ∀ z, z ≠ 0 → g z ≤ A * (diamondNorm z ^ (-(12 / 5) : ℝ)
      + diamondNorm z ^ (-(11 / 5) : ℝ)))
    {y : Fin 2 → ℝ} (hy : y ≠ 0) :
    c * g (s⁻¹ • y) ≤ c * A * max (s ^ (12 / 5 : ℝ)) (s ^ (11 / 5 : ℝ))
      * (diamondNorm y ^ (-(12 / 5) : ℝ) + diamondNorm y ^ (-(11 / 5) : ℝ)) := by
  have hy' : s⁻¹ • y ≠ 0 := smul_ne_zero (inv_ne_zero hs.ne') hy
  have hX : (0 : ℝ) ≤ diamondNorm y ^ (-(12 / 5) : ℝ) := Real.rpow_nonneg (diamondNorm_nonneg y) _
  have hY : (0 : ℝ) ≤ diamondNorm y ^ (-(11 / 5) : ℝ) := Real.rpow_nonneg (diamondNorm_nonneg y) _
  have h₁ : s ^ (12 / 5 : ℝ) * diamondNorm y ^ (-(12 / 5) : ℝ)
      ≤ max (s ^ (12 / 5 : ℝ)) (s ^ (11 / 5 : ℝ)) * diamondNorm y ^ (-(12 / 5) : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hX
  have h₂ : s ^ (11 / 5 : ℝ) * diamondNorm y ^ (-(11 / 5) : ℝ)
      ≤ max (s ^ (12 / 5 : ℝ)) (s ^ (11 / 5 : ℝ)) * diamondNorm y ^ (-(11 / 5) : ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hY
  have hstep : g (s⁻¹ • y) ≤ A * (max (s ^ (12 / 5 : ℝ)) (s ^ (11 / 5 : ℝ))
      * (diamondNorm y ^ (-(12 / 5) : ℝ) + diamondNorm y ^ (-(11 / 5) : ℝ))) := by
    refine (hg _ hy').trans ?_
    rw [diamond_rpow_inv_smul hs, diamond_rpow_inv_smul hs]
    have := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) hA
    calc A * (s ^ (12 / 5 : ℝ) * diamondNorm y ^ (-(12 / 5) : ℝ)
            + s ^ (11 / 5 : ℝ) * diamondNorm y ^ (-(11 / 5) : ℝ))
        ≤ A * (max (s ^ (12 / 5 : ℝ)) (s ^ (11 / 5 : ℝ)) * diamondNorm y ^ (-(12 / 5) : ℝ)
            + max (s ^ (12 / 5 : ℝ)) (s ^ (11 / 5 : ℝ)) * diamondNorm y ^ (-(11 / 5) : ℝ)) := this
      _ = _ := by ring
  calc c * g (s⁻¹ • y)
      ≤ c * (A * (max (s ^ (12 / 5 : ℝ)) (s ^ (11 / 5 : ℝ))
          * (diamondNorm y ^ (-(12 / 5) : ℝ) + diamondNorm y ^ (-(11 / 5) : ℝ)))) :=
        mul_le_mul_of_nonneg_left hstep hc
    _ = _ := by ring

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
theorem exists_exceptional_set_frac {A : ℝ} (hA : 0 ≤ A)
    (hpos : ∀ z, z ≠ 0 → 0 ≤ fracKernel z) (hgen : 0 ≤ᵐ[volume] fracDensity)
    (hbd : ∀ z, z ≠ 0 → fracDensity z ≤ A * (diamondNorm z ^ (-(12 / 5) : ℝ)
      + diamondNorm z ^ (-(11 / 5) : ℝ)))
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
    have hgbd : ∀ y : Fin 2 → ℝ, y ≠ 0 → s ^ (-2 - 6 / 5 : ℝ) * fracGen (s⁻¹ • y)
        ≤ s ^ (-2 - 6 / 5 : ℝ) * A * max (s ^ (12 / 5 : ℝ)) (s ^ (11 / 5 : ℝ))
          * (diamondNorm y ^ (-(12 / 5) : ℝ) + diamondNorm y ^ (-(11 / 5) : ℝ)) :=
      fun y hy => dilate_density_le hA hc hs (fun z hz => fracGen_le hA hbd hz) hy
    have hgconv := hgconv_of_jumpEnergy_six_fifths hgm hg₀ hgbd hupm hupint hupE
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
`α = 6/5` certificate.** If the comparison kernel is nonnegative off the origin, at least `1` on
the punctured unit diamond, and its generator density is almost everywhere nonnegative and
dominated by `A (r^{−12/5} + r^{−11/5})` off the origin, then `c₂ ≤ ½ ∫ K < 3.622`.

The pointwise step `exists_exceptional_set_frac` feeds `isKernelWeakTypeBound_of_pointwise`, which
gives the weak type bound `∫ K` for the kernel maximal operator; since `K ≥ 1` on the unit
*diamond*, `weakTypeConstant_two_le_of_diamond` halves it, and the mass bound
`fracKernel_mass_lt` closes it. -/
theorem weakTypeConstant_two_le_frac {A : ℝ} (hA : 0 ≤ A)
    (hpos : ∀ z, z ≠ 0 → 0 ≤ fracKernel z)
    (hone : ∀ z, z ≠ 0 → diamondNorm z ≤ 1 → 1 ≤ fracKernel z)
    (hgen : 0 ≤ᵐ[volume] fracDensity)
    (hbd : ∀ z, z ≠ 0 → fracDensity z ≤ A * (diamondNorm z ^ (-(12 / 5) : ℝ)
      + diamondNorm z ^ (-(11 / 5) : ℝ))) :
    weakTypeConstant 2 ≤ ENNReal.ofReal (3622 / 1000) := by
  have hwt : IsKernelWeakTypeBound fracComp (ENNReal.ofReal (∫ x, fracComp x)) :=
    isKernelWeakTypeBound_of_pointwise (fun z => fracComp_nonneg hpos z) integrable_fracComp
      fun g Mg c hgm hg₀ hgM hgsupp hc lam hlam =>
        exists_exceptional_set_frac hA hpos hgen hbd g Mg c hgm hg₀ hgM hgsupp hc lam hlam
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
