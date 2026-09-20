/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.AntiRadial

/-!
# The full reserve of the truncated base's generator

`CenteredMaximal.Fractional.jumpGen_truncBase_ge_radial` adds the *radial* reserve of the exterior
tail onto the intrinsic power term of the generator of the truncated diamond base, keeping one of
the two displaced points of each coordinate direction.  This file adds the other one, using the
anti-radial minorant of `CenteredMaximal.Fractional.AntiRadial`, and states the resulting bound in
the rational form a certificate leaf consumes.

## Which point is which

At `z` with `u = |z₀|`, `v = |z₁|`, the `j`-th second difference of the exterior tail is the *sum*
of the two displaced values, because the tail itself vanishes inside the diamond.  The two
displaced radii are `|z j ± t| + |z (j+1)|`, and

* their **maximum** is `u + v + |t| = r + |t|`  (`le_max_diamondNorm_single`), which is what
  `tailRadial` reads, and
* both are at least `|t| − (|z j| − |z (j+1)|)`, because `|a ± t| ≥ |t| − |a|`, which is what
  `antiRadial` reads — so their **minimum** is too.

Since `max + min = a + b`, the two minorants may be added: one is paid for by the larger displaced
value and the other by the smaller.  Interchanging the two coordinate directions replaces the shift
`d = u − v` by `−d`, which is exactly the pair of opposite shifts that `integral_antiRadial_pair_ge`
bounds below by a partial sum of the *even* tail series.

## Main results

* `antiRadial_le_truncTail`: the anti-radial minorant against one displaced value.
* `tailRadial_add_antiRadial_le_secondDiff`: **the pointwise reserve**, both minorants at once.
* `jumpGen_truncTail_ge_full`: the two reserves as integrals.
* `jumpGen_truncBase_ge_full`, `jumpGen_truncBase_ge_series`: **the bound a leaf consumes**, the
  intrinsic power term plus two partial sums with explicit rational coefficients.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### The anti-radial minorant against one displaced value -/

/-- **The anti-radial minorant is below the tail at any point far enough out.**  Below the
truncation radius there is nothing to prove, the minorant being `0` there; above it this is the
monotonicity of the tail in the diamond radius. -/
theorem antiRadial_le_truncTail {α R w t : ℝ} (hα : 0 < α) (hR : 0 < R) {x : Fin 2 → ℝ}
    (hx : |t| - w ≤ diamondNorm x) : antiRadial α R w t ≤ truncTail α R x := by
  have hρ0 : 0 < max (|t| - w) R := lt_of_lt_of_le hR (le_max_right _ _)
  rcases le_or_gt (diamondNorm x) R with h | h
  · rw [antiRadial_of_le (le_trans hx h)]
    exact truncTail_nonneg α R x
  · exact tailRadial_le_truncTail hα hρ0 (max_le hx h.le)

/-! ### The diamond radius along a coordinate line -/

private theorem diamondNorm_addSingle (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z + s • Pi.single j 1) = |z j + s| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem diamondNorm_subSingle (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z - s • Pi.single j 1) = |z j - s| + |z (j + 1)| := by
  rw [sub_eq_add_neg, ← neg_smul, diamondNorm_addSingle, ← sub_eq_add_neg]

/-- `|t| − |a| ≤ |a + t|`, the inequality that puts the *smaller* displaced radius above the
anti-radial shift. -/
private theorem sub_abs_le_abs_add (a t : ℝ) : |t| - |a| ≤ |a + t| := by
  have h := abs_sub_abs_le_abs_sub t (-a)
  rwa [abs_neg, sub_neg_eq_add, add_comm t a] at h

private theorem sub_abs_le_abs_sub' (a t : ℝ) : |t| - |a| ≤ |a - t| := by
  have h := abs_sub_abs_le_abs_sub t a
  rwa [abs_sub_comm t a] at h

/-! ### The pointwise reserve -/

/-- **The pointwise reserve, both minorants at once.**  At a point of the punctured closed diamond
the `j`-th second difference of the exterior tail is the sum of its two displaced values; the
larger pays for the radial minorant and the smaller for the anti-radial one, and `max + min` is
their sum. -/
theorem tailRadial_add_antiRadial_le_secondDiff {α R : ℝ} (hα : 0 < α) (hR : 0 < R)
    {z : Fin 2 → ℝ} (hz0 : z ≠ 0) (hz : diamondNorm z ≤ R) (j : Fin 2) (t : ℝ) :
    tailRadial α R (diamondNorm z) t + antiRadial α R (|z j| - |z (j + 1)|) t
      ≤ secondDiff (truncTail α R) j z t := by
  have hzpos : 0 < diamondNorm z := diamondNorm_pos hz0
  have hρ : 0 < diamondNorm z + |t| := by positivity
  have hkey := le_max_diamondNorm_single z j t
  have hrad : tailRadial α R (diamondNorm z) t
      ≤ max (truncTail α R (z + t • Pi.single j 1)) (truncTail α R (z - t • Pi.single j 1)) := by
    rcases max_cases (diamondNorm (z + t • Pi.single j 1))
      (diamondNorm (z - t • Pi.single j 1)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hkey
    · exact (tailRadial_le_truncTail hα hρ hkey).trans (le_max_left _ _)
    · exact (tailRadial_le_truncTail hα hρ hkey).trans (le_max_right _ _)
  have hA : antiRadial α R (|z j| - |z (j + 1)|) t ≤ truncTail α R (z + t • Pi.single j 1) := by
    refine antiRadial_le_truncTail hα hR ?_
    rw [diamondNorm_addSingle]
    linarith [sub_abs_le_abs_add (z j) t]
  have hB : antiRadial α R (|z j| - |z (j + 1)|) t ≤ truncTail α R (z - t • Pi.single j 1) := by
    refine antiRadial_le_truncTail hα hR ?_
    rw [diamondNorm_subSingle]
    linarith [sub_abs_le_abs_sub' (z j) t]
  have hanti : antiRadial α R (|z j| - |z (j + 1)|) t
      ≤ min (truncTail α R (z + t • Pi.single j 1)) (truncTail α R (z - t • Pi.single j 1)) :=
    le_min hA hB
  rw [secondDiff, truncTail_eq_zero hα hz0 hz]
  rcases le_total (truncTail α R (z + t • Pi.single j 1))
    (truncTail α R (z - t • Pi.single j 1)) with h | h
  · rw [max_eq_right h] at hrad
    rw [min_eq_left h] at hanti
    linarith
  · rw [max_eq_left h] at hrad
    rw [min_eq_right h] at hanti
    linarith

/-- The anti-radial minorant alone is below the second difference, the radial one being
nonnegative. -/
theorem antiRadial_le_secondDiff {α R : ℝ} (hα : 0 < α) (hR : 0 < R) {z : Fin 2 → ℝ}
    (hz0 : z ≠ 0) (hz : diamondNorm z ≤ R) (j : Fin 2) (t : ℝ) :
    antiRadial α R (|z j| - |z (j + 1)|) t ≤ secondDiff (truncTail α R) j z t := by
  have h := tailRadial_add_antiRadial_le_secondDiff hα hR hz0 hz j t
  linarith [tailRadial_nonneg α R (diamondNorm z) t]

/-! ### Measurability of the two minorants -/

private theorem measurable_tailRadial_mul (α R r : ℝ) :
    Measurable fun t : ℝ => tailRadial α R r t * |t| ^ (-(1 + α)) := by
  have h1 : Measurable fun t : ℝ => (r + |t|) ^ (-α) :=
    (measurable_const.add continuous_abs.measurable).pow_const _
  exact ((measurable_const.sub h1).max measurable_const).mul
    (continuous_abs.measurable.pow_const _)

private theorem measurable_antiRadial_mul (α R w : ℝ) :
    Measurable fun t : ℝ => antiRadial α R w t * |t| ^ (-(1 + α)) := by
  have h1 : Measurable fun t : ℝ => (max (|t| - w) R) ^ (-α) :=
    ((continuous_abs.measurable.sub measurable_const).max measurable_const).pow_const _
  exact ((measurable_const.sub h1).max measurable_const).mul
    (continuous_abs.measurable.pow_const _)

/-! ### The two reserves as integrals -/

/-- **The full reserve of the exterior tail's generator.**  Both minorants are integrable, being
dominated by the integrable second difference, so the two directional bounds may be added. -/
theorem jumpGen_truncTail_ge_full {α R : ℝ} (hα : 0 < α) (hR : 0 < R) {z : Fin 2 → ℝ}
    (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (hz : diamondNorm z < R) :
    2 * (∫ t : ℝ, tailRadial α R (diamondNorm z) t * |t| ^ (-(1 + α)))
        + ((∫ t : ℝ, antiRadial α R (|z 0| - |z 1|) t * |t| ^ (-(1 + α)))
          + ∫ t : ℝ, antiRadial α R (-(|z 0| - |z 1|)) t * |t| ^ (-(1 + α)))
      ≤ jumpGen α (truncTail α R) z := by
  have hz0 : z ≠ 0 := fun h => h0 (by simp [h])
  have hw : ∀ t : ℝ, (0 : ℝ) ≤ |t| ^ (-(1 + α)) := fun t => Real.rpow_nonneg (abs_nonneg t) _
  have hrad : Integrable fun t : ℝ => tailRadial α R (diamondNorm z) t * |t| ^ (-(1 + α)) := by
    refine Integrable.mono' (integrable_secondDiff_truncTail hα h0 h1 hz 0)
      (measurable_tailRadial_mul _ _ _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (tailRadial_nonneg _ _ _ _) (hw t))]
    exact mul_le_mul_of_nonneg_right (tailRadial_le_secondDiff hα hz0 hz.le 0 t) (hw t)
  have hanti : ∀ j : Fin 2,
      Integrable fun t : ℝ => antiRadial α R (|z j| - |z (j + 1)|) t * |t| ^ (-(1 + α)) := by
    intro j
    refine Integrable.mono' (integrable_secondDiff_truncTail hα h0 h1 hz j)
      (measurable_antiRadial_mul _ _ _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (antiRadial_nonneg _ _ _ _) (hw t))]
    exact mul_le_mul_of_nonneg_right (antiRadial_le_secondDiff hα hR hz0 hz.le j t) (hw t)
  have hstep : ∀ j : Fin 2,
      (∫ t : ℝ, tailRadial α R (diamondNorm z) t * |t| ^ (-(1 + α)))
          + ∫ t : ℝ, antiRadial α R (|z j| - |z (j + 1)|) t * |t| ^ (-(1 + α))
        ≤ ∫ t : ℝ, secondDiff (truncTail α R) j z t * |t| ^ (-(1 + α)) := by
    intro j
    rw [← integral_add hrad (hanti j)]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => ?_)
      (integrable_secondDiff_truncTail hα h0 h1 hz j) (Filter.Eventually.of_forall fun t => ?_)
    · exact add_nonneg (mul_nonneg (tailRadial_nonneg _ _ _ _) (hw t))
        (mul_nonneg (antiRadial_nonneg _ _ _ _) (hw t))
    · have hcomb := tailRadial_add_antiRadial_le_secondDiff hα hR hz0 hz.le j t
      have := mul_le_mul_of_nonneg_right hcomb (hw t)
      nlinarith [this]
  have e0 : ((0 : Fin 2) + 1) = 1 := rfl
  have e1 : ((1 : Fin 2) + 1) = 0 := rfl
  have h00 := hstep 0
  have h11 := hstep 1
  rw [e0] at h00
  rw [e1] at h11
  rw [show -(|z 0| - |z 1|) = |z 1| - |z 0| from by ring]
  rw [jumpGen, Fin.sum_univ_two]
  linarith

/-! ### The bound a leaf consumes -/

/-- **The full reserve added onto the intrinsic power term.** -/
theorem jumpGen_truncBase_ge_full {α R : ℝ} (hα : 1 < α) (hα' : α < 2) (hR : 0 < R)
    {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (hz : diamondNorm z < R) :
    -4 * Real.pi * Real.Gamma (2 * α) * Real.cos (Real.pi * α / 2)
        / (α * Real.Gamma α ^ 2 * Real.sin (Real.pi * α / 2)) * diamondNorm z ^ (-2 * α)
        + 2 * (∫ t : ℝ, tailRadial α R (diamondNorm z) t * |t| ^ (-(1 + α)))
        + ((∫ t : ℝ, antiRadial α R (|z 0| - |z 1|) t * |t| ^ (-(1 + α)))
          + ∫ t : ℝ, antiRadial α R (-(|z 0| - |z 1|)) t * |t| ^ (-(1 + α)))
      ≤ jumpGen α (truncBase α R) z := by
  rw [jumpGen_truncBase hα hα' h0 h1 hz]
  linarith [jumpGen_truncTail_ge_full (by linarith : (0 : ℝ) < α) hR h0 h1 hz]

/-- **The rational form of the reserve.**  The intrinsic power term plus two partial sums: the
radial tail series at the diamond radius and the *even* tail series at the coordinate difference.
Both truncation orders are free, and at `α = 6/5` both coefficient sequences are exactly rational
(`tailCoeffQ`, `evenTailCoeffQ`). -/
theorem jumpGen_truncBase_ge_series {α R : ℝ} (hα : 1 < α) (hα' : α < 2) (hR : 0 < R)
    {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (hz : diamondNorm z < R) (K L : ℕ) :
    -4 * Real.pi * Real.Gamma (2 * α) * Real.cos (Real.pi * α / 2)
        / (α * Real.Gamma α ^ 2 * Real.sin (Real.pi * α / 2)) * diamondNorm z ^ (-2 * α)
        + 4 * R ^ (-2 * α) * ∑ n ∈ Finset.range K, tailCoeff α n * (diamondNorm z / R) ^ n
        + 4 * R ^ (-2 * α) *
            ∑ n ∈ Finset.range L, evenTailCoeff α n * ((|z 0| - |z 1|) / R) ^ n
      ≤ jumpGen α (truncBase α R) z := by
  have hα0 : 0 < α := by linarith
  have hz0 : z ≠ 0 := fun h => h0 (by simp [h])
  have hrpos : 0 < diamondNorm z := diamondNorm_pos hz0
  have hdn : diamondNorm z = |z 0| + |z 1| := rfl
  have hwR : |(|z 0| - |z 1|)| < R := by
    have ha0 := abs_nonneg (z 0)
    have ha1 := abs_nonneg (z 1)
    have hz' : |z 0| + |z 1| < R := by rwa [hdn] at hz
    rw [abs_sub_lt_iff]
    exact ⟨by linarith, by linarith⟩
  have hser := integral_tailRadial_ge (α := α) (R := R) (r := diamondNorm z) hα hα' hR
    hrpos.le hz K
  have hanti := integral_antiRadial_pair_ge (α := α) (R := R) (w := |z 0| - |z 1|) hα0 hwR L
  have hfull := jumpGen_truncBase_ge_full hα hα' hR h0 h1 hz
  linarith

end CenteredMaximal.Fractional

end

end
