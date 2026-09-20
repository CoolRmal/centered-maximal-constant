/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.KernelPositivity
public import CenteredMaximal.Fractional.RadialTangent

/-!
# Assembling one rectangle of the `α = 6/5` generator certificate

`CenteredMaximal.Fractional.jumpGen_fracKernel_sub_base` computes the generator of the *spline part*
of the comparison kernel and `CenteredMaximal.Fractional.jumpGen_truncBase_ge_radial` bounds the
generator of the *base part* below.  Nothing yet joins them, because `jumpGen` is additive only on
functions whose integrands are integrable.  This file supplies the missing integrability, the
resulting decomposition of `jumpGen (6/5) fracKernel`, and the leaf inequality the `4582` rectangle
rows discharge.

## Main results

* `secondDiff_truncBase`, `integrable_secondDiff_truncBase`: the truncated base's integrand is
  integrable at a point of the open diamond off the coordinate axes.  The truncated base is the
  diamond power plus a constant plus the exterior tail (`truncBase_eq`), the constant has vanishing
  second difference, and the two remaining pieces are `integrable_secondDiff_diamondPow` and
  `integrable_secondDiff_truncTail`.
* `integrable_secondDiff_fracSpline`: the same for the spline part, from
  `integrable_secondDiff_splineCell` over the `1201` cells.
* `jumpGen_fracKernel_eq`: **the decomposition**,
  `jumpGen (6/5) fracKernel z = a · jumpGen (6/5) (truncBase (6/5) (7/4)) z + (the spline sum)`.
* `jumpGen_fracKernel_nonneg_of_bounds`: **the leaf inequality.**  Given the radial tangent data of
  `CenteredMaximal.Fractional.RadialTangent` and *any* lower bound for the spline sum on the
  rectangle, a single rational inequality between the two corner values and that bound proves
  `0 ≤ jumpGen (6/5) fracKernel z` throughout the rectangle.

## What is still missing for a `decide`-checkable row

`jumpGen_fracKernel_nonneg_of_bounds` takes the spline lower bound as a hypothesis.  Supplying it
rationally is the remaining work, and it is the bulk of the certificate: the `1201` cells have to be
collapsed onto the `~2 JMAX + 5` row indices that meet the rectangle, each row's coefficient cubic
has to be formed from `CenteredMaximal.Fractional.bspline_eq_sum_of_mem_Icc`, each `|·| ^ (9/5)`
replaced by `CenteredMaximal.Fractional.abs_jumpGen1_bspline_sub_taylor`, and the resulting
bivariate polynomial bounded by `CenteredMaximal.Fractional.centeredPoly_ge`.  The intrinsic
constant is likewise still a parameter: `S` has to be nonnegative and at most the closed form of
`jumpGen_truncBase_ge_radial`, and the bridge from that closed form to
`CenteredMaximal.Fractional.sixFifthsConst` — and hence to the rational `125337337 / 50000000` of
`lt_sixFifths_const` — is not proved anywhere in the project yet.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### The integrand of the truncated base -/

/-- **The truncated base's second difference splits.**  `truncBase_eq` writes the base as the
diamond power minus a constant plus the exterior tail, and the constant contributes nothing. -/
theorem secondDiff_truncBase (α R : ℝ) (j : Fin 2) (z : Fin 2 → ℝ) (t : ℝ) :
    secondDiff (truncBase α R) j z t
      = secondDiff (diamondPow α) j z t + secondDiff (truncTail α R) j z t := by
  simp only [secondDiff, truncBase_eq]
  ring

/-- **The truncated base's integrand is integrable** at a point of the open diamond off the
coordinate axes. -/
theorem integrable_secondDiff_truncBase {α R : ℝ} (hα : 0 < α) (hα' : α < 2) {z : Fin 2 → ℝ}
    (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (hz : diamondNorm z < R) (j : Fin 2) :
    Integrable fun t : ℝ => secondDiff (truncBase α R) j z t * |t| ^ (-(1 + α)) := by
  refine ((integrable_secondDiff_diamondPow hα hα' h0 h1 j).add
    (integrable_secondDiff_truncTail hα h0 h1 hz j)).congr
    (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, secondDiff_truncBase]
  ring

/-! ### The integrand of the spline part -/

/-- **The spline part's integrand is integrable**, being a finite sum of tensor spline cells. -/
theorem integrable_secondDiff_fracSpline (z : Fin 2 → ℝ) (j : Fin 2) :
    Integrable fun t : ℝ =>
      secondDiff (fun w : Fin 2 → ℝ => ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
        (bspline (16 * w 0 - ij.1) * bspline (16 * w 1 - ij.2))) j z t
          * |t| ^ (-(1 + 6 / 5 : ℝ)) := by
  have hfam : ∀ ij ∈ fracCellFinset, Integrable (fun t : ℝ =>
      fracCoeff (fracCellCoeff ij) *
        (secondDiff (fun w : Fin 2 → ℝ => bspline (16 * w 0 - ij.1) * bspline (16 * w 1 - ij.2))
          j z t * |t| ^ (-(1 + 6 / 5 : ℝ)))) := fun ij _ =>
    (integrable_secondDiff_splineCell (α := 6 / 5) (by norm_num) (by norm_num)
      (by norm_num : (0 : ℝ) < 16) (ij.1 : ℝ) (ij.2 : ℝ) z j).const_mul _
  refine (integrable_finsetSum _ hfam).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [secondDiff_finsetSum, secondDiff_const_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun ij _ => by ring

/-! ### The decomposition of the generator of the comparison kernel -/

/-- **The generator of the comparison kernel splits into its base part and its spline part.**  Both
integrands are integrable at a point of the open diamond off the coordinate axes, so `jumpGen_add`
applies, and the spline part is evaluated by `jumpGen_splineSum`. -/
theorem jumpGen_fracKernel_eq {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0)
    (hz : diamondNorm z < 7 / 4) :
    jumpGen (6 / 5) fracKernel z
      = fracBaseCoeff * jumpGen (6 / 5) (truncBase (6 / 5) (7 / 4)) z
        + ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
            ((16 : ℝ) ^ (6 / 5 : ℝ) *
              (jumpGen1 (6 / 5) bspline (16 * z 0 - ij.1) * bspline (16 * z 1 - ij.2)
                + bspline (16 * z 0 - ij.1) * jumpGen1 (6 / 5) bspline (16 * z 1 - ij.2))) := by
  have hbase : ∀ j : Fin 2, Integrable fun t : ℝ =>
      secondDiff (fun w : Fin 2 → ℝ => fracBaseCoeff * truncBase (6 / 5) (7 / 4) w) j z t
        * |t| ^ (-(1 + 6 / 5 : ℝ)) := by
    intro j
    refine ((integrable_secondDiff_truncBase (α := 6 / 5) (by norm_num) (by norm_num) h0 h1 hz
      j).const_mul fracBaseCoeff).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [secondDiff_const_mul]
    ring
  have hsplit : fracKernel = (fun w : Fin 2 → ℝ => fracBaseCoeff * truncBase (6 / 5) (7 / 4) w)
      + fun w : Fin 2 → ℝ => ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
          (bspline (16 * w 0 - ij.1) * bspline (16 * w 1 - ij.2)) := by
    funext w
    rw [Pi.add_apply, fracKernel_eq_finsetSum w]
  rw [hsplit, jumpGen_add hbase (integrable_secondDiff_fracSpline z), jumpGen_const_mul,
    jumpGen_splineSum (by norm_num) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 16)]

/-! ### One rectangle of the certificate -/

/-- **The leaf inequality of the `α = 6/5` generator certificate.**  On a rectangle
`|z₀| ∈ [u₀, u₁]`, `|z₁| ∈ [v₀, v₁]` of the open diamond, off the coordinate axes, the generator of
the comparison kernel is nonnegative as soon as

* `S` is a nonnegative lower bound for the intrinsic constant of `jumpGen_truncBase_ge_radial`,
* `splineLo` is a lower bound for the spline sum at `z`, and
* the *rational* inequality `hcheck` holds between `splineLo` and the smaller of the two corner
  values of the radial tangent minorant.

Only `hcheck` depends on the rectangle's data, and `radialMinorant_eq_affine` makes it an inequality
between explicit rational expressions once `S` and the `tailCoeff` are rational. -/
theorem jumpGen_fracKernel_nonneg_of_bounds {S r₀ splineLo u₀ u₁ v₀ v₁ : ℝ} {K : ℕ}
    (hS : 0 ≤ S)
    (hSle : S ≤ -4 * Real.pi * Real.Gamma (2 * (6 / 5)) * Real.cos (Real.pi * (6 / 5) / 2)
      / (6 / 5 * Real.Gamma (6 / 5) ^ 2 * Real.sin (Real.pi * (6 / 5) / 2)))
    (hr₀ : 0 < r₀)
    (hcheck : 0 ≤ fracBaseCoeff * min (radialMinorant (6 / 5) (7 / 4) S K r₀ (u₀ + v₀))
        (radialMinorant (6 / 5) (7 / 4) S K r₀ (u₁ + v₁)) + splineLo)
    {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (hz : diamondNorm z < 7 / 4)
    (hu : u₀ ≤ |z 0|) (hu' : |z 0| ≤ u₁) (hv : v₀ ≤ |z 1|) (hv' : |z 1| ≤ v₁)
    (hspl : splineLo ≤ ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
        ((16 : ℝ) ^ (6 / 5 : ℝ) *
          (jumpGen1 (6 / 5) bspline (16 * z 0 - ij.1) * bspline (16 * z 1 - ij.2)
            + bspline (16 * z 0 - ij.1) * jumpGen1 (6 / 5) bspline (16 * z 1 - ij.2)))) :
    0 ≤ jumpGen (6 / 5) fracKernel z := by
  rw [jumpGen_fracKernel_eq h0 h1 hz]
  have hrad := radialMinorant_le (α := 6 / 5) (R := 7 / 4) (S := S) (r₀ := r₀) (by norm_num)
    (by norm_num) (by norm_num) hS hSle hr₀ K h0 h1 hz
  have hcorner := radialMinorant_corner_le (6 / 5) (7 / 4) S K r₀ hu hu' hv hv'
  have hmul := mul_le_mul_of_nonneg_left (hcorner.trans hrad) fracBaseCoeff_pos.le
  linarith

end CenteredMaximal.Fractional

end

end
