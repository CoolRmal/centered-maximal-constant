/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.FullMinorant
public import CenteredMaximal.Fractional.LeafBound

/-!
# The leaf inequality of the `α = 6/5` generator certificate, with the two halves combined

`CenteredMaximal.Fractional.jumpGen_fracKernel_nonneg_of_full` reduces one rectangle of the
generator certificate to a rational inequality by bounding the **two halves of the generator
separately**: the base half is replaced by the smallest of the four corner values of the affine
minorant `fullMinorant`, and the spline half by a single number `splineLo`.  That reduction is
sound, but it is *quantitatively far too weak to certify the rectangles the search program
produces*, and this file supplies the reduction that is not.

## Why the separated reduction cannot work

On a rectangle the generator is, up to a Taylor error, a polynomial in the deviations
`s = 16 |z₀| − u_c`, `t = 16 |z₁| − v_c` from the centre.  Its linear part has two sources: the
radial derivative of the base, of size `S · r^{−17/5}`, and the linear coefficient of the spline
model.  **The certificate works because these two very nearly cancel** — the spline was fitted to
the base, so its gradient tracks `−∂_r` of the base.  Bounding the two halves separately replaces
`|A_base + A_spline| · δ` by `|A_base| · δ + |A_spline| · δ`, which near the origin is larger by a
factor of about `10³`, because there `r^{−17/5}` is enormous while the sum is `O(1)`.

This is a measurement, not a guess.  Evaluating both reductions in exact rational arithmetic on all
`4582` rectangles of the certificate, at the precision-`12` fifth-root enclosures the Lean table
carries:

* the combined reduction of this file certifies **all `4582`** rectangles, with minimum margin
  `1.4099404 · 10⁻⁴` — this is the certificate the search program actually found;
* the separated reduction of `jumpGen_fracKernel_nonneg_of_full` fails on **`2674` of the `4582`**,
  and the worst rectangle, `16 |z₀| ∈ [1.5, 1.625]`, `16 |z₁| ∈ [0.25, 0.375]`, fails by `−139.3`.
  Choosing the tangent point at the far corner or at the centre, and refining, do not repair it:
  the deficit is a factor, not an `O(δ)` slack.

So the four-corner principle `fullMinorant_corner_le` is the wrong last step.  The corner principle
is *exact* for the base alone — an affine function really is minimised at a corner — but taking the
minimum of the base before adding the spline discards the cancellation, and the cancellation is the
whole content of the certificate.

## Main results

* `fullMinorant_centred`: **the affine minorant, recentred.**  `fullMinorant`, read at
  `r = x + y`, `d = x − y`, is affine in `(x, y)`; here it is written in the deviations
  `16 x − u_c`, `16 y − v_c` of the grid coordinates from the centre of a rectangle, which is the
  form in which its coefficients are *added into* the spline model's.
* `jumpGen_fracKernel_nonneg_of_centred`: **the combined leaf inequality.**  A single centred
  polynomial model of base *and* spline together, one rational check on its coefficients, and the
  generator is nonnegative on the rectangle.  `hmodel` is where a certificate's interval arithmetic
  lands, and because it is one inequality about the sum, the linear coefficients are added before
  their absolute values are taken.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### The affine minorant in the deviations from the centre of a rectangle -/

/-- **`fullMinorant` recentred at the centre of a rectangle.**  The radial and anti-radial tangents
are affine in `r` and in `d`, so their sum, read at `r = x + y` and `d = x − y`, is affine in
`(x, y)`; this writes it in the two deviations `16 x − u_c` and `16 y − v_c` of the grid
coordinates.  The two slopes are `(b + e)/16` and `(b − e)/16`, *unequal* because the radial and
anti-radial tangents have unequal slopes — which is exactly why the base contributes two independent
linear coefficients to the certificate's polynomial model.

The affine forms of the two tangents are hypotheses rather than `radialMinorant_eq_affine` and
`antiMinorant_eq_affine` themselves, so that a leaf may supply rational enclosures of `a`, `b`, `c`
and `e` instead of their closed forms. -/
theorem fullMinorant_centred {α R S : ℝ} {K L : ℕ} {r₀ d₀ : ℝ} {a b c e : ℝ}
    (hr : ∀ r : ℝ, radialMinorant α R S K r₀ r = a + b * r)
    (ha : ∀ d : ℝ, antiMinorant α R L d₀ d = c + e * d) (uc vc x y : ℝ) :
    fullMinorant α R S K L r₀ d₀ (x + y) (x - y)
      = (a + c + (b + e) * uc / 16 + (b - e) * vc / 16)
        + (b + e) / 16 * (16 * x - uc) + (b - e) / 16 * (16 * y - vc) := by
  rw [fullMinorant, hr, ha]
  ring

/-! ### The combined leaf inequality -/

/-- **The combined leaf inequality of the `α = 6/5` generator certificate.**  On a rectangle of the
open diamond centred at the grid point `(u_c, v_c)` with half-width `δ`, off the coordinate axes,
the generator of the comparison kernel is nonnegative as soon as

* `S` is a nonnegative lower bound for the intrinsic constant of the reserve,
* `co` is a coefficient family for a **single** centred polynomial model of the whole generator —
  base minorant *and* spline half together — accurate to `err` on the rectangle (`hmodel`), and
* the rational inequality `hcheck` holds: the model's constant term, less the `δ`-weighted sum of
  the absolute values of its other coefficients, less the model error, is nonnegative.

The point of the statement is that `hmodel` is one inequality about the *sum* of the two halves.
A certificate builds `co` by adding the base's two recentred slopes (`fullMinorant_centred`) into
the `(1, 0)` and `(0, 1)` coefficients of the spline's Taylor model *before* `hcheck` takes absolute
values, and that cancellation is what makes the check pass; see the module docstring for the
measured cost of not doing so.

`err` is the accumulated Taylor error of the spline model, which `hmodel` subtracts and `hcheck`
pays for; it plays no other role, so a model with no error may take `err = 0`. -/
theorem jumpGen_fracKernel_nonneg_of_centred {S r₀ d₀ : ℝ} {K L : ℕ} (hS : 0 ≤ S)
    (hSle : S ≤ -4 * Real.pi * Real.Gamma (2 * (6 / 5)) * Real.cos (Real.pi * (6 / 5) / 2)
      / (6 / 5 * Real.Gamma (6 / 5) ^ 2 * Real.sin (Real.pi * (6 / 5) / 2)))
    (hr₀ : 0 < r₀) {F : Finset (ℕ × ℕ)} (hF : (0, 0) ∈ F) (co : ℕ × ℕ → ℝ) {uc vc δ err : ℝ}
    (hcheck : 0 ≤ co (0, 0) - (∑ p ∈ F.erase (0, 0), |co p| * δ ^ (p.1 + p.2)) - err)
    {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (hz : diamondNorm z < 7 / 4)
    (hu : |16 * |z 0| - uc| ≤ δ) (hv : |16 * |z 1| - vc| ≤ δ)
    (hmodel : (∑ p ∈ F, co p * (16 * |z 0| - uc) ^ p.1 * (16 * |z 1| - vc) ^ p.2) - err
      ≤ fracBaseCoeff * fullMinorant (6 / 5) (7 / 4) S K L r₀ d₀ (diamondNorm z) (|z 0| - |z 1|)
        + ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
            ((16 : ℝ) ^ (6 / 5 : ℝ) *
              (jumpGen1 (6 / 5) bspline (16 * z 0 - ij.1) * bspline (16 * z 1 - ij.2)
                + bspline (16 * z 0 - ij.1) * jumpGen1 (6 / 5) bspline (16 * z 1 - ij.2)))) :
    0 ≤ jumpGen (6 / 5) fracKernel z := by
  rw [jumpGen_fracKernel_eq h0 h1 hz]
  have hfull := fullMinorant_le (α := 6 / 5) (R := 7 / 4) (S := S) (r₀ := r₀) (d₀ := d₀)
    (by norm_num) (by norm_num) (by norm_num) hS hSle hr₀ K L h0 h1 hz
  have hmul := mul_le_mul_of_nonneg_left hfull fracBaseCoeff_pos.le
  have hpoly := centeredPoly_ge hF co hu hv
  linarith

end CenteredMaximal.Fractional

end

end
