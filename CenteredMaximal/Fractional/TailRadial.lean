/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.TruncatedBase

/-!
# The radial reserve of the exterior tail's generator

`CenteredMaximal.Fractional.jumpGen_truncBase_ge` bounds the generator of the truncated diamond
base below by the intrinsic power term alone, having dropped the generator of the exterior tail
`truncTail α R = (R^{-α} − r^{-α})₊` as merely nonnegative.  **That bound is far too weak for the
`α = 6/5` comparison certificate.**  The certificate's margin over the `4582` rectangles is
`7.1 · 10⁻⁵`, while the tail's generator is of size `0.4` near the origin and grows without bound
as `r ↑ R`; dropping it makes `154` of the first `200` rectangles fail, by as much as `3.3`.  The
tail is not a spare reserve, it is a load-bearing part of the certificate.

This file recovers the *radial* part of it, which is where almost all of it lives.

## The bound

At a point `z` of the punctured closed diamond the tail vanishes, so

`secondDiff (truncTail α R) j z t = truncTail α R (z + t e_j) + truncTail α R (z − t e_j)`,

a sum of two nonnegative terms.  One of the two displaced points always has diamond radius exactly
`r(z) + |t|`, because `max |a + t| |a − t| = |a| + |t|` for the displaced coordinate `a = z j`
(`add_abs_le_max_abs`), and the untouched coordinate contributes the same `|z (j+1)|` to both.
Since the tail is increasing in the diamond radius, each of the two summands of each of the two
coordinate directions is therefore at least

`tailRadial α R r(z) t = (R^{-α} − (r(z) + |t|)^{-α})₊`,

which depends on `|t|` alone.  Both coordinate directions give the same reserve, whence the
factor `2` of `jumpGen_truncTail_ge_radial`.

## Main results

* `tailRadial`: the radial minorant `(R^{-α} − (r + |t|)^{-α})₊` of a tail second difference.
* `tailRadial_le_truncTail`: the tail is increasing in the diamond radius.
* `tailRadial_le_secondDiff`: the pointwise bound, valid on the whole punctured closed diamond.
* `jumpGen_truncTail_ge_radial`: **the reserve**,
  `2 ∫ tailRadial α R r(z) t · |t|^{−(1+α)} dt ≤ jumpGen α (truncTail α R) z`.
* `jumpGen_truncBase_ge_radial`: the same reserve added back onto the intrinsic power term, i.e.
  the strengthening of `jumpGen_truncBase_ge` that the certificate actually needs.

## No integrability is needed for the minorant

`integral_mono_of_nonneg` asks only that the *larger* integrand be integrable, and that is exactly
`integrable_secondDiff_truncTail`.  The minorant is a positive part, hence nonnegative, so it needs
no integrability hypothesis of its own — which matters, because the minorant is *not* integrable
when `r(z) = R`, the very case in which the tail's generator diverges and the certificate leans on
it hardest.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### A displaced coordinate attains the sum of the absolute values -/

/-- **`|a| + |b| ≤ max |a + b| |a − b|`.**  Squaring, one of the two right-hand sides is exactly
`|a| + |b|`, according to the sign of `a b`. -/
theorem add_abs_le_max_abs (a b : ℝ) : |a| + |b| ≤ max |a + b| |a - b| := by
  have key : ∀ c : ℝ, 0 ≤ a * c → |a| + |c| ≤ |a + c| := by
    intro c hac
    refine le_of_pow_le_pow_left₀ two_ne_zero (abs_nonneg _) ?_
    have h1 : |a| ^ 2 = a ^ 2 := sq_abs a
    have h2 : |c| ^ 2 = c ^ 2 := sq_abs c
    have h3 : |a + c| ^ 2 = (a + c) ^ 2 := sq_abs (a + c)
    have h4 : |a| * |c| = |a * c| := (abs_mul a c).symm
    have h5 : |a * c| = a * c := abs_of_nonneg hac
    nlinarith [h1, h2, h3, h4, h5]
  rcases le_total 0 (a * b) with h | h
  · exact (key b h).trans (le_max_left _ _)
  · have h' := key (-b) (by rw [mul_neg]; exact neg_nonneg.2 h)
    rw [abs_neg, ← sub_eq_add_neg] at h'
    exact h'.trans (le_max_right _ _)

/-! ### The diamond radius along a coordinate line -/

private theorem diamondNorm_eq_abs_add' (z : Fin 2 → ℝ) (j : Fin 2) :
    diamondNorm z = |z j| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem diamondNorm_add_single' (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z + s • Pi.single j 1) = |z j + s| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem diamondNorm_sub_single' (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z - s • Pi.single j 1) = |z j - s| + |z (j + 1)| := by
  rw [sub_eq_add_neg, ← neg_smul, diamondNorm_add_single', ← sub_eq_add_neg]

/-- **One of the two displaced points has diamond radius `r(z) + |t|`.**  The displacement leaves
the other coordinate alone, and `max |z j + t| |z j − t| = |z j| + |t|`. -/
theorem le_max_diamondNorm_single (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    diamondNorm z + |t| ≤
      max (diamondNorm (z + t • Pi.single j 1)) (diamondNorm (z - t • Pi.single j 1)) := by
  rw [diamondNorm_add_single', diamondNorm_sub_single', diamondNorm_eq_abs_add' z j]
  have h := add_abs_le_max_abs (z j) t
  rcases max_cases |z j + t| |z j - t| with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h
  · exact le_trans (by linarith) (le_max_left _ _)
  · exact le_trans (by linarith) (le_max_right _ _)

/-! ### The radial minorant -/

/-- The radial minorant `(R^{-α} − (r + |t|)^{-α})₊` of a second difference of the exterior tail
at a point of diamond radius `r`.  It is a function of `|t|` alone. -/
def tailRadial (α R r t : ℝ) : ℝ := max (R ^ (-α) - (r + |t|) ^ (-α)) 0

/-- The radial minorant is nonnegative, being a positive part. -/
theorem tailRadial_nonneg (α R r t : ℝ) : 0 ≤ tailRadial α R r t := le_max_right _ _

/-- The radial minorant is even in the displacement. -/
theorem tailRadial_neg (α R r t : ℝ) : tailRadial α R r (-t) = tailRadial α R r t := by
  rw [tailRadial, tailRadial, abs_neg]

/-- **The tail is increasing in the diamond radius.**  A point of diamond radius at least `ρ > 0`
carries at least the tail value of radius `ρ`, because `s ↦ s^{-α}` is antitone for `α > 0`. -/
theorem tailRadial_le_truncTail {α R ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ) {w : Fin 2 → ℝ}
    (hw : ρ ≤ diamondNorm w) : max (R ^ (-α) - ρ ^ (-α)) 0 ≤ truncTail α R w := by
  refine max_le_max ?_ le_rfl
  have := Real.rpow_le_rpow_of_nonpos hρ hw (neg_nonpos.2 hα.le)
  linarith

/-- **The pointwise reserve.**  At a point of the punctured closed diamond, off the two coordinate
axes, every second difference of the exterior tail is at least the radial minorant.  Only *one* of
the two displaced points is used; the other is discarded as nonnegative. -/
theorem tailRadial_le_secondDiff {α R : ℝ} (hα : 0 < α) {z : Fin 2 → ℝ} (hz0 : z ≠ 0)
    (hz : diamondNorm z ≤ R) (j : Fin 2) (t : ℝ) :
    tailRadial α R (diamondNorm z) t ≤ secondDiff (truncTail α R) j z t := by
  have hzpos : 0 < diamondNorm z := diamondNorm_pos hz0
  have hρ : 0 < diamondNorm z + |t| := by positivity
  have hplus := truncTail_nonneg α R (z + t • Pi.single j 1)
  have hminus := truncTail_nonneg α R (z - t • Pi.single j 1)
  have hkey := le_max_diamondNorm_single z j t
  rw [secondDiff, truncTail_eq_zero hα hz0 hz]
  have hone : tailRadial α R (diamondNorm z) t ≤
      max (truncTail α R (z + t • Pi.single j 1)) (truncTail α R (z - t • Pi.single j 1)) := by
    rcases max_cases (diamondNorm (z + t • Pi.single j 1))
      (diamondNorm (z - t • Pi.single j 1)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hkey
    · exact (tailRadial_le_truncTail hα hρ hkey).trans (le_max_left _ _)
    · exact (tailRadial_le_truncTail hα hρ hkey).trans (le_max_right _ _)
  rcases max_cases (truncTail α R (z + t • Pi.single j 1))
    (truncTail α R (z - t • Pi.single j 1)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hone <;> linarith

/-! ### The reserve as an integral -/

/-- **The radial reserve of the tail's generator.**  Inside the open diamond, off the coordinate
axes, the generator of the exterior tail is at least twice the radial integral — once for each
coordinate direction.  The minorant needs no integrability of its own: it is nonnegative, and
`integral_mono_of_nonneg` asks integrability only of the larger integrand, which is
`integrable_secondDiff_truncTail`. -/
theorem jumpGen_truncTail_ge_radial {α R : ℝ} (hα : 0 < α) {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0)
    (h1 : z 1 ≠ 0) (hz : diamondNorm z < R) :
    2 * ∫ t : ℝ, tailRadial α R (diamondNorm z) t * |t| ^ (-(1 + α))
      ≤ jumpGen α (truncTail α R) z := by
  have hz0 : z ≠ 0 := fun h => h0 (by simp [h])
  have hstep : ∀ j : Fin 2, (∫ t : ℝ, tailRadial α R (diamondNorm z) t * |t| ^ (-(1 + α)))
      ≤ ∫ t : ℝ, secondDiff (truncTail α R) j z t * |t| ^ (-(1 + α)) := by
    intro j
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => ?_)
      (integrable_secondDiff_truncTail hα h0 h1 hz j) (Filter.Eventually.of_forall fun t => ?_)
    · exact mul_nonneg (tailRadial_nonneg _ _ _ _) (Real.rpow_nonneg (abs_nonneg t) _)
    · exact mul_le_mul_of_nonneg_right (tailRadial_le_secondDiff hα hz0 hz.le j t)
        (Real.rpow_nonneg (abs_nonneg t) _)
  rw [jumpGen, Fin.sum_univ_two]
  linarith [hstep 0, hstep 1]

/-- **The strengthening of `jumpGen_truncBase_ge` that the certificate needs.**  The generator of
the truncated base is at least the closed-form intrinsic power term *plus* the radial reserve of
the exterior tail.  Dropping the second summand recovers `jumpGen_truncBase_ge`, which the `α = 6/5`
rectangle certificate cannot afford. -/
theorem jumpGen_truncBase_ge_radial {α R : ℝ} (hα : 1 < α) (hα' : α < 2) {z : Fin 2 → ℝ}
    (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (hz : diamondNorm z < R) :
    -4 * Real.pi * Real.Gamma (2*α) * Real.cos (Real.pi*α/2)
        / (α * Real.Gamma α ^ 2 * Real.sin (Real.pi*α/2)) * diamondNorm z ^ (-2*α)
        + 2 * ∫ t : ℝ, tailRadial α R (diamondNorm z) t * |t| ^ (-(1 + α))
      ≤ jumpGen α (truncBase α R) z := by
  rw [jumpGen_truncBase hα hα' h0 h1 hz]
  linarith [jumpGen_truncTail_ge_radial (by linarith : (0:ℝ) < α) h0 h1 hz]

end CenteredMaximal.Fractional

end

end
