/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.SplineGenerator
public import CenteredMaximal.Fractional.SplineTaylor

/-!
# The leaf arithmetic of the `α = 6/5` generator certificate

`CenteredMaximal.Fractional.RadialTangent` handles the radial half of a certificate leaf and
`CenteredMaximal.Fractional.SplineTaylor` the elementary function of the spline half.  This file
supplies the three remaining *shape* lemmas that turn those into one rational inequality per dyadic
rectangle.

## Main results

* `jumpGen1_bspline_sixFifths`: `jumpGen1_bspline` at `α = 6/5`, with the prefactor evaluated:
  `jumpGen1 (6/5) β x = (625/108) ∑_{q<5} (−1)^q C(4,q) |x + 2 − q|^{9/5}`.
* `bspline_eq_sum_of_mem_Icc`: **the B-spline is an explicit cubic on each unit cell.**  For
  `m ≤ y ≤ m + 1` the truncations of `bspline` are resolved by the single integer comparison
  `q ≤ m + 2`; this is the `beta_poly` of the search program.
* `abs_jumpGen1_bspline_sub_taylor`: **the spline generator of one cell against its cubic model.**
  The five terms of `jumpGen1_bspline_sixFifths` are expanded at the five centres `c + 2 − q`, and
  the error is the *sum* of the five Lagrange remainders of
  `CenteredMaximal.Fractional.abs_rpow_nine_fifths_taylor`.
* `centeredPoly_ge`: **the centred-coefficient bound.**  A bivariate polynomial in the deviations
  from the centre of a rectangle is at least its constant term minus `∑ |coefficient| δ^{degree}`.
  This is the final step of every leaf of the search program.

## The five remainders do not cancel

`CenteredMaximal.Fractional.sum_alt_choose_cubic` says that the weights `(−1)^q C(4,q)` annihilate
*one* cubic evaluated at the five shifted points.  The five cubic Taylor polynomials of
`abs_jumpGen1_bspline_sub_taylor` are *five different* cubics, one per centre `c + 2 − q`, so they
are not annihilated: their weighted sum is what reproduces the fourth difference.  The error term of
`abs_jumpGen1_bspline_sub_taylor` is therefore `∑_q C(4,q) · (9/625) δ⁴ (|c + 2 − q| − δ)^{-11/5}`,
which is `16 · (9/625) δ⁴ · O(1)` and *not* zero.  It is small because it is `O(δ⁴)` — a leaf at
subdivision depth `d` has `δ = 2^{-d-1}` in grid coordinates, and the search program refines a
rectangle until its total is positive, reaching depth `5` on the `4582` leaves of the certificate —
not because of any cancellation.
-/

@[expose] public section

noncomputable section

open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### The spline generator at `α = 6/5` -/

/-- **The fractional generator of the cardinal cubic B-spline at order `6/5`.**  The prefactor
`2 / (−(α(1−α)(2−α)(3−α)))` of `jumpGen1_bspline` is `625/108` and the exponent `3 − α` is `9/5`. -/
theorem jumpGen1_bspline_sixFifths (x : ℝ) :
    jumpGen1 (6 / 5) bspline x
      = 625 / 108 * ∑ q ∈ Finset.range 5,
          (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * |x + 2 - q| ^ (9 / 5 : ℝ) := by
  rw [jumpGen1_bspline (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-! ### The B-spline on one unit cell -/

/-- **The B-spline is an explicit cubic on each unit cell.**  On `[m, m + 1]` the truncated cube
`((y + 2 − q)₊)³` is `(y + 2 − q)³` exactly when `q ≤ m + 2` and vanishes otherwise, so no
truncation survives inside the cell. -/
theorem bspline_eq_sum_of_mem_Icc {m : ℤ} {y : ℝ} (h : (m : ℝ) ≤ y) (h' : y ≤ (m : ℝ) + 1) :
    bspline y = 1 / 6 * ∑ q ∈ Finset.range 5,
      (if (q : ℤ) ≤ m + 2 then (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * (y + 2 - q) ^ 3 else 0) := by
  rw [bspline]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hcase : (q : ℤ) ≤ m + 2
  · have hcast : (q : ℝ) ≤ (m : ℝ) + 2 := by
      have := (Int.cast_le (R := ℝ)).2 hcase
      push_cast at this
      linarith
    rw [if_pos hcase, truncCube_of_nonneg (by linarith)]
  · have hcast : (m : ℝ) + 3 ≤ (q : ℝ) := by
      have : m + 3 ≤ (q : ℤ) := by omega
      have := (Int.cast_le (R := ℝ)).2 this
      push_cast at this
      linarith
    rw [if_neg hcase, truncCube_of_nonpos (by linarith), mul_zero]

/-! ### One cell of the spline generator against its cubic model -/

/-- **The cubic model of the spline generator on a dyadic interval.**  The five values of
`|·| ^ (9/5)` in `jumpGen1_bspline_sixFifths` are expanded at the five centres `c + 2 − q`, each by
`abs_rpow_nine_fifths_taylor`, and the errors *add*: the five cubics are five different cubics and
the fourth-difference weights do not annihilate them. -/
theorem abs_jumpGen1_bspline_sub_taylor {x c δ : ℝ} (hδ : 0 < δ) (hx : |x - c| ≤ δ)
    (hc : ∀ q ∈ Finset.range 5, δ < |c + 2 - q|) :
    |jumpGen1 (6 / 5) bspline x - 625 / 108 * ∑ q ∈ Finset.range 5,
        (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * nineFifthsTaylor (c + 2 - q) (x + 2 - q)|
      ≤ 625 / 108 * ∑ q ∈ Finset.range 5,
        (Nat.choose 4 q : ℝ) * (9 / 625 * δ ^ 4 * (|c + 2 - q| - δ) ^ (-(11 / 5) : ℝ)) := by
  rw [jumpGen1_bspline_sixFifths, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    show |(625 : ℝ) / 108| = 625 / 108 from abs_of_pos (by norm_num)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 625 / 108)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q hq => ?_)
  have hstep := abs_rpow_nine_fifths_taylor (c := c + 2 - q) (δ := δ) (x := x + 2 - q) hδ (hc q hq)
    (by rwa [show x + 2 - (q : ℝ) - (c + 2 - q) = x - c from by ring])
  calc |(-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * |x + 2 - (q : ℝ)| ^ (9 / 5 : ℝ)
        - (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * nineFifthsTaylor (c + 2 - q) (x + 2 - q)|
      = (Nat.choose 4 q : ℝ) *
          |(|x + 2 - (q : ℝ)| ^ (9 / 5 : ℝ)) - nineFifthsTaylor (c + 2 - q) (x + 2 - q)| := by
        rw [show (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * |x + 2 - (q : ℝ)| ^ (9 / 5 : ℝ)
            - (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * nineFifthsTaylor (c + 2 - q) (x + 2 - q)
            = (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
              ((|x + 2 - (q : ℝ)| ^ (9 / 5 : ℝ)) - nineFifthsTaylor (c + 2 - q) (x + 2 - q))
            from by ring, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          Nat.abs_cast]
    _ ≤ (Nat.choose 4 q : ℝ) * (9 / 625 * δ ^ 4 * (|c + 2 - (q : ℝ)| - δ) ^ (-(11 / 5) : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)

/-! ### The centred-coefficient bound -/

/-- **The centred-coefficient bound.**  A bivariate polynomial in the deviations `s`, `t` from the
centre of a rectangle of half-width `δ` is at least its constant term minus
`∑ |coefficient| δ^{total degree}`.  Every leaf of the search program ends in this inequality. -/
theorem centeredPoly_ge {F : Finset (ℕ × ℕ)} (h0 : (0, 0) ∈ F) (co : ℕ × ℕ → ℝ) {s t δ : ℝ}
    (hs : |s| ≤ δ) (ht : |t| ≤ δ) :
    co (0, 0) - ∑ p ∈ F.erase (0, 0), |co p| * δ ^ (p.1 + p.2)
      ≤ ∑ p ∈ F, co p * s ^ p.1 * t ^ p.2 := by
  have hδ0 : (0 : ℝ) ≤ δ := (abs_nonneg s).trans hs
  have hterm : ∀ p ∈ F.erase (0, 0),
      -(|co p| * δ ^ (p.1 + p.2)) ≤ co p * s ^ p.1 * t ^ p.2 := by
    intro p _
    have h1 : |s| ^ p.1 ≤ δ ^ p.1 := by gcongr
    have h2 : |t| ^ p.2 ≤ δ ^ p.2 := by gcongr
    have hbound : |co p * s ^ p.1 * t ^ p.2| ≤ |co p| * δ ^ (p.1 + p.2) := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow, pow_add, ← mul_assoc]
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2
        (pow_nonneg (abs_nonneg t) _) (mul_nonneg (abs_nonneg _) (pow_nonneg hδ0 _))
    linarith [neg_abs_le (co p * s ^ p.1 * t ^ p.2)]
  have hsum : ∑ p ∈ F.erase (0, 0), -(|co p| * δ ^ (p.1 + p.2))
      ≤ ∑ p ∈ F.erase (0, 0), co p * s ^ p.1 * t ^ p.2 := Finset.sum_le_sum hterm
  rw [Finset.sum_neg_distrib] at hsum
  rw [← Finset.sum_erase_add F (fun p => co p * s ^ p.1 * t ^ p.2) h0]
  simp only [pow_zero, mul_one]
  linarith

end CenteredMaximal.Fractional

end

end
