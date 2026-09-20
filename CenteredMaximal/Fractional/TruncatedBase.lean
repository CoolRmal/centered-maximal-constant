/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.DiamondPower

/-!
# The fractional generator of the truncated diamond base

The comparison kernel of order `α ∈ (1, 2)` is built from the **truncated diamond base**

`truncBase α R z = (r(z)^{-α} − R^{-α})₊`,   `r = diamondNorm`,

which agrees with the diamond power up to an additive constant inside the diamond of radius `R`
and vanishes outside it. Since the tensor-spline correction that is added to it carries a
*negative* generator, the certificate needs a *positive* lower bound for the generator of the
base, and that is what this file supplies.

The whole computation rests on the tautology `a₊ = a + (−a)₊`, i.e.

`truncBase α R = (diamondPow α − R^{-α}) + truncTail α R`,
`truncTail α R z = (R^{-α} − r(z)^{-α})₊`

(`truncBase_eq`), which needs no hypothesis whatsoever. The additive constant drops out of every
second difference (`jumpGen_sub_const`), so the generator of the base is the generator of the
diamond power — evaluated in closed form by
`CenteredMaximal.Fractional.jumpGen_diamondPow_eq_const` — plus the generator of the exterior
tail (`jumpGen_truncBase`). Inside the open diamond the tail *vanishes at the base point* while
staying nonnegative everywhere, so each of the four displaced values contributes nonnegatively and
its generator is nonnegative with no integrability input at all (`jumpGen_truncTail_nonneg`,
the trick of `CenteredMaximal.Cauchy.jumpGen_looseKernel_nonneg`). Dropping it gives the reserve
`jumpGen_truncBase_ge`.

## Main results

* `truncBase`, `truncTail`: the truncated base and its exterior complement.
* `truncBase_eq`: the exact splitting `truncBase = (diamondPow − R^{-α}) + truncTail`.
* `jumpGen_truncTail_nonneg`: `0 ≤ jumpGen α (truncTail α R) z` for `0 < r(z) < R`.
* `integrable_secondDiff_diamondPow`, `integrable_secondDiff_truncTail`: the two integrands are
  integrable at a point off the coordinate axes, which is what splits the generator.
* `jumpGen_truncBase`, `jumpGen_truncBase_ge`: the generator of the base and the lower bound
  `-4π Γ(2α) cos(πα/2) / (α Γ(α)² sin(πα/2)) · r(z)^{-2α} ≤ jumpGen α (truncBase α R) z`, whose
  coefficient is positive on `1 < α < 2` because `cos(πα/2) < 0` there.

## Integrability

The diamond power's integrand is the one of `CenteredMaximal.Fractional.diamondDiff` up to a
pointwise identity, so `integrable_diamondDiff` applies verbatim. The tail's integrand is handled
by hand from two crude facts: `0 ≤ truncTail α R ≤ R^{-α}` bounds the second difference by
`4 R^{-α}`, which is enough past `|t| = R − r(z)`, and *below* that threshold the second difference
is identically zero, because all three points `z`, `z ± t e_j` then lie in the closed diamond and
none of them is the origin (the displacement leaves the other coordinate, which is nonzero,
untouched). No `O(t²)` estimate is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Cauchy

open scoped Real

namespace CenteredMaximal.Fractional

/-- The truncated diamond base `(r^{-α} − R^{-α})₊`, supported in the closed diamond of
radius `R`. -/
def truncBase (α R : ℝ) (z : Fin 2 → ℝ) : ℝ := max (diamondNorm z ^ (-α) - R ^ (-α)) 0

/-- The complementary piece, supported outside the diamond of radius `R`. -/
def truncTail (α R : ℝ) (z : Fin 2 → ℝ) : ℝ := max (R ^ (-α) - diamondNorm z ^ (-α)) 0

/-! ### The exact splitting -/

/-- **The splitting of the truncated base.** The positive part of `a = r^{-α} − R^{-α}` is `a`
plus the positive part of `−a`, so the truncated base is the diamond power, shifted by the
constant `R^{-α}`, plus the exterior tail. Being the tautology `a₊ = a + (−a)₊`, the identity
needs no hypothesis: it holds at `z = 0` as well, where Lean's `0 ^ (-α) = 0` makes both
`truncBase α R 0 = 0` and `truncTail α R 0 = R^{-α}`. -/
theorem truncBase_eq (α R : ℝ) (z : Fin 2 → ℝ) :
    truncBase α R z = diamondPow α z - R ^ (-α) + truncTail α R z := by
  rcases le_total (R ^ (-α)) (diamondNorm z ^ (-α)) with h | h
  · rw [truncBase, truncTail, max_eq_left (by linarith), max_eq_right (by linarith), diamondPow]
    ring
  · rw [truncBase, truncTail, max_eq_right (by linarith), max_eq_left (by linarith), diamondPow]
    ring

/-! ### Elementary properties of the tail -/

/-- The tail is nonnegative, being a positive part. -/
theorem truncTail_nonneg (α R : ℝ) (z : Fin 2 → ℝ) : 0 ≤ truncTail α R z := le_max_right _ _

/-- The tail is bounded by `R^{-α}`, since `r^{-α} ≥ 0`. -/
theorem truncTail_le {R : ℝ} (hR : 0 < R) (α : ℝ) (z : Fin 2 → ℝ) :
    truncTail α R z ≤ R ^ (-α) :=
  max_le (by linarith [Real.rpow_nonneg (diamondNorm_nonneg z) (-α)]) (Real.rpow_nonneg hR.le _)

/-- The two bounds together: `|truncTail α R| ≤ R^{-α}`. -/
theorem abs_truncTail_le {R : ℝ} (hR : 0 < R) (α : ℝ) (z : Fin 2 → ℝ) :
    |truncTail α R z| ≤ R ^ (-α) := by
  rw [abs_of_nonneg (truncTail_nonneg α R z)]
  exact truncTail_le hR α z

/-- The tail vanishes on the closed diamond of radius `R`, punctured at the origin: for
`0 < r(z) ≤ R` and `α > 0` the base `r ↦ r^{-α}` is antitone, so `R^{-α} ≤ r(z)^{-α}`. -/
theorem truncTail_eq_zero {α R : ℝ} (hα : 0 < α) {z : Fin 2 → ℝ} (hz0 : z ≠ 0)
    (hz : diamondNorm z ≤ R) : truncTail α R z = 0 :=
  max_eq_right (by
    linarith [Real.rpow_le_rpow_of_nonpos (diamondNorm_pos hz0) hz (neg_nonpos.2 hα.le)])

/-- The tail is measurable; it is *not* continuous, the origin being a jump. -/
theorem measurable_truncTail (α R : ℝ) : Measurable (truncTail α R) := by
  unfold truncTail
  exact (measurable_const.sub (measurable_diamondNorm.pow_const _)).max measurable_const

/-! ### Coordinate lines -/

private theorem diamondNorm_eq_abs_add (z : Fin 2 → ℝ) (j : Fin 2) :
    diamondNorm z = |z j| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem diamondNorm_add_single (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z + s • Pi.single j 1) = |z j + s| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem diamondNorm_sub_single (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z - s • Pi.single j 1) = |z j - s| + |z (j + 1)| := by
  rw [sub_eq_add_neg, ← neg_smul, diamondNorm_add_single, ← sub_eq_add_neg]

private theorem coord_succ_ne_zero {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2) :
    z (j + 1) ≠ 0 := by
  fin_cases j
  · simpa using h1
  · simpa using h0

/-- A coordinate line through a point off the two axes never meets the origin: the displacement
does not touch the other coordinate, which stays nonzero. -/
private theorem add_single_ne_zero {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2)
    (s : ℝ) : z + s • Pi.single j 1 ≠ 0 := by
  intro h
  have hd : diamondNorm (z + s • Pi.single j 1) = 0 := diamondNorm_eq_zero_iff.2 h
  rw [diamondNorm_add_single] at hd
  linarith [abs_nonneg (z j + s), abs_pos.2 (coord_succ_ne_zero h0 h1 j)]

private theorem sub_single_ne_zero {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2)
    (s : ℝ) : z - s • Pi.single j 1 ≠ 0 := by
  rw [sub_eq_add_neg, ← neg_smul]
  exact add_single_ne_zero h0 h1 j (-s)

/-! ### Nonnegativity of the tail's generator inside the diamond -/

/-- **The generator of the exterior tail is nonnegative inside the diamond.** At a point `z` of
the punctured closed diamond the tail vanishes, so every second difference is a sum of two
nonnegative displaced values; the Bochner integral of a nonnegative function is nonnegative
whether or not it is integrable. -/
theorem jumpGen_truncTail_nonneg {α R : ℝ} (hα : 0 < α) {z : Fin 2 → ℝ} (hz0 : z ≠ 0)
    (hz : diamondNorm z < R) : 0 ≤ jumpGen α (truncTail α R) z := by
  have hT : truncTail α R z = 0 := truncTail_eq_zero hα hz0 hz.le
  unfold jumpGen
  refine Finset.sum_nonneg fun j _ => integral_nonneg fun t => ?_
  have e1 := truncTail_nonneg α R (z + t • Pi.single j 1)
  have e2 := truncTail_nonneg α R (z - t • Pi.single j 1)
  rw [secondDiff, hT]
  exact mul_nonneg (by linarith) (Real.rpow_nonneg (abs_nonneg t) _)

/-! ### Integrability of the two integrands -/

/-- The second difference of `w ↦ (|w| + b)^{-α}` only sees `|a|`, the sign of `a` merely
exchanging the two outer terms. -/
private theorem diamondDiff_abs_eq (α b t a : ℝ) :
    ((|a + t| + b) ^ (-α) + (|a - t| + b) ^ (-α) - 2 * (|a| + b) ^ (-α)) * |t| ^ (-(1 + α))
      = diamondDiff α |a| b t := by
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha]
    rfl
  · rw [abs_of_nonpos ha, diamondDiff, show -a + t = -(a - t) by ring,
      show -a - t = -(a + t) by ring, abs_neg, abs_neg]
    ring

private theorem diamondPow_add_single (α : ℝ) (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondPow α (z + s • Pi.single j 1) = (|z j + s| + |z (j + 1)|) ^ (-α) := by
  rw [diamondPow, diamondNorm_add_single]

private theorem diamondPow_sub_single (α : ℝ) (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondPow α (z - s • Pi.single j 1) = (|z j - s| + |z (j + 1)|) ^ (-α) := by
  rw [diamondPow, diamondNorm_sub_single]

/-- The integrand of the generator of the diamond power is the profile integrand of
`CenteredMaximal.Fractional.DiamondReduction`, direction by direction. -/
private theorem secondDiff_diamondPow_mul (α : ℝ) (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    secondDiff (diamondPow α) j z t * |t| ^ (-(1 + α))
      = diamondDiff α |z j| |z (j + 1)| t := by
  rw [secondDiff, diamondPow_add_single, diamondPow_sub_single, diamondPow,
    diamondNorm_eq_abs_add z j]
  exact diamondDiff_abs_eq α |z (j + 1)| t (z j)

/-- **The diamond power's integrand is integrable** at every point off the coordinate axes. -/
theorem integrable_secondDiff_diamondPow {α : ℝ} (hα : 0 < α) (hα' : α < 2) {z : Fin 2 → ℝ}
    (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2) :
    Integrable fun t : ℝ => secondDiff (diamondPow α) j z t * |t| ^ (-(1 + α)) := by
  have hb : (0 : ℝ) < |z (j + 1)| := abs_pos.2 (coord_succ_ne_zero h0 h1 j)
  have ha : (0 : ℝ) < |z j| := by
    have h := diamondNorm_eq_abs_add z j
    fin_cases j
    · exact abs_pos.2 h0
    · exact abs_pos.2 h1
  exact (integrable_diamondDiff hα hα' ha hb).congr
    (Filter.Eventually.of_forall fun t => (secondDiff_diamondPow_mul α z j t).symm)

/-- Below the threshold `R − r(z)` the tail's second difference is identically zero: all three
points `z`, `z ± t e_j` then lie in the closed diamond of radius `R` and none of them is the
origin. -/
private theorem secondDiff_truncTail_eq_zero {α R : ℝ} (hα : 0 < α) {z : Fin 2 → ℝ}
    (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2) {t : ℝ} (ht : diamondNorm z + |t| ≤ R) :
    secondDiff (truncTail α R) j z t = 0 := by
  have hz0 : z ≠ 0 := fun h => h0 (by simp [h])
  have hr := diamondNorm_eq_abs_add z j
  have hp : diamondNorm (z + t • Pi.single j 1) ≤ R := by
    rw [diamondNorm_add_single]
    linarith [abs_add_le (z j) t]
  have habs : |z j - t| ≤ |z j| + |t| := by
    rw [sub_eq_add_neg, ← abs_neg t]
    exact abs_add_le _ _
  have hm : diamondNorm (z - t • Pi.single j 1) ≤ R := by
    rw [diamondNorm_sub_single]
    linarith
  rw [secondDiff, truncTail_eq_zero hα (add_single_ne_zero h0 h1 j t) hp,
    truncTail_eq_zero hα (sub_single_ne_zero h0 h1 j t) hm,
    truncTail_eq_zero hα hz0 (by linarith [abs_nonneg t])]
  ring

private theorem measurable_secondDiff_truncTail_mul (α R : ℝ) (z : Fin 2 → ℝ) (j : Fin 2) :
    Measurable fun t : ℝ => secondDiff (truncTail α R) j z t * |t| ^ (-(1 + α)) := by
  have hc : Continuous fun t : ℝ => z + t • Pi.single j 1 :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hc' : Continuous fun t : ℝ => z - t • Pi.single j 1 :=
    continuous_const.sub (continuous_id.smul continuous_const)
  unfold secondDiff
  exact ((((measurable_truncTail α R).comp hc.measurable).add
    ((measurable_truncTail α R).comp hc'.measurable)).sub measurable_const).mul
    (continuous_abs.measurable.pow_const _)

/-- **The tail's integrand is integrable** at a point of the open diamond off the coordinate axes.
It vanishes on `|t| ≤ R − r(z)` and is dominated by `4 R^{-α} |t|^{-(1+α)}` beyond. -/
theorem integrable_secondDiff_truncTail {α R : ℝ} (hα : 0 < α) {z : Fin 2 → ℝ}
    (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (hz : diamondNorm z < R) (j : Fin 2) :
    Integrable fun t : ℝ => secondDiff (truncTail α R) j z t * |t| ^ (-(1 + α)) := by
  have hR : 0 < R := lt_of_le_of_lt (diamondNorm_nonneg z) hz
  set ρ : ℝ := R - diamondNorm z with hρ_def
  have hρ : 0 < ρ := by rw [hρ_def]; linarith
  have hmeas := measurable_secondDiff_truncTail_mul α R z j
  refine integrable_of_even (fun t => by rw [secondDiff_neg, abs_neg]) ?_
  rw [← Ioc_union_Ioi_eq_Ioi hρ.le, integrableOn_union]
  refine ⟨(integrable_zero ℝ ℝ volume).integrableOn.congr_fun (fun t ht => ?_)
    measurableSet_Ioc, ?_⟩
  · have hsmall : diamondNorm z + |t| ≤ R := by
      rw [abs_of_pos ht.1]
      linarith [ht.2]
    show (0 : ℝ) = _
    rw [secondDiff_truncTail_eq_zero hα h0 h1 j hsmall, zero_mul]
  · have hdom : IntegrableOn (fun t : ℝ => 4 * R ^ (-α) * t ^ (-(1 + α))) (Ioi ρ) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hρ).const_mul _
    refine hdom.mono' hmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    have hb := abs_secondDiff_le_const (abs_truncTail_le hR α) j z t
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _),
      abs_of_pos (hρ.trans ht)]
    exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (hρ.trans ht).le _)

/-! ### The generator of the truncated base -/

/-- A constant function has vanishing second difference. -/
theorem secondDiff_const (c : ℝ) (j : Fin 2) (x : Fin 2 → ℝ) (t : ℝ) :
    secondDiff (fun _ : Fin 2 → ℝ => c) j x t = 0 := by
  simp only [secondDiff]
  ring

/-- A constant function has vanishing generator. -/
theorem jumpGen_const (α c : ℝ) (x : Fin 2 → ℝ) : jumpGen α (fun _ => c) x = 0 := by
  simp [jumpGen, secondDiff_const]

/-- Subtracting a constant does not change a second difference. -/
theorem secondDiff_sub_const (φ : (Fin 2 → ℝ) → ℝ) (c : ℝ) (j : Fin 2) (x : Fin 2 → ℝ) (t : ℝ) :
    secondDiff (fun w => φ w - c) j x t = secondDiff φ j x t := by
  simp only [secondDiff]
  ring

/-- A constant has vanishing generator, so subtracting one does not change the generator. -/
theorem jumpGen_sub_const (α : ℝ) (φ : (Fin 2 → ℝ) → ℝ) (c : ℝ) (x : Fin 2 → ℝ) :
    jumpGen α (fun w => φ w - c) x = jumpGen α φ x := by
  simp only [jumpGen, secondDiff_sub_const]

/-- **The generator of the truncated diamond base.** Inside the open diamond, off the coordinate
axes, it is the closed-form generator of the diamond power plus the nonnegative generator of the
exterior tail; the truncation constant contributes nothing. -/
theorem jumpGen_truncBase {α R : ℝ} (hα : 1 < α) (hα' : α < 2) {z : Fin 2 → ℝ}
    (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (hz : diamondNorm z < R) :
    jumpGen α (truncBase α R) z
      = -4 * π * Real.Gamma (2*α) * Real.cos (π*α/2)
          / (α * Real.Gamma α ^ 2 * Real.sin (π*α/2)) * diamondNorm z ^ (-2*α)
        + jumpGen α (truncTail α R) z := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hfun : truncBase α R = (fun w => diamondPow α w - R ^ (-α)) + truncTail α R := by
    funext w
    exact truncBase_eq α R w
  have hbase : ∀ j, Integrable fun t : ℝ =>
      secondDiff (fun w => diamondPow α w - R ^ (-α)) j z t * |t| ^ (-(1 + α)) := fun j => by
    simpa only [secondDiff_sub_const] using integrable_secondDiff_diamondPow hα0 hα' h0 h1 j
  have htail := integrable_secondDiff_truncTail (R := R) hα0 h0 h1 hz
  rw [hfun, jumpGen_add hbase htail, jumpGen_sub_const,
    jumpGen_diamondPow_eq_const hα hα' h0 h1]

/-- **The reserve the certificate consumes.** Dropping the nonnegative tail generator leaves the
closed-form lower bound
`-4π Γ(2α) cos(πα/2) / (α Γ(α)² sin(πα/2)) · r(z)^{-2α} ≤ jumpGen α (truncBase α R) z`
inside the open diamond, off the coordinate axes. The coefficient is positive for `1 < α < 2`,
since `cos(πα/2) < 0` there; at `α = 6/5` it is `5.0134934972…`. -/
theorem jumpGen_truncBase_ge {α R : ℝ} (hα : 1 < α) (hα' : α < 2) {z : Fin 2 → ℝ}
    (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (hz : diamondNorm z < R) :
    -4 * π * Real.Gamma (2*α) * Real.cos (π*α/2)
        / (α * Real.Gamma α ^ 2 * Real.sin (π*α/2)) * diamondNorm z ^ (-2*α)
      ≤ jumpGen α (truncBase α R) z := by
  rw [jumpGen_truncBase hα hα' h0 h1 hz]
  linarith [jumpGen_truncTail_nonneg (R := R) (by linarith : (0:ℝ) < α)
    (fun h => h0 (by simp [h])) hz]

end CenteredMaximal.Fractional

end

end
