/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.SplineGenerator

/-!
# The fractional generator of a tensor product of splines

The comparison kernel for `α = 6/5` is a truncated diamond power corrected by a finite linear
combination of **tensor products of shifted, scaled cardinal cubic B-splines**,

`∑_{i,j} C_{ij} β(c u − i) β(c v − j)`.

This file computes the two-dimensional jump generator `jumpGen` of such a combination, reducing it
to the one-dimensional generator `jumpGen1 α β` that `CenteredMaximal.Fractional.SplineGenerator`
already evaluates in closed form.

## Main results

* `jumpGen_tensor`: the **product rule**. For arbitrary `f g : ℝ → ℝ` and no hypotheses at all,
  `jumpGen α (f ⊗ g) z = jumpGen1 α f (z 0) * g (z 1) + f (z 0) * jumpGen1 α g (z 1)`.
  The reason is that the operator only ever moves one coordinate at a time, so in the `j`-th
  summand the other factor is a constant and comes out of the integral.
* `jumpGen1_comp_affine`: the one-dimensional generator under `y ↦ c y − d` with `c > 0` picks up
  exactly `c ^ α`, the weight contributing `c ^ (1 + α)` and the measure `c⁻¹`.
* `jumpGen_splineCell`, `jumpGen_splineCell_eq`: the generator of a single tensor spline cell
  `w ↦ β (c w₀ − i) β (c w₁ − j)`, first in terms of `jumpGen1 α β` and then with both
  occurrences expanded into the alternating sums of `|·| ^ (3 − α)` of `jumpGen1_bspline`.
* `jumpGen_splineSum`: the generator of a finite `ℝ`-linear combination of such cells.

## Integrability

The product rule and the affine scaling law are identities of *integrands*: they hold with no
hypotheses beyond `c > 0`, because `Measure.integral_comp_mul_left` needs none and a constant
factor may always be pulled out of a Bochner integral. Integrability is needed only for
`jumpGen_splineSum`, where the integral of a finite sum must be split.

It is obtained here **without** `ContDiff ℝ 2 bspline`, by the compact-support argument of
`jumpGen1_bspline` rather than the `jumpBound` API of `CenteredMaximal.Analysis.JumpGenerator`:
`integrable_bsplineJump` splits `(0, ∞)` at `R = |x| + 3`, on `(0, R]` expands the second
difference into the five truncated cubes handled by `integrableOn_cubeDiff` (this needs `α < 2`),
and on `(R, ∞)` uses that `β(x ± s)` already vanishes there, leaving `−2 β(x) s^{−(1+α)}`
(this needs `0 < α`). Evenness of the integrand then extends this to all of `ℝ`. The affine and
tensor cases follow from that one lemma by `Integrable.comp_mul_left'` and by multiplying with a
constant, since `secondDiff` of a tensor product factors.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace CenteredMaximal.Fractional

/-! ### The second difference of a tensor product -/

/-- Along the first axis only the first coordinate of a tensor product moves, so its second
difference is the one-dimensional second difference of the first factor times the second factor. -/
theorem secondDiff_tensor_zero (f g : ℝ → ℝ) (z : Fin 2 → ℝ) (t : ℝ) :
    secondDiff (fun w => f (w 0) * g (w 1)) 0 z t
      = (f (z 0 + t) + f (z 0 - t) - 2 * f (z 0)) * g (z 1) := by
  have e0 : (t • Pi.single (0 : Fin 2) (1 : ℝ)) 0 = t := by
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  have e1 : (t • Pi.single (0 : Fin 2) (1 : ℝ)) 1 = 0 := by
    rw [Pi.smul_apply, Pi.single_eq_of_ne (by decide), smul_zero]
  simp only [secondDiff, Pi.add_apply, Pi.sub_apply, e0, e1, add_zero, sub_zero]
  ring

/-- Along the second axis only the second coordinate of a tensor product moves. -/
theorem secondDiff_tensor_one (f g : ℝ → ℝ) (z : Fin 2 → ℝ) (t : ℝ) :
    secondDiff (fun w => f (w 0) * g (w 1)) 1 z t
      = f (z 0) * (g (z 1 + t) + g (z 1 - t) - 2 * g (z 1)) := by
  have e0 : (t • Pi.single (1 : Fin 2) (1 : ℝ)) 0 = 0 := by
    rw [Pi.smul_apply, Pi.single_eq_of_ne (by decide), smul_zero]
  have e1 : (t • Pi.single (1 : Fin 2) (1 : ℝ)) 1 = t := by
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  simp only [secondDiff, Pi.add_apply, Pi.sub_apply, e0, e1, add_zero, sub_zero]
  ring

/-- The second difference is homogeneous. -/
theorem secondDiff_const_mul (k : ℝ) (φ : (Fin 2 → ℝ) → ℝ) (j : Fin 2) (z : Fin 2 → ℝ) (t : ℝ) :
    secondDiff (fun w => k * φ w) j z t = k * secondDiff φ j z t := by
  simp only [secondDiff]
  ring

/-- The second difference is additive over a finite sum. -/
theorem secondDiff_finsetSum {ι : Type*} (s : Finset ι) (φ : ι → (Fin 2 → ℝ) → ℝ) (j : Fin 2)
    (z : Fin 2 → ℝ) (t : ℝ) :
    secondDiff (fun w => ∑ i ∈ s, φ i w) j z t = ∑ i ∈ s, secondDiff (φ i) j z t := by
  simp only [secondDiff, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ### The product rule -/

/-- **The product rule for the jump generator.** The generator only ever displaces one coordinate
at a time, so on a tensor product `w ↦ f (w 0) * g (w 1)` the `j`-th summand of `jumpGen` is the
one-dimensional jump integral of the `j`-th factor times the value of the other factor. No
hypotheses are needed: this is an identity of integrands. -/
theorem jumpGen_tensor (α : ℝ) (f g : ℝ → ℝ) (z : Fin 2 → ℝ) :
    jumpGen α (fun w => f (w 0) * g (w 1)) z
      = jumpGen1 α f (z 0) * g (z 1) + f (z 0) * jumpGen1 α g (z 1) := by
  simp only [jumpGen, Fin.sum_univ_two, jumpGen1]
  congr 1
  · rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [secondDiff_tensor_zero f g z]
    ring
  · rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [secondDiff_tensor_one f g z]
    ring

/-! ### The affine change of variables in one dimension -/

private theorem mul_assoc_cancel {K L : ℝ} (h : K * L = 1) (A W : ℝ) :
    A * W = K * (A * (L * W)) := by
  linear_combination (-(A * W)) * h

/-- The substitution `s = c t` at the level of integrands: the integrand of
`jumpGen1 α (f (c · − d))` at `x` is `c ^ (1 + α)` times the integrand of `jumpGen1 α f` at
`c x − d`, evaluated at `c t`. -/
theorem jumpIntegrand_comp_affine {α c : ℝ} (hc : 0 < c) (d : ℝ) (f : ℝ → ℝ) (x t : ℝ) :
    (f (c * (x + t) - d) + f (c * (x - t) - d) - 2 * f (c * x - d)) * |t| ^ (-(1 + α))
      = c ^ (1 + α) * ((f (c * x - d + c * t) + f (c * x - d - c * t) - 2 * f (c * x - d))
          * |c * t| ^ (-(1 + α))) := by
  have hcc : c ^ (1 + α) * c ^ (-(1 + α)) = 1 := by
    rw [← Real.rpow_add hc, show (1 + α) + -(1 + α) = 0 from by ring, Real.rpow_zero]
  rw [show c * (x + t) - d = c * x - d + c * t from by ring,
    show c * (x - t) - d = c * x - d - c * t from by ring, abs_mul, abs_of_pos hc,
    Real.mul_rpow hc.le (abs_nonneg t)]
  exact mul_assoc_cancel hcc _ _

/-- **Scaling and translation of the one-dimensional generator.** For `c > 0` and any `d`,
`jumpGen1 α (f (c · − d)) x = c ^ α * jumpGen1 α f (c x − d)`: the weight `|s|^{−(1+α)}`
contributes `c ^ (1 + α)` and the Lebesgue measure contributes `c⁻¹`. -/
theorem jumpGen1_comp_affine {α : ℝ} (_hα : 0 < α) {c : ℝ} (hc : 0 < c) (d : ℝ) (f : ℝ → ℝ)
    (x : ℝ) :
    jumpGen1 α (fun y => f (c * y - d)) x = c ^ α * jumpGen1 α f (c * x - d) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hcv := Measure.integral_comp_mul_left
    (fun u : ℝ => (f (c * x - d + u) + f (c * x - d - u) - 2 * f (c * x - d))
      * |u| ^ (-(1 + α))) c
  simp only [jumpGen1, smul_eq_mul, abs_of_pos (inv_pos.2 hc)] at hcv ⊢
  simp_rw [jumpIntegrand_comp_affine (α := α) hc d f x]
  rw [integral_const_mul, hcv, Real.rpow_add hc, Real.rpow_one]
  field_simp

/-! ### Integrability of the spline integrands -/

/-- The integrand of `jumpGen1 α bspline` is integrable on all of `ℝ` for `0 < α < 2`. The
argument is the one inside `jumpGen1_bspline`: past `R = |x| + 3` the shifted values of `β`
already vanish, and below `R` the second difference splits into the five truncated cubes of
`integrableOn_cubeDiff`. -/
theorem integrable_bsplineJump {α : ℝ} (hα : 0 < α) (hα' : α < 2) (x : ℝ) :
    Integrable fun s : ℝ =>
      (bspline (x + s) + bspline (x - s) - 2 * bspline x) * |s| ^ (-(1 + α)) := by
  have habs := abs_nonneg x
  set R : ℝ := |x| + 3 with hRdef
  have hR0 : 0 < R := by rw [hRdef]; linarith
  have hcR : ∀ q ∈ Finset.range 5, |x + 2 - (q : ℝ)| ≤ R := by
    intro q hq
    have hq4 : (q : ℝ) ≤ 4 := by
      exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hb : |2 - (q : ℝ)| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    calc |x + 2 - (q : ℝ)| ≤ |x| + |2 - (q : ℝ)| := by
          rw [show x + 2 - (q : ℝ) = x + (2 - q) by ring]; exact abs_add_le _ _
      _ ≤ |x| + 2 := by linarith
      _ ≤ R := by rw [hRdef]; linarith
  have hFeven : ∀ s : ℝ,
      (bspline (x + -s) + bspline (x - -s) - 2 * bspline x) * |(-s)| ^ (-(1 + α))
        = (bspline (x + s) + bspline (x - s) - 2 * bspline x) * |s| ^ (-(1 + α)) := by
    intro s
    rw [abs_neg, show x + -s = x - s by ring, show x - -s = x + s by ring]
    ring
  have hfsum : EqOn (fun s : ℝ => (bspline (x + s) + bspline (x - s) - 2 * bspline x) *
        |s| ^ (-(1 + α)))
      (fun s : ℝ => ∑ q ∈ Finset.range 5, 1 / 6 * ((-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ)) *
        (cubeDiff (x + 2 - q) s * s ^ (-(1 + α)))) (Ioc 0 R) := by
    intro s hs
    simp only
    rw [bspline_secondDiff, abs_of_pos hs.1, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hftail : EqOn (fun s : ℝ => (bspline (x + s) + bspline (x - s) - 2 * bspline x) *
        |s| ^ (-(1 + α))) (fun s : ℝ => -2 * bspline x * s ^ (-(1 + α))) (Ioi R) := by
    intro s hs
    have hs' : R < s := hs
    have hxa : -|x| ≤ x := neg_abs_le x
    have hxb : x ≤ |x| := le_abs_self x
    rw [hRdef] at hs'
    show (bspline (x + s) + bspline (x - s) - 2 * bspline x) * |s| ^ (-(1 + α))
      = -2 * bspline x * s ^ (-(1 + α))
    rw [bspline_of_two_le (by linarith : (2 : ℝ) ≤ x + s),
      bspline_of_le_neg_two (by linarith : x - s ≤ -2), abs_of_pos (hR0.trans hs)]
    ring
  have hint_bdd : IntegrableOn (fun s : ℝ => (bspline (x + s) + bspline (x - s) - 2 * bspline x) *
      |s| ^ (-(1 + α))) (Ioc 0 R) := by
    refine IntegrableOn.congr_fun ?_ (fun s hs => (hfsum hs).symm) measurableSet_Ioc
    exact integrable_finsetSum _ fun q hq =>
      (integrableOn_cubeDiff hα' _ (hcR q hq)).const_mul _
  have hint_tail : IntegrableOn (fun s : ℝ => (bspline (x + s) + bspline (x - s) - 2 * bspline x) *
      |s| ^ (-(1 + α))) (Ioi R) := by
    refine IntegrableOn.congr_fun ?_ (fun s hs => (hftail hs).symm) measurableSet_Ioi
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) hR0).const_mul _
  refine integrable_of_even hFeven ?_
  rw [← Ioc_union_Ioi_eq_Ioi hR0.le, integrableOn_union]
  exact ⟨hint_bdd, hint_tail⟩

/-- The integrand of `jumpGen1 α (bspline (c · − d))` is integrable, by the substitution
`s = c t` applied to `integrable_bsplineJump`. -/
theorem integrable_bsplineJump_affine {α : ℝ} (hα : 0 < α) (hα' : α < 2) {c : ℝ} (hc : 0 < c)
    (d x : ℝ) :
    Integrable fun t : ℝ => (bspline (c * (x + t) - d) + bspline (c * (x - t) - d)
      - 2 * bspline (c * x - d)) * |t| ^ (-(1 + α)) :=
  (((integrable_bsplineJump hα hα' (c * x - d)).comp_mul_left' hc.ne').const_mul
      (c ^ (1 + α))).congr
    (Filter.Eventually.of_forall fun t =>
      (jumpIntegrand_comp_affine (α := α) hc d bspline x t).symm)

/-- The integrand of `jumpGen` for a single tensor spline cell is integrable in both coordinate
directions: the second difference factors, so it is a constant multiple of a one-dimensional
spline integrand. -/
theorem integrable_secondDiff_splineCell {α : ℝ} (hα : 0 < α) (hα' : α < 2) {c : ℝ} (hc : 0 < c)
    (i j : ℝ) (z : Fin 2 → ℝ) (jj : Fin 2) :
    Integrable fun t : ℝ =>
      secondDiff (fun w => bspline (c * w 0 - i) * bspline (c * w 1 - j)) jj z t
        * |t| ^ (-(1 + α)) := by
  have h0 := secondDiff_tensor_zero (fun y => bspline (c * y - i)) (fun y => bspline (c * y - j)) z
  have h1 := secondDiff_tensor_one (fun y => bspline (c * y - i)) (fun y => bspline (c * y - j)) z
  revert jj
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · refine ((integrable_bsplineJump_affine hα hα' hc i (z 0)).mul_const
      (bspline (c * z 1 - j))).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [h0]
    ring
  · refine ((integrable_bsplineJump_affine hα hα' hc j (z 1)).const_mul
      (bspline (c * z 0 - i))).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [h1]
    ring

/-! ### The generator of a spline cell and of a finite sum of cells -/

/-- **The generator of one tensor spline cell.** For `c > 0` the product rule and the affine
scaling law give a single overall factor `c ^ α`. -/
theorem jumpGen_splineCell {α : ℝ} (hα : 0 < α) (_hα' : α < 2) (_hα1 : α ≠ 1) {c : ℝ}
    (hc : 0 < c) (i j : ℝ) (z : Fin 2 → ℝ) :
    jumpGen α (fun w => bspline (c * w 0 - i) * bspline (c * w 1 - j)) z
      = c ^ α * (jumpGen1 α bspline (c * z 0 - i) * bspline (c * z 1 - j)
          + bspline (c * z 0 - i) * jumpGen1 α bspline (c * z 1 - j)) := by
  rw [jumpGen_tensor α (fun y => bspline (c * y - i)) (fun y => bspline (c * y - j)) z,
    jumpGen1_comp_affine hα hc i bspline (z 0), jumpGen1_comp_affine hα hc j bspline (z 1)]
  ring

/-- **The generator of one tensor spline cell in closed form**, with both one-dimensional
generators expanded by `jumpGen1_bspline` into alternating sums of `|·| ^ (3 − α)`. -/
theorem jumpGen_splineCell_eq {α : ℝ} (hα : 0 < α) (hα' : α < 2) (hα1 : α ≠ 1) {c : ℝ}
    (hc : 0 < c) (i j : ℝ) (z : Fin 2 → ℝ) :
    jumpGen α (fun w => bspline (c * w 0 - i) * bspline (c * w 1 - j)) z
      = c ^ α * ((2 / (-(α * (1 - α) * (2 - α) * (3 - α)))
              * ∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ)
                  * |c * z 0 - i + 2 - q| ^ (3 - α)) * bspline (c * z 1 - j)
          + bspline (c * z 0 - i) * (2 / (-(α * (1 - α) * (2 - α) * (3 - α)))
              * ∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ)
                  * |c * z 1 - j + 2 - q| ^ (3 - α))) := by
  rw [jumpGen_splineCell hα hα' hα1 hc i j z, jumpGen1_bspline hα hα' hα1 (c * z 0 - i),
    jumpGen1_bspline hα hα' hα1 (c * z 1 - j)]

/-- The generator is homogeneous. -/
theorem jumpGen_const_mul (α k : ℝ) (φ : (Fin 2 → ℝ) → ℝ) (z : Fin 2 → ℝ) :
    jumpGen α (fun w => k * φ w) z = k * jumpGen α φ z := by
  simp only [jumpGen, secondDiff_const_mul, mul_assoc, integral_const_mul, Finset.mul_sum]

/-- The generator is additive over a finite sum of functions whose integrands are integrable. -/
theorem jumpGen_finsetSum {α : ℝ} {ι : Type*} (s : Finset ι) (φ : ι → (Fin 2 → ℝ) → ℝ)
    (z : Fin 2 → ℝ)
    (h : ∀ i ∈ s, ∀ j : Fin 2,
      Integrable fun t : ℝ => secondDiff (φ i) j z t * |t| ^ (-(1 + α))) :
    jumpGen α (fun w => ∑ i ∈ s, φ i w) z = ∑ i ∈ s, jumpGen α (φ i) z := by
  simp only [jumpGen, secondDiff_finsetSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => integral_finsetSum s fun i hi => h i hi j

/-- **The generator of a finite sum of tensor spline cells.** For `c > 0` and `0 < α < 2` with
`α ≠ 1`, the generator of `∑_{ij} C_{ij} β(c w₀ − i) β(c w₁ − j)` is the corresponding sum of the
single-cell generators of `jumpGen_splineCell`. -/
theorem jumpGen_splineSum {α : ℝ} (hα : 0 < α) (hα' : α < 2) (hα1 : α ≠ 1) {c : ℝ} (hc : 0 < c)
    (s : Finset (ℤ × ℤ)) (C : ℤ × ℤ → ℝ) (z : Fin 2 → ℝ) :
    jumpGen α (fun w => ∑ ij ∈ s, C ij * (bspline (c * w 0 - ij.1) * bspline (c * w 1 - ij.2))) z
      = ∑ ij ∈ s, C ij * (c ^ α * (jumpGen1 α bspline (c * z 0 - ij.1) * bspline (c * z 1 - ij.2)
          + bspline (c * z 0 - ij.1) * jumpGen1 α bspline (c * z 1 - ij.2))) := by
  have hint : ∀ ij ∈ s, ∀ j : Fin 2, Integrable fun t : ℝ =>
      secondDiff (fun w : Fin 2 → ℝ =>
        C ij * (bspline (c * w 0 - (ij.1 : ℝ)) * bspline (c * w 1 - (ij.2 : ℝ)))) j z t
          * |t| ^ (-(1 + α)) := by
    intro ij _ j
    have hk := secondDiff_const_mul (C ij) (fun w : Fin 2 → ℝ =>
      bspline (c * w 0 - (ij.1 : ℝ)) * bspline (c * w 1 - (ij.2 : ℝ))) j z
    refine ((integrable_secondDiff_splineCell hα hα' hc (ij.1 : ℝ) (ij.2 : ℝ) z j).const_mul
      (C ij)).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [hk]
    ring
  rw [jumpGen_finsetSum s (fun ij : ℤ × ℤ => fun w : Fin 2 → ℝ =>
    C ij * (bspline (c * w 0 - (ij.1 : ℝ)) * bspline (c * w 1 - (ij.2 : ℝ)))) z hint]
  exact Finset.sum_congr rfl fun ij _ => by
    rw [jumpGen_const_mul, jumpGen_splineCell hα hα' hα1 hc (ij.1 : ℝ) (ij.2 : ℝ) z]

end CenteredMaximal.Fractional

end

end
