/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.JumpGenerator
public import CenteredMaximal.Cauchy.LooseKernel
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Reducing the diamond power to a one-dimensional profile

The fractional layer of the planar centred maximal bound needs the jump generator of order
`α ∈ (1, 2)` applied to the **diamond power** `z ↦ r(z)^{-α}`, where `r = |u| + |v|` is the diamond
radius `CenteredMaximal.Cauchy.diamondNorm`. This file performs the first step: it collapses the
two-dimensional generator into a sum of two copies of a one-dimensional **profile** and records the
homogeneity of that profile. The closed evaluation of the profile, and the constancy of the sum
along the diamond, are not treated here.

Since `r (z + t e_j) = |z j + t| + |z (j + 1)|`, the axis-`j` second difference of `r^{-α}` at `z`
is the second difference of the one-dimensional function `w ↦ (|w| + b)^{-α}` with
`b = |z (j + 1)|`, evaluated at `a = z j`, and that second difference only sees `|a|`
(`diamondDiff_abs_left`), the sign of `a` merely exchanging the two outer terms. Writing

`diamondProfile α a b = ∫_ℝ ((|a + t| + b)^{-α} + (|a − t| + b)^{-α} − 2 (a + b)^{-α}) w(t) dt`

with the jump weight `w(t) = |t|^{-(1+α)}`, the generator is therefore the *sum of two profiles*,
one for each coordinate direction.

## Main results

* `diamondPow`, `diamondDiff`, `diamondProfile`: the diamond power, the integrand of the profile
  and the profile itself.
* `integrable_diamondDiff`: the integrand is integrable on `ℝ` for `0 < α < 2`, `0 < a`, `0 < b`.
* `jumpGen_diamondPow`: `jumpGen α (diamondPow α) z = P α |z 0| |z 1| + P α |z 1| |z 0|` off the
  coordinate axes, with `P = diamondProfile`.
* `diamondProfile_smul`, `diamondProfile_eq_rpow_mul`: the homogeneity
  `P α (c a) (c b) = c^{−2α} P α a b` and its normalisation to the unit diamond.
* `jumpGen_diamondPow_eq`: the resulting radial homogeneity of the generator.

## Integrability

Two régimes, split at `t = a / 2`. Near the origin the second difference is `O(t²)`: for
`|t| ≤ a / 2` both moduli open up, `|a ± t| = a ± t`, and the bracket becomes the symmetric second
difference of the smooth function `y ↦ y^{-α}` at `y = a + b` with step `t`, which stays inside the
half-line `[a/2 + b, ∞)`. Two applications of Lagrange's mean value theorem, one on each side,
turn that second difference into `t (g'(u) − g'(v))` with `u`, `v` in the half-line, and the mean
value *inequality* for `g'` — whose derivative `α (α + 1) y^{-α-2}` is bounded by
`α (α + 1) (a/2 + b)^{-α-2}` there — gives `|g'(u) − g'(v)| ≤ 2 α (α + 1) (a/2 + b)^{-α-2} t`; this
is `abs_rpow_secondDiff_le`. Against the weight the integrand is then `O(t^{1−α})`, integrable
because `α < 2`. Past `t = a / 2` the bracket is merely bounded, by `4 b^{-α}`, and the weight
`|t|^{-(1+α)}` is integrable at infinity because `α > 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-- The diamond power `r ^ (-α)`, with `r = |u| + |v|` the diamond radius. -/
def diamondPow (α : ℝ) (z : Fin 2 → ℝ) : ℝ := diamondNorm z ^ (-α)

/-- The integrand of the one-dimensional profile: the symmetric second difference of
`w ↦ (|w| + b)^{-α}` at `a` with step `t`, against the jump weight `|t|^{-(1+α)}`. -/
def diamondDiff (α a b t : ℝ) : ℝ :=
  ((|a + t| + b) ^ (-α) + (|a - t| + b) ^ (-α) - 2 * (a + b) ^ (-α)) * |t| ^ (-(1 + α))

/-- The one-dimensional profile: the directional jump integral at distance `a` from the axis,
with `b` the other coordinate. -/
def diamondProfile (α a b : ℝ) : ℝ :=
  ∫ t : ℝ, ((|a + t| + b) ^ (-α) + (|a - t| + b) ^ (-α) - 2 * (a + b) ^ (-α)) * |t| ^ (-(1 + α))

theorem diamondProfile_eq_integral (α a b : ℝ) :
    diamondProfile α a b = ∫ t : ℝ, diamondDiff α a b t := rfl

/-! ### Elementary properties of the integrand -/

/-- The integrand is even in the step. -/
theorem diamondDiff_neg (α a b t : ℝ) : diamondDiff α a b (-t) = diamondDiff α a b t := by
  simp only [diamondDiff, ← sub_eq_add_neg, sub_neg_eq_add, abs_neg]
  ring

private theorem measurable_diamondDiff (α a b : ℝ) : Measurable (diamondDiff α a b) := by
  unfold diamondDiff
  exact ((((continuous_const.add continuous_id).abs.add
      continuous_const).measurable.pow_const _).add
    (((continuous_const.sub continuous_id).abs.add
      continuous_const).measurable.pow_const _) |>.sub measurable_const).mul
    (continuous_abs.measurable.pow_const _)

/-- The second difference of `w ↦ (|w| + b)^{-α}` only sees `|a|`, the sign of `a` merely
exchanging the two outer terms. -/
private theorem diamondDiff_abs_left (α a b t : ℝ) :
    ((|a + t| + b) ^ (-α) + (|a - t| + b) ^ (-α) - 2 * (|a| + b) ^ (-α)) * |t| ^ (-(1 + α))
      = diamondDiff α |a| b t := by
  simp only [diamondDiff]
  rcases abs_cases a with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, show -a + t = -(a - t) from by ring, abs_neg, show -a - t = -(a + t) from by ring,
      abs_neg]
    ring

/-! ### The second-difference bound for `y ↦ y^{-α}` -/

/-- **The quantitative second-difference bound.** If the step `t` keeps `x ± t` inside the
half-line `[c, ∞)`, the symmetric second difference of `y ↦ y^{-α}` at `x` is `O(t²)`, with the
constant `2 α (α + 1) c^{-α-2}` coming from the bound `α (α + 1) c^{-α-2}` for the second
derivative on that half-line.

Both increments are turned into derivative values by Lagrange's mean value theorem, and their
difference is controlled by the mean value inequality for the first derivative. -/
private theorem abs_rpow_secondDiff_le {α c x t : ℝ} (hα : 0 < α) (hc : 0 < c) (ht0 : 0 ≤ t)
    (ht : t ≤ x - c) :
    |(x + t) ^ (-α) + (x - t) ^ (-α) - 2 * x ^ (-α)|
      ≤ 2 * (α * (α + 1) * c ^ (-α - 2)) * t ^ 2 := by
  have hM0 : (0 : ℝ) ≤ α * (α + 1) * c ^ (-α - 2) := by positivity
  set M := α * (α + 1) * c ^ (-α - 2) with hM
  -- the first two derivatives of `y ↦ y^{-α}` away from the origin
  have hd1 : ∀ y : ℝ, y ≠ 0 → HasDerivAt (fun y : ℝ => y ^ (-α)) (-α * y ^ (-α - 1)) y :=
    fun _ hy => Real.hasDerivAt_rpow_const (Or.inl hy)
  have hd2 : ∀ y : ℝ, y ≠ 0 →
      HasDerivAt (fun y : ℝ => -α * y ^ (-α - 1)) (α * (α + 1) * y ^ (-α - 2)) y := by
    intro y hy
    have h := (Real.hasDerivAt_rpow_const (x := y) (p := -α - 1) (Or.inl hy)).const_mul (-α)
    rw [show (-α - 1 - 1 : ℝ) = -α - 2 from by ring] at h
    exact h.congr_deriv (by ring)
  -- the second derivative is bounded by `M` on `[c, ∞)`
  have hbd : ∀ y ∈ Ici c, ‖α * (α + 1) * y ^ (-α - 2)‖ ≤ M := by
    intro y hy
    have hy0 : 0 < y := hc.trans_le hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hM]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hc hy (by linarith))
      (by positivity)
  -- hence the first derivative is `M`-Lipschitz there
  have hmv : ∀ u ∈ Ici c, ∀ v ∈ Ici c,
      |-α * u ^ (-α - 1) - -α * v ^ (-α - 1)| ≤ M * |u - v| := by
    intro u hu v hv
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun y : ℝ => -α * y ^ (-α - 1))
      (f' := fun y : ℝ => α * (α + 1) * y ^ (-α - 2)) (s := Ici c)
      (fun y hy => (hd2 y (hc.trans_le hy).ne').hasDerivWithinAt) hbd (convex_Ici c) hv hu
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h
  rcases eq_or_lt_of_le ht0 with rfl | ht0'
  · rw [add_zero, sub_zero, show x ^ (-α) + x ^ (-α) - 2 * x ^ (-α) = 0 from by ring]
    simp
  have htne : t ≠ 0 := ht0'.ne'
  have hxc : c ≤ x - t := by linarith
  -- Lagrange's mean value theorem on each side of `x`
  have hcont1 : ContinuousOn (fun y : ℝ => y ^ (-α)) (Icc x (x + t)) := fun y hy =>
    (hd1 y (by linarith [hy.1] : (0 : ℝ) < y).ne').continuousAt.continuousWithinAt
  have hcont2 : ContinuousOn (fun y : ℝ => y ^ (-α)) (Icc (x - t) x) := fun y hy =>
    (hd1 y (by linarith [hy.1] : (0 : ℝ) < y).ne').continuousAt.continuousWithinAt
  obtain ⟨u, hu, hsu⟩ := exists_hasDerivAt_eq_slope (fun y : ℝ => y ^ (-α))
    (fun y : ℝ => -α * y ^ (-α - 1)) (by linarith : x < x + t) hcont1
    (fun y hy => hd1 y (by linarith [hy.1] : (0 : ℝ) < y).ne')
  obtain ⟨v, hv, hsv⟩ := exists_hasDerivAt_eq_slope (fun y : ℝ => y ^ (-α))
    (fun y : ℝ => -α * y ^ (-α - 1)) (by linarith : x - t < x) hcont2
    (fun y hy => hd1 y (by linarith [hy.1] : (0 : ℝ) < y).ne')
  have e1 : (x + t) ^ (-α) - x ^ (-α) = t * (-α * u ^ (-α - 1)) := by
    rw [hsu, show x + t - x = t from by ring]
    field_simp
  have e2 : x ^ (-α) - (x - t) ^ (-α) = t * (-α * v ^ (-α - 1)) := by
    rw [hsv, show x - (x - t) = t from by ring]
    field_simp
  have hN : (x + t) ^ (-α) + (x - t) ^ (-α) - 2 * x ^ (-α)
      = t * (-α * u ^ (-α - 1) - -α * v ^ (-α - 1)) := by linear_combination e1 - e2
  have hbnd := hmv u (mem_Ici.2 (by linarith [hu.1])) v (mem_Ici.2 (by linarith [hv.1]))
  have h2t : |-α * u ^ (-α - 1) - -α * v ^ (-α - 1)| ≤ M * (2 * t) := by
    refine hbnd.trans (mul_le_mul_of_nonneg_left ?_ hM0)
    rw [abs_of_pos (by linarith [hu.1, hv.2] : (0 : ℝ) < u - v)]
    linarith [hu.2, hv.1]
  rw [hN, abs_mul, abs_of_pos ht0']
  calc t * |-α * u ^ (-α - 1) - -α * v ^ (-α - 1)| ≤ t * (M * (2 * t)) :=
        mul_le_mul_of_nonneg_left h2t ht0'.le
    _ = 2 * M * t ^ 2 := by ring

/-! ### Integrability of the profile integrand -/

/-- **Near the origin.** For `0 < t ≤ a / 2` both moduli open up and the bracket is the second
difference of `y ↦ y^{-α}` at `a + b`, hence `O(t²)`; against the weight the integrand is
`O(t^{1−α})`, which is integrable because `α < 2`. -/
private theorem integrableOn_diamondDiff_Ioc {α a b : ℝ} (hα : 0 < α) (hα' : α < 2) (ha : 0 < a)
    (hb : 0 < b) : IntegrableOn (diamondDiff α a b) (Ioc 0 (a / 2)) := by
  set K := 2 * (α * (α + 1) * (a / 2 + b) ^ (-α - 2)) with hK
  have hK0 : (0 : ℝ) ≤ K := by rw [hK]; positivity
  have hi : IntegrableOn (fun t : ℝ => K * t ^ (1 - α)) (Ioc 0 (a / 2)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul K
  refine hi.mono' (measurable_diamondDiff α a b).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  obtain ⟨ht0, ht2⟩ := ht
  have h1 : |a + t| = a + t := abs_of_pos (by linarith)
  have h2 : |a - t| = a - t := abs_of_nonneg (by linarith)
  have hsd := abs_rpow_secondDiff_le (α := α) (c := a / 2 + b) (x := a + b) (t := t) hα
    (by positivity) ht0.le (by linarith)
  rw [Real.norm_eq_abs, diamondDiff, h1, h2, abs_of_pos ht0, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ht0.le _), show a + t + b = a + b + t from by ring,
    show a - t + b = a + b - t from by ring]
  calc |(a + b + t) ^ (-α) + (a + b - t) ^ (-α) - 2 * (a + b) ^ (-α)| * t ^ (-(1 + α))
      ≤ K * t ^ 2 * t ^ (-(1 + α)) :=
        mul_le_mul_of_nonneg_right hsd (Real.rpow_nonneg ht0.le _)
    _ = K * t ^ (1 - α) := by
        rw [mul_assoc, ← Real.rpow_two, ← Real.rpow_add ht0,
          show (2 : ℝ) + -(1 + α) = 1 - α from by ring]

/-- **Past the corner.** For `a / 2 < t` the bracket is bounded by `4 b^{-α}`, and the weight
`t^{-(1+α)}` is integrable at infinity because `α > 0`. -/
private theorem integrableOn_diamondDiff_Ioi {α a b : ℝ} (hα : 0 < α) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (diamondDiff α a b) (Ioi (a / 2)) := by
  have hi : IntegrableOn (fun t : ℝ => 4 * b ^ (-α) * t ^ (-(1 + α))) (Ioi (a / 2)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by positivity)).const_mul _
  refine hi.mono' (measurable_diamondDiff α a b).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have ht0 : 0 < t := lt_trans (by positivity) ht
  have hle : ∀ w : ℝ, 0 ≤ w → (w + b) ^ (-α) ≤ b ^ (-α) := fun w hw =>
    Real.rpow_le_rpow_of_nonpos hb (by linarith) (by linarith)
  have hnn : ∀ w : ℝ, 0 ≤ w → (0 : ℝ) ≤ (w + b) ^ (-α) := fun w hw =>
    Real.rpow_nonneg (by linarith) _
  have e1 := hle _ (abs_nonneg (a + t))
  have e2 := hle _ (abs_nonneg (a - t))
  have e3 := hle a ha.le
  have f1 := hnn _ (abs_nonneg (a + t))
  have f2 := hnn _ (abs_nonneg (a - t))
  have f3 := hnn a ha.le
  rw [Real.norm_eq_abs, diamondDiff, abs_of_pos ht0, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ht0.le _)
  rw [abs_le]
  constructor <;> linarith

/-- **The profile integrand is integrable.** Near the origin the second difference is `O(t²)`
because `a > 0` keeps the corner of `w ↦ (|w| + b)^{-α}` away, and at infinity the bracket is
bounded, leaving the integrable decay `|t|^{-(1+α)}`. -/
theorem integrable_diamondDiff {α a b : ℝ} (hα : 0 < α) (hα' : α < 2) (ha : 0 < a) (hb : 0 < b) :
    Integrable (diamondDiff α a b) := by
  refine integrable_of_even (diamondDiff_neg α a b) ?_
  rw [← Ioc_union_Ioi_eq_Ioi (by positivity : (0 : ℝ) ≤ a / 2), integrableOn_union]
  exact ⟨integrableOn_diamondDiff_Ioc hα hα' ha hb, integrableOn_diamondDiff_Ioi hα ha hb⟩

/-- The profile integrand is integrable on the half-line. -/
theorem integrableOn_diamondDiff_Ioi_zero {α a b : ℝ} (hα : 0 < α) (hα' : α < 2) (ha : 0 < a)
    (hb : 0 < b) : IntegrableOn (diamondDiff α a b) (Ioi 0) :=
  (integrable_diamondDiff hα hα' ha hb).integrableOn

/-! ### The two-dimensional reduction -/

private theorem diamondNorm_eq_abs_add (z : Fin 2 → ℝ) (j : Fin 2) :
    diamondNorm z = |z j| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem diamondNorm_add_single (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z + s • Pi.single j 1) = |z j + s| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

/-- Each coordinate direction contributes the corresponding one-dimensional profile. -/
private theorem integral_secondDiff_diamondPow (α : ℝ) (z : Fin 2 → ℝ) (j : Fin 2) :
    ∫ t : ℝ, secondDiff (diamondPow α) j z t * |t| ^ (-(1 + α))
      = diamondProfile α |z j| |z (j + 1)| := by
  have key : ∀ t : ℝ, secondDiff (diamondPow α) j z t * |t| ^ (-(1 + α))
      = diamondDiff α |z j| |z (j + 1)| t := by
    intro t
    have h1 : diamondPow α (z + t • Pi.single j 1) = (|z j + t| + |z (j + 1)|) ^ (-α) := by
      rw [diamondPow, diamondNorm_add_single]
    have h2 : diamondPow α (z - t • Pi.single j 1) = (|z j - t| + |z (j + 1)|) ^ (-α) := by
      rw [sub_eq_add_neg, ← neg_smul, diamondPow, diamondNorm_add_single, ← sub_eq_add_neg]
    have h3 : diamondPow α z = (|z j| + |z (j + 1)|) ^ (-α) := by
      rw [diamondPow, diamondNorm_eq_abs_add z j]
    rw [secondDiff, h1, h2, h3]
    exact diamondDiff_abs_left α (z j) |z (j + 1)| t
  rw [integral_congr_ae (Filter.Eventually.of_forall key), diamondProfile_eq_integral]

set_option linter.unusedVariables false in
/-- **The reduction.** Off the coordinate axes the jump generator of the diamond power is the sum
of the two one-dimensional profiles, one for each coordinate direction.

The identity is a pointwise identity of integrands, so it holds for every `α` and every `z`; the
standing hypotheses are kept in the signature because they are what makes the two profiles finite
(`integrable_diamondDiff`), which is what every consumer of this lemma needs. -/
theorem jumpGen_diamondPow {α : ℝ} (hα : 0 < α) (hα' : α < 2) {z : Fin 2 → ℝ}
    (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) :
    jumpGen α (diamondPow α) z
      = diamondProfile α |z 0| |z 1| + diamondProfile α |z 1| |z 0| := by
  have e0 := integral_secondDiff_diamondPow α z 0
  have e1 := integral_secondDiff_diamondPow α z 1
  rw [show (0 : Fin 2) + 1 = 1 from by decide] at e0
  rw [show (1 : Fin 2) + 1 = 0 from by decide] at e1
  unfold jumpGen
  rw [Fin.sum_univ_two, e0, e1]

/-! ### Homogeneity of the profile -/

set_option linter.unusedVariables false in
/-- **The homogeneity of the profile.** The substitution `t = c s` produces one factor `c^{-α}`
from the bracket and one factor `c^{-(1+α)}` from the weight, against one factor `c` from the
measure. Only `0 < c` enters the change of variables; `0 < α` is kept for interface uniformity. -/
theorem diamondProfile_smul {α : ℝ} (hα : 0 < α) {c a b : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hb : 0 < b) : diamondProfile α (c * a) (c * b) = c ^ (-2 * α) * diamondProfile α a b := by
  have hkey : ∀ s : ℝ,
      diamondDiff α (c * a) (c * b) (c * s) = c ^ (-(1 + 2 * α)) * diamondDiff α a b s := by
    intro s
    have hcc : c ^ (-α) * c ^ (-(1 + α)) = c ^ (-(1 + 2 * α)) := by
      rw [← Real.rpow_add hc, show -α + -(1 + α) = -(1 + 2 * α) from by ring]
    have h1 : |c * a + c * s| + c * b = c * (|a + s| + b) := by
      rw [show c * a + c * s = c * (a + s) from by ring, abs_mul, abs_of_pos hc]; ring
    have h2 : |c * a - c * s| + c * b = c * (|a - s| + b) := by
      rw [show c * a - c * s = c * (a - s) from by ring, abs_mul, abs_of_pos hc]; ring
    have h3 : c * a + c * b = c * (a + b) := by ring
    have h4 : |c * s| = c * |s| := by rw [abs_mul, abs_of_pos hc]
    simp only [diamondDiff]
    rw [h1, h2, h3, h4, Real.mul_rpow hc.le (by positivity), Real.mul_rpow hc.le (by positivity),
      Real.mul_rpow hc.le (by positivity), Real.mul_rpow hc.le (abs_nonneg s), ← hcc]
    ring
  have hcI : c ^ (-2 * α) = c * c ^ (-(1 + 2 * α)) := by
    rw [show (-2 * α : ℝ) = 1 + -(1 + 2 * α) from by ring, Real.rpow_add hc, Real.rpow_one]
  have hcv := Measure.integral_comp_mul_left (fun t : ℝ => diamondDiff α (c * a) (c * b) t) c
  simp only [hkey] at hcv
  rw [integral_const_mul] at hcv
  rw [diamondProfile_eq_integral, diamondProfile_eq_integral, hcI, mul_assoc, hcv, smul_eq_mul,
    abs_of_pos (inv_pos.2 hc), ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- The profile normalised to the unit diamond: `P α a b = (a + b)^{−2α} P α a' b'` with
`a' + b' = 1`. -/
theorem diamondProfile_eq_rpow_mul {α : ℝ} (hα : 0 < α) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    diamondProfile α a b
      = (a + b) ^ (-2 * α) * diamondProfile α (a / (a + b)) (b / (a + b)) := by
  have hs : 0 < a + b := by linarith
  have hne : a + b ≠ 0 := hs.ne'
  have h := diamondProfile_smul (α := α) hα (c := a + b) (a := a / (a + b)) (b := b / (a + b))
    hs (by positivity) (by positivity)
  rwa [show (a + b) * (a / (a + b)) = a from by field_simp,
    show (a + b) * (b / (a + b)) = b from by field_simp] at h

/-- **Radial homogeneity of the generator.** Combining the reduction with the homogeneity of the
profile, the generator of the diamond power is `r^{−2α}` times a function of the direction alone. -/
theorem jumpGen_diamondPow_eq {α : ℝ} (hα : 0 < α) (hα' : α < 2) {z : Fin 2 → ℝ}
    (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) :
    jumpGen α (diamondPow α) z = diamondNorm z ^ (-2 * α) *
      (diamondProfile α (|z 0| / diamondNorm z) (|z 1| / diamondNorm z)
        + diamondProfile α (|z 1| / diamondNorm z) (|z 0| / diamondNorm z)) := by
  have ha : 0 < |z 0| := abs_pos.2 h0
  have hb : 0 < |z 1| := abs_pos.2 h1
  have hr : diamondNorm z = |z 0| + |z 1| := rfl
  rw [jumpGen_diamondPow hα hα' h0 h1, hr, diamondProfile_eq_rpow_mul hα ha hb,
    diamondProfile_eq_rpow_mul hα hb ha, show |z 1| + |z 0| = |z 0| + |z 1| from add_comm _ _,
    mul_add]

end CenteredMaximal.Fractional

end

end
