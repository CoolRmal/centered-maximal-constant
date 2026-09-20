/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.TensorSpline
public import CenteredMaximal.Fractional.TruncatedBase

/-!
# The mass of the ingredients of the fractional comparison kernel

The comparison kernel of order `α = 6/5` is
`K = a · truncBase α R + ∑_{ij} C_{ij} β(N z₀ − i) β(N z₁ − j)`,
and its *mass* `∫ K` is twice the comparison cost the certificate pays. This file computes the
mass of each of the three ingredients separately.

## Main results

* `integral_bspline`: `∫ β = 1`. The five truncated cubes `(y₊)³` making up the cardinal cubic
  B-spline have divergent integrals on their own, so the computation is done on `[−2, 2]`, which
  contains the support (`intervalIntegral_bspline`), and extended by
  `bspline_of_two_le` / `bspline_of_le_neg_two`.
* `integral_truncBase`: `∫ truncBase α R = (4/(2 − α) − 2) R^{2−α}` for `0 < α < 2`, `0 < R`.
  At `α = 6/5` this is `3 R^{4/5}` (`integral_truncBase_six_fifths`).
* `integral_splineCell`: `∫ β(c z₀ − i) β(c z₁ − j) = (c²)⁻¹` for `c > 0`.

## Method

The B-spline's mass is a finite alternating sum of the elementary integrals
`∫_a^b (x − c)₊³ dx = (b − c)⁴/4` (`integral_truncCube_shift`), which come to
`(256 − 4·81 + 6·16 − 4·1)/4 = 6`, divided by the normalisation `6`.

The base is a function of `diamondNorm` alone, so its mass is given by the radial formula
`CenteredMaximal.Cauchy.lintegral_comp_diamondNorm`, exactly as `integral_looseCusp` does for the
Cauchy kernel: `∫_0^R 4t (t^{-α} − R^{-α}) dt = 4 R^{2−α}/(2−α) − 2 R^{2−α}`. The radial integrand
`4 t^{1−α}` is *not* continuous at the origin for `α > 1`, so the continuity-based helper of
`Cauchy.LooseKernel` does not apply and the `Ioc 0 R`/`Ioi R` split is done by hand with
`intervalIntegral.intervalIntegrable_rpow'`.

A single spline cell is a tensor product, so Fubini on `Fin 2 → ℝ` through
`volume_preserving_finTwoArrow` reduces its mass to two copies of `∫ β(c x − d) dx = c⁻¹`, which is
`integral_bspline` composed with the affine substitutions `Measure.integral_comp_mul_left` and
`integral_sub_right_eq_self`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### The mass of the cardinal cubic B-spline -/

/-- The elementary integral `∫_a^b (x − c)₊³ dx = (b − c)⁴/4` when the breakpoint `c` lies in
`[a, b]`: the integrand vanishes to the left of `c` and is `(x − c)³` to its right. -/
private theorem integral_truncCube_shift {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    ∫ x in a..b, truncCube (x - c) = (b - c) ^ 4 / 4 := by
  have hcont : Continuous fun x : ℝ => truncCube (x - c) :=
    continuous_truncCube.comp (continuous_id.sub continuous_const)
  have h1 : ∫ x in a..c, truncCube (x - c) = 0 := by
    have he : EqOn (fun x : ℝ => truncCube (x - c)) (fun _ : ℝ => (0 : ℝ)) (uIcc a c) :=
      fun x hx => by
        rw [uIcc_of_le hac] at hx
        exact truncCube_of_nonpos (by linarith [hx.2])
    rw [intervalIntegral.integral_congr he, intervalIntegral.integral_const, smul_zero]
  have h2 : ∫ x in c..b, truncCube (x - c) = (b - c) ^ 4 / 4 := by
    have he : EqOn (fun x : ℝ => truncCube (x - c)) (fun x : ℝ => (x - c) ^ 3) (uIcc c b) :=
      fun x hx => by
        rw [uIcc_of_le hcb] at hx
        exact truncCube_of_nonneg (by linarith [hx.1])
    rw [intervalIntegral.integral_congr he,
      intervalIntegral.integral_comp_sub_right (f := fun x : ℝ => x ^ 3) c, sub_self,
      integral_pow]
    norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := c)
    (hcont.intervalIntegrable a c) (hcont.intervalIntegrable c b), h1, h2, zero_add]

/-- **The B-spline has unit mass on its support.** Expanding the defining alternating sum and
evaluating each truncated cube by `integral_truncCube_shift` gives
`(1·4⁴ − 4·3⁴ + 6·2⁴ − 4·1⁴ + 0)/4 = 6`, and the normalisation `1/6` turns that into `1`. -/
theorem intervalIntegral_bspline : ∫ x in (-2 : ℝ)..2, bspline x = 1 := by
  have hint : ∀ q ∈ Finset.range 5, IntervalIntegrable
      (fun x : ℝ => (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * truncCube (x + 2 - q)) volume (-2) 2 :=
    fun q _ => Continuous.intervalIntegrable
      (continuous_const.mul (continuous_truncCube.comp (by fun_prop))) _ _
  have hterm : ∀ q ∈ Finset.range 5,
      ∫ x in (-2 : ℝ)..2, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * truncCube (x + 2 - q)
        = (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * ((4 - (q : ℝ)) ^ 4 / 4) := by
    intro q hq
    have hq4 : (q : ℝ) ≤ 4 := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have he : ∀ x : ℝ, x + 2 - (q : ℝ) = x - ((q : ℝ) - 2) := fun x => by ring
    simp only [he]
    rw [intervalIntegral.integral_const_mul,
      integral_truncCube_shift (by linarith : (-2 : ℝ) ≤ (q : ℝ) - 2) (by linarith),
      show (2 : ℝ) - ((q : ℝ) - 2) = 4 - (q : ℝ) from by ring]
  calc ∫ x in (-2 : ℝ)..2, bspline x
      = ∫ x in (-2 : ℝ)..2, 1 / 6 * ∑ q ∈ Finset.range 5,
          (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * truncCube (x + 2 - q) := by
        simp only [bspline]
    _ = 1 / 6 * ∑ q ∈ Finset.range 5, ∫ x in (-2 : ℝ)..2,
          (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * truncCube (x + 2 - q) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hint]
    _ = 1 / 6 * ∑ q ∈ Finset.range 5,
          (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * ((4 - (q : ℝ)) ^ 4 / 4) := by
        rw [Finset.sum_congr rfl hterm]
    _ = 1 := by
        norm_num [Finset.sum_range_succ, Nat.choose]

/-- The B-spline is continuous, being a linear combination of truncated cubes. -/
theorem continuous_bspline : Continuous bspline := by
  unfold bspline
  exact continuous_const.mul (continuous_finsetSum _ fun q _ =>
    continuous_const.mul (continuous_truncCube.comp (by fun_prop)))

/-- The B-spline is integrable: it is continuous and vanishes off `[−2, 2]`. -/
theorem integrable_bspline : Integrable bspline := by
  refine continuous_bspline.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun x hx => ?_)
  rw [mem_Icc]
  by_contra hc
  rw [not_and_or, not_le, not_le] at hc
  refine hx ?_
  rcases hc with h | h
  · exact bspline_of_le_neg_two h.le
  · exact bspline_of_two_le h.le

/-- **The cardinal cubic B-spline integrates to `1`.** The five truncated cubes it is built from
each have a divergent integral, so the computation runs over `[−2, 2]`, which contains the
support. -/
theorem integral_bspline : ∫ x : ℝ, bspline x = 1 := by
  have hz : ∀ x : ℝ, x ∉ Ioc (-2 : ℝ) 2 → bspline x = 0 := by
    intro x hx
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hx
    rcases hx with h | h
    · exact bspline_of_le_neg_two h
    · exact bspline_of_two_le h.le
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2), intervalIntegral_bspline]

/-! ### The mass of the truncated diamond base -/

/-- The truncated base is measurable. -/
theorem measurable_truncBase (α R : ℝ) : Measurable (truncBase α R) := by
  unfold truncBase
  exact ((measurable_diamondNorm.pow_const _).sub measurable_const).max measurable_const

theorem truncBase_nonneg (α R : ℝ) (z : Fin 2 → ℝ) : 0 ≤ truncBase α R z := le_max_right _ _

/-- The radial profile `(t^{-α} − R^{-α})₊` of the truncated base. -/
private def baseProfile (α R t : ℝ) : ℝ := max (t ^ (-α) - R ^ (-α)) 0

/-- The base is a function of the diamond radius alone. -/
private theorem truncBase_eq_baseProfile (α R : ℝ) (z : Fin 2 → ℝ) :
    truncBase α R z = baseProfile α R (diamondNorm z) := rfl

private theorem measurable_baseProfile (α R : ℝ) : Measurable (baseProfile α R) :=
  ((measurable_id.pow_const _).sub measurable_const).max measurable_const

private theorem baseProfile_nonneg (α R t : ℝ) : 0 ≤ baseProfile α R t := le_max_right _ _

/-- The profile vanishes beyond the truncation radius. -/
private theorem baseProfile_eq_zero {α R t : ℝ} (hα : 0 ≤ α) (hR : 0 < R) (ht : R ≤ t) :
    baseProfile α R t = 0 :=
  max_eq_right (sub_nonpos.2 (Real.rpow_le_rpow_of_nonpos hR ht (neg_nonpos.2 hα)))

/-- On `(0, R]` the radial integrand `4 t (t^{-α} − R^{-α})₊` of the truncated base is the
difference of the two elementary powers `4 t^{1−α}` and `4 R^{-α} t`. -/
private theorem baseIntegrand_eq {α R t : ℝ} (hα : 0 ≤ α) (ht : 0 < t) (htR : t ≤ R) :
    4 * t * baseProfile α R t = 4 * t ^ (1 - α) - 4 * R ^ (-α) * t := by
  have hmax : 0 ≤ t ^ (-α) - R ^ (-α) :=
    sub_nonneg.2 (Real.rpow_le_rpow_of_nonpos ht htR (neg_nonpos.2 hα))
  have h : t * t ^ (-α) = t ^ (1 - α) := by
    rw [show (1 : ℝ) - α = 1 + -α from by ring, Real.rpow_add ht, Real.rpow_one]
  rw [baseProfile, max_eq_left hmax]
  nlinarith [h]

/-- `∫_0^R (4 t^{1−α} − 4 R^{-α} t) dt = 4 R^{2−α}/(2−α) − 2 R^{2−α}`. Only `α < 2` is needed:
the exponent `1 − α` stays above `−1`, so the power is interval integrable up to the origin. -/
private theorem intervalIntegral_baseProfile {α R : ℝ} (hα' : α < 2) (hR : 0 < R) :
    ∫ t in (0 : ℝ)..R, (4 * t ^ (1 - α) - 4 * R ^ (-α) * t)
      = (4 / (2 - α) - 2) * R ^ (2 - α) := by
  have h2α : (0 : ℝ) < 2 - α := by linarith
  have h1 : IntervalIntegrable (fun t : ℝ => t ^ (1 - α)) volume 0 R :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have h2 : IntervalIntegrable (fun t : ℝ => t) volume 0 R := continuous_id.intervalIntegrable _ _
  have hpow : R ^ (-α) * R ^ 2 = R ^ (2 - α) := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_add hR,
      show -α + ((2 : ℕ) : ℝ) = 2 - α from by push_cast; ring]
  rw [intervalIntegral.integral_sub (h1.const_mul 4) (h2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : (-1 : ℝ) < 1 - α)), integral_id,
    show (1 : ℝ) - α + 1 = 2 - α from by ring, Real.zero_rpow h2α.ne']
  linear_combination (-2 : ℝ) * hpow

/-- The radial integrand of the truncated base is integrable on `(0, R]`. -/
private theorem integrableOn_baseIntegrand {α R : ℝ} (hα' : α < 2) (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => 4 * t ^ (1 - α) - 4 * R ^ (-α) * t) (Ioc 0 R) := by
  have h1 : IntervalIntegrable (fun t : ℝ => t ^ (1 - α)) volume 0 R :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have h2 : IntervalIntegrable (fun t : ℝ => t) volume 0 R := continuous_id.intervalIntegrable _ _
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).1
    ((h1.const_mul 4).sub (h2.const_mul _))

/-- **The mass of the truncated diamond base, as a lower Lebesgue integral.** The base is a
function of the diamond radius alone, so the radial formula
`CenteredMaximal.Cauchy.lintegral_comp_diamondNorm` applies; the profile vanishes beyond `R`. -/
private theorem lintegral_truncBase {α R : ℝ} (hα : 0 < α) (hα' : α < 2) (hR : 0 < R) :
    ∫⁻ z, ENNReal.ofReal (truncBase α R z)
      = ENNReal.ofReal ((4 / (2 - α) - 2) * R ^ (2 - α)) := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) R)]
      fun t : ℝ => 4 * t ^ (1 - α) - 4 * R ^ (-α) * t :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
      show (0 : ℝ) ≤ 4 * t ^ (1 - α) - 4 * R ^ (-α) * t
      rw [← baseIntegrand_eq hα.le ht.1 ht.2]
      exact mul_nonneg (by linarith [ht.1]) (baseProfile_nonneg α R t)
  have hhead : ∫⁻ t in Ioc (0 : ℝ) R,
      4 * ENNReal.ofReal t * ENNReal.ofReal (baseProfile α R t)
        = ENNReal.ofReal ((4 / (2 - α) - 2) * R ^ (2 - α)) := by
    rw [← intervalIntegral_baseProfile hα' hR, intervalIntegral.integral_of_le hR.le,
      ofReal_integral_eq_lintegral_ofReal (integrableOn_baseIntegrand hα' hR) hnn]
    refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht.1
    rw [← baseIntegrand_eq hα.le ht.1 ht.2,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * t),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have htail : ∫⁻ t in Ioi R,
      4 * ENNReal.ofReal t * ENNReal.ofReal (baseProfile α R t) = 0 := by
    refine setLIntegral_eq_zero measurableSet_Ioi fun t ht => ?_
    simp [baseProfile_eq_zero hα.le hR (le_of_lt ht)]
  simp only [truncBase_eq_baseProfile]
  rw [lintegral_comp_diamondNorm (g := fun t : ℝ => ENNReal.ofReal (baseProfile α R t))
      (ENNReal.measurable_ofReal.comp (measurable_baseProfile α R)),
    ← Ioc_union_Ioi_eq_Ioi hR.le, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same,
    hhead, htail, add_zero]

/-- The truncated base is integrable, its mass being finite by the radial formula. -/
theorem integrable_truncBase {α R : ℝ} (hα : 0 < α) (hα' : α < 2) (hR : 0 < R) :
    Integrable (truncBase α R) := by
  refine ⟨(measurable_truncBase α R).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (.of_forall fun z => truncBase_nonneg α R z),
    lintegral_truncBase hα hα' hR]
  exact ENNReal.ofReal_lt_top

/-- **The mass of the truncated diamond base**: `∫ (r^{-α} − R^{-α})₊ = (4/(2−α) − 2) R^{2−α}`,
the radial formula turning it into `∫_0^R 4 t (t^{-α} − R^{-α}) dt`. -/
theorem integral_truncBase {α R : ℝ} (hα : 0 < α) (hα' : α < 2) (hR : 0 < R) :
    ∫ z, truncBase α R z = (4 / (2 - α) - 2) * R ^ (2 - α) := by
  have h2α : (0 : ℝ) < 2 - α := by linarith
  rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun z => truncBase_nonneg α R z)
    (measurable_truncBase α R).aestronglyMeasurable, lintegral_truncBase hα hα' hR,
    ENNReal.toReal_ofReal]
  exact mul_nonneg (by rw [sub_nonneg, le_div_iff₀ h2α]; linarith)
    (Real.rpow_nonneg hR.le _)

/-- **At `α = 6/5` the base has mass `3 R^{4/5}`**, the coefficient `4/(2 − α) − 2` being `3`. -/
theorem integral_truncBase_six_fifths {R : ℝ} (hR : 0 < R) :
    ∫ z, truncBase (6 / 5) R z = 3 * R ^ (4 / 5 : ℝ) := by
  rw [integral_truncBase (by norm_num) (by norm_num) hR,
    show (2 : ℝ) - 6 / 5 = 4 / 5 from by norm_num]
  norm_num

/-! ### The mass of a single tensor spline cell -/

/-- The mass of a shifted, scaled B-spline: `∫ β(c x − d) dx = c⁻¹`, the substitution contributing
the Jacobian `c⁻¹` and the shift nothing. -/
theorem integral_bspline_affine {c : ℝ} (hc : 0 < c) (d : ℝ) :
    ∫ x : ℝ, bspline (c * x - d) = c⁻¹ := by
  have h := Measure.integral_comp_mul_left (fun y : ℝ => bspline (y - d)) c
  rw [integral_sub_right_eq_self bspline d, integral_bspline, smul_eq_mul, mul_one,
    abs_of_pos (inv_pos.2 hc)] at h
  exact h

/-- A shifted, scaled B-spline is integrable, being continuous with support in the compact
interval `[(d − 2)/c, (d + 2)/c]`. -/
theorem integrable_bspline_affine {c : ℝ} (hc : 0 < c) (d : ℝ) :
    Integrable fun x : ℝ => bspline (c * x - d) := by
  refine (continuous_bspline.comp (by fun_prop)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := (d - 2) / c) (b := (d + 2) / c)) fun x hx => ?_)
  rw [mem_Icc]
  by_contra hcon
  rw [not_and_or, not_le, not_le] at hcon
  refine hx ?_
  rcases hcon with h | h
  · exact bspline_of_le_neg_two (by linarith [(lt_div_iff₀ hc).1 h])
  · exact bspline_of_two_le (by linarith [(div_lt_iff₀ hc).1 h])

/-- A single tensor spline cell is integrable: Fubini turns it into a product of two integrable
one-dimensional factors. -/
theorem integrable_splineCell {c : ℝ} (hc : 0 < c) (i j : ℝ) :
    Integrable fun z : Fin 2 → ℝ => bspline (c * z 0 - i) * bspline (c * z 1 - j) := by
  have hfub : Integrable fun p : ℝ × ℝ => bspline (c * p.1 - i) * bspline (c * p.2 - j) := by
    rw [Measure.volume_eq_prod]
    exact (integrable_bspline_affine hc i).mul_prod (integrable_bspline_affine hc j)
  rw [← (volume_preserving_finTwoArrow ℝ).map_eq] at hfub
  exact (integrable_map_equiv _ _).1 hfub

/-- **The mass of one tensor spline cell** is `(c²)⁻¹`. Fubini on `Fin 2 → ℝ` through
`volume_preserving_finTwoArrow` splits the tensor product into two copies of
`integral_bspline_affine`. -/
theorem integral_splineCell {c : ℝ} (hc : 0 < c) (i j : ℝ) :
    ∫ z : Fin 2 → ℝ, bspline (c * z 0 - i) * bspline (c * z 1 - j) = (c ^ 2)⁻¹ := by
  have hfub : ∫ p : ℝ × ℝ, bspline (c * p.1 - i) * bspline (c * p.2 - j)
      = ∫ z : Fin 2 → ℝ, bspline (c * z 0 - i) * bspline (c * z 1 - j) := by
    rw [← (volume_preserving_finTwoArrow ℝ).map_eq, integral_map_equiv]
    rfl
  rw [← hfub, Measure.volume_eq_prod,
    integral_prod_mul (fun x : ℝ => bspline (c * x - i)) (fun y : ℝ => bspline (c * y - j)),
    integral_bspline_affine hc, integral_bspline_affine hc]
  ring

end CenteredMaximal.Fractional

end

end
