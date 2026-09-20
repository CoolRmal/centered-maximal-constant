/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The one-bump comparison kernel for the Cauchy generator

In diamond coordinates on the plane, with the diamond radius `r(u, v) = |u| + |v|`, the loose
kernel is `K = (R/r − 1)₊ / (R − 1) − ε (1 − r)₊²` with `R = 3797/2000` and `ε = 159411/200000`.
It is even, nonnegative, at least `1` on the unit diamond and supported in the diamond of radius
`R`. Its mass is `∫ K = 2 R²/(R − 1) − ε/3`, so the comparison cost `½ ∫ K = R²/(R − 1) − ε/6`
is `2787954611/718800000 < 3.879`.

The mass comes from the radial formula `lintegral_comp_diamondNorm`: for measurable
`g : ℝ → ℝ≥0∞`, `∫ g(r(z)) dz = ∫₀^∞ 4 t g(t) dt`. It is proved without polar coordinates: Tonelli
on `ℝ × ℝ`, evenness in each variable, the substitution `t = u + v` and Tonelli again on the
triangle `{0 < u < t}`.

At `z = 0` Lean evaluates `R / 0 = 0`, so `looseKernel 0 = -looseBump` although the kernel is
meant to be `+∞` there. The pointwise lemmas therefore assume `z ≠ 0`; the origin is a null set,
so nothing is lost in the integrals (`looseKernel_nonneg_ae`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace CenteredMaximal.Cauchy

/-- The diamond radius `r(u, v) = |u| + |v|`. -/
def diamondNorm (z : Fin 2 → ℝ) : ℝ := |z 0| + |z 1|

/-- The support radius `R = 3797/2000` of the loose kernel. -/
def looseRadius : ℝ := 3797 / 2000

/-- The bump coefficient `ε = 159411/200000`. -/
def looseBump : ℝ := 159411 / 200000

/-- The one-bump comparison kernel for the Cauchy generator, in diamond coordinates:
`(R/r − 1)₊ / (R − 1) − ε (1 − r)₊²`. At `z = 0` this evaluates to `-looseBump` because
`R / 0 = 0` in Lean; the kernel is meant to be `+∞` there. -/
def looseKernel (z : Fin 2 → ℝ) : ℝ :=
  max (looseRadius / diamondNorm z - 1) 0 / (looseRadius - 1) -
    looseBump * max (1 - diamondNorm z) 0 ^ 2

/-- The radial profile `(R/t − 1)₊ / (R − 1)` of the singular part of the loose kernel. -/
def looseCusp (t : ℝ) : ℝ := max (looseRadius / t - 1) 0 / (looseRadius - 1)

/-- The radial profile `(1 − t)₊²` of the bump. -/
def looseHump (t : ℝ) : ℝ := max (1 - t) 0 ^ 2

/-- The comparison cost `½ ∫ K = R²/(R − 1) − ε/6` of the loose kernel. -/
def looseCost : ℝ := looseRadius ^ 2 / (looseRadius - 1) - looseBump / 6

/-! ### The constants -/

/-- The support radius exceeds `1`, so the singular part is positive on the unit diamond. -/
theorem one_lt_looseRadius : 1 < looseRadius := by
  norm_num [looseRadius]

/-- The support radius is positive. -/
theorem looseRadius_pos : 0 < looseRadius := by
  norm_num [looseRadius]

/-- The bump coefficient is positive. -/
theorem looseBump_pos : 0 < looseBump := by
  norm_num [looseBump]

/-- The bump coefficient is below `1`, so the bump never exceeds the singular part. -/
theorem looseBump_lt_one : looseBump < 1 := by
  norm_num [looseBump]

/-- The comparison cost as a rational number. -/
theorem looseCost_eq : looseCost = 2787954611 / 718800000 := by
  norm_num [looseCost, looseRadius, looseBump]

/-- The comparison cost is below `3.879`. -/
theorem looseCost_lt : looseCost < 3879 / 1000 := by
  rw [looseCost_eq]
  norm_num

/-! ### The diamond radius -/

theorem diamondNorm_nonneg (z : Fin 2 → ℝ) : 0 ≤ diamondNorm z :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

/-- The sup norm is at most the diamond radius: `‖z‖ = max |z₀| |z₁| ≤ |z₀| + |z₁|`. -/
theorem norm_le_diamondNorm (z : Fin 2 → ℝ) : ‖z‖ ≤ diamondNorm z := by
  refine (pi_norm_le_iff_of_nonneg (diamondNorm_nonneg z)).2 fun i => ?_
  fin_cases i <;> simp [diamondNorm]

/-- The diamond radius is even. -/
theorem diamondNorm_neg (z : Fin 2 → ℝ) : diamondNorm (-z) = diamondNorm z := by
  simp [diamondNorm]

/-- The diamond radius is absolutely homogeneous. -/
theorem diamondNorm_smul (c : ℝ) (z : Fin 2 → ℝ) : diamondNorm (c • z) = |c| * diamondNorm z := by
  simp [diamondNorm, abs_mul, mul_add]

/-- The diamond radius vanishes only at the origin. -/
theorem diamondNorm_eq_zero_iff {z : Fin 2 → ℝ} : diamondNorm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h₀ := (add_eq_zero_iff_of_nonneg (abs_nonneg _) (abs_nonneg _)).1 h
    ext i
    fin_cases i
    · exact abs_eq_zero.1 h₀.1
    · exact abs_eq_zero.1 h₀.2
  · rintro rfl
    simp [diamondNorm]

theorem diamondNorm_pos {z : Fin 2 → ℝ} (hz : z ≠ 0) : 0 < diamondNorm z :=
  (diamondNorm_nonneg z).lt_of_ne fun h => hz (diamondNorm_eq_zero_iff.1 h.symm)

theorem continuous_diamondNorm : Continuous diamondNorm := by
  unfold diamondNorm
  fun_prop

theorem measurable_diamondNorm : Measurable diamondNorm :=
  continuous_diamondNorm.measurable

/-! ### The radial profiles -/

theorem measurable_looseCusp : Measurable looseCusp := by
  unfold looseCusp
  fun_prop

theorem continuous_looseHump : Continuous looseHump := by
  unfold looseHump
  fun_prop

theorem looseCusp_nonneg (t : ℝ) : 0 ≤ looseCusp t :=
  div_nonneg (le_max_right _ _) (by linarith [one_lt_looseRadius])

theorem looseHump_nonneg (t : ℝ) : 0 ≤ looseHump t :=
  sq_nonneg _

/-- The bump vanishes outside the unit diamond. -/
theorem looseHump_eq_zero {t : ℝ} (ht : 1 ≤ t) : looseHump t = 0 := by
  rw [looseHump, max_eq_right (by linarith), zero_pow two_ne_zero]

/-- The singular part vanishes outside the diamond of radius `R`. -/
theorem looseCusp_eq_zero {t : ℝ} (ht : looseRadius ≤ t) : looseCusp t = 0 := by
  have h : looseRadius / t - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one (looseRadius_pos.trans_le ht)]
    exact ht
  rw [looseCusp, max_eq_right h, zero_div]

/-- On the punctured unit interval the singular part dominates `1 + ε (1 − t)²`: the inequality
`R(1 − t)/((R − 1) t) ≥ (1 − t)²` reduces to `R ≥ (R − 1) t (1 − t)`, and `t (1 − t) ≤ 1/4`. -/
theorem one_add_le_looseCusp {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) :
    1 + looseBump * looseHump t ≤ looseCusp t := by
  have hR : 0 < looseRadius - 1 := by linarith [one_lt_looseRadius]
  have hmax : 0 ≤ looseRadius / t - 1 := by
    rw [sub_nonneg, le_div_iff₀ ht, one_mul]
    linarith [one_lt_looseRadius]
  rw [looseCusp, looseHump, max_eq_left hmax, max_eq_left (by linarith), le_div_iff₀ hR,
    le_sub_iff_add_le, le_div_iff₀ ht]
  have h₀ : t * (1 - t) ≤ 1 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
  have h₁ : 0 ≤ looseRadius - looseBump * (looseRadius - 1) * (t * (1 - t)) := by
    unfold looseRadius looseBump
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 ht₁) h₁]

/-! ### Pointwise properties of the kernel -/

/-- The kernel is the singular profile minus `ε` times the bump profile of the diamond radius. -/
theorem looseKernel_eq (z : Fin 2 → ℝ) :
    looseKernel z = looseCusp (diamondNorm z) - looseBump * looseHump (diamondNorm z) :=
  rfl

/-- The kernel is at least `1` on the punctured unit diamond. -/
theorem one_le_looseKernel {z : Fin 2 → ℝ} (hz : diamondNorm z ≤ 1) (hz₀ : z ≠ 0) :
    1 ≤ looseKernel z := by
  rw [looseKernel_eq, le_sub_iff_add_le]
  exact one_add_le_looseCusp (diamondNorm_pos hz₀) hz

/-- The kernel is nonnegative away from the origin, where Lean evaluates it to `-looseBump`. -/
theorem looseKernel_nonneg {z : Fin 2 → ℝ} (hz : z ≠ 0) : 0 ≤ looseKernel z := by
  rw [looseKernel_eq]
  rcases le_or_gt (diamondNorm z) 1 with h | h
  · linarith [one_add_le_looseCusp (diamondNorm_pos hz) h]
  · rw [looseHump_eq_zero h.le, mul_zero, sub_zero]
    exact looseCusp_nonneg _

/-- The kernel is almost everywhere nonnegative; the origin is a null set. -/
theorem looseKernel_nonneg_ae : 0 ≤ᵐ[volume] looseKernel := by
  show ∀ᵐ z ∂volume, 0 ≤ looseKernel z
  refine ae_iff.2 (measure_mono_null (fun z hz => ?_) (measure_singleton 0))
  exact by_contra fun h => hz (looseKernel_nonneg h)

/-- The kernel is even. -/
theorem looseKernel_neg (z : Fin 2 → ℝ) : looseKernel (-z) = looseKernel z := by
  simp only [looseKernel, diamondNorm_neg]

/-- The kernel is supported in the closed diamond of radius `R`. -/
theorem looseKernel_eq_zero_of_le {z : Fin 2 → ℝ} (h : looseRadius ≤ diamondNorm z) :
    looseKernel z = 0 := by
  rw [looseKernel_eq, looseCusp_eq_zero h, looseHump_eq_zero (one_lt_looseRadius.le.trans h),
    mul_zero, sub_zero]

/-! ### The radial integration formula -/

/-- A function of `|x|` integrates to twice its integral over the positive half-line. -/
private theorem lintegral_comp_abs (h : ℝ → ℝ≥0∞) :
    ∫⁻ x, h |x| = 2 * ∫⁻ x in Ioi 0, h x := by
  rw [← lintegral_add_compl (fun x => h |x|) measurableSet_Ioi, compl_Ioi, two_mul]
  congr 1
  · exact setLIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [abs_of_pos hx]
  · calc ∫⁻ x in Iic 0, h |x| = ∫⁻ x, (Iic 0).indicator (fun x => h |x|) (-x) := by
          rw [lintegral_neg_eq_self ((Iic 0).indicator fun x => h |x|),
            lintegral_indicator measurableSet_Iic]
      _ = ∫⁻ x in Ici 0, h x := by
          rw [← lintegral_indicator measurableSet_Ici]
          refine lintegral_congr fun x => ?_
          by_cases hx : 0 ≤ x
          · simp [hx, abs_of_nonneg hx]
          · simp [hx]
      _ = ∫⁻ x in Ioi 0, h x := (setLIntegral_congr Ioi_ae_eq_Ici).symm

/-- Translating the half-line: `∫₀^∞ g(u + v) dv = ∫ᵤ^∞ g(t) dt`. -/
private theorem lintegral_Ioi_comp_add (g : ℝ → ℝ≥0∞) (u : ℝ) :
    ∫⁻ v in Ioi 0, g (u + v) = ∫⁻ t in Ioi u, g t := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_add_left_eq_self (fun t => (Ioi u).indicator g t) u]
  refine lintegral_congr fun v => ?_
  simp [indicator_apply]

/-- Tonelli on the triangle `{0 < u < t}`: `∫₀^∞ ∫ᵤ^∞ g(t) dt du = ∫₀^∞ t g(t) dt`. -/
private theorem lintegral_Ioi_lintegral_Ioi {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ u in Ioi 0, ∫⁻ t in Ioi u, g t = ∫⁻ t in Ioi 0, ENNReal.ofReal t * g t := by
  have h₁ : EqOn (fun u => ∫⁻ t in Ioi u, g t)
      (fun u => ∫⁻ t in Ioi 0, (Ioi u).indicator g t) (Ioi 0) := fun u hu => by
    simp only
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Ioi_inter_Ioi, sup_eq_left.2 (le_of_lt hu)]
  rw [setLIntegral_congr_fun measurableSet_Ioi h₁]
  refine (lintegral_lintegral_swap ?_).trans (setLIntegral_congr_fun measurableSet_Ioi
    fun t _ => ?_)
  · have : (Function.uncurry fun u t => (Ioi u).indicator g t) =
        {p : ℝ × ℝ | p.1 < p.2}.indicator (g ∘ Prod.snd) := by
      ext p
      simp [indicator_apply, Function.uncurry]
    rw [this]
    exact ((hg.comp measurable_snd).indicator
      (measurableSet_lt measurable_fst measurable_snd)).aemeasurable
  · have : ∀ u, (Ioi u).indicator g t = (Iio t).indicator (fun _ => g t) u := fun u => by
      simp [indicator_apply]
    simp_rw [this]
    rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      setLIntegral_const, inter_comm, Ioi_inter_Iio, Real.volume_Ioo, sub_zero, mul_comm]

/-- The radial formula in diamond coordinates: `∫ g(r(z)) dz = ∫₀^∞ 4 t g(t) dt`, the perimeter of
the diamond of radius `t` being `4t` in the diamond measure. -/
theorem lintegral_comp_diamondNorm {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g (diamondNorm z) = ∫⁻ t in Ioi 0, 4 * ENNReal.ofReal t * g t := by
  calc ∫⁻ z, g (diamondNorm z) = ∫⁻ p : ℝ × ℝ, g (|p.1| + |p.2|) := by
        rw [← (volume_preserving_finTwoArrow ℝ).map_eq, lintegral_map_equiv]
        rfl
    _ = ∫⁻ u, ∫⁻ v, g (|u| + |v|) := lintegral_prod _ (by fun_prop)
    _ = ∫⁻ u, 2 * ∫⁻ v in Ioi 0, g (|u| + v) :=
        lintegral_congr fun u => lintegral_comp_abs fun v => g (|u| + v)
    _ = 2 * ∫⁻ u in Ioi 0, 2 * ∫⁻ v in Ioi 0, g (u + v) :=
        lintegral_comp_abs fun u => 2 * ∫⁻ v in Ioi 0, g (u + v)
    _ = 2 * (2 * ∫⁻ u in Ioi 0, ∫⁻ t in Ioi u, g t) := by
        rw [lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top]
        congr 2
        exact setLIntegral_congr_fun measurableSet_Ioi fun u _ => lintegral_Ioi_comp_add g u
    _ = ∫⁻ t in Ioi 0, 4 * ENNReal.ofReal t * g t := by
        rw [lintegral_Ioi_lintegral_Ioi hg, ← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
          ← lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top]
        refine lintegral_congr fun t => ?_
        ring

/-! ### The mass of the kernel -/

/-- A continuous function that is nonnegative on `(0, ∞)` and vanishes beyond `b ≥ 0` has the same
Lebesgue integral over `(0, ∞)` and interval integral over `(0, b)`. -/
private theorem lintegral_Ioi_ofReal_eq_intervalIntegral {φ : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hφ : Continuous φ) (hφ₀ : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ φ t) (hφb : ∀ t, b ≤ t → φ t = 0) :
    ∫⁻ t in Ioi 0, ENNReal.ofReal (φ t) = ENNReal.ofReal (∫ t in (0 : ℝ)..b, φ t) := by
  rw [intervalIntegral.integral_of_le hb, ofReal_integral_eq_lintegral_ofReal hφ.integrableOn_Ioc
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => hφ₀ t ht.1),
    ← Ioc_union_Ioi_eq_Ioi hb, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same,
    setLIntegral_eq_zero measurableSet_Ioi fun t ht => by simp [hφb t (le_of_lt ht)], add_zero]

/-- `∫₀^R 4 (R − t) / (R − 1) dt = 2 R² / (R − 1)`. -/
private theorem integral_looseCusp_profile :
    ∫ t in (0 : ℝ)..looseRadius, 4 * max (looseRadius - t) 0 / (looseRadius - 1) =
      2 * looseRadius ^ 2 / (looseRadius - 1) := by
  have h : EqOn (fun t => 4 * max (looseRadius - t) 0 / (looseRadius - 1))
      (fun t => 4 / (looseRadius - 1) * (looseRadius - t)) (uIcc 0 looseRadius) := fun t ht => by
    rw [uIcc_of_le looseRadius_pos.le] at ht
    simp only [max_eq_left (sub_nonneg.2 ht.2)]
    ring
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const, integral_id, smul_eq_mul]
  ring

/-- `∫₀^1 4 t (1 − t)² dt = 1/3`. -/
private theorem integral_looseHump_profile :
    ∫ t in (0 : ℝ)..1, 4 * t * max (1 - t) 0 ^ 2 = 1 / 3 := by
  have h : EqOn (fun t : ℝ => 4 * t * max (1 - t) 0 ^ 2)
      (fun t => 4 * (t - 2 * t ^ 2 + t ^ 3)) (uIcc 0 1) := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    simp only [max_eq_left (sub_nonneg.2 ht.2)]
    ring
  rw [intervalIntegral.integral_congr h, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_id]
  norm_num

/-- The singular part has mass `2 R² / (R − 1)`: by the radial formula, `∫₀^R 4 (R − t)/(R − 1)`. -/
theorem lintegral_looseCusp :
    ∫⁻ z, ENNReal.ofReal (looseCusp (diamondNorm z)) =
      ENNReal.ofReal (2 * looseRadius ^ 2 / (looseRadius - 1)) := by
  rw [lintegral_comp_diamondNorm (g := fun t => ENNReal.ofReal (looseCusp t))
      (ENNReal.measurable_ofReal.comp measurable_looseCusp),
    ← integral_looseCusp_profile, ← lintegral_Ioi_ofReal_eq_intervalIntegral looseRadius_pos.le
      (by fun_prop)
      (fun t _ => by
        exact div_nonneg (mul_nonneg (by norm_num) (le_max_right _ _))
          (by linarith [one_lt_looseRadius]))
      (fun t ht => by rw [max_eq_right (by linarith), mul_zero, zero_div])]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : (0 : ℝ) < t := ht
  have key : t * looseCusp t = max (looseRadius - t) 0 / (looseRadius - 1) := by
    rw [looseCusp, ← mul_div_assoc, mul_max_of_nonneg _ _ ht.le, mul_zero, mul_sub, mul_one,
      mul_div_cancel₀ _ ht.ne']
  rw [mul_div_assoc, ← key, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul ht.le]
  simp [mul_assoc]

/-- The bump has mass `1/3`: by the radial formula, `∫₀^1 4 t (1 − t)² dt`. -/
theorem lintegral_looseHump :
    ∫⁻ z, ENNReal.ofReal (looseHump (diamondNorm z)) = ENNReal.ofReal (1 / 3) := by
  rw [lintegral_comp_diamondNorm (g := fun t => ENNReal.ofReal (looseHump t))
      (ENNReal.measurable_ofReal.comp continuous_looseHump.measurable),
    ← integral_looseHump_profile, ← lintegral_Ioi_ofReal_eq_intervalIntegral zero_le_one
      (by fun_prop)
      (fun t ht => by
        have ht : (0 : ℝ) < t := ht
        positivity)
      (fun t ht => by rw [max_eq_right (by linarith), zero_pow two_ne_zero, mul_zero])]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht : (0 : ℝ) < t := ht
  rw [looseHump, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
  simp

theorem integrable_looseCusp : Integrable fun z => looseCusp (diamondNorm z) := by
  refine ⟨(measurable_looseCusp.comp measurable_diamondNorm).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => looseCusp_nonneg _),
    lintegral_looseCusp]
  exact ENNReal.ofReal_lt_top

theorem integrable_looseHump : Integrable fun z => looseHump (diamondNorm z) := by
  refine ⟨(continuous_looseHump.comp continuous_diamondNorm).measurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => looseHump_nonneg _),
    lintegral_looseHump]
  exact ENNReal.ofReal_lt_top

theorem integral_looseCusp :
    ∫ z, looseCusp (diamondNorm z) = 2 * looseRadius ^ 2 / (looseRadius - 1) := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => looseCusp_nonneg _)
    integrable_looseCusp.1, lintegral_looseCusp, ENNReal.toReal_ofReal]
  exact div_nonneg (by positivity) (by linarith [one_lt_looseRadius])

theorem integral_looseHump : ∫ z, looseHump (diamondNorm z) = 1 / 3 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => looseHump_nonneg _)
    integrable_looseHump.1, lintegral_looseHump, ENNReal.toReal_ofReal (by norm_num)]

/-- The loose kernel is integrable: the singular part has finite mass by the radial formula, and
the bump is bounded with compact support. -/
theorem integrable_looseKernel : Integrable looseKernel :=
  integrable_looseCusp.sub (integrable_looseHump.const_mul looseBump)

/-- The mass of the loose kernel is `2 R² / (R − 1) − ε / 3`, twice the comparison cost. -/
theorem integral_looseKernel :
    ∫ z, looseKernel z = 2 * (looseRadius ^ 2 / (looseRadius - 1) - looseBump / 6) := by
  have h : looseKernel =
      fun z => looseCusp (diamondNorm z) - looseBump * looseHump (diamondNorm z) := rfl
  rw [h, integral_sub integrable_looseCusp (integrable_looseHump.const_mul _), integral_const_mul,
    integral_looseCusp, integral_looseHump]
  ring

/-- The comparison cost is half the mass of the loose kernel. -/
theorem integral_looseKernel_eq_two_mul_looseCost : ∫ z, looseKernel z = 2 * looseCost :=
  integral_looseKernel

end CenteredMaximal.Cauchy
