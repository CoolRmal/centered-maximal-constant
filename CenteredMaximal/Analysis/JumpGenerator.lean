/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The jump generator on `C²` functions

The coordinate-stable generator of order `α ∈ (0, 2)` on the plane acts on a smooth bounded
function `φ` by
`A φ (x) = (c_α / 2) ∑_j ∫_ℝ (φ(x + t e_j) + φ(x − t e_j) − 2 φ(x)) |t|^{−1−α} dt`,
where `e_j` is the `j`-th coordinate vector. This file defines the second difference
`secondDiff φ j x t = φ(x + t e_j) + φ(x − t e_j) − 2 φ(x)` and the *unnormalised* generator
`jumpGen α φ x = ∑_j ∫ secondDiff φ j x t |t|^{−1−α} dt` (a Bochner integral; the constant
`c_α / 2` is kept out of the definition), and proves its basic properties for `φ` of class `C²`
with `|φ| ≤ M₀` and `‖D²φ‖ ≤ M₂`:

* `abs_secondDiff_le_const`, `abs_secondDiff_le_sq`: `|secondDiff φ j x t| ≤ 4 M₀` and
  `|secondDiff φ j x t| ≤ M₂ t²`, the latter by the fundamental theorem of calculus and the mean
  value inequality along the line `s ↦ φ(x + s e_j)`;
* `jumpBound`: the even dominating function `min(M₂ t², 4 M₀) |t|^{−(1+α)}`, integrable on `ℝ`
  with `∫ jumpBound ≤ 2 (M₂ / (2 − α) + 4 M₀ / α)`;
* `integrable_secondDiff_mul_rpow`, `abs_jumpGen_le`: the integrand is integrable and
  `|jumpGen α φ x| ≤ 2 (2 M₂ / (2 − α) + 8 M₀ / α)`;
* `jumpGen_comp_add_right`, `jumpGen_add`, `jumpGen_smul`, `jumpGen_neg`, `jumpGen_sub`:
  translation invariance and linearity;
* `jumpGen_comp_smul_inv`, `abs_jumpGen_comp_smul_inv_le`: the scaling law
  `jumpGen α (φ (λ⁻¹ ·)) x = λ^{−α} jumpGen α φ (λ⁻¹ x)` for `λ > 0` and its consequence;
* `continuous_jumpGen`: `jumpGen α φ` is continuous, by dominated convergence;
* `exists_bounds_of_hasCompactSupport`: the bounds `M₀`, `M₂` exist for `φ ∈ C²_c`.

Even functions on `ℝ` are handled through `integrable_of_even` and `integral_of_even`, which
reduce integrability and integrals over `ℝ` to the half-line `(0, ∞)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace CenteredMaximal

/-- The symmetric second difference `φ(x + t e_j) + φ(x − t e_j) − 2 φ(x)` of `φ` at `x` in the
`j`-th coordinate direction with step `t`. -/
def secondDiff (φ : (Fin 2 → ℝ) → ℝ) (j : Fin 2) (x : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  φ (x + t • Pi.single j 1) + φ (x - t • Pi.single j 1) - 2 * φ x

/-- The unnormalised coordinate jump generator
`∑_j ∫ (φ(x + t e_j) + φ(x − t e_j) − 2 φ(x)) |t|^{−(1+α)} dt`, a Bochner integral (zero if the
integrand is not integrable, following Mathlib's convention). The normalising constant `c_α / 2`
is not included. -/
def jumpGen (α : ℝ) (φ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  ∑ j : Fin 2, ∫ t : ℝ, secondDiff φ j x t * |t| ^ (-(1 + α))

/-- The even dominating function `min(M₂ t², 4 M₀) |t|^{−(1+α)}` of the integrand of `jumpGen`
for `φ` with `|φ| ≤ M₀` and `‖D²φ‖ ≤ M₂`. -/
def jumpBound (α M₀ M₂ t : ℝ) : ℝ := min (M₂ * t ^ 2) (4 * M₀) * |t| ^ (-(1 + α))

variable {φ ψ : (Fin 2 → ℝ) → ℝ} {α M₀ M₂ : ℝ}

/-! ### Algebra of the second difference -/

/-- The second difference with step `0` vanishes. -/
@[simp]
theorem secondDiff_zero (φ : (Fin 2 → ℝ) → ℝ) (j : Fin 2) (x : Fin 2 → ℝ) :
    secondDiff φ j x 0 = 0 := by
  simp [secondDiff]; ring

/-- The second difference is even in the step. -/
theorem secondDiff_neg (φ : (Fin 2 → ℝ) → ℝ) (j : Fin 2) (x : Fin 2 → ℝ) (t : ℝ) :
    secondDiff φ j x (-t) = secondDiff φ j x t := by
  simp only [secondDiff, neg_smul, ← sub_eq_add_neg, sub_neg_eq_add]
  ring

/-- The second difference is additive in the function. -/
theorem secondDiff_add (φ ψ : (Fin 2 → ℝ) → ℝ) (j : Fin 2) (x : Fin 2 → ℝ) (t : ℝ) :
    secondDiff (φ + ψ) j x t = secondDiff φ j x t + secondDiff ψ j x t := by
  simp only [secondDiff, Pi.add_apply]; ring

/-- The second difference is homogeneous in the function. -/
theorem secondDiff_smul (c : ℝ) (φ : (Fin 2 → ℝ) → ℝ) (j : Fin 2) (x : Fin 2 → ℝ) (t : ℝ) :
    secondDiff (c • φ) j x t = c * secondDiff φ j x t := by
  simp only [secondDiff, Pi.smul_apply, smul_eq_mul]; ring

/-- The second difference of `−φ` is minus the second difference of `φ`. -/
theorem secondDiff_neg_left (φ : (Fin 2 → ℝ) → ℝ) (j : Fin 2) (x : Fin 2 → ℝ) (t : ℝ) :
    secondDiff (-φ) j x t = -secondDiff φ j x t := by
  simp only [secondDiff, Pi.neg_apply]; ring

/-- The second difference of a translate is the second difference at the translated point. -/
theorem secondDiff_comp_add_right (φ : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ) (j : Fin 2)
    (x : Fin 2 → ℝ) (t : ℝ) :
    secondDiff (fun y => φ (y + a)) j x t = secondDiff φ j (x + a) t := by
  simp only [secondDiff, add_right_comm _ _ a, sub_add_eq_add_sub]

/-- The second difference of a dilate `y ↦ φ (c • y)` is the second difference of `φ` at `c • x`
with step `c * t`. -/
theorem secondDiff_comp_smul (φ : (Fin 2 → ℝ) → ℝ) (c : ℝ) (j : Fin 2) (x : Fin 2 → ℝ) (t : ℝ) :
    secondDiff (fun y => φ (c • y)) j x t = secondDiff φ j (c • x) (c * t) := by
  simp only [secondDiff, smul_add, smul_sub, smul_smul]

/-- For continuous `φ`, the second difference is continuous in the step. -/
theorem continuous_secondDiff (hφ : Continuous φ) (j : Fin 2) (x : Fin 2 → ℝ) :
    Continuous (secondDiff φ j x) := by
  unfold secondDiff; fun_prop

/-- For continuous `φ`, the second difference is continuous in the base point. -/
theorem continuous_secondDiff_left (hφ : Continuous φ) (j : Fin 2) (t : ℝ) :
    Continuous fun x => secondDiff φ j x t := by
  unfold secondDiff; fun_prop

/-! ### Pointwise bounds on the second difference -/

/-- If `|φ| ≤ M₀` then `|secondDiff φ j x t| ≤ 4 M₀`. -/
theorem abs_secondDiff_le_const (h₀ : ∀ x, |φ x| ≤ M₀) (j : Fin 2) (x : Fin 2 → ℝ) (t : ℝ) :
    |secondDiff φ j x t| ≤ 4 * M₀ := by
  have h₁ := abs_le.1 (h₀ (x + t • Pi.single j 1))
  have h₂ := abs_le.1 (h₀ (x - t • Pi.single j 1))
  have h₃ := abs_le.1 (h₀ x)
  rw [secondDiff, abs_le]
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2, h₃.1, h₃.2]

/-- If `φ` is `C²` with `‖D²φ‖ ≤ M₂` then `|secondDiff φ j x t| ≤ M₂ t²`.

Along the line `g(s) = φ(x + s e_j)` one has `g'' = D²φ(e_j, e_j)`, so `|g''| ≤ M₂` since
`‖e_j‖ = 1`; the mean value inequality gives `|g'(s) − g'(−s)| ≤ 2 M₂ |s|`, and the fundamental
theorem of calculus `g(t) + g(−t) − 2 g(0) = ∫₀ᵗ (g'(s) − g'(−s)) ds` gives the bound
`2 M₂ ∫₀ᵗ s ds = M₂ t²` for `t ≥ 0`; the case `t < 0` follows by evenness. -/
theorem abs_secondDiff_le_sq (hφ : ContDiff ℝ 2 φ) (h₂ : ∀ x, ‖iteratedFDeriv ℝ 2 φ x‖ ≤ M₂)
    (j : Fin 2) (x : Fin 2 → ℝ) (t : ℝ) : |secondDiff φ j x t| ≤ M₂ * t ^ 2 := by
  set e : Fin 2 → ℝ := Pi.single j 1 with he
  set g : ℝ → ℝ := fun s => φ (x + s • e) with hg_def
  set g' : ℝ → ℝ := fun s => fderiv ℝ φ (x + s • e) e with hg'_def
  -- the affine path `s ↦ x + s • e`
  have hℓ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • e) e s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const e).const_add x
  have hg : ∀ s, HasDerivAt g (g' s) s := fun s =>
    (hφ.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s (hℓ s)
  have hg' : ∀ s, HasDerivAt g' (fderiv ℝ (fderiv ℝ φ) (x + s • e) e e) s := fun s => by
    have h1 : HasDerivAt (fun s => fderiv ℝ φ (x + s • e)) (fderiv ℝ (fderiv ℝ φ) (x + s • e) e)
        s :=
      ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
        _).hasFDerivAt.comp_hasDerivAt s (hℓ s)
    simpa using h1.clm_apply (hasDerivAt_const s e)
  -- the second derivative along the line is bounded by `M₂`, since `‖e‖ = 1`
  have hbound : ∀ s : ℝ, ‖fderiv ℝ (fderiv ℝ φ) (x + s • e) e e‖ ≤ M₂ := fun s => by
    have h := (iteratedFDeriv ℝ 2 φ (x + s • e)).le_opNorm ![e, e]
    rw [iteratedFDeriv_two_apply] at h
    simpa [Fin.prod_univ_two, he, Pi.norm_single] using
      h.trans (mul_le_mul_of_nonneg_right (h₂ _) (by positivity))
  -- mean value inequality for `g'`
  have hmv : ∀ s, ‖g' s - g' (-s)‖ ≤ M₂ * ‖s - -s‖ := fun s =>
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ)
      (fun y _ => (hg' y).hasDerivWithinAt) (fun y _ => hbound y) convex_univ (mem_univ _)
      (mem_univ _)
  have hsd : ∀ s, secondDiff φ j x s = g s + g (-s) - 2 * g 0 := fun s => by
    simp [secondDiff, hg_def, he, neg_smul, sub_eq_add_neg]
  have hh : ∀ s, HasDerivAt (fun s => g s + g (-s) - 2 * g 0) (g' s - g' (-s)) s := fun s => by
    have h2 : HasDerivAt (fun y => g (-y)) (g' (-s) * -1) s := (hg (-s)).comp s (hasDerivAt_neg s)
    exact (((hg s).add h2).sub_const (2 * g 0)).congr_deriv (by ring)
  have hg'c : Continuous g' := continuous_iff_continuousAt.2 fun s => (hg' s).continuousAt
  have hcont : Continuous fun s => g' s - g' (-s) := hg'c.sub (hg'c.comp continuous_neg)
  -- the case `0 ≤ t`, by the fundamental theorem of calculus
  have key : ∀ t, 0 ≤ t → |secondDiff φ j x t| ≤ M₂ * t ^ 2 := fun t ht => by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hh s)
      (hcont.intervalIntegrable 0 t)
    have hle : ‖∫ s in (0:ℝ)..t, (g' s - g' (-s))‖ ≤ ∫ s in (0:ℝ)..t, 2 * M₂ * s := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht (Filter.Eventually.of_forall
        fun s hs => ?_) ((by fun_prop : Continuous fun s : ℝ => 2 * M₂ * s).intervalIntegrable 0 t)
      have := hmv s
      simp only [Real.norm_eq_abs] at this ⊢
      rw [abs_of_pos (by linarith [hs.1] : 0 < s - -s)] at this
      linarith
    rw [hftc, intervalIntegral.integral_const_mul, integral_id, neg_zero] at hle
    rw [hsd, ← Real.norm_eq_abs]
    calc ‖g t + g (-t) - 2 * g 0‖ = ‖g t + g (-t) - 2 * g 0 - (g 0 + g 0 - 2 * g 0)‖ := by
          congr 1; ring
      _ ≤ 2 * M₂ * ((t ^ 2 - 0 ^ 2) / 2) := hle
      _ = M₂ * t ^ 2 := by ring
  rcases le_or_gt 0 t with ht | ht
  · exact key t ht
  · simpa [secondDiff_neg] using key (-t) (by linarith)

/-! ### Even functions on the line -/

/-- An even function integrable on `(0, ∞)` is integrable on `(−∞, 0)`. -/
theorem integrableOn_Iio_of_even {f : ℝ → ℝ} (hf : ∀ t, f (-t) = f t)
    (h : IntegrableOn f (Ioi 0)) : IntegrableOn f (Iio 0) := by
  simpa [hf] using h.comp_neg

/-- An even function integrable on `(0, ∞)` is integrable on `ℝ`. -/
theorem integrable_of_even {f : ℝ → ℝ} (hf : ∀ t, f (-t) = f t) (h : IntegrableOn f (Ioi 0)) :
    Integrable f := by
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union]
  exact ⟨integrableOn_Iio_of_even hf h, (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2 h⟩

/-- The integral over `ℝ` of an even function integrable on `(0, ∞)` is twice its integral over
`(0, ∞)`. -/
theorem integral_of_even {f : ℝ → ℝ} (hf : ∀ t, f (-t) = f t) (h : IntegrableOn f (Ioi 0)) :
    ∫ t, f t = 2 * ∫ t in Ioi 0, f t := by
  have hI := integral_comp_neg_Ioi 0 f
  simp only [hf, neg_zero] at hI
  rw [← integral_add_compl measurableSet_Iio (integrable_of_even hf h), compl_Iio,
    integral_Ici_eq_integral_Ioi, ← integral_Iic_eq_integral_Iio, ← hI]
  ring

/-! ### The dominating function -/

/-- The dominating function is even. -/
theorem jumpBound_neg (α M₀ M₂ t : ℝ) : jumpBound α M₀ M₂ (-t) = jumpBound α M₀ M₂ t := by
  simp [jumpBound]

/-- The dominating function is nonnegative when `M₀` and `M₂` are. -/
theorem jumpBound_nonneg (h₀ : 0 ≤ M₀) (h₂ : 0 ≤ M₂) (α t : ℝ) : 0 ≤ jumpBound α M₀ M₂ t :=
  mul_nonneg (le_min (by positivity) (by positivity)) (Real.rpow_nonneg (abs_nonneg _) _)

/-- The dominating function is measurable. -/
theorem measurable_jumpBound (α M₀ M₂ : ℝ) : Measurable (jumpBound α M₀ M₂) :=
  ((measurable_const.mul (measurable_id.pow_const 2)).min measurable_const).mul
    (continuous_abs.measurable.pow_const _)

/-- The integrand of `jumpGen` is dominated by `jumpBound`. -/
theorem norm_secondDiff_mul_rpow_le_jumpBound (hφ : ContDiff ℝ 2 φ) (h₀ : ∀ x, |φ x| ≤ M₀)
    (h₂ : ∀ x, ‖iteratedFDeriv ℝ 2 φ x‖ ≤ M₂) (α : ℝ) (j : Fin 2) (x : Fin 2 → ℝ) (t : ℝ) :
    ‖secondDiff φ j x t * |t| ^ (-(1 + α))‖ ≤ jumpBound α M₀ M₂ t := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact mul_le_mul_of_nonneg_right
    (le_min (abs_secondDiff_le_sq hφ h₂ j x t) (abs_secondDiff_le_const h₀ j x t))
    (Real.rpow_nonneg (abs_nonneg _) _)

/-- On `(0, 1]` the dominating function is at most `M₂ t^{1−α}`. -/
theorem jumpBound_le_of_mem_Ioc (α : ℝ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    jumpBound α M₀ M₂ t ≤ M₂ * t ^ (1 - α) := by
  rw [jumpBound, abs_of_pos ht.1]
  calc min (M₂ * t ^ 2) (4 * M₀) * t ^ (-(1 + α)) ≤ M₂ * t ^ 2 * t ^ (-(1 + α)) :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg ht.1.le _)
    _ = M₂ * t ^ (1 - α) := by
        rw [mul_assoc, ← Real.rpow_two, ← Real.rpow_add ht.1,
          show (2 : ℝ) + -(1 + α) = 1 - α by ring]

/-- On `(1, ∞)` the dominating function is at most `4 M₀ t^{−(1+α)}`. -/
theorem jumpBound_le_of_mem_Ioi (α : ℝ) {t : ℝ} (ht : t ∈ Ioi (1 : ℝ)) :
    jumpBound α M₀ M₂ t ≤ 4 * M₀ * t ^ (-(1 + α)) := by
  rw [jumpBound, abs_of_pos (zero_lt_one.trans ht)]
  exact mul_le_mul_of_nonneg_right (min_le_right _ _)
    (Real.rpow_nonneg (zero_le_one.trans ht.le) _)

/-- The dominating function is integrable on `(0, 1]` when `α < 2`. -/
theorem integrableOn_jumpBound_Ioc (hα' : α < 2) (h₀ : 0 ≤ M₀) (h₂ : 0 ≤ M₂) :
    IntegrableOn (jumpBound α M₀ M₂) (Ioc 0 1) := by
  have hi : IntegrableOn (fun t : ℝ => M₂ * t ^ (1 - α)) (Ioc 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul M₂
  refine hi.mono' (measurable_jumpBound α M₀ M₂).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (jumpBound_nonneg h₀ h₂ _ _)]
  exact jumpBound_le_of_mem_Ioc α ht

/-- The dominating function is integrable on `(1, ∞)` when `0 < α`. -/
theorem integrableOn_jumpBound_Ioi (hα : 0 < α) (h₀ : 0 ≤ M₀) (h₂ : 0 ≤ M₂) :
    IntegrableOn (jumpBound α M₀ M₂) (Ioi 1) := by
  have hi : IntegrableOn (fun t : ℝ => 4 * M₀ * t ^ (-(1 + α))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  refine hi.mono' (measurable_jumpBound α M₀ M₂).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (jumpBound_nonneg h₀ h₂ _ _)]
  exact jumpBound_le_of_mem_Ioi α ht

/-- The dominating function is integrable on `ℝ` when `0 < α < 2`. -/
theorem integrable_jumpBound (hα : 0 < α) (hα' : α < 2) (h₀ : 0 ≤ M₀) (h₂ : 0 ≤ M₂) :
    Integrable (jumpBound α M₀ M₂) := by
  refine integrable_of_even (jumpBound_neg α M₀ M₂) ?_
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  exact ⟨integrableOn_jumpBound_Ioc hα' h₀ h₂, integrableOn_jumpBound_Ioi hα h₀ h₂⟩

/-- The integral of the dominating function is at most `2 (M₂ / (2 − α) + 4 M₀ / α)`, from
`∫₀¹ t^{1−α} dt = 1 / (2 − α)` and `∫₁^∞ t^{−(1+α)} dt = 1 / α`. -/
theorem integral_jumpBound_le (hα : 0 < α) (hα' : α < 2) (h₀ : 0 ≤ M₀) (h₂ : 0 ≤ M₂) :
    ∫ t, jumpBound α M₀ M₂ t ≤ 2 * (M₂ / (2 - α) + 4 * M₀ / α) := by
  have hIoc := integrableOn_jumpBound_Ioc (α := α) hα' h₀ h₂
  have hIoi := integrableOn_jumpBound_Ioi (α := α) hα h₀ h₂
  rw [integral_of_even (jumpBound_neg α M₀ M₂) (integrable_jumpBound hα hα' h₀ h₂).integrableOn,
    ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hIoc hIoi]
  have hA : ∫ t in Ioc (0 : ℝ) 1, jumpBound α M₀ M₂ t ≤ M₂ / (2 - α) := by
    have hi : IntegrableOn (fun t : ℝ => M₂ * t ^ (1 - α)) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul M₂
    refine (setIntegral_mono_on hIoc hi measurableSet_Ioc fun t ht =>
      jumpBound_le_of_mem_Ioc α ht).trans_eq ?_
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith)), Real.one_rpow, Real.zero_rpow (by linarith),
      show (1 : ℝ) - α + 1 = 2 - α by ring]
    ring
  have hB : ∫ t in Ioi (1 : ℝ), jumpBound α M₀ M₂ t ≤ 4 * M₀ / α := by
    have hi : IntegrableOn (fun t : ℝ => 4 * M₀ * t ^ (-(1 + α))) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
    refine (setIntegral_mono_on hIoi hi measurableSet_Ioi fun t ht =>
      jumpBound_le_of_mem_Ioi α ht).trans_eq ?_
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show -(1 + α) + 1 = -α by ring, neg_div_neg_eq]
    ring
  linarith

/-! ### Integrability and boundedness of the generator -/

/-- For `0 < α < 2` and `φ ∈ C²` with `|φ| ≤ M₀`, `‖D²φ‖ ≤ M₂`, the integrand of `jumpGen` is
integrable. -/
theorem integrable_secondDiff_mul_rpow (hα : 0 < α) (hα' : α < 2) (hφ : ContDiff ℝ 2 φ)
    (h₀ : ∀ x, |φ x| ≤ M₀) (h₂ : ∀ x, ‖iteratedFDeriv ℝ 2 φ x‖ ≤ M₂) (j : Fin 2)
    (x : Fin 2 → ℝ) : Integrable fun t : ℝ => secondDiff φ j x t * |t| ^ (-(1 + α)) :=
  (integrable_jumpBound hα hα' ((abs_nonneg _).trans (h₀ x))
    ((norm_nonneg _).trans (h₂ x))).mono'
    ((continuous_secondDiff hφ.continuous j x).measurable.mul
      (continuous_abs.measurable.pow_const _)).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_secondDiff_mul_rpow_le_jumpBound hφ h₀ h₂ α j x))

/-- For `0 < α < 2` and `φ ∈ C²` with `|φ| ≤ M₀`, `‖D²φ‖ ≤ M₂`, the generator is bounded by
`2 (2 M₂ / (2 − α) + 8 M₀ / α)`. -/
theorem abs_jumpGen_le (hα : 0 < α) (hα' : α < 2) (hφ : ContDiff ℝ 2 φ)
    (h₀ : ∀ x, |φ x| ≤ M₀) (h₂ : ∀ x, ‖iteratedFDeriv ℝ 2 φ x‖ ≤ M₂) (x : Fin 2 → ℝ) :
    |jumpGen α φ x| ≤ 2 * (2 * M₂ / (2 - α) + 8 * M₀ / α) := by
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h₀ x)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (h₂ x)
  rw [← Real.norm_eq_abs]
  calc ‖jumpGen α φ x‖
      ≤ ∑ j : Fin 2, ‖∫ t : ℝ, secondDiff φ j x t * |t| ^ (-(1 + α))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 2, ∫ t, jumpBound α M₀ M₂ t :=
        Finset.sum_le_sum fun j _ => norm_integral_le_of_norm_le
          (integrable_jumpBound hα hα' hM₀ hM₂)
          (Filter.Eventually.of_forall (norm_secondDiff_mul_rpow_le_jumpBound hφ h₀ h₂ α j x))
    _ = 2 * ∫ t, jumpBound α M₀ M₂ t := by simp
    _ ≤ 2 * (2 * (M₂ / (2 - α) + 4 * M₀ / α)) := by
        gcongr; exact integral_jumpBound_le hα hα' hM₀ hM₂
    _ = 2 * (2 * M₂ / (2 - α) + 8 * M₀ / α) := by ring

/-! ### Translation, linearity and scaling -/

/-- The generator commutes with translations. -/
theorem jumpGen_comp_add_right (α : ℝ) (φ : (Fin 2 → ℝ) → ℝ) (a x : Fin 2 → ℝ) :
    jumpGen α (fun y => φ (y + a)) x = jumpGen α φ (x + a) := by
  simp only [jumpGen, secondDiff_comp_add_right]

/-- The generator is additive on functions with integrable integrands. -/
theorem jumpGen_add {x : Fin 2 → ℝ}
    (hφ : ∀ j, Integrable fun t : ℝ => secondDiff φ j x t * |t| ^ (-(1 + α)))
    (hψ : ∀ j, Integrable fun t : ℝ => secondDiff ψ j x t * |t| ^ (-(1 + α))) :
    jumpGen α (φ + ψ) x = jumpGen α φ x + jumpGen α ψ x := by
  simp only [jumpGen, secondDiff_add, add_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => integral_add (hφ j) (hψ j)

/-- The generator is homogeneous. -/
theorem jumpGen_smul (α : ℝ) (c : ℝ) (φ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) :
    jumpGen α (c • φ) x = c * jumpGen α φ x := by
  simp only [jumpGen, secondDiff_smul, mul_assoc, integral_const_mul, Finset.mul_sum]

/-- The generator is odd. -/
theorem jumpGen_neg (α : ℝ) (φ : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) :
    jumpGen α (-φ) x = -jumpGen α φ x := by
  simp only [jumpGen, secondDiff_neg_left, neg_mul, integral_neg, Finset.sum_neg_distrib]

/-- The generator respects differences of functions with integrable integrands. -/
theorem jumpGen_sub {x : Fin 2 → ℝ}
    (hφ : ∀ j, Integrable fun t : ℝ => secondDiff φ j x t * |t| ^ (-(1 + α)))
    (hψ : ∀ j, Integrable fun t : ℝ => secondDiff ψ j x t * |t| ^ (-(1 + α))) :
    jumpGen α (φ - ψ) x = jumpGen α φ x - jumpGen α ψ x := by
  have hneg : ∀ j, Integrable fun t : ℝ => secondDiff (-ψ) j x t * |t| ^ (-(1 + α)) := fun j => by
    simp only [secondDiff_neg_left, neg_mul]
    exact (hψ j).neg
  rw [sub_eq_add_neg, jumpGen_add hφ hneg, jumpGen_neg, ← sub_eq_add_neg]

/-- The scaling law: for `l > 0` and `φ_l (y) = φ (l⁻¹ • y)`,
`jumpGen α φ_l x = l^{−α} jumpGen α φ (l⁻¹ • x)`, by the substitution `t = l s`. -/
theorem jumpGen_comp_smul_inv {l : ℝ} (hl : 0 < l) (α : ℝ) (φ : (Fin 2 → ℝ) → ℝ)
    (x : Fin 2 → ℝ) :
    jumpGen α (fun y => φ (l⁻¹ • y)) x = l ^ (-α) * jumpGen α φ (l⁻¹ • x) := by
  simp only [jumpGen, secondDiff_comp_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hG : ∀ t, secondDiff φ j (l⁻¹ • x) (l⁻¹ * t) * |t| ^ (-(1 + α)) =
      l ^ (-(1 + α)) * (secondDiff φ j (l⁻¹ • x) (l⁻¹ * t) * |l⁻¹ * t| ^ (-(1 + α))) := by
    intro t
    rw [abs_mul, abs_of_pos (inv_pos.2 hl), Real.mul_rpow (inv_nonneg.2 hl.le) (abs_nonneg _),
      Real.inv_rpow hl.le]
    field_simp
  simp_rw [hG]
  have h : ∫ t, secondDiff φ j (l⁻¹ • x) (l⁻¹ * t) * |l⁻¹ * t| ^ (-(1 + α)) =
      |l| • ∫ s, secondDiff φ j (l⁻¹ • x) s * |s| ^ (-(1 + α)) :=
    Measure.integral_comp_inv_mul_left (fun s => secondDiff φ j (l⁻¹ • x) s * |s| ^ (-(1 + α))) l
  rw [integral_const_mul, h, abs_of_pos hl, smul_eq_mul, ← mul_assoc, ← Real.rpow_add_one hl.ne',
    show -(1 + α) + 1 = -α by ring]

/-- The generator of the dilate `φ (l⁻¹ ·)` is bounded by `l^{−α}` times the bound of
`abs_jumpGen_le`. -/
theorem abs_jumpGen_comp_smul_inv_le (hα : 0 < α) (hα' : α < 2) (hφ : ContDiff ℝ 2 φ)
    (h₀ : ∀ x, |φ x| ≤ M₀) (h₂ : ∀ x, ‖iteratedFDeriv ℝ 2 φ x‖ ≤ M₂) {l : ℝ} (hl : 0 < l)
    (x : Fin 2 → ℝ) :
    |jumpGen α (fun y => φ (l⁻¹ • y)) x| ≤ l ^ (-α) * (2 * (2 * M₂ / (2 - α) + 8 * M₀ / α)) := by
  rw [jumpGen_comp_smul_inv hl, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hl _)]
  exact mul_le_mul_of_nonneg_left (abs_jumpGen_le hα hα' hφ h₀ h₂ _) (Real.rpow_pos_of_pos hl _).le

/-! ### Continuity -/

/-- For `0 < α < 2` and `φ ∈ C²` with `|φ| ≤ M₀`, `‖D²φ‖ ≤ M₂`, the generator `jumpGen α φ` is
continuous, by dominated convergence with the dominating function `jumpBound`. -/
theorem continuous_jumpGen (hα : 0 < α) (hα' : α < 2) (hφ : ContDiff ℝ 2 φ)
    (h₀ : ∀ x, |φ x| ≤ M₀) (h₂ : ∀ x, ‖iteratedFDeriv ℝ 2 φ x‖ ≤ M₂) :
    Continuous (jumpGen α φ) := by
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h₀ 0)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (h₂ 0)
  unfold jumpGen
  refine continuous_finsetSum _ fun j _ => ?_
  refine continuous_of_dominated (bound := jumpBound α M₀ M₂)
    (fun x => (integrable_secondDiff_mul_rpow hα hα' hφ h₀ h₂ j x).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall (norm_secondDiff_mul_rpow_le_jumpBound hφ h₀ h₂ α j x))
    (integrable_jumpBound hα hα' hM₀ hM₂) (Filter.Eventually.of_forall fun t => ?_)
  exact (continuous_secondDiff_left hφ.continuous j t).mul continuous_const

/-- A `C²` function with compact support satisfies the hypotheses `|φ| ≤ M₀` and `‖D²φ‖ ≤ M₂`
for some `M₀`, `M₂`. -/
theorem exists_bounds_of_hasCompactSupport (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    ∃ M₀ M₂ : ℝ, (∀ x, |φ x| ≤ M₀) ∧ ∀ x, ‖iteratedFDeriv ℝ 2 φ x‖ ≤ M₂ :=
  let ⟨M₀, h₀⟩ := hφ.continuous.bounded_above_of_compact_support hs
  let ⟨M₂, h₂⟩ := (hφ.continuous_iteratedFDeriv le_rfl).bounded_above_of_compact_support
    (hs.iteratedFDeriv 2)
  ⟨M₀, M₂, h₀, h₂⟩

end CenteredMaximal

end
