/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.BoundedFunctional
public import CenteredMaximal.Analysis.JumpGenerator
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Transferring the obstacle equation through a convolution

Let `K : ℝ² → ℝ` be an even integrable kernel with compact support, let `β` be a finite measure
on the plane and let `a ∈ ℝ`. Suppose that, in the weak sense against test functions,
`A u = σ − f` for the jump generator `A = jumpGen α` and that `A K = β − a δ₀`. Then the
convolution `K ⋆ f` is determined by `K ⋆ σ`, `β ⋆ u` and `u`:
`K ⋆ f = K ⋆ σ − β ⋆ u + a u` almost everywhere.

This file is purely interface driven: the obstacle equation and the generator identity for the
kernel are taken as hypotheses, and nothing here depends on how they are established.

* `isTestFunction_convolution`: `K ⋆ φ` is a test function when `K` is integrable with compact
  support and `φ` is a test function (smoothness from `HasCompactSupport.contDiff_convolution_right`
  and compact support from `HasCompactSupport.convolution`, through the bridging lemma
  `convolution_eq` to Mathlib's `MeasureTheory.convolution`);
* `secondDiff_convolution`, `jumpGen_convolution`: the generator commutes with convolution,
  `A (K ⋆ φ) = K ⋆ (A φ)`. The second difference commutes by linearity of the integral, and the
  interchange of the `t` and `y` integrals is justified by the dominating function
  `|K y| · jumpBound α M₀ M₂ t`, a product of integrable functions;
* `integral_mul_convolution_comm`, `integral_mul_integral_comp_add`: convolution against an even
  kernel, respectively against a finite measure, is self-adjoint for the pairing with a test
  function;
* `convolution_source_eq`: the transfer identity, obtained by testing the obstacle equation
  against `K ⋆ φ`;
* `convolution_le_of_eq_zero`: at almost every point where `u` vanishes, `K ⋆ f ≤ κ ∫ K`, since
  `K ⋆ σ ≤ κ ∫ K` for `0 ≤ σ ≤ κ` and `β ⋆ u ≥ 0`. Two locally integrable functions with the
  same integral against every test function agree almost everywhere
  (`MeasureTheory.ae_eq_of_integral_contDiff_smul_eq`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Convolution ENNReal

namespace CenteredMaximal

/-! ### Test functions: `C²` smoothness and translation -/

namespace IsTestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : E → ℝ}

/-- A test function is of class `C²`. -/
theorem contDiff_two (hφ : IsTestFunction φ) : ContDiff ℝ 2 φ :=
  hφ.1.of_le (by exact_mod_cast ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- Translates of a test function are test functions: the support of `z ↦ φ (z + y)` is the
translate by `−y` of the support of `φ`. -/
theorem comp_add_right (hφ : IsTestFunction φ) (y : E) : IsTestFunction fun z => φ (z + y) := by
  refine ⟨hφ.1.comp (contDiff_id.add contDiff_const), ?_⟩
  refine HasCompactSupport.of_support_subset_isCompact
    (K := (fun w => w - y) '' tsupport φ)
    (hφ.2.isCompact.image (continuous_id.sub continuous_const)) fun z hz => ?_
  exact ⟨z + y, subset_closure hz, by simp⟩

end IsTestFunction

variable {K u σ f g φ : (Fin 2 → ℝ) → ℝ} {α a κ M₀ M₂ : ℝ}

/-! ### Convolution against an integrable kernel -/

/-- Mathlib's convolution with respect to scalar multiplication and Lebesgue measure is the
kernel convolution `x ↦ ∫ K(y) φ(x − y) dy`. -/
theorem convolution_eq (K φ : (Fin 2 → ℝ) → ℝ) :
    (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) = fun x => ∫ y, K y * φ (x - y) := by
  ext x
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-- If `K` is integrable and `g` is continuous and bounded by `C`, then `y ↦ K y · g (x − y)` is
integrable. -/
theorem integrable_kernel_mul_comp_sub (hKint : Integrable K) (hg : Continuous g) {C : ℝ}
    (hgb : ∀ z, |g z| ≤ C) (x : Fin 2 → ℝ) : Integrable fun y => K y * g (x - y) :=
  hKint.mul_bdd ((hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => hgb (x - y))

/-- **Convolution with a test function is a test function.** If `K` is integrable with compact
support and `φ` is a test function, then so is `x ↦ ∫ K(y) φ(x − y) dy`. -/
theorem isTestFunction_convolution (hKint : Integrable K) (hKsupp : HasCompactSupport K)
    (hφ : IsTestFunction φ) : IsTestFunction fun x => ∫ y, K y * φ (x - y) := by
  have h : IsTestFunction (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) :=
    ⟨hφ.2.contDiff_convolution_right _ hKint.locallyIntegrable hφ.1, hKsupp.convolution _ hφ.2⟩
  rwa [convolution_eq] at h

/-- The integrand of a convolution of two integrable functions is integrable on the product. -/
theorem integrable_prod_kernel_mul (hKint : Integrable K) (hgint : Integrable g) :
    Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => K p.2 * g (p.1 - p.2))
      (volume.prod volume) := by
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    hKint.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hgint

/-- The convolution of two integrable functions is integrable. -/
theorem integrable_kernel_conv (hKint : Integrable K) (hgint : Integrable g) :
    Integrable fun x => ∫ y, K y * g (x - y) :=
  (integrable_prod_kernel_mul hKint hgint).integral_prod_left

/-! ### The generator commutes with convolution -/

/-- The second difference of a convolution is the convolution of the second differences. -/
theorem secondDiff_convolution (hKint : Integrable K) (hφ : IsTestFunction φ) (j : Fin 2)
    (x : Fin 2 → ℝ) (t : ℝ) :
    secondDiff (fun z => ∫ y, K y * φ (z - y)) j x t = ∫ y, K y * secondDiff φ j (x - y) t := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφ.2
  have hi : ∀ z : Fin 2 → ℝ, Integrable fun y => K y * φ (z - y) := fun z =>
    integrable_kernel_mul_comp_sub hKint hφ.continuous hC z
  have hA : Integrable fun y : Fin 2 → ℝ => K y * φ (x + t • Pi.single j 1 - y) :=
    hi (x + t • Pi.single j 1)
  have hB : Integrable fun y : Fin 2 → ℝ => K y * φ (x - t • Pi.single j 1 - y) :=
    hi (x - t • Pi.single j 1)
  have hE : Integrable fun y : Fin 2 → ℝ => 2 * (K y * φ (x - y)) := (hi x).const_mul 2
  have key : ∀ y : Fin 2 → ℝ, K y * secondDiff φ j (x - y) t
      = K y * φ (x + t • Pi.single j 1 - y) + K y * φ (x - t • Pi.single j 1 - y)
        - 2 * (K y * φ (x - y)) := fun y => by
    rw [secondDiff, show x - y + t • Pi.single j 1 = x + t • Pi.single j 1 - y from by abel,
      show x - y - t • Pi.single j 1 = x - t • Pi.single j 1 - y from by abel]
    ring
  calc secondDiff (fun z => ∫ y, K y * φ (z - y)) j x t
      = ((∫ y, K y * φ (x + t • Pi.single j 1 - y))
          + ∫ y, K y * φ (x - t • Pi.single j 1 - y)) - ∫ y, 2 * (K y * φ (x - y)) := by
        simp only [secondDiff, integral_const_mul]
    _ = ∫ y, (K y * φ (x + t • Pi.single j 1 - y) + K y * φ (x - t • Pi.single j 1 - y)
          - 2 * (K y * φ (x - y))) := by
        rw [integral_sub (hA.fun_add hB) hE, integral_add hA hB]
    _ = ∫ y, K y * secondDiff φ j (x - y) t :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => (key y).symm)

/-- The `j`-th summand of the generator is continuous, by dominated convergence with the
dominating function `jumpBound`. -/
theorem continuous_integral_secondDiff_mul_rpow (hα : 0 < α) (hα' : α < 2) (hφ : ContDiff ℝ 2 φ)
    (h₀ : ∀ x, |φ x| ≤ M₀) (h₂ : ∀ x, ‖iteratedFDeriv ℝ 2 φ x‖ ≤ M₂) (j : Fin 2) :
    Continuous fun x => ∫ t : ℝ, secondDiff φ j x t * |t| ^ (-(1 + α)) :=
  continuous_of_dominated (bound := jumpBound α M₀ M₂)
    (fun x => (integrable_secondDiff_mul_rpow hα hα' hφ h₀ h₂ j x).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall (norm_secondDiff_mul_rpow_le_jumpBound hφ h₀ h₂ α j x))
    (integrable_jumpBound hα hα' ((abs_nonneg _).trans (h₀ 0)) ((norm_nonneg _).trans (h₂ 0)))
    (Filter.Eventually.of_forall fun t =>
      (continuous_secondDiff_left hφ.continuous j t).mul continuous_const)

/-- The `j`-th summand of the generator is bounded by the integral of `jumpBound`. -/
theorem abs_integral_secondDiff_mul_rpow_le (hα : 0 < α) (hα' : α < 2) (hφ : ContDiff ℝ 2 φ)
    (h₀ : ∀ x, |φ x| ≤ M₀) (h₂ : ∀ x, ‖iteratedFDeriv ℝ 2 φ x‖ ≤ M₂) (j : Fin 2)
    (x : Fin 2 → ℝ) :
    |∫ t : ℝ, secondDiff φ j x t * |t| ^ (-(1 + α))| ≤ ∫ t, jumpBound α M₀ M₂ t := by
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le
    (integrable_jumpBound hα hα' ((abs_nonneg _).trans (h₀ 0)) ((norm_nonneg _).trans (h₂ 0)))
    (Filter.Eventually.of_forall (norm_secondDiff_mul_rpow_le_jumpBound hφ h₀ h₂ α j x))

/-- **The generator commutes with convolution.** For `0 < α < 2`, an integrable kernel `K` and a
test function `φ`, `A (K ⋆ φ) = K ⋆ (A φ)`.

The second difference commutes with the convolution by `secondDiff_convolution`; the interchange
of the `t` and `y` integrals is justified by the integrable dominating function
`|K y| · jumpBound α M₀ M₂ t`. -/
theorem jumpGen_convolution (hα : 0 < α) (hα' : α < 2) (hKint : Integrable K)
    (hφ : IsTestFunction φ) (x : Fin 2 → ℝ) :
    jumpGen α (fun z => ∫ y, K y * φ (z - y)) x = ∫ y, K y * jumpGen α φ (x - y) := by
  obtain ⟨M₀, M₂, h₀, h₂⟩ := exists_bounds_of_hasCompactSupport hφ.contDiff_two hφ.2
  have hbd := integrable_jumpBound (α := α) hα hα' ((abs_nonneg _).trans (h₀ 0))
    ((norm_nonneg _).trans (h₂ 0))
  have hterm : ∀ j : Fin 2, Integrable fun y : Fin 2 → ℝ =>
      K y * ∫ t : ℝ, secondDiff φ j (x - y) t * |t| ^ (-(1 + α)) := fun j =>
    integrable_kernel_mul_comp_sub hKint
      (continuous_integral_secondDiff_mul_rpow hα hα' hφ.contDiff_two h₀ h₂ j)
      (fun z => abs_integral_secondDiff_mul_rpow_le hα hα' hφ.contDiff_two h₀ h₂ j z) x
  have hswap : ∀ j : Fin 2, Integrable (fun p : ℝ × (Fin 2 → ℝ) =>
      K p.2 * (secondDiff φ j (x - p.2) p.1 * |p.1| ^ (-(1 + α)))) (volume.prod volume) := by
    intro j
    have hcφ : Continuous φ := hφ.continuous
    have hc : Continuous fun p : ℝ × (Fin 2 → ℝ) => secondDiff φ j (x - p.2) p.1 := by
      unfold secondDiff
      fun_prop
    refine (hbd.mul_prod hKint.abs).mono' ((hKint.aestronglyMeasurable.comp_snd).mul
      (hc.aestronglyMeasurable.mul
        (((continuous_abs.measurable.comp measurable_fst).pow_const
          (-(1 + α))).aestronglyMeasurable)))
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (norm_secondDiff_mul_rpow_le_jumpBound hφ.contDiff_two h₀ h₂ α j (x - p.2) p.1)
      (abs_nonneg _)
  have key : ∀ j : Fin 2,
      (∫ t : ℝ, secondDiff (fun z => ∫ y, K y * φ (z - y)) j x t * |t| ^ (-(1 + α)))
        = ∫ y, K y * ∫ t : ℝ, secondDiff φ j (x - y) t * |t| ^ (-(1 + α)) := by
    intro j
    calc (∫ t : ℝ, secondDiff (fun z => ∫ y, K y * φ (z - y)) j x t * |t| ^ (-(1 + α)))
        = ∫ t : ℝ, ∫ y, K y * (secondDiff φ j (x - y) t * |t| ^ (-(1 + α))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          show secondDiff (fun z => ∫ y, K y * φ (z - y)) j x t * |t| ^ (-(1 + α))
            = ∫ y, K y * (secondDiff φ j (x - y) t * |t| ^ (-(1 + α)))
          rw [secondDiff_convolution hKint hφ, ← integral_mul_const]
          exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
      _ = ∫ y, ∫ t : ℝ, K y * (secondDiff φ j (x - y) t * |t| ^ (-(1 + α))) :=
          integral_integral_swap (hswap j)
      _ = ∫ y, K y * ∫ t : ℝ, secondDiff φ j (x - y) t * |t| ^ (-(1 + α)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => integral_const_mul _ _)
  have hsum : (∫ y, K y * jumpGen α φ (x - y))
      = ∑ j : Fin 2, ∫ y, K y * ∫ t : ℝ, secondDiff φ j (x - y) t * |t| ^ (-(1 + α)) := by
    rw [← integral_finsetSum Finset.univ fun j _ => hterm j]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [jumpGen, Finset.mul_sum]
  calc jumpGen α (fun z => ∫ y, K y * φ (z - y)) x
      = ∑ j : Fin 2, ∫ t : ℝ, secondDiff (fun z => ∫ y, K y * φ (z - y)) j x t
          * |t| ^ (-(1 + α)) := rfl
    _ = ∑ j : Fin 2, ∫ y, K y * ∫ t : ℝ, secondDiff φ j (x - y) t * |t| ^ (-(1 + α)) :=
        Finset.sum_congr rfl fun j _ => key j
    _ = ∫ y, K y * jumpGen α φ (x - y) := hsum.symm

/-! ### Self-adjointness of convolution for the pairing with a test function -/

/-- Convolution against an even integrable kernel is self-adjoint for the pairing with a test
function: `∫ g · (K ⋆ φ) = ∫ (K ⋆ g) · φ`. Both sides equal `∫ K(y) (∫ g(x + y) φ(x) dx) dy`,
by Fubini, translation invariance and the substitution `y ↦ −y`. -/
theorem integral_mul_convolution_comm (hKint : Integrable K) (hKeven : ∀ z, K (-z) = K z)
    (hgint : Integrable g) (hφ : IsTestFunction φ) :
    (∫ x, g x * ∫ y, K y * φ (x - y)) = ∫ x, (∫ y, K y * g (x - y)) * φ x := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφ.2
  have hF₁ : Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      g p.1 * (K p.2 * φ (p.1 - p.2))) (volume.prod volume) := by
    refine ((hgint.abs.mul_prod hKint.abs).const_mul C).mono'
      ((hgint.aestronglyMeasurable.comp_fst).mul ((hKint.aestronglyMeasurable.comp_snd).mul
        ((hφ.continuous.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable)))
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |g p.1| * (|K p.2| * |φ (p.1 - p.2)|) ≤ |g p.1| * (|K p.2| * C) := by
          gcongr
          exact hC _
      _ = C * (|g p.1| * |K p.2|) := by ring
  have hF₂ : Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      K p.2 * g (p.1 - p.2) * φ p.1) (volume.prod volume) :=
    (integrable_prod_kernel_mul hKint hgint).mul_bdd
      ((hφ.continuous.comp continuous_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => hC p.1)
  have hstep₁ : (∫ x, g x * ∫ y, K y * φ (x - y)) = ∫ y, K y * ∫ x, g (x + y) * φ x := by
    calc (∫ x, g x * ∫ y, K y * φ (x - y))
        = ∫ x, ∫ y, g x * (K y * φ (x - y)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x =>
            (integral_const_mul (g x) _).symm)
      _ = ∫ y, ∫ x, g x * (K y * φ (x - y)) := integral_integral_swap hF₁
      _ = ∫ y, K y * ∫ x, g x * φ (x - y) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          show (∫ x, g x * (K y * φ (x - y))) = K y * ∫ x, g x * φ (x - y)
          rw [← integral_const_mul]
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = ∫ y, K y * ∫ x, g (x + y) * φ x := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          show K y * (∫ x, g x * φ (x - y)) = K y * ∫ x, g (x + y) * φ x
          have hy : ∀ x : Fin 2 → ℝ, x + y - y = x := fun x => by abel
          congr 1
          calc (∫ x, g x * φ (x - y)) = ∫ x, g (x + y) * φ (x + y - y) :=
                (integral_add_right_eq_self (fun x => g x * φ (x - y)) y).symm
            _ = ∫ x, g (x + y) * φ x := by simp only [hy]
  have hstep₂ : (∫ x, (∫ y, K y * g (x - y)) * φ x) = ∫ y, K y * ∫ x, g (x + y) * φ x := by
    calc (∫ x, (∫ y, K y * g (x - y)) * φ x)
        = ∫ x, ∫ y, K y * g (x - y) * φ x :=
          integral_congr_ae (Filter.Eventually.of_forall fun x =>
            (integral_mul_const (φ x) _).symm)
      _ = ∫ y, ∫ x, K y * g (x - y) * φ x := integral_integral_swap hF₂
      _ = ∫ y, K y * ∫ x, g (x - y) * φ x := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          show (∫ x, K y * g (x - y) * φ x) = K y * ∫ x, g (x - y) * φ x
          rw [← integral_const_mul]
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = ∫ y, K y * ∫ x, g (x + y) * φ x := by
          rw [← integral_neg_eq_self (fun y => K y * ∫ x, g (x + y) * φ x) volume]
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          show K y * (∫ x, g (x - y) * φ x) = K (-y) * ∫ x, g (x + -y) * φ x
          simp only [← sub_eq_add_neg, hKeven]
  rw [hstep₁, hstep₂]

/-! ### Convolution against a finite measure -/

variable {β : Measure (Fin 2 → ℝ)}

/-- For a finite measure `β` and an integrable `u`, the function `(z, x) ↦ u (x − z)` is
integrable on `β ⊗ volume`: by Tonelli and translation invariance its norm has integral
`β(ℝ²) ‖u‖₁`. -/
theorem integrable_comp_sub_prod [IsFiniteMeasure β] (hum : Measurable u)
    (huint : Integrable u) :
    Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => u (p.2 - p.1)) (β.prod volume) := by
  have hm : Measurable fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => u (p.2 - p.1) :=
    hum.comp (measurable_snd.sub measurable_fst)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have hcalc : ∫⁻ p : (Fin 2 → ℝ) × (Fin 2 → ℝ), ‖u (p.2 - p.1)‖ₑ ∂β.prod volume
      = β univ * ∫⁻ x, ‖u x‖ₑ := by
    rw [lintegral_prod _ hm.enorm.aemeasurable]
    simp only [lintegral_sub_right_eq_self fun x => ‖u x‖ₑ]
    rw [lintegral_const, mul_comm]
  rw [hasFiniteIntegral_iff_enorm, hcalc]
  exact ENNReal.mul_lt_top (measure_lt_top β univ) huint.2

/-- The convolution of an integrable function against a finite measure is integrable. -/
theorem integrable_integral_comp_sub [IsFiniteMeasure β] (hum : Measurable u)
    (huint : Integrable u) : Integrable fun x => ∫ z, u (x - z) ∂β := by
  simpa using (integrable_comp_sub_prod (β := β) hum huint).swap.integral_prod_left

/-- The integrand `(x, z) ↦ u x · φ (z + x)` is integrable on `volume ⊗ β`. -/
theorem integrable_prod_mul_comp_add [IsFiniteMeasure β] (huint : Integrable u)
    (hφ : IsTestFunction φ) :
    Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => u p.1 * φ (p.2 + p.1)) (volume.prod β) := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφ.2
  refine (huint.abs.mul_prod (integrable_const C)).mono'
    ((huint.aestronglyMeasurable.comp_fst).mul
      ((hφ.continuous.comp (continuous_snd.add continuous_fst)).aestronglyMeasurable))
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)

/-- The function `x ↦ u x · ∫ φ(z + x) dβ(z)` is integrable. -/
theorem integrable_mul_integral_comp_add [IsFiniteMeasure β] (huint : Integrable u)
    (hφ : IsTestFunction φ) : Integrable fun x => u x * ∫ z, φ (z + x) ∂β :=
  (integrable_prod_mul_comp_add (β := β) huint hφ).integral_prod_left.congr
    (Filter.Eventually.of_forall fun x => integral_const_mul (u x) _)

/-- Convolution against a finite measure is self-adjoint for the pairing with a test function:
`∫ u(x) (∫ φ(z + x) dβ(z)) dx = ∫ (∫ u(x − z) dβ(z)) φ(x) dx`. -/
theorem integral_mul_integral_comp_add [IsFiniteMeasure β] (hum : Measurable u)
    (huint : Integrable u) (hφ : IsTestFunction φ) :
    (∫ x, u x * ∫ z, φ (z + x) ∂β) = ∫ x, (∫ z, u (x - z) ∂β) * φ x := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφ.2
  have hB : Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => u (p.2 - p.1) * φ p.2)
      (β.prod volume) :=
    (integrable_comp_sub_prod hum huint).mul_bdd
      ((hφ.continuous.comp continuous_snd).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun p => hC p.2)
  calc (∫ x, u x * ∫ z, φ (z + x) ∂β)
      = ∫ x, ∫ z, u x * φ (z + x) ∂β :=
        integral_congr_ae (Filter.Eventually.of_forall fun x =>
          (integral_const_mul (u x) _).symm)
    _ = ∫ z, (∫ x, u x * φ (z + x)) ∂β :=
        integral_integral_swap (integrable_prod_mul_comp_add huint hφ)
    _ = ∫ z, (∫ x, u (x - z) * φ x) ∂β := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        have hz : ∀ x : Fin 2 → ℝ, z + (x - z) = x := fun x => by abel
        calc (∫ x, u x * φ (z + x)) = ∫ x, u (x - z) * φ (z + (x - z)) :=
              (integral_sub_right_eq_self (fun x => u x * φ (z + x)) z).symm
          _ = ∫ x, u (x - z) * φ x := by simp only [hz]
    _ = ∫ x, ∫ z, u (x - z) * φ x ∂β := integral_integral_swap hB
    _ = ∫ x, (∫ z, u (x - z) ∂β) * φ x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => integral_mul_const (φ x) _)

/-! ### The transfer identity -/

/-- **The transfer identity.** Assume `A u = σ − f` and `A K = β − a δ₀` weakly, for the jump
generator `A = jumpGen α` with `0 < α < 2` and an even integrable kernel `K` with compact
support. Then for every test function `φ`,
`∫ (K ⋆ f) φ = ∫ (K ⋆ σ) φ − ∫ (β ⋆ u) φ + a ∫ u φ`.

Test the obstacle equation against the test function `K ⋆ φ`. On the left, `A (K ⋆ φ) (x)` equals
`∫ K(y) Aφ(x − y) dy = ∫ K(y) Aφ(y + x) dy` by evenness of `K`, which is `∫ φ(z + x) dβ(z) − a φ(x)`
by the generator identity applied to the translate `z ↦ φ (z + x)`. On the right, convolution
moves onto `σ − f` by self-adjointness. -/
theorem convolution_source_eq [IsFiniteMeasure β] (hα : 0 < α) (hα' : α < 2)
    (hKint : Integrable K) (hKeven : ∀ z, K (-z) = K z) (hKsupp : HasCompactSupport K)
    (hum : Measurable u) (huint : Integrable u) (hσint : Integrable σ) (hfint : Integrable f)
    (hu : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      (∫ x, u x * jumpGen α ψ x) = ∫ x, (σ x - f x) * ψ x)
    (hKgen : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      (∫ x, K x * jumpGen α ψ x) = (∫ x, ψ x ∂β) - a * ψ 0)
    (hφ : IsTestFunction φ) :
    (∫ x, (∫ y, K y * f (x - y)) * φ x)
      = (∫ x, (∫ y, K y * σ (x - y)) * φ x) - (∫ x, (∫ y, u (x - y) ∂β) * φ x)
        + a * ∫ x, u x * φ x := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφ.2
  have hψ : IsTestFunction fun z : Fin 2 → ℝ => ∫ y, K y * φ (z - y) :=
    isTestFunction_convolution hKint hKsupp hφ
  obtain ⟨D, hD⟩ := hψ.continuous.bounded_above_of_compact_support hψ.2
  have hstar : ∀ x : Fin 2 → ℝ,
      (∫ y, K y * jumpGen α φ (y + x)) = (∫ z, φ (z + x) ∂β) - a * φ x := fun x => by
    have h := hKgen (fun z => φ (z + x)) (hφ.comp_add_right x)
    rw [zero_add] at h
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)) h
    rw [jumpGen_comp_add_right α φ x y]
  have hgen : ∀ x : Fin 2 → ℝ, jumpGen α (fun z => ∫ y, K y * φ (z - y)) x
      = (∫ z, φ (z + x) ∂β) - a * φ x := fun x => by
    rw [jumpGen_convolution hα hα' hKint hφ]
    calc (∫ y, K y * jumpGen α φ (x - y))
        = ∫ y, K (-y) * jumpGen α φ (-y + x) :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => by
            dsimp only
            rw [hKeven, show -y + x = x - y from by abel])
      _ = ∫ y, K y * jumpGen α φ (y + x) :=
          integral_neg_eq_self (fun y => K y * jumpGen α φ (y + x)) volume
      _ = (∫ z, φ (z + x) ∂β) - a * φ x := hstar x
  have h1 : (∫ x, u x * jumpGen α (fun z => ∫ y, K y * φ (z - y)) x)
      = ∫ x, (σ x - f x) * ∫ y, K y * φ (x - y) := hu _ hψ
  have hI₁ : Integrable fun x : Fin 2 → ℝ => u x * ∫ z, φ (z + x) ∂β :=
    integrable_mul_integral_comp_add huint hφ
  have hI₂ : Integrable fun x : Fin 2 → ℝ => a * (u x * φ x) :=
    (huint.mul_bdd hφ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)).const_mul a
  have hLHS : (∫ x, u x * jumpGen α (fun z => ∫ y, K y * φ (z - y)) x)
      = (∫ x, (∫ y, u (x - y) ∂β) * φ x) - a * ∫ x, u x * φ x := by
    calc (∫ x, u x * jumpGen α (fun z => ∫ y, K y * φ (z - y)) x)
        = ∫ x, ((u x * ∫ z, φ (z + x) ∂β) - a * (u x * φ x)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by
            dsimp only
            rw [hgen x]
            ring)
      _ = (∫ x, u x * ∫ z, φ (z + x) ∂β) - ∫ x, a * (u x * φ x) := integral_sub hI₁ hI₂
      _ = (∫ x, (∫ y, u (x - y) ∂β) * φ x) - a * ∫ x, u x * φ x := by
          rw [integral_mul_integral_comp_add hum huint hφ, integral_const_mul]
  have hJ₁ : Integrable fun x : Fin 2 → ℝ => σ x * ∫ y, K y * φ (x - y) :=
    hσint.mul_bdd hψ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hD)
  have hJ₂ : Integrable fun x : Fin 2 → ℝ => f x * ∫ y, K y * φ (x - y) :=
    hfint.mul_bdd hψ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hD)
  have hRHS : (∫ x, (σ x - f x) * ∫ y, K y * φ (x - y))
      = (∫ x, (∫ y, K y * σ (x - y)) * φ x) - ∫ x, (∫ y, K y * f (x - y)) * φ x := by
    calc (∫ x, (σ x - f x) * ∫ y, K y * φ (x - y))
        = ∫ x, ((σ x * ∫ y, K y * φ (x - y)) - f x * ∫ y, K y * φ (x - y)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = (∫ x, σ x * ∫ y, K y * φ (x - y)) - ∫ x, f x * ∫ y, K y * φ (x - y) :=
          integral_sub hJ₁ hJ₂
      _ = (∫ x, (∫ y, K y * σ (x - y)) * φ x) - ∫ x, (∫ y, K y * f (x - y)) * φ x := by
          rw [integral_mul_convolution_comm hKint hKeven hσint hφ,
            integral_mul_convolution_comm hKint hKeven hfint hφ]
  linarith [h1, hLHS, hRHS]

/-- **The pointwise bound.** Under the hypotheses of `convolution_source_eq`, with in addition
`0 ≤ u`, `0 ≤ σ ≤ κ` and `0 ≤ K`, at almost every point where `u` vanishes one has
`K ⋆ f ≤ κ ∫ K`.

The transfer identity says that the locally integrable functions `K ⋆ f` and
`K ⋆ σ − β ⋆ u + a u` have the same integral against every test function, hence agree almost
everywhere. At a point where `u` vanishes the last term drops, `β ⋆ u ≥ 0` because `u ≥ 0`, and
`K ⋆ σ ≤ κ ∫ K` because `0 ≤ σ ≤ κ` and `K ≥ 0`. -/
theorem convolution_le_of_eq_zero [IsFiniteMeasure β] (hα : 0 < α) (hα' : α < 2)
    (hK₀ : ∀ z, 0 ≤ K z) (hKint : Integrable K) (hKeven : ∀ z, K (-z) = K z)
    (hKsupp : HasCompactSupport K) (hum : Measurable u) (huint : Integrable u)
    (hu₀ : ∀ x, 0 ≤ u x) (hσm : Measurable σ) (hσint : Integrable σ) (hσ₀ : ∀ x, 0 ≤ σ x)
    (hσκ : ∀ x, σ x ≤ κ) (hfint : Integrable f)
    (hu : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      (∫ x, u x * jumpGen α ψ x) = ∫ x, (σ x - f x) * ψ x)
    (hKgen : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      (∫ x, K x * jumpGen α ψ x) = (∫ x, ψ x ∂β) - a * ψ 0) :
    ∀ᵐ x : Fin 2 → ℝ, u x = 0 → (∫ y, K y * f (x - y)) ≤ κ * ∫ y, K y := by
  have hae : ∀ᵐ x : Fin 2 → ℝ, (∫ y, K y * f (x - y))
      = (∫ y, K y * σ (x - y)) - (∫ y, u (x - y) ∂β) + a * u x := by
    have hL1 : LocallyIntegrable (fun x : Fin 2 → ℝ => ∫ y, K y * f (x - y)) volume :=
      (integrable_kernel_conv hKint hfint).locallyIntegrable
    have hs : Integrable (fun x : Fin 2 → ℝ =>
        (∫ y, K y * σ (x - y)) - ∫ y, u (x - y) ∂β) volume :=
      (integrable_kernel_conv hKint hσint).sub' (integrable_integral_comp_sub hum huint)
    have hL2 : LocallyIntegrable (fun x : Fin 2 → ℝ =>
        (∫ y, K y * σ (x - y)) - (∫ y, u (x - y) ∂β) + a * u x) volume :=
      (hs.fun_add (huint.const_mul a)).locallyIntegrable
    refine ae_eq_of_integral_contDiff_smul_eq hL1 hL2 fun w hw hwc => ?_
    have hwt : IsTestFunction w := ⟨hw, hwc⟩
    obtain ⟨Cw, hCw⟩ := hwt.continuous.bounded_above_of_compact_support hwt.2
    have h1 : Integrable fun x : Fin 2 → ℝ => (∫ y, K y * σ (x - y)) * w x :=
      (integrable_kernel_conv hKint hσint).mul_bdd hwt.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hCw)
    have h2 : Integrable fun x : Fin 2 → ℝ => (∫ y, u (x - y) ∂β) * w x :=
      (integrable_integral_comp_sub hum huint).mul_bdd hwt.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hCw)
    have h3 : Integrable fun x : Fin 2 → ℝ => a * (u x * w x) :=
      (huint.mul_bdd hwt.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hCw)).const_mul a
    have hR : (∫ x, w x * ((∫ y, K y * σ (x - y)) - (∫ y, u (x - y) ∂β) + a * u x))
        = (∫ x, (∫ y, K y * σ (x - y)) * w x) - (∫ x, (∫ y, u (x - y) ∂β) * w x)
          + a * ∫ x, u x * w x := by
      calc (∫ x, w x * ((∫ y, K y * σ (x - y)) - (∫ y, u (x - y) ∂β) + a * u x))
          = ∫ x, ((∫ y, K y * σ (x - y)) * w x - (∫ y, u (x - y) ∂β) * w x + a * (u x * w x)) :=
            integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
        _ = ((∫ x, (∫ y, K y * σ (x - y)) * w x) - ∫ x, (∫ y, u (x - y) ∂β) * w x)
              + ∫ x, a * (u x * w x) := by
            rw [integral_add (h1.sub' h2) h3, integral_sub h1 h2]
        _ = (∫ x, (∫ y, K y * σ (x - y)) * w x) - (∫ x, (∫ y, u (x - y) ∂β) * w x)
              + a * ∫ x, u x * w x := by rw [integral_const_mul]
    simp only [smul_eq_mul]
    rw [hR, integral_congr_ae (Filter.Eventually.of_forall fun x =>
      mul_comm (w x) (∫ y, K y * f (x - y)))]
    exact convolution_source_eq hα hα' hKint hKeven hKsupp hum huint hσint hfint hu hKgen hwt
  filter_upwards [hae] with x hx hux
  have h1 : (∫ y, K y * σ (x - y)) ≤ κ * ∫ y, K y := by
    have hi1 : Integrable fun y : Fin 2 → ℝ => K y * σ (x - y) :=
      hKint.mul_bdd ((hσm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hσ₀ _)]
          exact hσκ _)
    calc (∫ y, K y * σ (x - y)) ≤ ∫ y, K y * κ :=
          integral_mono hi1 (hKint.mul_const κ) fun y =>
            mul_le_mul_of_nonneg_left (hσκ _) (hK₀ y)
      _ = κ * ∫ y, K y := by rw [integral_mul_const]; ring
  have h2 : (0 : ℝ) ≤ ∫ y, u (x - y) ∂β := integral_nonneg fun y => hu₀ _
  rw [hx, hux, mul_zero]
  linarith

end CenteredMaximal

end

end
