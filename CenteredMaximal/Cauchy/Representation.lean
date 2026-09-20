/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Cauchy.Assembly
public import CenteredMaximal.Cauchy.Delta
public import CenteredMaximal.Cauchy.Generator
public import CenteredMaximal.Cauchy.PairingBound

/-!
# The generator of the comparison kernel is a finite measure minus a point mass

This file discharges the hypothesis `hgen` left open by `CenteredMaximal.Cauchy.Assembly` and so
turns the conditional bounds of that file into the unconditional statement
`c₂ ≤ looseCost < 3.879`.

Away from the origin the comparison kernel is an affine function `c₁ G + c₂` of the Cauchy
potential `G` plus the bounded part `g = tail R − ε ψ` (`looseKernel_eq_affine`), with

`c₁ = 2 π R / (R − 1)`,   `c₂ = −1 / (R − 1)`,   `R = looseRadius`,   `ε = looseBump`.

The affine summand contributes only a point mass: it is generator-harmonic off the two coordinate
axes (`jumpGen_affine_potential_eq_zero`), while against a test function the potential pairs as
`∫ G · A ψ = −2 π ψ 0` (`potential_jumpGen`) and the generator of a test function integrates to
zero (`integral_jumpGen_eq_zero`). The bounded summand is genuinely a density: it is Lipschitz and
bounded, so the pairing is self-adjoint on it (`integral_mul_jumpGen_comm`, whose Fubini hypothesis
is `integrable_uncurry_secondDiff_boundedPart`), giving

`∫ K · A ψ = (∫ genDensity · ψ) − pointMass · ψ 0`,   `genDensity = A g`,
`pointMass = 2 π c₁ = 4 π² R / (R − 1)`.

The density is nonnegative because `A K ≥ 0` almost everywhere
(`ae_jumpGen_looseKernel_nonneg`) and `A K = A g` off the axes, and it has finite mass because
testing the representation against the cutoffs `testCutoff l`, whose generators decay like `1 / l`,
bounds `∫ genDensity · testCutoff l` by `pointMass + (∫ K) C` uniformly in `l ≥ 1`.

The smooth exhaustion is rebuilt here rather than imported from
`CenteredMaximal.Analysis.Cutoff`, whose `cutoff` collides with the Lipschitz cutoff of
`CenteredMaximal.Analysis.EnergyDensity`, a transitive import of
`CenteredMaximal.Cauchy.Assembly`.

## Main results

* `testCutoff`, `isTestFunction_testCutoff`, `exists_abs_jumpGen_testCutoff_le`: a smooth
  exhaustion of the plane by test functions whose generators decay like `1 / l`;
* `measurable_genDensity`, `ae_genDensity_nonneg`: the density of the generator is measurable and
  almost everywhere nonnegative;
* `representation`: the pairing identity
  `∫ compKernel · jumpGen 1 ψ = (∫ genDensity · ψ) − pointMass · ψ 0`;
* `integrable_genDensity_mul`: the density is integrable against a test function;
* `exists_massBound`, `lintegral_genDensity_ne_top`: the density has finite mass;
* `genMeasure`, `isFiniteMeasure_genMeasure`, `integral_genMeasure`, `genMeasure_representation`:
  the finite measure `genDensity · volume` and the hypothesis `hgen` in the exact shape required by
  `CenteredMaximal.Cauchy.Assembly`;
* `weakTypeConstant_two_le_cost`, `weakTypeConstant_two_le_ratio`, `weakTypeConstant_two_le`:
  **unconditionally** `c₂ ≤ looseCost = 2787954611/718800000 < 3.879`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace CenteredMaximal.Cauchy

/-! ### A smooth exhaustion of the plane by test functions -/

/-- The one-dimensional smooth bump used to build the cutoffs: it equals `1` on `[-1, 1]` and
vanishes outside `(-2, 2)`. -/
def testBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := one_pos
  rIn_lt_rOut := one_lt_two

/-- The base cutoff on the plane: the product of the one-dimensional bump `testBump` in each
coordinate. It equals `1` on the closed unit ball of the sup norm and vanishes outside the ball of
radius `2`. -/
def testCutoffBase (x : Fin 2 → ℝ) : ℝ := testBump (x 0) * testBump (x 1)

/-- The cutoff at scale `l`: the dilate `x ↦ testCutoffBase (l⁻¹ • x)` of the base cutoff, written
in this shape so that `jumpGen_comp_smul_inv` applies to it verbatim. -/
def testCutoff (l : ℝ) (x : Fin 2 → ℝ) : ℝ := testCutoffBase (l⁻¹ • x)

private theorem norm_eq_max (x : Fin 2 → ℝ) : ‖x‖ = max |x 0| |x 1| := by
  refine le_antisymm ?_ (max_le (by simpa using norm_le_pi_norm x 0)
    (by simpa using norm_le_pi_norm x 1))
  rw [pi_norm_le_iff_of_nonneg (by positivity), Fin.forall_fin_two]
  exact ⟨by simp, by simp⟩

private theorem norm_inv_smul {l : ℝ} (hl : 0 < l) (x : Fin 2 → ℝ) : ‖l⁻¹ • x‖ = l⁻¹ * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl)]

private theorem testCutoffBase_nonneg (x : Fin 2 → ℝ) : 0 ≤ testCutoffBase x :=
  mul_nonneg testBump.nonneg testBump.nonneg

private theorem testCutoffBase_eq_one {x : Fin 2 → ℝ} (hx : ‖x‖ ≤ 1) : testCutoffBase x = 1 := by
  have key : ∀ j : Fin 2, testBump (x j) = 1 := fun j =>
    testBump.one_of_mem_closedBall (by
      have hj : |x j| ≤ ‖x‖ := by simpa using norm_le_pi_norm x j
      simpa [testBump, Real.dist_eq] using hj.trans hx)
  simp [testCutoffBase, key 0, key 1]

private theorem testCutoffBase_eq_zero {x : Fin 2 → ℝ} (hx : 2 ≤ ‖x‖) : testCutoffBase x = 0 := by
  have key : ∀ j : Fin 2, 2 ≤ |x j| → testBump (x j) = 0 := fun j hj =>
    testBump.zero_of_le_dist (by simpa [testBump, Real.dist_eq] using hj)
  rw [norm_eq_max, le_max_iff] at hx
  rcases hx with h | h
  · simp [testCutoffBase, key 0 h]
  · simp [testCutoffBase, key 1 h]

private theorem isTestFunction_testCutoffBase : IsTestFunction testCutoffBase := by
  refine ⟨(testBump.contDiff.comp (contDiff_apply ℝ ℝ 0)).mul
    (testBump.contDiff.comp (contDiff_apply ℝ ℝ 1)), ?_⟩
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 2 → ℝ) 2) fun x hx => ?_
  refine testCutoffBase_eq_zero (le_of_lt ?_)
  simpa [mem_closedBall, dist_zero_right] using hx

/-- The cutoffs are nonnegative. -/
theorem testCutoff_nonneg (l : ℝ) (x : Fin 2 → ℝ) : 0 ≤ testCutoff l x :=
  testCutoffBase_nonneg _

/-- The cutoff at scale `l` equals `1` on the closed ball of radius `l`. -/
theorem testCutoff_eq_one_of_norm_le {l : ℝ} (hl : 0 < l) {x : Fin 2 → ℝ} (hx : ‖x‖ ≤ l) :
    testCutoff l x = 1 := by
  refine testCutoffBase_eq_one ?_
  rw [norm_inv_smul hl]
  calc l⁻¹ * ‖x‖ ≤ l⁻¹ * l := mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hl.le)
    _ = 1 := inv_mul_cancel₀ hl.ne'

private theorem testCutoff_eq_zero_of_le {l : ℝ} (hl : 0 < l) {x : Fin 2 → ℝ} (hx : 2 * l ≤ ‖x‖) :
    testCutoff l x = 0 := by
  refine testCutoffBase_eq_zero ?_
  rw [norm_inv_smul hl]
  calc (2 : ℝ) = l⁻¹ * (2 * l) := by field_simp
    _ ≤ l⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hl.le)

/-- Each cutoff is a test function, supported in the closed ball of radius `2 l`. -/
theorem isTestFunction_testCutoff {l : ℝ} (hl : 0 < l) : IsTestFunction (testCutoff l) := by
  refine ⟨isTestFunction_testCutoffBase.1.comp (contDiff_id.const_smul l⁻¹), ?_⟩
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 2 → ℝ) (2 * l)) fun x hx => ?_
  refine testCutoff_eq_zero_of_le hl (le_of_lt ?_)
  simpa [mem_closedBall, dist_zero_right] using hx

/-- **The uniform decay of the generators of the cutoffs**: there is a constant `C ≥ 0` with
`|jumpGen 1 (testCutoff l) x| ≤ C / l` for every `l > 0` and every `x`.

The scaling law `jumpGen_comp_smul_inv` turns the generator of `testCutoff l` into `l⁻¹` times the
generator of `testCutoffBase` at `l⁻¹ • x`, and `abs_jumpGen_le` bounds the latter uniformly in
terms of bounds for `testCutoffBase` and its second derivative. -/
theorem exists_abs_jumpGen_testCutoff_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℝ, 0 < l → ∀ x, |jumpGen 1 (testCutoff l) x| ≤ C / l := by
  have hC2 : ContDiff ℝ 2 testCutoffBase := isTestFunction_testCutoffBase.1.of_le (by norm_cast)
  obtain ⟨M₀, M₂, h₀, h₂⟩ :=
    exists_bounds_of_hasCompactSupport hC2 isTestFunction_testCutoffBase.2
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h₀ 0)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (h₂ 0)
  refine ⟨2 * (2 * M₂ / (2 - 1) + 8 * M₀ / 1), ?_, fun l hl x => ?_⟩
  · have h21 : (2 : ℝ) - 1 = 1 := by norm_num
    rw [h21, div_one, div_one]
    linarith
  · have h := abs_jumpGen_comp_smul_inv_le (α := 1) one_pos one_lt_two hC2 h₀ h₂ hl x
    rw [Real.rpow_neg_one, ← div_eq_inv_mul] at h
    exact h

/-- If the lower integrals of `ENNReal.ofReal ∘ g` over all the balls `closedBall 0 n`, `n : ℕ`,
are at most `ENNReal.ofReal a`, then so is the lower integral over the whole plane. The indicators
of the balls increase to `1`, so monotone convergence identifies the integral over the plane with
the supremum of the integrals over the balls. -/
theorem lintegral_le_of_ball_le {g : (Fin 2 → ℝ) → ℝ} (hg : Measurable g) {a : ℝ}
    (h : ∀ n : ℕ, (∫⁻ x in closedBall 0 (n : ℝ), ENNReal.ofReal (g x)) ≤ ENNReal.ofReal a) :
    (∫⁻ x, ENNReal.ofReal (g x)) ≤ ENNReal.ofReal a := by
  have hmeas : ∀ n : ℕ, Measurable ((closedBall (0 : Fin 2 → ℝ) (n : ℝ)).indicator
      fun x => ENNReal.ofReal (g x)) := fun n =>
    hg.ennreal_ofReal.indicator measurableSet_closedBall
  have hmono : Monotone fun n : ℕ => (closedBall (0 : Fin 2 → ℝ) (n : ℝ)).indicator
      fun x => ENNReal.ofReal (g x) := fun m n hmn x =>
    indicator_le_indicator_of_subset
      (closedBall_subset_closedBall (by exact_mod_cast hmn)) (fun _ => zero_le) x
  have hsup : ∀ x, ⨆ n : ℕ, (closedBall (0 : Fin 2 → ℝ) (n : ℝ)).indicator
      (fun y => ENNReal.ofReal (g y)) x = ENNReal.ofReal (g x) := fun x => by
    refine le_antisymm (iSup_le fun n =>
      indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le) ?_
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    have hmem : x ∈ closedBall (0 : Fin 2 → ℝ) (N : ℝ) := by
      simpa [mem_closedBall, dist_zero_right] using hN
    exact le_iSup_of_le N
      (le_of_eq (indicator_of_mem hmem fun y => ENNReal.ofReal (g y)).symm)
  calc (∫⁻ x, ENNReal.ofReal (g x))
      = ∫⁻ x, ⨆ n : ℕ, (closedBall (0 : Fin 2 → ℝ) (n : ℝ)).indicator
          (fun y => ENNReal.ofReal (g y)) x := by simp_rw [hsup]
    _ = ⨆ n : ℕ, ∫⁻ x, (closedBall (0 : Fin 2 → ℝ) (n : ℝ)).indicator
          (fun y => ENNReal.ofReal (g y)) x := lintegral_iSup hmeas hmono
    _ ≤ ENNReal.ofReal a := iSup_le fun n => by
        rw [lintegral_indicator measurableSet_closedBall]
        exact h n

/-! ### The density and the point mass -/

/-- The density of the generator of the comparison kernel: the Cauchy generator of the bounded
part of the kernel. -/
def genDensity (z : Fin 2 → ℝ) : ℝ := jumpGen 1 boundedPart z

/-- The mass `2 π c₁ = 4 π² R / (R − 1)` of the point mass of the generator at the origin. -/
def pointMass : ℝ := 4 * Real.pi ^ 2 * looseRadius / (looseRadius - 1)

theorem pointMass_nonneg : 0 ≤ pointMass := by
  have h : (0 : ℝ) < looseRadius - 1 := by linarith [one_lt_looseRadius]
  have hR : (0 : ℝ) < looseRadius := by linarith [one_lt_looseRadius]
  rw [pointMass]
  exact div_nonneg (mul_nonneg (by positivity) hR.le) h.le

/-! ### Coordinates along a line through a point off the axes -/

private theorem diamondNorm_eq_abs_add (z : Fin 2 → ℝ) (j : Fin 2) :
    diamondNorm z = |z j| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem diamondNorm_add_single (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z + s • Pi.single j 1) = |z j + s| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem coord_ne_zero {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2) :
    z j ≠ 0 := by
  fin_cases j
  · simpa using h0
  · simpa using h1

private theorem coord_succ_ne_zero {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2) :
    z (j + 1) ≠ 0 := by
  fin_cases j
  · simpa using h1
  · simpa using h0

/-- A coordinate line through a point off the two axes never meets the origin. -/
private theorem add_single_ne_zero {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2)
    (t : ℝ) : z + t • Pi.single j 1 ≠ 0 := by
  intro h
  have hd : diamondNorm (z + t • Pi.single j 1) = 0 := diamondNorm_eq_zero_iff.2 h
  rw [diamondNorm_add_single] at hd
  have hpos := abs_pos.2 (coord_succ_ne_zero h0 h1 j)
  linarith [abs_nonneg (z j + t)]

private theorem sub_single_ne_zero {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2)
    (t : ℝ) : z - t • Pi.single j 1 ≠ 0 := by
  rw [sub_eq_add_neg, ← neg_smul]
  exact add_single_ne_zero h0 h1 j (-t)

/-- A coordinate hyperplane of the plane is a null set, being a strict subspace. -/
private theorem volume_coord_eq_zero (i : Fin 2) : volume {z : Fin 2 → ℝ | z i = 0} = 0 := by
  have hset : {z : Fin 2 → ℝ | z i = 0}
      = (LinearMap.ker (LinearMap.proj i : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) : Set (Fin 2 → ℝ)) := by
    ext z
    simp [LinearMap.mem_ker]
  rw [hset]
  refine Measure.addHaar_submodule volume _ fun htop => ?_
  have hmem : Pi.single i (1 : ℝ) ∈ LinearMap.ker (LinearMap.proj i : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) := by
    rw [htop]
    exact Submodule.mem_top
  simp [LinearMap.mem_ker] at hmem

private theorem ae_coord_ne_zero (i : Fin 2) : ∀ᵐ z : Fin 2 → ℝ, z i ≠ 0 := by
  rw [ae_iff]
  exact measure_mono_null (fun _ hz => not_not.1 hz) (volume_coord_eq_zero i)

/-! ### Step 1: the density is measurable -/

private theorem measurable_secondDiff_boundedPart (j : Fin 2) :
    Measurable fun p : (Fin 2 → ℝ) × ℝ => secondDiff boundedPart j p.1 p.2 := by
  unfold secondDiff
  exact ((measurable_boundedPart.comp (measurable_fst.add (measurable_snd.smul_const _))).add
    (measurable_boundedPart.comp (measurable_fst.sub (measurable_snd.smul_const _)))).sub
    (measurable_const.mul (measurable_boundedPart.comp measurable_fst))

/-- **The density of the generator is measurable**: the bounded part is continuous, so its second
difference is jointly measurable in the base point and the step, and the Bochner integral in the
step is measurable in the base point. -/
theorem measurable_genDensity : Measurable genDensity := by
  show Measurable fun z : Fin 2 → ℝ =>
    ∑ j : Fin 2, ∫ t : ℝ, secondDiff boundedPart j z t * |t| ^ (-(1 + (1 : ℝ)))
  refine Finset.measurable_sum _ fun j _ => ?_
  have hm : Measurable fun p : (Fin 2 → ℝ) × ℝ =>
      secondDiff boundedPart j p.1 p.2 * |p.2| ^ (-(1 + (1 : ℝ))) :=
    (measurable_secondDiff_boundedPart j).mul
      ((continuous_abs.measurable.pow_const _).comp measurable_snd)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable

/-! ### Step 2: the density is nonnegative -/

private theorem secondDiff_potential_mul (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    secondDiff potential j z t * |t| ^ (-(1 + 1) : ℝ)
      = (2 * Real.pi)⁻¹ * profileDiff |z j| |z (j + 1)| t := by
  have h1 : potential (z + t • Pi.single j 1)
      = (2 * Real.pi)⁻¹ * (|z j + t| + |z (j + 1)|)⁻¹ := by
    rw [potential, diamondNorm_add_single, one_div, mul_inv]
  have h2 : potential (z - t • Pi.single j 1)
      = (2 * Real.pi)⁻¹ * (|z j - t| + |z (j + 1)|)⁻¹ := by
    rw [sub_eq_add_neg, ← neg_smul, potential, diamondNorm_add_single, ← sub_eq_add_neg,
      one_div, mul_inv]
  have h3 : potential z = (2 * Real.pi)⁻¹ * (|z j| + |z (j + 1)|)⁻¹ := by
    rw [potential, diamondNorm_eq_abs_add z j, one_div, mul_inv]
  rw [secondDiff, h1, h2, h3, CenteredMaximal.abs_rpow_neg_two, ← profileDiff_abs_left]
  ring

/-- Off the two axes the jump integrand of an affine function of the potential is integrable. -/
private theorem integrable_secondDiff_affine {c₁ c₂ : ℝ} {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0)
    (h1 : z 1 ≠ 0) (j : Fin 2) :
    Integrable fun t : ℝ =>
      secondDiff (fun w => c₁ * potential w + c₂) j z t * |t| ^ (-(1 + 1) : ℝ) := by
  refine ((integrable_profileDiff (abs_pos.2 (coord_ne_zero h0 h1 j))
    (abs_pos.2 (coord_succ_ne_zero h0 h1 j))).const_mul (c₁ * (2 * Real.pi)⁻¹)).congr
    (Filter.Eventually.of_forall fun t => ?_)
  calc c₁ * (2 * Real.pi)⁻¹ * profileDiff |z j| |z (j + 1)| t
      = c₁ * (secondDiff potential j z t * |t| ^ (-(1 + 1) : ℝ)) := by
        rw [secondDiff_potential_mul]; ring
    _ = secondDiff (fun w => c₁ * potential w + c₂) j z t * |t| ^ (-(1 + 1) : ℝ) := by
        simp only [secondDiff]; ring

/-- **For almost every `z` the jump integrand of the bounded part is integrable in the step.**

This is the slice of the Fubini hypothesis `integrable_uncurry_secondDiff_boundedPart`, taken at
the test function `testCutoff (n + 1)` for every `n : ℕ`; at a point `z` with `‖z‖ ≤ n + 1` that
cutoff equals `1`, so the constant factor it contributes divides out. -/
theorem ae_integrable_secondDiff_boundedPart : ∀ᵐ z : Fin 2 → ℝ, ∀ j : Fin 2,
    Integrable fun t : ℝ => secondDiff boundedPart j z t * |t| ^ (-(1 + (1 : ℝ))) := by
  have key : ∀ᵐ z : Fin 2 → ℝ, ∀ (n : ℕ) (j : Fin 2), Integrable fun t : ℝ =>
      secondDiff boundedPart j z t * testCutoff ((n : ℝ) + 1) z * |t| ^ (-(1 + (1 : ℝ))) := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact (integrable_uncurry_secondDiff_boundedPart
      (isTestFunction_testCutoff (l := (n : ℝ) + 1) (by positivity)) j).prod_left_ae
  filter_upwards [key] with z hz j
  obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
  have hl : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hone : testCutoff ((n : ℝ) + 1) z = 1 :=
    testCutoff_eq_one_of_norm_le hl (by linarith)
  refine (hz n j).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [hone, mul_one]

/-- **The density of the generator is almost everywhere nonnegative.** Off the two coordinate axes
the kernel coincides with its affine form along every coordinate line, the affine summand is
generator-harmonic, and the remaining summand is the bounded part; so the generator of the bounded
part equals that of the kernel, which is nonnegative almost everywhere. -/
theorem ae_genDensity_nonneg : 0 ≤ᵐ[volume] genDensity := by
  filter_upwards [ae_coord_ne_zero 0, ae_coord_ne_zero 1, ae_jumpGen_looseKernel_nonneg,
    ae_integrable_secondDiff_boundedPart] with z h0 h1 hpos hint
  have hzne : z ≠ 0 := fun h => h0 (by rw [h]; simp)
  -- the second differences of the bounded part and of the bounded summand of `looseKernelAff`
  -- agree along every coordinate line through `z`, since no such line meets the origin
  have hsd : ∀ (j : Fin 2) (t : ℝ),
      secondDiff (tail looseRadius - looseBump • bump) j z t = secondDiff boundedPart j z t := by
    intro j t
    simp only [secondDiff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [boundedPart_eq (add_single_ne_zero h0 h1 j t),
      boundedPart_eq (sub_single_ne_zero h0 h1 j t), boundedPart_eq hzne]
  have hTB : ∀ j, Integrable fun t : ℝ =>
      secondDiff (tail looseRadius - looseBump • bump) j z t * |t| ^ (-(1 + (1 : ℝ))) := fun j =>
    (hint j).congr (Filter.Eventually.of_forall fun t => by simp only [hsd j t])
  have hP : ∀ j, Integrable fun t : ℝ =>
      secondDiff (fun w => 2 * Real.pi * looseRadius / (looseRadius - 1) * potential w
        + -(1 / (looseRadius - 1))) j z t * |t| ^ (-(1 + (1 : ℝ))) :=
    fun j => integrable_secondDiff_affine h0 h1 j
  have hsplit : looseKernelAff
      = (fun w => 2 * Real.pi * looseRadius / (looseRadius - 1) * potential w
          + -(1 / (looseRadius - 1))) + (tail looseRadius - looseBump • bump) := by
    funext w
    simp only [looseKernelAff, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hjbp : jumpGen 1 (tail looseRadius - looseBump • bump) z = genDensity z := by
    show jumpGen 1 (tail looseRadius - looseBump • bump) z = jumpGen 1 boundedPart z
    unfold jumpGen
    exact Finset.sum_congr rfl fun j _ =>
      integral_congr_ae (Filter.Eventually.of_forall fun t => by simp only [hsd j t])
  calc (0 : ℝ) ≤ jumpGen 1 looseKernel z := hpos
    _ = jumpGen 1 looseKernelAff z := jumpGen_looseKernel_eq_aff h0 h1
    _ = jumpGen 1 (fun w => 2 * Real.pi * looseRadius / (looseRadius - 1) * potential w
          + -(1 / (looseRadius - 1))) z
        + jumpGen 1 (tail looseRadius - looseBump • bump) z := by
          rw [hsplit]; exact jumpGen_add hP hTB
    _ = genDensity z := by rw [jumpGen_affine_potential_eq_zero h0 h1, zero_add, hjbp]

/-! ### Step 3: the pairing identity -/

/-- Away from the origin the kernel splits into the affine part and the bounded part. -/
private theorem compKernel_mul_eq {z : Fin 2 → ℝ} (hz : z ≠ 0) (A : ℝ) :
    compKernel z * A
      = (2 * Real.pi * looseRadius / (looseRadius - 1) * potential z
          + -(1 / (looseRadius - 1))) * A + boundedPart z * A := by
  rw [compKernel_of_ne hz, looseKernel_eq_affine hz, looseKernelAff, boundedPart_eq hz]
  ring

/-- **The affine part pairs to a point mass at the origin.** -/
private theorem integral_affine_mul_jumpGen {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTestFunction ψ) :
    (∫ z, (2 * Real.pi * looseRadius / (looseRadius - 1) * potential z
        + -(1 / (looseRadius - 1))) * jumpGen 1 ψ z) = -(pointMass * ψ 0) := by
  have hAint : Integrable (jumpGen 1 ψ) :=
    integrable_jumpGen_of_isTestFunction one_pos (by norm_num) hψ
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpot : (∫ z, potential z * jumpGen 1 ψ z) = -(2 * Real.pi) * ψ 0 := by
    have h := potential_jumpGen hψ
    field_simp at h
    linarith
  have hzero : (∫ z, jumpGen 1 ψ z) = 0 := integral_jumpGen_eq_zero one_pos (by norm_num) hψ
  calc (∫ z, (2 * Real.pi * looseRadius / (looseRadius - 1) * potential z
          + -(1 / (looseRadius - 1))) * jumpGen 1 ψ z)
      = ∫ z, (2 * Real.pi * looseRadius / (looseRadius - 1) * (potential z * jumpGen 1 ψ z)
          + -(1 / (looseRadius - 1)) * jumpGen 1 ψ z) :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
    _ = 2 * Real.pi * looseRadius / (looseRadius - 1) * (∫ z, potential z * jumpGen 1 ψ z)
          + -(1 / (looseRadius - 1)) * ∫ z, jumpGen 1 ψ z := by
        rw [integral_add ((integrable_potential_mul_jumpGen hψ).const_mul _)
          (hAint.const_mul _), integral_const_mul, integral_const_mul]
    _ = -(pointMass * ψ 0) := by
        rw [hpot, hzero, pointMass]
        ring

/-- **The representation of the generator of the comparison kernel.** Against a test function the
kernel pairs as the density `genDensity` plus a negative point mass of size `pointMass` at the
origin. -/
theorem representation {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTestFunction ψ) :
    ∫ x, compKernel x * jumpGen 1 ψ x = (∫ x, genDensity x * ψ x) - pointMass * ψ 0 := by
  have hAint : Integrable (jumpGen 1 ψ) :=
    integrable_jumpGen_of_isTestFunction one_pos (by norm_num) hψ
  have hIA : Integrable fun z => (2 * Real.pi * looseRadius / (looseRadius - 1) * potential z
      + -(1 / (looseRadius - 1))) * jumpGen 1 ψ z := by
    refine (((integrable_potential_mul_jumpGen hψ).const_mul
      (2 * Real.pi * looseRadius / (looseRadius - 1))).add
      (hAint.const_mul (-(1 / (looseRadius - 1))))).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply]
    ring
  have hIB : Integrable fun z => boundedPart z * jumpGen 1 ψ z :=
    hAint.bdd_mul measurable_boundedPart.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => (Real.norm_eq_abs _).trans_le (abs_boundedPart_le z))
  have hae : ∀ᵐ z : Fin 2 → ℝ, compKernel z * jumpGen 1 ψ z
      = (2 * Real.pi * looseRadius / (looseRadius - 1) * potential z
          + -(1 / (looseRadius - 1))) * jumpGen 1 ψ z + boundedPart z * jumpGen 1 ψ z := by
    have h0 : volume ({0} : Set (Fin 2 → ℝ)) = 0 := measure_singleton 0
    filter_upwards [compl_mem_ae_iff.2 h0] with z hz
    exact compKernel_mul_eq (by simpa using hz) _
  have hcomm : (∫ z, boundedPart z * jumpGen 1 ψ z) = ∫ x, genDensity x * ψ x :=
    integral_mul_jumpGen_comm one_pos (by norm_num) measurable_boundedPart abs_boundedPart_le hψ
      fun j => integrable_uncurry_secondDiff_boundedPart hψ j
  rw [integral_congr_ae hae, integral_add hIA hIB, integral_affine_mul_jumpGen hψ, hcomm]
  ring

/-! ### Step 4: the density is integrable against a test function -/

/-- **The density is integrable against a test function**, by the Fubini marginal of the hypothesis
`integrable_uncurry_secondDiff_boundedPart`. -/
theorem integrable_genDensity_mul {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTestFunction ψ) :
    Integrable fun z => genDensity z * ψ z := by
  have hz : ∀ (j : Fin 2) (z : Fin 2 → ℝ),
      (∫ t : ℝ, secondDiff boundedPart j z t * ψ z * |t| ^ (-(1 + (1 : ℝ))))
        = (∫ t : ℝ, secondDiff boundedPart j z t * |t| ^ (-(1 + (1 : ℝ)))) * ψ z := by
    intro j z
    calc (∫ t : ℝ, secondDiff boundedPart j z t * ψ z * |t| ^ (-(1 + (1 : ℝ))))
        = ∫ t : ℝ, secondDiff boundedPart j z t * |t| ^ (-(1 + (1 : ℝ))) * ψ z :=
          integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
      _ = _ := integral_mul_const _ _
  have hj : ∀ j : Fin 2, Integrable fun z : Fin 2 → ℝ =>
      (∫ t : ℝ, secondDiff boundedPart j z t * |t| ^ (-(1 + (1 : ℝ)))) * ψ z := fun j =>
    (integrable_uncurry_secondDiff_boundedPart hψ j).integral_prod_right.congr
      (Filter.Eventually.of_forall fun z => hz j z)
  refine (integrable_finsetSum Finset.univ fun j _ => hj j).congr
    (Filter.Eventually.of_forall fun z => ?_)
  show (∑ j : Fin 2, (∫ t : ℝ, secondDiff boundedPart j z t * |t| ^ (-(1 + (1 : ℝ)))) * ψ z)
    = genDensity z * ψ z
  rw [← Finset.sum_mul]
  rfl

/-! ### Step 5: the density has finite mass -/

/-- **The density has finite mass.** Testing the representation against `testCutoff l` and using
`testCutoff l 0 = 1` gives `∫ genDensity · testCutoff l = (∫ K · A (testCutoff l)) + pointMass`,
and the generator of the cutoff is at most `C / l ≤ C` in absolute value, so the pairing is bounded
by `(∫ K) C = 2 looseCost C` uniformly in `l ≥ 1`. -/
theorem exists_massBound :
    ∃ m : ℝ, 0 ≤ m ∧ (∫⁻ z, ENNReal.ofReal (genDensity z)) ≤ ENNReal.ofReal m := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_jumpGen_testCutoff_le
  have hcost : (0 : ℝ) < looseCost := by rw [looseCost_eq]; norm_num
  refine ⟨pointMass + 2 * looseCost * C, by nlinarith [pointMass_nonneg], ?_⟩
  have key : ∀ l : ℝ, 1 ≤ l → (∫⁻ z in closedBall 0 l, ENNReal.ofReal (genDensity z))
      ≤ ENNReal.ofReal (pointMass + 2 * looseCost * C) := by
    intro l hl
    have hl0 : (0 : ℝ) < l := zero_lt_one.trans_le hl
    have hψ : IsTestFunction (testCutoff l) := isTestFunction_testCutoff hl0
    have hAint : Integrable (jumpGen 1 (testCutoff l)) :=
      integrable_jumpGen_of_isTestFunction one_pos (by norm_num) hψ
    have hprod : Integrable fun x => compKernel x * jumpGen 1 (testCutoff l) x :=
      integrable_compKernel.mul_bdd hAint.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => (Real.norm_eq_abs _).trans_le (hC l hl0 x))
    have habs : |∫ x, compKernel x * jumpGen 1 (testCutoff l) x| ≤ 2 * looseCost * C := by
      calc |∫ x, compKernel x * jumpGen 1 (testCutoff l) x|
          ≤ ∫ x, |compKernel x * jumpGen 1 (testCutoff l) x| := abs_integral_le_integral_abs
        _ ≤ ∫ x, compKernel x * (C / l) := by
            refine integral_mono hprod.abs (integrable_compKernel.mul_const _) fun x => ?_
            rw [abs_mul, abs_of_nonneg (compKernel_nonneg x)]
            exact mul_le_mul_of_nonneg_left (hC l hl0 x) (compKernel_nonneg x)
        _ = (∫ x, compKernel x) * (C / l) := integral_mul_const _ _
        _ = 2 * looseCost * (C / l) := by rw [integral_compKernel]
        _ ≤ 2 * looseCost * C :=
            mul_le_mul_of_nonneg_left (div_le_self hC0 hl) (by linarith)
    have hone : testCutoff l 0 = 1 := testCutoff_eq_one_of_norm_le hl0 (by simpa using hl0.le)
    have hrep := representation hψ
    rw [hone, mul_one] at hrep
    have hbound : (∫ z, genDensity z * testCutoff l z) ≤ pointMass + 2 * looseCost * C := by
      have habs' := abs_le.1 habs
      linarith [hrep, habs'.2]
    have hgi : Integrable fun z => genDensity z * testCutoff l z := integrable_genDensity_mul hψ
    have hg0 : 0 ≤ᵐ[volume] fun z => genDensity z * testCutoff l z := by
      filter_upwards [ae_genDensity_nonneg] with z hzz
      exact mul_nonneg hzz (testCutoff_nonneg l z)
    calc (∫⁻ z in closedBall 0 l, ENNReal.ofReal (genDensity z))
        = ∫⁻ z in closedBall 0 l, ENNReal.ofReal (genDensity z * testCutoff l z) := by
          refine setLIntegral_congr_fun measurableSet_closedBall fun z hz => ?_
          rw [testCutoff_eq_one_of_norm_le hl0
            (by simpa [mem_closedBall, dist_zero_right] using hz), mul_one]
      _ ≤ ∫⁻ z, ENNReal.ofReal (genDensity z * testCutoff l z) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (∫ z, genDensity z * testCutoff l z) :=
          (ofReal_integral_eq_lintegral_ofReal hgi hg0).symm
      _ ≤ ENNReal.ofReal (pointMass + 2 * looseCost * C) := ENNReal.ofReal_le_ofReal hbound
  refine lintegral_le_of_ball_le measurable_genDensity fun n => ?_
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact le_trans (lintegral_mono_set (closedBall_subset_closedBall (by linarith)))
    (key ((n : ℝ) + 1) (by linarith))

theorem lintegral_genDensity_ne_top : (∫⁻ z, ENNReal.ofReal (genDensity z)) ≠ ⊤ := by
  obtain ⟨m, -, hm⟩ := exists_massBound
  exact (hm.trans_lt ENNReal.ofReal_lt_top).ne

/-! ### Step 6: the measure, and the unconditional bounds -/

/-- The generating measure of the comparison kernel: the density `genDensity` times Lebesgue
measure on the plane. -/
def genMeasure : Measure (Fin 2 → ℝ) :=
  volume.withDensity fun z => ENNReal.ofReal (genDensity z)

instance isFiniteMeasure_genMeasure : IsFiniteMeasure genMeasure :=
  isFiniteMeasure_withDensity lintegral_genDensity_ne_top

/-- Integration against the generating measure is integration against the density. -/
theorem integral_genMeasure (ψ : (Fin 2 → ℝ) → ℝ) :
    ∫ x, ψ x ∂genMeasure = ∫ x, genDensity x * ψ x := by
  rw [genMeasure, integral_withDensity_eq_integral_toReal_smul
    measurable_genDensity.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [ae_genDensity_nonneg] with z hz
  rw [smul_eq_mul, ENNReal.toReal_ofReal hz]

/-- **The hypothesis `hgen` of `CenteredMaximal.Cauchy.Assembly`**: the generator of the comparison
kernel is the finite measure `genMeasure` minus the point mass `pointMass` at the origin. -/
theorem genMeasure_representation {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTestFunction ψ) :
    ∫ x, compKernel x * jumpGen 1 ψ x = (∫ x, ψ x ∂genMeasure) - pointMass * ψ 0 := by
  rw [integral_genMeasure, representation hψ]

/-- **The weak type bound for the centred maximal operator over cubes in the plane**, now
unconditional: `c₂ ≤ ½ ∫ K = looseCost`. -/
theorem weakTypeConstant_two_le_cost : weakTypeConstant 2 ≤ ENNReal.ofReal looseCost :=
  weakTypeConstant_two_le_looseCost genMeasure pointMass_nonneg
    fun _ hψ => genMeasure_representation hψ

/-- The unconditional weak type bound as an exact rational number. -/
theorem weakTypeConstant_two_le_ratio :
    weakTypeConstant 2 ≤ ENNReal.ofReal (2787954611 / 718800000) :=
  weakTypeConstant_two_le_rat genMeasure pointMass_nonneg
    fun _ hψ => genMeasure_representation hψ

/-- **The unconditional weak type bound in decimal form: `c₂ < 3.879`.** -/
theorem weakTypeConstant_two_le : weakTypeConstant 2 ≤ ENNReal.ofReal (3879 / 1000) :=
  weakTypeConstant_two_le_upper genMeasure pointMass_nonneg
    fun _ hψ => genMeasure_representation hψ

end CenteredMaximal.Cauchy

end

end
