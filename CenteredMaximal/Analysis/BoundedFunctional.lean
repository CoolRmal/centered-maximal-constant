/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.UniformMulAction

/-!
# A bounded positive functional on test functions is a density in `[0, κ]`

Let `μ₀` be an additive Haar measure on a finite-dimensional real normed space `E`, and let
`T : (E → ℝ) → ℝ` be additive, homogeneous and positive on the test functions (smooth functions
with compact support), with `T φ ≤ κ ∫ φ dμ₀` for every nonnegative test function `φ`. Then
there is a measurable `σ : E → ℝ` with `0 ≤ σ ≤ κ` everywhere and `T φ = ∫ σ φ dμ₀` for every
test function `φ` (`IsBoundedPositiveFunctional.exists_density`).

The proof goes through the Riesz–Markov–Kakutani and Radon–Nikodym theorems.

* `IsBoundedPositiveFunctional.abs_map_le`: `|T φ| ≤ T ψ` when `|φ| ≤ ψ`, so on test functions
  supported in a fixed compact set `T` is controlled by the sup norm
  (`exists_forall_abs_map_le_mul`), through a smooth cutoff equal to `1` on the compact set;
* `approx μ₀ f n = bump n ⋆ f`: smooth approximations of a continuous `f` with compact support,
  converging uniformly to `f` with supports in a fixed compact set (`tendstoUniformly_approx`);
* `extend μ₀ T f = lim T (approx μ₀ f n)`, packaged as the positive linear functional
  `IsBoundedPositiveFunctional.extension` on `C_c(E, ℝ)`, which agrees with `T` on test
  functions and is still bounded by `κ ∫ f dμ₀` on nonnegative `f`;
* `IsBoundedPositiveFunctional.rieszMeasure_extension_le`: the Riesz measure `μ` of the extension
  satisfies `μ ≤ κ μ₀`, since `κ μ₀ - μ` is the Riesz measure of the positive functional
  `f ↦ κ ∫ f dμ₀ - Λ f`;
* `exists_density_of_le`: a measure `μ ≤ κ μ₀` has a Radon–Nikodym density with respect to `μ₀`
  with values in `[0, κ]`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Set Function CompactlySupportedContinuousMap
open scoped Topology Convolution ContDiff CompactlySupported Pointwise

namespace CenteredMaximal

variable {E : Type*} [NormedAddCommGroup E]

/-! ### Test functions -/

/-- The topological support of a sum is contained in every closed set containing both
topological supports. -/
theorem tsupport_add_subset_of_subset {K : Set E} (hK : IsClosed K) {φ ψ : E → ℝ}
    (hφ : tsupport φ ⊆ K) (hψ : tsupport ψ ⊆ K) : tsupport (φ + ψ) ⊆ K :=
  closure_minimal ((support_add φ ψ).trans
    (union_subset (subset_closure.trans hφ) (subset_closure.trans hψ))) hK

/-- The topological support of a difference is contained in every closed set containing both
topological supports. -/
theorem tsupport_sub_subset_of_subset {K : Set E} (hK : IsClosed K) {φ ψ : E → ℝ}
    (hφ : tsupport φ ⊆ K) (hψ : tsupport ψ ⊆ K) : tsupport (φ - ψ) ⊆ K :=
  closure_minimal ((support_sub φ ψ).trans
    (union_subset (subset_closure.trans hφ) (subset_closure.trans hψ))) hK

variable [NormedSpace ℝ E]

/-- A test function is a smooth function with compact support. -/
def IsTestFunction (φ : E → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ

namespace IsTestFunction

variable {φ ψ : E → ℝ}

/-- Test functions are continuous. -/
theorem continuous (hφ : IsTestFunction φ) : Continuous φ :=
  hφ.1.continuous

/-- Test functions are closed under addition. -/
theorem add (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ) : IsTestFunction (φ + ψ) :=
  ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩

/-- Test functions are closed under subtraction. -/
theorem sub (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ) : IsTestFunction (φ - ψ) :=
  ⟨hφ.1.sub hψ.1, hφ.2.sub hψ.2⟩

/-- Test functions are closed under scalar multiplication. -/
theorem smul (c : ℝ) (hφ : IsTestFunction φ) : IsTestFunction (c • φ) :=
  ⟨hφ.1.const_smul c, hφ.2.mono (support_const_smul_subset c φ)⟩

end IsTestFunction

variable [FiniteDimensional ℝ E]

/-- A nonnegative test function equal to `1` on a compact set: a bump function centred at the
origin whose inner ball contains the compact set. -/
theorem exists_isTestFunction_eq_one_of_isCompact {K : Set E} (hK : IsCompact K) :
    ∃ χ : E → ℝ, IsTestFunction χ ∧ (∀ x, 0 ≤ χ x) ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : E)
  let χ : ContDiffBump (0 : E) :=
    ⟨max R 0 + 1, max R 0 + 2, by linarith [le_max_right R 0], by linarith⟩
  exact ⟨χ, ⟨χ.contDiff, χ.hasCompactSupport⟩, χ.nonneg', fun x hx ↦ χ.one_of_mem_closedBall
    (closedBall_subset_closedBall (by linarith [le_max_left R 0]) (hR hx))⟩

variable (E) in
/-- The regularising bumps, centred at the origin with outer radius `1 / (n + 1)`. -/
def bump (n : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / (n + 2)
  rOut := 1 / (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith)

variable [MeasurableSpace E]

/-! ### Bounded positive functionals -/

/-- A positive functional on test functions bounded by `κ` times the integral: `T` is additive
and homogeneous on test functions, nonnegative on nonnegative test functions, and satisfies
`T φ ≤ κ ∫ φ dμ` for nonnegative test functions `φ`. -/
structure IsBoundedPositiveFunctional (μ : Measure E) (T : (E → ℝ) → ℝ) (κ : ℝ) : Prop where
  /-- `T` is additive on test functions. -/
  map_add : ∀ φ ψ, IsTestFunction φ → IsTestFunction ψ → T (φ + ψ) = T φ + T ψ
  /-- `T` is homogeneous on test functions. -/
  map_smul : ∀ (c : ℝ) φ, IsTestFunction φ → T (c • φ) = c * T φ
  /-- `T` is nonnegative on nonnegative test functions. -/
  map_nonneg : ∀ φ, IsTestFunction φ → (∀ x, 0 ≤ φ x) → 0 ≤ T φ
  /-- `T` is bounded by `κ` times the integral on nonnegative test functions. -/
  map_le : ∀ φ, IsTestFunction φ → (∀ x, 0 ≤ φ x) → T φ ≤ κ * ∫ x, φ x ∂μ

/-- The smooth approximation `bump n ⋆ f` of a function `f`. -/
def approx (μ : Measure E) (f : E → ℝ) (n : ℕ) : E → ℝ :=
  (bump E n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f

/-- The extension of `T` to a function `f`: the limit of `T (approx μ f n)`. -/
def extend (μ : Measure E) (T : (E → ℝ) → ℝ) (f : E → ℝ) : ℝ :=
  limUnder atTop fun n ↦ T (approx μ f n)

variable {μ : Measure E} {f : E → ℝ} {n : ℕ}

/-- The smooth approximations of a nonnegative function are nonnegative. -/
theorem approx_nonneg (hf : ∀ x, 0 ≤ f x) (x : E) : 0 ≤ approx μ f n x := by
  simp only [approx, convolution_lsmul]
  exact integral_nonneg fun t ↦ smul_nonneg ((bump E n).nonneg_normed t) (hf _)

namespace IsBoundedPositiveFunctional

variable {T : (E → ℝ) → ℝ} {κ : ℝ} (h : IsBoundedPositiveFunctional μ T κ) {φ ψ : E → ℝ}
include h

omit [FiniteDimensional ℝ E] in
/-- `T` is subtractive on test functions. -/
theorem map_sub (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ) : T (φ - ψ) = T φ - T ψ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ ψ, h.map_add φ _ hφ (hψ.smul _), h.map_smul _ ψ hψ,
    neg_one_mul, ← sub_eq_add_neg]

omit [FiniteDimensional ℝ E] in
/-- `|T φ| ≤ T ψ` for test functions `φ`, `ψ` with `|φ| ≤ ψ`, since `ψ ± φ ≥ 0`. -/
theorem abs_map_le (hφ : IsTestFunction φ) (hψ : IsTestFunction ψ) (hle : ∀ x, |φ x| ≤ ψ x) :
    |T φ| ≤ T ψ := by
  have h₁ := h.map_nonneg (ψ + φ) (hψ.add hφ) fun x ↦ by
    show 0 ≤ ψ x + φ x
    linarith [(abs_le.1 (hle x)).1]
  have h₂ := h.map_nonneg (ψ - φ) (hψ.sub hφ) fun x ↦ by
    show 0 ≤ ψ x - φ x
    linarith [(abs_le.1 (hle x)).2]
  rw [h.map_add ψ φ hψ hφ] at h₁
  rw [h.map_sub hψ hφ] at h₂
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- On test functions supported in a fixed compact set `K`, `T` is controlled by the sup norm:
there is `C ≥ 0` with `|T φ| ≤ C ε` whenever `tsupport φ ⊆ K` and `|φ| ≤ ε`. The constant is
`T χ` for a cutoff `χ ≥ 0` equal to `1` on `K`, since then `|φ| ≤ ε χ`. -/
theorem exists_forall_abs_map_le_mul {K : Set E} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ φ ε, IsTestFunction φ → tsupport φ ⊆ K → (∀ x, |φ x| ≤ ε) →
      |T φ| ≤ C * ε := by
  obtain ⟨χ, hχ, hχ₀, hχ₁⟩ := exists_isTestFunction_eq_one_of_isCompact hK
  refine ⟨T χ, h.map_nonneg χ hχ hχ₀, fun φ ε hφ hφK hφε ↦ ?_⟩
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hφε 0)
  calc |T φ| ≤ T (ε • χ) := h.abs_map_le hφ (hχ.smul ε) fun x ↦ ?_
    _ = T χ * ε := by rw [h.map_smul ε χ hχ, mul_comm]
  by_cases hx : x ∈ K
  · rw [Pi.smul_apply, hχ₁ x hx, smul_eq_mul, mul_one]
    exact hφε x
  · rw [image_eq_zero_of_notMem_tsupport fun hx' ↦ hx (hφK hx'), abs_zero]
    exact smul_nonneg hε (hχ₀ x)

/-- If test functions supported in a fixed compact set converge uniformly to `0`, then their
images under `T` converge to `0`. -/
theorem tendsto_map_of_tendstoUniformly_zero {K : Set E} (hK : IsCompact K) {ψ : ℕ → E → ℝ}
    (hψ : ∀ n, IsTestFunction (ψ n)) (hψK : ∀ n, tsupport (ψ n) ⊆ K)
    (hlim : TendstoUniformly ψ 0 atTop) : Tendsto (fun n ↦ T (ψ n)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hTC⟩ := h.exists_forall_abs_map_le_mul hK
  rw [Metric.tendstoUniformly_iff] at hlim
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim (ε / (C + 1)) (by positivity))
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_0_eq_abs]
  calc |T (ψ n)| ≤ C * (ε / (C + 1)) :=
        hTC _ _ (hψ n) (hψK n) fun x ↦ by simpa using (hN n hn x).le
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

end IsBoundedPositiveFunctional

/-! ### Smooth approximation by convolution with bumps -/

variable [BorelSpace E] {μ₀ : Measure E} [μ₀.IsAddHaarMeasure]

/-- The smooth approximations of a continuous function with compact support are test
functions. -/
theorem isTestFunction_approx (hf : Continuous f) (hfc : HasCompactSupport f) :
    IsTestFunction (approx μ₀ f n) :=
  ⟨(bump E n).hasCompactSupport_normed.contDiff_convolution_left _ (bump E n).contDiff_normed
    hf.locallyIntegrable, (bump E n).hasCompactSupport_normed.convolution _ hfc⟩

/-- The smooth approximations are supported in the compact set `closedBall 0 1 + tsupport f`. -/
theorem tsupport_approx_subset (hfc : HasCompactSupport f) :
    tsupport (approx μ₀ f n) ⊆ closedBall (0 : E) 1 + tsupport f := by
  refine closure_minimal ((support_convolution_subset _).trans (add_subset_add ?_ subset_closure))
    ((isCompact_closedBall (0 : E) 1).add hfc).isClosed
  rw [(bump E n).support_normed_eq]
  refine ball_subset_closedBall.trans (closedBall_subset_closedBall ?_)
  show 1 / ((n : ℝ) + 1) ≤ 1
  exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)

/-- The smooth approximations of a continuous function with compact support converge to it
uniformly, by uniform continuity. -/
theorem tendstoUniformly_approx (hf : Continuous f) (hfc : HasCompactSupport f) :
    TendstoUniformly (approx μ₀ f) f atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.1
    (hfc.uniformContinuous_of_continuous hf) (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine eventually_atTop.2 ⟨N, fun n hn x ↦ ?_⟩
  rw [dist_comm]
  refine ((bump E n).dist_normed_convolution_le hf.aestronglyMeasurable fun y hy ↦
    (hfδ ?_).le).trans_lt (half_lt_self hε)
  calc dist y x < 1 / ((n : ℝ) + 1) := mem_ball.1 hy
    _ ≤ 1 / ((N : ℝ) + 1) := by
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    _ < δ := hN

/-- The smooth approximations have the same integral as the function. -/
theorem integral_approx (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∫ x, approx μ₀ f n x ∂μ₀ = ∫ x, f x ∂μ₀ := by
  rw [approx, integral_convolution _ (bump E n).integrable_normed
    (hf.integrable_of_hasCompactSupport hfc), (bump E n).integral_normed,
    ContinuousLinearMap.lsmul_apply, one_smul]

/-! ### The Radon–Nikodym step -/

omit [BorelSpace E] in
/-- A measure `μ ≤ κ μ₀` has a Radon–Nikodym density with respect to `μ₀` with values in
`[0, κ]`, representing every integral against `μ`. -/
theorem exists_density_of_le [SigmaFinite μ] {κ : ℝ} (hκ : 0 ≤ κ)
    (hle : μ ≤ ENNReal.ofReal κ • μ₀) :
    ∃ σ : E → ℝ, Measurable σ ∧ (∀ x, 0 ≤ σ x ∧ σ x ≤ κ) ∧
      ∀ φ : E → ℝ, ∫ x, φ x ∂μ = ∫ x, σ x * φ x ∂μ₀ := by
  have hac : μ ≪ μ₀ := Measure.absolutelyContinuous_of_le_smul hle
  have hρ : μ.rnDeriv μ₀ ≤ᵐ[μ₀] fun _ ↦ ENNReal.ofReal κ := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv μ μ₀)
      fun s hs _ ↦ ?_
    rw [Measure.setLIntegral_rnDeriv' hac hs, setLIntegral_const]
    simpa using hle s
  refine ⟨fun x ↦ min κ (μ.rnDeriv μ₀ x).toReal,
    measurable_const.min (Measure.measurable_rnDeriv μ μ₀).ennreal_toReal,
    fun x ↦ ⟨le_min hκ ENNReal.toReal_nonneg, min_le_left _ _⟩, fun φ ↦ ?_⟩
  calc ∫ x, φ x ∂μ = ∫ x, φ x ∂(μ₀.withDensity (μ.rnDeriv μ₀)) := by
        rw [Measure.withDensity_rnDeriv_eq μ μ₀ hac]
    _ = ∫ x, (μ.rnDeriv μ₀ x).toReal • φ x ∂μ₀ :=
        integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv μ μ₀)
          (Measure.rnDeriv_lt_top μ μ₀) φ
    _ = ∫ x, min κ (μ.rnDeriv μ₀ x).toReal * φ x ∂μ₀ := by
        refine integral_congr_ae ?_
        filter_upwards [hρ] with x hx
        rw [smul_eq_mul, min_eq_right (ENNReal.toReal_le_of_le_ofReal hκ hx)]

/-! ### Extension to compactly supported continuous functions -/

namespace IsBoundedPositiveFunctional

variable {T : (E → ℝ) → ℝ} {κ : ℝ} (h : IsBoundedPositiveFunctional μ₀ T κ)
include h

/-- The constant `κ` is nonnegative: test `T` against a bump function. -/
theorem nonneg : 0 ≤ κ := by
  let χ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have hχ : IsTestFunction χ := ⟨χ.contDiff, χ.hasCompactSupport⟩
  refine le_of_mul_le_mul_right ?_ (χ.integral_pos (μ := μ₀))
  rw [zero_mul]
  exact (h.map_nonneg χ hχ χ.nonneg').trans (h.map_le χ hχ χ.nonneg')

/-- The sequence `T (approx μ₀ f n)` is Cauchy, since the approximations converge uniformly with
supports in a fixed compact set. -/
theorem cauchySeq_map_approx (hf : Continuous f) (hfc : HasCompactSupport f) :
    CauchySeq fun n ↦ T (approx μ₀ f n) := by
  have hK := (isCompact_closedBall (0 : E) 1).add hfc
  obtain ⟨C, hC, hTC⟩ := h.exists_forall_abs_map_le_mul hK
  have hlim := Metric.tendstoUniformly_iff.1 (tendstoUniformly_approx (μ₀ := μ₀) hf hfc)
  refine Metric.cauchySeq_iff'.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim (ε / (2 * (C + 1))) (by positivity))
  refine ⟨N, fun n hn ↦ ?_⟩
  have hφ : ∀ m, IsTestFunction (approx μ₀ f m) := fun m ↦ isTestFunction_approx hf hfc
  rw [Real.dist_eq, ← h.map_sub (hφ n) (hφ N)]
  calc |T (approx μ₀ f n - approx μ₀ f N)| ≤ C * (2 * (ε / (2 * (C + 1)))) :=
        hTC _ _ ((hφ n).sub (hφ N)) (tsupport_sub_subset_of_subset hK.isClosed
          (tsupport_approx_subset hfc) (tsupport_approx_subset hfc)) fun x ↦ ?_
    _ < ε := by
        rw [mul_div_assoc', mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  have h₁ := (hN n hn x).le
  have h₂ := (hN N le_rfl x).le
  rw [Real.dist_eq] at h₁ h₂
  calc |approx μ₀ f n x - approx μ₀ f N x|
      ≤ |approx μ₀ f n x - f x| + |f x - approx μ₀ f N x| := abs_sub_le _ _ _
    _ = |f x - approx μ₀ f n x| + |f x - approx μ₀ f N x| := by
        rw [abs_sub_comm (approx μ₀ f n x)]
    _ ≤ 2 * (ε / (2 * (C + 1))) := by linarith

/-- `T (approx μ₀ f n)` converges to `extend μ₀ T f`. -/
theorem tendsto_map_approx (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun n ↦ T (approx μ₀ f n)) atTop (𝓝 (extend μ₀ T f)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (h.cauchySeq_map_approx hf hfc))

/-- Along any sequence of test functions supported in a fixed compact set and converging
uniformly to `f`, the values of `T` tend to `extend μ₀ T f`. -/
theorem tendsto_map_of_tendstoUniformly (hf : Continuous f) (hfc : HasCompactSupport f)
    {K : Set E} (hK : IsCompact K) {ψ : ℕ → E → ℝ} (hψ : ∀ n, IsTestFunction (ψ n))
    (hψK : ∀ n, tsupport (ψ n) ⊆ K) (hlim : TendstoUniformly ψ f atTop) :
    Tendsto (fun n ↦ T (ψ n)) atTop (𝓝 (extend μ₀ T f)) := by
  have hK' := hK.union ((isCompact_closedBall (0 : E) 1).add hfc)
  have hφ : ∀ n, IsTestFunction (approx μ₀ f n) := fun n ↦ isTestFunction_approx hf hfc
  have h₀ := h.tendsto_map_of_tendstoUniformly_zero hK' (ψ := ψ - approx μ₀ f)
    (fun n ↦ (hψ n).sub (hφ n))
    (fun n ↦ tsupport_sub_subset_of_subset hK'.isClosed ((hψK n).trans subset_union_left)
      ((tsupport_approx_subset hfc).trans subset_union_right))
    (by simpa using hlim.sub (tendstoUniformly_approx (μ₀ := μ₀) hf hfc))
  have h₁ := h₀.add (h.tendsto_map_approx hf hfc)
  rw [zero_add] at h₁
  exact h₁.congr fun n ↦ by rw [Pi.sub_apply, h.map_sub (hψ n) (hφ n), sub_add_cancel]

/-- The extension is additive: `approx μ₀ f n + approx μ₀ g n` converges uniformly to `f + g`
with supports in a fixed compact set. -/
theorem extend_add (f g : C_c(E, ℝ)) :
    extend μ₀ T (f + g) = extend μ₀ T f + extend μ₀ T g := by
  have hK := ((isCompact_closedBall (0 : E) 1).add f.hasCompactSupport).union
    ((isCompact_closedBall (0 : E) 1).add g.hasCompactSupport)
  have hf : ∀ n, IsTestFunction (approx μ₀ f n) := fun n ↦
    isTestFunction_approx (map_continuous f) f.hasCompactSupport
  have hg : ∀ n, IsTestFunction (approx μ₀ g n) := fun n ↦
    isTestFunction_approx (map_continuous g) g.hasCompactSupport
  refine tendsto_nhds_unique (h.tendsto_map_of_tendstoUniformly (map_continuous (f + g))
    (f + g).hasCompactSupport hK (ψ := approx μ₀ f + approx μ₀ g)
    (fun n ↦ (hf n).add (hg n)) (fun n ↦ tsupport_add_subset_of_subset hK.isClosed
      ((tsupport_approx_subset f.hasCompactSupport).trans subset_union_left)
      ((tsupport_approx_subset g.hasCompactSupport).trans subset_union_right)) ?_)
    (((h.tendsto_map_approx (map_continuous f) f.hasCompactSupport).add
      (h.tendsto_map_approx (map_continuous g) g.hasCompactSupport)).congr fun n ↦ by
      rw [Pi.add_apply, h.map_add _ _ (hf n) (hg n)])
  simpa using (tendstoUniformly_approx (μ₀ := μ₀) (map_continuous f) f.hasCompactSupport).add
    (tendstoUniformly_approx (μ₀ := μ₀) (map_continuous g) g.hasCompactSupport)

/-- The extension is homogeneous: `c • approx μ₀ f n` converges uniformly to `c • f`. -/
theorem extend_smul (c : ℝ) (f : C_c(E, ℝ)) : extend μ₀ T (c • f) = c * extend μ₀ T f := by
  have hK := (isCompact_closedBall (0 : E) 1).add f.hasCompactSupport
  have hf : ∀ n, IsTestFunction (approx μ₀ f n) := fun n ↦
    isTestFunction_approx (map_continuous f) f.hasCompactSupport
  refine tendsto_nhds_unique (h.tendsto_map_of_tendstoUniformly (map_continuous (c • f))
    (c • f).hasCompactSupport hK (ψ := fun n ↦ c • approx μ₀ f n) (fun n ↦ (hf n).smul c)
    (fun n ↦ (closure_mono (support_const_smul_subset c _)).trans
      (tsupport_approx_subset f.hasCompactSupport)) ?_)
    (((h.tendsto_map_approx (map_continuous f) f.hasCompactSupport).const_mul c).congr fun n ↦
      (h.map_smul c _ (hf n)).symm)
  exact (uniformContinuous_const_smul c).comp_tendstoUniformly
    (tendstoUniformly_approx (μ₀ := μ₀) (map_continuous f) f.hasCompactSupport)

/-- The extension is nonnegative on nonnegative functions. -/
theorem extend_nonneg (f : C_c(E, ℝ)) (hf : 0 ≤ f) : 0 ≤ extend μ₀ T f :=
  ge_of_tendsto' (h.tendsto_map_approx (map_continuous f) f.hasCompactSupport) fun n ↦
    h.map_nonneg _ (isTestFunction_approx (map_continuous f) f.hasCompactSupport)
      (approx_nonneg fun x ↦ by simpa using le_def.1 hf x)

/-- The extension of `T` to a positive linear functional on `C_c(E, ℝ)`. -/
def extension : C_c(E, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f ↦ extend μ₀ T f
      map_add' := h.extend_add
      map_smul' := h.extend_smul }
    h.extend_nonneg

/-- The extension agrees with `T` on test functions. -/
theorem extension_apply {φ : E → ℝ} (hφ : IsTestFunction φ) :
    h.extension ⟨⟨φ, hφ.continuous⟩, hφ.2⟩ = T φ :=
  tendsto_nhds_unique (h.tendsto_map_of_tendstoUniformly hφ.continuous hφ.2 hφ.2
    (ψ := fun _ ↦ φ) (fun _ ↦ hφ) (fun _ ↦ subset_rfl) (Metric.tendstoUniformly_iff.2
      fun ε hε ↦ Eventually.of_forall fun _ x ↦ by simpa using hε)) tendsto_const_nhds

/-- The extension is bounded by `κ` times the integral on nonnegative functions, since the
smooth approximations have the same integral. -/
theorem extension_le (f : C_c(E, ℝ)) (hf : 0 ≤ f) : h.extension f ≤ κ * ∫ x, f x ∂μ₀ :=
  le_of_tendsto' (h.tendsto_map_approx (map_continuous f) f.hasCompactSupport) fun n ↦
    (h.map_le _ (isTestFunction_approx (map_continuous f) f.hasCompactSupport)
      (approx_nonneg fun x ↦ by simpa using le_def.1 hf x)).trans_eq
      (by rw [integral_approx (map_continuous f) f.hasCompactSupport])

/-- The Riesz measure of the extension `Λ` is at most `κ μ₀`: the sum of the Riesz measures of
`Λ` and of the positive functional `f ↦ κ ∫ f dμ₀ - Λ f` is `κ μ₀`. -/
theorem rieszMeasure_extension_le :
    RealRMK.rieszMeasure h.extension ≤ ENNReal.ofReal κ • μ₀ := by
  let Λ' : C_c(E, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀
    (κ • (integralPositiveLinearMap μ₀).toLinearMap - h.extension.toLinearMap) fun f hf ↦ by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, PositiveLinearMap.coe_toLinearMap,
        integralPositiveLinearMap_apply, smul_eq_mul]
      exact sub_nonneg.2 (h.extension_le f hf)
  have hΛ' (f : C_c(E, ℝ)) : Λ' f = κ * ∫ x, f x ∂μ₀ - h.extension f := rfl
  have : IsFiniteMeasureOnCompacts
      (RealRMK.rieszMeasure h.extension + RealRMK.rieszMeasure Λ') :=
    ⟨fun K hK ↦ by
      rw [Measure.add_apply]
      exact ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  have hreg : (ENNReal.ofReal κ • μ₀).Regular := Measure.Regular.smul ENNReal.ofReal_ne_top
  have heq : RealRMK.rieszMeasure h.extension + RealRMK.rieszMeasure Λ' =
      ENNReal.ofReal κ • μ₀ := by
    refine Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
    rw [integral_add_measure f.integrable f.integrable, RealRMK.integral_rieszMeasure,
      RealRMK.integral_rieszMeasure, integral_smul_measure, ENNReal.toReal_ofReal h.nonneg, hΛ',
      smul_eq_mul]
    ring
  rw [← heq]
  exact Measure.le_add_right le_rfl

/-- **A positive functional bounded by `κ` times the integral is a density in `[0, κ]`.** If
`T` is additive, homogeneous and positive on test functions, with `T φ ≤ κ ∫ φ dμ₀` for every
nonnegative test function `φ`, then there is a measurable `σ : E → ℝ` with `0 ≤ σ ≤ κ`
everywhere and `T φ = ∫ σ φ dμ₀` for every test function `φ`. -/
theorem exists_density :
    ∃ σ : E → ℝ, Measurable σ ∧ (∀ x, 0 ≤ σ x ∧ σ x ≤ κ) ∧
      ∀ φ : E → ℝ, IsTestFunction φ → T φ = ∫ x, σ x * φ x ∂μ₀ := by
  obtain ⟨σ, hσm, hσ, hσT⟩ := exists_density_of_le h.nonneg h.rieszMeasure_extension_le
  refine ⟨σ, hσm, hσ, fun φ hφ ↦ ?_⟩
  rw [← h.extension_apply hφ, ← RealRMK.integral_rieszMeasure]
  exact hσT _

end IsBoundedPositiveFunctional

end CenteredMaximal
