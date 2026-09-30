/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.ObstacleCriterion
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Smooth reduction for the centred ball maximal operator

Nonnegative smooth compactly supported functions are dense in the nonnegative cone of `L¹`.
The key construction approximates the square root of a nonnegative function in `L²` and then
squares the smooth approximant.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal NNReal ContDiff

namespace CenteredMaximal.Ball

variable {d : ℕ}

private theorem memLp_sqrt_abs_of_integrable
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Integrable f) :
    MemLp (fun x ↦ Real.sqrt |f x|) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  have h := (memLp_one_iff_integrable.mpr hf).norm_rpow_div (1 / 2 : ℝ≥0∞)
  convert h using 1
  · ext x
    simp only [Real.norm_eq_abs, ENNReal.toReal_div]
    rw [Real.sqrt_eq_rpow]
    norm_num
  · norm_num

private theorem eLpNorm_square_sub_square_le
    {u g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hg : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    eLpNorm (fun x ↦ u x ^ 2 - g x ^ 2) 1 volume ≤
      eLpNorm (u - g) 2 volume * eLpNorm (u + g) 2 volume := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
    (fun a b : ℝ ↦ a * b) 1 (by fun_prop)
    (hu.aestronglyMeasurable.sub hg.aestronglyMeasurable)
    (hu.aestronglyMeasurable.add hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ by simp [nnnorm_mul])
    (p := 2) (q := 2) (r := 1)
  convert h using 1
  · congr 1
    ext x
    dsimp
    ring
  · simp

/-- Nonnegative smooth compactly supported functions approximate the absolute value of an
integrable function in `L¹`. -/
theorem exists_smooth_nonneg_approx
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Integrable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin d) → ℝ,
      HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ (∀ x, 0 ≤ g x) ∧
        eLpNorm ((fun x ↦ |f x|) - g) 1 volume < ENNReal.ofReal ε := by
  let u : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦ Real.sqrt |f x|
  have hu : MemLp u 2 volume := memLp_sqrt_abs_of_integrable hf
  let U : ℝ≥0∞ := eLpNorm u 2 volume
  have hU : U ≠ (⊤ : ℝ≥0∞) := (ne_of_lt hu.eLpNorm_lt_top)
  have hA : 2 * U + 1 ≠ (⊤ : ℝ≥0∞) := by finiteness
  have hε₀ : ENNReal.ofReal ε ≠ 0 := by positivity
  obtain ⟨δ, hδ₀, hδ⟩ := ENNReal.exists_nnreal_pos_mul_lt hA hε₀
  let η : ℝ≥0 := min δ (1 : ℝ≥0)
  have hη₀ : 0 < η := lt_min hδ₀ zero_lt_one
  have hη₁ : (η : ℝ≥0∞) ≤ 1 := by exact_mod_cast min_le_right δ 1
  have hηδ : (η : ℝ≥0∞) ≤ δ := by exact_mod_cast min_le_left δ 1
  obtain ⟨v, hvcompact, hvsmooth, hvclose⟩ :=
    hu.exist_eLpNorm_sub_le (by simp) (by norm_num) (show (0 : ℝ) < η from hη₀)
  have hvclose' : eLpNorm (u - v) 2 volume ≤ (η : ℝ≥0∞) := by
    simpa using hvclose
  have hv : MemLp v 2 volume := hvsmooth.continuous.memLp_of_hasCompactSupport hvcompact
  let g : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦ v x ^ 2
  have hgcompact : HasCompactSupport g := by
    apply hvcompact.mono
    intro x hx
    by_contra hvx
    have hvx' : v x = 0 := by simpa [Function.mem_support] using hvx
    simp [g, hvx'] at hx
  have hgsmooth : ContDiff ℝ ∞ g := hvsmooth.pow 2
  have hgnonneg : ∀ x, 0 ≤ g x := fun x ↦ sq_nonneg _
  refine ⟨g, hgcompact, hgsmooth, hgnonneg, ?_⟩
  have hsq : (fun x ↦ |f x|) = fun x ↦ u x ^ 2 := by
    funext x
    exact (Real.sq_sqrt (abs_nonneg (f x))).symm
  rw [hsq]
  have hvnorm : eLpNorm v 2 volume ≤ U + (η : ℝ≥0∞) := by
    calc
      eLpNorm v 2 volume = eLpNorm ((v - u) + u) 2 volume := by simp
      _ ≤ eLpNorm (v - u) 2 volume + eLpNorm u 2 volume :=
        eLpNorm_add_le (by norm_num)
      _ ≤ U + (η : ℝ≥0∞) := by
        rw [eLpNorm_sub_comm]
        calc
          eLpNorm (u - v) 2 volume + eLpNorm u 2 volume ≤
              (η : ℝ≥0∞) + U := add_le_add_left hvclose' _
          _ = U + (η : ℝ≥0∞) := add_comm _ _
  have hsum : eLpNorm (u + v) 2 volume ≤ 2 * U + (η : ℝ≥0∞) := by
    calc
      _ ≤ eLpNorm u 2 volume + eLpNorm v 2 volume :=
        eLpNorm_add_le (by norm_num)
      _ ≤ 2 * U + (η : ℝ≥0∞) := by
        calc
          eLpNorm u 2 volume + eLpNorm v 2 volume ≤ U + (U + (η : ℝ≥0∞)) :=
            add_le_add_right hvnorm U
          _ = 2 * U + (η : ℝ≥0∞) := by rw [two_mul, add_assoc]
  calc
    eLpNorm (fun x ↦ u x ^ 2 - v x ^ 2) 1 volume
        ≤ eLpNorm (u - v) 2 volume * eLpNorm (u + v) 2 volume :=
          eLpNorm_square_sub_square_le hu hv
    _ ≤ (η : ℝ≥0∞) * (2 * U + η) := by gcongr
    _ ≤ (η : ℝ≥0∞) * (2 * U + 1) := by gcongr
    _ ≤ (δ : ℝ≥0∞) * (2 * U + 1) := by gcongr
    _ < ENNReal.ofReal ε := hδ

private theorem tendsto_setLIntegral_enorm_of_eLpNorm_sub
    {a : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    (ha : MemLp a 1 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hg : ∀ n, MemLp (g n) 1 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hconv : Filter.Tendsto (fun n ↦ eLpNorm (g n - a) 1 volume) Filter.atTop (nhds 0))
    (s : Set (EuclideanSpace ℝ (Fin d))) :
    Filter.Tendsto (fun n ↦ ∫⁻ x in s, ‖g n x‖ₑ)
      Filter.atTop (nhds (∫⁻ x in s, ‖a x‖ₑ)) := by
  let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict s
  have haμ : MemLp a 1 μ := ha.restrict s
  have hgμ : ∀ n, MemLp (g n) 1 μ := fun n ↦ (hg n).restrict s
  have hconvμ : Filter.Tendsto (fun n ↦ eLpNorm (g n - a) 1 μ)
      Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
    · intro n
      exact zero_le
    · intro n
      exact eLpNorm_mono_measure _ Measure.restrict_le_self
  have hLp : Filter.Tendsto (fun n ↦ (hgμ n).toLp (g n)) Filter.atTop
      (nhds (haμ.toLp a)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hgμ a haμ).2 hconvμ
  have hnorm := hLp.enorm
  have hnorm' : Filter.Tendsto (fun n ↦ eLpNorm (g n) 1 μ) Filter.atTop
      (nhds (eLpNorm a 1 μ)) := by
    simpa only [Lp.enorm_def,
      eLpNorm_congr_ae (MemLp.coeFn_toLp _)] using hnorm
  convert hnorm' using 1
  · funext n
    exact (eLpNorm_one_eq_lintegral_enorm (hgμ n).aestronglyMeasurable).symm
  · exact congrArg nhds
      (eLpNorm_one_eq_lintegral_enorm haμ.aestronglyMeasurable).symm

private theorem ballMaximalFunction_abs
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ballMaximalFunction (fun y ↦ |f y|) x = ballMaximalFunction f x := by
  simp only [ballMaximalFunction, Real.enorm_abs]

private theorem eventually_ball_level_of_eLpNorm_tendsto
    {a : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    (ha : MemLp a 1 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hg : ∀ n, MemLp (g n) 1 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hconv : Filter.Tendsto (fun n ↦ eLpNorm (g n - a) 1 volume) Filter.atTop (nhds 0))
    {x : EuclideanSpace ℝ (Fin d)} {α : ℝ≥0∞}
    (hx : α < ballMaximalFunction a x) :
    ∀ᶠ n in Filter.atTop, α < ballMaximalFunction (g n) x := by
  obtain ⟨r, hr, hxr⟩ := exists_lt_ball_average_of_lt_ballMaximalFunction hx
  have hball := tendsto_setLIntegral_enorm_of_eLpNorm_sub ha hg hconv (ball x r)
  have hvol : (volume (ball x r))⁻¹ ≠ (⊤ : ℝ≥0∞) := by
    apply ENNReal.inv_ne_top.mpr
    exact ne_of_gt (Metric.measure_ball_pos volume x hr)
  have hscaled := ENNReal.Tendsto.const_mul hball (Or.inr hvol)
  have hEventually : ∀ᶠ n in Filter.atTop,
      α < (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖g n y‖ₑ :=
    hscaled.eventually (lt_mem_nhds hxr)
  exact hEventually.mono fun n hn ↦ hn.trans_le (le_ballMaximalFunction (g n) x hr)

private theorem ball_level_bound_of_dense_sequence
    {a : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : ℕ → EuclideanSpace ℝ (Fin d) → ℝ}
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (ha : Integrable a volume) (hg : ∀ n, Integrable (g n) volume)
    (hconv : Filter.Tendsto (fun n ↦ eLpNorm (g n - a) 1 volume)
      Filter.atTop (nhds 0))
    (hbound : ∀ (n : ℕ) (α : ℝ≥0∞),
      α * volume {x | α < ballMaximalFunction (g n) x} ≤
        C * ∫⁻ y, ‖g n y‖ₑ) (α : ℝ≥0∞) :
    α * volume {x | α < ballMaximalFunction a x} ≤ C * ∫⁻ y, ‖a y‖ₑ := by
  let E : ℕ → Set (EuclideanSpace ℝ (Fin d)) :=
    fun n ↦ {x | α < ballMaximalFunction (g n) x}
  let F : ℕ → Set (EuclideanSpace ℝ (Fin d)) :=
    fun N ↦ ⋂ (n : ℕ) (_ : N ≤ n), E n
  have hFmono : Monotone F := by
    intro N M hNM x hx
    simp only [F, Set.mem_iInter] at hx ⊢
    intro n hn
    exact hx n (hNM.trans hn)
  have hsub : {x | α < ballMaximalFunction a x} ⊆ ⋃ N, F N := by
    intro x hx
    have hev := eventually_ball_level_of_eLpNorm_tendsto
      (memLp_one_iff_integrable.mpr ha) (fun n ↦ memLp_one_iff_integrable.mpr (hg n))
      hconv hx
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    simp only [F, Set.mem_iInter]
    intro n hn
    exact hN n hn
  have hmass : Filter.Tendsto (fun n ↦ ∫⁻ y, ‖g n y‖ₑ)
      Filter.atTop (nhds (∫⁻ y, ‖a y‖ₑ)) := by
    simpa only [Measure.restrict_univ] using
      tendsto_setLIntegral_enorm_of_eLpNorm_sub
        (memLp_one_iff_integrable.mpr ha)
        (fun n ↦ memLp_one_iff_integrable.mpr (hg n)) hconv Set.univ
  have hright : Filter.Tendsto (fun n ↦ C * ∫⁻ y, ‖g n y‖ₑ)
      Filter.atTop (nhds (C * ∫⁻ y, ‖a y‖ₑ)) :=
    ENNReal.Tendsto.const_mul hmass (Or.inr hC)
  have hFbound (N : ℕ) : α * volume (F N) ≤ C * ∫⁻ y, ‖a y‖ₑ := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hright
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hFn : F N ⊆ E n := by
      intro x hx
      simp only [F, Set.mem_iInter] at hx
      exact hx n hn
    exact (mul_le_mul_right (measure_mono hFn) α).trans (hbound n α)
  calc
    α * volume {x | α < ballMaximalFunction a x} ≤
        α * volume (⋃ N, F N) := mul_le_mul_right (measure_mono hsub) α
    _ = ⨆ N, α * volume (F N) := by rw [hFmono.measure_iUnion, ENNReal.mul_iSup]
    _ ≤ C * ∫⁻ y, ‖a y‖ₑ := iSup_le hFbound

/-- A weak type estimate for nonnegative smooth compactly supported inputs extends to every
integrable real-valued input. -/
theorem isBallWeakTypeBound_of_smooth_nonneg {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hSmooth : IsSmoothBallWeakTypeBound d C) : IsBallWeakTypeBound d C := by
  classical
  intro f hf α
  let a : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦ |f x|
  have ha : Integrable a volume := hf.abs
  let εn : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ)
  have hεn (n : ℕ) : 0 < εn n := by
    dsimp [εn]
    positivity
  have hApprox (n : ℕ) :
      ∃ g : EuclideanSpace ℝ (Fin d) → ℝ,
        HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ (∀ x, 0 ≤ g x) ∧
          eLpNorm (a - g) 1 volume < ENNReal.ofReal (εn n) := by
    exact exists_smooth_nonneg_approx hf (hεn n)
  choose g hgcomp hgsmooth hgnn hgerr using hApprox
  have hgInt (n : ℕ) : Integrable (g n) volume :=
    (hgsmooth n).continuous.integrable_of_hasCompactSupport (hgcomp n)
  have hεtend : Filter.Tendsto εn Filter.atTop (nhds 0) := by
    simpa only [εn, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hεtend' : Filter.Tendsto (fun n ↦ ENNReal.ofReal (εn n))
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
    simpa using ENNReal.tendsto_ofReal hεtend
  have herrtend : Filter.Tendsto (fun n ↦ eLpNorm (a - g n) 1 volume)
      Filter.atTop (nhds 0) := by
    have h := tendsto_of_tendsto_of_tendsto_of_le_of_le
      (f := fun n ↦ eLpNorm (a - g n) 1 volume)
      (g := fun _ ↦ (0 : ℝ≥0∞))
      (h := fun n ↦ ENNReal.ofReal (εn n))
      tendsto_const_nhds hεtend'
      (fun _ ↦ zero_le) (fun n ↦ (hgerr n).le)
    simpa only [ENNReal.ofReal_zero] using h
  have hconv : Filter.Tendsto (fun n ↦ eLpNorm (g n - a) 1 volume)
      Filter.atTop (nhds 0) := by
    simpa only [eLpNorm_sub_comm] using herrtend
  have hbound (n : ℕ) (β : ℝ≥0∞) :
      β * volume {x | β < ballMaximalFunction (g n) x} ≤ C * ∫⁻ y, ‖g n y‖ₑ :=
    hSmooth (g n) (hgcomp n) (hgsmooth n) (hgnn n) β
  have hfinal := ball_level_bound_of_dense_sequence hC ha hgInt hconv hbound α
  simpa only [a, ballMaximalFunction_abs, Real.enorm_abs] using hfinal

end CenteredMaximal.Ball
