/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.DirichletSmoothComposition
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

/-!
# Smooth approximation of the positive part

The scalar maps `smoothPositive ε` are smooth, one-Lipschitz, and fix zero for `ε > 0`.
As `ε` tends to zero, their values approach `t ↦ max t 0`, while their derivatives
approach the indicator of `t > 0`, including derivative zero at `t = 0`. This choice
removes the need for a separate theorem that Sobolev gradients vanish on level sets.
-/

@[expose] public section
open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal NNReal
noncomputable section
namespace CenteredMaximal.Ball.DirichletSobolev

/-- A smooth one-Lipschitz regularization of the positive part, adjusted so that its
derivative at zero is zero. -/
def smoothPositive (ε t : ℝ) : ℝ :=
  (t + Real.sqrt (t ^ 2 + ε ^ 2) - ε - ε * t / Real.sqrt (t ^ 2 + ε ^ 2)) / 2

private theorem smoothPositive_arg_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 < t ^ 2 + ε ^ 2 := by positivity

private theorem smoothPositive_sqrt_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 < Real.sqrt (t ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr (smoothPositive_arg_pos hε t)

theorem smoothPositive_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothPositive ε) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.sqrt (t ^ 2 + ε ^ 2)) :=
    ((contDiff_id.pow 2).add contDiff_const).sqrt
      (fun t => (smoothPositive_arg_pos hε t).ne')
  have hr : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => ε * t / Real.sqrt (t ^ 2 + ε ^ 2)) :=
    (contDiff_const.mul contDiff_id).div hs
      (fun t => (smoothPositive_sqrt_pos hε t).ne')
  unfold smoothPositive
  fun_prop

private theorem smoothPositive_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (smoothPositive ε)
      ((1 + t / Real.sqrt (t ^ 2 + ε ^ 2) -
        ε ^ 3 / Real.sqrt (t ^ 2 + ε ^ 2) ^ 3) / 2) t := by
  let s : ℝ := Real.sqrt (t ^ 2 + ε ^ 2)
  have hspos : 0 < s := smoothPositive_sqrt_pos hε t
  have hsne : s ≠ 0 := hspos.ne'
  have hsq : s ^ 2 = t ^ 2 + ε ^ 2 := Real.sq_sqrt (smoothPositive_arg_pos hε t).le
  have harg : HasDerivAt (fun y : ℝ => y ^ 2 + ε ^ 2) (2 * t) t := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      (hasDerivAt_pow 2 t).add_const (ε ^ 2)
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + ε ^ 2)) (t / s) t := by
    convert harg.sqrt (smoothPositive_arg_pos hε t).ne' using 1
    change t / s = 2 * t / (2 * s)
    field_simp
  have hnum : HasDerivAt (fun y : ℝ => ε * y) ε t := by
    simpa using (hasDerivAt_id t).const_mul ε
  have hq := hnum.div hs hsne
  have hfull := (((hasDerivAt_id t).add hs).sub_const ε).sub hq |>.div_const 2
  change HasDerivAt (smoothPositive ε)
    ((1 + t / s - (ε * s - ε * t * (t / s)) / s ^ 2) / 2) t at hfull
  refine hfull.congr_deriv ?_
  change (1 + t / s - (ε * s - ε * t * (t / s)) / s ^ 2) / 2 =
    (1 + t / s - ε ^ 3 / s ^ 3) / 2
  field_simp
  nlinarith [hsq]

theorem deriv_smoothPositive {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    deriv (smoothPositive ε) t =
      (1 + t / Real.sqrt (t ^ 2 + ε ^ 2) -
        ε ^ 3 / Real.sqrt (t ^ 2 + ε ^ 2) ^ 3) / 2 :=
  (smoothPositive_hasDerivAt hε t).deriv

theorem smoothPositive_deriv_bound {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ‖deriv (smoothPositive ε) t‖ ≤ 1 := by
  let s : ℝ := Real.sqrt (t ^ 2 + ε ^ 2)
  have hspos : 0 < s := smoothPositive_sqrt_pos hε t
  have hsq : s ^ 2 = t ^ 2 + ε ^ 2 := Real.sq_sqrt (smoothPositive_arg_pos hε t).le
  have htsq : t ^ 2 ≤ s ^ 2 := by nlinarith [sq_nonneg ε]
  have htlo : -s ≤ t := by nlinarith [htsq]
  have hthi : t ≤ s := by nlinarith [htsq]
  have hεsq : ε ^ 2 ≤ s ^ 2 := by nlinarith [sq_nonneg t]
  have hεle : ε ≤ s := by nlinarith [hεsq]
  have hqlo : -1 ≤ t / s := (le_div_iff₀ hspos).mpr (by nlinarith)
  have hqhi : t / s ≤ 1 := (div_le_iff₀ hspos).mpr (by nlinarith)
  have hcubelo : 0 ≤ ε ^ 3 / s ^ 3 := by positivity
  have hcubehi : ε ^ 3 / s ^ 3 ≤ 1 :=
    (div_le_one (pow_pos hspos 3)).mpr (pow_le_pow_left₀ hε.le hεle 3)
  rw [deriv_smoothPositive hε]
  simp only [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> dsimp [s] at * <;> linarith

theorem smoothPositive_zero {ε : ℝ} (hε : 0 < ε) : smoothPositive ε 0 = 0 := by
  simp [smoothPositive, Real.sqrt_sq hε.le]

theorem smoothPositive_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith 1 (smoothPositive ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    ((smoothPositive_contDiff hε).differentiable (by simp))
  intro t
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  exact smoothPositive_deriv_bound hε t

theorem smoothPositive_tendsto (t : ℝ) :
    Tendsto (fun n : ℕ => smoothPositive (1 / (n + 1 : ℝ)) t)
      atTop (𝓝 (max t 0)) := by
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  by_cases ht : t = 0
  · subst t
    have hzero : ∀ n, smoothPositive (ε n) 0 = 0 := fun n =>
      smoothPositive_zero (by positivity)
    simp only [max_self]
    change Tendsto (fun n => smoothPositive (ε n) 0) atTop (𝓝 0)
    simp_rw [hzero]
    exact tendsto_const_nhds
  · have harg : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    have hcont : ContinuousAt (fun e : ℝ => smoothPositive e t) 0 := by
      unfold smoothPositive
      fun_prop (disch := positivity)
    have hlim := hcont.tendsto.comp hε0
    have hval : smoothPositive 0 t = max t 0 := by
      simp only [smoothPositive, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        zero_mul, zero_div, sub_zero, add_zero]
      rw [Real.sqrt_sq_eq_abs]
      rcases lt_or_gt_of_ne ht with hneg | hpos
      · rw [max_eq_right hneg.le, abs_of_neg hneg]
        ring
      · rw [max_eq_left hpos.le, abs_of_pos hpos]
        ring
    simpa only [Function.comp_def, ε, hval] using hlim

theorem smoothPositive_deriv_tendsto (t : ℝ) :
    Tendsto (fun n : ℕ => deriv (smoothPositive (1 / (n + 1 : ℝ))) t)
      atTop (𝓝 (if 0 < t then 1 else 0)) := by
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  by_cases ht : t = 0
  · subst t
    have hzero : ∀ n, deriv (smoothPositive (ε n)) 0 = 0 := by
      intro n
      rw [deriv_smoothPositive (hεpos n)]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, zero_div,
        Real.sqrt_sq (hεpos n).le]
      rw [div_self (pow_ne_zero 3 (hεpos n).ne')]
      norm_num
    simp only [lt_self_iff_false, ↓reduceIte]
    change Tendsto (fun n => deriv (smoothPositive (ε n)) 0) atTop (𝓝 0)
    simp_rw [hzero]
    exact tendsto_const_nhds
  · have harg : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    let Q : ℝ → ℝ := fun e =>
      (1 + t / Real.sqrt (t ^ 2 + e ^ 2) -
        e ^ 3 / Real.sqrt (t ^ 2 + e ^ 2) ^ 3) / 2
    have hcont : ContinuousAt Q 0 := by
      dsimp [Q]
      fun_prop (disch := positivity)
    have hlim := hcont.tendsto.comp hε0
    have hval : Q 0 = if 0 < t then 1 else 0 := by
      simp only [Q, zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_div, sub_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
      rw [Real.sqrt_sq_eq_abs]
      split_ifs with hpos
      · rw [abs_of_pos hpos]
        field_simp
        norm_num
      · have hneg : t < 0 := lt_of_le_of_ne (not_lt.mp hpos) ht
        rw [abs_of_neg hneg]
        field_simp
        ring
    have hrewrite : (fun n : ℕ => deriv (smoothPositive (ε n)) t) = Q ∘ ε := by
      funext n
      exact deriv_smoothPositive (hεpos n) t
    change Tendsto (fun n => deriv (smoothPositive (ε n)) t) atTop _
    rw [hrewrite]
    simpa only [hval] using hlim

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Positive part preserves the zero-boundary Sobolev space and has the expected
weak gradient, including at the zero level. -/
theorem exists_isPositivePartGraph (U : H01 Ω) :
    ∃ P : H01 Ω, IsPositivePartGraph U P := by
  classical
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  set v : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ((U : H1amb Ω) 0 x : ℝ) with hvdef
  set g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun i x => ((U : H1amb Ω) i.succ x : ℝ) with hgdef
  have hvm : MemLp v 2 (volume.restrict Ω) := Lp.memLp _
  have hgm : ∀ i, MemLp (g i) 2 (volume.restrict Ω) := fun i => Lp.memLp _
  have hP : ∀ n : ℕ, ∃ W ∈ H01 Ω,
      ((W 0 : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] (fun x => smoothPositive (ε n) (v x)) ∧
      ∀ i : Fin d, ((W i.succ : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω]
          (fun x => deriv (smoothPositive (ε n)) (v x) * g i x) := by
    intro n
    exact exists_mem_H01_smooth_comp U.2 (smoothPositive_contDiff (hεpos n))
      (smoothPositive_lipschitz (hεpos n)) (smoothPositive_zero (hεpos n))
      (smoothPositive_deriv_bound (hεpos n))
  choose W hW hW0 hWi using hP
  let Pₙ : ℕ → H01 Ω := fun n => ⟨W n, hW n⟩
  let p0 : L2D Ω := Lp.posPart ((U : H1amb Ω) 0)
  have hp0ae : (p0 : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => max (v x) 0 := by
    simpa only [p0, v] using Lp.coeFn_posPart ((U : H1amb Ω) 0)
  have hgradmeas (i : Fin d) : AEStronglyMeasurable
      (fun x => if 0 < v x then g i x else 0) (volume.restrict Ω) := by
    have hs : NullMeasurableSet {x | 0 < v x} (volume.restrict Ω) :=
      stronglyMeasurable_const.aestronglyMeasurable.nullMeasurableSet_lt
        hvm.aestronglyMeasurable
    convert (hgm i).aestronglyMeasurable.indicator₀ hs using 1
    · rfl
  have hgradMem (i : Fin d) : MemLp
      (fun x => if 0 < v x then g i x else 0) 2 (volume.restrict Ω) := by
    refine (hgm i).of_le (hgradmeas i) (Eventually.of_forall fun x => ?_)
    split_ifs <;> simp
  let P : H1amb Ω := WithLp.toLp 2 (Fin.cons p0 fun i =>
    (hgradMem i).toLp (fun x => if 0 < v x then g i x else 0))
  have hP0 : ((P 0 : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => max (v x) 0 := by simpa [P] using hp0ae
  have hPi : ∀ i : Fin d, ((P i.succ : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => if 0 < v x then g i x else 0 := by
    intro i
    simpa [P] using (hgradMem i).coeFn_toLp
  have hvalMem : MemLp (fun x => max (v x) 0) 2 (volume.restrict Ω) :=
    (Lp.memLp p0).ae_eq hp0ae
  have hvalDCT : Tendsto (fun n => eLpNorm
      ((fun x => smoothPositive (ε n) (v x)) - fun x => max (v x) 0)
      2 (volume.restrict Ω)) atTop (𝓝 0) := by
    let F : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
      fun n x => smoothPositive (ε n) (v x) - max (v x) 0
    have hFm : ∀ n, AEStronglyMeasurable (F n) (volume.restrict Ω) := fun n =>
      ((smoothPositive_contDiff (hεpos n)).continuous.comp_aestronglyMeasurable
        hvm.aestronglyMeasurable).sub
          (((continuous_id.max continuous_const).comp_aestronglyMeasurable
            hvm.aestronglyMeasurable))
    have hFb : ∀ n x, ‖F n x‖ ≤ ‖(2 : ℝ) * v x‖ := by
      intro n x
      have hFbound : ‖smoothPositive (ε n) (v x)‖ ≤ ‖v x‖ := by
        have h := (smoothPositive_lipschitz (hεpos n)).norm_sub_le (v x) 0
        simpa only [smoothPositive_zero (hεpos n), sub_zero, NNReal.coe_one,
          one_mul] using h
      have hmax : ‖max (v x) 0‖ ≤ ‖v x‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        rw [Real.norm_eq_abs]
        exact max_le (le_abs_self _) (abs_nonneg _)
      calc
        ‖F n x‖ ≤ ‖smoothPositive (ε n) (v x)‖ + ‖max (v x) 0‖ := norm_sub_le _ _
        _ ≤ ‖v x‖ + ‖v x‖ := add_le_add hFbound hmax
        _ = ‖(2 : ℝ) * v x‖ := by simp [norm_mul, Real.norm_eq_abs]; ring
    have hFp : ∀ᵐ x ∂(volume.restrict Ω), Tendsto (fun n => F n x) atTop (𝓝 0) := by
      filter_upwards with x
      have ht := (smoothPositive_tendsto (v x)).sub_const (max (v x) 0)
      simpa only [F, sub_self] using ht
    exact tendsto_eLpNorm_two_zero_of_dominated (volume.restrict Ω)
      ((hvm).const_mul 2) hFm hFb hFp
  have hgradDCT : ∀ i : Fin d, Tendsto (fun n => eLpNorm
      ((fun x => deriv (smoothPositive (ε n)) (v x) * g i x) -
        fun x => if 0 < v x then g i x else 0)
      2 (volume.restrict Ω)) atTop (𝓝 0) := by
    intro i
    let F : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n x =>
      deriv (smoothPositive (ε n)) (v x) * g i x -
        (if 0 < v x then g i x else 0)
    have hderivcont : ∀ n, Continuous (deriv (smoothPositive (ε n))) := fun n =>
      (smoothPositive_contDiff (hεpos n)).continuous_deriv (by simp)
    have hFm : ∀ n, AEStronglyMeasurable (F n) (volume.restrict Ω) := fun n =>
      ((hderivcont n).comp_aestronglyMeasurable hvm.aestronglyMeasurable).mul
        (hgm i).aestronglyMeasurable |>.sub (hgradmeas i)
    have hFb : ∀ n x, ‖F n x‖ ≤ ‖(2 : ℝ) * g i x‖ := by
      intro n x
      have hpart : ‖(if 0 < v x then g i x else 0)‖ ≤ ‖g i x‖ := by
        split_ifs <;> simp
      calc
        ‖F n x‖ ≤ ‖deriv (smoothPositive (ε n)) (v x) * g i x‖ +
          ‖(if 0 < v x then g i x else 0)‖ := norm_sub_le _ _
        _ ≤ ‖g i x‖ + ‖g i x‖ := by
          rw [norm_mul]
          have hmul : ‖deriv (smoothPositive (ε n)) (v x)‖ * ‖g i x‖ ≤ ‖g i x‖ := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right
                (smoothPositive_deriv_bound (hεpos n) (v x)) (norm_nonneg (g i x))
          exact add_le_add hmul hpart
        _ = ‖(2 : ℝ) * g i x‖ := by simp [norm_mul, Real.norm_eq_abs]; ring
    have hFp : ∀ᵐ x ∂(volume.restrict Ω), Tendsto (fun n => F n x) atTop (𝓝 0) := by
      filter_upwards with x
      have ht := (smoothPositive_deriv_tendsto (v x)).mul_const (g i x)
      have htarget : (if 0 < v x then (1 : ℝ) else 0) * g i x =
          if 0 < v x then g i x else 0 := by split_ifs <;> simp
      rw [htarget] at ht
      have hs := ht.sub_const (if 0 < v x then g i x else 0)
      simpa only [F, sub_self] using hs
    exact tendsto_eLpNorm_two_zero_of_dominated (volume.restrict Ω)
      ((hgm i).const_mul 2) hFm hFb hFp
  have hPt : Tendsto (fun n => W n) atTop (𝓝 P) := by
    have hWt0 : Tendsto (fun n => W n 0) atTop (𝓝 p0) := by
      apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n => W n 0) p0).2
      convert hvalDCT using 1
      funext n
      apply eLpNorm_congr_ae
      exact (hW0 n).sub hp0ae
    have hWti (i : Fin d) : Tendsto (fun n => W n i.succ) atTop (𝓝 (P i.succ)) := by
      apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun n => W n i.succ) (P i.succ)).2
      convert hgradDCT i using 1
      funext n
      apply eLpNorm_congr_ae
      exact (hWi n i).sub (hPi i)
    have hc : Tendsto (fun n => (W n).ofLp) atTop (𝓝 P.ofLp) := by
      rw [tendsto_pi_nhds]
      intro j
      induction j using Fin.cases with
      | zero => exact hWt0
      | succ i => exact hWti i
    convert ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin (d + 1) => L2D Ω)).tendsto
      P.ofLp).comp hc using 1
    funext n
    exact (WithLp.toLp_ofLp 2 (W n)).symm
  have hPmem : P ∈ H01 Ω := by
    exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hPt
      (Eventually.of_forall hW)
  exact ⟨⟨P, hPmem⟩, ⟨hP0, hPi⟩⟩

/-- The minimum of two zero-boundary Sobolev functions has the expected weak gradient. -/
theorem exists_isMinimumGraph (U V : H01 Ω) :
    ∃ M : H01 Ω, IsMinimumGraph U V M := by
  obtain ⟨P, hP⟩ := exists_isPositivePartGraph (U - V)
  exact ⟨U - P, isMinimumGraph_of_isPositivePartGraph U V P hP⟩

end CenteredMaximal.Ball.DirichletSobolev
