/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.DirichletPositivePart
public import Mathlib.Tactic

/-!
# Shifted positive-part truncations in Dirichlet H₀¹

For nonnegative thresholds, the positive part of `u - t` remains in H₀¹. Its weak gradient
is the gradient of `u` where `u > t` and zero elsewhere. A zero-fixing smooth
regularizer gives this even at the threshold level, where the derivative converges to zero.
-/

@[expose] public section
open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal NNReal
noncomputable section
namespace CenteredMaximal.Ball.DirichletSobolev
variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

def smoothShiftedPositive (ε t s : ℝ) : ℝ :=
  smoothPositive ε (s - t) - smoothPositive ε (-t)

theorem smoothShiftedPositive_contDiff {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothShiftedPositive ε t) := by
  unfold smoothShiftedPositive
  exact ((smoothPositive_contDiff hε).comp (contDiff_id.sub contDiff_const)).sub
    contDiff_const

theorem smoothShiftedPositive_zero (ε t : ℝ) : smoothShiftedPositive ε t 0 = 0 := by
  simp [smoothShiftedPositive]

theorem smoothShiftedPositive_deriv {ε : ℝ} (_hε : 0 < ε) (t s : ℝ) :
    deriv (smoothShiftedPositive ε t) s = deriv (smoothPositive ε) (s - t) := by
  unfold smoothShiftedPositive
  rw [deriv_sub_const, deriv_comp_sub_const]

theorem smoothShiftedPositive_deriv_bound {ε : ℝ} (hε : 0 < ε) (t s : ℝ) :
    ‖deriv (smoothShiftedPositive ε t) s‖ ≤ 1 := by
  rw [smoothShiftedPositive_deriv hε]
  exact smoothPositive_deriv_bound hε (s - t)

theorem smoothShiftedPositive_lipschitz {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    LipschitzWith 1 (smoothShiftedPositive ε t) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    ((smoothShiftedPositive_contDiff hε t).differentiable (by simp))
  intro s
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  exact smoothShiftedPositive_deriv_bound hε t s

theorem smoothShiftedPositive_tendsto (t s : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => smoothShiftedPositive (1 / (n + 1 : ℝ)) t s)
      atTop (𝓝 (max (s - t) 0)) := by
  have h := (smoothPositive_tendsto (s - t)).sub (smoothPositive_tendsto (-t))
  have hneg : max (-t) 0 = 0 := max_eq_right (neg_nonpos.mpr ht)
  simpa only [smoothShiftedPositive, hneg, sub_zero] using h

theorem smoothShiftedPositive_deriv_tendsto (t s : ℝ) :
    Tendsto (fun n : ℕ => deriv (smoothShiftedPositive (1 / (n + 1 : ℝ)) t) s)
      atTop (𝓝 (if t < s then 1 else 0)) := by
  have h := smoothPositive_deriv_tendsto (s - t)
  convert h using 1
  · funext n
    exact smoothShiftedPositive_deriv (by positivity) t s
  · simp only [sub_pos]

theorem exists_shiftedPositivePartGraph (U : H01 Ω) (t : ℝ) (ht : 0 ≤ t) :
    ∃ P : H01 Ω,
      (((P : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x => max (((U : H1amb Ω) 0 x : ℝ) - t) 0) ∧
      ∀ i : Fin d, ((P : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x =>
          if t < ((U : H1amb Ω) 0 x : ℝ) then ((U : H1amb Ω) i.succ x : ℝ) else 0 := by
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
        =ᵐ[volume.restrict Ω] (fun x => smoothShiftedPositive (ε n) t (v x)) ∧
      ∀ i : Fin d, ((W i.succ : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω]
          (fun x => deriv (smoothShiftedPositive (ε n) t) (v x) * g i x) := by
    intro n
    exact exists_mem_H01_smooth_comp U.2 (smoothShiftedPositive_contDiff (hεpos n) t)
      (smoothShiftedPositive_lipschitz (hεpos n) t) (smoothShiftedPositive_zero (ε n) t)
      (smoothShiftedPositive_deriv_bound (hεpos n) t)
  choose W hW hW0 hWi using hP
  let Pₙ : ℕ → H01 Ω := fun n => ⟨W n, hW n⟩
  have hvalmeas : AEStronglyMeasurable (fun x => max (v x - t) 0)
      (volume.restrict Ω) :=
    (((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
      hvm.aestronglyMeasurable)
  have hvalbound : ∀ x, ‖max (v x - t) 0‖ ≤ ‖v x‖ := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), Real.norm_eq_abs]
    exact max_le ((sub_le_self (v x) ht).trans (le_abs_self _)) (abs_nonneg _)
  have hvalMem : MemLp (fun x => max (v x - t) 0) 2 (volume.restrict Ω) :=
    hvm.of_le hvalmeas (Eventually.of_forall hvalbound)
  let p0 : L2D Ω := hvalMem.toLp (fun x => max (v x - t) 0)
  have hp0ae : (p0 : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => max (v x - t) 0 := hvalMem.coeFn_toLp
  have hgradmeas (i : Fin d) : AEStronglyMeasurable
      (fun x => if t < v x then g i x else 0) (volume.restrict Ω) := by
    have hs : NullMeasurableSet {x | t < v x} (volume.restrict Ω) :=
      stronglyMeasurable_const.aestronglyMeasurable.nullMeasurableSet_lt
        hvm.aestronglyMeasurable
    convert (hgm i).aestronglyMeasurable.indicator₀ hs using 1
    · rfl
  have hgradMem (i : Fin d) : MemLp
      (fun x => if t < v x then g i x else 0) 2 (volume.restrict Ω) := by
    refine (hgm i).of_le (hgradmeas i) (Eventually.of_forall fun x => ?_)
    split_ifs <;> simp
  let P : H1amb Ω := WithLp.toLp 2 (Fin.cons p0 fun i =>
    (hgradMem i).toLp (fun x => if t < v x then g i x else 0))
  have hP0 : ((P 0 : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => max (v x - t) 0 := by simpa [P] using hp0ae
  have hPi : ∀ i : Fin d, ((P i.succ : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => if t < v x then g i x else 0 := by
    intro i
    simpa [P] using (hgradMem i).coeFn_toLp
  have hvalDCT : Tendsto (fun n => eLpNorm
      ((fun x => smoothShiftedPositive (ε n) t (v x)) - fun x => max (v x - t) 0)
      2 (volume.restrict Ω)) atTop (𝓝 0) := by
    let F : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
      fun n x => smoothShiftedPositive (ε n) t (v x) - max (v x - t) 0
    have hFm : ∀ n, AEStronglyMeasurable (F n) (volume.restrict Ω) := fun n =>
      ((smoothShiftedPositive_contDiff (hεpos n) t).continuous.comp_aestronglyMeasurable
        hvm.aestronglyMeasurable).sub hvalmeas
    have hFb : ∀ n x, ‖F n x‖ ≤ ‖(2 : ℝ) * v x‖ := by
      intro n x
      have hFbound : ‖smoothShiftedPositive (ε n) t (v x)‖ ≤ ‖v x‖ := by
        have h := (smoothShiftedPositive_lipschitz (hεpos n) t).norm_sub_le (v x) 0
        simpa only [smoothShiftedPositive_zero (ε n) t, sub_zero, NNReal.coe_one,
          one_mul] using h
      have hmax : ‖max (v x - t) 0‖ ≤ ‖v x‖ := hvalbound x
      calc
        ‖F n x‖ ≤ ‖smoothShiftedPositive (ε n) t (v x)‖ + ‖max (v x - t) 0‖ :=
          norm_sub_le _ _
        _ ≤ ‖v x‖ + ‖v x‖ := add_le_add hFbound hmax
        _ = ‖(2 : ℝ) * v x‖ := by simp [norm_mul, Real.norm_eq_abs]; ring
    have hFp : ∀ᵐ x ∂(volume.restrict Ω), Tendsto (fun n => F n x) atTop (𝓝 0) := by
      filter_upwards with x
      have ht := (smoothShiftedPositive_tendsto t (v x) ht).sub_const (max (v x - t) 0)
      simpa only [F, sub_self] using ht
    exact tendsto_eLpNorm_two_zero_of_dominated (volume.restrict Ω)
      ((hvm).const_mul 2) hFm hFb hFp
  have hgradDCT : ∀ i : Fin d, Tendsto (fun n => eLpNorm
      ((fun x => deriv (smoothShiftedPositive (ε n) t) (v x) * g i x) -
        fun x => if t < v x then g i x else 0)
      2 (volume.restrict Ω)) atTop (𝓝 0) := by
    intro i
    let F : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n x =>
      deriv (smoothShiftedPositive (ε n) t) (v x) * g i x -
        (if t < v x then g i x else 0)
    have hderivcont : ∀ n, Continuous (deriv (smoothShiftedPositive (ε n) t)) := fun n =>
      (smoothShiftedPositive_contDiff (hεpos n) t).continuous_deriv (by simp)
    have hFm : ∀ n, AEStronglyMeasurable (F n) (volume.restrict Ω) := fun n =>
      ((hderivcont n).comp_aestronglyMeasurable hvm.aestronglyMeasurable).mul
        (hgm i).aestronglyMeasurable |>.sub (hgradmeas i)
    have hFb : ∀ n x, ‖F n x‖ ≤ ‖(2 : ℝ) * g i x‖ := by
      intro n x
      have hpart : ‖(if t < v x then g i x else 0)‖ ≤ ‖g i x‖ := by
        split_ifs <;> simp
      calc
        ‖F n x‖ ≤ ‖deriv (smoothShiftedPositive (ε n) t) (v x) * g i x‖ +
          ‖(if t < v x then g i x else 0)‖ := norm_sub_le _ _
        _ ≤ ‖g i x‖ + ‖g i x‖ := by
          rw [norm_mul]
          have hmul : ‖deriv (smoothShiftedPositive (ε n) t) (v x)‖ * ‖g i x‖ ≤
              ‖g i x‖ := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right
                (smoothShiftedPositive_deriv_bound (hεpos n) t (v x)) (norm_nonneg (g i x))
          exact add_le_add hmul hpart
        _ = ‖(2 : ℝ) * g i x‖ := by simp [norm_mul, Real.norm_eq_abs]; ring
    have hFp : ∀ᵐ x ∂(volume.restrict Ω), Tendsto (fun n => F n x) atTop (𝓝 0) := by
      filter_upwards with x
      have ht := (smoothShiftedPositive_deriv_tendsto t (v x)).mul_const (g i x)
      have htarget : (if t < v x then (1 : ℝ) else 0) * g i x =
          if t < v x then g i x else 0 := by split_ifs <;> simp
      rw [htarget] at ht
      have hs := ht.sub_const (if t < v x then g i x else 0)
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


/-- Upper truncation `min u t` belongs to `H₀¹` for `t ≥ 0`, with the expected
weak gradient. At the level `u=t` the gradient is that of `u`. -/
theorem exists_upperTruncationGraph (U : H01 Ω) (t : ℝ) (ht : 0 ≤ t) :
    ∃ M : H01 Ω,
      (((M : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x => min (((U : H1amb Ω) 0 x : ℝ)) t) ∧
      ∀ i : Fin d, ((M : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x =>
          if t < ((U : H1amb Ω) 0 x : ℝ) then 0
          else ((U : H1amb Ω) i.succ x : ℝ) := by
  obtain ⟨P, hP0, hPi⟩ := exists_shiftedPositivePartGraph U t ht
  refine ⟨U - P, ?_, ?_⟩
  · filter_upwards [hP0, Lp.coeFn_sub ((U : H1amb Ω) 0) ((P : H1amb Ω) 0)] with x hp hm
    simp only [Submodule.coe_sub, PiLp.sub_apply, Pi.sub_apply, hm, hp]
    by_cases hx : t < ((U : H1amb Ω) 0 x : ℝ)
    · rw [max_eq_left (sub_nonneg.mpr hx.le), min_eq_right hx.le]
      ring
    · have hle := le_of_not_gt hx
      rw [max_eq_right (sub_nonpos.mpr hle), min_eq_left hle]
      ring
  · intro i
    filter_upwards [hPi i, Lp.coeFn_sub ((U : H1amb Ω) i.succ) ((P : H1amb Ω) i.succ)]
      with x hp hm
    simp only [Submodule.coe_sub, PiLp.sub_apply, Pi.sub_apply, hm, hp]
    split_ifs <;> ring

/-- The Dirichlet pairing of a function with its upper truncation is nonnegative. -/
theorem laplaceBilin_nonneg_of_upperTruncationGraph (U M : H01 Ω) (t : ℝ)
    (hMi : ∀ i : Fin d, ((M : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x =>
        if t < ((U : H1amb Ω) 0 x : ℝ) then 0
        else ((U : H1amb Ω) i.succ x : ℝ)) :
    0 ≤ laplaceBilin Ω U M := by
  rw [laplaceBilin_apply]
  apply Finset.sum_nonneg
  intro i _
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [hMi i] with x hx
  rw [hx]
  split_ifs <;> simp [sq_nonneg]

/-- The negative-part test has exactly the opposite Dirichlet energy:
`B(U, (-U-t)⁺) = -B((-U-t)⁺, (-U-t)⁺)`. -/
theorem laplaceBilin_shiftedNegativePart_identity (U P : H01 Ω) (t : ℝ)
    (hPi : ∀ i : Fin d, ((P : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x =>
        if t < (((-U : H01 Ω) : H1amb Ω) 0 x : ℝ)
        then (((-U : H01 Ω) : H1amb Ω) i.succ x : ℝ) else 0) :
    laplaceBilin Ω U P = -laplaceBilin Ω P P := by
  rw [laplaceBilin_apply, laplaceBilin_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def, L2.inner_def, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hPi i, Lp.coeFn_neg ((U : H1amb Ω) i.succ)] with x hp hn
  simp only [Submodule.coe_neg, PiLp.neg_apply, hn] at hp
  rw [hp]
  split_ifs <;> simp [pow_two]

/-- Testing an obstacle variational inequality with `(u-t)⁺` makes the source
nonnegative on `min(u,t)`. This is the Hilbert-space step in the contact mass bound. -/
theorem source_nonneg_of_upperTruncation_variational
    (ℓ : H01 Ω →L[ℝ] ℝ) (U M : H01 Ω) (t : ℝ)
    (hMi : ∀ i : Fin d, ((M : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x =>
        if t < ((U : H1amb Ω) 0 x : ℝ) then 0
        else ((U : H1amb Ω) i.succ x : ℝ))
    (hVI : ℓ ((U - M) - U) ≤ laplaceBilin Ω U ((U - M) - U)) :
    0 ≤ ℓ M := by
  have hB := laplaceBilin_nonneg_of_upperTruncationGraph U M t hMi
  have hVeq : (U - M) - U = -M := by abel
  rw [hVeq] at hVI
  simp only [map_neg] at hVI
  linarith

end CenteredMaximal.Ball.DirichletSobolev
