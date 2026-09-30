/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.DirichletShiftedPart
public import CenteredMaximal.Ball.ContactTruncation
public import CenteredMaximal.Ball.ObstacleExistence
public import Mathlib.Tactic

/-!
# Contact mass bound for the ball obstacle

The zero-boundary Sobolev upper truncation tests the ball obstacle variational inequality.
Its Dirichlet pairing is nonnegative, so the source is nonnegative on every upper
truncation. The contact-set limiting argument then bounds the volume of the obstacle's
positive set by the mass of the input density.
-/

@[expose] public section
open MeasureTheory Set Filter Topology Metric
open scoped RealInnerProductSpace ENNReal NNReal
noncomputable section
namespace CenteredMaximal.Ball.DirichletSobolev
variable {n : ℕ}

/-- The obstacle variational inequality tested with `(u-t)⁺` gives the integral
inequality for the capped mass estimate. -/
theorem ball_obstacle_truncation_variation
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : L2D (ball center R)) (κ : ℝ)
    (hf : 0 ≤ f)
    (U : H01 (ball center R))
    (hU : 0 ≤ (U : H1amb (ball center R)) 0)
    (hVI : ∀ V : H01 (ball center R),
      0 ≤ (V : H1amb (ball center R)) 0 →
        (l2Functional (ball center R) f -
          κ • l2Functional (ball center R) (ballUnitL2 center R)) (V - U) ≤
          laplaceBilin (ball center R) U (V - U))
    (t : ℝ) (ht : 0 < t) :
    κ * ∫ x in ball center R,
      min (max ((U : H1amb (ball center R)) 0 x : ℝ) 0) t ≤
    ∫ x in ball center R,
      max (f x : ℝ) 0 *
        min (max ((U : H1amb (ball center R)) 0 x : ℝ) 0) t := by
  let D := ball center R
  let ℓ : H01 D →L[ℝ] ℝ :=
    l2Functional D f - κ • l2Functional D (ballUnitL2 center R)
  obtain ⟨M, hM0, hMi⟩ := exists_upperTruncationGraph U t ht.le
  let P := U - M
  have hP0 : ((P : H1amb D) 0 : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      =ᵐ[volume.restrict D] fun x =>
        max (((U : H1amb D) 0 x : ℝ) - t) 0 := by
    filter_upwards [hM0, Lp.coeFn_sub ((U : H1amb D) 0) ((M : H1amb D) 0)]
      with x hm hp
    simp only [P, Submodule.coe_sub, PiLp.sub_apply, Pi.sub_apply, hp, hm]
    by_cases hx : t < ((U : H1amb D) 0 x : ℝ)
    · rw [min_eq_right hx.le, max_eq_left (sub_nonneg.mpr hx.le)]
    · have hle := le_of_not_gt hx
      rw [min_eq_left hle, max_eq_right (sub_nonpos.mpr hle)]
      ring
  have hPpositive : 0 ≤ (P : H1amb D) 0 := by
    rw [← Lp.coeFn_nonneg]
    filter_upwards [hP0] with x hp
    rw [hp]
    exact le_max_right _ _
  have hVIp := hVI P hPpositive
  change ℓ (P - U) ≤ laplaceBilin D U (P - U) at hVIp
  have hsource := source_nonneg_of_upperTruncation_variational ℓ U M t hMi hVIp
  change 0 ≤ l2Functional D f M - κ * l2Functional D (ballUnitL2 center R) M
    at hsource
  rw [l2Functional_eq_integral, ballMassFunctional_apply] at hsource
  have huAE : ((U : H1amb D) 0 : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      =ᵐ[volume.restrict D] fun x => max ((U : H1amb D) 0 x : ℝ) 0 := by
    filter_upwards [(Lp.coeFn_nonneg ((U : H1amb D) 0)).2 hU] with x hx
    exact (max_eq_left hx).symm
  have hfAE : (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      =ᵐ[volume.restrict D] fun x => max (f x : ℝ) 0 := by
    filter_upwards [(Lp.coeFn_nonneg f).2 hf] with x hx
    exact (max_eq_left hx).symm
  have hMtr : ((M : H1amb D) 0 : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      =ᵐ[volume.restrict D] fun x => min (max ((U : H1amb D) 0 x : ℝ) 0) t := by
    filter_upwards [hM0, huAE] with x hm hu
    rw [hm, ← hu]
  have hint1 : (∫ x in D, (f x : ℝ) * ((M : H1amb D) 0 x : ℝ)) =
      ∫ x in D, max (f x : ℝ) 0 * min (max ((U : H1amb D) 0 x : ℝ) 0) t := by
    apply integral_congr_ae
    filter_upwards [hfAE, hMtr] with x hf' hm
    rw [← hf', ← hm]
  have hint2 : (∫ x in D, ((M : H1amb D) 0 x : ℝ)) =
      ∫ x in D, min (max ((U : H1amb D) 0 x : ℝ) 0) t :=
    integral_congr_ae hMtr
  rw [hint1, hint2] at hsource
  linarith

/-- Every nonnegative solution of the ball obstacle variational inequality has a
contact set whose κ-weighted volume is bounded by the input mass. -/
theorem ball_obstacle_contact_bound_of_variational
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : L2D (ball center R)) (κ : ℝ) (hκ : 0 ≤ κ) (hf : 0 ≤ f)
    (U : H01 (ball center R))
    (hU : 0 ≤ (U : H1amb (ball center R)) 0)
    (hVI : ∀ V : H01 (ball center R),
      0 ≤ (V : H1amb (ball center R)) 0 →
        (l2Functional (ball center R) f -
          κ • l2Functional (ball center R) (ballUnitL2 center R)) (V - U) ≤
          laplaceBilin (ball center R) U (V - U)) :
    ENNReal.ofReal κ *
      (volume.restrict (ball center R))
        {x | 0 < ((U : H1amb (ball center R)) 0 x : ℝ)} ≤
      ∫⁻ x in ball center R, ‖(f x : ℝ)‖ₑ := by
  let D := ball center R
  letI : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
    fun x => max ((U : H1amb D) 0 x : ℝ) 0
  let fpos : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun x => max (f x : ℝ) 0
  have hu_meas : Measurable u := by fun_prop
  have hfAE : (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) =ᵐ[volume.restrict D] fpos := by
    filter_upwards [(Lp.coeFn_nonneg f).2 hf] with x hx
    exact (max_eq_left hx).symm
  have hf_int : Integrable fpos (volume.restrict D) := by
    apply ((Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).congr hfAE
  have hcontact := contact_measure_le_lintegral_of_variational_truncations
    (volume.restrict D) u fpos (ENNReal.ofReal κ) (by simp) hu_meas
    (fun x => le_max_right _ _) hf_int (fun x => le_max_right _ _) ?_
  ·
    have hset : {x | 0 < u x} =
        {x | 0 < ((U : H1amb D) 0 x : ℝ)} := by
      ext x
      simp [u]
    have hlin : (∫⁻ x in D, ‖fpos x‖ₑ) = (∫⁻ x in D, ‖(f x : ℝ)‖ₑ) := by
      apply lintegral_congr_ae
      filter_upwards [hfAE] with x hx
      rw [← hx]
    simpa only [hset, hlin] using hcontact
  · intro t ht
    simpa only [u, fpos, ENNReal.toReal_ofReal hκ] using
      ball_obstacle_truncation_variation center R f κ hf U hU hVI t ht

/-- The ball obstacle variational problem has a solution satisfying the direct
contact-set mass bound. -/
theorem exists_ball_obstacle_contact_bound
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : L2D (ball center R)) (κ : ℝ) (hκ : 0 ≤ κ) (hf : 0 ≤ f) :
    ∃ U : H01 (ball center R),
      0 ≤ (U : H1amb (ball center R)) 0 ∧
      ENNReal.ofReal κ *
        (volume.restrict (ball center R))
          {x | 0 < ((U : H1amb (ball center R)) 0 x : ℝ)} ≤
        ∫⁻ x in ball center R, ‖(f x : ℝ)‖ₑ := by
  obtain ⟨U, hU, hVI⟩ := exists_ball_obstacle_variational center R f κ
  exact ⟨U, hU, ball_obstacle_contact_bound_of_variational center R f κ hκ hf U hU hVI⟩

end CenteredMaximal.Ball.DirichletSobolev
