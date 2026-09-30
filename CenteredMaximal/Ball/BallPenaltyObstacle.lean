/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.BallPenaltyVariational
public import CenteredMaximal.Ball.BallDensityExtension

/-!
# A capped obstacle from penalized ball equations

The weak limit of uniformly bounded capped penalties is nonnegative, solves the ball obstacle
variational inequality, carries a capped `L²` density, and satisfies the contact-mass bound.
-/

@[expose] public section

noncomputable section

set_option maxHeartbeats 800000

open InnerProductSpace MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace NNReal ENNReal

namespace CenteredMaximal.Ball.DirichletSobolev

variable {n : ℕ}

/-- The penalized construction supplies one obstacle with a capped weak density and the exact
contact-mass estimate. -/
theorem exists_ball_penalty_obstacle_with_density
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : L2D (ball center R)) (κ : ℝ) (hκ : 0 ≤ κ) (hf : 0 ≤ f) :
    ∃ U : H01 (ball center R), ∃ ν : L2D (ball center R),
      0 ≤ valueEmbedding (ball center R) U ∧
      (0 ≤ ν ∧ ν ≤ κ • ballUnitL2 center R) ∧
      (∀ V : H01 (ball center R),
        laplaceBilin (ball center R) U V =
          l2Functional (ball center R) f V -
            κ * l2Functional (ball center R) (ballUnitL2 center R) V +
            ⟪ν, valueEmbedding (ball center R) V⟫_ℝ) ∧
      (∀ V : H01 (ball center R),
        0 ≤ valueEmbedding (ball center R) V →
        (l2Functional (ball center R) f -
          κ • l2Functional (ball center R) (ballUnitL2 center R)) (V - U) ≤
          laplaceBilin (ball center R) U (V - U)) ∧
      ENNReal.ofReal κ *
        (volume.restrict (ball center R))
          {x | 0 < ((U : H1amb (ball center R)) 0 x : ℝ)} ≤
        ∫⁻ x in ball center R, ‖(f x : ℝ)‖ₑ := by
  have hfAE : ∀ᵐ x ∂(volume.restrict (ball center R)), 0 ≤ (f x : ℝ) :=
    (Lp.coeFn_nonneg f).2 hf
  obtain ⟨C, Uk, hbound, heq, hcap⟩ :=
    exists_ball_penalized_sequence center R f κ hκ hfAE
  obtain ⟨U, ν, χ, hν, hχ, hweak, -, hlimEq⟩ :=
    ball_penalized_weak_limit_of_sequence center R f κ Uk C hbound heq hcap
  have hneg := ball_penalty_negPart_tendsto_zero center R Uk κ hcap χ hχ
  have hU : 0 ≤ valueEmbedding (ball center R) U :=
    nonneg_of_weak_limit_and_negPart_tendsto_zero
      (valueEmbedding (ball center R)) Uk U χ hweak hneg
  have hVI := ball_penalized_weak_limit_variational center R f κ Uk U χ hweak heq
  have hcontact := ball_obstacle_contact_bound_of_variational
    center R f κ hκ hf U hU hVI
  exact ⟨U, ν, hU, hν, hlimEq, hVI, hcontact⟩

/-- The capped obstacle density extends by zero to a whole-space density with the contact
mass and cap required by the maximal-function transfer. -/
theorem exists_ball_penalty_wholeSpace_density
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : L2D (ball center R)) (κ : ℝ) (hκ : 0 ≤ κ) (hf : 0 ≤ f) :
    ∃ U : H01 (ball center R), ∃ νlocal : L2D (ball center R),
      ∃ Ω : Set (EuclideanSpace ℝ (Fin (n + 1))),
      ∃ ν : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞,
        Ω = {x | x ∈ ball center R ∧
          0 < ((U : H1amb (ball center R)) 0 x : ℝ)} ∧
        ν = extendRestrictedDensity (ball center R) νlocal ∧
        ENNReal.ofReal κ * volume Ω ≤ ∫⁻ x, ‖(f x : ℝ)‖ₑ ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
          ν x ≤ ENNReal.ofReal κ) ∧
        0 ≤ valueEmbedding (ball center R) U ∧
        (∀ V : H01 (ball center R),
          laplaceBilin (ball center R) U V =
            l2Functional (ball center R) f V -
              κ * l2Functional (ball center R) (ballUnitL2 center R) V +
              ⟪νlocal, valueEmbedding (ball center R) V⟫_ℝ) := by
  obtain ⟨U, νlocal, hU, hνlocal, hweak, -, hcontact⟩ :=
    exists_ball_penalty_obstacle_with_density center R f κ hκ hf
  let D := ball center R
  let Ω : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {x | x ∈ D ∧ 0 < ((U : H1amb D) 0 x : ℝ)}
  let ν := extendRestrictedDensity D νlocal
  have hcontactGlobal : ENNReal.ofReal κ * volume Ω ≤
      ∫⁻ x, ‖(f x : ℝ)‖ₑ :=
    global_contact_bound_of_restricted volume D measurableSet_ball
      (fun x => ((U : H1amb D) 0 x : ℝ))
      (fun x => ‖(f x : ℝ)‖ₑ) (ENNReal.ofReal κ) hcontact
  have hcapGlobal : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      ν x ≤ ENNReal.ofReal κ :=
    ae_ballDensityExtension_le_cap center R νlocal κ hνlocal.2
  exact ⟨U, νlocal, Ω, ν, rfl, rfl, hcontactGlobal, hcapGlobal, hU, hweak⟩

/-- The global contact-mass bound can use an ordinary whole-space source whose restriction
agrees almost everywhere with the local `L²` source. -/
theorem exists_ball_penalty_wholeSpace_density_of_ae_eq
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (F : L2D (ball center R))
    (hF : (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      =ᵐ[volume.restrict (ball center R)] f)
    (κ : ℝ) (hκ : 0 ≤ κ) (hF0 : 0 ≤ F) :
    ∃ U : H01 (ball center R), ∃ νlocal : L2D (ball center R),
      ∃ Ω : Set (EuclideanSpace ℝ (Fin (n + 1))),
      ∃ ν : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞,
        Ω = {x | x ∈ ball center R ∧
          0 < ((U : H1amb (ball center R)) 0 x : ℝ)} ∧
        ν = extendRestrictedDensity (ball center R) νlocal ∧
        ENNReal.ofReal κ * volume Ω ≤ ∫⁻ x, ‖f x‖ₑ ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
          ν x ≤ ENNReal.ofReal κ) ∧
        0 ≤ valueEmbedding (ball center R) U ∧
        (∀ V : H01 (ball center R),
          laplaceBilin (ball center R) U V =
            l2Functional (ball center R) F V -
              κ * l2Functional (ball center R) (ballUnitL2 center R) V +
              ⟪νlocal, valueEmbedding (ball center R) V⟫_ℝ) := by
  obtain ⟨U, νlocal, hU, hνlocal, hweak, -, hcontact⟩ :=
    exists_ball_penalty_obstacle_with_density center R F κ hκ hF0
  let D := ball center R
  let Ω : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {x | x ∈ D ∧ 0 < ((U : H1amb D) 0 x : ℝ)}
  let ν := extendRestrictedDensity D νlocal
  have hcontact' : ENNReal.ofReal κ * (volume.restrict D)
      {x | 0 < ((U : H1amb D) 0 x : ℝ)} ≤
      ∫⁻ x in D, ‖f x‖ₑ := by
    convert hcontact using 1
    apply lintegral_congr_ae
    filter_upwards [hF] with x hx
    rw [hx]
  have hcontactGlobal : ENNReal.ofReal κ * volume Ω ≤ ∫⁻ x, ‖f x‖ₑ :=
    global_contact_bound_of_restricted volume D measurableSet_ball
      (fun x => ((U : H1amb D) 0 x : ℝ))
      (fun x => ‖f x‖ₑ) (ENNReal.ofReal κ) hcontact'
  have hcapGlobal : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      ν x ≤ ENNReal.ofReal κ :=
    ae_ballDensityExtension_le_cap center R νlocal κ hνlocal.2
  exact ⟨U, νlocal, Ω, ν, rfl, rfl, hcontactGlobal, hcapGlobal, hU, hweak⟩

end CenteredMaximal.Ball.DirichletSobolev
