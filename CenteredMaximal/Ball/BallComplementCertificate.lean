/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.BallSmoothObstacle
public import CenteredMaximal.Ball.LocalDistributionAdapter

/-!
# Complement density for the ball obstacle certificate

The penalty density in the weak equation has the opposite sign from the density used in the
Green-kernel comparison. Subtracting it from the cap produces the correct nonnegative density.
-/

@[expose] public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace NNReal ENNReal

namespace CenteredMaximal.Ball.DirichletSobolev

variable {n : ℕ}

/-- The nonnegative density appearing with a negative sign in the weak equation. -/
def ballComplementDensity
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R κ : ℝ)
    (νpen : L2D (ball center R)) : L2D (ball center R) :=
  κ • ballUnitL2 center R - νpen

/-- A capped penalty density gives a capped complement density. -/
theorem ballComplementDensity_nonneg_le_cap
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R κ : ℝ)
    (νpen : L2D (ball center R))
    (hν : 0 ≤ νpen ∧ νpen ≤ κ • ballUnitL2 center R) :
    0 ≤ ballComplementDensity center R κ νpen ∧
      ballComplementDensity center R κ νpen ≤ κ • ballUnitL2 center R := by
  constructor
  · exact sub_nonneg.mpr hν.2
  · exact sub_le_self _ hν.1

/-- In the weak equation, the cap minus the penalty is the source subtracted from `f`. -/
theorem ball_weak_equation_complement
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R κ : ℝ)
    (F νpen : L2D (ball center R)) (U : H01 (ball center R))
    (hweak : ∀ V : H01 (ball center R),
      laplaceBilin (ball center R) U V =
        l2Functional (ball center R) F V -
          κ * l2Functional (ball center R) (ballUnitL2 center R) V +
          ⟪νpen, valueEmbedding (ball center R) V⟫_ℝ) :
    ∀ V : H01 (ball center R),
      laplaceBilin (ball center R) U V =
        l2Functional (ball center R) F V -
          l2Functional (ball center R) (ballComplementDensity center R κ νpen) V := by
  intro V
  rw [hweak V]
  simp only [ballComplementDensity, l2Functional_apply, valueEmbedding_apply,
    inner_sub_left, real_inner_smul_left]
  ring

/-- The corrected local distributional Laplacian is the complement density minus the source. -/
theorem ballComplement_hasLocalDistributionalLaplacian
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R κ : ℝ)
    (F νpen : L2D (ball center R)) (U : H01 (ball center R))
    (hweak : ∀ V : H01 (ball center R),
      laplaceBilin (ball center R) U V =
        l2Functional (ball center R) F V -
          κ * l2Functional (ball center R) (ballUnitL2 center R) V +
          ⟪νpen, valueEmbedding (ball center R) V⟫_ℝ) :
    HasLocalDistributionalLaplacian (n + 1) (ball center R)
      (fun x ↦ ((U : H1amb (ball center R)) 0 x : ℝ))
      (fun x ↦ -((F - ballComplementDensity center R κ νpen) x : ℝ)) := by
  have h := ball_obstacle_hasLocalDistributionalLaplacian center R U F νpen κ hweak
  have hl2 : F - κ • ballUnitL2 center R + νpen =
      F - ballComplementDensity center R κ νpen := by
    unfold ballComplementDensity
    abel
  simpa only [hl2] using h

/-- The nonnegative representative of the obstacle obeys the corrected local equation. -/
theorem ballComplement_positiveRepresentative_hasLocalDistributionalLaplacian
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R κ : ℝ)
    (F νpen : L2D (ball center R)) (U : H01 (ball center R))
    (hU : 0 ≤ (U : H1amb (ball center R)) 0)
    (hweak : ∀ V : H01 (ball center R),
      laplaceBilin (ball center R) U V =
        l2Functional (ball center R) F V -
          κ * l2Functional (ball center R) (ballUnitL2 center R) V +
          ⟪νpen, valueEmbedding (ball center R) V⟫_ℝ) :
    HasLocalDistributionalLaplacian (n + 1) (ball center R)
      (ballPositiveRepresentative center R U)
      (fun x ↦ -((F - ballComplementDensity center R κ νpen) x : ℝ)) := by
  have h := ballPositiveRepresentative_hasLocalDistributionalLaplacian
    center R U hU F νpen κ hweak
  have hl2 : F - κ • ballUnitL2 center R + νpen =
      F - ballComplementDensity center R κ νpen := by
    unfold ballComplementDensity
    abel
  simpa only [hl2] using h

/-- The obstacle and its capped complementary density, for a local `L²` source. -/
theorem exists_ball_penalty_complement_certificate
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (F : L2D (ball center R))
    (hF : (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
      =ᵐ[volume.restrict (ball center R)] f)
    (κ : ℝ) (hκ : 0 ≤ κ) (hF0 : 0 ≤ F) :
    ∃ U : H01 (ball center R), ∃ νpen ρlocal : L2D (ball center R),
      ∃ Ω : Set (EuclideanSpace ℝ (Fin (n + 1))),
      ∃ ρ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞,
        ρlocal = ballComplementDensity center R κ νpen ∧
        Ω = {x | x ∈ ball center R ∧
          0 < ((U : H1amb (ball center R)) 0 x : ℝ)} ∧
        ρ = extendRestrictedDensity (ball center R) ρlocal ∧
        ENNReal.ofReal κ * volume Ω ≤ ∫⁻ x, ‖f x‖ₑ ∧
        (0 ≤ ρlocal ∧ ρlocal ≤ κ • ballUnitL2 center R) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
          ρ x ≤ ENNReal.ofReal κ) ∧
        0 ≤ valueEmbedding (ball center R) U ∧
        (∀ V : H01 (ball center R),
          laplaceBilin (ball center R) U V =
            l2Functional (ball center R) F V -
              l2Functional (ball center R) ρlocal V) := by
  obtain ⟨U, νpen, hU, hνpen, hweak, -, hcontact⟩ :=
    exists_ball_penalty_obstacle_with_density center R F κ hκ hF0
  let D := ball center R
  let ρlocal := ballComplementDensity center R κ νpen
  let Ω : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {x | x ∈ D ∧ 0 < ((U : H1amb D) 0 x : ℝ)}
  let ρ := extendRestrictedDensity D ρlocal
  have hρlocal : 0 ≤ ρlocal ∧ ρlocal ≤ κ • ballUnitL2 center R :=
    ballComplementDensity_nonneg_le_cap center R κ νpen hνpen
  have hcontact' : ENNReal.ofReal κ * (volume.restrict D)
      {x | 0 < ((U : H1amb D) 0 x : ℝ)} ≤
      ∫⁻ x in D, ‖f x‖ₑ := by
    convert hcontact using 1
    apply lintegral_congr_ae
    filter_upwards [hF] with x hx
    rw [hx]
  have hcontactGlobal : ENNReal.ofReal κ * volume Ω ≤
      ∫⁻ x, ‖f x‖ₑ :=
    global_contact_bound_of_restricted volume D measurableSet_ball
      (fun x => ((U : H1amb D) 0 x : ℝ))
      (fun x => ‖f x‖ₑ) (ENNReal.ofReal κ) hcontact'
  have hcapGlobal : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      ρ x ≤ ENNReal.ofReal κ :=
    ae_ballDensityExtension_le_cap center R ρlocal κ hρlocal.2
  exact ⟨U, νpen, ρlocal, Ω, ρ, rfl, rfl, rfl, hcontactGlobal,
    hρlocal, hcapGlobal, hU,
    ball_weak_equation_complement center R κ F νpen U hweak⟩

/-- The corrected complementary certificate for a smooth compactly supported source. -/
theorem exists_ball_smooth_complement_certificate
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hfcont : Continuous f) (hfcomp : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ U : H01 (ball center R), ∃ νpen ρlocal : L2D (ball center R),
      ∃ Ω : Set (EuclideanSpace ℝ (Fin (n + 1))),
      ∃ ρ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞,
        ρlocal = ballComplementDensity center R κ νpen ∧
        Ω = {x | x ∈ ball center R ∧
          0 < ((U : H1amb (ball center R)) 0 x : ℝ)} ∧
        ρ = extendRestrictedDensity (ball center R) ρlocal ∧
        ENNReal.ofReal κ * volume Ω ≤ ∫⁻ x, ‖f x‖ₑ ∧
        (0 ≤ ρlocal ∧ ρlocal ≤ κ • ballUnitL2 center R) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
          ρ x ≤ ENNReal.ofReal κ) ∧
        0 ≤ valueEmbedding (ball center R) U ∧
        (∀ V : H01 (ball center R),
          laplaceBilin (ball center R) U V =
            l2Functional (ball center R)
              (ballSourceL2 center R f hfcont hfcomp) V -
              l2Functional (ball center R) ρlocal V) := by
  let F := ballSourceL2 center R f hfcont hfcomp
  have hF0 : 0 ≤ F := by
    rw [← Lp.coeFn_nonneg]
    filter_upwards [ballSourceL2_coeFn center R f hfcont hfcomp] with x hx
    rw [hx]
    exact hf0 x
  obtain ⟨U, νpen, ρlocal, Ω, ρ, hρdef, hΩ, hρext, hcontact,
    hρlocal, hcap, hU, hweak⟩ :=
    exists_ball_penalty_complement_certificate center R f F
      (ballSourceL2_coeFn center R f hfcont hfcomp) κ hκ hF0
  exact ⟨U, νpen, ρlocal, Ω, ρ, hρdef, hΩ, hρext,
    hcontact, hρlocal, hcap, hU, hweak⟩

end CenteredMaximal.Ball.DirichletSobolev
