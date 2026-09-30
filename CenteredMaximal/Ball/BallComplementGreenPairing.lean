/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.BallPositiveMollifierPackage
public import CenteredMaximal.Ball.ComplementDistributionAdapter
public import CenteredMaximal.Ball.BallComplementSourceBound
public import CenteredMaximal.Ball.AEGreenFromMollifiers

/-!
# Green pairing for the weak ball obstacle

The positive representative of a weak Dirichlet obstacle can be mollified. The local
distributional equation controls the mollified Laplacians on a fixed region containing every
Green kernel in the maximal-function transfer range. The smooth Green identity then passes to
almost every center outside the contact set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace CenteredMaximal.Ball

open DirichletSobolev

/-- The weak obstacle yields one sequence of nonnegative mollifiers whose Laplacians are
uniformly bounded and converge on the common Green cutoff domain. -/
theorem exists_ballComplement_green_local_mollifiers
    (n : ℕ) (R r₀ G : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hfcont : Continuous f) (hfcomp : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (U : H01 (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
      (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2)))
    (ρlocal : L2D (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
      (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2)))
    (hU : 0 ≤ (U : H1amb
      (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
        (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2))) 0)
    (hρ : 0 ≤ ρlocal ∧ ρlocal ≤ κ •
      ballUnitL2 (0 : EuclideanSpace ℝ (Fin (n + 1)))
        (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2))
    (hweak : ∀ V : H01
      (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
        (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2)),
      laplaceBilin (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
        (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2)) U V =
        l2Functional (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
          (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2))
          (ballSourceL2 (0 : EuclideanSpace ℝ (Fin (n + 1)))
            (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2)
            f hfcont hfcomp - ρlocal) V) :
    ∃ (B : ℝ) (w : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ),
      (∀ k, ContDiff ℝ 2 (w k)) ∧
      (∀ k, HasCompactSupport (w k)) ∧
      (∀ k y, 0 ≤ w k y) ∧
      (∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
        Tendsto (fun k => w k y) atTop
          (𝓝 (ballPositiveRepresentative 0
            (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2) U y))) ∧
      (∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
        y ∈ greenCutoffDomain (n + 1) R r₀ G →
          ‖Laplacian.laplacian (w k) y‖ ≤ B) ∧
      (∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
        y ∈ greenCutoffDomain (n + 1) R r₀ G →
          Tendsto (fun k => Laplacian.laplacian (w k) y) atTop
            (𝓝 (ballComplementSourceExtension 0
              (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2)
              (ballSourceL2 0 (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2)
                f hfcont hfcomp) ρlocal y))) := by
  let S := greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2
  let F := ballSourceL2 (0 : EuclideanSpace ℝ (Fin (n + 1))) S f hfcont hfcomp
  let u := ballPositiveRepresentative (0 : EuclideanSpace ℝ (Fin (n + 1))) S U
  let g := ballComplementSourceExtension (0 : EuclideanSpace ℝ (Fin (n + 1))) S F ρlocal
  have hu : Integrable u := ballPositiveRepresentative_integrable 0 S U hU
  have hucomp : HasCompactSupport u := ballPositiveRepresentative_hasCompactSupport 0 S U
  have hu0 : ∀ y, 0 ≤ u y := ballPositiveRepresentative_nonneg 0 S U
  have hg : Integrable g := ballComplementSourceExtension_integrable 0 S F ρlocal
  have hlocal0 : HasLocalDistributionalLaplacian (n + 1) (ball 0 S) u
      (fun y => ((ρlocal - F) y : ℝ)) :=
    ballPositiveRepresentative_hasLocalDistributionalLaplacian_of_complement
      0 S U F ρlocal hU hweak
  have hlocal : HasLocalDistributionalLaplacian (n + 1)
      (greenObstacleDomain (n + 1) R r₀ G) u g := by
    apply hlocal0.congr_ae_restrict (ball 0 S) measurableSet_ball
      u (fun y => ((ρlocal - F) y : ℝ)) g
    exact (ballComplementSourceExtension_ae_eq_local 0 S F ρlocal).symm
  obtain ⟨B, -, -, hBg⟩ :=
    exists_bounded_ballComplementSourceExtension 0 S f hfcont hfcomp
      ρlocal κ hκ hρ
  obtain ⟨w, hwsmooth, hwcomp, hw0, hwlim, hwcap, hwΔlim⟩ :=
    exists_green_local_mollifiers (n + 1) R r₀ G u g
      hu hucomp hu0 hg hlocal B hBg
  exact ⟨B, w, hwsmooth, hwcomp, hw0, hwlim, hwcap, hwΔlim⟩

/-- The planar Green pairing with the zero-extended weak Laplacian is nonnegative for almost
every point outside the obstacle contact set. The exceptional set is independent of radius. -/
theorem ae_planar_ballComplement_green_pairing_nonneg
    (R r₀ : ℝ) (hr₀ : 0 < r₀)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hfcont : Continuous f) (hfcomp : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (U : H01 (ball (0 : EuclideanSpace ℝ (Fin 2))
      (greenCutoffInnerRadius R r₀ planarGreenRadius + 2 * r₀ + 2)))
    (ρlocal : L2D (ball (0 : EuclideanSpace ℝ (Fin 2))
      (greenCutoffInnerRadius R r₀ planarGreenRadius + 2 * r₀ + 2)))
    (hU : 0 ≤ (U : H1amb (ball (0 : EuclideanSpace ℝ (Fin 2))
      (greenCutoffInnerRadius R r₀ planarGreenRadius + 2 * r₀ + 2))) 0)
    (hρ : 0 ≤ ρlocal ∧ ρlocal ≤ κ • ballUnitL2 0
      (greenCutoffInnerRadius R r₀ planarGreenRadius + 2 * r₀ + 2))
    (hweak : ∀ V : H01 (ball (0 : EuclideanSpace ℝ (Fin 2))
      (greenCutoffInnerRadius R r₀ planarGreenRadius + 2 * r₀ + 2)),
      laplaceBilin (ball (0 : EuclideanSpace ℝ (Fin 2))
        (greenCutoffInnerRadius R r₀ planarGreenRadius + 2 * r₀ + 2)) U V =
      l2Functional (ball (0 : EuclideanSpace ℝ (Fin 2))
        (greenCutoffInnerRadius R r₀ planarGreenRadius + 2 * r₀ + 2))
        (ballSourceL2 0
          (greenCutoffInnerRadius R r₀ planarGreenRadius + 2 * r₀ + 2)
          f hfcont hfcomp - ρlocal) V) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      x ∉ {y | y ∈ ball 0
        (greenCutoffInnerRadius R r₀ planarGreenRadius + 2 * r₀ + 2) ∧
        0 < ((U : H1amb (ball (0 : EuclideanSpace ℝ (Fin 2))
          (greenCutoffInnerRadius R r₀ planarGreenRadius + 2 * r₀ + 2))) 0 y : ℝ)} →
      ‖x‖ < R + r₀ → ∀ r : ℝ, 0 < r → r < r₀ →
        0 ≤ (∫ y : EuclideanSpace ℝ (Fin 2),
          ((volume (ball x r))⁻¹ * planarKernel (r⁻¹ • (x-y))).toReal *
            ballComplementSourceExtension 0
              (greenCutoffInnerRadius R r₀ planarGreenRadius + 2 * r₀ + 2)
              (ballSourceL2 0
                (greenCutoffInnerRadius R r₀ planarGreenRadius + 2 * r₀ + 2)
                f hfcont hfcomp) ρlocal y) := by
  let S := greenCutoffInnerRadius R r₀ planarGreenRadius + 2 * r₀ + 2
  let F := ballSourceL2 (0 : EuclideanSpace ℝ (Fin 2)) S f hfcont hfcomp
  let u := ballPositiveRepresentative (0 : EuclideanSpace ℝ (Fin 2)) S U
  let g := ballComplementSourceExtension (0 : EuclideanSpace ℝ (Fin 2)) S F ρlocal
  let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
    {y | y ∈ ball 0 S ∧ 0 < ((U : H1amb (ball 0 S)) 0 y : ℝ)}
  obtain ⟨B, w, hwsmooth, hwcomp, hw0, hwlim, hwcap, hwΔlim⟩ :=
    exists_ballComplement_green_local_mollifiers 1 R r₀ planarGreenRadius
      f hfcont hfcomp κ hκ U ρlocal hU hρ hweak
  have hzero : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      x ∉ Ω → u x = 0 :=
    ae_of_all _ (fun x hx => ballPositiveRepresentative_eq_zero_of_not_contact
      0 S U x hx)
  exact ae_planar_green_pairing_nonneg_of_local_mollifiers R r₀ hr₀ Ω u g w
    hwsmooth hwcomp hw0 hwlim hzero B hwcap hwΔlim

/-- The Newtonian Green pairing with the zero-extended weak Laplacian is nonnegative for
almost every point outside the obstacle contact set, simultaneously at all transfer radii. -/
theorem ae_newtonian_ballComplement_green_pairing_nonneg
    (n : ℕ) (hn : 3 ≤ n + 1)
    (R r₀ : ℝ) (hr₀ : 0 < r₀)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hfcont : Continuous f) (hfcomp : HasCompactSupport f)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (U : H01 (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
      (greenCutoffInnerRadius R r₀ (greenRadius (n + 1)) + 2 * r₀ + 2)))
    (ρlocal : L2D (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
      (greenCutoffInnerRadius R r₀ (greenRadius (n + 1)) + 2 * r₀ + 2)))
    (hU : 0 ≤ (U : H1amb (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
      (greenCutoffInnerRadius R r₀ (greenRadius (n + 1)) + 2 * r₀ + 2))) 0)
    (hρ : 0 ≤ ρlocal ∧ ρlocal ≤ κ • ballUnitL2 0
      (greenCutoffInnerRadius R r₀ (greenRadius (n + 1)) + 2 * r₀ + 2))
    (hweak : ∀ V : H01 (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
      (greenCutoffInnerRadius R r₀ (greenRadius (n + 1)) + 2 * r₀ + 2)),
      laplaceBilin (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
        (greenCutoffInnerRadius R r₀ (greenRadius (n + 1)) + 2 * r₀ + 2)) U V =
      l2Functional (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
        (greenCutoffInnerRadius R r₀ (greenRadius (n + 1)) + 2 * r₀ + 2))
        (ballSourceL2 0
          (greenCutoffInnerRadius R r₀ (greenRadius (n + 1)) + 2 * r₀ + 2)
          f hfcont hfcomp - ρlocal) V) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      x ∉ {y | y ∈ ball 0
        (greenCutoffInnerRadius R r₀ (greenRadius (n + 1)) + 2 * r₀ + 2) ∧
        0 < ((U : H1amb (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
          (greenCutoffInnerRadius R r₀ (greenRadius (n + 1)) + 2 * r₀ + 2)))
            0 y : ℝ)} →
      ‖x‖ < R + r₀ → ∀ r : ℝ, 0 < r → r < r₀ →
        0 ≤ (∫ y : EuclideanSpace ℝ (Fin (n + 1)),
          ((volume (ball x r))⁻¹ *
              newtonianKernel (n + 1) (r⁻¹ • (x-y))).toReal *
            ballComplementSourceExtension 0
              (greenCutoffInnerRadius R r₀ (greenRadius (n + 1)) + 2 * r₀ + 2)
              (ballSourceL2 0
                (greenCutoffInnerRadius R r₀ (greenRadius (n + 1)) + 2 * r₀ + 2)
                f hfcont hfcomp) ρlocal y) := by
  let S := greenCutoffInnerRadius R r₀ (greenRadius (n + 1)) + 2 * r₀ + 2
  let F := ballSourceL2 (0 : EuclideanSpace ℝ (Fin (n + 1))) S f hfcont hfcomp
  let u := ballPositiveRepresentative (0 : EuclideanSpace ℝ (Fin (n + 1))) S U
  let g := ballComplementSourceExtension (0 : EuclideanSpace ℝ (Fin (n + 1))) S F ρlocal
  let Ω : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {y | y ∈ ball 0 S ∧ 0 < ((U : H1amb (ball 0 S)) 0 y : ℝ)}
  obtain ⟨B, w, hwsmooth, hwcomp, hw0, hwlim, hwcap, hwΔlim⟩ :=
    exists_ballComplement_green_local_mollifiers n R r₀ (greenRadius (n + 1))
      f hfcont hfcomp κ hκ U ρlocal hU hρ hweak
  have hzero : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      x ∉ Ω → u x = 0 :=
    ae_of_all _ (fun x hx => ballPositiveRepresentative_eq_zero_of_not_contact
      0 S U x hx)
  exact ae_newtonian_green_pairing_nonneg_of_local_mollifiers (n + 1) hn
    R r₀ hr₀ Ω u g w hwsmooth hwcomp hw0 hwlim hzero B hwcap hwΔlim

end CenteredMaximal.Ball
