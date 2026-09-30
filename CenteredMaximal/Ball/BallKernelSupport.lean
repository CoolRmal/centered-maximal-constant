/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.LocalWeakPairing

/-!
# One cutoff for all relevant Green kernels

For centers in the region considered by the maximal-function transfer and radii below its
threshold, every truncated Green kernel is supported in a fixed interior ball. A single
smooth cutoff equals one there and has closed support strictly inside a larger Dirichlet ball.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace CenteredMaximal.Ball

/-- Radius on which the common Green cutoff is one. -/
def greenCutoffInnerRadius (R r₀ G : ℝ) : ℝ := max R 0 + (G + 1) * r₀

/-- The fixed Dirichlet domain containing the cutoff's closed support. -/
def greenCutoffDomain (n : ℕ) (R r₀ G : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  ball 0 (greenCutoffInnerRadius R r₀ G + 2 * r₀)

/-- A larger Dirichlet ball with two units of room around the common cutoff domain. -/
def greenObstacleDomain (n : ℕ) (R r₀ G : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  ball 0 (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2)

/-- Points in the closure of the common cutoff domain stay within its closed radius. -/
theorem norm_le_of_mem_closure_greenCutoffDomain (n : ℕ) (R r₀ G : ℝ)
    (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ closure (greenCutoffDomain n R r₀ G)) :
    ‖y‖ ≤ greenCutoffInnerRadius R r₀ G + 2 * r₀ := by
  have hclosed : closure (greenCutoffDomain n R r₀ G) ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin n))
        (greenCutoffInnerRadius R r₀ G + 2 * r₀) := by
    apply closure_minimal
    · exact ball_subset_closedBall
    · exact isClosed_closedBall
  simpa only [mem_closedBall, dist_zero_right] using hclosed hy

/-- A whole closed unit ball around every point in the closure of the cutoff domain remains
inside the larger obstacle domain. -/
theorem closedBall_subset_greenObstacleDomain_of_mem_closure (n : ℕ)
    (R r₀ G : ℝ) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ closure (greenCutoffDomain n R r₀ G)) :
    closedBall y 1 ⊆ greenObstacleDomain n R r₀ G := by
  intro z hz
  have hyNorm := norm_le_of_mem_closure_greenCutoffDomain n R r₀ G y hy
  have hzNorm : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by
    convert norm_add_le (z - y) y using 1; simp
  have hzy : ‖z - y‖ ≤ 1 := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  change z ∈ ball (0 : EuclideanSpace ℝ (Fin n))
    (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2)
  simpa only [mem_ball, dist_zero_right] using
    (by linarith : ‖z‖ < greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2)

/-- The cutoff domain has closure strictly inside the larger obstacle ball. -/
theorem closure_greenCutoffDomain_subset_greenObstacleDomain (n : ℕ)
    (R r₀ G : ℝ) :
    closure (greenCutoffDomain n R r₀ G) ⊆
      greenObstacleDomain n R r₀ G := by
  intro y hy
  exact closedBall_subset_greenObstacleDomain_of_mem_closure n R r₀ G y hy
    (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1))

/-- A single smooth cutoff for all centers and radii in the transfer region. -/
def greenCutoff (n : ℕ) (R r₀ G : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  smoothBallCutoff n 0 (greenCutoffInnerRadius R r₀ G) r₀

theorem greenCutoffInnerRadius_pos {R r₀ G : ℝ}
    (hr₀ : 0 < r₀) (hG : 0 ≤ G) :
    0 < greenCutoffInnerRadius R r₀ G := by
  unfold greenCutoffInnerRadius
  have hmax : 0 ≤ max R 0 := le_max_right R 0
  have hG1 : 0 < G + 1 := by linarith
  nlinarith [mul_pos hG1 hr₀]

/-- Every scaled Green support ball in the transfer range lies in the common cutoff's
unit region. -/
theorem scaled_ball_subset_greenCutoff_inner (n : ℕ)
    {R r₀ G : ℝ} (_hr₀ : 0 < r₀) (hG : 0 ≤ G)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ < R + r₀)
    {r : ℝ} (_hr : 0 < r) (hrr₀ : r < r₀)
    (y : EuclideanSpace ℝ (Fin n))
    (hy : ‖y - x‖ < r * G) :
    y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (greenCutoffInnerRadius R r₀ G) := by
  have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    convert norm_add_le (y - x) x using 1; simp
  have hrg : r * G ≤ r₀ * G := mul_le_mul_of_nonneg_right hrr₀.le hG
  have hR : R ≤ max R 0 := le_max_left R 0
  simp only [mem_ball, dist_zero_right, greenCutoffInnerRadius]
  linarith

/-- The common cutoff equals one throughout each scaled support ball. -/
theorem greenCutoff_eq_one_of_scaled_ball (n : ℕ)
    {R r₀ G : ℝ} (hr₀ : 0 < r₀) (hG : 0 ≤ G)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ < R + r₀)
    {r : ℝ} (hr : 0 < r) (hrr₀ : r < r₀)
    (y : EuclideanSpace ℝ (Fin n))
    (hy : ‖y - x‖ < r * G) :
    greenCutoff n R r₀ G y = 1 := by
  have hI := greenCutoffInnerRadius_pos (R := R) hr₀ hG
  have hyI := scaled_ball_subset_greenCutoff_inner n hr₀ hG x hx hr hrr₀ y hy
  exact smoothBallCutoff_one n 0 y hI hr₀ (ball_subset_closedBall hyI)

/-- The closed support of the common smooth cutoff lies strictly inside the fixed Dirichlet
ball. -/
theorem greenCutoff_tsupport_subset_domain (n : ℕ)
    {R r₀ G : ℝ} (hr₀ : 0 < r₀) (hG : 0 ≤ G) :
    tsupport (greenCutoff n R r₀ G) ⊆ greenCutoffDomain n R r₀ G := by
  let I := greenCutoffInnerRadius R r₀ G
  have hI : 0 < I := greenCutoffInnerRadius_pos hr₀ hG
  have hsupp : Function.support (greenCutoff n R r₀ G) ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin n)) (I + r₀) := by
    intro y hy
    by_contra hball
    have hnorm : I + r₀ ≤ ‖y‖ := by
      exact le_of_lt (by simpa only [mem_closedBall, dist_zero_right, not_le] using hball)
    exact hy (smoothBallCutoff_zero n 0 y hI hr₀ (by simpa using hnorm))
  have hclosed : tsupport (greenCutoff n R r₀ G) ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin n)) (I + r₀) := by
    change closure (Function.support (greenCutoff n R r₀ G)) ⊆ _
    exact closure_minimal hsupp isClosed_closedBall
  intro y hy
  have hynorm : ‖y‖ ≤ I + r₀ := by
    simpa only [mem_closedBall, dist_zero_right] using hclosed hy
  change y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (I + 2 * r₀)
  simpa only [mem_ball, dist_zero_right] using (by linarith : ‖y‖ < I + 2 * r₀)

theorem greenCutoff_hasCompactSupport (n : ℕ)
    {R r₀ G : ℝ} (hr₀ : 0 < r₀) (hG : 0 ≤ G) :
    HasCompactSupport (greenCutoff n R r₀ G) := by
  exact smoothBallCutoff_hasCompactSupport n 0
    (greenCutoffInnerRadius_pos hr₀ hG) hr₀

theorem greenCutoff_contDiff (n : ℕ) (R r₀ G : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (greenCutoff n R r₀ G) :=
  smoothBallCutoff_contDiff_smooth n 0 _ _

theorem greenCutoff_norm_le_one (n : ℕ) (R r₀ G : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖greenCutoff n R r₀ G y‖ ≤ 1 :=
  smoothBallCutoff_norm_le_one n 0 _ _ y

/-- Any kernel supported in the radius-`G` ball is unchanged by the common cutoff after
normalization at every center and scale in the transfer range. -/
theorem normalized_kernel_mul_greenCutoff (n : ℕ)
    (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    {R r₀ G : ℝ} (hr₀ : 0 < r₀) (hG : 0 ≤ G)
    (hK : ∀ z, G ≤ ‖z‖ → K z = 0)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ < R + r₀)
    {r : ℝ} (hr : 0 < r) (hrr₀ : r < r₀)
    (y : EuclideanSpace ℝ (Fin n)) :
    ((volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))).toReal *
      greenCutoff n R r₀ G y =
        ((volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))).toReal := by
  by_cases hy : G ≤ ‖r⁻¹ • (x - y)‖
  · rw [hK _ hy]
    simp
  · have hscaled : ‖y - x‖ = r * ‖r⁻¹ • (x - y)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, norm_sub_rev]
      field_simp
    have hyball : ‖y - x‖ < r * G := by
      rw [hscaled]
      exact mul_lt_mul_of_pos_left (lt_of_not_ge hy) hr
    rw [greenCutoff_eq_one_of_scaled_ball n hr₀ hG x hx hr hrr₀ y hyball, mul_one]

/-- The planar logarithmic kernel is unchanged by the common cutoff. -/
theorem normalized_planarKernel_mul_greenCutoff
    {R r₀ : ℝ} (hr₀ : 0 < r₀)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : ‖x‖ < R + r₀)
    {r : ℝ} (hr : 0 < r) (hrr₀ : r < r₀)
    (y : EuclideanSpace ℝ (Fin 2)) :
    ((volume (ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal *
      greenCutoff 2 R r₀ planarGreenRadius y =
        ((volume (ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal := by
  have hG : 0 ≤ planarGreenRadius := by unfold planarGreenRadius; positivity
  exact normalized_kernel_mul_greenCutoff 2 planarKernel hr₀ hG
    planarKernel_eq_zero_of_radius_le x hx hr hrr₀ y

/-- The Newtonian kernel is unchanged by the common cutoff. -/
theorem normalized_newtonianKernel_mul_greenCutoff (n : ℕ) (hn : 3 ≤ n)
    {R r₀ : ℝ} (hr₀ : 0 < r₀)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ < R + r₀)
    {r : ℝ} (hr : 0 < r) (hrr₀ : r < r₀)
    (y : EuclideanSpace ℝ (Fin n)) :
    ((volume (ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal *
      greenCutoff n R r₀ (greenRadius n) y =
        ((volume (ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal := by
  exact normalized_kernel_mul_greenCutoff n (newtonianKernel n) hr₀
    (greenRadius_pos n hn).le (newtonianKernel_eq_zero_of_radius_le n hn)
    x hx hr hrr₀ y

end CenteredMaximal.Ball
