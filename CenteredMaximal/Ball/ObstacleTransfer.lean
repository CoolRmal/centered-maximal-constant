/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.GreenKernel

/-!
# From a ball obstacle certificate to a weak type estimate

The analytic obstacle construction supplies a capped density `ν` and a contact set `Ω`. At a point
outside `Ω`, Green comparison bounds a ball average of `f` by the corresponding Green integral of
`ν`, provided the dilated Green kernel fits in the obstacle domain. The large-radius and
far-from-support cases complete the estimate at every radius.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace CenteredMaximal.Ball

variable {n : ℕ} [Nonempty (Fin n)]

omit [Nonempty (Fin n)] in
/-- Every normalized ball average is bounded by the normalized integral of a kernel which is at
least one on the unit ball. This is the single-radius version of
`ballMaximalFunction_le_kernelMaximal`. -/
theorem ball_average_le_kernel_integral
    {K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hK : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, 1 ≤ K z)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) :
    (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ ≤
      ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ := by
  calc
    (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ
        ≤ ∫⁻ y in ball x r, (volume (ball x r))⁻¹ * ‖f y‖ₑ :=
          lintegral_const_mul_le _ _
    _ ≤ ∫⁻ y in ball x r,
          (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ := by
      refine setLIntegral_mono' measurableSet_ball fun y hy ↦ ?_
      have hz : r⁻¹ • (x - y) ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr.le]
        have hxy : ‖x - y‖ < r := by rwa [mem_ball', dist_eq_norm] at hy
        calc
          r⁻¹ * ‖x - y‖ = ‖x - y‖ / r := by ring
          _ < 1 := (div_lt_one hr).2 hxy
      calc
        _ = (volume (ball x r))⁻¹ * 1 * ‖f y‖ₑ := by simp
        _ ≤ (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ := by
          gcongr
          exact hK _ hz
    _ ≤ ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ :=
      setLIntegral_le_lintegral _ _

omit [Nonempty (Fin n)] in
/-- An almost-everywhere bound for a density transfers through a nonnegative normalized kernel. -/
theorem kernel_integral_le_of_density_le_ae
    (K ν : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (x : EuclideanSpace ℝ (Fin n))
    (r : ℝ) (κ C : ℝ≥0∞) (hκfin : κ ≠ ∞)
    (hν : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ν y ≤ κ)
    (hKmass : (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))) = C) :
    (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ν y) ≤ C * κ := by
  calc
    (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ν y)
        ≤ ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * κ :=
          lintegral_mono_ae <| hν.mono fun y hy ↦ by
            simpa only [mul_comm] using
              (mul_le_mul_left hy ((volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))))
    _ = (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))) * κ := by
      rw [lintegral_mul_const' _ _ hκfin]
    _ = C * κ := by rw [hKmass]

omit [Nonempty (Fin n)] in
/-- Pointwise form of `kernel_integral_le_of_density_le_ae`. -/
theorem kernel_integral_le_of_density_le
    (K ν : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (x : EuclideanSpace ℝ (Fin n))
    (r : ℝ) (κ C : ℝ≥0∞) (hκfin : κ ≠ ∞) (hν : ∀ y, ν y ≤ κ)
    (hKmass : (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))) = C) :
    (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ν y) ≤ C * κ :=
  kernel_integral_le_of_density_le_ae K ν x r κ C hκfin (ae_of_all _ hν) hKmass

/-- A sufficiently large radius has a small average, using only the total mass of `f`. -/
theorem ball_average_le_of_large_radius
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    {r r₀ : ℝ} (hr₀ : 0 < r₀) (hrr₀ : r₀ ≤ r) {A : ℝ≥0∞}
    (hlarge : (∫⁻ y, ‖f y‖ₑ) ≤
      A * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r₀)) :
    (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ ≤ A := by
  have hvol : volume (ball (0 : EuclideanSpace ℝ (Fin n)) r₀) ≤ volume (ball x r) := by
    simp only [EuclideanSpace.volume_ball]
    gcongr
  have hvol₀ : volume (ball (0 : EuclideanSpace ℝ (Fin n)) r₀) ≠ 0 :=
    (measure_ball_pos volume 0 hr₀).ne'
  have hvol_top : volume (ball (0 : EuclideanSpace ℝ (Fin n)) r₀) ≠ ∞ :=
    measure_ball_lt_top.ne
  calc
    (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ
        ≤ (volume (ball x r))⁻¹ * ∫⁻ y, ‖f y‖ₑ :=
          by simpa only [mul_comm] using
            (mul_le_mul_left (setLIntegral_le_lintegral (ball x r) (fun y ↦ ‖f y‖ₑ))
              (volume (ball x r))⁻¹)
    _ ≤ (volume (ball (0 : EuclideanSpace ℝ (Fin n)) r₀))⁻¹ * ∫⁻ y, ‖f y‖ₑ :=
      mul_le_mul_left (ENNReal.inv_le_inv.mpr hvol) _
    _ ≤ (volume (ball (0 : EuclideanSpace ℝ (Fin n)) r₀))⁻¹ *
          (A * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r₀)) :=
            by simpa only [mul_comm] using
              (mul_le_mul_left hlarge (volume (ball (0 : EuclideanSpace ℝ (Fin n)) r₀))⁻¹)
    _ = A := by
      rw [mul_left_comm, ENNReal.inv_mul_cancel hvol₀ hvol_top, mul_one]

/-- An integrable function has a large enough ball whose volume, multiplied by any positive finite
constant, exceeds its total mass. This supplies the cutoff radius in the three-radius argument. -/
theorem exists_large_radius_for_mass
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Integrable f)
    (A : ℝ≥0∞) (hA₀ : 0 < A) (hAtop : A ≠ ∞) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      (∫⁻ y, ‖f y‖ₑ) ≤ A * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r₀) := by
  let V := volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hV₀ : V ≠ 0 := (measure_ball_pos volume 0 zero_lt_one).ne'
  have hVtop : V ≠ ∞ := measure_ball_lt_top.ne
  let D := A * V
  have hD₀ : D ≠ 0 := mul_ne_zero hA₀.ne' hV₀
  have hDtop : D ≠ ∞ := ENNReal.mul_ne_top hAtop hVtop
  have hFtop : (∫⁻ y, ‖f y‖ₑ) ≠ ∞ :=
    (hasFiniteIntegral_iff_enorm.1 hf.2).ne
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hFtop hD₀)
  let r₀ : ℝ := (m + 1 : ℕ)
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  have hn : n ≠ 0 := by
    obtain ⟨i⟩ := ‹Nonempty (Fin n)›
    exact Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  have hq : (∫⁻ y, ‖f y‖ₑ) / D ≤ (m + 1 : ℕ) :=
    hm.le.trans (by exact_mod_cast Nat.le_succ m)
  have hqpow : (∫⁻ y, ‖f y‖ₑ) / D ≤ ((m + 1 : ℕ) : ℝ≥0∞) ^ n :=
    hq.trans (le_self_pow₀ (by simp) hn)
  have hcast : ENNReal.ofReal r₀ = ((m + 1 : ℕ) : ℝ≥0∞) := by
    simpa only [r₀] using ENNReal.ofReal_natCast (m + 1)
  have hvol : volume (ball (0 : EuclideanSpace ℝ (Fin n)) r₀) =
      ((m + 1 : ℕ) : ℝ≥0∞) ^ n * V := by
    rw [EuclideanSpace.volume_ball, hcast]
    simp [V, EuclideanSpace.volume_ball]
  refine ⟨r₀, hr₀, ?_⟩
  calc
    (∫⁻ y, ‖f y‖ₑ) = ((∫⁻ y, ‖f y‖ₑ) / D) * D :=
      (ENNReal.div_mul_cancel hD₀ hDtop).symm
    _ ≤ (((m + 1 : ℕ) : ℝ≥0∞) ^ n) * D := by
      simpa only [mul_comm] using (mul_le_mul_right hqpow D)
    _ = A * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r₀) := by
      rw [hvol]
      dsimp [D]
      ac_rfl

omit [Nonempty (Fin n)] in
/-- If a small ball is centered sufficiently far from the support, its average vanishes. -/
theorem ball_average_eq_zero_of_far
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {R r₀ : ℝ}
    (hsupp : ∀ y, R ≤ ‖y‖ → f y = 0)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : r < r₀)
    (hx : R + r₀ ≤ ‖x‖) :
    (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ = 0 := by
  have hzero : ∀ y ∈ ball x r, f y = 0 := by
    intro y hy
    have hxy : ‖x - y‖ < r := by rwa [mem_ball', dist_eq_norm] at hy
    have htriangle : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
      calc
        ‖x‖ = ‖y + (x - y)‖ := by congr 1; abel
        _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
    exact hsupp y (by linarith)
  rw [setLIntegral_eq_zero measurableSet_ball (fun y hy ↦ by simp [hzero y hy])]
  simp

omit [Nonempty (Fin n)] in
/-- If the capped density equals its cap on the contact set, the density mass controls the
measure of that set. -/
theorem contact_measure_le_density_mass
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : MeasurableSet Ω)
    (ν : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (κ : ℝ≥0∞)
    (hcontact : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∈ Ω → ν x = κ) :
    κ * volume Ω ≤ ∫⁻ y, ν y := by
  calc
    κ * volume Ω = ∫⁻ _ in Ω, κ := by rw [setLIntegral_const, mul_comm]
    _ = ∫⁻ y in Ω, ν y := by
      refine setLIntegral_congr_fun_ae hΩ ?_
      filter_upwards [hcontact] with y hy hyΩ
      exact (hy hyΩ).symm
    _ ≤ ∫⁻ y, ν y := setLIntegral_le_lintegral _ _

/-- The three-radius argument. The obstacle certificate supplies a contact set `Ω`, a density
bounded by `κ`, a contact-set mass estimate, and Green comparison at zeros of the obstacle. The
radius `r₀` is chosen so that the total mass already controls all larger ball averages. -/
theorem ball_level_bound_of_obstacle_certificate_ae
    (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (C κ : ℝ≥0∞) (R r₀ : ℝ)
    (hκfin : κ ≠ ∞)
    (hr₀ : 0 < r₀) (hsupp : ∀ y, R ≤ ‖y‖ → f y = 0)
    (hlarge : (∫⁻ y, ‖f y‖ₑ) ≤
      (C * κ) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r₀))
    (hKunit : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, 1 ≤ K z)
    (hKmass : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))) = C)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (ν : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hcontact : κ * volume Ω ≤ ∫⁻ y, ‖f y‖ₑ)
    (hν : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ν y ≤ κ)
    (hgreen : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), x ∉ Ω → 0 < r →
      r < r₀ → ‖x‖ < R + r₀ →
      (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ) ≤
        ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ν y) :
    (C * κ) * volume {x | C * κ < ballMaximalFunction f x} ≤
      C * ∫⁻ y, ‖f y‖ₑ := by
  have hsubset : {x | C * κ < ballMaximalFunction f x} ⊆ Ω := by
    intro x hx
    by_contra hxΩ
    have hbound : ballMaximalFunction f x ≤ C * κ := by
      refine iSup₂_le fun r hr ↦ ?_
      by_cases hbig : r₀ ≤ r
      · exact ball_average_le_of_large_radius f x hr₀ hbig hlarge
      by_cases hfar : R + r₀ ≤ ‖x‖
      · rw [ball_average_eq_zero_of_far hsupp (lt_of_not_ge hbig) hfar]
        exact bot_le
      calc
        (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ
            ≤ ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ :=
              ball_average_le_kernel_integral hKunit f x hr
        _ ≤ ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ν y :=
          hgreen x r hxΩ hr (lt_of_not_ge hbig) (lt_of_not_ge hfar)
        _ ≤ C * κ :=
          kernel_integral_le_of_density_le_ae K ν x r κ C hκfin hν (hKmass x r hr)
    exact (not_lt_of_ge hbound) hx
  calc
    (C * κ) * volume {x | C * κ < ballMaximalFunction f x}
        ≤ (C * κ) * volume Ω := by
          simpa only [mul_comm] using (mul_le_mul_left (measure_mono hsubset) (C * κ))
    _ = C * (κ * volume Ω) := by ac_rfl
    _ ≤ C * ∫⁻ y, ‖f y‖ₑ := by
      simpa only [mul_comm] using (mul_le_mul_left hcontact C)

/-- Pointwise-density form of `ball_level_bound_of_obstacle_certificate_ae`. -/
theorem ball_level_bound_of_obstacle_certificate
    (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (C κ : ℝ≥0∞) (R r₀ : ℝ)
    (hκfin : κ ≠ ∞)
    (hr₀ : 0 < r₀) (hsupp : ∀ y, R ≤ ‖y‖ → f y = 0)
    (hlarge : (∫⁻ y, ‖f y‖ₑ) ≤
      (C * κ) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r₀))
    (hKunit : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, 1 ≤ K z)
    (hKmass : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))) = C)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (ν : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hcontact : κ * volume Ω ≤ ∫⁻ y, ‖f y‖ₑ)
    (hν : ∀ y, ν y ≤ κ)
    (hgreen : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), x ∉ Ω → 0 < r →
      r < r₀ → ‖x‖ < R + r₀ →
      (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ) ≤
        ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ν y) :
    (C * κ) * volume {x | C * κ < ballMaximalFunction f x} ≤
      C * ∫⁻ y, ‖f y‖ₑ :=
  ball_level_bound_of_obstacle_certificate_ae K f C κ R r₀ hκfin hr₀ hsupp hlarge
    hKunit hKmass Ω ν hcontact (ae_of_all _ hν) hgreen

omit [Nonempty (Fin n)] in
/-- Reparameterize a family of estimates at levels `C * κ` as a weak type bound at every
`ENNReal` level, including zero and infinity. -/
theorem ball_level_bound_of_scaled_levels
    (C : ℝ≥0∞) (hC₀ : 0 < C) (hCtop : C ≠ ∞)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (h : ∀ κ : ℝ≥0∞, 0 < κ → κ ≠ ∞ →
      (C * κ) * volume {x | C * κ < ballMaximalFunction f x} ≤
        C * ∫⁻ y, ‖f y‖ₑ) (α : ℝ≥0∞) :
    α * volume {x | α < ballMaximalFunction f x} ≤ C * ∫⁻ y, ‖f y‖ₑ := by
  by_cases hα₀ : α = 0
  · subst α
    simp
  by_cases hαtop : α = ∞
  · subst α
    simp
  let κ := α / C
  have hκ₀ : 0 < κ := ENNReal.div_pos_iff.mpr ⟨hα₀, hCtop⟩
  have hκtop : κ ≠ ∞ := ENNReal.div_ne_top hαtop hC₀.ne'
  have hlevel : C * κ = α := ENNReal.mul_div_cancel hC₀.ne' hCtop
  simpa only [hlevel] using h κ hκ₀ hκtop

end CenteredMaximal.Ball
