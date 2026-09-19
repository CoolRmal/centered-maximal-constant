/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.JumpEnergy
public import CenteredMaximal.Basic
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The Gagliardo energy and the averaging trick

For `u : ℝ² → ℝ` and `α > 0`, the Gagliardo energy of order `α / 2` is
`[u]² = ∫∫ (u x - u y)² ‖x - y‖^{-(2 + α)} dy dx ∈ [0, ∞]`, where `ℝ² = Fin 2 → ℝ` carries the
sup norm. Everything is done in `ℝ≥0∞`, so that no integrability hypotheses are needed.

The **averaging trick** bounds `|u x|` by cube averages: for every cube `Q` of volume `|Q|`,
`|u x| |Q| ≤ ∫_Q |u x - u y| dy + ∫_Q |u y| dy` (`enorm_mul_volume_le`), and by Cauchy–Schwarz
with the weight `‖x - y‖^{-(2 + α)}`, `(∫_Q |u x - u y| dy)² ≤ g(x) ∫_Q ‖x - y‖^{2 + α} dy`, where
`g(x) = ∫ (u x - u y)² ‖x - y‖^{-(2 + α)} dy` is the inner Gagliardo integral.

* `gagliardo`: the energy, and `measurable_gagliardoIntegrand`, `gagliardo_eq_lintegral_prod`;
* `lintegral_sq_le_gagliardo_add`: the interpolation inequality
  `‖u‖₂² ≤ 2 (ρ^α / 4) [u]² + 2 (4 ρ²)⁻¹ ‖u‖₁²` for every `ρ > 0`, from cubes of radius `ρ`
  centred at every point;
* `setLIntegral_enorm_closedBall_sq_le`: the local `L¹` bound
  `(∫_{Q(0, b)} |u|)² ≤ 2 (2b)² (2R)^{2 + α} (2R)⁻² [u]² + 2 (b / R)⁴ ‖u‖₁²` for `0 < b ≤ R`,
  from the single cube `Q(0, R)`; the coefficient of `‖u‖₁²` tends to `0` as `R → ∞`
  (`exists_setLIntegral_enorm_closedBall_sq_le`);
* `gagliardo_le_jumpEnergy`: the comparison `[u]² ≤ 4 (2 + α) / (1 + α) · E(u)` with the
  axis-split jump energy `E` of `CenteredMaximal.Analysis.JumpEnergy`, from the one-dimensional
  weight integral `∫ max(|h₀|, |h₁|)^{-(2 + α)} dh₁ = 2 (2 + α) / (1 + α) · |h₀|^{-(1 + α)}`
  (`lintegral_ofReal_max_rpow`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

/-- `(a + b)² ≤ 2 a² + 2 b²` in `[0, ∞]`. -/
theorem ENNReal.add_sq_le_two_mul_add (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) one_le_two
  simp only [ENNReal.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at h
  rwa [← mul_add]

/-- **Cauchy–Schwarz** in `[0, ∞]`: `(∫ f g)² ≤ (∫ f²) (∫ g²)`. -/
theorem ENNReal.sq_lintegral_mul_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  refine (pow_le_pow_left₀ zero_le h 2).trans_eq ?_
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  norm_num

namespace CenteredMaximal

variable {u : (Fin 2 → ℝ) → ℝ} {α : ℝ}

/-- The Gagliardo energy `∫∫ (u x − u y)² ‖x − y‖^{−(2+α)}` of order `α/2`, in `[0, ∞]`. -/
def gagliardo (α : ℝ) (u : (Fin 2 → ℝ) → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((u x - u y) ^ 2 * ‖x - y‖ ^ (-(2 + α)))

/-- The integrand of the Gagliardo energy is measurable on the product. -/
theorem measurable_gagliardoIntegrand (hu : Measurable u) (α : ℝ) :
    Measurable fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) ↦
      ENNReal.ofReal ((u p.1 - u p.2) ^ 2 * ‖p.1 - p.2‖ ^ (-(2 + α))) := by
  fun_prop

/-- The inner integral of the Gagliardo energy is a measurable function of `x`. -/
theorem measurable_gagliardoInner (hu : Measurable u) (α : ℝ) :
    Measurable fun x ↦ ∫⁻ y, ENNReal.ofReal ((u x - u y) ^ 2 * ‖x - y‖ ^ (-(2 + α))) :=
  (measurable_gagliardoIntegrand hu α).lintegral_prod_right'

/-- The Gagliardo energy as an integral over the product `ℝ² × ℝ²`. -/
theorem gagliardo_eq_lintegral_prod (hu : Measurable u) (α : ℝ) :
    gagliardo α u = ∫⁻ p : (Fin 2 → ℝ) × (Fin 2 → ℝ),
      ENNReal.ofReal ((u p.1 - u p.2) ^ 2 * ‖p.1 - p.2‖ ^ (-(2 + α))) := by
  rw [Measure.volume_eq_prod, lintegral_prod _ (measurable_gagliardoIntegrand hu α).aemeasurable]
  rfl

/-! ### Splitting the weight -/

/-- Splitting the weight for Cauchy–Schwarz:
`|u x − u y| = (|u x − u y| ‖x − y‖^{−s/2}) · ‖x − y‖^{s/2}`, also at `y = x`. -/
theorem enorm_sub_eq_ofReal_mul_ofReal (u : (Fin 2 → ℝ) → ℝ) (x y : Fin 2 → ℝ) (s : ℝ) :
    ‖u x - u y‖ₑ = ENNReal.ofReal (|u x - u y| * ‖x - y‖ ^ (-s / 2)) *
      ENNReal.ofReal (‖x - y‖ ^ (s / 2)) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity)]
  rcases eq_or_ne x y with rfl | hxy
  · simp
  · have h : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    rw [mul_assoc, ← Real.rpow_add h, neg_div, neg_add_cancel, Real.rpow_zero, mul_one]

/-- The square of the first factor in `enorm_sub_eq_ofReal_mul_ofReal`. -/
theorem ofReal_abs_mul_rpow_sq (a : ℝ) {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    ENNReal.ofReal (|a| * r ^ (-s / 2)) ^ 2 = ENNReal.ofReal (a ^ 2 * r ^ (-s)) := by
  rw [← ENNReal.ofReal_pow (by positivity), mul_pow, sq_abs,
    ← Real.rpow_natCast (r ^ (-s / 2)) 2, ← Real.rpow_mul hr]
  congr 3
  push_cast
  ring

/-- The square of the second factor in `enorm_sub_eq_ofReal_mul_ofReal`. -/
theorem ofReal_rpow_half_sq {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    ENNReal.ofReal (r ^ (s / 2)) ^ 2 = ENNReal.ofReal (r ^ s) := by
  rw [← ENNReal.ofReal_pow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hr]
  congr 2
  push_cast
  ring

/-! ### The averaging trick -/

/-- The averaging trick: `|u x| |s| ≤ ∫_s |u x − u y| dy + ∫_s |u y| dy` for every set `s`. -/
theorem enorm_mul_volume_le (hu : Measurable u) (x : Fin 2 → ℝ) (s : Set (Fin 2 → ℝ)) :
    ‖u x‖ₑ * volume s ≤ (∫⁻ y in s, ‖u x - u y‖ₑ) + ∫⁻ y in s, ‖u y‖ₑ := by
  rw [← setLIntegral_const, ← lintegral_add_right _ hu.enorm]
  exact lintegral_mono fun y ↦ by simpa using enorm_add_le (u x - u y) (u y)

/-- Cauchy–Schwarz on the cube `Q(x, ρ)`: `(∫_Q |u x − u y| dy)² ≤ g(x) · ρ^{2+α} |Q|`, where
`g(x) = ∫ (u x − u y)² ‖x − y‖^{−(2+α)} dy` is the inner Gagliardo integral. -/
theorem setLIntegral_enorm_sub_sq_le (hu : Measurable u) (hα : 0 ≤ α) (x : Fin 2 → ℝ) (ρ : ℝ) :
    (∫⁻ y in closedBall x ρ, ‖u x - u y‖ₑ) ^ 2 ≤
      (∫⁻ y, ENNReal.ofReal ((u x - u y) ^ 2 * ‖x - y‖ ^ (-(2 + α)))) *
        (ENNReal.ofReal (ρ ^ (2 + α)) * volume (closedBall x ρ)) := by
  calc (∫⁻ y in closedBall x ρ, ‖u x - u y‖ₑ) ^ 2
      = (∫⁻ y in closedBall x ρ, ENNReal.ofReal (|u x - u y| * ‖x - y‖ ^ (-(2 + α) / 2)) *
          ENNReal.ofReal (‖x - y‖ ^ ((2 + α) / 2))) ^ 2 := by
        congr 1
        exact lintegral_congr fun y ↦ enorm_sub_eq_ofReal_mul_ofReal u x y (2 + α)
    _ ≤ (∫⁻ y in closedBall x ρ, ENNReal.ofReal (|u x - u y| * ‖x - y‖ ^ (-(2 + α) / 2)) ^ 2) *
          ∫⁻ y in closedBall x ρ, ENNReal.ofReal (‖x - y‖ ^ ((2 + α) / 2)) ^ 2 :=
        ENNReal.sq_lintegral_mul_le (by fun_prop) (by fun_prop)
    _ ≤ (∫⁻ y, ENNReal.ofReal ((u x - u y) ^ 2 * ‖x - y‖ ^ (-(2 + α)))) *
          (ENNReal.ofReal (ρ ^ (2 + α)) * volume (closedBall x ρ)) := by
        refine mul_le_mul' ?_ ?_
        · calc _ = ∫⁻ y in closedBall x ρ,
                ENNReal.ofReal ((u x - u y) ^ 2 * ‖x - y‖ ^ (-(2 + α))) :=
                lintegral_congr fun y ↦ ofReal_abs_mul_rpow_sq _ (norm_nonneg _) _
            _ ≤ _ := setLIntegral_le_lintegral _ _
        · calc _ = ∫⁻ y in closedBall x ρ, ENNReal.ofReal (‖x - y‖ ^ (2 + α)) :=
                lintegral_congr fun y ↦ ofReal_rpow_half_sq (norm_nonneg _) _
            _ ≤ ∫⁻ _ in closedBall x ρ, ENNReal.ofReal (ρ ^ (2 + α)) :=
                setLIntegral_mono' measurableSet_closedBall fun y hy ↦ by
                  rw [mem_closedBall, dist_comm, dist_eq_norm] at hy
                  exact ENNReal.ofReal_le_ofReal
                    (Real.rpow_le_rpow (norm_nonneg _) hy (by positivity))
            _ = _ := setLIntegral_const _ _

/-- The cube integral `∫_{Q(x, ρ)} F x y dy` is a measurable function of the centre `x`. -/
theorem measurable_setLIntegral_closedBall {F : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) (ρ : ℝ) :
    Measurable fun x ↦ ∫⁻ y in closedBall x ρ, F x y := by
  have hS : MeasurableSet {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) | dist p.2 p.1 ≤ ρ} :=
    measurableSet_le (by fun_prop) measurable_const
  have : (fun x ↦ ∫⁻ y in closedBall x ρ, F x y) = fun x ↦ ∫⁻ y,
      {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) | dist p.2 p.1 ≤ ρ}.indicator (Function.uncurry F) (x, y) := by
    ext x
    rw [← lintegral_indicator measurableSet_closedBall]
    rfl
  rw [this]
  exact (hF.indicator hS).lintegral_prod_right'

/-- Tonelli: integrating `∫_{Q(x, ρ)} |u|` over all centres `x` gives `|Q_ρ| ‖u‖₁`. -/
theorem lintegral_setLIntegral_closedBall_enorm (hu : Measurable u) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫⁻ x, ∫⁻ y in closedBall x ρ, ‖u y‖ₑ = ENNReal.ofReal ((2 * ρ) ^ 2) * ∫⁻ y, ‖u y‖ₑ := by
  set S : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) := {p | dist p.2 p.1 ≤ ρ} with hS
  have hSm : MeasurableSet S := measurableSet_le (by fun_prop) measurable_const
  have hF : Measurable (S.indicator fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) ↦ ‖u p.2‖ₑ) :=
    (hu.comp measurable_snd).enorm.indicator hSm
  calc ∫⁻ x, ∫⁻ y in closedBall x ρ, ‖u y‖ₑ
      = ∫⁻ x, ∫⁻ y, S.indicator (fun p ↦ ‖u p.2‖ₑ) (x, y) := by
        refine lintegral_congr fun x ↦ ?_
        rw [← lintegral_indicator measurableSet_closedBall]
        rfl
    _ = ∫⁻ y, ∫⁻ x, S.indicator (fun p ↦ ‖u p.2‖ₑ) (x, y) :=
        lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ y, ‖u y‖ₑ * volume (closedBall y ρ) := by
        refine lintegral_congr fun y ↦ ?_
        rw [← setLIntegral_const, ← lintegral_indicator measurableSet_closedBall]
        refine lintegral_congr fun x ↦ ?_
        by_cases hx : x ∈ closedBall y ρ
        · rw [indicator_of_mem hx, indicator_of_mem (by simpa [hS, dist_comm] using hx)]
        · rw [indicator_of_notMem hx, indicator_of_notMem (by simpa [hS, dist_comm] using hx)]
    _ = ENNReal.ofReal ((2 * ρ) ^ 2) * ∫⁻ y, ‖u y‖ₑ := by
        simp_rw [volume_closedBall_eq _ hρ]
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]

/-! ### Interpolation -/

/-- **Interpolation**: `‖u‖₂² ≤ 2 (ρ^α / 4) [u]² + 2 (4ρ²)⁻¹ ‖u‖₁²` for every `ρ > 0`. This is the
averaging trick on the cubes `Q(x, ρ)`, `x ∈ ℝ²`, with Cauchy–Schwarz
(`setLIntegral_enorm_sub_sq_le`) for the oscillation term and Tonelli
(`lintegral_setLIntegral_closedBall_enorm`) for the average of `|u|`. -/
theorem lintegral_sq_le_gagliardo_add (hu : Measurable u) (hα : 0 ≤ α) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ x, ENNReal.ofReal (u x ^ 2) ≤
      2 * ENNReal.ofReal (ρ ^ α / 4) * gagliardo α u +
        2 * ENNReal.ofReal (1 / (4 * ρ ^ 2)) * (∫⁻ x, ‖u x‖ₑ) ^ 2 := by
  set V : ℝ≥0∞ := ENNReal.ofReal ((2 * ρ) ^ 2) with hV
  have hV0 : V ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  set c : ℝ≥0∞ := V⁻¹ with hc
  have hcV : c * V = 1 := ENNReal.inv_mul_cancel hV0 ENNReal.ofReal_ne_top
  have hc2V : c ^ 2 * V = c := by rw [sq, mul_assoc, hcV, mul_one]
  set N := ∫⁻ x, ‖u x‖ₑ with hN
  set g : (Fin 2 → ℝ) → ℝ≥0∞ :=
    fun x ↦ ∫⁻ y, ENNReal.ofReal ((u x - u y) ^ 2 * ‖x - y‖ ^ (-(2 + α))) with hg
  set J : (Fin 2 → ℝ) → ℝ≥0∞ := fun x ↦ ∫⁻ y in closedBall x ρ, ‖u y‖ₑ with hJ
  have hgm : Measurable g := measurable_gagliardoInner hu α
  have hJm : Measurable J :=
    measurable_setLIntegral_closedBall (F := fun _ y ↦ ‖u y‖ₑ) (hu.comp measurable_snd).enorm ρ
  have hJint : ∫⁻ x, J x = V * N := lintegral_setLIntegral_closedBall_enorm hu hρ.le
  have hG : gagliardo α u = ∫⁻ x, g x := rfl
  -- the pointwise bound `|u x|² ≤ 2 (c ρ^{2+α}) g x + 2 c² ‖u‖₁ J x`
  have hpt : ∀ x, ENNReal.ofReal (u x ^ 2) ≤
      2 * (c * ENNReal.ofReal (ρ ^ (2 + α))) * g x + 2 * (c ^ 2 * N) * J x := by
    intro x
    set I := ∫⁻ y in closedBall x ρ, ‖u x - u y‖ₑ with hI
    have h1 : ‖u x‖ₑ ≤ (I + J x) * c := by
      calc ‖u x‖ₑ = ‖u x‖ₑ * V * c := by rw [mul_assoc, mul_comm V, hcV, mul_one]
        _ ≤ (I + J x) * c := by
          gcongr
          simpa [hV, volume_closedBall_eq x hρ.le] using enorm_mul_volume_le hu x (closedBall x ρ)
    have h2 : I ^ 2 ≤ g x * (ENNReal.ofReal (ρ ^ (2 + α)) * V) := by
      simpa only [hV, volume_closedBall_eq x hρ.le] using setLIntegral_enorm_sub_sq_le hu hα x ρ
    have h3 : J x ≤ N := setLIntegral_le_lintegral _ _
    calc ENNReal.ofReal (u x ^ 2) = ‖u x‖ₑ ^ 2 := by
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
      _ ≤ ((I + J x) * c) ^ 2 := pow_le_pow_left₀ zero_le h1 2
      _ = (I + J x) ^ 2 * c ^ 2 := mul_pow _ _ _
      _ ≤ (2 * I ^ 2 + 2 * J x ^ 2) * c ^ 2 := by gcongr; exact ENNReal.add_sq_le_two_mul_add _ _
      _ ≤ (2 * (g x * (ENNReal.ofReal (ρ ^ (2 + α)) * V)) + 2 * (N * J x)) * c ^ 2 := by
          gcongr
          rw [sq]
          gcongr
      _ = 2 * (c ^ 2 * V * ENNReal.ofReal (ρ ^ (2 + α))) * g x + 2 * (c ^ 2 * N) * J x := by ring
      _ = _ := by rw [hc2V]
  -- integrate in `x`
  calc ∫⁻ x, ENNReal.ofReal (u x ^ 2)
      ≤ ∫⁻ x, (2 * (c * ENNReal.ofReal (ρ ^ (2 + α))) * g x + 2 * (c ^ 2 * N) * J x) :=
        lintegral_mono hpt
    _ = (2 * (c * ENNReal.ofReal (ρ ^ (2 + α))) * ∫⁻ x, g x) + 2 * (c ^ 2 * N) * ∫⁻ x, J x := by
        rw [lintegral_add_left (hgm.const_mul _), lintegral_const_mul _ hgm,
          lintegral_const_mul _ hJm]
    _ = 2 * (c * ENNReal.ofReal (ρ ^ (2 + α))) * gagliardo α u + 2 * (c ^ 2 * V) * N ^ 2 := by
        rw [hJint, hG]; ring
    _ = _ := by
        rw [hc2V]
        congr 3
        · rw [hc, hV, ← ENNReal.ofReal_inv_of_pos (by positivity),
            ← ENNReal.ofReal_mul (by positivity), Real.rpow_add hρ, Real.rpow_two]
          congr 1
          field_simp
          ring
        · rw [hc, hV, ← ENNReal.ofReal_inv_of_pos (by positivity)]
          congr 1
          ring

/-! ### Local integrability -/

/-- **Local `L¹` bound**: for `0 < b ≤ R`,
`(∫_{Q(0, b)} |u|)² ≤ 2 (2b)² (2R)^{2+α} (2R)⁻² [u]² + 2 (b / R)⁴ ‖u‖₁²`. This is the averaging
trick on the single cube `Q(0, R)`, integrated over `x ∈ Q(0, b)`, with Cauchy–Schwarz on
`Q(0, b) × Q(0, R)`, where `‖x − y‖ ≤ 2R`. For fixed `b` the coefficient of `‖u‖₁²` tends to `0`
as `R → ∞`. -/
theorem setLIntegral_enorm_closedBall_sq_le (hu : Measurable u) (hα : 0 ≤ α) {b R : ℝ}
    (hb : 0 < b) (hbR : b ≤ R) :
    (∫⁻ x in closedBall (0 : Fin 2 → ℝ) b, ‖u x‖ₑ) ^ 2 ≤
      2 * ENNReal.ofReal ((2 * b) ^ 2 * (2 * R) ^ (2 + α) / (2 * R) ^ 2) * gagliardo α u +
        2 * ENNReal.ofReal ((b / R) ^ 4) * (∫⁻ x, ‖u x‖ₑ) ^ 2 := by
  have hR : 0 < R := hb.trans_le hbR
  set B : Set (Fin 2 → ℝ) := closedBall 0 b with hB
  set D : Set (Fin 2 → ℝ) := closedBall 0 R with hD
  set W : ℝ≥0∞ := volume D with hW
  have hW' : W = ENNReal.ofReal ((2 * R) ^ 2) := volume_closedBall_eq _ hR.le
  have hVB : volume B = ENNReal.ofReal ((2 * b) ^ 2) := volume_closedBall_eq _ hb.le
  have hW0 : W ≠ 0 := hW' ▸ (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hWt : W ≠ ∞ := hW' ▸ ENNReal.ofReal_ne_top
  set c : ℝ≥0∞ := W⁻¹ with hc
  have hcW : c * W = 1 := ENNReal.inv_mul_cancel hW0 hWt
  have hc2W : c ^ 2 * W = c := by rw [sq, mul_assoc, hcW, mul_one]
  set N := ∫⁻ x, ‖u x‖ₑ with hN
  set K := ∫⁻ x in B, ∫⁻ y in D, ‖u x - u y‖ₑ with hK
  set J := ∫⁻ y in D, ‖u y‖ₑ with hJ
  have hJN : J ≤ N := setLIntegral_le_lintegral _ _
  -- the averaging trick on `Q(0, R)`, integrated over `Q(0, b)`
  have h1 : ∫⁻ x in B, ‖u x‖ₑ ≤ (K + J * volume B) * c := by
    calc ∫⁻ x in B, ‖u x‖ₑ = (∫⁻ x in B, ‖u x‖ₑ) * W * c := by
          rw [mul_assoc, mul_comm W, hcW, mul_one]
      _ ≤ (K + J * volume B) * c := by
          gcongr
          rw [← lintegral_mul_const' _ _ hWt]
          calc ∫⁻ x in B, ‖u x‖ₑ * W ≤ ∫⁻ x in B, ((∫⁻ y in D, ‖u x - u y‖ₑ) + J) :=
                lintegral_mono fun x ↦ enorm_mul_volume_le hu x D
            _ = K + J * volume B := by
                rw [lintegral_add_right _ measurable_const, setLIntegral_const]
  -- Cauchy–Schwarz on `Q(0, b) × Q(0, R)`
  have h2 : K ^ 2 ≤ gagliardo α u * (ENNReal.ofReal ((2 * R) ^ (2 + α)) * W * volume B) := by
    have hKprod : K = ∫⁻ p, ENNReal.ofReal (|u p.1 - u p.2| * ‖p.1 - p.2‖ ^ (-(2 + α) / 2)) *
        ENNReal.ofReal (‖p.1 - p.2‖ ^ ((2 + α) / 2))
          ∂((volume.restrict B).prod (volume.restrict D)) := by
      rw [lintegral_prod _ (by fun_prop)]
      exact lintegral_congr fun x ↦ lintegral_congr fun y ↦
        enorm_sub_eq_ofReal_mul_ofReal u x y (2 + α)
    rw [hKprod]
    refine (ENNReal.sq_lintegral_mul_le (by fun_prop) (by fun_prop)).trans ?_
    rw [lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
    gcongr
    · calc _ = ∫⁻ x in B, ∫⁻ y in D, ENNReal.ofReal ((u x - u y) ^ 2 * ‖x - y‖ ^ (-(2 + α))) :=
            lintegral_congr fun x ↦ lintegral_congr fun y ↦
              ofReal_abs_mul_rpow_sq _ (norm_nonneg _) _
        _ ≤ gagliardo α u :=
            (setLIntegral_le_lintegral _ _).trans
              (lintegral_mono fun x ↦ setLIntegral_le_lintegral _ _)
    · calc _ = ∫⁻ x in B, ∫⁻ y in D, ENNReal.ofReal (‖x - y‖ ^ (2 + α)) :=
            lintegral_congr fun x ↦ lintegral_congr fun y ↦ ofReal_rpow_half_sq (norm_nonneg _) _
        _ ≤ ∫⁻ _ in B, ∫⁻ _ in D, ENNReal.ofReal ((2 * R) ^ (2 + α)) :=
            setLIntegral_mono' measurableSet_closedBall fun x hx ↦
              setLIntegral_mono' measurableSet_closedBall fun y hy ↦ by
                rw [hB, mem_closedBall_zero_iff] at hx
                rw [hD, mem_closedBall_zero_iff] at hy
                refine ENNReal.ofReal_le_ofReal
                  (Real.rpow_le_rpow (norm_nonneg _) ?_ (by positivity))
                linarith [norm_sub_le x y]
        _ = ENNReal.ofReal ((2 * R) ^ (2 + α)) * W * volume B := by
            rw [setLIntegral_const, setLIntegral_const]
  -- combine
  have hcB : c * volume B = ENNReal.ofReal ((b / R) ^ 2) := by
    rw [hc, hW', hVB, ← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  calc (∫⁻ x in B, ‖u x‖ₑ) ^ 2 ≤ ((K + J * volume B) * c) ^ 2 := pow_le_pow_left₀ zero_le h1 2
    _ = (K + J * volume B) ^ 2 * c ^ 2 := mul_pow _ _ _
    _ ≤ (2 * K ^ 2 + 2 * (J * volume B) ^ 2) * c ^ 2 := by
        gcongr; exact ENNReal.add_sq_le_two_mul_add _ _
    _ ≤ (2 * (gagliardo α u * (ENNReal.ofReal ((2 * R) ^ (2 + α)) * W * volume B)) +
          2 * (N * volume B) ^ 2) * c ^ 2 := by gcongr
    _ = 2 * (c ^ 2 * W * volume B * ENNReal.ofReal ((2 * R) ^ (2 + α))) * gagliardo α u +
          2 * (c * volume B) ^ 2 * N ^ 2 := by ring
    _ = _ := by
        rw [hc2W, hcB]
        congr 3
        · rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
        · rw [← ENNReal.ofReal_pow (by positivity)]
          congr 1
          ring

/-- For every `ε > 0` there is a cube `Q(0, R)` that makes the coefficient of `‖u‖₁²` in
`setLIntegral_enorm_closedBall_sq_le` at most `ε`. -/
theorem exists_setLIntegral_enorm_closedBall_sq_le (hu : Measurable u) (hα : 0 ≤ α) {b : ℝ}
    (hb : 0 < b) {ε : ℝ} (hε : 0 < ε) :
    ∃ R, b ≤ R ∧ (∫⁻ x in closedBall (0 : Fin 2 → ℝ) b, ‖u x‖ₑ) ^ 2 ≤
      2 * ENNReal.ofReal ((2 * b) ^ 2 * (2 * R) ^ (2 + α) / (2 * R) ^ 2) * gagliardo α u +
        2 * ENNReal.ofReal ε * (∫⁻ x, ‖u x‖ₑ) ^ 2 := by
  have hR : b ≤ max b (b / ε) := le_max_left _ _
  have hR₀ : 0 < max b (b / ε) := hb.trans_le hR
  refine ⟨max b (b / ε), hR, (setLIntegral_enorm_closedBall_sq_le hu hα hb hR).trans ?_⟩
  gcongr
  refine (pow_le_of_le_one (by positivity) ((div_le_one hR₀).2 hR) four_ne_zero).trans ?_
  rw [div_le_iff₀ hR₀]
  calc b = ε * (b / ε) := by field_simp
    _ ≤ ε * max b (b / ε) := by gcongr; exact le_max_right _ _

/-! ### Comparison with the jump energy -/

/-- The sup norm on `ℝ²`: `‖h‖ = max |h₀| |h₁|`. -/
theorem norm_eq_max_abs (h : Fin 2 → ℝ) : ‖h‖ = max |h 0| |h 1| := by
  refine le_antisymm ?_ (max_le (by simpa using norm_le_pi_norm h 0)
    (by simpa using norm_le_pi_norm h 1))
  rw [pi_norm_le_iff_of_nonneg (by positivity), Fin.forall_fin_two]
  exact ⟨by simp, by simp⟩

/-- The one-dimensional weight integral: for `c > 0` and `α > -1`,
`∫ max(c, |t|)^{-(2+α)} dt = 2 (2 + α) / (1 + α) · c^{-(1+α)}`, by splitting at `|t| = c`. -/
theorem lintegral_ofReal_max_rpow {c : ℝ} (hc : 0 < c) (hα : -1 < α) :
    ∫⁻ t : ℝ, ENNReal.ofReal (max c |t| ^ (-(2 + α))) =
      ENNReal.ofReal (2 * (2 + α) / (1 + α) * c ^ (-(1 + α))) := by
  set f : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (max c |t| ^ (-(2 + α))) with hf
  have heven : ∀ t, f (-t) = f t := fun t ↦ by simp [hf]
  -- the integrand is even, so the negative half-line contributes as much as the positive one
  have hneg : ∫⁻ t in Iic 0, f t = ∫⁻ t in Ioi 0, f t := by
    rw [restrict_Ioi_eq_restrict_Ici, ← lintegral_indicator measurableSet_Iic,
      ← lintegral_indicator measurableSet_Ici, ← lintegral_neg_eq_self ((Ici 0).indicator f)]
    refine lintegral_congr fun t ↦ ?_
    by_cases ht : t ≤ 0
    · rw [indicator_of_mem (mem_Iic.2 ht), indicator_of_mem (mem_Ici.2 (neg_nonneg.2 ht)), heven]
    · rw [indicator_of_notMem (by simpa using ht), indicator_of_notMem (by simpa using ht)]
  -- on the positive half-line, split at `t = c`
  have hpos : ∫⁻ t in Ioi 0, f t =
      ENNReal.ofReal (c ^ (-(2 + α)) * c) + ENNReal.ofReal (c ^ (-(1 + α)) / (1 + α)) := by
    rw [← Ioc_union_Ioi_eq_Ioi hc.le, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
    congr 1
    · rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ ↦ ENNReal.ofReal (c ^ (-(2 + α))))
        fun t ht ↦ ?_, setLIntegral_const, Real.volume_Ioc, sub_zero,
        ← ENNReal.ofReal_mul (by positivity)]
      simp only [hf]
      rw [abs_of_pos ht.1, max_eq_left ht.2]
    · rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun t ↦ ENNReal.ofReal (t ^ (-(2 + α))))
        fun t ht ↦ ?_]
      · rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt (by linarith) hc)
          ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht ↦
            Real.rpow_nonneg (hc.trans ht).le _)), integral_Ioi_rpow_of_lt (by linarith) hc]
        congr 1
        rw [show -(2 + α) + 1 = -(1 + α) by ring, neg_div_neg_eq]
      · simp only [hf]
        rw [abs_of_pos (hc.trans ht), max_eq_right (mem_Ioi.1 ht).le]
  have h1α : 1 + α ≠ 0 := (by linarith : (0 : ℝ) < 1 + α).ne'
  rw [← lintegral_add_compl f measurableSet_Iic (A := Iic 0), compl_Iic, hneg, hpos, ← two_mul,
    ← ENNReal.ofReal_add (by positivity) (div_nonneg (Real.rpow_nonneg hc.le _) (by linarith)),
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  rw [← Real.rpow_add_one hc.ne', show -(2 + α) + 1 = -(1 + α) by ring]
  field_simp
  ring

/-- Integrating a function of one coordinate against the weight `‖h‖^{-(2+α)}` over `ℝ²`
reduces to the one-dimensional weight `|s|^{-(1+α)}`, provided the function vanishes at `0`. -/
theorem lintegral_mul_ofReal_norm_rpow {G : ℝ → ℝ≥0∞} (hG : Measurable G) (hG0 : G 0 = 0)
    (hα : -1 < α) (j : Fin 2) :
    ∫⁻ h : Fin 2 → ℝ, G (h j) * ENNReal.ofReal (‖h‖ ^ (-(2 + α))) =
      ENNReal.ofReal (2 * (2 + α) / (1 + α)) * ∫⁻ s, G s * ENNReal.ofReal (|s| ^ (-(1 + α))) := by
  have key : ∀ s : ℝ, ∫⁻ t, G s * ENNReal.ofReal (max |s| |t| ^ (-(2 + α))) =
      ENNReal.ofReal (2 * (2 + α) / (1 + α)) * (G s * ENNReal.ofReal (|s| ^ (-(1 + α)))) := by
    intro s
    rw [lintegral_const_mul _ (by fun_prop)]
    rcases eq_or_ne s 0 with rfl | hs
    · simp [hG0]
    · rw [lintegral_ofReal_max_rpow (abs_pos.2 hs) hα,
        ENNReal.ofReal_mul (div_nonneg (by linarith) (by linarith))]
      ring
  have hmeas : Measurable fun h : Fin 2 → ℝ ↦ G (h j) * ENNReal.ofReal (‖h‖ ^ (-(2 + α))) := by
    fun_prop
  rw [← ((volume_preserving_finTwoArrow ℝ).symm _).lintegral_comp hmeas, Measure.volume_eq_prod]
  simp only [norm_eq_max_abs, MeasurableEquiv.finTwoArrow_symm_apply, Fin.cons_zero, Fin.cons_one]
  fin_cases j
  · rw [lintegral_prod _ (by fun_prop), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun s ↦ key s
  · rw [lintegral_prod_symm _ (by fun_prop), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun t ↦ ?_
    simp only [max_comm]
    exact key t

/-- The Gagliardo-type integral of the increment along the coordinate axis `e_j` is
`2 (2 + α) / (1 + α)` times the `j`-th summand of the jump energy. -/
theorem lintegral_lintegral_single_norm_rpow (hu : Measurable u) (hα : -1 < α) (j : Fin 2) :
    ∫⁻ x, ∫⁻ h : Fin 2 → ℝ,
        ENNReal.ofReal ((u (x + h j • Pi.single j 1) - u x) ^ 2 * ‖h‖ ^ (-(2 + α))) =
      ENNReal.ofReal (2 * (2 + α) / (1 + α)) * ∫⁻ p : (Fin 2 → ℝ) × ℝ,
        ENNReal.ofReal ((u (p.1 + p.2 • Pi.single j 1) - u p.1) ^ 2 * |p.2| ^ (-(1 + α))) := by
  rw [Measure.volume_eq_prod, lintegral_prod _ (measurable_jumpIntegrand α hu j).aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x ↦ ?_
  calc ∫⁻ h : Fin 2 → ℝ,
        ENNReal.ofReal ((u (x + h j • Pi.single j 1) - u x) ^ 2 * ‖h‖ ^ (-(2 + α)))
      = ∫⁻ h : Fin 2 → ℝ, ENNReal.ofReal ((u (x + h j • Pi.single j 1) - u x) ^ 2) *
          ENNReal.ofReal (‖h‖ ^ (-(2 + α))) :=
        lintegral_congr fun h ↦ ENNReal.ofReal_mul (sq_nonneg _)
    _ = ENNReal.ofReal (2 * (2 + α) / (1 + α)) * ∫⁻ s,
          ENNReal.ofReal ((u (x + s • Pi.single j 1) - u x) ^ 2) *
            ENNReal.ofReal (|s| ^ (-(1 + α))) :=
        lintegral_mul_ofReal_norm_rpow
          (G := fun s ↦ ENNReal.ofReal ((u (x + s • Pi.single j 1) - u x) ^ 2))
          (by fun_prop) (by simp) hα j
    _ = _ := by
        congr 1
        exact lintegral_congr fun s ↦ (ENNReal.ofReal_mul (sq_nonneg _)).symm

/-- The decomposition `h = h₀ e₀ + h₁ e₁` of a vector of `ℝ²`, in the form used for the
intermediate point `x + h₀ e₀`. -/
theorem add_single_add_single (x h : Fin 2 → ℝ) :
    x + h 0 • Pi.single 0 1 + h 1 • Pi.single 1 1 = x + h := by
  ext i; fin_cases i <;> simp

/-- The Gagliardo energy in the increment variable `h = y − x`. -/
theorem gagliardo_eq_lintegral_lintegral_add (α : ℝ) (u : (Fin 2 → ℝ) → ℝ) :
    gagliardo α u = ∫⁻ x, ∫⁻ h, ENNReal.ofReal ((u (x + h) - u x) ^ 2 * ‖h‖ ^ (-(2 + α))) := by
  refine lintegral_congr fun x ↦ ?_
  have h := lintegral_add_right_eq_self (μ := volume)
    (fun y ↦ ENNReal.ofReal ((u x - u y) ^ 2 * ‖x - y‖ ^ (-(2 + α)))) x
  refine h.symm.trans (lintegral_congr fun h ↦ ?_)
  show ENNReal.ofReal ((u x - u (h + x)) ^ 2 * ‖x - (h + x)‖ ^ (-(2 + α))) = _
  rw [add_comm h x, sub_add_cancel_left, norm_neg,
    show (u x - u (x + h)) ^ 2 = (u (x + h) - u x) ^ 2 by ring]

/-- Splitting the increment `u(x + h) − u(x)` at the intermediate point `x + h₀ e₀`, with
`(a + b)² ≤ 2 a² + 2 b²`. -/
theorem ofReal_sq_mul_le_add (u : (Fin 2 → ℝ) → ℝ) (α : ℝ) (x h : Fin 2 → ℝ) :
    ENNReal.ofReal ((u (x + h) - u x) ^ 2 * ‖h‖ ^ (-(2 + α))) ≤
      2 * ENNReal.ofReal ((u (x + h) - u (x + h 0 • Pi.single 0 1)) ^ 2 * ‖h‖ ^ (-(2 + α))) +
        2 * ENNReal.ofReal ((u (x + h 0 • Pi.single 0 1) - u x) ^ 2 * ‖h‖ ^ (-(2 + α))) := by
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [mul_nonneg (sq_nonneg ((u (x + h) - u (x + h 0 • Pi.single 0 1)) -
    (u (x + h 0 • Pi.single 0 1) - u x))) (Real.rpow_nonneg (norm_nonneg h) (-(2 + α)))]

/-- The integrand of the increment from `x + h₀ e₀` to `x + h` is measurable on `ℝ² × ℝ²`. -/
theorem measurable_subSingleIntegrand (hu : Measurable u) (α : ℝ) :
    Measurable fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) ↦
      ENNReal.ofReal ((u (p.1 + p.2) - u (p.1 + p.2 0 • Pi.single 0 1)) ^ 2 *
        ‖p.2‖ ^ (-(2 + α))) := by
  fun_prop

/-- The integrand of the axis-`j` increment `u(x + h_j e_j) − u(x)` with the weight
`‖h‖^{-(2+α)}` is measurable on `ℝ² × ℝ²`. -/
theorem measurable_singleIntegrand (hu : Measurable u) (α : ℝ) (j : Fin 2) :
    Measurable fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) ↦
      ENNReal.ofReal ((u (p.1 + p.2 j • Pi.single j 1) - u p.1) ^ 2 * ‖p.2‖ ^ (-(2 + α))) := by
  fun_prop

/-- The translation `x ↦ x + h₀ e₀` at fixed `h` turns the increment from `x + h₀ e₀` to `x + h`
into the axis-`1` increment `u(x + h₁ e₁) − u(x)`. -/
theorem lintegral_lintegral_sub_single_eq (hu : Measurable u) (α : ℝ) :
    ∫⁻ x, ∫⁻ h : Fin 2 → ℝ,
        ENNReal.ofReal ((u (x + h) - u (x + h 0 • Pi.single 0 1)) ^ 2 * ‖h‖ ^ (-(2 + α))) =
      ∫⁻ x, ∫⁻ h : Fin 2 → ℝ,
        ENNReal.ofReal ((u (x + h 1 • Pi.single 1 1) - u x) ^ 2 * ‖h‖ ^ (-(2 + α))) := by
  have hm1 := (measurable_subSingleIntegrand hu α).aemeasurable (μ := volume.prod volume)
  have hm2 := (measurable_singleIntegrand hu α 1).aemeasurable (μ := volume.prod volume)
  calc ∫⁻ x, ∫⁻ h : Fin 2 → ℝ,
        ENNReal.ofReal ((u (x + h) - u (x + h 0 • Pi.single 0 1)) ^ 2 * ‖h‖ ^ (-(2 + α)))
      = ∫⁻ h : Fin 2 → ℝ, ∫⁻ x,
          ENNReal.ofReal ((u (x + h) - u (x + h 0 • Pi.single 0 1)) ^ 2 * ‖h‖ ^ (-(2 + α))) := by
        rw [← lintegral_prod _ hm1, ← lintegral_prod_symm _ hm1]
    _ = ∫⁻ h : Fin 2 → ℝ, ∫⁻ x,
          ENNReal.ofReal ((u (x + h 1 • Pi.single 1 1) - u x) ^ 2 * ‖h‖ ^ (-(2 + α))) := by
        refine lintegral_congr fun h ↦ ?_
        have := lintegral_add_right_eq_self (μ := volume) (fun x ↦
          ENNReal.ofReal ((u (x + h 1 • Pi.single 1 1) - u x) ^ 2 * ‖h‖ ^ (-(2 + α))))
          (h 0 • Pi.single 0 1)
        refine Eq.trans ?_ this
        refine lintegral_congr fun x ↦ ?_
        simp only [add_single_add_single]
    _ = _ := by
        rw [← lintegral_prod _ hm2, ← lintegral_prod_symm _ hm2]

/-- **Comparison with the jump energy**: `[u]² ≤ 4 (2 + α) / (1 + α) · E(u)`. Writing `y = x + h`,
one splits `u(x + h) − u(x)` at the intermediate point `x + h₀ e₀`, uses `(a + b)² ≤ 2a² + 2b²`,
and integrates out the coordinate of `h` which does not appear in each increment
(`lintegral_lintegral_single_norm_rpow`), after a translation in `x` for the first term
(`lintegral_lintegral_sub_single_eq`). -/
theorem gagliardo_le_jumpEnergy (hu : Measurable u) (hα : 0 < α) :
    gagliardo α u ≤ ENNReal.ofReal (4 * (2 + α) / (1 + α)) * jumpEnergy α u := by
  have hα' : -1 < α := by linarith
  have hF : Measurable fun x ↦ ∫⁻ h : Fin 2 → ℝ,
      ENNReal.ofReal ((u (x + h) - u (x + h 0 • Pi.single 0 1)) ^ 2 * ‖h‖ ^ (-(2 + α))) :=
    (measurable_subSingleIntegrand hu α).lintegral_prod_right'
  calc gagliardo α u
      = ∫⁻ x, ∫⁻ h, ENNReal.ofReal ((u (x + h) - u x) ^ 2 * ‖h‖ ^ (-(2 + α))) :=
        gagliardo_eq_lintegral_lintegral_add α u
    _ ≤ ∫⁻ x, ∫⁻ h : Fin 2 → ℝ,
          (2 * ENNReal.ofReal ((u (x + h) - u (x + h 0 • Pi.single 0 1)) ^ 2 *
            ‖h‖ ^ (-(2 + α))) +
          2 * ENNReal.ofReal ((u (x + h 0 • Pi.single 0 1) - u x) ^ 2 * ‖h‖ ^ (-(2 + α)))) :=
        lintegral_mono fun x ↦ lintegral_mono fun h ↦ ofReal_sq_mul_le_add u α x h
    _ = ∫⁻ x, ((2 * ∫⁻ h : Fin 2 → ℝ,
          ENNReal.ofReal ((u (x + h) - u (x + h 0 • Pi.single 0 1)) ^ 2 * ‖h‖ ^ (-(2 + α)))) +
          2 * ∫⁻ h : Fin 2 → ℝ,
            ENNReal.ofReal ((u (x + h 0 • Pi.single 0 1) - u x) ^ 2 * ‖h‖ ^ (-(2 + α)))) := by
        refine lintegral_congr fun x ↦ ?_
        have hFx : Measurable fun h : Fin 2 → ℝ ↦ ENNReal.ofReal
            ((u (x + h) - u (x + h 0 • Pi.single 0 1)) ^ 2 * ‖h‖ ^ (-(2 + α))) := by
          fun_prop
        rw [lintegral_add_left (hFx.const_mul _), lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    _ = (2 * ∫⁻ x, ∫⁻ h : Fin 2 → ℝ,
          ENNReal.ofReal ((u (x + h) - u (x + h 0 • Pi.single 0 1)) ^ 2 * ‖h‖ ^ (-(2 + α)))) +
          2 * ∫⁻ x, ∫⁻ h : Fin 2 → ℝ,
            ENNReal.ofReal ((u (x + h 0 • Pi.single 0 1) - u x) ^ 2 * ‖h‖ ^ (-(2 + α))) := by
        rw [lintegral_add_left (hF.const_mul _), lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    _ = ENNReal.ofReal (4 * (2 + α) / (1 + α)) * jumpEnergy α u := by
        rw [lintegral_lintegral_sub_single_eq hu α, lintegral_lintegral_single_norm_rpow hu hα' 1,
          lintegral_lintegral_single_norm_rpow hu hα' 0, jumpEnergy, Fin.sum_univ_two,
          show (4 * (2 + α) / (1 + α) : ℝ) = 2 * (2 * (2 + α) / (1 + α)) by ring,
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        ring

end CenteredMaximal
