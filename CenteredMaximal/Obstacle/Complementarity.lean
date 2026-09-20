/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.JumpGenerator
public import CenteredMaximal.Obstacle.Variational

/-!
# Complementarity and mass conservation for the obstacle minimiser

Fix `0 < α < 2`, `0 < κ` and an obstacle `f` which is measurable, nonnegative, bounded and
compactly supported, let `u` be a minimiser of the obstacle functional over the nonnegative
elements of the energy space of finite `L¹` norm, and let `σ` be the capped density
`σ = f − L u` of `CenteredMaximal.exists_density`. This file identifies the contact set of `u`:
the density saturates its cap `κ` almost everywhere on `{u > 0}`.

* `jumpForm_eq_neg_integral_jumpGen`: **duality between the form and the generator**. For a
  measurable integrable `v` of finite energy and a test function `φ`,
  `E(v, φ) = −∫ v A φ`, where `A = jumpGen α` is the generator of
  `CenteredMaximal.Analysis.JumpGenerator`. At a fixed step `t` the `x`-integral of the product of
  the two increments is absolutely convergent — `v` is in `L¹` and `φ` is bounded — and the shift
  `x ↦ x − t e_j` in the cross term carrying the forward value of `v` turns it into minus the
  pairing of `v` with the second difference of `φ` (`integral_jumpDiff_mul_eq`). The two iterated
  integrals are then exchanged by Fubini, whose hypothesis is the domination
  `|v(x)| jumpBound α M₀ M₂ t` of `integrable_mul_secondDiff_mul_rpow`;
* `jumpForm_self_eq_integral`: **the energy identity** `E(u, u) = ∫ u (f − σ)`, by passing the
  test-function identity of `exists_density` to the limit along the smooth compactly supported
  approximants of `u` given by
  `CenteredMaximal.exists_contDiff_hasCompactSupport_approx`; the form converges by Cauchy–Schwarz
  and the two source terms converge because `f` and `σ` are bounded;
* `jumpForm_self_add_l1_eq`: **the scaling identity** `E(u, u) + κ ‖u‖₁ = ∫ f u`, the variational
  inequality tested against the two competitors `2 u` and `0`;
* `integral_mul_sub_eq_zero`, `ae_eq_of_pos`: **complementarity**, `∫ u (κ − σ) = 0` and hence
  `σ = κ` almost everywhere on `{u > 0}`, since the integrand is nonnegative;
* `integrable_and_integral_density_eq`: **mass conservation** `∫ σ = ∫ f`. The test functions are
  the dilates `χ_R = χ(R⁻¹ ·)` of a fixed bump `χ` equal to `1` on the unit ball
  (`isTestFunction_comp_smul_inv`); the generator of a dilate is `O(R^{−α})` by the scaling law
  `abs_jumpGen_comp_smul_inv_le`, so the form term is negligible, monotone convergence over the
  balls `B(0, n)` shows that `σ` is integrable, and dominated convergence identifies the limits of
  the two source terms;
* `volume_pos_lt_le`: **the contact-set bound** `κ |{u > 0}| ≤ ∫ f`, the mass of the density on the
  contact set, where it equals `κ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace CenteredMaximal

/-- `L²(ℝ²)` with respect to Lebesgue measure. -/
local notation "L²" => Lp ℝ 2 (volume : Measure (Fin 2 → ℝ))

open EnergySpace

variable {α κ : ℝ} {f φ : (Fin 2 → ℝ) → ℝ}

/-! ### Duality between the form and the generator -/

/-- The second difference is jointly measurable in the base point and the step. -/
theorem measurable_secondDiff_uncurry (hφ : Measurable φ) (j : Fin 2) :
    Measurable fun p : (Fin 2 → ℝ) × ℝ => secondDiff φ j p.1 p.2 := by
  unfold secondDiff
  exact ((hφ.comp (measurable_fst.add (measurable_snd.smul_const _))).add
    (hφ.comp (measurable_fst.sub (measurable_snd.smul_const _)))).sub
    (measurable_const.mul (hφ.comp measurable_fst))

/-- The integrand `v(x) (φ(x + t e_j) + φ(x − t e_j) − 2 φ(x)) |t|^{−(1+α)}` of the duality
identity is integrable on `ℝ² × ℝ`: it is dominated by `|v(x)| jumpBound α M₀ M₂ t`, the product
of an integrable function of `x` and an integrable function of `t`. -/
theorem integrable_mul_secondDiff_mul_rpow {α : ℝ} (hα : 0 < α) (hα' : α < 2)
    {v : (Fin 2 → ℝ) → ℝ} (hv : Measurable v) (hv₁ : Integrable v volume) {M₀ M₂ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (h₀ : ∀ x, |φ x| ≤ M₀)
    (h₂ : ∀ x, ‖iteratedFDeriv ℝ 2 φ x‖ ≤ M₂) (j : Fin 2) :
    Integrable (fun p : (Fin 2 → ℝ) × ℝ =>
      v p.1 * (secondDiff φ j p.1 p.2 * |p.2| ^ (-(1 + α)))) volume := by
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h₀ 0)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (h₂ 0)
  have hdom : Integrable (fun p : (Fin 2 → ℝ) × ℝ => |v p.1| * jumpBound α M₀ M₂ p.2) volume := by
    rw [Measure.volume_eq_prod]
    exact hv₁.abs.mul_prod (integrable_jumpBound hα hα' hM₀ hM₂)
  refine hdom.mono' (((hv.comp measurable_fst).mul
    ((measurable_secondDiff_uncurry hφ.continuous.measurable j).mul
      (measurable_jumpWeight α))).aestronglyMeasurable) (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  simpa only [Real.norm_eq_abs] using
    norm_secondDiff_mul_rpow_le_jumpBound hφ h₀ h₂ α j p.1 p.2

/-- **The duality identity at a fixed step**: for `v` integrable and `φ` bounded and measurable,
`∫ (v(x + t e_j) − v(x)) (φ(x + t e_j) − φ(x)) dx = −∫ v(x) (φ(x + t e_j) + φ(x − t e_j) − 2 φ(x))
dx`, by the shift `x ↦ x − t e_j` in the cross term carrying the forward value of `v`. Every
`x`-integral here converges absolutely, since `v` is in `L¹` and `φ` is bounded. -/
theorem integral_jumpDiff_mul_eq {v : (Fin 2 → ℝ) → ℝ} (hv₁ : Integrable v volume) {M₀ : ℝ}
    (hφm : Measurable φ) (h₀ : ∀ x, |φ x| ≤ M₀) (j : Fin 2) (t : ℝ) :
    (∫ x, (v (x + t • Pi.single j 1) - v x) * (φ (x + t • Pi.single j 1) - φ x)) =
      -∫ x, v x * secondDiff φ j x t := by
  have hbd : ∀ a b : Fin 2 → ℝ, ‖φ a - φ b‖ ≤ 2 * M₀ := fun a b => by
    obtain ⟨h₁, h₂⟩ := abs_le.1 (h₀ a)
    obtain ⟨h₃, h₄⟩ := abs_le.1 (h₀ b)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hg₂ : Integrable (fun x => v x * (φ (x + t • Pi.single j 1) - φ x)) volume :=
    hv₁.mul_bdd ((hφm.comp (measurable_id.add_const _)).sub hφm).aestronglyMeasurable
      (ae_of_all _ fun x => hbd _ _)
  have hg₃ : Integrable (fun x => v x * (φ x - φ (x - t • Pi.single j 1))) volume :=
    hv₁.mul_bdd (hφm.sub (hφm.comp (measurable_id.sub_const _))).aestronglyMeasurable
      (ae_of_all _ fun x => hbd _ _)
  have hg₁ : Integrable (fun x => v (x + t • Pi.single j 1) *
      (φ (x + t • Pi.single j 1) - φ x)) volume := by
    have h := hg₃.comp_add_right (t • Pi.single j 1)
    simp only [add_sub_cancel_right] at h
    exact h
  have hshift : (∫ x, v (x + t • Pi.single j 1) * (φ (x + t • Pi.single j 1) - φ x)) =
      ∫ x, v x * (φ x - φ (x - t • Pi.single j 1)) := by
    have h := integral_add_right_eq_self (μ := (volume : Measure (Fin 2 → ℝ)))
      (fun y => v y * (φ y - φ (y - t • Pi.single j 1))) (t • Pi.single j 1)
    simp only [add_sub_cancel_right] at h
    exact h
  calc (∫ x, (v (x + t • Pi.single j 1) - v x) * (φ (x + t • Pi.single j 1) - φ x))
      = ∫ x, (v (x + t • Pi.single j 1) * (φ (x + t • Pi.single j 1) - φ x) -
          v x * (φ (x + t • Pi.single j 1) - φ x)) :=
        integral_congr_ae (ae_of_all _ fun x => by ring)
    _ = (∫ x, v (x + t • Pi.single j 1) * (φ (x + t • Pi.single j 1) - φ x)) -
          ∫ x, v x * (φ (x + t • Pi.single j 1) - φ x) := integral_sub hg₁ hg₂
    _ = (∫ x, v x * (φ x - φ (x - t • Pi.single j 1))) -
          ∫ x, v x * (φ (x + t • Pi.single j 1) - φ x) := by rw [hshift]
    _ = ∫ x, (v x * (φ x - φ (x - t • Pi.single j 1)) -
          v x * (φ (x + t • Pi.single j 1) - φ x)) := (integral_sub hg₃ hg₂).symm
    _ = ∫ x, -(v x * secondDiff φ j x t) :=
        integral_congr_ae (ae_of_all _ fun x => by simp only [secondDiff]; ring)
    _ = -∫ x, v x * secondDiff φ j x t := integral_neg _

/-- **Duality between the form and the generator**: for `v` measurable and integrable of finite
energy and `φ` a test function, `E(v, φ) = −∫ v A φ`. Each coordinate summand of the form is
turned into an iterated integral by Fubini, the `x`-integral at a fixed step is computed by
`integral_jumpDiff_mul_eq`, and Fubini in the other order recognises the generator. -/
theorem jumpForm_eq_neg_integral_jumpGen (hα : 0 < α) (hα' : α < 2) {v : (Fin 2 → ℝ) → ℝ}
    (hv : Measurable v) (hv₁ : Integrable v volume) (hvE : jumpEnergy α v ≠ ⊤)
    (hφ : IsTestFunction φ) : jumpForm α v φ = -∫ x, v x * jumpGen α φ x := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.1.of_le (by norm_cast)
  have hφm : Measurable φ := hφ.continuous.measurable
  obtain ⟨M₀, M₂, h₀, h₂⟩ := exists_bounds_of_hasCompactSupport hφ2 hφ.2
  have hφE : jumpEnergy α φ ≠ ⊤ := jumpEnergy_ne_top_of_isTestFunction hα hα' hφ
  -- the two integrands on `ℝ² × ℝ`, both integrable
  have hK : ∀ j : Fin 2, Integrable (fun p : (Fin 2 → ℝ) × ℝ =>
      v p.1 * (secondDiff φ j p.1 p.2 * |p.2| ^ (-(1 + α))))
      ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ)) := fun j => by
    rw [← Measure.volume_eq_prod]
    exact integrable_mul_secondDiff_mul_rpow hα hα' hv hv₁ hφ2 h₀ h₂ j
  have hJ : ∀ j : Fin 2, Integrable (fun p : (Fin 2 → ℝ) × ℝ =>
      (v (p.1 + p.2 • Pi.single j 1) - v p.1) * (φ (p.1 + p.2 • Pi.single j 1) - φ p.1) *
        |p.2| ^ (-(1 + α)))
      ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ)) := fun j => by
    rw [← Measure.volume_eq_prod]
    exact integrable_jumpFormIntegrand hv hφm hvE hφE j
  -- each coordinate summand of the form
  have hstep : ∀ j : Fin 2, (∫ p : (Fin 2 → ℝ) × ℝ,
      (v (p.1 + p.2 • Pi.single j 1) - v p.1) * (φ (p.1 + p.2 • Pi.single j 1) - φ p.1) *
        |p.2| ^ (-(1 + α))) =
      -∫ x, v x * ∫ t : ℝ, secondDiff φ j x t * |t| ^ (-(1 + α)) := by
    intro j
    have e1 : (∫ p : (Fin 2 → ℝ) × ℝ,
        (v (p.1 + p.2 • Pi.single j 1) - v p.1) * (φ (p.1 + p.2 • Pi.single j 1) - φ p.1) *
          |p.2| ^ (-(1 + α))) =
        ∫ t : ℝ, ∫ x, (v (x + t • Pi.single j 1) - v x) *
          (φ (x + t • Pi.single j 1) - φ x) * |t| ^ (-(1 + α)) := by
      have h := integral_prod_symm _ (hJ j)
      rwa [← Measure.volume_eq_prod] at h
    have e2 : (∫ p : (Fin 2 → ℝ) × ℝ,
        v p.1 * (secondDiff φ j p.1 p.2 * |p.2| ^ (-(1 + α)))) =
        ∫ t : ℝ, ∫ x, v x * (secondDiff φ j x t * |t| ^ (-(1 + α))) := by
      have h := integral_prod_symm _ (hK j)
      rwa [← Measure.volume_eq_prod] at h
    have e3 : (∫ p : (Fin 2 → ℝ) × ℝ,
        v p.1 * (secondDiff φ j p.1 p.2 * |p.2| ^ (-(1 + α)))) =
        ∫ x, v x * ∫ t : ℝ, secondDiff φ j x t * |t| ^ (-(1 + α)) := by
      have h : (∫ p : (Fin 2 → ℝ) × ℝ,
          v p.1 * (secondDiff φ j p.1 p.2 * |p.2| ^ (-(1 + α)))) =
          ∫ x, ∫ t : ℝ, v x * (secondDiff φ j x t * |t| ^ (-(1 + α))) := by
        have h' := integral_prod _ (hK j)
        rwa [← Measure.volume_eq_prod] at h'
      rw [h]
      exact integral_congr_ae (ae_of_all _ fun x =>
        integral_const_mul (v x) fun t : ℝ => secondDiff φ j x t * |t| ^ (-(1 + α)))
    have e4 : ∀ t : ℝ, (∫ x, (v (x + t • Pi.single j 1) - v x) *
        (φ (x + t • Pi.single j 1) - φ x) * |t| ^ (-(1 + α))) =
        -∫ x, v x * (secondDiff φ j x t * |t| ^ (-(1 + α))) := by
      intro t
      have hA : (∫ x, (v (x + t • Pi.single j 1) - v x) *
          (φ (x + t • Pi.single j 1) - φ x) * |t| ^ (-(1 + α))) =
          |t| ^ (-(1 + α)) * ∫ x, (v (x + t • Pi.single j 1) - v x) *
            (φ (x + t • Pi.single j 1) - φ x) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ fun x => by ring)
      have hB : (∫ x, v x * (secondDiff φ j x t * |t| ^ (-(1 + α)))) =
          |t| ^ (-(1 + α)) * ∫ x, v x * secondDiff φ j x t := by
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ fun x => by ring)
      rw [hA, hB, integral_jumpDiff_mul_eq hv₁ hφm h₀ j t]
      ring
    calc (∫ p : (Fin 2 → ℝ) × ℝ,
        (v (p.1 + p.2 • Pi.single j 1) - v p.1) * (φ (p.1 + p.2 • Pi.single j 1) - φ p.1) *
          |p.2| ^ (-(1 + α)))
        = ∫ t : ℝ, ∫ x, (v (x + t • Pi.single j 1) - v x) *
            (φ (x + t • Pi.single j 1) - φ x) * |t| ^ (-(1 + α)) := e1
      _ = ∫ t : ℝ, -∫ x, v x * (secondDiff φ j x t * |t| ^ (-(1 + α))) :=
          integral_congr_ae (ae_of_all _ e4)
      _ = -∫ t : ℝ, ∫ x, v x * (secondDiff φ j x t * |t| ^ (-(1 + α))) := integral_neg _
      _ = -∫ p : (Fin 2 → ℝ) × ℝ,
            v p.1 * (secondDiff φ j p.1 p.2 * |p.2| ^ (-(1 + α))) := by rw [e2]
      _ = -∫ x, v x * ∫ t : ℝ, secondDiff φ j x t * |t| ^ (-(1 + α)) := by rw [e3]
  -- the pairing with the generator splits over the two coordinates
  have hinner : ∀ j : Fin 2, Integrable (fun x => ∫ t : ℝ,
      v x * (secondDiff φ j x t * |t| ^ (-(1 + α)))) volume := fun j => (hK j).integral_prod_left
  have hint : ∀ j : Fin 2, Integrable (fun x =>
      v x * ∫ t : ℝ, secondDiff φ j x t * |t| ^ (-(1 + α))) volume := fun j =>
    (hinner j).congr (ae_of_all _ fun x =>
      integral_const_mul (v x) fun t : ℝ => secondDiff φ j x t * |t| ^ (-(1 + α)))
  have hlast : (∫ x, v x * jumpGen α φ x) =
      ∑ j : Fin 2, ∫ x, v x * ∫ t : ℝ, secondDiff φ j x t * |t| ^ (-(1 + α)) := by
    have hpt : ∀ x, v x * jumpGen α φ x =
        ∑ j : Fin 2, v x * ∫ t : ℝ, secondDiff φ j x t * |t| ^ (-(1 + α)) := fun x => by
      rw [jumpGen, Finset.mul_sum]
    rw [integral_congr_ae (ae_of_all _ hpt)]
    exact integral_finsetSum _ fun j _ => hint j
  rw [hlast, jumpForm, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => hstep j

/-! ### Two elementary inequalities -/

/-- A real number bounded by `S η + C η²` for every `η > 0` vanishes: taking
`η = min 1 (|D| / (2 (S + C + 1)))` makes the bound at most `|D| / 2`. -/
theorem eq_zero_of_abs_le_add_sq {D S C : ℝ} (hS : 0 ≤ S) (hC : 0 ≤ C)
    (h : ∀ η : ℝ, 0 < η → |D| ≤ S * η + C * η ^ 2) : D = 0 := by
  by_contra hD
  have hD0 : 0 < |D| := abs_pos.2 hD
  have hpos : (0 : ℝ) < 2 * (S + C + 1) := by linarith
  obtain ⟨η, hη⟩ : ∃ z : ℝ, z = min 1 (|D| / (2 * (S + C + 1))) := ⟨_, rfl⟩
  have hη0 : 0 < η := hη ▸ lt_min one_pos (div_pos hD0 hpos)
  have hη1 : η ≤ 1 := hη ▸ min_le_left _ _
  have hmul : η * (2 * (S + C + 1)) ≤ |D| :=
    (le_div_iff₀ hpos).1 (hη ▸ min_le_right _ _)
  have hsq : η ^ 2 ≤ η := by nlinarith
  nlinarith [h η hη0, mul_le_mul_of_nonneg_left hsq hC]

/-- A bounded weight sees only the `L¹` distance: if `|g| ≤ M` then the pairings of `g` with `w₁`
and with `w₂` differ by at most `M ∫ |w₁ − w₂|`. -/
theorem abs_integral_mul_sub_integral_mul_le {g w₁ w₂ : (Fin 2 → ℝ) → ℝ} {M : ℝ}
    (hgM : ∀ x, |g x| ≤ M) (h₁ : Integrable (fun x => g x * w₁ x) volume)
    (h₂ : Integrable (fun x => g x * w₂ x) volume)
    (hd : Integrable (fun x => w₁ x - w₂ x) volume) :
    |(∫ x, g x * w₁ x) - ∫ x, g x * w₂ x| ≤ M * ∫ x, |w₁ x - w₂ x| := by
  rw [← integral_sub h₁ h₂]
  calc |∫ x, (g x * w₁ x - g x * w₂ x)| ≤ ∫ x, |g x * w₁ x - g x * w₂ x| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, M * |w₁ x - w₂ x| := by
        refine integral_mono (h₁.sub h₂).abs (hd.abs.const_mul M) fun x => ?_
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_right (hgM x) (abs_nonneg _)
    _ = M * ∫ x, |w₁ x - w₂ x| := integral_const_mul _ _


/-! ### The energy identity -/

/-- **The energy identity**: for the minimiser `u` and the capped density `σ` of `exists_density`,
`E(u, u) = ∫ u (f − σ)`. The test-function identity is passed to the limit along the smooth
compactly supported approximants `ψ` of `u`: the form converges by Cauchy–Schwarz, since
`E(u, u − ψ)² ≤ E(u, u) E(u − ψ, u − ψ)` and the second factor is small, and the two source terms
converge because `f` and `σ` are bounded and `ψ → u` in `L¹`. -/
theorem jumpForm_self_eq_integral (hα : 0 < α) (hα' : α < 2) {Mf : ℝ} (hf2 : MemLp f 2 volume)
    (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ Mf) {u : EnergySpace α} (hufin : l1Norm u ≠ ⊤)
    {σ : (Fin 2 → ℝ) → ℝ} (hσm : Measurable σ) (hσ0 : ∀ x, 0 ≤ σ x) (hσκ : ∀ x, σ x ≤ κ)
    (hσT : ∀ (ψ : (Fin 2 → ℝ) → ℝ) (hψ : IsTestFunction ψ), ∫ x, σ x * ψ x =
      (∫ x, f x * ψ x) - jumpForm α ⇑u ⇑(ofTestFunction hα hα' hψ)) :
    jumpForm α ⇑u ⇑u = ∫ x, u x * (f x - σ x) := by
  have hfabs : ∀ x, |f x| ≤ Mf := fun x => abs_le.2 ⟨by linarith [hf0 x, hfM x], hfM x⟩
  have hσabs : ∀ x, |σ x| ≤ κ := fun x => abs_le.2 ⟨by linarith [hσ0 x, hσκ x], hσκ x⟩
  have hum : Measurable ⇑u := measurable_coeFn u
  have hu₁ : Integrable ⇑u volume := integrable_of_l1Norm_ne_top hufin
  have hu2 : MemLp ⇑u 2 volume := Lp.memLp (u : L²)
  have huE : jumpEnergy α ⇑u ≠ ⊤ := u.jumpEnergy_ne_top
  have hEu : 0 ≤ jumpForm α ⇑u ⇑u := jumpForm_self_nonneg α ⇑u
  have hMf : 0 ≤ Mf := (hf0 0).trans (hfM 0)
  have hκ : 0 ≤ κ := (hσ0 0).trans (hσκ 0)
  have hσbd : ∀ᵐ x ∂(volume : Measure (Fin 2 → ℝ)), ‖σ x‖ ≤ κ :=
    ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hσabs x
  have hfu : Integrable (fun x => f x * ⇑u x) volume := hf2.integrable_mul hu2
  have hσu : Integrable (fun x => σ x * ⇑u x) volume :=
    hu₁.bdd_mul hσm.aestronglyMeasurable hσbd
  -- the approximation bound, with an arbitrary `η > 0`
  have hkey : ∀ η : ℝ, 0 < η →
      |jumpForm α ⇑u ⇑u - ((∫ x, f x * ⇑u x) - ∫ x, σ x * ⇑u x)| ≤
        √(jumpForm α ⇑u ⇑u) * η + (Mf + κ) * η ^ 2 := by
    intro η hη
    obtain ⟨ψ, hψc, hψk, hψE, hψ₁, -⟩ := exists_contDiff_hasCompactSupport_approx hα hα'
      hum hu₁ hu2 huE (by positivity : (0 : ℝ) < η ^ 2)
    have hψ : IsTestFunction ψ := ⟨hψc, hψk⟩
    have hψm : Measurable ψ := hψ.continuous.measurable
    have hψEfin : jumpEnergy α ψ ≠ ⊤ := jumpEnergy_ne_top_of_isTestFunction hα hα' hψ
    have hψint : Integrable ψ volume := integrable_of_isTestFunction hψ
    have hd : Integrable (fun x => ⇑u x - ψ x) volume := hu₁.sub hψint
    have hdE : jumpEnergy α (⇑u - ψ) ≠ ⊤ := hψE.ne_top
    -- the `L¹` error
    have hL1 : (∫ x, |⇑u x - ψ x|) ≤ η ^ 2 := by
      have h := integral_norm_eq_lintegral_enorm (f := fun x => ⇑u x - ψ x)
        hd.aestronglyMeasurable
      calc (∫ x, |⇑u x - ψ x|) = (∫⁻ x, ‖⇑u x - ψ x‖ₑ).toReal := by
            simpa only [Real.norm_eq_abs] using h
        _ ≤ η ^ 2 := ENNReal.toReal_le_of_le_ofReal (by positivity) hψ₁.le
    -- the form converges by Cauchy–Schwarz
    have hAeq : jumpForm α ⇑u (⇑u - ψ) = jumpForm α ⇑u ⇑u - jumpForm α ⇑u ψ := by
      rw [jumpForm_comm α ⇑u (⇑u - ψ), jumpForm_sub_left α hum hψm hum huE hψEfin huE,
        jumpForm_comm α ψ ⇑u]
    have hqf : jumpForm α (⇑u - ψ) (⇑u - ψ) ≤ η ^ 2 := by
      have hq : ENNReal.ofReal (jumpForm α (⇑u - ψ) (⇑u - ψ)) = jumpEnergy α (⇑u - ψ) :=
        jumpForm_self α (hum.sub hψm) hdE
      refine (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 ?_
      rw [hq]
      exact hψE.le
    have hcs : jumpForm α ⇑u (⇑u - ψ) ^ 2 ≤
        jumpForm α ⇑u ⇑u * jumpForm α (⇑u - ψ) (⇑u - ψ) :=
      jumpForm_sq_le α hum (hum.sub hψm) huE hdE
    have hA : |jumpForm α ⇑u ⇑u - jumpForm α ⇑u ψ| ≤ √(jumpForm α ⇑u ⇑u) * η := by
      rw [← hAeq]
      have h1 : jumpForm α ⇑u (⇑u - ψ) ^ 2 ≤ (√(jumpForm α ⇑u ⇑u) * η) ^ 2 := by
        have h2 : (√(jumpForm α ⇑u ⇑u) * η) ^ 2 = jumpForm α ⇑u ⇑u * η ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hEu]
        rw [h2]
        exact hcs.trans (mul_le_mul_of_nonneg_left hqf hEu)
      calc |jumpForm α ⇑u (⇑u - ψ)| = √(jumpForm α ⇑u (⇑u - ψ) ^ 2) :=
            (Real.sqrt_sq_eq_abs _).symm
        _ ≤ √((√(jumpForm α ⇑u ⇑u) * η) ^ 2) := Real.sqrt_le_sqrt h1
        _ = √(jumpForm α ⇑u ⇑u) * η :=
            Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hη.le)
    -- the two source terms converge
    have hB : |(∫ x, f x * ⇑u x) - ∫ x, f x * ψ x| ≤ Mf * η ^ 2 := by
      refine (abs_integral_mul_sub_integral_mul_le hfabs hfu
        (hf2.integrable_mul (memLp_two_of_isTestFunction hψ)) hd).trans ?_
      exact mul_le_mul_of_nonneg_left hL1 hMf
    have hC : |(∫ x, σ x * ⇑u x) - ∫ x, σ x * ψ x| ≤ κ * η ^ 2 := by
      refine (abs_integral_mul_sub_integral_mul_le hσabs hσu
        (hψint.bdd_mul hσm.aestronglyMeasurable hσbd) hd).trans ?_
      exact mul_le_mul_of_nonneg_left hL1 hκ
    have hid : jumpForm α ⇑u ψ = (∫ x, f x * ψ x) - ∫ x, σ x * ψ x := by
      have h := hσT ψ hψ
      rw [jumpForm_coeFn_ofTestFunction hα hα' hψ] at h
      linarith
    obtain ⟨hA1, hA2⟩ := abs_le.1 hA
    obtain ⟨hB1, hB2⟩ := abs_le.1 hB
    obtain ⟨hC1, hC2⟩ := abs_le.1 hC
    rw [abs_le]
    constructor <;> nlinarith [hid]
  have hD : jumpForm α ⇑u ⇑u - ((∫ x, f x * ⇑u x) - ∫ x, σ x * ⇑u x) = 0 :=
    eq_zero_of_abs_le_add_sq (Real.sqrt_nonneg _) (by linarith) hkey
  have hsplit : (∫ x, ⇑u x * (f x - σ x)) = (∫ x, f x * ⇑u x) - ∫ x, σ x * ⇑u x := by
    rw [← integral_sub hfu hσu]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [hsplit]
  linarith

/-! ### The scaling identity -/

/-- **The scaling identity**: the variational inequality tested against the two competitors `2 u`
and `0` gives `E(u, u) + κ ‖u‖₁ − ∫ f u = 0`, since both competitors are admissible and both
variations are exactly `± u`. -/
theorem jumpForm_self_add_l1_eq (hf : MemLp f 2 volume) {u : EnergySpace α}
    (hu : u ∈ nonnegCone α) (hufin : l1Norm u ≠ ⊤)
    (hmin : ∀ v ∈ nonnegCone α, l1Norm v ≠ ⊤ → obstacleFun α κ f u ≤ obstacleFun α κ f v) :
    jumpForm α ⇑u ⇑u + κ * (l1Norm u).toReal - ∫ x, f x * u x = 0 := by
  -- the competitor `2 u`
  have h2cone : (2 : ℝ) • u ∈ nonnegCone α := smul_mem_nonnegCone (by norm_num) hu
  have h2fin : l1Norm ((2 : ℝ) • u) ≠ ⊤ := by
    rw [l1Norm_smul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hufin
  have h2real : (l1Norm ((2 : ℝ) • u)).toReal = 2 * (l1Norm u).toReal := by
    rw [l1Norm_smul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
  have hsub2 : (2 : ℝ) • u - u = u := by module
  have hint2 : (∫ x, f x * (⇑((2 : ℝ) • u) x - ⇑u x)) = ∫ x, f x * u x := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_smul_ae (2 : ℝ) u] with x hx
    rw [hx]
    ring
  have hv1 := variational_inequality hf hu hufin hmin h2cone h2fin
  rw [hsub2, h2real, hint2] at hv1
  -- the competitor `0`
  have h0cone : (0 : EnergySpace α) ∈ nonnegCone α := mem_nonnegCone.2 toLp_zero.ge
  have h0fin : l1Norm (0 : EnergySpace α) ≠ ⊤ := by
    rw [l1Norm_zero]
    exact ENNReal.zero_ne_top
  have hint0 : (∫ x, f x * (⇑(0 : EnergySpace α) x - ⇑u x)) = -∫ x, f x * u x := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_zero_ae α] with x hx
    rw [hx, Pi.zero_apply]
    ring
  have hv0 := variational_inequality hf hu hufin hmin h0cone h0fin
  rw [zero_sub, jumpForm_coeFn_neg_right, l1Norm_zero, ENNReal.toReal_zero, hint0] at hv0
  linarith

/-! ### Complementarity -/

/-- **Complementarity**: combining the energy identity with the scaling identity gives
`∫ u (κ − σ) = 0`. -/
theorem integral_mul_sub_eq_zero (hα : 0 < α) (hα' : α < 2) {Mf : ℝ} (hf2 : MemLp f 2 volume)
    (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ Mf) {u : EnergySpace α} (hu : u ∈ nonnegCone α)
    (hufin : l1Norm u ≠ ⊤)
    (hmin : ∀ v ∈ nonnegCone α, l1Norm v ≠ ⊤ → obstacleFun α κ f u ≤ obstacleFun α κ f v)
    {σ : (Fin 2 → ℝ) → ℝ} (hσm : Measurable σ) (hσ0 : ∀ x, 0 ≤ σ x) (hσκ : ∀ x, σ x ≤ κ)
    (hσT : ∀ (ψ : (Fin 2 → ℝ) → ℝ) (hψ : IsTestFunction ψ), ∫ x, σ x * ψ x =
      (∫ x, f x * ψ x) - jumpForm α ⇑u ⇑(ofTestFunction hα hα' hψ)) :
    ∫ x, u x * (κ - σ x) = 0 := by
  have hσabs : ∀ x, |σ x| ≤ κ := fun x => abs_le.2 ⟨by linarith [hσ0 x, hσκ x], hσκ x⟩
  have hu₁ : Integrable ⇑u volume := integrable_of_l1Norm_ne_top hufin
  have hu2 : MemLp ⇑u 2 volume := Lp.memLp (u : L²)
  have hσbd : ∀ᵐ x ∂(volume : Measure (Fin 2 → ℝ)), ‖σ x‖ ≤ κ :=
    ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hσabs x
  have hfu : Integrable (fun x => f x * ⇑u x) volume := hf2.integrable_mul hu2
  have hσu : Integrable (fun x => σ x * ⇑u x) volume :=
    hu₁.bdd_mul hσm.aestronglyMeasurable hσbd
  have h2 := jumpForm_self_eq_integral hα hα' hf2 hf0 hfM hufin hσm hσ0 hσκ hσT
  have h3 := jumpForm_self_add_l1_eq hf2 hu hufin hmin
  have hL : (l1Norm u).toReal = ∫ x, u x := toReal_l1Norm hu
  have hsplit : (∫ x, ⇑u x * (f x - σ x)) = (∫ x, f x * ⇑u x) - ∫ x, σ x * ⇑u x := by
    rw [← integral_sub hfu hσu]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  have hgoal : (∫ x, ⇑u x * (κ - σ x)) = κ * (∫ x, ⇑u x) - ∫ x, σ x * ⇑u x := by
    rw [← integral_const_mul, ← integral_sub (hu₁.const_mul κ) hσu]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [hsplit] at h2
  rw [hL] at h3
  rw [hgoal]
  linarith

/-- **The pointwise form of complementarity**: the density saturates its cap almost everywhere on
the contact set `{u > 0}`, because the nonnegative integrand `u (κ − σ)` has vanishing
integral. -/
theorem ae_eq_of_pos (hα : 0 < α) (hα' : α < 2) {Mf : ℝ} (hf2 : MemLp f 2 volume)
    (hf0 : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ Mf) {u : EnergySpace α} (hu : u ∈ nonnegCone α)
    (hufin : l1Norm u ≠ ⊤)
    (hmin : ∀ v ∈ nonnegCone α, l1Norm v ≠ ⊤ → obstacleFun α κ f u ≤ obstacleFun α κ f v)
    {σ : (Fin 2 → ℝ) → ℝ} (hσm : Measurable σ) (hσ0 : ∀ x, 0 ≤ σ x) (hσκ : ∀ x, σ x ≤ κ)
    (hσT : ∀ (ψ : (Fin 2 → ℝ) → ℝ) (hψ : IsTestFunction ψ), ∫ x, σ x * ψ x =
      (∫ x, f x * ψ x) - jumpForm α ⇑u ⇑(ofTestFunction hα hα' hψ)) :
    ∀ᵐ x ∂(volume : Measure (Fin 2 → ℝ)), 0 < u x → σ x = κ := by
  have hκ : 0 ≤ κ := (hσ0 0).trans (hσκ 0)
  have hu₁ : Integrable ⇑u volume := integrable_of_l1Norm_ne_top hufin
  have hσbd : ∀ᵐ x ∂(volume : Measure (Fin 2 → ℝ)), ‖κ - σ x‖ ≤ 2 * κ := by
    refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hσ0 x, hσκ x]
  have hint : Integrable (fun x => ⇑u x * (κ - σ x)) volume :=
    hu₁.mul_bdd (measurable_const.sub hσm).aestronglyMeasurable hσbd
  have hnn : 0 ≤ᵐ[volume] fun x => ⇑u x * (κ - σ x) := by
    filter_upwards [nonneg_ae_of_mem_nonnegCone hu] with x hx
    exact mul_nonneg hx (by linarith [hσκ x])
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1
    (integral_mul_sub_eq_zero hα hα' hf2 hf0 hfM hu hufin hmin hσm hσ0 hσκ hσT)
  filter_upwards [hz] with x hxz
  intro hpos
  have hxz' : ⇑u x * (κ - σ x) = 0 := hxz
  rcases mul_eq_zero.1 hxz' with h' | h'
  · exact absurd h' (ne_of_gt hpos)
  · linarith

/-! ### Mass conservation -/

/-- The dilate `x ↦ φ (R⁻¹ x)` of a test function by `R > 0` is a test function: it is the
composition with a linear map, and its support is the dilate of the support of `φ`. -/
theorem isTestFunction_comp_smul_inv {R : ℝ} (hR : 0 < R) (hφ : IsTestFunction φ) :
    IsTestFunction fun x : Fin 2 → ℝ => φ (R⁻¹ • x) := by
  obtain ⟨r, hr⟩ := hφ.2.isBounded.subset_closedBall (0 : Fin 2 → ℝ)
  refine ⟨hφ.1.comp (contDiff_const_smul (R⁻¹ : ℝ)), HasCompactSupport.intro
    (isCompact_closedBall (0 : Fin 2 → ℝ) (R * max r 0)) fun x hx => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun h => hx ?_
  have h₁ : ‖R⁻¹ • x‖ ≤ r := mem_closedBall_zero_iff.1 (hr h)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)] at h₁
  have h₂ := mul_le_mul_of_nonneg_left h₁ hR.le
  rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul] at h₂
  exact mem_closedBall_zero_iff.2
    (h₂.trans (mul_le_mul_of_nonneg_left (le_max_left r 0) hR.le))

/-- **Mass conservation**: the capped density is integrable and has the same total mass as the
obstacle. The test functions are the dilates `χ_R = χ(R⁻¹ ·)` of a fixed bump `χ` equal to `1` on
the unit ball: the generator of a dilate is `O(R^{−α})` by the scaling law of
`CenteredMaximal.Analysis.JumpGenerator`, so the form term is negligible, monotone convergence
over the balls `B(0, n)` shows that `σ` is integrable, and dominated convergence identifies the
limits of the two source terms. -/
theorem integrable_and_integral_density_eq (hα : 0 < α) (hα' : α < 2)
    (hf₁ : Integrable f volume) (hf0 : ∀ x, 0 ≤ f x) {u : EnergySpace α} (hufin : l1Norm u ≠ ⊤)
    {σ : (Fin 2 → ℝ) → ℝ} (hσm : Measurable σ) (hσ0 : ∀ x, 0 ≤ σ x) (hσκ : ∀ x, σ x ≤ κ)
    (hσT : ∀ (ψ : (Fin 2 → ℝ) → ℝ) (hψ : IsTestFunction ψ), ∫ x, σ x * ψ x =
      (∫ x, f x * ψ x) - jumpForm α ⇑u ⇑(ofTestFunction hα hα' hψ)) :
    Integrable σ volume ∧ ∫ x, σ x = ∫ x, f x := by
  have hum : Measurable ⇑u := measurable_coeFn u
  have hu₁ : Integrable ⇑u volume := integrable_of_l1Norm_ne_top hufin
  have huE : jumpEnergy α ⇑u ≠ ⊤ := u.jumpEnergy_ne_top
  -- a fixed bump equal to one on the unit ball
  obtain ⟨χ, hχ, hχ0, hχ1⟩ :=
    exists_isTestFunction_eq_one_of_isCompact (isCompact_closedBall (0 : Fin 2 → ℝ) 1)
  have hχ2 : ContDiff ℝ 2 χ := hχ.1.of_le (by norm_cast)
  obtain ⟨M₀, M₂, h₀, h₂⟩ := exists_bounds_of_hasCompactSupport hχ2 hχ.2
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h₀ 0)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (h₂ 0)
  obtain ⟨C, hC⟩ : ∃ z : ℝ, z = 2 * (2 * M₂ / (2 - α) + 8 * M₀ / α) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    have hd₁ : 0 ≤ 2 * M₂ / (2 - α) := div_nonneg (by linarith) (by linarith)
    have hd₂ : 0 ≤ 8 * M₀ / α := div_nonneg (by linarith) hα.le
    rw [hC]
    linarith
  -- the dilates are test functions equal to one on the ball of radius `R`
  have hχR : ∀ R : ℝ, 0 < R → IsTestFunction fun x : Fin 2 → ℝ => χ (R⁻¹ • x) :=
    fun _ hR => isTestFunction_comp_smul_inv hR hχ
  have hχone : ∀ R : ℝ, 0 < R → ∀ x : Fin 2 → ℝ, ‖x‖ ≤ R → χ (R⁻¹ • x) = 1 := by
    intro R hR x hx
    refine hχ1 _ (mem_closedBall_zero_iff.2 ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
    have h := mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hR.le)
    rwa [inv_mul_cancel₀ hR.ne'] at h
  -- the form against a dilate is `O(R^{−α})`
  have hform : ∀ R : ℝ, 0 < R →
      |jumpForm α ⇑u fun y : Fin 2 → ℝ => χ (R⁻¹ • y)| ≤ (∫ x, |⇑u x|) * (R ^ (-α) * C) := by
    intro R hR
    rw [jumpForm_eq_neg_integral_jumpGen hα hα' hum hu₁ huE (hχR R hR), abs_neg,
      ← Real.norm_eq_abs]
    calc ‖∫ x, ⇑u x * jumpGen α (fun y : Fin 2 → ℝ => χ (R⁻¹ • y)) x‖
        ≤ ∫ x, |⇑u x| * (R ^ (-α) * C) := by
          refine norm_integral_le_of_norm_le (hu₁.abs.mul_const _) (ae_of_all _ fun x => ?_)
          rw [Real.norm_eq_abs, abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [hC]
          exact abs_jumpGen_comp_smul_inv_le hα hα' hχ2 h₀ h₂ hR x
      _ = (∫ x, |⇑u x|) * (R ^ (-α) * C) := integral_mul_const _ _
  -- the source term against a dilate is bounded by the mass of the obstacle
  have hsrc : ∀ R : ℝ, 0 < R → (∫ x, f x * χ (R⁻¹ • x)) ≤ M₀ * ∫ x, f x := by
    intro R hR
    have hint : Integrable (fun x => f x * χ (R⁻¹ • x)) volume :=
      hf₁.mul_bdd (hχR R hR).continuous.aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact h₀ _)
    rw [← integral_const_mul]
    refine integral_mono hint (hf₁.const_mul M₀) fun x => ?_
    nlinarith [hf0 x, (abs_le.1 (h₀ (R⁻¹ • x))).2]
  have hσχ : ∀ R : ℝ, 0 < R → Integrable (fun x => σ x * χ (R⁻¹ • x)) volume := fun R hR =>
    (integrable_of_isTestFunction (hχR R hR)).bdd_mul hσm.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hσ0 x)]; exact hσκ x)
  have hdil : ∀ R : ℝ, 0 < R → (∫ x, σ x * χ (R⁻¹ • x)) =
      (∫ x, f x * χ (R⁻¹ • x)) - jumpForm α ⇑u fun y : Fin 2 → ℝ => χ (R⁻¹ • y) := by
    intro R hR
    have h := hσT (fun y : Fin 2 → ℝ => χ (R⁻¹ • y)) (hχR R hR)
    rwa [jumpForm_coeFn_ofTestFunction hα hα' (hχR R hR)] at h
  -- a bound on the mass of `σ` over every ball
  obtain ⟨B, hB⟩ : ∃ z : ℝ, z = M₀ * (∫ x, f x) + (∫ x, |⇑u x|) * C := ⟨_, rfl⟩
  have hbdd : ∀ R : ℝ, 1 ≤ R → (∫ x, σ x * χ (R⁻¹ • x)) ≤ B := by
    intro R hR1
    have hR : (0 : ℝ) < R := by linarith
    have hrp : R ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR1 (by linarith)
    have hN : 0 ≤ ∫ x, |⇑u x| := integral_nonneg fun x => abs_nonneg _
    obtain ⟨hfo1, hfo2⟩ := abs_le.1 (hform R hR)
    have hmono : (∫ x, |⇑u x|) * (R ^ (-α) * C) ≤ (∫ x, |⇑u x|) * C := by
      refine mul_le_mul_of_nonneg_left ?_ hN
      nlinarith
    rw [hdil R hR, hB]
    linarith [hsrc R hR]
  have hRpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hRone : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n =>
    le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hball : ∀ n : ℕ,
      (∫⁻ x in closedBall (0 : Fin 2 → ℝ) (n : ℝ), ENNReal.ofReal (σ x)) ≤
        ENNReal.ofReal B := by
    intro n
    calc (∫⁻ x in closedBall (0 : Fin 2 → ℝ) (n : ℝ), ENNReal.ofReal (σ x))
        = ∫⁻ x in closedBall (0 : Fin 2 → ℝ) (n : ℝ),
            ENNReal.ofReal (σ x * χ (((n : ℝ) + 1)⁻¹ • x)) := by
          refine setLIntegral_congr_fun measurableSet_closedBall fun x hx => ?_
          rw [hχone _ (hRpos n) x (by
            have h := mem_closedBall_zero_iff.1 hx
            linarith), mul_one]
      _ ≤ ∫⁻ x, ENNReal.ofReal (σ x * χ (((n : ℝ) + 1)⁻¹ • x)) :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (∫ x, σ x * χ (((n : ℝ) + 1)⁻¹ • x)) :=
          (ofReal_integral_eq_lintegral_ofReal (hσχ _ (hRpos n))
            (ae_of_all _ fun x => mul_nonneg (hσ0 x) (hχ0 _))).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hbdd _ (hRone n))
  -- monotone convergence: `σ` is integrable
  have hlint : (∫⁻ x, ENNReal.ofReal (σ x)) ≤ ENNReal.ofReal B := by
    have hmeas : ∀ n : ℕ, Measurable ((closedBall (0 : Fin 2 → ℝ) (n : ℝ)).indicator
        fun x => ENNReal.ofReal (σ x)) :=
      fun _ => hσm.ennreal_ofReal.indicator measurableSet_closedBall
    have hmono : Monotone fun n : ℕ => (closedBall (0 : Fin 2 → ℝ) (n : ℝ)).indicator
        fun x => ENNReal.ofReal (σ x) := by
      intro m n hmn x
      exact indicator_le_indicator_of_subset
        (closedBall_subset_closedBall (by exact_mod_cast hmn)) (fun _ => zero_le) x
    calc (∫⁻ x, ENNReal.ofReal (σ x))
        = ∫⁻ x, ⨆ n : ℕ, (closedBall (0 : Fin 2 → ℝ) (n : ℝ)).indicator
            (fun x => ENNReal.ofReal (σ x)) x := by
          refine lintegral_congr fun x => ?_
          obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
          refine le_antisymm (le_iSup_of_le n ?_) (iSup_le fun _ => indicator_le_self _ _ x)
          rw [indicator_of_mem (by simpa [mem_closedBall, dist_eq_norm] using hn)]
      _ = ⨆ n : ℕ, ∫⁻ x, (closedBall (0 : Fin 2 → ℝ) (n : ℝ)).indicator
            (fun x => ENNReal.ofReal (σ x)) x := lintegral_iSup hmeas hmono
      _ = ⨆ n : ℕ, ∫⁻ x in closedBall (0 : Fin 2 → ℝ) (n : ℝ), ENNReal.ofReal (σ x) :=
          iSup_congr fun _ => lintegral_indicator measurableSet_closedBall _
      _ ≤ ENNReal.ofReal B := iSup_le hball
  have hσint : Integrable σ volume := by
    refine ⟨hσm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hσ0)]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  refine ⟨hσint, ?_⟩
  -- dominated convergence for the two source terms
  have hσlim : Filter.Tendsto (fun n : ℕ => ∫ x, σ x * χ (((n : ℝ) + 1)⁻¹ • x))
      Filter.atTop (nhds (∫ x, σ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => M₀ * σ x)
      (fun n => (hσχ _ (hRpos n)).aestronglyMeasurable) (hσint.const_mul M₀)
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hσ0 x) (hχ0 _))]
      calc σ x * χ (((n : ℝ) + 1)⁻¹ • x) ≤ σ x * M₀ :=
            mul_le_mul_of_nonneg_left (abs_le.1 (h₀ _)).2 (hσ0 x)
        _ = M₀ * σ x := mul_comm _ _
    · obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
      have heq : (fun n : ℕ => σ x * χ (((n : ℝ) + 1)⁻¹ • x)) =ᶠ[Filter.atTop]
          fun _ : ℕ => σ x := by
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        rw [hχone _ (hRpos n) x (by
          have hNn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
          linarith), mul_one]
      exact tendsto_const_nhds.congr' heq.symm
  have hflim : Filter.Tendsto (fun n : ℕ => ∫ x, f x * χ (((n : ℝ) + 1)⁻¹ • x))
      Filter.atTop (nhds (∫ x, f x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => M₀ * |f x|)
      (fun n => hf₁.aestronglyMeasurable.mul
        (hχR _ (hRpos n)).continuous.aestronglyMeasurable) (hf₁.abs.const_mul M₀)
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      calc |f x| * |χ (((n : ℝ) + 1)⁻¹ • x)| ≤ |f x| * M₀ :=
            mul_le_mul_of_nonneg_left (h₀ _) (abs_nonneg _)
        _ = M₀ * |f x| := mul_comm _ _
    · obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
      have heq : (fun n : ℕ => f x * χ (((n : ℝ) + 1)⁻¹ • x)) =ᶠ[Filter.atTop]
          fun _ : ℕ => f x := by
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        rw [hχone _ (hRpos n) x (by
          have hNn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
          linarith), mul_one]
      exact tendsto_const_nhds.congr' heq.symm
  -- the form term is negligible
  have hJlim : Filter.Tendsto
      (fun n : ℕ => jumpForm α ⇑u fun y : Fin 2 → ℝ => χ (((n : ℝ) + 1)⁻¹ • y))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-α)) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hα).comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    have hg : Filter.Tendsto
        (fun n : ℕ => (∫ x, |⇑u x|) * (((n : ℝ) + 1) ^ (-α) * C)) Filter.atTop (nhds 0) := by
      simpa using (h0.mul_const C).const_mul (∫ x, |⇑u x|)
    refine squeeze_zero_norm (fun n => ?_) hg
    rw [Real.norm_eq_abs]
    exact hform _ (hRpos n)
  have hlim2 : Filter.Tendsto (fun n : ℕ => ∫ x, σ x * χ (((n : ℝ) + 1)⁻¹ • x))
      Filter.atTop (nhds ((∫ x, f x) - 0)) :=
    (hflim.sub hJlim).congr fun n => (hdil _ (hRpos n)).symm
  have hmass := tendsto_nhds_unique hσlim hlim2
  linarith

/-! ### The contact-set bound -/

/-- **The contact-set bound**: the density saturates its cap on the contact set `{u > 0}`, so the
mass `∫ f` of the obstacle bounds `κ` times the measure of that set. -/
theorem volume_pos_lt_le (hα : 0 < α) (hα' : α < 2) (hκ : 0 < κ) {Mf : ℝ}
    (hf₁ : Integrable f volume) (hf2 : MemLp f 2 volume) (hf0 : ∀ x, 0 ≤ f x)
    (hfM : ∀ x, f x ≤ Mf) {u : EnergySpace α} (hu : u ∈ nonnegCone α) (hufin : l1Norm u ≠ ⊤)
    (hmin : ∀ v ∈ nonnegCone α, l1Norm v ≠ ⊤ → obstacleFun α κ f u ≤ obstacleFun α κ f v)
    {σ : (Fin 2 → ℝ) → ℝ} (hσm : Measurable σ) (hσ0 : ∀ x, 0 ≤ σ x) (hσκ : ∀ x, σ x ≤ κ)
    (hσT : ∀ (ψ : (Fin 2 → ℝ) → ℝ) (hψ : IsTestFunction ψ), ∫ x, σ x * ψ x =
      (∫ x, f x * ψ x) - jumpForm α ⇑u ⇑(ofTestFunction hα hα' hψ)) :
    volume {x : Fin 2 → ℝ | 0 < u x} ≤ ENNReal.ofReal ((∫ x, f x) / κ) := by
  obtain ⟨hσint, hmass⟩ :=
    integrable_and_integral_density_eq hα hα' hf₁ hf0 hufin hσm hσ0 hσκ hσT
  have hae := ae_eq_of_pos hα hα' hf2 hf0 hfM hu hufin hmin hσm hσ0 hσκ hσT
  have hS : MeasurableSet {x : Fin 2 → ℝ | 0 < ⇑u x} :=
    measurableSet_lt measurable_const (measurable_coeFn u)
  have hkey : volume {x : Fin 2 → ℝ | 0 < ⇑u x} * ENNReal.ofReal κ ≤
      ENNReal.ofReal (∫ x, f x) := by
    calc volume {x : Fin 2 → ℝ | 0 < ⇑u x} * ENNReal.ofReal κ
        = ∫⁻ _ in {x : Fin 2 → ℝ | 0 < ⇑u x}, ENNReal.ofReal κ := by
          rw [setLIntegral_const, mul_comm]
      _ = ∫⁻ x in {x : Fin 2 → ℝ | 0 < ⇑u x}, ENNReal.ofReal (σ x) := by
          refine setLIntegral_congr_fun_ae hS ?_
          filter_upwards [hae] with x hx hxS
          rw [hx hxS]
      _ ≤ ∫⁻ x, ENNReal.ofReal (σ x) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (∫ x, σ x) :=
          (ofReal_integral_eq_lintegral_ofReal hσint (ae_of_all _ hσ0)).symm
      _ = ENNReal.ofReal (∫ x, f x) := by rw [hmass]
  rw [ENNReal.ofReal_div_of_pos hκ,
    ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hκ).ne')
      (Or.inl ENNReal.ofReal_ne_top)]
  exact hkey

end CenteredMaximal

end
