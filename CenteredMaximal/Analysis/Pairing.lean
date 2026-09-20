/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.BoundedFunctional
public import CenteredMaximal.Analysis.JumpGenerator

/-!
# Self-adjointness of the jump pairing

Fix `0 < α < 2`, a bounded measurable function `g` on the plane and a test function `φ`. This
file moves the coordinate jump generator `jumpGen α` of
`CenteredMaximal.Analysis.JumpGenerator` from `φ` onto `g` inside the pairing
`∫ g · jumpGen α φ`, so that pointwise lower bounds on `jumpGen α g` turn into the weak
statement `0 ≤ ∫ g · jumpGen α φ` for nonnegative test functions `φ`.

* `integrable_bdd_mul_secondDiff_mul_rpow`: the integrand
  `g(z) (φ(z + t e_j) + φ(z − t e_j) − 2 φ(z)) |t|^{−(1+α)}` is integrable on `ℝ² × ℝ`. At a
  fixed step `t` it vanishes off the union of the three translates `tsupport φ ∓ t e_j` and
  `tsupport φ`, whose measure is at most `3 |tsupport φ|` for *every* `t`, and it is bounded by
  `C · jumpBound α M₀ M₂ t`; Tonelli then gives the finiteness. This is where boundedness of
  `g` is used, in place of the integrability assumed in `Obstacle.Complementarity`;
* `integral_mul_secondDiff_eq_integral_secondDiff_mul`: at a fixed step the second difference
  moves from `φ` onto `g`, by the shifts `z ↦ z ∓ t e_j`;
* `integral_mul_jumpGen_eq_integral_integral`: **the easy direction**,
  `∫ g A φ = ∑_j ∫ (∫ (Δ_j^t g) φ) |t|^{−(1+α)} dt`, valid for every bounded measurable `g`;
* `integral_mul_jumpGen_comm`: **self-adjointness** `∫ g A φ = ∫ (A g) φ`, under the explicit
  hypothesis that the double integral of the right-hand side converges absolutely. For a merely
  Lipschitz `g` this is not automatic — `∫_{|t| ≤ 1} |t| · |t|^{−2} dt` diverges — so the
  hypothesis must be checked separately for each `g` of interest;
* `nonneg_integral_mul_jumpGen`: consequently `0 ≤ ∫ g A φ` for `0 ≤ φ` as soon as `A g ≥ 0`
  almost everywhere;
* `integrable_uncurry_of_bound`: a checkable sufficient condition for that hypothesis, namely a
  pointwise-in-`z` bound `B` on the inner `t`-integral which is integrable on `tsupport φ`;
* `lintegral_secondDiff_le_of_lipschitz_of_c2`: the bound `B` for a bounded Lipschitz function
  which is quadratically flat at `z` only up to the scale `δ`,
  `∫ |Δ_j^t g(z)| t^{−2} dt ≤ 2 M₂ δ + 4 L log(1/δ) + 8 C`, by splitting the step range into
  `|t| ≤ δ`, `δ < |t| ≤ 1` and `|t| > 1`. Downstream `δ` is the distance from `z` to a kink set
  of `g`, and `log (1 / dist)` is locally integrable in the plane.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace CenteredMaximal

variable {α : ℝ} {g φ : (Fin 2 → ℝ) → ℝ}

/-! ### Measurability and translations -/

/-- The second difference is jointly measurable in the base point and the step. -/
private theorem measurable_secondDiff_prod (hg : Measurable g) (j : Fin 2) :
    Measurable fun p : (Fin 2 → ℝ) × ℝ => secondDiff g j p.1 p.2 := by
  unfold secondDiff
  exact ((hg.comp (measurable_fst.add (measurable_snd.smul_const _))).add
    (hg.comp (measurable_fst.sub (measurable_snd.smul_const _)))).sub
    (measurable_const.mul (hg.comp measurable_fst))

/-- The second difference is jointly measurable in the step and the base point. -/
private theorem measurable_secondDiff_prod_swap (hg : Measurable g) (j : Fin 2) :
    Measurable fun p : ℝ × (Fin 2 → ℝ) => secondDiff g j p.2 p.1 :=
  (measurable_secondDiff_prod hg j).comp measurable_swap

/-- Moving a translation from one factor of a product integral to the other. -/
private theorem integral_mul_comp_add (u v : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ) :
    ∫ z, u z * v (z + a) = ∫ z, u (z - a) * v z := by
  have h := integral_add_right_eq_self (μ := (volume : Measure (Fin 2 → ℝ)))
    (fun z : Fin 2 → ℝ => u (z - a) * v z) a
  simpa using h

/-- Moving a translation from one factor of a product integral to the other. -/
private theorem integral_mul_comp_sub (u v : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ) :
    ∫ z, u z * v (z - a) = ∫ z, u (z + a) * v z := by
  have h := integral_mul_comp_add u v (-a)
  simpa [sub_eq_add_neg] using h

/-- `c x (x²)⁻¹ = c / x` for `x ≠ 0`. -/
private theorem mul_mul_inv_sq {x : ℝ} (hx : x ≠ 0) (c : ℝ) : c * x * (x ^ 2)⁻¹ = c / x := by
  rw [sq, mul_inv, ← mul_assoc, mul_assoc c x x⁻¹, mul_inv_cancel₀ hx, mul_one, div_eq_mul_inv]

/-- At `α = 1` the weight `|t|^{−(1+α)}` is `(t²)⁻¹`, including at `t = 0`, where both sides
vanish by the convention `0^{−2} = 0`. -/
theorem abs_rpow_neg_one_add_one (t : ℝ) : |t| ^ (-(1 + (1 : ℝ))) = (t ^ 2)⁻¹ := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [abs_zero, Real.zero_rpow (by norm_num), zero_pow (by norm_num), inv_zero]
  · rw [show -(1 + (1 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (abs_nonneg t),
      Real.rpow_natCast, sq_abs]

/-! ### Integrability of the pairing integrand -/

/-- The integrand `g(z) (φ(z + t e_j) + φ(z − t e_j) − 2 φ(z)) |t|^{−(1+α)}` of the pairing is
integrable on `ℝ² × ℝ` for `g` bounded and measurable and `φ` a test function.

At a fixed step `t` the second difference of `φ` vanishes off the union `S_t` of the three
translates `tsupport φ ∓ t e_j` and `tsupport φ`, so `|S_t| ≤ 3 |tsupport φ|` for every `t`,
while the integrand is bounded by `C · jumpBound α M₀ M₂ t`. The iterated Tonelli bound is
therefore `3 C |tsupport φ| ∫ jumpBound α M₀ M₂ < ∞`. -/
theorem integrable_bdd_mul_secondDiff_mul_rpow (hα : 0 < α) (hα' : α < 2) (hgm : Measurable g)
    {C : ℝ} (hgb : ∀ z, |g z| ≤ C) (hφ : IsTestFunction φ) (j : Fin 2) :
    Integrable (fun p : (Fin 2 → ℝ) × ℝ =>
        g p.1 * (secondDiff φ j p.1 p.2 * |p.2| ^ (-(1 + α))))
      ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ)) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.1.of_le (by norm_cast)
  obtain ⟨M₀, M₂, h₀, h₂⟩ := exists_bounds_of_hasCompactSupport hφ2 hφ.2
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h₀ 0)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (h₂ 0)
  have hC : 0 ≤ C := (abs_nonneg _).trans (hgb 0)
  have hKm : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
  have hKc : IsCompact (tsupport φ) := hφ.2
  have hK3 : (3 : ℝ≥0∞) * volume (tsupport φ) ≠ ⊤ :=
    (ENNReal.mul_lt_top (by simp) hKc.measure_lt_top).ne
  have hm : Measurable fun p : (Fin 2 → ℝ) × ℝ =>
      g p.1 * (secondDiff φ j p.1 p.2 * |p.2| ^ (-(1 + α))) :=
    (hgm.comp measurable_fst).mul
      ((measurable_secondDiff_prod hφ.continuous.measurable j).mul
        ((continuous_abs.measurable.pow_const _).comp measurable_snd))
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  -- the inner integral at a fixed step, over three translates of the support of `φ`
  have hinner : ∀ t : ℝ, (∫⁻ z, ‖g z * (secondDiff φ j z t * |t| ^ (-(1 + α)))‖ₑ)
      ≤ ENNReal.ofReal (C * jumpBound α M₀ M₂ t) * (3 * volume (tsupport φ)) := by
    intro t
    obtain ⟨a, ha⟩ : ∃ a : Fin 2 → ℝ, a = t • Pi.single j (1 : ℝ) := ⟨_, rfl⟩
    obtain ⟨S, hS⟩ : ∃ S : Set (Fin 2 → ℝ), S =
        ((fun z => z + a) ⁻¹' tsupport φ ∪ (fun z => z - a) ⁻¹' tsupport φ) ∪ tsupport φ :=
      ⟨_, rfl⟩
    have hSm : MeasurableSet S := by
      rw [hS]
      exact ((hKm.preimage (measurable_id.add_const a)).union
        (hKm.preimage (measurable_id.sub_const a))).union hKm
    have hSvol : volume S ≤ 3 * volume (tsupport φ) := by
      have h1 : volume ((fun z : Fin 2 → ℝ => z + a) ⁻¹' tsupport φ) = volume (tsupport φ) :=
        measure_preimage_add_right volume a _
      have h2 : volume ((fun z : Fin 2 → ℝ => z - a) ⁻¹' tsupport φ) = volume (tsupport φ) := by
        simp [sub_eq_add_neg]
      calc volume S
          ≤ volume ((fun z : Fin 2 → ℝ => z + a) ⁻¹' tsupport φ ∪
              (fun z : Fin 2 → ℝ => z - a) ⁻¹' tsupport φ) + volume (tsupport φ) := by
            rw [hS]; exact measure_union_le _ _
        _ ≤ volume ((fun z : Fin 2 → ℝ => z + a) ⁻¹' tsupport φ) +
              volume ((fun z : Fin 2 → ℝ => z - a) ⁻¹' tsupport φ) + volume (tsupport φ) := by
            gcongr
            exact measure_union_le _ _
        _ = 3 * volume (tsupport φ) := by rw [h1, h2]; ring
    have hpt : ∀ z, ‖g z * (secondDiff φ j z t * |t| ^ (-(1 + α)))‖ₑ
        ≤ S.indicator (fun _ => ENNReal.ofReal (C * jumpBound α M₀ M₂ t)) z := by
      intro z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem hz, Real.enorm_eq_ofReal_abs]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [abs_mul]
        refine mul_le_mul (hgb z) ?_ (abs_nonneg _) hC
        simpa only [Real.norm_eq_abs] using
          norm_secondDiff_mul_rpow_le_jumpBound hφ2 h₀ h₂ α j z t
      · have hz0 : secondDiff φ j z t = 0 := by
          rw [hS] at hz
          simp only [Set.mem_union, Set.mem_preimage, not_or] at hz
          obtain ⟨⟨hz1, hz2⟩, hz3⟩ := hz
          rw [secondDiff, ← ha, image_eq_zero_of_notMem_tsupport hz1,
            image_eq_zero_of_notMem_tsupport hz2, image_eq_zero_of_notMem_tsupport hz3]
          ring
        rw [Set.indicator_of_notMem hz]
        simp [hz0]
    calc (∫⁻ z, ‖g z * (secondDiff φ j z t * |t| ^ (-(1 + α)))‖ₑ)
        ≤ ∫⁻ z, S.indicator (fun _ => ENNReal.ofReal (C * jumpBound α M₀ M₂ t)) z :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (C * jumpBound α M₀ M₂ t) * volume S := by
          rw [lintegral_indicator hSm, setLIntegral_const]
      _ ≤ ENNReal.ofReal (C * jumpBound α M₀ M₂ t) * (3 * volume (tsupport φ)) :=
          mul_le_mul_right hSvol _
  calc (∫⁻ p, ‖g p.1 * (secondDiff φ j p.1 p.2 * |p.2| ^ (-(1 + α)))‖ₑ
        ∂((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ)))
      = ∫⁻ t : ℝ, ∫⁻ z, ‖g z * (secondDiff φ j z t * |t| ^ (-(1 + α)))‖ₑ :=
        lintegral_prod_symm _ hm.enorm.aemeasurable
    _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal (C * jumpBound α M₀ M₂ t) * (3 * volume (tsupport φ)) :=
        lintegral_mono hinner
    _ = (∫⁻ t : ℝ, ENNReal.ofReal (C * jumpBound α M₀ M₂ t)) * (3 * volume (tsupport φ)) :=
        lintegral_mul_const' _ _ hK3
    _ = ENNReal.ofReal (∫ t, C * jumpBound α M₀ M₂ t) * (3 * volume (tsupport φ)) := by
        rw [ofReal_integral_eq_lintegral_ofReal ((integrable_jumpBound hα hα' hM₀ hM₂).const_mul C)
          (ae_of_all _ fun t => mul_nonneg hC (jumpBound_nonneg hM₀ hM₂ α t))]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hK3)

/-! ### The pairing identity at a fixed step -/

/-- **The pairing identity at a fixed step**: for `g` bounded and measurable and `φ` integrable,
`∫ g(z) (φ(z + t e_j) + φ(z − t e_j) − 2 φ(z)) dz = ∫ (g(z + t e_j) + g(z − t e_j) − 2 g(z)) φ(z)
dz`, by the shifts `z ↦ z ∓ t e_j` in the two outer terms. Every integral here converges
absolutely, since `g` is bounded and `φ` is integrable. -/
theorem integral_mul_secondDiff_eq_integral_secondDiff_mul (hgm : Measurable g) {C : ℝ}
    (hgb : ∀ z, |g z| ≤ C) (hφ : Integrable φ) (j : Fin 2) (t : ℝ) :
    ∫ z, g z * secondDiff φ j z t = ∫ z, secondDiff g j z t * φ z := by
  obtain ⟨a, ha⟩ : ∃ a : Fin 2 → ℝ, a = t • Pi.single j (1 : ℝ) := ⟨_, rfl⟩
  have hgbd : ∀ᵐ z : Fin 2 → ℝ, ‖g z‖ ≤ C :=
    ae_of_all _ fun z => (Real.norm_eq_abs _).trans_le (hgb z)
  have hA : Integrable fun z => g z * φ (z + a) :=
    (hφ.comp_add_right a).bdd_mul hgm.aestronglyMeasurable hgbd
  have hB : Integrable fun z => g z * φ (z - a) :=
    (hφ.comp_sub_right a).bdd_mul hgm.aestronglyMeasurable hgbd
  have hAB : Integrable fun z => g z * φ (z + a) + g z * φ (z - a) := hA.add hB
  have hM : Integrable fun z => g z * φ z := hφ.bdd_mul hgm.aestronglyMeasurable hgbd
  have hA' : Integrable fun z => g (z + a) * φ z :=
    hφ.bdd_mul ((hgm.comp (measurable_id.add_const a)).aestronglyMeasurable)
      (ae_of_all _ fun z => (Real.norm_eq_abs _).trans_le (hgb _))
  have hB' : Integrable fun z => g (z - a) * φ z :=
    hφ.bdd_mul ((hgm.comp (measurable_id.sub_const a)).aestronglyMeasurable)
      (ae_of_all _ fun z => (Real.norm_eq_abs _).trans_le (hgb _))
  have hAB' : Integrable fun z => g (z - a) * φ z + g (z + a) * φ z := hB'.add hA'
  have hsdφ : ∀ z, secondDiff φ j z t = φ (z + a) + φ (z - a) - 2 * φ z := fun z => by
    rw [ha]; rfl
  have hsdg : ∀ z, secondDiff g j z t = g (z + a) + g (z - a) - 2 * g z := fun z => by
    rw [ha]; rfl
  have hleft : (∫ z, g z * secondDiff φ j z t)
      = ((∫ z, g z * φ (z + a)) + ∫ z, g z * φ (z - a)) - 2 * ∫ z, g z * φ z := by
    calc (∫ z, g z * secondDiff φ j z t)
        = ∫ z, (g z * φ (z + a) + g z * φ (z - a) - 2 * (g z * φ z)) :=
          integral_congr_ae (ae_of_all _ fun z => by
            show g z * secondDiff φ j z t
              = g z * φ (z + a) + g z * φ (z - a) - 2 * (g z * φ z)
            rw [hsdφ z]; ring)
      _ = (∫ z, (g z * φ (z + a) + g z * φ (z - a))) - ∫ z, 2 * (g z * φ z) :=
          integral_sub hAB (hM.const_mul 2)
      _ = ((∫ z, g z * φ (z + a)) + ∫ z, g z * φ (z - a)) - 2 * ∫ z, g z * φ z := by
          rw [integral_add hA hB, integral_const_mul]
  have hright : (∫ z, secondDiff g j z t * φ z)
      = ((∫ z, g (z - a) * φ z) + ∫ z, g (z + a) * φ z) - 2 * ∫ z, g z * φ z := by
    calc (∫ z, secondDiff g j z t * φ z)
        = ∫ z, (g (z - a) * φ z + g (z + a) * φ z - 2 * (g z * φ z)) :=
          integral_congr_ae (ae_of_all _ fun z => by
            show secondDiff g j z t * φ z
              = g (z - a) * φ z + g (z + a) * φ z - 2 * (g z * φ z)
            rw [hsdg z]; ring)
      _ = (∫ z, (g (z - a) * φ z + g (z + a) * φ z)) - ∫ z, 2 * (g z * φ z) :=
          integral_sub hAB' (hM.const_mul 2)
      _ = ((∫ z, g (z - a) * φ z) + ∫ z, g (z + a) * φ z) - 2 * ∫ z, g z * φ z := by
          rw [integral_add hB' hA', integral_const_mul]
  rw [hleft, hright, integral_mul_comp_add g φ a, integral_mul_comp_sub g φ a]

/-! ### The easy direction -/

/-- **The easy direction of the pairing identity**: for every bounded measurable `g` and every
test function `φ`,
`∫ g A φ = ∑_j ∫_ℝ (∫ (g(z + t e_j) + g(z − t e_j) − 2 g(z)) φ(z) dz) |t|^{−(1+α)} dt`.

The two integrations are exchanged by Fubini, whose hypothesis is
`integrable_bdd_mul_secondDiff_mul_rpow`, and at a fixed step the second difference is moved
from `φ` onto `g` by `integral_mul_secondDiff_eq_integral_secondDiff_mul`. -/
theorem integral_mul_jumpGen_eq_integral_integral (hα : 0 < α) (hα' : α < 2)
    (hgm : Measurable g) {C : ℝ} (hgb : ∀ z, |g z| ≤ C) (hφ : IsTestFunction φ) :
    ∫ z, g z * jumpGen α φ z
      = ∑ j : Fin 2, ∫ t : ℝ, (∫ z, secondDiff g j z t * φ z) * |t| ^ (-(1 + α)) := by
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφ.2
  have hprod : ∀ j : Fin 2, Integrable (fun p : (Fin 2 → ℝ) × ℝ =>
      g p.1 * (secondDiff φ j p.1 p.2 * |p.2| ^ (-(1 + α))))
      ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ)) := fun j =>
    integrable_bdd_mul_secondDiff_mul_rpow hα hα' hgm hgb hφ j
  have hint : ∀ j : Fin 2, Integrable fun z =>
      g z * ∫ t : ℝ, secondDiff φ j z t * |t| ^ (-(1 + α)) := fun j =>
    (hprod j).integral_prod_left.congr (ae_of_all _ fun z =>
      integral_const_mul (g z) fun t : ℝ => secondDiff φ j z t * |t| ^ (-(1 + α)))
  have hL : (∫ z, g z * jumpGen α φ z)
      = ∑ j : Fin 2, ∫ z, g z * ∫ t : ℝ, secondDiff φ j z t * |t| ^ (-(1 + α)) := by
    rw [← integral_finsetSum _ fun j _ => hint j]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show g z * (∑ j : Fin 2, ∫ t : ℝ, secondDiff φ j z t * |t| ^ (-(1 + α)))
      = ∑ j : Fin 2, g z * ∫ t : ℝ, secondDiff φ j z t * |t| ^ (-(1 + α))
    rw [Finset.mul_sum]
  rw [hL]
  refine Finset.sum_congr rfl fun j _ => ?_
  have htrans : ∀ t : ℝ, (∫ z, g z * (secondDiff φ j z t * |t| ^ (-(1 + α))))
      = (∫ z, secondDiff g j z t * φ z) * |t| ^ (-(1 + α)) := by
    intro t
    calc (∫ z, g z * (secondDiff φ j z t * |t| ^ (-(1 + α))))
        = ∫ z, g z * secondDiff φ j z t * |t| ^ (-(1 + α)) :=
          integral_congr_ae (ae_of_all _ fun z => by ring)
      _ = (∫ z, g z * secondDiff φ j z t) * |t| ^ (-(1 + α)) := integral_mul_const _ _
      _ = (∫ z, secondDiff g j z t * φ z) * |t| ^ (-(1 + α)) := by
          rw [integral_mul_secondDiff_eq_integral_secondDiff_mul hgm hgb hφi j t]
  calc (∫ z, g z * ∫ t : ℝ, secondDiff φ j z t * |t| ^ (-(1 + α)))
      = ∫ z, ∫ t : ℝ, g z * (secondDiff φ j z t * |t| ^ (-(1 + α))) :=
        integral_congr_ae (ae_of_all _ fun z => (integral_const_mul _ _).symm)
    _ = ∫ t : ℝ, ∫ z, g z * (secondDiff φ j z t * |t| ^ (-(1 + α))) :=
        integral_integral_swap (f := fun (z : Fin 2 → ℝ) (t : ℝ) =>
          g z * (secondDiff φ j z t * |t| ^ (-(1 + α)))) (hprod j)
    _ = ∫ t : ℝ, (∫ z, secondDiff g j z t * φ z) * |t| ^ (-(1 + α)) :=
        integral_congr_ae (ae_of_all _ htrans)

/-! ### Self-adjointness -/

/-- **Self-adjointness of the jump pairing**: `∫ g A φ = ∫ (A g) φ` for a bounded measurable `g`
and a test function `φ`, under the hypothesis `hfin` that the double integral defining the
right-hand side converges absolutely.

The hypothesis cannot be dropped: for a merely Lipschitz `g` the naive domination fails, since
`∫_{|t| ≤ 1} |t| · |t|^{−2} dt` diverges. It is verified in `integrable_uncurry_of_bound` from a
pointwise bound on the inner integral. -/
theorem integral_mul_jumpGen_comm (hα : 0 < α) (hα' : α < 2) (hgm : Measurable g) {C : ℝ}
    (hgb : ∀ z, |g z| ≤ C) (hφ : IsTestFunction φ)
    (hfin : ∀ j : Fin 2, Integrable (Function.uncurry fun (t : ℝ) (z : Fin 2 → ℝ) =>
        secondDiff g j z t * φ z * |t| ^ (-(1 + α)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)))) :
    ∫ z, g z * jumpGen α φ z = ∫ z, jumpGen α g z * φ z := by
  have hz : ∀ (j : Fin 2) (z : Fin 2 → ℝ),
      (∫ t : ℝ, secondDiff g j z t * φ z * |t| ^ (-(1 + α)))
        = (∫ t : ℝ, secondDiff g j z t * |t| ^ (-(1 + α))) * φ z := by
    intro j z
    calc (∫ t : ℝ, secondDiff g j z t * φ z * |t| ^ (-(1 + α)))
        = ∫ t : ℝ, secondDiff g j z t * |t| ^ (-(1 + α)) * φ z :=
          integral_congr_ae (ae_of_all _ fun t => by ring)
      _ = (∫ t : ℝ, secondDiff g j z t * |t| ^ (-(1 + α))) * φ z := integral_mul_const _ _
  have hintR : ∀ j : Fin 2, Integrable fun z =>
      (∫ t : ℝ, secondDiff g j z t * |t| ^ (-(1 + α))) * φ z := fun j =>
    (hfin j).integral_prod_right.congr (ae_of_all _ fun z => hz j z)
  have hR : (∫ z, jumpGen α g z * φ z)
      = ∑ j : Fin 2, ∫ z, (∫ t : ℝ, secondDiff g j z t * |t| ^ (-(1 + α))) * φ z := by
    rw [← integral_finsetSum _ fun j _ => hintR j]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show (∑ j : Fin 2, ∫ t : ℝ, secondDiff g j z t * |t| ^ (-(1 + α))) * φ z
      = ∑ j : Fin 2, (∫ t : ℝ, secondDiff g j z t * |t| ^ (-(1 + α))) * φ z
    rw [Finset.sum_mul]
  rw [integral_mul_jumpGen_eq_integral_integral hα hα' hgm hgb hφ, hR]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc (∫ t : ℝ, (∫ z, secondDiff g j z t * φ z) * |t| ^ (-(1 + α)))
      = ∫ t : ℝ, ∫ z, secondDiff g j z t * φ z * |t| ^ (-(1 + α)) :=
        integral_congr_ae (ae_of_all _ fun t => (integral_mul_const _ _).symm)
    _ = ∫ z, ∫ t : ℝ, secondDiff g j z t * φ z * |t| ^ (-(1 + α)) :=
        integral_integral_swap (f := fun (t : ℝ) (z : Fin 2 → ℝ) =>
          secondDiff g j z t * φ z * |t| ^ (-(1 + α))) (hfin j)
    _ = ∫ z, (∫ t : ℝ, secondDiff g j z t * |t| ^ (-(1 + α))) * φ z :=
        integral_congr_ae (ae_of_all _ fun z => hz j z)

/-- **Pointwise lower bounds become weak ones**: if the generator of `g` is nonnegative almost
everywhere, then `g` pairs nonnegatively with the generator of every nonnegative test
function. -/
theorem nonneg_integral_mul_jumpGen (hα : 0 < α) (hα' : α < 2) (hgm : Measurable g) {C : ℝ}
    (hgb : ∀ z, |g z| ≤ C) (hφ : IsTestFunction φ)
    (hfin : ∀ j : Fin 2, Integrable (Function.uncurry fun (t : ℝ) (z : Fin 2 → ℝ) =>
        secondDiff g j z t * φ z * |t| ^ (-(1 + α)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))))
    (hφ0 : ∀ z, 0 ≤ φ z) (hg0 : ∀ᵐ z : Fin 2 → ℝ, 0 ≤ jumpGen α g z) :
    0 ≤ ∫ z, g z * jumpGen α φ z := by
  rw [integral_mul_jumpGen_comm hα hα' hgm hgb hφ hfin]
  exact integral_nonneg_of_ae (hg0.mono fun z hz => mul_nonneg hz (hφ0 z))

/-! ### A checkable sufficient condition -/

/-- **A checkable sufficient condition for the Fubini hypothesis of
`integral_mul_jumpGen_comm`**: it is enough to have a pointwise-in-`z` bound `B` on the inner
`t`-integral of the second difference of `g` which is integrable on the support of `φ`.

By Tonelli the double integral of the absolute value is `∫ (∫ |Δ_j^t g(z)| |t|^{−(1+α)} dt)
|φ(z)| dz`, which is at most `M₀ ∫_{tsupport φ} B`. -/
theorem integrable_uncurry_of_bound (hgm : Measurable g) (hφ : IsTestFunction φ) {j : Fin 2}
    {B : (Fin 2 → ℝ) → ℝ}
    (hB : ∀ z, (∫⁻ t : ℝ, ENNReal.ofReal (|secondDiff g j z t| * |t| ^ (-(1 + α))))
      ≤ ENNReal.ofReal (B z))
    (hBint : IntegrableOn B (tsupport φ)) :
    Integrable (Function.uncurry fun (t : ℝ) (z : Fin 2 → ℝ) =>
        secondDiff g j z t * φ z * |t| ^ (-(1 + α)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.1.of_le (by norm_cast)
  obtain ⟨M₀, M₂, h₀, h₂⟩ := exists_bounds_of_hasCompactSupport hφ2 hφ.2
  have hKm : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
  have hm : Measurable fun p : ℝ × (Fin 2 → ℝ) =>
      secondDiff g j p.2 p.1 * φ p.2 * |p.1| ^ (-(1 + α)) :=
    ((measurable_secondDiff_prod_swap hgm j).mul
      (hφ.continuous.measurable.comp measurable_snd)).mul
      ((continuous_abs.measurable.pow_const _).comp measurable_fst)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hinner : ∀ z : Fin 2 → ℝ,
      (∫⁻ t : ℝ, ‖secondDiff g j z t * φ z * |t| ^ (-(1 + α))‖ₑ)
        ≤ ENNReal.ofReal (B z) * ENNReal.ofReal |φ z| := by
    intro z
    have h1 : ∀ t : ℝ, ‖secondDiff g j z t * φ z * |t| ^ (-(1 + α))‖ₑ
        = ENNReal.ofReal (|secondDiff g j z t| * |t| ^ (-(1 + α))) * ENNReal.ofReal |φ z| := by
      intro t
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]
      ring
    rw [lintegral_congr h1, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_left (hB z) _
  have hpt : ∀ z : Fin 2 → ℝ, ENNReal.ofReal (B z) * ENNReal.ofReal |φ z|
      ≤ (tsupport φ).indicator (fun z => ENNReal.ofReal (B z) * ENNReal.ofReal M₀) z := by
    intro z
    by_cases hz : z ∈ tsupport φ
    · rw [Set.indicator_of_mem hz]
      exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (h₀ z)) _
    · rw [Set.indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hz]
      simp
  calc (∫⁻ p, ‖secondDiff g j p.2 p.1 * φ p.2 * |p.1| ^ (-(1 + α))‖ₑ
        ∂((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))))
      = ∫⁻ z : Fin 2 → ℝ, ∫⁻ t : ℝ, ‖secondDiff g j z t * φ z * |t| ^ (-(1 + α))‖ₑ :=
        lintegral_prod_symm _ hm.enorm.aemeasurable
    _ ≤ ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (B z) * ENNReal.ofReal |φ z| := lintegral_mono hinner
    _ ≤ ∫⁻ z : Fin 2 → ℝ,
          (tsupport φ).indicator (fun z => ENNReal.ofReal (B z) * ENNReal.ofReal M₀) z :=
        lintegral_mono hpt
    _ = ∫⁻ z in tsupport φ, ENNReal.ofReal (B z) * ENNReal.ofReal M₀ :=
        lintegral_indicator hKm _
    _ = (∫⁻ z in tsupport φ, ENNReal.ofReal (B z)) * ENNReal.ofReal M₀ :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ (∫⁻ z in tsupport φ, ‖B z‖ₑ) * ENNReal.ofReal M₀ := by
        gcongr with z
        exact Real.ofReal_le_enorm (B z)
    _ < ⊤ :=
        ENNReal.mul_lt_top (hasFiniteIntegral_iff_enorm.1 hBint.2) ENNReal.ofReal_lt_top

/-! ### The bound for a Lipschitz function with one bad scale -/

/-- **The inner bound for a bounded Lipschitz function which is quadratically flat at `z` only
up to the scale `δ`.** If `|g| ≤ C`, `g` is `L`-Lipschitz and
`|Δ_j^t g(z)| ≤ M₂ t²` for `|t| ≤ δ ≤ 1`, then
`∫_ℝ |Δ_j^t g(z)| t^{−2} dt ≤ 2 M₂ δ + 4 L log(1/δ) + 8 C`.

Split the step range into `|t| ≤ δ`, where the quadratic bound gives the integrand `M₂`;
`δ < |t| ≤ 1`, where `|Δ_j^t g(z)| ≤ 2 L |t|` gives the integrand `2 L / |t|` and hence the
logarithm; and `|t| > 1`, where `|Δ_j^t g(z)| ≤ 4 C` gives the integrand `4 C / t²`. -/
theorem lintegral_secondDiff_le_of_lipschitz_of_c2 {L : ℝ≥0} (hL : LipschitzWith L g) {C : ℝ}
    (hgb : ∀ z, |g z| ≤ C) {M₂ δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) (j : Fin 2) (z : Fin 2 → ℝ)
    (hC2 : ∀ t : ℝ, |t| ≤ δ → |secondDiff g j z t| ≤ M₂ * t ^ 2) :
    (∫⁻ t : ℝ, ENNReal.ofReal (|secondDiff g j z t| * (t ^ 2)⁻¹))
      ≤ ENNReal.ofReal (2 * M₂ * δ + 4 * L * Real.log (1 / δ) + 8 * C) := by
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hgb z)
  have hM₂ : 0 ≤ M₂ := by
    have h := hC2 δ (by rw [abs_of_pos hδ])
    nlinarith [abs_nonneg (secondDiff g j z δ), mul_pos hδ hδ]
  -- the two elementary bounds on the second difference
  have hLip : ∀ t : ℝ, |secondDiff g j z t| ≤ 2 * L * |t| := by
    intro t
    have he : ‖t • Pi.single j (1 : ℝ)‖ = |t| := by
      rw [norm_smul, Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    have h1 : |g (z + t • Pi.single j 1) - g z| ≤ L * |t| := by
      have h := hL.dist_le_mul (z + t • Pi.single j (1 : ℝ)) z
      rwa [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, he] at h
    have h2 : |g (z - t • Pi.single j 1) - g z| ≤ L * |t| := by
      have h := hL.dist_le_mul (z - t • Pi.single j (1 : ℝ)) z
      rwa [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg, he] at h
    have e1 := abs_le.1 h1
    have e2 := abs_le.1 h2
    rw [secondDiff, abs_le]
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  have hUnif : ∀ t : ℝ, |secondDiff g j z t| ≤ 4 * C := fun t =>
    abs_secondDiff_le_const hgb j z t
  -- the even dominating function
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ, H = fun t =>
      if |t| ≤ δ then M₂ else if |t| ≤ 1 then 2 * (L : ℝ) / |t| else 4 * C / t ^ 2 := ⟨_, rfl⟩
  have hH1 : ∀ t : ℝ, |t| ≤ δ → H t = M₂ := fun t ht => by rw [hH]; simp [ht]
  have hH2 : ∀ t : ℝ, δ < |t| → |t| ≤ 1 → H t = 2 * (L : ℝ) / |t| := fun t ht ht' => by
    rw [hH]; simp [not_le.2 ht, ht']
  have hH3 : ∀ t : ℝ, 1 < |t| → H t = 4 * C / t ^ 2 := fun t ht => by
    rw [hH]; simp [not_le.2 (lt_of_le_of_lt hδ' ht), not_le.2 ht]
  have hHnn : ∀ t : ℝ, 0 ≤ H t := by
    intro t
    rw [hH]
    dsimp only
    split_ifs
    · exact hM₂
    · exact div_nonneg (by linarith) (abs_nonneg t)
    · exact div_nonneg (by linarith) (sq_nonneg t)
  have hHeven : ∀ t : ℝ, H (-t) = H t := by
    intro t
    rw [hH]
    simp only [abs_neg, neg_sq]
  have hHm : Measurable H := by
    rw [hH]
    refine Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
      measurable_const (Measurable.ite
        (measurableSet_le continuous_abs.measurable measurable_const) ?_ ?_)
    · exact measurable_const.div continuous_abs.measurable
    · exact measurable_const.div (measurable_id.pow_const 2)
  -- the pointwise domination
  have hpt : ∀ t : ℝ, |secondDiff g j z t| * (t ^ 2)⁻¹ ≤ H t := by
    intro t
    have hw : (0 : ℝ) ≤ (t ^ 2)⁻¹ := by positivity
    by_cases h1 : |t| ≤ δ
    · rw [hH1 t h1]
      rcases eq_or_ne t 0 with rfl | ht0
      · simpa using hM₂
      · calc |secondDiff g j z t| * (t ^ 2)⁻¹ ≤ M₂ * t ^ 2 * (t ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_right (hC2 t h1) hw
          _ = M₂ := mul_inv_cancel_right₀ (pow_ne_zero 2 ht0) M₂
    · have ht0 : t ≠ 0 := fun h => h1 (by rw [h, abs_zero]; exact hδ.le)
      have habs : 0 < |t| := abs_pos.2 ht0
      by_cases h2 : |t| ≤ 1
      · rw [hH2 t (not_le.1 h1) h2]
        calc |secondDiff g j z t| * (t ^ 2)⁻¹ ≤ 2 * (L : ℝ) * |t| * (t ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_right (hLip t) hw
          _ = 2 * (L : ℝ) / |t| := by
              rw [← sq_abs t]; exact mul_mul_inv_sq habs.ne' (2 * L)
      · rw [hH3 t (not_le.1 h2)]
        calc |secondDiff g j z t| * (t ^ 2)⁻¹ ≤ 4 * C * (t ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_right (hUnif t) hw
          _ = 4 * C / t ^ 2 := (div_eq_mul_inv _ _).symm
  -- the three pieces of the half-line
  have hEq1 : EqOn H (fun _ => M₂) (Ioc 0 δ) := fun t ht =>
    hH1 t (by rw [abs_of_pos ht.1]; exact ht.2)
  have hEq2 : EqOn H (fun t => 2 * (L : ℝ) * t⁻¹) (Ioc δ 1) := by
    intro t ht
    have ht0 : 0 < t := hδ.trans ht.1
    rw [hH2 t (by rw [abs_of_pos ht0]; exact ht.1) (by rw [abs_of_pos ht0]; exact ht.2),
      abs_of_pos ht0, div_eq_mul_inv]
  have hEq3 : EqOn H (fun t => 4 * C * t ^ (-2 : ℝ)) (Ioi 1) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    show H t = 4 * C * t ^ (-2 : ℝ)
    rw [hH3 t (by rw [abs_of_pos ht0]; exact ht), show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg ht0.le, Real.rpow_natCast, div_eq_mul_inv]
  have hI1 : IntegrableOn H (Ioc 0 δ) :=
    (integrableOn_congr_fun hEq1 measurableSet_Ioc).2 (integrableOn_const (by simp))
  have hI2 : IntegrableOn H (Ioc δ 1) := by
    refine (integrableOn_congr_fun hEq2 measurableSet_Ioc).2 (IntegrableOn.mono_set ?_
      Ioc_subset_Icc_self)
    exact ContinuousOn.integrableOn_Icc (a := δ) (b := 1)
      (continuousOn_const.mul (continuousOn_id.inv₀ fun t ht => (hδ.trans_le ht.1).ne'))
  have hI3 : IntegrableOn H (Ioi 1) :=
    (integrableOn_congr_fun hEq3 measurableSet_Ioi).2
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul (4 * C))
  have hsplit01 : Ioc (0 : ℝ) 1 = Ioc 0 δ ∪ Ioc δ 1 := (Ioc_union_Ioc_eq_Ioc hδ.le hδ').symm
  have hsplitIoi : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) δ) (Ioc δ 1) :=
    Set.disjoint_left.2 fun t ht ht' => absurd ht.2 (not_le.2 ht'.1)
  have hI01 : IntegrableOn H (Ioc 0 1) := by
    rw [hsplit01, integrableOn_union]
    exact ⟨hI1, hI2⟩
  have hIoi : IntegrableOn H (Ioi 0) := by
    rw [hsplitIoi, integrableOn_union]
    exact ⟨hI01, hI3⟩
  -- the three integrals
  have hv1 : ∫ t in Ioc (0 : ℝ) δ, H t = M₂ * δ := by
    rw [setIntegral_congr_fun measurableSet_Ioc hEq1, setIntegral_const,
      Real.volume_real_Ioc_of_le hδ.le, sub_zero, smul_eq_mul, mul_comm]
  have hv2 : ∫ t in Ioc δ (1 : ℝ), H t = 2 * (L : ℝ) * Real.log (1 / δ) := by
    rw [setIntegral_congr_fun measurableSet_Ioc hEq2, ← intervalIntegral.integral_of_le hδ',
      intervalIntegral.integral_const_mul,
      integral_inv (by rw [Set.uIcc_of_le hδ']; exact fun h => absurd h.1 (not_le.2 hδ))]
  have hv3 : ∫ t in Ioi (1 : ℝ), H t = 4 * C := by
    rw [setIntegral_congr_fun measurableSet_Ioi hEq3, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num [Real.one_rpow]
  have hvtot : ∫ t, H t = 2 * M₂ * δ + 4 * L * Real.log (1 / δ) + 8 * C := by
    rw [integral_of_even hHeven hIoi, hsplitIoi,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI01 hI3, hsplit01,
      setIntegral_union hdisj measurableSet_Ioc hI1 hI2, hv1, hv2, hv3]
    ring
  calc (∫⁻ t : ℝ, ENNReal.ofReal (|secondDiff g j z t| * (t ^ 2)⁻¹))
      ≤ ∫⁻ t : ℝ, ENNReal.ofReal (H t) :=
        lintegral_mono fun t => ENNReal.ofReal_le_ofReal (hpt t)
    _ = ENNReal.ofReal (∫ t, H t) :=
        (ofReal_integral_eq_lintegral_ofReal (integrable_of_even hHeven hIoi)
          (ae_of_all _ hHnn)).symm
    _ = ENNReal.ofReal (2 * M₂ * δ + 4 * L * Real.log (1 / δ) + 8 * C) := by rw [hvtot]

/-- The bound of `lintegral_secondDiff_le_of_lipschitz_of_c2` in the form required by
`integrable_uncurry_of_bound` at `α = 1`. -/
theorem lintegral_secondDiff_mul_rpow_le_of_lipschitz_of_c2 {L : ℝ≥0} (hL : LipschitzWith L g)
    {C : ℝ} (hgb : ∀ z, |g z| ≤ C) {M₂ δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) (j : Fin 2)
    (z : Fin 2 → ℝ) (hC2 : ∀ t : ℝ, |t| ≤ δ → |secondDiff g j z t| ≤ M₂ * t ^ 2) :
    (∫⁻ t : ℝ, ENNReal.ofReal (|secondDiff g j z t| * |t| ^ (-(1 + (1 : ℝ)))))
      ≤ ENNReal.ofReal (2 * M₂ * δ + 4 * L * Real.log (1 / δ) + 8 * C) := by
  simpa only [abs_rpow_neg_one_add_one] using
    lintegral_secondDiff_le_of_lipschitz_of_c2 hL hgb hδ hδ' j z hC2

end CenteredMaximal

end
