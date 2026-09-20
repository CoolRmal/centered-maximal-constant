/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.Gagliardo
public import CenteredMaximal.Fractional.KernelPositivity

/-!
# The joint integrability hypothesis from finite Gagliardo energy

`CenteredMaximal.Fractional.hgconv_of_modulus` derives the joint integrability hypothesis
`hgconv` of `CenteredMaximal.convolution_le_of_eq_zero_fp` from a **global** `L¹` modulus of
continuity `∫ x, |u (x − z) − u x| ≤ C min(1, ‖z‖^θ)`. The solution of the obstacle problem is
only known to be integrable with finite jump energy, and there is no route from that to a global
`L¹` modulus. This file removes the need for one.

Two observations do it.

* The test function `w` of `hgconv` sits at `p.1`, so it **localises** the `x`-integral to the
  compact set `tsupport w`. Only a *local* statement about the increments of `u` is ever needed
  (`hgconv_of_setLIntegral_ne_top`, `hgconv_of_local_modulus`).
* On a compact set the increments are controlled by the **squared** increment
  `m z = ∫ x, (u (x − z) − u x)²` through Cauchy–Schwarz, and `m` is not needed pointwise: the
  Gagliardo energy is exactly `∫ z, m z ‖z‖^{−(2+α)}` (`gagliardo_eq_lintegral_sqIncrement`), an
  *averaged* bound, and a second Cauchy–Schwarz — this time in `z` — consumes it in that form.

## Main results

* `sqIncrement`, `gagliardo_eq_lintegral_sqIncrement`: the Gagliardo energy read in the difference
  variable, `[u]² = ∫ z, m z ‖z‖^{−(2+α)}`, by `z ↦ −z` and Tonelli.
* `sq_setLIntegral_enorm_sub_le`: Cauchy–Schwarz on a compact set,
  `(∫_K |u(x − z) − u x| dx)² ≤ |K| · m z`.
* `hgconv_of_setLIntegral_ne_top`: the localisation. `hgconv` holds as soon as
  `∫ z, g z ∫_K |u(x − z) − u x| dx < ∞` for every compact `K`; the test function contributes only
  its sup bound and its support.
* `hgconv_of_local_modulus`: the localised replacement for `hgconv_of_modulus` — the modulus of
  continuity is only asked for on compact sets, with a constant allowed to depend on the set.
* `setLIntegral_conv_ne_top`, `hgconv_of_gagliardo`: **the main result**, `hgconv` from finite
  Gagliardo energy alone, for a density `g ≤ A (r^{−p} + r^{−q})` with `2 < p, q` and
  `2p, 2q < 4 + α`. `hgconv_of_jumpEnergy` states it from finite jump energy, and
  `hgconv_of_jumpEnergy_six_fifths` is the numerical case `α = 6/5`, `p = 12/5`, `q = 11/5` of the
  `α = 6/5` certificate.

## The two regimes

Write `P z = ∫_K |u(x − z) − u x| dx` and `N = {‖z‖ ≤ 1}`.

*Near.* Cauchy–Schwarz in `z`, splitting the weight as `‖z‖^{(2+α)/2} · ‖z‖^{−(2+α)/2}`, gives

`(∫_N g P)² ≤ (∫_N g² ‖z‖^{2+α}) · (∫_N P² ‖z‖^{−(2+α)})`,

and `P² ≤ |K| m` turns the second factor into `|K| [u]² < ∞`. The first factor is a moment of the
*square* of the density against the weight `min(1, ‖z‖^{2+α})`, so
`CenteredMaximal.Fractional.integrable_mul_min_one_rpow_of_le` applies with `θ = 2 + α` and the
doubled exponents `2p`, `2q`; it needs `2p, 2q < 2 + θ = 4 + α`. At `α = 6/5` and `p = 12/5` this
is `24/5 < 26/5`, i.e. the radial exponent `−24/5 + (2 + 6/5) + 1 = −3/5` is `> −1`.

*Far.* No modulus at all: `P z ≤ 2 ‖u‖₁`, and `min(1, ‖z‖^{2+α}) = 1` on `Nᶜ`, so the same moment
lemma applied to `g` itself — exponents `p`, `q`, still below `4 + α` — bounds `∫_{Nᶜ} g`. At
`q = 11/5` the radial exponent is `−11/5 + 1 = −6/5 < −1`.

The density is truncated at the origin (`Set.indicator {0}ᶜ g`) before the moment lemma is
applied, because the hypothesis `g z ≤ A (r^{−p} + r^{−q})` is vacuous at `z = 0`, where the
right-hand side is `0`; the truncation is invisible to both integrals because their weights
vanish there.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

variable {g u : (Fin 2 → ℝ) → ℝ} {α : ℝ}

/-! ### The squared increment -/

/-- The squared `L²` increment `m z = ∫ x, (u (x − z) − u x)²`, in `[0, ∞]`. -/
def sqIncrement (u : (Fin 2 → ℝ) → ℝ) (z : Fin 2 → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((u (x - z) - u x) ^ 2)

@[simp]
theorem sqIncrement_zero (u : (Fin 2 → ℝ) → ℝ) : sqIncrement u 0 = 0 := by
  simp [sqIncrement]

theorem measurable_sqIncrement (hu : Measurable u) : Measurable (sqIncrement u) := by
  have h : Measurable fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      ENNReal.ofReal ((u (p.2 - p.1) - u p.2) ^ 2) := by fun_prop
  exact h.lintegral_prod_right'

/-- **The Gagliardo energy in the difference variable**: `[u]² = ∫ z, m z ‖z‖^{−(2+α)}`, where
`m` is `sqIncrement`. The substitution `h ↦ −h` turns the increment `u(x + h) − u(x)` of
`CenteredMaximal.gagliardo_eq_lintegral_lintegral_add` into `u(x − z) − u(x)`, and Tonelli moves
the `x`-integral inside, where the weight is a constant. -/
theorem gagliardo_eq_lintegral_sqIncrement (hu : Measurable u) (α : ℝ) :
    gagliardo α u = ∫⁻ z, sqIncrement u z * ENNReal.ofReal (‖z‖ ^ (-(2 + α))) := by
  have hneg : ∀ x : Fin 2 → ℝ,
      (∫⁻ h : Fin 2 → ℝ, ENNReal.ofReal ((u (x + h) - u x) ^ 2 * ‖h‖ ^ (-(2 + α))))
        = ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal ((u (x - z) - u x) ^ 2 * ‖z‖ ^ (-(2 + α))) := by
    intro x
    rw [← lintegral_neg_eq_self (μ := volume)
      (fun h : Fin 2 → ℝ => ENNReal.ofReal ((u (x + h) - u x) ^ 2 * ‖h‖ ^ (-(2 + α))))]
    refine lintegral_congr fun z => ?_
    show ENNReal.ofReal ((u (x + -z) - u x) ^ 2 * ‖-z‖ ^ (-(2 + α))) = _
    rw [← sub_eq_add_neg, norm_neg]
  have hswap : ∫⁻ x : Fin 2 → ℝ, ∫⁻ z : Fin 2 → ℝ,
        ENNReal.ofReal ((u (x - z) - u x) ^ 2 * ‖z‖ ^ (-(2 + α)))
      = ∫⁻ z : Fin 2 → ℝ, ∫⁻ x : Fin 2 → ℝ,
        ENNReal.ofReal ((u (x - z) - u x) ^ 2 * ‖z‖ ^ (-(2 + α))) := by
    refine lintegral_lintegral_swap ?_
    exact (by fun_prop : Measurable fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      ENNReal.ofReal ((u (p.1 - p.2) - u p.1) ^ 2 * ‖p.2‖ ^ (-(2 + α)))).aemeasurable
  rw [gagliardo_eq_lintegral_lintegral_add, lintegral_congr hneg, hswap]
  refine lintegral_congr fun z => ?_
  rw [show sqIncrement u z * ENNReal.ofReal (‖z‖ ^ (-(2 + α)))
      = ∫⁻ x : Fin 2 → ℝ,
        ENNReal.ofReal ((u (x - z) - u x) ^ 2) * ENNReal.ofReal (‖z‖ ^ (-(2 + α))) from
    (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm]
  exact lintegral_congr fun x => ENNReal.ofReal_mul (sq_nonneg _)

/-- **Cauchy–Schwarz on a compact set**: the local `L¹` increment is controlled by the squared
increment, `(∫_K |u(x − z) − u x| dx)² ≤ |K| · m z`. -/
theorem sq_setLIntegral_enorm_sub_le (hu : Measurable u) (K : Set (Fin 2 → ℝ))
    (z : Fin 2 → ℝ) :
    (∫⁻ x in K, ‖u (x - z) - u x‖ₑ) ^ 2 ≤ volume K * sqIncrement u z := by
  have hm : Measurable fun x : Fin 2 → ℝ => ‖u (x - z) - u x‖ₑ := by fun_prop
  calc (∫⁻ x in K, ‖u (x - z) - u x‖ₑ) ^ 2
      ≤ (∫⁻ _ in K, (1 : ℝ≥0∞)) * ∫⁻ x in K, ‖u (x - z) - u x‖ₑ ^ 2 := by
        simpa only [one_mul, one_pow] using ENNReal.sq_lintegral_mul_le
          (μ := volume.restrict K) (f := fun _ : Fin 2 → ℝ => (1 : ℝ≥0∞))
          (g := fun x => ‖u (x - z) - u x‖ₑ) aemeasurable_const hm.aemeasurable
    _ = volume K * ∫⁻ x in K, ‖u (x - z) - u x‖ₑ ^ 2 := by rw [setLIntegral_one]
    _ ≤ volume K * sqIncrement u z := by
        gcongr
        refine (setLIntegral_le_lintegral K _).trans (le_of_eq (lintegral_congr fun x => ?_))
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-! ### Localising the joint integrability hypothesis -/

/-- **The localisation of `hgconv`.** The test function `w` of the joint integrability hypothesis
of `CenteredMaximal.convolution_le_of_eq_zero_fp` sits at `p.1`, so it contributes only two
things: its sup bound, and the compact set `tsupport w` outside which the integrand vanishes. Once
those are extracted, all that is left is the finiteness, for every compact `K`, of
`∫ z, g z ∫_K |u(x − z) − u x| dx`. -/
theorem hgconv_of_setLIntegral_ne_top (hgm : Measurable g) (hg₀ : ∀ z, 0 ≤ g z)
    (hum : Measurable u)
    (hfin : ∀ K : Set (Fin 2 → ℝ), IsCompact K →
      ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (g z) * ∫⁻ x in K, ‖u (x - z) - u x‖ₑ ≠ ⊤) :
    ∀ w : (Fin 2 → ℝ) → ℝ, IsTestFunction w →
      Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        g p.2 * ((u (p.1 - p.2) - u p.1) * w p.1)) (volume.prod volume) := by
  intro w hw
  obtain ⟨Cw, hCw⟩ := hw.continuous.bounded_above_of_compact_support hw.2
  have hKm : MeasurableSet (tsupport w) := (isClosed_tsupport w).measurableSet
  have hFm : Measurable fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      g p.2 * ((u (p.1 - p.2) - u p.1) * w p.1) :=
    (hgm.comp measurable_snd).mul
      (((hum.comp (measurable_fst.sub measurable_snd)).sub (hum.comp measurable_fst)).mul
        (hw.continuous.measurable.comp measurable_fst))
  refine ⟨hFm.aestronglyMeasurable, ?_⟩
  have hstep : ∀ z : Fin 2 → ℝ, ∫⁻ x : Fin 2 → ℝ, ‖g z * ((u (x - z) - u x) * w x)‖ₑ
      ≤ ENNReal.ofReal Cw *
        (ENNReal.ofReal (g z) * ∫⁻ x in tsupport w, ‖u (x - z) - u x‖ₑ) := by
    intro z
    rw [show ENNReal.ofReal Cw * (ENNReal.ofReal (g z) * ∫⁻ x in tsupport w,
          ‖u (x - z) - u x‖ₑ)
        = ∫⁻ x : Fin 2 → ℝ, ENNReal.ofReal Cw * ENNReal.ofReal (g z) *
            (tsupport w).indicator (fun x => ‖u (x - z) - u x‖ₑ) x from by
      rw [lintegral_const_mul' _ _ (by finiteness), lintegral_indicator hKm, mul_assoc]]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ tsupport w
    · rw [Set.indicator_of_mem hx]
      have hwx : ‖w x‖ₑ ≤ ENNReal.ofReal Cw := by
        rw [← ofReal_norm (w x)]
        exact ENNReal.ofReal_le_ofReal (hCw x)
      calc ‖g z * ((u (x - z) - u x) * w x)‖ₑ
          = ENNReal.ofReal (g z) * (‖u (x - z) - u x‖ₑ * ‖w x‖ₑ) := by
            rw [enorm_mul, enorm_mul, Real.enorm_eq_ofReal (hg₀ z)]
        _ ≤ ENNReal.ofReal (g z) * (‖u (x - z) - u x‖ₑ * ENNReal.ofReal Cw) := by gcongr
        _ = ENNReal.ofReal Cw * ENNReal.ofReal (g z) * ‖u (x - z) - u x‖ₑ := by ring
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm' _ hFm.enorm]
  calc ∫⁻ z : Fin 2 → ℝ, ∫⁻ x : Fin 2 → ℝ, ‖g z * ((u (x - z) - u x) * w x)‖ₑ
      ≤ ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal Cw *
          (ENNReal.ofReal (g z) * ∫⁻ x in tsupport w, ‖u (x - z) - u x‖ₑ) :=
        lintegral_mono hstep
    _ = ENNReal.ofReal Cw *
          ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (g z) * ∫⁻ x in tsupport w, ‖u (x - z) - u x‖ₑ :=
        lintegral_const_mul' _ _ (by finiteness)
    _ < ⊤ := ENNReal.mul_lt_top (by finiteness) (lt_top_iff_ne_top.2 (hfin _ hw.2))

/-- **`hgconv` from a local `L¹` modulus of continuity**, the localised form of
`CenteredMaximal.Fractional.hgconv_of_modulus`: the modulus is only required on compact sets, and
its constant is allowed to depend on the set. -/
theorem hgconv_of_local_modulus {θ : ℝ} (hgm : Measurable g) (hg₀ : ∀ z, 0 ≤ g z)
    (hum : Measurable u) (huint : Integrable u)
    (hmod : ∀ K : Set (Fin 2 → ℝ), IsCompact K → ∃ C, 0 ≤ C ∧
      ∀ z, ∫ x in K, |u (x - z) - u x| ≤ C * min 1 (‖z‖ ^ θ))
    (hgmom : Integrable fun z => g z * min 1 (‖z‖ ^ θ)) :
    ∀ w : (Fin 2 → ℝ) → ℝ, IsTestFunction w →
      Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        g p.2 * ((u (p.1 - p.2) - u p.1) * w p.1)) (volume.prod volume) := by
  refine hgconv_of_setLIntegral_ne_top hgm hg₀ hum fun K hK => ?_
  obtain ⟨C, hC0, hC⟩ := hmod K hK
  have hmin0 : ∀ z : Fin 2 → ℝ, 0 ≤ min 1 (‖z‖ ^ θ) := fun z =>
    le_min zero_le_one (Real.rpow_nonneg (norm_nonneg z) θ)
  have hmom : ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (g z * min 1 (‖z‖ ^ θ)) ≠ ⊤ :=
    ((hasFiniteIntegral_iff_ofReal
      (.of_forall fun z => mul_nonneg (hg₀ z) (hmin0 z))).1 hgmom.hasFiniteIntegral).ne
  have hbd : ∀ z : Fin 2 → ℝ, ENNReal.ofReal (g z) * ∫⁻ x in K, ‖u (x - z) - u x‖ₑ
      ≤ ENNReal.ofReal C * ENNReal.ofReal (g z * min 1 (‖z‖ ^ θ)) := by
    intro z
    have hv : Integrable (fun x : Fin 2 → ℝ => u (x - z) - u x) volume :=
      (huint.comp_sub_right z).sub huint
    have hK' : ∫⁻ x in K, ‖u (x - z) - u x‖ₑ ≤ ENNReal.ofReal (C * min 1 (‖z‖ ^ θ)) := by
      rw [← ofReal_integral_norm_eq_lintegral_enorm hv.integrableOn]
      exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hC z)
    calc ENNReal.ofReal (g z) * ∫⁻ x in K, ‖u (x - z) - u x‖ₑ
        ≤ ENNReal.ofReal (g z) * ENNReal.ofReal (C * min 1 (‖z‖ ^ θ)) := by gcongr
      _ = ENNReal.ofReal C * ENNReal.ofReal (g z * min 1 (‖z‖ ^ θ)) := by
          rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_mul (hg₀ z)]
          ring
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono hbd) ?_)
  rw [lintegral_const_mul' _ _ (by finiteness)]
  exact ENNReal.mul_lt_top (by finiteness) (lt_top_iff_ne_top.2 hmom)

end CenteredMaximal.Fractional

end

end
