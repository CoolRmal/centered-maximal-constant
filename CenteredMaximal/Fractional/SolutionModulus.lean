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

/-! ### The two-regime bound from finite Gagliardo energy -/

/-- Splitting the weight for the Cauchy–Schwarz in the difference variable: the two factors
`‖z‖^{(2+α)/2}` and `‖z‖^{−(2+α)/2}` cancel away from the origin, and at the origin both sides
vanish because `P 0 = 0`. -/
private theorem mul_eq_weight_split (g : (Fin 2 → ℝ) → ℝ) {P : (Fin 2 → ℝ) → ℝ≥0∞}
    (hP0 : P 0 = 0) (α : ℝ) (z : Fin 2 → ℝ) :
    ENNReal.ofReal (g z) * P z
      = ENNReal.ofReal (g z) * ENNReal.ofReal (‖z‖ ^ ((2 + α) / 2)) *
        (P z * ENNReal.ofReal (‖z‖ ^ (-(2 + α) / 2))) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [hP0]
  · have hz0 : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
    have hcancel : ENNReal.ofReal (‖z‖ ^ ((2 + α) / 2)) *
        ENNReal.ofReal (‖z‖ ^ (-(2 + α) / 2)) = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hz0.le _), ← Real.rpow_add hz0,
        show (2 + α) / 2 + -(2 + α) / 2 = 0 by ring, Real.rpow_zero, ENNReal.ofReal_one]
    calc ENNReal.ofReal (g z) * P z
        = ENNReal.ofReal (g z) * P z *
            (ENNReal.ofReal (‖z‖ ^ ((2 + α) / 2)) *
              ENNReal.ofReal (‖z‖ ^ (-(2 + α) / 2))) := by rw [hcancel, mul_one]
      _ = _ := by ring

/-- Doubling a negative rpow exponent. -/
private theorem rpow_neg_sq {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    (r ^ (-t)) ^ 2 = r ^ (-(2 * t)) := by
  rw [← Real.rpow_natCast (r ^ (-t)) 2, ← Real.rpow_mul hr]
  congr 1
  push_cast
  ring

/-- **The two-regime bound, and the whole mathematical content of this file.** For a density
dominated by `A (r^{−p} + r^{−q})` with `2 < p, q` and `2p, 2q < 4 + α`, and for `u` integrable
with finite Gagliardo energy of order `α/2`, the localised quantity
`∫ z, g z ∫_K |u(x − z) − u x| dx` that `hgconv_of_setLIntegral_ne_top` asks for is finite on every
compact `K`. No pointwise modulus of continuity on `u` is used, and none is available: the squared
increment `sqIncrement u` stays under the `z`-integral throughout.

Near the origin, Cauchy–Schwarz in `z` against the weight `‖z‖^{±(2+α)/2}` splits the integral
into a moment of `g²` against `min(1, ‖z‖^{2+α})` — finite because `2p, 2q < 4 + α` — and
`|K| · [u]²`, by the Cauchy–Schwarz `sq_setLIntegral_enorm_sub_le` on `K` and the
difference-variable form `gagliardo_eq_lintegral_sqIncrement` of the energy. Away from the origin
no modulus is needed: the increment is bounded by `2 ‖u‖₁` and the weight `min(1, ‖z‖^{2+α})` is
`1`, so the same moment lemma applied to `g` itself finishes. -/
theorem setLIntegral_conv_ne_top {A p q : ℝ} (hgm : Measurable g) (hg₀ : ∀ z, 0 ≤ g z)
    (hp : 2 < p) (hq : 2 < q) (hp' : 2 * p < 4 + α) (hq' : 2 * q < 4 + α)
    (hgb : ∀ z, z ≠ 0 → g z ≤ A * (diamondNorm z ^ (-p) + diamondNorm z ^ (-q)))
    (hum : Measurable u) (huint : Integrable u) (hgag : gagliardo α u ≠ ⊤)
    {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) :
    ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (g z) * ∫⁻ x in K, ‖u (x - z) - u x‖ₑ ≠ ⊤ := by
  have hθ : (0 : ℝ) < 2 + α := by linarith
  have hKvol : volume K ≠ ⊤ := hK.measure_lt_top.ne
  set P : (Fin 2 → ℝ) → ℝ≥0∞ := fun z => ∫⁻ x in K, ‖u (x - z) - u x‖ₑ with hPdef
  have hPm : Measurable P := by
    have h : Measurable fun pt : (Fin 2 → ℝ) × (Fin 2 → ℝ) => ‖u (pt.2 - pt.1) - u pt.2‖ₑ := by
      fun_prop
    exact h.lintegral_prod_right' (ν := volume.restrict K)
  have hP0 : P 0 = 0 := by simp [hPdef]
  -- the density, truncated at the origin, where the hypothesis `hgb` says nothing
  set g' : (Fin 2 → ℝ) → ℝ := ({0}ᶜ : Set (Fin 2 → ℝ)).indicator g with hg'def
  have hg'm : Measurable g' := hgm.indicator (measurableSet_singleton _).compl
  have hg'zero : g' 0 = 0 := Set.indicator_of_notMem (by simp) g
  have hg'eq : ∀ z : Fin 2 → ℝ, z ≠ 0 → g' z = g z := fun z hz =>
    Set.indicator_of_mem (by simpa using hz) g
  have hg'0 : ∀ z, 0 ≤ g' z := by
    intro z
    rcases eq_or_ne z 0 with rfl | hz
    · rw [hg'zero]
    · rw [hg'eq z hz]; exact hg₀ z
  have hd0 : diamondNorm (0 : Fin 2 → ℝ) = 0 := diamondNorm_eq_zero_iff.2 rfl
  have hb1 : ∀ z : Fin 2 → ℝ, g' z ≤ A * (diamondNorm z ^ (-p) + diamondNorm z ^ (-q)) := by
    intro z
    rcases eq_or_ne z 0 with rfl | hz
    · rw [hg'zero, hd0, Real.zero_rpow (by linarith : (-p) ≠ 0),
        Real.zero_rpow (by linarith : (-q) ≠ 0)]
      simp
    · rw [hg'eq z hz]; exact hgb z hz
  have hb2 : ∀ z : Fin 2 → ℝ, g' z ^ 2
      ≤ 2 * A ^ 2 * (diamondNorm z ^ (-(2 * p)) + diamondNorm z ^ (-(2 * q))) := by
    intro z
    have hr : 0 ≤ diamondNorm z := diamondNorm_nonneg z
    rw [← rpow_neg_sq hr p, ← rpow_neg_sq hr q]
    nlinarith [mul_self_le_mul_self (hg'0 z) (hb1 z),
      sq_nonneg (A * (diamondNorm z ^ (-p) - diamondNorm z ^ (-q)))]
  have hmin0 : ∀ z : Fin 2 → ℝ, 0 ≤ min 1 (‖z‖ ^ (2 + α)) := fun z =>
    le_min zero_le_one (Real.rpow_nonneg (norm_nonneg z) _)
  have hmom1 : ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (g' z * min 1 (‖z‖ ^ (2 + α))) ≠ ⊤ := by
    have hint := integrable_mul_min_one_rpow_of_le (θ := 2 + α) (p := p) (q := q)
      hg'm hg'0 hθ hp (by linarith) hq (by linarith) hb1
    exact ((hasFiniteIntegral_iff_ofReal
      (.of_forall fun z => mul_nonneg (hg'0 z) (hmin0 z))).1 hint.hasFiniteIntegral).ne
  have hmom2 : ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (g' z ^ 2 * min 1 (‖z‖ ^ (2 + α))) ≠ ⊤ := by
    have hint := integrable_mul_min_one_rpow_of_le (θ := 2 + α) (p := 2 * p) (q := 2 * q)
      (hg'm.pow_const 2) (fun z => sq_nonneg _) hθ (by linarith) (by linarith) (by linarith)
      (by linarith) hb2
    exact ((hasFiniteIntegral_iff_ofReal
      (.of_forall fun z => mul_nonneg (sq_nonneg _) (hmin0 z))).1 hint.hasFiniteIntegral).ne
  set N : Set (Fin 2 → ℝ) := {z | ‖z‖ ≤ 1} with hNdef
  have hNm : MeasurableSet N := measurableSet_le measurable_norm measurable_const
  -- the near regime: two Cauchy–Schwarz inequalities and the Gagliardo energy
  have hnear : ∫⁻ z in N, ENNReal.ofReal (g z) * P z ≠ ⊤ := by
    have hfm : Measurable fun z : Fin 2 → ℝ =>
        ENNReal.ofReal (g z) * ENNReal.ofReal (‖z‖ ^ ((2 + α) / 2)) :=
      (ENNReal.measurable_ofReal.comp hgm).mul
        (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _))
    have hhm : Measurable fun z : Fin 2 → ℝ => P z * ENNReal.ofReal (‖z‖ ^ (-(2 + α) / 2)) :=
      hPm.mul (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _))
    have hCS := ENNReal.sq_lintegral_mul_le (μ := volume.restrict N)
      hfm.aemeasurable hhm.aemeasurable
    have hLHS : ∫⁻ z in N, ENNReal.ofReal (g z) * P z
        = ∫⁻ z in N, ENNReal.ofReal (g z) * ENNReal.ofReal (‖z‖ ^ ((2 + α) / 2)) *
            (P z * ENNReal.ofReal (‖z‖ ^ (-(2 + α) / 2))) :=
      lintegral_congr fun z => mul_eq_weight_split g hP0 α z
    have hfin1 : ∫⁻ z in N,
        (ENNReal.ofReal (g z) * ENNReal.ofReal (‖z‖ ^ ((2 + α) / 2))) ^ 2 ≠ ⊤ := by
      refine ne_top_of_le_ne_top hmom2
        ((setLIntegral_mono' hNm fun z hz => ?_).trans (setLIntegral_le_lintegral _ _))
      rcases eq_or_ne z 0 with rfl | hz0
      · rw [norm_zero, Real.zero_rpow (by linarith : (2 + α) / 2 ≠ 0)]
        simp
      · have hminz : min 1 (‖z‖ ^ (2 + α)) = ‖z‖ ^ (2 + α) :=
          min_eq_right (Real.rpow_le_one (norm_nonneg z) hz hθ.le)
        rw [hg'eq z hz0, hminz, mul_pow, ← ENNReal.ofReal_pow (hg₀ z),
          ofReal_rpow_half_sq (norm_nonneg z) (2 + α), ← ENNReal.ofReal_mul (sq_nonneg _)]
    have hfin2 : ∫⁻ z in N, (P z * ENNReal.ofReal (‖z‖ ^ (-(2 + α) / 2))) ^ 2
        ≤ volume K * gagliardo α u := by
      calc ∫⁻ z in N, (P z * ENNReal.ofReal (‖z‖ ^ (-(2 + α) / 2))) ^ 2
          ≤ ∫⁻ z : Fin 2 → ℝ,
              volume K * (sqIncrement u z * ENNReal.ofReal (‖z‖ ^ (-(2 + α)))) := by
            refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun z => ?_)
            rw [mul_pow, ofReal_rpow_half_sq (norm_nonneg z) (-(2 + α)), ← mul_assoc]
            gcongr
            exact sq_setLIntegral_enorm_sub_le hum K z
        _ = volume K * gagliardo α u := by
            rw [gagliardo_eq_lintegral_sqIncrement hum α, lintegral_const_mul' _ _ hKvol]
    have hsq : (∫⁻ z in N, ENNReal.ofReal (g z) * P z) ^ 2 ≠ ⊤ := by
      rw [hLHS]
      exact ne_top_of_le_ne_top
        (ENNReal.mul_ne_top hfin1
          (ne_top_of_le_ne_top (ENNReal.mul_ne_top hKvol hgag) hfin2)) hCS
    exact fun h => hsq (by simp [h])
  -- the far regime: no modulus of continuity at all, just `‖u‖₁`
  have hfar : ∫⁻ z in Nᶜ, ENNReal.ofReal (g z) * P z ≠ ⊤ := by
    have hL : ∫⁻ x : Fin 2 → ℝ, ‖u x‖ₑ ≠ ⊤ :=
      (hasFiniteIntegral_iff_enorm.1 huint.hasFiniteIntegral).ne
    have hPle : ∀ z : Fin 2 → ℝ, P z ≤ 2 * ∫⁻ x : Fin 2 → ℝ, ‖u x‖ₑ := by
      intro z
      calc P z ≤ ∫⁻ x : Fin 2 → ℝ, ‖u (x - z) - u x‖ₑ := setLIntegral_le_lintegral _ _
        _ ≤ ∫⁻ x : Fin 2 → ℝ, (‖u (x - z)‖ₑ + ‖u x‖ₑ) := lintegral_mono fun _ => enorm_sub_le
        _ = (∫⁻ x : Fin 2 → ℝ, ‖u (x - z)‖ₑ) + ∫⁻ x : Fin 2 → ℝ, ‖u x‖ₑ :=
            lintegral_add_left (by fun_prop) _
        _ = 2 * ∫⁻ x : Fin 2 → ℝ, ‖u x‖ₑ := by
            rw [lintegral_sub_right_eq_self (fun x : Fin 2 → ℝ => ‖u x‖ₑ) z, two_mul]
    have hbd : ∀ z ∈ Nᶜ, ENNReal.ofReal (g z) * P z
        ≤ 2 * (∫⁻ x : Fin 2 → ℝ, ‖u x‖ₑ) *
            ENNReal.ofReal (g' z * min 1 (‖z‖ ^ (2 + α))) := by
      intro z hz
      have hz1 : 1 < ‖z‖ := not_le.1 hz
      have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz1; linarith
      rw [hg'eq z hz0, min_eq_left (Real.one_le_rpow hz1.le hθ.le), mul_one]
      calc ENNReal.ofReal (g z) * P z
          ≤ ENNReal.ofReal (g z) * (2 * ∫⁻ x : Fin 2 → ℝ, ‖u x‖ₑ) := by gcongr; exact hPle z
        _ = 2 * (∫⁻ x : Fin 2 → ℝ, ‖u x‖ₑ) * ENNReal.ofReal (g z) := by ring
    refine ne_of_lt (lt_of_le_of_lt (setLIntegral_mono' hNm.compl hbd)
      (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) ?_))
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) hL)]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (ENNReal.mul_ne_top (by norm_num) hL))
      (lt_top_iff_ne_top.2 hmom1)
  rw [← lintegral_add_compl _ hNm]
  exact ENNReal.add_ne_top.2 ⟨hnear, hfar⟩

/-- **`hgconv` from finite Gagliardo energy.** The joint integrability hypothesis of
`CenteredMaximal.convolution_le_of_eq_zero_fp` holds for any integrable `u` of finite Gagliardo
energy of order `α/2` and any nonnegative density dominated by `A (r^{−p} + r^{−q})` with
`2 < p, q` and `2p, 2q < 4 + α`. No modulus of continuity on `u` is required. -/
theorem hgconv_of_gagliardo {A p q : ℝ} (hgm : Measurable g) (hg₀ : ∀ z, 0 ≤ g z)
    (hp : 2 < p) (hq : 2 < q) (hp' : 2 * p < 4 + α) (hq' : 2 * q < 4 + α)
    (hgb : ∀ z, z ≠ 0 → g z ≤ A * (diamondNorm z ^ (-p) + diamondNorm z ^ (-q)))
    (hum : Measurable u) (huint : Integrable u) (hgag : gagliardo α u ≠ ⊤) :
    ∀ w : (Fin 2 → ℝ) → ℝ, IsTestFunction w →
      Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        g p.2 * ((u (p.1 - p.2) - u p.1) * w p.1)) (volume.prod volume) :=
  hgconv_of_setLIntegral_ne_top hgm hg₀ hum fun _ hK =>
    setLIntegral_conv_ne_top hgm hg₀ hp hq hp' hq' hgb hum huint hgag hK

/-- **`hgconv` from finite jump energy**, which is the form in which the obstacle solution carries
its energy (`CenteredMaximal.EnergySpace`): the comparison
`CenteredMaximal.gagliardo_le_jumpEnergy` turns it into finite Gagliardo energy. -/
theorem hgconv_of_jumpEnergy {A p q : ℝ} (hgm : Measurable g) (hg₀ : ∀ z, 0 ≤ g z)
    (hp : 2 < p) (hq : 2 < q) (hp' : 2 * p < 4 + α) (hq' : 2 * q < 4 + α)
    (hgb : ∀ z, z ≠ 0 → g z ≤ A * (diamondNorm z ^ (-p) + diamondNorm z ^ (-q)))
    (hum : Measurable u) (huint : Integrable u) (hE : jumpEnergy α u ≠ ⊤) :
    ∀ w : (Fin 2 → ℝ) → ℝ, IsTestFunction w →
      Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        g p.2 * ((u (p.1 - p.2) - u p.1) * w p.1)) (volume.prod volume) := by
  have hle := gagliardo_le_jumpEnergy hum (by linarith : (0 : ℝ) < α)
  exact hgconv_of_gagliardo hgm hg₀ hp hq hp' hq' hgb hum huint
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE) hle)

/-- **The numerical case of the `α = 6/5` certificate.** The generator density of `fracKernel`
behaves like `r^{−12/5}` at the origin and like `r^{−11/5}` at infinity, and both doubled exponents
`24/5` and `22/5` are below `4 + 6/5 = 26/5`, so an integrable solution of the obstacle problem with
finite jump energy satisfies the joint integrability hypothesis `hgconv`. -/
theorem hgconv_of_jumpEnergy_six_fifths {A : ℝ} (hgm : Measurable g) (hg₀ : ∀ z, 0 ≤ g z)
    (hgb : ∀ z, z ≠ 0 → g z ≤ A * (diamondNorm z ^ (-(12 / 5) : ℝ) +
      diamondNorm z ^ (-(11 / 5) : ℝ)))
    (hum : Measurable u) (huint : Integrable u) (hE : jumpEnergy (6 / 5) u ≠ ⊤) :
    ∀ w : (Fin 2 → ℝ) → ℝ, IsTestFunction w →
      Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        g p.2 * ((u (p.1 - p.2) - u p.1) * w p.1)) (volume.prod volume) :=
  hgconv_of_jumpEnergy hgm hg₀ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hgb hum
    huint hE

end CenteredMaximal.Fractional

end

end
