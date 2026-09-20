/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Cauchy.LooseKernel
public import CenteredMaximal.Cauchy.TentGenerator

/-!
# The Cauchy jump generator of the two-dimensional bump

The bump subtracted from the loose comparison kernel of `CenteredMaximal.Cauchy.LooseKernel` is
`ψ (u, v) = (1 − |u| − |v|)₊²`, that is `bump z = looseHump (diamondNorm z)`. This file computes its
Cauchy jump generator in closed form and bounds it by a function of the diamond radius alone.

## The slice factorisation

The generator `jumpGen` sums two one-dimensional jump integrals, one per coordinate axis, and each
of them only sees the corresponding slice of the bump. The slice `bumpSlice c x = (1 − |x| − |c|)₊²`
is a dilate of the squared tent of `CenteredMaximal.Cauchy.TentGenerator`: for `|c| < 1` and
`a = 1 − |c| > 0`,

`bumpSlice c x = a² tentSq (x / a)`

(`bumpSlice_eq_smul_tentSq`), while for `1 ≤ |c|` the slice vanishes identically
(`bumpSlice_eq_zero`). The one-dimensional operator scales as
`jumpGen1 1 (a² φ (· / a)) t = a jumpGen1 1 φ (t / a)` (`jumpGen1_smul_div`), by the substitution
`s = a σ` in the Bochner integral; no integrability hypothesis is needed, since
`Measure.integral_comp_mul_left` is an identity of Bochner integrals. Together with the closed form
`jumpGen1_tentSq` this gives the main computation `jumpGen_bump`: for `z` off both axes with
`diamondNorm z < 1`,

`jumpGen 1 bump z = 4 ((1 − v) Ffun (u / (1 − v)) + (1 − u) Ffun (v / (1 − u)))`, `u = |z 0|`,
`v = |z 1|`.

## The angular bounds

`Ffun` is concave on `(0, 1)` (`concaveOn_Ffun`), and the two weights `1 − v` and `1 − u` sum to
`2 − r` with `r = u + v`, while the two arguments average to `r / (2 − r)` against the normalised
weights. Weighted Jensen therefore bounds the generator by a function of `r` alone
(`jumpGen_bump_le`):

`jumpGen 1 bump z ≤ 4 Tfun r`, `Tfun r = (2 − r) Ffun (r / (2 − r))`,

with equality when the two coordinates agree. Outside the unit diamond every surviving slice has
argument at least `1`, where `Ffun ≤ 2 − 2 log 2` (`Ffun_le_of_one_le`), and the surviving weights
`(1 − v)₊` and `(1 − u)₊` sum to at most `1`; hence `jumpGen_bump_le_exterior`,

`jumpGen 1 bump z ≤ 4 (2 − 2 log 2)`.

## Properties of the angular bound

The downstream certificate needs `Tfun_eq`, the closed form
`Tfun r = 2 (2 − r) (1 − log 2 + log r) − 2 (1 − r) log (1 − r)` on `(0, 1)` — the two logarithms of
`2 − r` cancel — the sign fact `Tfun_nonpos_of_le_half`, the derivative `hasDerivAt_Tfun`

`Tfun' r = 2 log 2 − 2 log r + 2 log (1 − r) + 4 / r − 2`,

and the second derivative `deriv2_Tfun`, `Tfun'' r = −2 (2 − r) / (r² (1 − r))`, whose minimum
modulus on `(0, 1)` is attained near `r = 0.72`; the certificate uses the clean consequence
`deriv2_Tfun_le`, `Tfun'' ≤ −27/2`, which follows from `27 r³ − 27 r² + 4 = (3r − 2)² (3r + 1) ≥ 0`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace CenteredMaximal.Cauchy

/-- The bump subtracted from the loose comparison kernel, `ψ (u, v) = (1 − |u| − |v|)₊²`. -/
def bump (z : Fin 2 → ℝ) : ℝ := looseHump (diamondNorm z)

/-- The slice `x ↦ (1 − |x| − |c|)₊²` of the bump along a coordinate axis. -/
def bumpSlice (c x : ℝ) : ℝ := looseHump (|x| + |c|)

/-- The angular bound `T (r) = (2 − r) Ffun (r / (2 − r))` on the generator of the bump. -/
def Tfun (r : ℝ) : ℝ := (2 - r) * Ffun (r / (2 - r))

/-! ### The slices of the bump -/

theorem bump_eq_bumpSlice_zero (z : Fin 2 → ℝ) : bump z = bumpSlice (z 1) (z 0) := by
  simp [bump, bumpSlice, diamondNorm]

theorem bump_eq_bumpSlice_one (z : Fin 2 → ℝ) : bump z = bumpSlice (z 0) (z 1) := by
  simp [bump, bumpSlice, diamondNorm, add_comm]

theorem bump_add_single_zero (z : Fin 2 → ℝ) (t : ℝ) :
    bump (z + t • Pi.single 0 1) = bumpSlice (z 1) (z 0 + t) := by
  simp [bump, bumpSlice, diamondNorm]

theorem bump_sub_single_zero (z : Fin 2 → ℝ) (t : ℝ) :
    bump (z - t • Pi.single 0 1) = bumpSlice (z 1) (z 0 - t) := by
  simp [bump, bumpSlice, diamondNorm]

theorem bump_add_single_one (z : Fin 2 → ℝ) (t : ℝ) :
    bump (z + t • Pi.single 1 1) = bumpSlice (z 0) (z 1 + t) := by
  simp [bump, bumpSlice, diamondNorm, add_comm]

theorem bump_sub_single_one (z : Fin 2 → ℝ) (t : ℝ) :
    bump (z - t • Pi.single 1 1) = bumpSlice (z 0) (z 1 - t) := by
  simp [bump, bumpSlice, diamondNorm, add_comm]

/-- A slice past the unit diamond vanishes identically. -/
theorem bumpSlice_eq_zero {c : ℝ} (hc : 1 ≤ |c|) (x : ℝ) : bumpSlice c x = 0 :=
  looseHump_eq_zero (by linarith [abs_nonneg x])

/-- **The slice of the bump is a dilate of the squared tent**, with dilation factor
`a = 1 − |c| > 0`: `bumpSlice c x = a² tentSq (x / a)`. -/
theorem bumpSlice_eq_smul_tentSq {c : ℝ} (hc : |c| < 1) (x : ℝ) :
    bumpSlice c x = (1 - |c|) ^ 2 * tentSq (x / (1 - |c|)) := by
  have ha : (0 : ℝ) < 1 - |c| := by linarith
  have h1 : (1 - |c|) * max (1 - |x| / (1 - |c|)) 0 = max (1 - |c| - |x|) 0 := by
    rw [mul_max_of_nonneg _ _ ha.le, mul_zero, mul_sub, mul_one, mul_div_cancel₀ _ ha.ne']
  calc bumpSlice c x = max (1 - |c| - |x|) 0 ^ 2 := by
        rw [bumpSlice, looseHump, show 1 - (|x| + |c|) = 1 - |c| - |x| by ring]
    _ = ((1 - |c|) * max (1 - |x| / (1 - |c|)) 0) ^ 2 := by rw [h1]
    _ = (1 - |c|) ^ 2 * tentSq (x / (1 - |c|)) := by
        rw [tentSq, abs_div, abs_of_pos ha]; ring

/-! ### The scaling law of the one-dimensional operator -/

/-- **The scaling law.** The one-dimensional jump operator of order `1` turns the dilate
`x ↦ a² φ (x / a)` into `a` times the operator of `φ` at the dilated point. Both sides being
Bochner integrals, the substitution `s = a σ` needs no integrability hypothesis. -/
theorem jumpGen1_smul_div {a : ℝ} (ha : 0 < a) (φ : ℝ → ℝ) (t : ℝ) :
    jumpGen1 1 (fun x => a ^ 2 * φ (x / a)) t = a * jumpGen1 1 φ (t / a) := by
  have ha0 : a ≠ 0 := ha.ne'
  set f : ℝ → ℝ := fun s => (a ^ 2 * φ ((t + s) / a) + a ^ 2 * φ ((t - s) / a)
    - 2 * (a ^ 2 * φ (t / a))) * (s ^ 2)⁻¹ with hf
  have hcomp : ∀ s : ℝ,
      f (a * s) = (φ (t / a + s) + φ (t / a - s) - 2 * φ (t / a)) * (s ^ 2)⁻¹ := by
    intro s
    have h1 : (t + a * s) / a = t / a + s := by field_simp
    have h2 : (t - a * s) / a = t / a - s := by field_simp
    have h3 : ((a * s) ^ 2)⁻¹ = (a ^ 2)⁻¹ * (s ^ 2)⁻¹ := by rw [mul_pow, mul_inv]
    simp only [hf, h1, h2, h3]
    field_simp
  calc jumpGen1 1 (fun x => a ^ 2 * φ (x / a)) t = ∫ s : ℝ, f s := by
        simp only [jumpGen1, CenteredMaximal.abs_rpow_neg_two, hf]
    _ = a * ∫ s : ℝ, f (a * s) := by
        rw [MeasureTheory.Measure.integral_comp_mul_left f a, smul_eq_mul,
          abs_of_pos (by positivity : (0 : ℝ) < a⁻¹), ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
    _ = a * jumpGen1 1 φ (t / a) := by
        simp only [jumpGen1, CenteredMaximal.abs_rpow_neg_two, hcomp]

/-! ### The one-dimensional jump integral of a slice -/

/-- The jump integral of the squared tent is even, the squared tent being even. -/
theorem jumpGen1_tentSq_neg (t : ℝ) : jumpGen1 1 tentSq (-t) = jumpGen1 1 tentSq t := by
  simp only [jumpGen1]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  dsimp only
  rw [show -t + s = -(t - s) by ring, show -t - s = -(t + s) by ring, tentSq_neg, tentSq_neg,
    tentSq_neg]
  ring

/-- The closed form of the jump integral of the squared tent at an arbitrary nonzero point. -/
theorem jumpGen1_tentSq_abs {t : ℝ} (ht : t ≠ 0) : jumpGen1 1 tentSq t = 4 * Ffun |t| := by
  rcases lt_or_gt_of_ne ht with h | h
  · rw [abs_of_neg h, ← jumpGen1_tentSq_neg, jumpGen1_tentSq (by linarith)]
  · rw [abs_of_pos h, jumpGen1_tentSq h]

/-- **The jump integral of a slice** of the bump, for a slice that does not vanish identically:
`jumpGen1 1 (bumpSlice c) x = 4 (1 − |c|) Ffun (|x| / (1 − |c|))`. -/
theorem jumpGen1_bumpSlice {c x : ℝ} (hc : |c| < 1) (hx : x ≠ 0) :
    jumpGen1 1 (bumpSlice c) x = 4 * ((1 - |c|) * Ffun (|x| / (1 - |c|))) := by
  have ha : (0 : ℝ) < 1 - |c| := by linarith
  rw [show bumpSlice c = fun y => (1 - |c|) ^ 2 * tentSq (y / (1 - |c|)) from
      funext (bumpSlice_eq_smul_tentSq hc), jumpGen1_smul_div ha,
    jumpGen1_tentSq_abs (div_ne_zero hx ha.ne'), abs_div, abs_of_pos ha]
  ring

/-- A slice that vanishes identically has vanishing jump integral. -/
theorem jumpGen1_bumpSlice_of_one_le {c : ℝ} (hc : 1 ≤ |c|) (x : ℝ) :
    jumpGen1 1 (bumpSlice c) x = 0 := by
  simp [jumpGen1, bumpSlice_eq_zero hc]

/-- **The integrand of the jump integral of a slice is integrable** away from the corner of the
slice: a slice that does not vanish identically is a dilate of the squared tent, whose jump
integrand is integrable by `integrable_tentSqDiff_div_sq`. -/
theorem integrable_bumpSliceDiff {c x : ℝ} (hx : x ≠ 0) :
    Integrable fun s : ℝ => (bumpSlice c (x + s) + bumpSlice c (x - s) - 2 * bumpSlice c x)
      * |s| ^ (-(1 + 1) : ℝ) := by
  rcases lt_or_ge |c| 1 with hc | hc
  · have ha : (0 : ℝ) < 1 - |c| := by linarith
    have ha0 : (1 : ℝ) - |c| ≠ 0 := ha.ne'
    refine ((integrable_tentSqDiff_div_sq (div_ne_zero hx ha0)).comp_div ha0).congr
      (Filter.Eventually.of_forall fun s => ?_)
    have hw : ((s / (1 - |c|)) ^ 2)⁻¹ = (1 - |c|) ^ 2 * (s ^ 2)⁻¹ := by
      rw [div_pow, inv_div, div_eq_mul_inv]
    have ea : (x + s) / (1 - |c|) = x / (1 - |c|) + s / (1 - |c|) := by ring
    have eb : (x - s) / (1 - |c|) = x / (1 - |c|) - s / (1 - |c|) := by ring
    show tentSqDiff (x / (1 - |c|)) (s / (1 - |c|)) * ((s / (1 - |c|)) ^ 2)⁻¹
        = (bumpSlice c (x + s) + bumpSlice c (x - s) - 2 * bumpSlice c x)
          * |s| ^ (-(1 + 1) : ℝ)
    rw [tentSqDiff, ← ea, ← eb, bumpSlice_eq_smul_tentSq hc (x + s),
      bumpSlice_eq_smul_tentSq hc (x - s), bumpSlice_eq_smul_tentSq hc x,
      CenteredMaximal.abs_rpow_neg_two, hw]
    ring
  · refine (integrable_zero ℝ ℝ volume).congr (Filter.Eventually.of_forall fun s => ?_)
    simp [bumpSlice_eq_zero hc]

/-! ### The generator of the bump -/

/-- **The second difference of the bump along the first axis** is the second difference of the
slice. -/
theorem secondDiff_bump_zero (z : Fin 2 → ℝ) (t : ℝ) :
    CenteredMaximal.secondDiff bump 0 z t = bumpSlice (z 1) (z 0 + t)
      + bumpSlice (z 1) (z 0 - t) - 2 * bumpSlice (z 1) (z 0) := by
  rw [CenteredMaximal.secondDiff, bump_add_single_zero, bump_sub_single_zero,
    bump_eq_bumpSlice_zero]

/-- **The second difference of the bump along the second axis** is the second difference of the
slice. -/
theorem secondDiff_bump_one (z : Fin 2 → ℝ) (t : ℝ) :
    CenteredMaximal.secondDiff bump 1 z t = bumpSlice (z 0) (z 1 + t)
      + bumpSlice (z 0) (z 1 - t) - 2 * bumpSlice (z 0) (z 1) := by
  rw [CenteredMaximal.secondDiff, bump_add_single_one, bump_sub_single_one,
    bump_eq_bumpSlice_one]

/-- The generator of the bump is the sum of the two one-dimensional jump integrals of its
slices. -/
theorem jumpGen_bump_eq_add (z : Fin 2 → ℝ) :
    CenteredMaximal.jumpGen 1 bump z
      = jumpGen1 1 (bumpSlice (z 1)) (z 0) + jumpGen1 1 (bumpSlice (z 0)) (z 1) := by
  simp only [CenteredMaximal.jumpGen, Fin.sum_univ_two, jumpGen1, secondDiff_bump_zero,
    secondDiff_bump_one]

/-- **The Cauchy jump generator of the bump in closed form.** Off both coordinate axes and inside
the unit diamond,
`jumpGen 1 ψ (u, v) = 4 ((1 − |v|) Ffun (|u| / (1 − |v|)) + (1 − |u|) Ffun (|v| / (1 − |u|)))`. -/
theorem jumpGen_bump {z : Fin 2 → ℝ} (hu : z 0 ≠ 0) (hv : z 1 ≠ 0) (hz : diamondNorm z < 1) :
    CenteredMaximal.jumpGen 1 bump z
      = 4 * ((1 - |z 1|) * Ffun (|z 0| / (1 - |z 1|))
        + (1 - |z 0|) * Ffun (|z 1| / (1 - |z 0|))) := by
  have hr : |z 0| + |z 1| < 1 := hz
  have h0 : |z 0| < 1 := by linarith [abs_nonneg (z 1)]
  have h1 : |z 1| < 1 := by linarith [abs_nonneg (z 0)]
  rw [jumpGen_bump_eq_add, jumpGen1_bumpSlice h1 hu, jumpGen1_bumpSlice h0 hv]
  ring

/-! ### The Jensen bound -/

/-- **The angular bound on the open unit diamond.** Weighted Jensen against the concavity of `Ffun`
collapses the two-variable closed form to a function of the diamond radius alone. -/
theorem jumpGen_bump_le {z : Fin 2 → ℝ} (hu : z 0 ≠ 0) (hv : z 1 ≠ 0) (hz : diamondNorm z < 1) :
    CenteredMaximal.jumpGen 1 bump z ≤ 4 * Tfun (diamondNorm z) := by
  have hdn : diamondNorm z = |z 0| + |z 1| := rfl
  have hu0 : 0 < |z 0| := abs_pos.2 hu
  have hv0 : 0 < |z 1| := abs_pos.2 hv
  have hr : |z 0| + |z 1| < 1 := hz
  have hau : (0 : ℝ) < 1 - |z 1| := by linarith
  have hav : (0 : ℝ) < 1 - |z 0| := by linarith
  have h2r : (0 : ℝ) < 2 - (|z 0| + |z 1|) := by linarith
  have hau' : 1 - |z 1| ≠ 0 := hau.ne'
  have hav' : 1 - |z 0| ≠ 0 := hav.ne'
  have h2r' : 2 - (|z 0| + |z 1|) ≠ 0 := h2r.ne'
  have hsum : (1 - |z 1|) / (2 - (|z 0| + |z 1|)) + (1 - |z 0|) / (2 - (|z 0| + |z 1|)) = 1 := by
    field_simp
    ring
  have ht1 : |z 0| / (1 - |z 1|) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_lt_one hau]; linarith⟩
  have ht2 : |z 1| / (1 - |z 0|) ∈ Ioo (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_lt_one hav]; linarith⟩
  have hpt : (1 - |z 1|) / (2 - (|z 0| + |z 1|)) * (|z 0| / (1 - |z 1|))
      + (1 - |z 0|) / (2 - (|z 0| + |z 1|)) * (|z 1| / (1 - |z 0|))
      = (|z 0| + |z 1|) / (2 - (|z 0| + |z 1|)) := by
    field_simp
  have key := concaveOn_Ffun.2 ht1 ht2 (by positivity) (by positivity) hsum
  simp only [smul_eq_mul] at key
  rw [hpt] at key
  have hexp : (2 - (|z 0| + |z 1|))
      * ((1 - |z 1|) / (2 - (|z 0| + |z 1|)) * Ffun (|z 0| / (1 - |z 1|))
        + (1 - |z 0|) / (2 - (|z 0| + |z 1|)) * Ffun (|z 1| / (1 - |z 0|)))
      = (1 - |z 1|) * Ffun (|z 0| / (1 - |z 1|)) + (1 - |z 0|) * Ffun (|z 1| / (1 - |z 0|)) := by
    field_simp
  have hmul := mul_le_mul_of_nonneg_left key h2r.le
  rw [hexp] at hmul
  rw [jumpGen_bump hu hv hz, hdn, Tfun]
  linarith

/-! ### The exterior bound -/

/-- The value `Ffun 1 = 2 − 2 log 2` of the closed form at `1` is positive. -/
private theorem two_sub_two_mul_log_two_pos : 0 < 2 - 2 * Real.log 2 := by
  nlinarith [Real.log_two_lt_d9]

/-- The jump integral of a slice, for a base point outside the unit diamond: either the slice
vanishes identically, or its argument is at least `1`, where `Ffun ≤ 2 − 2 log 2`. -/
private theorem jumpGen1_bumpSlice_le_exterior {c x : ℝ} (hx : x ≠ 0) (hcx : 1 ≤ |x| + |c|) :
    jumpGen1 1 (bumpSlice c) x ≤ 4 * max (1 - |c|) 0 * (2 - 2 * Real.log 2) := by
  rcases lt_or_ge |c| 1 with hc | hc
  · have ha : (0 : ℝ) < 1 - |c| := by linarith
    have h1 : 1 ≤ |x| / (1 - |c|) := by rw [le_div_iff₀ ha]; linarith
    rw [jumpGen1_bumpSlice hc hx, max_eq_left ha.le]
    nlinarith [Ffun_le_of_one_le h1]
  · rw [jumpGen1_bumpSlice_of_one_le hc, max_eq_right (by linarith)]
    simp

/-- **The angular bound outside the unit diamond.** Every surviving slice has argument at least
`1`, where `Ffun ≤ 2 − 2 log 2`, and the surviving weights sum to at most `1`. -/
theorem jumpGen_bump_le_exterior {z : Fin 2 → ℝ} (hu : z 0 ≠ 0) (hv : z 1 ≠ 0)
    (hz : 1 ≤ diamondNorm z) : CenteredMaximal.jumpGen 1 bump z ≤ 4 * (2 - 2 * Real.log 2) := by
  have hr : 1 ≤ |z 0| + |z 1| := hz
  have hw : max (1 - |z 1|) 0 + max (1 - |z 0|) 0 ≤ 1 := by
    rcases le_or_gt 1 |z 1| with h1 | h1
    · rw [max_eq_right (by linarith)]
      exact le_trans (by rw [zero_add]) (max_le (by linarith [abs_nonneg (z 0)]) zero_le_one)
    · rcases le_or_gt 1 |z 0| with h0 | h0
      · rw [max_eq_right (by linarith : 1 - |z 0| ≤ 0), max_eq_left (by linarith)]
        linarith [abs_nonneg (z 1)]
      · rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - |z 1|),
          max_eq_left (by linarith : (0 : ℝ) ≤ 1 - |z 0|)]
        linarith
  have e0 := jumpGen1_bumpSlice_le_exterior (c := z 1) (x := z 0) hu (by linarith)
  have e1 := jumpGen1_bumpSlice_le_exterior (c := z 0) (x := z 1) hv (by linarith)
  rw [jumpGen_bump_eq_add]
  nlinarith [two_sub_two_mul_log_two_pos, le_max_right (1 - |z 1|) (0 : ℝ),
    le_max_right (1 - |z 0|) (0 : ℝ)]

/-! ### Properties of the angular bound -/

/-- **The closed form of the angular bound** on `(0, 1)`: the two logarithms of `2 − r` cancel,
leaving `Tfun r = 2 (2 − r) (1 − log 2 + log r) − 2 (1 − r) log (1 − r)`. -/
theorem Tfun_eq {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    Tfun r = 2 * (2 - r) * (1 - Real.log 2 + Real.log r) - 2 * (1 - r) * Real.log (1 - r) := by
  have h2r : (0 : ℝ) < 2 - r := by linarith
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have h2r' : (2 : ℝ) - r ≠ 0 := h2r.ne'
  have h1r' : (1 : ℝ) - r ≠ 0 := h1r.ne'
  have e1 : (1 : ℝ) - r / (2 - r) = (2 - 2 * r) / (2 - r) := by field_simp; ring
  have e2 : (1 : ℝ) + r / (2 - r) = 2 / (2 - r) := by field_simp; ring
  have l1 : Real.log |1 - r / (2 - r)|
      = Real.log 2 + Real.log (1 - r) - Real.log (2 - r) := by
    rw [e1, abs_of_nonneg (div_nonneg (by linarith) (by linarith)),
      Real.log_div (by linarith) h2r', show (2 : ℝ) - 2 * r = 2 * (1 - r) by ring,
      Real.log_mul two_ne_zero h1r']
  have l2 : Real.log (1 + r / (2 - r)) = Real.log 2 - Real.log (2 - r) := by
    rw [e2, Real.log_div two_ne_zero h2r']
  have l3 : Real.log (r / (2 - r)) = Real.log r - Real.log (2 - r) := Real.log_div hr.ne' h2r'
  simp only [Tfun, Ffun]
  rw [l1, l2, l3, e1, e2]
  field_simp
  ring

/-- The angular bound is nonpositive on `(0, 1/2]`, since `r ≤ 1/2` forces `r / (2 − r) ≤ 1/3`. -/
theorem Tfun_nonpos_of_le_half {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) : Tfun r ≤ 0 := by
  have h2r : (0 : ℝ) < 2 - r := by linarith
  have h1 : 0 < r / (2 - r) := by positivity
  have h2 : r / (2 - r) ≤ 1 / 3 := by rw [div_le_iff₀ h2r]; linarith
  have h3 := Ffun_nonpos_of_le_third h1 h2
  rw [Tfun]
  nlinarith

/-- The derivative of the angular bound,
`Tfun' r = 2 log 2 − 2 log r + 2 log (1 − r) + 4 / r − 2`. -/
theorem hasDerivAt_Tfun {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    HasDerivAt Tfun
      (2 * Real.log 2 - 2 * Real.log r + 2 * Real.log (1 - r) + 4 / r - 2) r := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have heq : ∀ᶠ x in 𝓝 r, Tfun x
      = 2 * (2 - x) * (1 - Real.log 2 + Real.log x) - 2 * (1 - x) * Real.log (1 - x) := by
    filter_upwards [Ioo_mem_nhds hr hr'] with x hx using Tfun_eq hx.1 hx.2
  refine (EventuallyEq.hasDerivAt_iff heq).2 ?_
  have hu : HasDerivAt (fun x : ℝ => 2 * (2 - x)) (-2) r := by
    simpa using ((hasDerivAt_id' (x := r)).const_sub 2).const_mul 2
  have hv : HasDerivAt (fun x : ℝ => 1 - Real.log 2 + Real.log x) r⁻¹ r :=
    (Real.hasDerivAt_log hr.ne').const_add (1 - Real.log 2)
  have hw : HasDerivAt (fun x : ℝ => 2 * (1 - x)) (-2) r := by
    simpa using ((hasDerivAt_id' (x := r)).const_sub 1).const_mul 2
  have hx : HasDerivAt (fun x : ℝ => 1 - x) (-1) r := (hasDerivAt_id' (x := r)).const_sub 1
  refine ((hu.mul hv).sub (hw.mul (hx.log h1r.ne'))).congr_deriv ?_
  field_simp
  ring

theorem deriv_Tfun {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    deriv Tfun r = 2 * Real.log 2 - 2 * Real.log r + 2 * Real.log (1 - r) + 4 / r - 2 :=
  (hasDerivAt_Tfun hr hr').deriv

/-- The second derivative of the angular bound on `(0, 1)`, `−2 (2 − r) / (r² (1 − r))`. -/
theorem hasDerivAt_deriv_Tfun {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    HasDerivAt (deriv Tfun) (-2 * (2 - r) / (r ^ 2 * (1 - r))) r := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have heq : ∀ᶠ x in 𝓝 r, deriv Tfun x
      = 2 * Real.log 2 - 2 * Real.log x + 2 * Real.log (1 - x) + 4 / x - 2 := by
    filter_upwards [Ioo_mem_nhds hr hr'] with x hx using deriv_Tfun hx.1 hx.2
  refine (EventuallyEq.hasDerivAt_iff heq).2 ?_
  have hu : HasDerivAt (fun x : ℝ => 2 * Real.log 2 - 2 * Real.log x) (-(2 * r⁻¹)) r := by
    simpa using ((Real.hasDerivAt_log hr.ne').const_mul 2).const_sub (2 * Real.log 2)
  have hx : HasDerivAt (fun x : ℝ => 1 - x) (-1) r := (hasDerivAt_id' (x := r)).const_sub 1
  have hv : HasDerivAt (fun x : ℝ => 2 * Real.log (1 - x)) (2 * (-1 / (1 - r))) r :=
    ((hx.log h1r.ne').const_mul 2)
  have hw : HasDerivAt (fun x : ℝ => 4 / x) ((0 * r - 4 * 1) / r ^ 2) r :=
    (hasDerivAt_const r (4 : ℝ)).div (hasDerivAt_id' (x := r)) hr.ne'
  refine (((hu.add hv).add hw).sub_const 2).congr_deriv ?_
  field_simp
  ring

theorem deriv2_Tfun {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    deriv^[2] Tfun r = -2 * (2 - r) / (r ^ 2 * (1 - r)) := by
  rw [show deriv^[2] Tfun r = deriv (deriv Tfun) r by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq],
    (hasDerivAt_deriv_Tfun hr hr').deriv]

/-- **The angular bound is uniformly strictly concave on `(0, 1)`**: `Tfun'' ≤ −27/2`, from
`27 r³ − 27 r² + 4 = (3 r − 2)² (3 r + 1) ≥ 0`. The true infimum of `|Tfun''|` is close to
`17.63`, attained near `r = 0.72`. -/
theorem deriv2_Tfun_le {r : ℝ} (hr : 0 < r) (hr' : r < 1) : deriv^[2] Tfun r ≤ -27 / 2 := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  rw [deriv2_Tfun hr hr', div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg (3 * r - 2)) (by linarith : (0 : ℝ) ≤ 3 * r + 1)]

end CenteredMaximal.Cauchy

end

end
