/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.FracRepresentation

/-!
# The moment hypothesis for the truncated diamond base

`CenteredMaximal.Fractional.jumpMoment_fracKernel` reduces the moment hypothesis
`JumpMoment (6/5) fracKernel` to the same hypothesis for the truncated diamond base
`T = truncBase (6/5) (7/4)`. This file discharges it, for every order `1 < α < 3/2`.

## Main results

* `jumpMoment_truncBase_of_lt`: `JumpMoment α (truncBase α R)` for `1 < α < 3/2` and `0 < R`;
* `jumpMoment_truncBase`: the `α = 6/5`, `R = 7/4` instance;
* `jumpMoment_fracKernel'`, `hKgen_fracKernel'`, `integrable_fracDensity_mul_min_one'`: the
  hypothesis-free forms of the three consequences isolated by `FracRepresentation`.

## Method

The base is *compactly supported* — it vanishes off the closed diamond of radius `R` — and that,
not any decay at infinity, is what makes the double integral
`∫∫ |Δ_j^t T (z)| min(1, ‖z‖) |t|^{-(1+α)} dz dt` finite. The step is split at `|t| = R/4`.

* **Large steps, `R/4 ≤ |t|`.** Only `T ∈ L¹` is used: the three displaced values integrate to
  `4 ∫ T` by translation invariance, and `∫_{|t| ≥ R/4} |t|^{-(1+α)} dt < ∞` because `α > 0`.
* **Small steps, `|t| < R/4`.** The three points `z`, `z ± t e_j` then lie on the same side of the
  boundary `{r = R}` unless `z` lies in the shell `{ |r − R| ≤ |t| }`. Off that shell and inside
  the diamond the base is the diamond power up to the additive constant `R^{-α}`, so its second
  difference is that of `r^{-α}`; off it and outside the diamond the second difference vanishes.
  On the shell the radial profile is Lipschitz — all three radii are at least `R/2` — so the
  second difference is `O(|t|)`, and `volume_shell_le` bounds the shell by `8 R |t|`; against the
  weight this contributes `|t|^{1-α}`, integrable because `α < 2`.
* **The homogeneous piece.** `lintegral_abs_brk_mul_le` bounds the plane integral of
  `|Δ_j^1 (r^{-α})|` weighted by the diamond radius by `O(|t|^{3-α})`; against the weight this
  contributes `|t|^{2-2α}`, integrable at the origin exactly for `α < 3/2`. The plane integral is
  taken in the coordinates `a = |z j|`, `b = |z (j+1)|`, and splits into three regions: `a > 2s`,
  where two derivatives of `r^{-α}` survive and the second difference is `O(s² (a+b)^{-α-2})`;
  `a ≤ 2s < b/2`, where only one does and it is `O(s b^{-α-1})`; and the core `a ≤ 2s`, `b ≤ 4s`,
  where the three displaced values are merely summed, the corner term `(|a − s| + b)^{-α}`
  included.

The exceptional set `{z (j+1) = 0}` — where the origin can be one of the three points, and the
identification of the base with the diamond power fails — is a coordinate line, hence null.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Cauchy

open scoped ENNReal

namespace CenteredMaximal.Fractional

/-! ### Elementary lower integrals of powers -/

/-- `∫₀^c v^p dv = c^{p+1}/(p+1)` as a lower integral, for `−1 < p`. -/
private theorem lintegral_Ioc_rpow {p c : ℝ} (hp : -1 < p) (hc : 0 ≤ c) :
    ∫⁻ v in Ioc 0 c, ENNReal.ofReal (v ^ p) = ENNReal.ofReal (c ^ (p + 1) / (p + 1)) := by
  have hint : IntegrableOn (fun v : ℝ => v ^ p) (Ioc 0 c) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hc).1
      (intervalIntegral.intervalIntegrable_rpow' hp)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) c)] fun v : ℝ => v ^ p :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun v hv => Real.rpow_nonneg hv.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← intervalIntegral.integral_of_le hc, integral_rpow (Or.inl hp),
    Real.zero_rpow (by linarith), sub_zero]

/-- `∫_c^∞ v^p dv = −c^{p+1}/(p+1)` as a lower integral, for `p < −1` and `0 < c`. -/
private theorem lintegral_Ioi_rpow {p c : ℝ} (hp : p < -1) (hc : 0 < c) :
    ∫⁻ v in Ioi c, ENNReal.ofReal (v ^ p) = ENNReal.ofReal (-c ^ (p + 1) / (p + 1)) := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi c)] fun v : ℝ => v ^ p :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun v hv => Real.rpow_nonneg (hc.trans hv).le _
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hp hc) hnn,
    integral_Ioi_rpow_of_lt hp hc]

/-- Translating a half-line: `∫_c^∞ g(m + v) dv = ∫_{m+c}^∞ g(t) dt`. -/
private theorem lintegral_Ioi_comp_add (g : ℝ → ℝ≥0∞) (c m : ℝ) :
    ∫⁻ v in Ioi c, g (m + v) = ∫⁻ t in Ioi (m + c), g t := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_add_left_eq_self (fun t => (Ioi (m + c)).indicator g t) m]
  refine lintegral_congr fun v => ?_
  simp [indicator_apply]

/-- `∫_c^∞ (v + m)^p dv = −(m + c)^{p+1}/(p+1)` for `p < −1` and `0 < m + c`. -/
private theorem lintegral_Ioi_add_rpow {p c m : ℝ} (hp : p < -1) (hm : 0 < m + c) :
    ∫⁻ v in Ioi c, ENNReal.ofReal ((v + m) ^ p)
      = ENNReal.ofReal (-(m + c) ^ (p + 1) / (p + 1)) := by
  calc ∫⁻ v in Ioi c, ENNReal.ofReal ((v + m) ^ p)
      = ∫⁻ t in Ioi (m + c), ENNReal.ofReal (t ^ p) := by
        rw [← lintegral_Ioi_comp_add (fun t : ℝ => ENNReal.ofReal (t ^ p)) c m]
        exact lintegral_congr fun v => by rw [add_comm]
    _ = _ := lintegral_Ioi_rpow hp hm

/-! ### Reduction of a plane integral to an iterated integral -/

/-- A function of `|x|` integrates to twice its integral over the positive half-line. -/
private theorem lintegral_comp_abs (h : ℝ → ℝ≥0∞) :
    ∫⁻ x, h |x| = 2 * ∫⁻ x in Ioi 0, h x := by
  rw [← lintegral_add_compl (fun x => h |x|) measurableSet_Ioi, compl_Ioi, two_mul]
  congr 1
  · exact setLIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [abs_of_pos hx]
  · calc ∫⁻ x in Iic 0, h |x| = ∫⁻ x, (Iic 0).indicator (fun x => h |x|) (-x) := by
          rw [lintegral_neg_eq_self ((Iic 0).indicator fun x => h |x|),
            lintegral_indicator measurableSet_Iic]
      _ = ∫⁻ x in Ici 0, h x := by
          rw [← lintegral_indicator measurableSet_Ici]
          refine lintegral_congr fun x => ?_
          by_cases hx : 0 ≤ x
          · simp [hx, abs_of_nonneg hx]
          · simp [hx]
      _ = ∫⁻ x in Ioi 0, h x := (setLIntegral_congr Ioi_ae_eq_Ici).symm

/-- A plane lower integral is the iterated lower integral of the two coordinates. -/
private theorem lintegral_finTwoArrow (f : ℝ → ℝ → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) :
    ∫⁻ z : Fin 2 → ℝ, f (z 0) (z 1) = ∫⁻ u, ∫⁻ v, f u v := by
  have h1 : (∫⁻ z : Fin 2 → ℝ, f (z 0) (z 1)) = ∫⁻ p : ℝ × ℝ, f p.1 p.2 := by
    rw [← (volume_preserving_finTwoArrow ℝ).map_eq, lintegral_map_equiv]
    rfl
  rw [h1]
  exact lintegral_prod _ hf.aemeasurable

/-- Tonelli on the open quadrant. -/
private theorem lintegral_Ioi_swap (f : ℝ → ℝ → ℝ≥0∞) (hf : Measurable (Function.uncurry f)) :
    (∫⁻ a in Ioi 0, ∫⁻ b in Ioi 0, f a b) = ∫⁻ b in Ioi 0, ∫⁻ a in Ioi 0, f a b :=
  lintegral_lintegral_swap hf.aemeasurable

/-- **The plane integral of a function of the two absolute coordinates.** -/
private theorem lintegral_abs_pair (f : ℝ → ℝ → ℝ≥0∞) (hf : Measurable (Function.uncurry f))
    (j : Fin 2) :
    ∫⁻ z : Fin 2 → ℝ, f |z j| |z (j + 1)| = 4 * ∫⁻ a in Ioi 0, ∫⁻ b in Ioi 0, f a b := by
  have key : ∀ g : ℝ → ℝ → ℝ≥0∞, Measurable (Function.uncurry g) →
      (∫⁻ z : Fin 2 → ℝ, g |z 0| |z 1|) = 4 * ∫⁻ a in Ioi 0, ∫⁻ b in Ioi 0, g a b := by
    intro g hg
    have h1 : (∫⁻ z : Fin 2 → ℝ, g |z 0| |z 1|) = ∫⁻ u, ∫⁻ v, g |u| |v| :=
      lintegral_finTwoArrow (fun u v => g |u| |v|)
        (hg.comp ((continuous_abs.comp continuous_fst).prodMk
          (continuous_abs.comp continuous_snd)).measurable)
    have h2 : ∀ u : ℝ, (∫⁻ v, g |u| |v|) = 2 * ∫⁻ v in Ioi 0, g |u| v := fun u =>
      lintegral_comp_abs fun v => g |u| v
    have h3 : (∫⁻ u, (fun w : ℝ => ∫⁻ v in Ioi 0, g w v) |u|)
        = 2 * ∫⁻ u in Ioi 0, ∫⁻ v in Ioi 0, g u v :=
      lintegral_comp_abs fun w => ∫⁻ v in Ioi 0, g w v
    rw [h1, lintegral_congr h2, lintegral_const_mul' 2 _ (by simp), h3]
    ring
  fin_cases j
  · simpa using key f hf
  · have hswap := lintegral_Ioi_swap f hf
    have := key (fun a b => f b a) (hf.comp measurable_swap)
    simpa [← hswap] using this

/-! ### Pointwise bounds on the second difference of the diamond power -/

/-- **The quantitative second-difference bound** for `y ↦ y^{-α}` on a half-line, reproved here
because `CenteredMaximal.Fractional.DiamondReduction` keeps it private: if the step `t` keeps
`x ± t` inside `[c, ∞)`, the symmetric second difference is `O(t²)` with constant
`2 α (α + 1) c^{-α-2}`. -/
private theorem abs_rpow_secondDiff_le {α c x t : ℝ} (hα : 0 < α) (hc : 0 < c) (ht0 : 0 ≤ t)
    (ht : t ≤ x - c) :
    |(x + t) ^ (-α) + (x - t) ^ (-α) - 2 * x ^ (-α)|
      ≤ 2 * (α * (α + 1) * c ^ (-α - 2)) * t ^ 2 := by
  have hM0 : (0 : ℝ) ≤ α * (α + 1) * c ^ (-α - 2) := by positivity
  set M := α * (α + 1) * c ^ (-α - 2) with hM
  have hd1 : ∀ y : ℝ, y ≠ 0 → HasDerivAt (fun y : ℝ => y ^ (-α)) (-α * y ^ (-α - 1)) y :=
    fun _ hy => Real.hasDerivAt_rpow_const (Or.inl hy)
  have hd2 : ∀ y : ℝ, y ≠ 0 →
      HasDerivAt (fun y : ℝ => -α * y ^ (-α - 1)) (α * (α + 1) * y ^ (-α - 2)) y := by
    intro y hy
    have h := (Real.hasDerivAt_rpow_const (x := y) (p := -α - 1) (Or.inl hy)).const_mul (-α)
    rw [show (-α - 1 - 1 : ℝ) = -α - 2 from by ring] at h
    exact h.congr_deriv (by ring)
  have hbd : ∀ y ∈ Ici c, ‖α * (α + 1) * y ^ (-α - 2)‖ ≤ M := by
    intro y hy
    have hy0 : 0 < y := hc.trans_le hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hM]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hc hy (by linarith))
      (by positivity)
  have hmv : ∀ u ∈ Ici c, ∀ v ∈ Ici c,
      |-α * u ^ (-α - 1) - -α * v ^ (-α - 1)| ≤ M * |u - v| := by
    intro u hu v hv
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun y : ℝ => -α * y ^ (-α - 1))
      (f' := fun y : ℝ => α * (α + 1) * y ^ (-α - 2)) (s := Ici c)
      (fun y hy => (hd2 y (hc.trans_le hy).ne').hasDerivWithinAt) hbd (convex_Ici c) hv hu
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h
  rcases eq_or_lt_of_le ht0 with rfl | ht0'
  · rw [add_zero, sub_zero, show x ^ (-α) + x ^ (-α) - 2 * x ^ (-α) = 0 from by ring]
    simp
  have hxc : c ≤ x - t := by linarith
  have hcont1 : ContinuousOn (fun y : ℝ => y ^ (-α)) (Icc x (x + t)) := fun y hy =>
    (hd1 y (by linarith [hy.1] : (0 : ℝ) < y).ne').continuousAt.continuousWithinAt
  have hcont2 : ContinuousOn (fun y : ℝ => y ^ (-α)) (Icc (x - t) x) := fun y hy =>
    (hd1 y (by linarith [hy.1] : (0 : ℝ) < y).ne').continuousAt.continuousWithinAt
  obtain ⟨u, hu, hsu⟩ := exists_hasDerivAt_eq_slope (fun y : ℝ => y ^ (-α))
    (fun y : ℝ => -α * y ^ (-α - 1)) (by linarith : x < x + t) hcont1
    (fun y hy => hd1 y (by linarith [hy.1] : (0 : ℝ) < y).ne')
  obtain ⟨v, hv, hsv⟩ := exists_hasDerivAt_eq_slope (fun y : ℝ => y ^ (-α))
    (fun y : ℝ => -α * y ^ (-α - 1)) (by linarith : x - t < x) hcont2
    (fun y hy => hd1 y (by linarith [hy.1] : (0 : ℝ) < y).ne')
  have e1 : (x + t) ^ (-α) - x ^ (-α) = t * (-α * u ^ (-α - 1)) := by
    rw [hsu, show x + t - x = t from by ring]
    field_simp
  have e2 : x ^ (-α) - (x - t) ^ (-α) = t * (-α * v ^ (-α - 1)) := by
    rw [hsv, show x - (x - t) = t from by ring]
    field_simp
  have hN : (x + t) ^ (-α) + (x - t) ^ (-α) - 2 * x ^ (-α)
      = t * (-α * u ^ (-α - 1) - -α * v ^ (-α - 1)) := by linear_combination e1 - e2
  have hbnd := hmv u (mem_Ici.2 (by linarith [hu.1])) v (mem_Ici.2 (by linarith [hv.1]))
  have h2t : |-α * u ^ (-α - 1) - -α * v ^ (-α - 1)| ≤ M * (2 * t) := by
    refine hbnd.trans (mul_le_mul_of_nonneg_left ?_ hM0)
    rw [abs_of_pos (by linarith [hu.1, hv.2] : (0 : ℝ) < u - v)]
    linarith [hu.2, hv.1]
  rw [hN, abs_mul, abs_of_pos ht0']
  calc t * |-α * u ^ (-α - 1) - -α * v ^ (-α - 1)| ≤ t * (M * (2 * t)) :=
        mul_le_mul_of_nonneg_left h2t ht0'.le
    _ = 2 * M * t ^ 2 := by ring

/-- **The first-difference bound** for `y ↦ (y + b)^{-α}` on `[0, ∞)`: the derivative is bounded
there by `α b^{-α-1}`. -/
private theorem abs_rpow_shift_sub_le {α b x y : ℝ} (hα : 0 < α) (hb : 0 < b) (hx : 0 ≤ x)
    (hy : 0 ≤ y) : |(x + b) ^ (-α) - (y + b) ^ (-α)| ≤ α * b ^ (-α - 1) * |x - y| := by
  have hd : ∀ u : ℝ, 0 ≤ u →
      HasDerivAt (fun w : ℝ => (w + b) ^ (-α)) (-α * (u + b) ^ (-α - 1)) u := by
    intro u hu
    have h1 : HasDerivAt (fun w : ℝ => w + b) 1 u := (hasDerivAt_id u).add_const b
    exact (h1.rpow_const (p := -α) (Or.inl (by positivity : u + b ≠ 0))).congr_deriv (by ring)
  have hbd : ∀ u ∈ Ici (0 : ℝ), ‖-α * (u + b) ^ (-α - 1)‖ ≤ α * b ^ (-α - 1) := by
    intro u hu
    have hu0 : (0 : ℝ) ≤ u := hu
    have h1 : (u + b) ^ (-α - 1) ≤ b ^ (-α - 1) :=
      Real.rpow_le_rpow_of_nonpos hb (by linarith) (by linarith)
    have h2 : (0 : ℝ) ≤ (u + b) ^ (-α - 1) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (by linarith : -α ≤ 0), neg_neg,
      abs_of_nonneg h2]
    exact mul_le_mul_of_nonneg_left h1 hα.le
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun w : ℝ => (w + b) ^ (-α)) (f' := fun u : ℝ => -α * (u + b) ^ (-α - 1))
    (s := Ici (0 : ℝ)) (fun u hu => (hd u hu).hasDerivWithinAt) hbd (convex_Ici 0)
    (mem_Ici.2 hy) (mem_Ici.2 hx)
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h

/-! ### The second difference of the diamond power in absolute coordinates -/

/-- The axis-`j` second difference of the diamond power at `z` with step `t`, read off in the
coordinates `a = |z j|`, `b = |z (j+1)|`, `s = |t|`. -/
private def brk (α a b s : ℝ) : ℝ :=
  (a + s + b) ^ (-α) + (|a - s| + b) ^ (-α) - 2 * (a + b) ^ (-α)

private theorem diamondNorm_eq_abs_add (z : Fin 2 → ℝ) (j : Fin 2) :
    diamondNorm z = |z j| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem diamondNorm_add_single (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z + s • Pi.single j 1) = |z j + s| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem diamondNorm_sub_single (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z - s • Pi.single j 1) = |z j - s| + |z (j + 1)| := by
  rw [sub_eq_add_neg, ← neg_smul, diamondNorm_add_single, ← sub_eq_add_neg]

/-- The unordered pair `{|c + t|, |c − t|}` is `{|c| + |t|, ||c| − |t||}`. -/
private theorem abs_pair_eq (c t : ℝ) :
    (|c + t| = |c| + |t| ∧ |c - t| = |(|c| - |t|)|) ∨
      (|c - t| = |c| + |t| ∧ |c + t| = |(|c| - |t|)|) := by
  rcases le_total 0 c with hc | hc <;> rcases le_total 0 t with ht | ht
  · refine Or.inl ⟨?_, ?_⟩
    · rw [abs_of_nonneg hc, abs_of_nonneg ht, abs_of_nonneg (by linarith : (0 : ℝ) ≤ c + t)]
    · rw [abs_of_nonneg hc, abs_of_nonneg ht]
  · refine Or.inr ⟨?_, ?_⟩
    · rw [abs_of_nonneg hc, abs_of_nonpos ht, abs_of_nonneg (by linarith : (0 : ℝ) ≤ c - t)]
      ring
    · rw [abs_of_nonneg hc, abs_of_nonpos ht, show c - -t = c + t from by ring]
  · refine Or.inr ⟨?_, ?_⟩
    · rw [abs_of_nonpos hc, abs_of_nonneg ht, abs_of_nonpos (by linarith : c - t ≤ 0)]
      ring
    · rw [abs_of_nonpos hc, abs_of_nonneg ht, show -c - t = -(c + t) from by ring, abs_neg]
  · refine Or.inl ⟨?_, ?_⟩
    · rw [abs_of_nonpos hc, abs_of_nonpos ht, abs_of_nonpos (by linarith : c + t ≤ 0)]
      ring
    · rw [abs_of_nonpos hc, abs_of_nonpos ht, show -c - -t = -(c - t) from by ring, abs_neg]

/-- The two displaced values of `w ↦ (|w| + b)^{-α}` only depend on `|c|` and `|t|`. -/
private theorem rpow_pair_abs (α b c t : ℝ) :
    (|c + t| + b) ^ (-α) + (|c - t| + b) ^ (-α)
      = (|c| + |t| + b) ^ (-α) + (|(|c| - |t|)| + b) ^ (-α) := by
  rcases abs_pair_eq c t with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]
    exact add_comm _ _

/-- The axis-`j` second difference of the diamond power is `brk`. -/
private theorem secondDiff_diamondPow_eq (α : ℝ) (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    secondDiff (diamondPow α) j z t = brk α |z j| |z (j + 1)| |t| := by
  rw [secondDiff, diamondPow, diamondPow, diamondPow, diamondNorm_add_single,
    diamondNorm_sub_single, diamondNorm_eq_abs_add z j, brk]
  linarith [rpow_pair_abs α |z (j + 1)| (z j) t]

/-! ### The three bounds on `brk` -/

/-- Away from the corner, `|brk| = O(s²)`. -/
private theorem abs_brk_le_sq {α a b s : ℝ} (hα : 0 < α) (hb : 0 ≤ b) (hs : 0 ≤ s)
    (ha0 : 0 < a) (ha : 2 * s ≤ a) :
    |brk α a b s| ≤ 2 * (α * (α + 1) * (a / 2 + b) ^ (-α - 2)) * s ^ 2 := by
  have hc : (0 : ℝ) < a / 2 + b := by linarith
  have habs : |a - s| = a - s := abs_of_nonneg (by linarith)
  have h := abs_rpow_secondDiff_le (α := α) (c := a / 2 + b) (x := a + b) (t := s) hα hc hs
    (by linarith)
  rw [brk, habs, show a + s + b = a + b + s from by ring, show a - s + b = a + b - s from by ring]
  exact h

/-- Near the axes only one derivative survives, and `|brk| = O(s)`. -/
private theorem abs_brk_le_lin {α a b s : ℝ} (hα : 0 < α) (hb : 0 < b) (ha : 0 ≤ a)
    (hs : 0 ≤ s) : |brk α a b s| ≤ 2 * (α * b ^ (-α - 1)) * s := by
  have hd1 : |(a + s + b) ^ (-α) - (a + b) ^ (-α)| ≤ α * b ^ (-α - 1) * s := by
    have h := abs_rpow_shift_sub_le (α := α) (b := b) (x := a + s) (y := a) hα hb
      (by linarith) ha
    rw [show a + s + b = a + s + b from rfl] at h
    calc |(a + s + b) ^ (-α) - (a + b) ^ (-α)| ≤ α * b ^ (-α - 1) * |a + s - a| := h
      _ = α * b ^ (-α - 1) * s := by rw [show a + s - a = s from by ring, abs_of_nonneg hs]
  have hd2 : |(|a - s| + b) ^ (-α) - (a + b) ^ (-α)| ≤ α * b ^ (-α - 1) * s := by
    have h := abs_rpow_shift_sub_le (α := α) (b := b) (x := |a - s|) (y := a) hα hb
      (abs_nonneg _) ha
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rcases le_total s a with hsa | hsa
    · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - s),
        show a - s - a = -s from by ring, abs_neg, abs_of_nonneg hs]
    · rw [abs_of_nonpos (by linarith : a - s ≤ 0), abs_le]
      constructor <;> [linarith; linarith]
  rw [brk]
  calc |(a + s + b) ^ (-α) + (|a - s| + b) ^ (-α) - 2 * (a + b) ^ (-α)|
      ≤ |(a + s + b) ^ (-α) - (a + b) ^ (-α)| + |(|a - s| + b) ^ (-α) - (a + b) ^ (-α)| := by
        rw [show (a + s + b) ^ (-α) + (|a - s| + b) ^ (-α) - 2 * (a + b) ^ (-α)
            = ((a + s + b) ^ (-α) - (a + b) ^ (-α)) + ((|a - s| + b) ^ (-α) - (a + b) ^ (-α))
          from by ring]
        exact abs_add_le _ _
    _ ≤ α * b ^ (-α - 1) * s + α * b ^ (-α - 1) * s := add_le_add hd1 hd2
    _ = 2 * (α * b ^ (-α - 1)) * s := by ring

/-- The crude bound, keeping the corner term. -/
private theorem abs_brk_le_sum {α a b s : ℝ} (hα : 0 < α) (hb : 0 < b) (ha : 0 ≤ a)
    (hs : 0 ≤ s) : |brk α a b s| ≤ 3 * (a + b) ^ (-α) + (|a - s| + b) ^ (-α) := by
  have hab : (0 : ℝ) < a + b := by linarith
  have h1 : (a + s + b) ^ (-α) ≤ (a + b) ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos hab (by linarith) (by linarith)
  have h2 : (0 : ℝ) ≤ (a + s + b) ^ (-α) := Real.rpow_nonneg (by linarith) _
  have h3 : (0 : ℝ) ≤ (|a - s| + b) ^ (-α) := Real.rpow_nonneg (by positivity) _
  have h4 : (0 : ℝ) ≤ (a + b) ^ (-α) := Real.rpow_nonneg hab.le _
  rw [brk, abs_le]
  constructor <;> linarith

/-! ### The inner integral in the first coordinate -/

/-- `−x/(1 − α) = x/(α − 1)`. -/
private theorem neg_div_one_sub {α : ℝ} (x : ℝ) : -x / (1 - α) = x / (α - 1) := by
  rw [neg_div, show (1 - α : ℝ) = -(α - 1) from by ring, div_neg, neg_neg]

private theorem measurable_brk (α s : ℝ) : Measurable fun p : ℝ × ℝ => brk α p.1 p.2 s := by
  have h1 : Continuous fun p : ℝ × ℝ => p.1 + s + p.2 := by fun_prop
  have h2 : Continuous fun p : ℝ × ℝ => |p.1 - s| + p.2 :=
    ((continuous_fst.sub continuous_const).abs).add continuous_snd
  have h3 : Continuous fun p : ℝ × ℝ => p.1 + p.2 := by fun_prop
  unfold brk
  exact ((h1.measurable.pow_const _).add (h2.measurable.pow_const _)).sub
    (measurable_const.mul (h3.measurable.pow_const _))

/-- `b^{-α-1} · b = b^{-α}`. -/
private theorem rpow_neg_sub_one_mul {α b : ℝ} (hb : 0 < b) : b ^ (-α - 1) * b = b ^ (-α) := by
  rw [← Real.rpow_add_one hb.ne' (-α - 1), show (-α - 1 + 1 : ℝ) = -α from by ring]

/-- **The leading region `a > 2s`.** -/
private theorem lintegral_a_far {α b s : ℝ} (hα : 1 < α) (hb : 0 < b) (hs : 0 < s) :
    ∫⁻ a in Ioi (2 * s), ENNReal.ofReal (32 * α * (α + 1) * s ^ 2 * (a + b) ^ (-α - 1))
      = ENNReal.ofReal (32 * (α + 1) * s ^ 2 * (b + 2 * s) ^ (-α)) := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hK : (0 : ℝ) ≤ 32 * α * (α + 1) * s ^ 2 := by positivity
  calc ∫⁻ a in Ioi (2 * s), ENNReal.ofReal (32 * α * (α + 1) * s ^ 2 * (a + b) ^ (-α - 1))
      = ∫⁻ a in Ioi (2 * s),
          ENNReal.ofReal (32 * α * (α + 1) * s ^ 2) * ENNReal.ofReal ((a + b) ^ (-α - 1)) :=
        lintegral_congr fun a => ENNReal.ofReal_mul hK
    _ = ENNReal.ofReal (32 * α * (α + 1) * s ^ 2)
          * ∫⁻ a in Ioi (2 * s), ENNReal.ofReal ((a + b) ^ (-α - 1)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (32 * α * (α + 1) * s ^ 2)
          * ENNReal.ofReal (-(b + 2 * s) ^ (-α) / (-α)) := by
        rw [lintegral_Ioi_add_rpow (p := -α - 1) (c := 2 * s) (m := b) (by linarith)
          (by linarith), show (-α - 1 + 1 : ℝ) = -α from by ring]
    _ = ENNReal.ofReal (32 * (α + 1) * s ^ 2 * (b + 2 * s) ^ (-α)) := by
        rw [← ENNReal.ofReal_mul hK]
        congr 1
        field_simp

/-- **The near region `0 < a ≤ 2s`.** Past `b = 4s` the near-axis bound applies; below it the
crude bound with the corner term does. -/
private theorem lintegral_a_near {α b s : ℝ} (hα : 1 < α) (hα' : α < 2) (hb : 0 < b)
    (hs : 0 < s) :
    ∫⁻ a in Ioc 0 (2 * s), ENNReal.ofReal (|brk α a b s| * (a + b))
      ≤ (Ioi (4 * s)).indicator (fun b => ENNReal.ofReal (8 * α * s ^ 2 * b ^ (-α))) b
        + (Iic (4 * s)).indicator
            (fun b => ENNReal.ofReal (30 * s / (α - 1) * b ^ (1 - α))) b := by
  have hα0 : (0 : ℝ) < α := by linarith
  by_cases hbs : 4 * s < b
  · rw [indicator_of_mem (mem_Ioi.2 hbs), indicator_of_notMem (by simp; linarith), add_zero]
    have hpt : ∀ a ∈ Ioc (0 : ℝ) (2 * s),
        ENNReal.ofReal (|brk α a b s| * (a + b))
          ≤ ENNReal.ofReal (4 * α * s * b ^ (-α)) := by
      intro a ha
      refine ENNReal.ofReal_le_ofReal ?_
      calc |brk α a b s| * (a + b) ≤ 2 * (α * b ^ (-α - 1)) * s * (2 * b) :=
            mul_le_mul (abs_brk_le_lin hα0 hb ha.1.le hs.le) (by linarith [ha.2])
              (by linarith [ha.1, hb]) (by positivity)
        _ = 4 * α * s * (b ^ (-α - 1) * b) := by ring
        _ = 4 * α * s * b ^ (-α) := by rw [rpow_neg_sub_one_mul hb]
    calc ∫⁻ a in Ioc 0 (2 * s), ENNReal.ofReal (|brk α a b s| * (a + b))
        ≤ ∫⁻ _a in Ioc (0 : ℝ) (2 * s), ENNReal.ofReal (4 * α * s * b ^ (-α)) :=
          setLIntegral_mono' measurableSet_Ioc hpt
      _ = ENNReal.ofReal (4 * α * s * b ^ (-α)) * ENNReal.ofReal (2 * s) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
      _ = ENNReal.ofReal (8 * α * s ^ 2 * b ^ (-α)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  · rw [indicator_of_notMem (by simpa using hbs),
      indicator_of_mem (by simpa using le_of_not_gt hbs), zero_add]
    have hpt : ∀ a ∈ Ioc (0 : ℝ) (2 * s),
        ENNReal.ofReal (|brk α a b s| * (a + b))
          ≤ ENNReal.ofReal (18 * s * (a + b) ^ (-α))
            + ENNReal.ofReal (6 * s * (|a - s| + b) ^ (-α)) := by
      intro a ha
      have ha0 : (0 : ℝ) < a := ha.1
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hsum := abs_brk_le_sum (α := α) (a := a) (b := b) (s := s) hα0 hb ha.1.le hs.le
      have hw : a + b ≤ 6 * s := by linarith [ha.2, le_of_not_gt hbs]
      calc |brk α a b s| * (a + b)
          ≤ (3 * (a + b) ^ (-α) + (|a - s| + b) ^ (-α)) * (6 * s) :=
            mul_le_mul hsum hw (by linarith [ha.1, hb]) (by positivity)
        _ = 18 * s * (a + b) ^ (-α) + 6 * s * (|a - s| + b) ^ (-α) := by ring
    have hm1 : Measurable fun a : ℝ => ENNReal.ofReal (18 * s * (a + b) ^ (-α)) :=
      ENNReal.measurable_ofReal.comp
        (measurable_const.mul ((measurable_id.add_const b).pow_const _))
    have hcorner : (∫⁻ a in Ioc (0 : ℝ) (2 * s), ENNReal.ofReal (6 * s * (|a - s| + b) ^ (-α)))
        ≤ ENNReal.ofReal (12 * s * (b ^ (1 - α) / (α - 1))) := by
      calc ∫⁻ a in Ioc (0 : ℝ) (2 * s), ENNReal.ofReal (6 * s * (|a - s| + b) ^ (-α))
          ≤ ∫⁻ a : ℝ, ENNReal.ofReal (6 * s * (|a - s| + b) ^ (-α)) :=
            setLIntegral_le_lintegral _ _
        _ = ∫⁻ v : ℝ, ENNReal.ofReal (6 * s * (|v| + b) ^ (-α)) :=
            lintegral_sub_right_eq_self
              (fun a : ℝ => ENNReal.ofReal (6 * s * (|a| + b) ^ (-α))) s
        _ = 2 * ∫⁻ v in Ioi 0, ENNReal.ofReal (6 * s * (v + b) ^ (-α)) :=
            lintegral_comp_abs fun w => ENNReal.ofReal (6 * s * (w + b) ^ (-α))
        _ = 2 * (ENNReal.ofReal (6 * s) * ∫⁻ v in Ioi 0, ENNReal.ofReal ((v + b) ^ (-α))) := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            exact congrArg _ (lintegral_congr fun v => ENNReal.ofReal_mul (by positivity))
        _ = ENNReal.ofReal (12 * s * (b ^ (1 - α) / (α - 1))) := by
            rw [lintegral_Ioi_add_rpow (p := -α) (c := 0) (m := b) (by linarith) (by linarith),
              show (-α + 1 : ℝ) = 1 - α from by ring, add_zero, neg_div_one_sub _,
              ← ENNReal.ofReal_mul (by positivity),
              show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
              ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            congr 1
            ring
    have hmain : (∫⁻ a in Ioc (0 : ℝ) (2 * s), ENNReal.ofReal (18 * s * (a + b) ^ (-α)))
        ≤ ENNReal.ofReal (18 * s * (b ^ (1 - α) / (α - 1))) := by
      calc ∫⁻ a in Ioc (0 : ℝ) (2 * s), ENNReal.ofReal (18 * s * (a + b) ^ (-α))
          ≤ ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (18 * s * (a + b) ^ (-α)) :=
            lintegral_mono_set Ioc_subset_Ioi_self
        _ = ENNReal.ofReal (18 * s) * ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal ((a + b) ^ (-α)) := by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            exact lintegral_congr fun v => ENNReal.ofReal_mul (by positivity)
        _ = ENNReal.ofReal (18 * s * (b ^ (1 - α) / (α - 1))) := by
            rw [lintegral_Ioi_add_rpow (p := -α) (c := 0) (m := b) (by linarith) (by linarith),
              show (-α + 1 : ℝ) = 1 - α from by ring, add_zero, neg_div_one_sub _,
              ← ENNReal.ofReal_mul (by positivity)]
    calc ∫⁻ a in Ioc 0 (2 * s), ENNReal.ofReal (|brk α a b s| * (a + b))
        ≤ ∫⁻ a in Ioc (0 : ℝ) (2 * s), (ENNReal.ofReal (18 * s * (a + b) ^ (-α))
            + ENNReal.ofReal (6 * s * (|a - s| + b) ^ (-α))) :=
          setLIntegral_mono' measurableSet_Ioc hpt
      _ = (∫⁻ a in Ioc (0 : ℝ) (2 * s), ENNReal.ofReal (18 * s * (a + b) ^ (-α)))
            + ∫⁻ a in Ioc (0 : ℝ) (2 * s), ENNReal.ofReal (6 * s * (|a - s| + b) ^ (-α)) :=
          lintegral_add_left hm1 _
      _ ≤ ENNReal.ofReal (18 * s * (b ^ (1 - α) / (α - 1)))
            + ENNReal.ofReal (12 * s * (b ^ (1 - α) / (α - 1))) := add_le_add hmain hcorner
      _ = ENNReal.ofReal (30 * s / (α - 1) * b ^ (1 - α)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring

/-! ### The outer integral in the second coordinate -/

/-- `x^p · x = x^{p+1}`. -/
private theorem rpow_succ_mul {x p : ℝ} (hx : 0 < x) : x ^ p * x = x ^ (p + 1) :=
  (Real.rpow_add_one hx.ne' p).symm

/-- Separating a power of the scale, linear case. -/
private theorem mul_rpow_scale {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) (q : ℝ) :
    s * (c * s) ^ q = c ^ q * s ^ (1 + q) := by
  rw [Real.mul_rpow hc hs.le, Real.rpow_add hs, Real.rpow_one]
  ring

/-- Separating a power of the scale, quadratic case. -/
private theorem sq_mul_rpow_scale {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) (q : ℝ) :
    s ^ 2 * (c * s) ^ q = c ^ q * s ^ (2 + q) := by
  rw [Real.mul_rpow hc hs.le, Real.rpow_add hs, Real.rpow_two]
  ring

/-- The three bounding profiles in the second coordinate. -/
private def bndFar (α s b : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (32 * (α + 1) * s ^ 2 * (b + 2 * s) ^ (-α))

private def bndTail (α s b : ℝ) : ℝ≥0∞ :=
  (Ioi (4 * s)).indicator (fun b => ENNReal.ofReal (8 * α * s ^ 2 * b ^ (-α))) b

private def bndCore (α s b : ℝ) : ℝ≥0∞ :=
  (Iic (4 * s)).indicator (fun b => ENNReal.ofReal (30 * s / (α - 1) * b ^ (1 - α))) b

/-- **The full inner integral in the first coordinate.** -/
private theorem lintegral_a_le {α b s : ℝ} (hα : 1 < α) (hα' : α < 2) (hb : 0 < b) (hs : 0 < s) :
    ∫⁻ a in Ioi 0, ENNReal.ofReal (|brk α a b s| * (a + b))
      ≤ bndFar α s b + bndTail α s b + bndCore α s b := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hfar : ∫⁻ a in Ioi (2 * s), ENNReal.ofReal (|brk α a b s| * (a + b)) ≤ bndFar α s b := by
    rw [bndFar, ← lintegral_a_far hα hb hs]
    refine setLIntegral_mono' measurableSet_Ioi fun a ha => ENNReal.ofReal_le_ofReal ?_
    have ha0 : (0 : ℝ) < a := lt_trans (by positivity) ha
    have hab : (0 : ℝ) < a + b := by linarith
    have hsq := abs_brk_le_sq (α := α) (a := a) (b := b) (s := s) hα0 hb.le hs.le ha0
      (le_of_lt ha)
    have h6 : (0 : ℝ) ≤ (a + b) ^ (-α - 2) := Real.rpow_nonneg hab.le _
    have hhalf : (a / 2 + b) ^ (-α - 2) ≤ 16 * (a + b) ^ (-α - 2) := by
      have hge : (1 / 2 : ℝ) * (a + b) ≤ a / 2 + b := by linarith
      have h1 : (a / 2 + b) ^ (-α - 2) ≤ ((1 / 2 : ℝ) * (a + b)) ^ (-α - 2) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hge (by linarith)
      have h2 : ((1 / 2 : ℝ) * (a + b)) ^ (-α - 2)
          = (1 / 2 : ℝ) ^ (-α - 2) * (a + b) ^ (-α - 2) :=
        Real.mul_rpow (by norm_num) hab.le
      have h3 : (1 / 2 : ℝ) ^ (-α - 2) ≤ 16 := by
        have h4 : (1 / 2 : ℝ) ^ (-α - 2) ≤ (1 / 2 : ℝ) ^ (-4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
        have h5 : (1 / 2 : ℝ) ^ (-4 : ℝ) = 16 := by
          rw [show (-4 : ℝ) = ((-4 : ℤ) : ℝ) from by norm_num, Real.rpow_intCast]
          norm_num
        linarith
      calc (a / 2 + b) ^ (-α - 2) ≤ (1 / 2 : ℝ) ^ (-α - 2) * (a + b) ^ (-α - 2) := by
            rw [← h2]; exact h1
        _ ≤ 16 * (a + b) ^ (-α - 2) := mul_le_mul_of_nonneg_right h3 h6
    have hkey : (a + b) ^ (-α - 2) * (a + b) = (a + b) ^ (-α - 1) := by
      rw [rpow_succ_mul hab, show (-α - 2 + 1 : ℝ) = -α - 1 from by ring]
    calc |brk α a b s| * (a + b)
        ≤ 2 * (α * (α + 1) * (a / 2 + b) ^ (-α - 2)) * s ^ 2 * (a + b) :=
          mul_le_mul_of_nonneg_right hsq hab.le
      _ ≤ 2 * (α * (α + 1) * (16 * (a + b) ^ (-α - 2))) * s ^ 2 * (a + b) := by
          have hc : (0 : ℝ) ≤ 2 * (α * (α + 1)) * (s ^ 2 * (a + b)) := by positivity
          nlinarith [hhalf]
      _ = 32 * α * (α + 1) * s ^ 2 * ((a + b) ^ (-α - 2) * (a + b)) := by ring
      _ = 32 * α * (α + 1) * s ^ 2 * (a + b) ^ (-α - 1) := by rw [hkey]
  rw [← Ioc_union_Ioi_eq_Ioi (by positivity : (0 : ℝ) ≤ 2 * s),
    lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same,
    show bndFar α s b + bndTail α s b + bndCore α s b
      = bndTail α s b + bndCore α s b + bndFar α s b from by ring]
  exact add_le_add (lintegral_a_near hα hα' hb hs) hfar

private theorem measurable_bndTail (α s : ℝ) : Measurable (bndTail α s) :=
  (ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))).indicator
    measurableSet_Ioi

private theorem measurable_bndFar (α s : ℝ) : Measurable (bndFar α s) :=
  ENNReal.measurable_ofReal.comp (measurable_const.mul ((measurable_id.add_const _).pow_const _))

private theorem lintegral_bndFar_le {α s : ℝ} (hα : 1 < α) (hs : 0 < s) :
    ∫⁻ b in Ioi 0, bndFar α s b
      ≤ ENNReal.ofReal (32 * (α + 1) / (α - 1) * s ^ (3 - α)) := by
  have hK : (0 : ℝ) ≤ 32 * (α + 1) * s ^ 2 := by positivity
  have hval : ∫⁻ b in Ioi 0, bndFar α s b
      = ENNReal.ofReal (32 * (α + 1) * s ^ 2 * ((2 * s) ^ (1 - α) / (α - 1))) := by
    calc ∫⁻ b in Ioi 0, bndFar α s b
        = ∫⁻ b in Ioi 0, ENNReal.ofReal (32 * (α + 1) * s ^ 2)
            * ENNReal.ofReal ((b + 2 * s) ^ (-α)) :=
          lintegral_congr fun b => by rw [bndFar, ENNReal.ofReal_mul hK]
      _ = ENNReal.ofReal (32 * (α + 1) * s ^ 2)
            * ∫⁻ b in Ioi 0, ENNReal.ofReal ((b + 2 * s) ^ (-α)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (32 * (α + 1) * s ^ 2 * ((2 * s) ^ (1 - α) / (α - 1))) := by
          rw [lintegral_Ioi_add_rpow (p := -α) (c := 0) (m := 2 * s) (by linarith) (by linarith),
            show (-α + 1 : ℝ) = 1 - α from by ring, add_zero, neg_div_one_sub _,
            ← ENNReal.ofReal_mul hK]
  rw [hval]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsep : s ^ 2 * (2 * s) ^ (1 - α) = 2 ^ (1 - α) * s ^ (3 - α) := by
    rw [sq_mul_rpow_scale hs (by norm_num) (1 - α),
      show (2 : ℝ) + (1 - α) = 3 - α from by ring]
  have h2 : (2 : ℝ) ^ (1 - α) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hsp : (0 : ℝ) ≤ s ^ (3 - α) := Real.rpow_nonneg hs.le _
  have hc : (0 : ℝ) ≤ 32 * (α + 1) / (α - 1) := by
    have : (0 : ℝ) < α - 1 := by linarith
    positivity
  calc 32 * (α + 1) * s ^ 2 * ((2 * s) ^ (1 - α) / (α - 1))
      = 32 * (α + 1) / (α - 1) * (2 ^ (1 - α) * s ^ (3 - α)) := by rw [← hsep]; ring
    _ ≤ 32 * (α + 1) / (α - 1) * (1 * s ^ (3 - α)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hsp) hc
    _ = 32 * (α + 1) / (α - 1) * s ^ (3 - α) := by ring

private theorem lintegral_bndTail_le {α s : ℝ} (hα : 1 < α) (hs : 0 < s) :
    ∫⁻ b in Ioi 0, bndTail α s b ≤ ENNReal.ofReal (8 * α / (α - 1) * s ^ (3 - α)) := by
  have hK : (0 : ℝ) ≤ 8 * α * s ^ 2 := by positivity
  have h0 : (∫⁻ b in Ioi 0, bndTail α s b)
      = ∫⁻ b in Ioi (4 * s), ENNReal.ofReal (8 * α * s ^ 2 * b ^ (-α)) := by
    simp only [bndTail]
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Ioi_inter_Ioi, sup_eq_left.2 (by positivity)]
  have hval : ∫⁻ b in Ioi 0, bndTail α s b
      = ENNReal.ofReal (8 * α * s ^ 2 * ((4 * s) ^ (1 - α) / (α - 1))) := by
    rw [h0]
    calc ∫⁻ b in Ioi (4 * s), ENNReal.ofReal (8 * α * s ^ 2 * b ^ (-α))
        = ∫⁻ b in Ioi (4 * s), ENNReal.ofReal (8 * α * s ^ 2) * ENNReal.ofReal (b ^ (-α)) :=
          lintegral_congr fun b => ENNReal.ofReal_mul hK
      _ = ENNReal.ofReal (8 * α * s ^ 2) * ∫⁻ b in Ioi (4 * s), ENNReal.ofReal (b ^ (-α)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (8 * α * s ^ 2 * ((4 * s) ^ (1 - α) / (α - 1))) := by
          rw [lintegral_Ioi_rpow (p := -α) (c := 4 * s) (by linarith) (by positivity),
            show (-α + 1 : ℝ) = 1 - α from by ring, neg_div_one_sub _, ← ENNReal.ofReal_mul hK]
  rw [hval]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsep : s ^ 2 * (4 * s) ^ (1 - α) = 4 ^ (1 - α) * s ^ (3 - α) := by
    rw [sq_mul_rpow_scale hs (by norm_num) (1 - α),
      show (2 : ℝ) + (1 - α) = 3 - α from by ring]
  have h4 : (4 : ℝ) ^ (1 - α) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hsp : (0 : ℝ) ≤ s ^ (3 - α) := Real.rpow_nonneg hs.le _
  have hc : (0 : ℝ) ≤ 8 * α / (α - 1) := by
    have : (0 : ℝ) < α - 1 := by linarith
    positivity
  calc 8 * α * s ^ 2 * ((4 * s) ^ (1 - α) / (α - 1))
      = 8 * α / (α - 1) * (4 ^ (1 - α) * s ^ (3 - α)) := by rw [← hsep]; ring
    _ ≤ 8 * α / (α - 1) * (1 * s ^ (3 - α)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hsp) hc
    _ = 8 * α / (α - 1) * s ^ (3 - α) := by ring

private theorem lintegral_bndCore_le {α s : ℝ} (hα : 1 < α) (hα' : α < 2) (hs : 0 < s) :
    ∫⁻ b in Ioi 0, bndCore α s b
      ≤ ENNReal.ofReal (120 / ((α - 1) * (2 - α)) * s ^ (3 - α)) := by
  have hα1 : (0 : ℝ) < α - 1 := by linarith
  have hα2 : (0 : ℝ) < 2 - α := by linarith
  have hK : (0 : ℝ) ≤ 30 * s / (α - 1) := by positivity
  have h0 : (∫⁻ b in Ioi 0, bndCore α s b)
      = ∫⁻ b in Ioc 0 (4 * s), ENNReal.ofReal (30 * s / (α - 1) * b ^ (1 - α)) := by
    simp only [bndCore]
    rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      inter_comm, Ioi_inter_Iic]
  have hval : ∫⁻ b in Ioi 0, bndCore α s b
      = ENNReal.ofReal (30 * s / (α - 1) * ((4 * s) ^ (2 - α) / (2 - α))) := by
    rw [h0]
    calc ∫⁻ b in Ioc 0 (4 * s), ENNReal.ofReal (30 * s / (α - 1) * b ^ (1 - α))
        = ∫⁻ b in Ioc 0 (4 * s),
            ENNReal.ofReal (30 * s / (α - 1)) * ENNReal.ofReal (b ^ (1 - α)) :=
          lintegral_congr fun b => ENNReal.ofReal_mul hK
      _ = ENNReal.ofReal (30 * s / (α - 1))
            * ∫⁻ b in Ioc 0 (4 * s), ENNReal.ofReal (b ^ (1 - α)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (30 * s / (α - 1) * ((4 * s) ^ (2 - α) / (2 - α))) := by
          rw [lintegral_Ioc_rpow (p := 1 - α) (c := 4 * s) (by linarith) (by positivity),
            show (1 - α + 1 : ℝ) = 2 - α from by ring, ← ENNReal.ofReal_mul hK]
  rw [hval]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsep : s * (4 * s) ^ (2 - α) = 4 ^ (2 - α) * s ^ (3 - α) := by
    rw [mul_rpow_scale hs (by norm_num) (2 - α), show (1 : ℝ) + (2 - α) = 3 - α from by ring]
  have h4 : (4 : ℝ) ^ (2 - α) ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (4 : ℝ)) (by norm_num)
      (show (2 : ℝ) - α ≤ 1 from by linarith)
    rwa [Real.rpow_one] at h
  have hsp : (0 : ℝ) ≤ s ^ (3 - α) := Real.rpow_nonneg hs.le _
  have hc : (0 : ℝ) ≤ 30 / ((α - 1) * (2 - α)) := by positivity
  calc 30 * s / (α - 1) * ((4 * s) ^ (2 - α) / (2 - α))
      = 30 / ((α - 1) * (2 - α)) * (4 ^ (2 - α) * s ^ (3 - α)) := by
        rw [← hsep]
        field_simp
    _ ≤ 30 / ((α - 1) * (2 - α)) * (4 * s ^ (3 - α)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hsp) hc
    _ = 120 / ((α - 1) * (2 - α)) * s ^ (3 - α) := by ring

/-! ### The two-dimensional estimate -/

/-- The constant of the two-dimensional estimate. -/
private def brkC (α : ℝ) : ℝ :=
  4 * (32 * (α + 1) / (α - 1) + 8 * α / (α - 1) + 120 / ((α - 1) * (2 - α)))

/-- **The two-dimensional estimate.** The plane integral of the second difference of the diamond
power at step `s`, weighted by the diamond radius, is `O(s^{3−α})`. -/
private theorem lintegral_abs_brk_mul_le {α : ℝ} (hα : 1 < α) (hα' : α < 2) {s : ℝ} (hs : 0 < s)
    (j : Fin 2) :
    ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (|brk α |z j| |z (j + 1)| s| * (|z j| + |z (j + 1)|))
      ≤ ENNReal.ofReal (brkC α * s ^ (3 - α)) := by
  have hα1 : (0 : ℝ) < α - 1 := by linarith
  have hα2 : (0 : ℝ) < 2 - α := by linarith
  have hsp : (0 : ℝ) ≤ s ^ (3 - α) := Real.rpow_nonneg hs.le _
  have hmeas : Measurable (Function.uncurry fun a b : ℝ =>
      ENNReal.ofReal (|brk α a b s| * (a + b))) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_abs.measurable.comp (measurable_brk α s)).mul
        (measurable_fst.add measurable_snd))
  have hinner : ∫⁻ b in Ioi 0, ∫⁻ a in Ioi 0, ENNReal.ofReal (|brk α a b s| * (a + b))
      ≤ (∫⁻ b in Ioi 0, bndFar α s b) + (∫⁻ b in Ioi 0, bndTail α s b)
        + ∫⁻ b in Ioi 0, bndCore α s b := by
    calc ∫⁻ b in Ioi 0, ∫⁻ a in Ioi 0, ENNReal.ofReal (|brk α a b s| * (a + b))
        ≤ ∫⁻ b in Ioi 0, (bndFar α s b + bndTail α s b + bndCore α s b) :=
          setLIntegral_mono' measurableSet_Ioi fun b hb => lintegral_a_le hα hα' hb hs
      _ = (∫⁻ b in Ioi 0, (bndFar α s b + bndTail α s b)) + ∫⁻ b in Ioi 0, bndCore α s b :=
          lintegral_add_left ((measurable_bndFar α s).add (measurable_bndTail α s)) _
      _ = (∫⁻ b in Ioi 0, bndFar α s b) + (∫⁻ b in Ioi 0, bndTail α s b)
            + ∫⁻ b in Ioi 0, bndCore α s b := by
          rw [lintegral_add_left (measurable_bndFar α s) _]
  rw [lintegral_abs_pair _ hmeas j, lintegral_Ioi_swap _ hmeas]
  calc (4 : ℝ≥0∞) * ∫⁻ b in Ioi 0, ∫⁻ a in Ioi 0, ENNReal.ofReal (|brk α a b s| * (a + b))
      ≤ 4 * ((∫⁻ b in Ioi 0, bndFar α s b) + (∫⁻ b in Ioi 0, bndTail α s b)
          + ∫⁻ b in Ioi 0, bndCore α s b) := by gcongr
    _ ≤ 4 * (ENNReal.ofReal (32 * (α + 1) / (α - 1) * s ^ (3 - α))
          + ENNReal.ofReal (8 * α / (α - 1) * s ^ (3 - α))
          + ENNReal.ofReal (120 / ((α - 1) * (2 - α)) * s ^ (3 - α))) := by
        gcongr
        · exact lintegral_bndFar_le hα hs
        · exact lintegral_bndTail_le hα hs
        · exact lintegral_bndCore_le hα hα' hs
    _ = ENNReal.ofReal (brkC α * s ^ (3 - α)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          show (4 : ℝ≥0∞) = ENNReal.ofReal 4 from by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), brkC]
        congr 1
        ring

/-! ### The truncated base near and across the truncation radius -/

/-- The Lipschitz constant of `x ↦ (x^{-α} − R^{-α})₊` on `[R/2, ∞)`. -/
private def lipC (α R : ℝ) : ℝ := α * (R / 2) ^ (-α - 1)

private theorem lipC_pos {α R : ℝ} (hα : 0 < α) (hR : 0 < R) : 0 < lipC α R := by
  rw [lipC]
  exact mul_pos hα (Real.rpow_pos_of_pos (by linarith) _)

/-- The mean value bound for `x ↦ x^{-α}` on `[c, ∞)`. -/
private theorem abs_rpow_sub_le {α c x y : ℝ} (hα : 0 < α) (hc : 0 < c) (hx : c ≤ x)
    (hy : c ≤ y) : |x ^ (-α) - y ^ (-α)| ≤ α * c ^ (-α - 1) * |x - y| := by
  have h := abs_rpow_shift_sub_le (α := α) (b := c) (x := x - c) (y := y - c) hα hc
    (by linarith) (by linarith)
  rwa [show x - c + c = x from by ring, show y - c + c = y from by ring,
    show x - c - (y - c) = x - y from by ring] at h

/-- **The truncated base is Lipschitz away from the origin.** -/
private theorem abs_truncBase_sub_le {α R : ℝ} (hα : 0 < α) (hR : 0 < R) {y w : Fin 2 → ℝ}
    (hy : R / 2 ≤ diamondNorm y) (hw : R / 2 ≤ diamondNorm w) :
    |truncBase α R y - truncBase α R w| ≤ lipC α R * |diamondNorm y - diamondNorm w| := by
  refine le_trans (abs_max_sub_max_le_abs _ _ _) ?_
  rw [show diamondNorm y ^ (-α) - R ^ (-α) - (diamondNorm w ^ (-α) - R ^ (-α))
      = diamondNorm y ^ (-α) - diamondNorm w ^ (-α) from by ring, lipC]
  exact abs_rpow_sub_le hα (by linarith) hy hw

/-- Inside the punctured closed diamond the base is the diamond power up to a constant. -/
private theorem truncBase_eq_sub {α R : ℝ} (hα : 0 < α) {y : Fin 2 → ℝ}
    (hy : 0 < diamondNorm y) (hyR : diamondNorm y ≤ R) :
    truncBase α R y = diamondPow α y - R ^ (-α) := by
  have h := Real.rpow_le_rpow_of_nonpos hy hyR (neg_nonpos.2 hα.le)
  rw [truncBase, diamondPow, max_eq_left (by linarith)]

/-- Outside the closed diamond the base vanishes. -/
private theorem truncBase_eq_zero_of_le {α R : ℝ} (hα : 0 < α) (hR : 0 < R) {y : Fin 2 → ℝ}
    (hy : R ≤ diamondNorm y) : truncBase α R y = 0 :=
  max_eq_right (by linarith [Real.rpow_le_rpow_of_nonpos hR hy (neg_nonpos.2 hα.le)])

private theorem abs_diamondNorm_add_single_sub (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    |diamondNorm (z + t • Pi.single j 1) - diamondNorm z| ≤ |t| := by
  rw [diamondNorm_add_single, diamondNorm_eq_abs_add z j,
    show |z j + t| + |z (j + 1)| - (|z j| + |z (j + 1)|) = |z j + t| - |z j| from by ring]
  simpa using abs_abs_sub_abs_le_abs_sub (z j + t) (z j)

private theorem sub_single_eq_add_single (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    z - t • Pi.single j 1 = z + (-t) • Pi.single j 1 := by
  rw [neg_smul, ← sub_eq_add_neg]

private theorem abs_diamondNorm_sub_single_sub (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    |diamondNorm (z - t • Pi.single j 1) - diamondNorm z| ≤ |t| := by
  rw [sub_single_eq_add_single]
  simpa using abs_diamondNorm_add_single_sub z j (-t)

private theorem diamondNorm_add_single_ge (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    |z (j + 1)| ≤ diamondNorm (z + t • Pi.single j 1) := by
  rw [diamondNorm_add_single]
  linarith [abs_nonneg (z j + t)]

private theorem diamondNorm_sub_single_ge (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    |z (j + 1)| ≤ diamondNorm (z - t • Pi.single j 1) := by
  rw [sub_single_eq_add_single]
  exact diamondNorm_add_single_ge z j (-t)

/-- **The pointwise majorant.** Off the coordinate line `z (j+1) = 0`, the weighted second
difference of the truncated base at a step smaller than `R/4` is bounded by the shell term and
the second difference of the diamond power. -/
private theorem enorm_secondDiff_truncBase_le {α R : ℝ} (hα : 0 < α) (hR : 0 < R) (j : Fin 2)
    {z : Fin 2 → ℝ} (hz : z (j + 1) ≠ 0) {t : ℝ} (ht : |t| < R / 4) :
    ENNReal.ofReal (|secondDiff (truncBase α R) j z t| * min 1 ‖z‖)
      ≤ {w : Fin 2 → ℝ | |diamondNorm w - R| ≤ |t|}.indicator
            (fun _ => ENNReal.ofReal (2 * lipC α R * |t|)) z
        + ENNReal.ofReal (|(brk α |z j| |z (j + 1)| |t|)| * (|z j| + |z (j + 1)|)) := by
  have hb : (0 : ℝ) < |z (j + 1)| := abs_pos.2 hz
  have ht0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  have hmin1 : min 1 ‖z‖ ≤ 1 := min_le_left _ _
  have hmin0 : (0 : ℝ) ≤ min 1 ‖z‖ := le_min zero_le_one (norm_nonneg _)
  have hmin2 : min 1 ‖z‖ ≤ |z j| + |z (j + 1)| := by
    rw [← diamondNorm_eq_abs_add z j]
    exact (min_le_right _ _).trans (norm_le_diamondNorm z)
  have hrz : diamondNorm z = |z j| + |z (j + 1)| := diamondNorm_eq_abs_add z j
  have hp := abs_diamondNorm_add_single_sub z j t
  have hm := abs_diamondNorm_sub_single_sub z j t
  rcases lt_or_ge (diamondNorm z) (R - |t|) with hcase | hcase
  · -- inside: the base is the diamond power up to a constant at all three points
    have hzR : diamondNorm z ≤ R := by linarith
    have hz0 : (0 : ℝ) < diamondNorm z := by rw [hrz]; linarith [abs_nonneg (z j)]
    have hpR : diamondNorm (z + t • Pi.single j 1) ≤ R := by
      have := abs_le.1 hp
      linarith [this.2]
    have hmR : diamondNorm (z - t • Pi.single j 1) ≤ R := by
      have := abs_le.1 hm
      linarith [this.2]
    have hp0 : (0 : ℝ) < diamondNorm (z + t • Pi.single j 1) :=
      lt_of_lt_of_le hb (diamondNorm_add_single_ge z j t)
    have hm0 : (0 : ℝ) < diamondNorm (z - t • Pi.single j 1) :=
      lt_of_lt_of_le hb (diamondNorm_sub_single_ge z j t)
    have hsd : secondDiff (truncBase α R) j z t = brk α |z j| |z (j + 1)| |t| := by
      rw [← secondDiff_diamondPow_eq α z j t, secondDiff, secondDiff,
        truncBase_eq_sub hα hp0 hpR, truncBase_eq_sub hα hm0 hmR, truncBase_eq_sub hα hz0 hzR]
      ring
    refine le_trans ?_ (le_add_self)
    rw [hsd]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hmin2 (abs_nonneg _))
  · rcases le_or_gt (diamondNorm z) (R + |t|) with hcase' | hcase'
    · -- the shell
      have hshell : |diamondNorm z - R| ≤ |t| := by
        rw [abs_le]; constructor <;> linarith
      have hzhalf : R / 2 ≤ diamondNorm z := by linarith
      have hphalf : R / 2 ≤ diamondNorm (z + t • Pi.single j 1) := by
        have := abs_le.1 hp
        linarith [this.1]
      have hmhalf : R / 2 ≤ diamondNorm (z - t • Pi.single j 1) := by
        have := abs_le.1 hm
        linarith [this.1]
      have h1 := abs_truncBase_sub_le hα hR hphalf hzhalf
      have h2 := abs_truncBase_sub_le hα hR hmhalf hzhalf
      have hL : (0 : ℝ) ≤ lipC α R := (lipC_pos hα hR).le
      have hbound : |secondDiff (truncBase α R) j z t| ≤ 2 * lipC α R * |t| := by
        have e1 : |truncBase α R (z + t • Pi.single j 1) - truncBase α R z| ≤ lipC α R * |t| :=
          h1.trans (mul_le_mul_of_nonneg_left hp hL)
        have e2 : |truncBase α R (z - t • Pi.single j 1) - truncBase α R z| ≤ lipC α R * |t| :=
          h2.trans (mul_le_mul_of_nonneg_left hm hL)
        have hsplit : secondDiff (truncBase α R) j z t
            = (truncBase α R (z + t • Pi.single j 1) - truncBase α R z)
              + (truncBase α R (z - t • Pi.single j 1) - truncBase α R z) := by
          rw [secondDiff]; ring
        calc |secondDiff (truncBase α R) j z t| ≤ _ := by rw [hsplit]; exact abs_add_le _ _
          _ ≤ lipC α R * |t| + lipC α R * |t| := add_le_add e1 e2
          _ = 2 * lipC α R * |t| := by ring
      have hmem : z ∈ {w : Fin 2 → ℝ | |diamondNorm w - R| ≤ |t|} := hshell
      rw [indicator_of_mem hmem]
      refine le_trans ?_ le_self_add
      refine ENNReal.ofReal_le_ofReal ?_
      calc |secondDiff (truncBase α R) j z t| * min 1 ‖z‖
          ≤ 2 * lipC α R * |t| * 1 :=
            mul_le_mul hbound hmin1 hmin0 (by positivity)
        _ = 2 * lipC α R * |t| := by ring
    · -- outside: all three points lie beyond the truncation radius
      have hpout : R ≤ diamondNorm (z + t • Pi.single j 1) := by
        have := abs_le.1 hp
        linarith [this.1]
      have hmout : R ≤ diamondNorm (z - t • Pi.single j 1) := by
        have := abs_le.1 hm
        linarith [this.1]
      have hsd : secondDiff (truncBase α R) j z t = 0 := by
        rw [secondDiff, truncBase_eq_zero_of_le hα hR hpout,
          truncBase_eq_zero_of_le hα hR hmout,
          truncBase_eq_zero_of_le hα hR (by linarith : R ≤ diamondNorm z)]
        ring
      rw [hsd]
      simp

/-! ### The volume of the shell and of a coordinate line -/

private theorem lintegral_Icc_id {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫⁻ t in Icc a b, ENNReal.ofReal t = ENNReal.ofReal ((b ^ 2 - a ^ 2) / 2) := by
  rw [← setLIntegral_congr (Ioc_ae_eq_Icc (a := a) (b := b))]
  have hint : IntegrableOn (fun t : ℝ => t) (Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 (continuous_id.intervalIntegrable a b)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc a b)] fun t : ℝ => t :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
      show (0 : ℝ) ≤ t
      linarith [ht.1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← intervalIntegral.integral_of_le hab,
    integral_id]

/-- **The shell `{ |r − R| ≤ s }` has area at most `8 R s`.** -/
private theorem volume_shell_le {R s : ℝ} (hs : 0 ≤ s) (hsR : s < R) :
    volume {z : Fin 2 → ℝ | |diamondNorm z - R| ≤ s} ≤ ENNReal.ofReal (8 * R * s) := by
  have hmI : MeasurableSet (Icc (R - s) (R + s)) := measurableSet_Icc
  have hSI : {z : Fin 2 → ℝ | |diamondNorm z - R| ≤ s}
      = diamondNorm ⁻¹' Icc (R - s) (R + s) := by
    ext z
    simp only [mem_setOf_eq, mem_preimage, mem_Icc, abs_le]
    constructor
    · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hmS : MeasurableSet {z : Fin 2 → ℝ | |diamondNorm z - R| ≤ s} := by
    rw [hSI]; exact measurable_diamondNorm hmI
  have hsub : Icc (R - s) (R + s) ⊆ Ioi (0 : ℝ) := fun x hx =>
    mem_Ioi.2 (lt_of_lt_of_le (by linarith) hx.1)
  calc volume {z : Fin 2 → ℝ | |diamondNorm z - R| ≤ s}
      = ∫⁻ _z in {z : Fin 2 → ℝ | |diamondNorm z - R| ≤ s}, (1 : ℝ≥0∞) :=
        (setLIntegral_one _).symm
    _ = ∫⁻ z, {z : Fin 2 → ℝ | |diamondNorm z - R| ≤ s}.indicator (fun _ => (1 : ℝ≥0∞)) z :=
        (lintegral_indicator hmS _).symm
    _ = ∫⁻ z : Fin 2 → ℝ,
          (Icc (R - s) (R + s)).indicator (fun _ => (1 : ℝ≥0∞)) (diamondNorm z) := by
        refine lintegral_congr fun z => ?_
        by_cases h : z ∈ {z : Fin 2 → ℝ | |diamondNorm z - R| ≤ s}
        · rw [indicator_of_mem h, indicator_of_mem (by rwa [hSI] at h)]
        · rw [indicator_of_notMem h, indicator_of_notMem (by rwa [hSI] at h)]
    _ = ∫⁻ t in Ioi 0,
          4 * ENNReal.ofReal t * (Icc (R - s) (R + s)).indicator (fun _ => (1 : ℝ≥0∞)) t :=
        lintegral_comp_diamondNorm (measurable_const.indicator hmI)
    _ = ∫⁻ t in Ioi 0, (Icc (R - s) (R + s)).indicator (fun t => 4 * ENNReal.ofReal t) t := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        by_cases h : t ∈ Icc (R - s) (R + s)
        · rw [indicator_of_mem h, indicator_of_mem h, mul_one]
        · rw [indicator_of_notMem h, indicator_of_notMem h, mul_zero]
    _ = ∫⁻ t in Icc (R - s) (R + s), 4 * ENNReal.ofReal t := by
        rw [lintegral_indicator hmI, Measure.restrict_restrict hmI, inter_eq_left.2 hsub]
    _ = 4 * ∫⁻ t in Icc (R - s) (R + s), ENNReal.ofReal t :=
        lintegral_const_mul' 4 _ (by simp)
    _ = 4 * ENNReal.ofReal (((R + s) ^ 2 - (R - s) ^ 2) / 2) := by
        rw [lintegral_Icc_id (by linarith) (by linarith)]
    _ = ENNReal.ofReal (8 * R * s) := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 from by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (8 * R * s) := le_rfl

/-- A coordinate line is null: it is a proper linear subspace of the plane. -/
private theorem volume_coord_eq_zero (i : Fin 2) : volume {z : Fin 2 → ℝ | z i = 0} = 0 := by
  have hker : {z : Fin 2 → ℝ | z i = 0}
      = (LinearMap.ker (LinearMap.proj i : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) : Set (Fin 2 → ℝ)) := by
    ext z
    simp [LinearMap.mem_ker]
  rw [hker]
  refine Measure.addHaar_submodule volume _ fun h => ?_
  have hmem : Pi.single i (1 : ℝ) ∈ LinearMap.ker (LinearMap.proj i : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) := by
    rw [h]; exact Submodule.mem_top
  simp [LinearMap.mem_ker] at hmem

/-! ### The dominating profile in the step -/

private def momProfile (α R M : ℝ) (u : ℝ) : ℝ≥0∞ :=
  if R / 4 ≤ u then ENNReal.ofReal (4 * M * u ^ (-(1 + α)))
  else ENNReal.ofReal (16 * R * lipC α R * u ^ (1 - α) + brkC α * u ^ (2 - 2 * α))

private def momBound (α R M : ℝ) (t : ℝ) : ℝ≥0∞ := momProfile α R M |t|

private theorem brkC_nonneg {α : ℝ} (hα : 1 < α) (hα' : α < 2) : 0 ≤ brkC α := by
  have h1 : (0 : ℝ) < α - 1 := by linarith
  have h2 : (0 : ℝ) < 2 - α := by linarith
  rw [brkC]
  positivity

private theorem lintegral_momBound_lt_top {α R M : ℝ} (hα : 1 < α) (hα' : α < 3 / 2) (hR : 0 < R)
    (hM : 0 ≤ M) : ∫⁻ t : ℝ, momBound α R M t < ⊤ := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hR4 : (0 : ℝ) < R / 4 := by linarith
  have hA : (0 : ℝ) ≤ 16 * R * lipC α R := by
    have hL := (lipC_pos hα0 hR).le
    positivity
  have hB : (0 : ℝ) ≤ brkC α := brkC_nonneg hα (by linarith)
  have hmA : Measurable fun u : ℝ => ENNReal.ofReal (16 * R * lipC α R * u ^ (1 - α)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_id.pow_const _))
  have hcore : ∫⁻ u in Ioc 0 (R / 4), momProfile α R M u
      ≤ ENNReal.ofReal (16 * R * lipC α R) * ENNReal.ofReal ((R / 4) ^ (2 - α) / (2 - α))
        + ENNReal.ofReal (brkC α) * ENNReal.ofReal ((R / 4) ^ (3 - 2 * α) / (3 - 2 * α)) := by
    have hcongr : ∫⁻ u in Ioc 0 (R / 4), momProfile α R M u
        = ∫⁻ u in Ioo 0 (R / 4), ENNReal.ofReal (16 * R * lipC α R * u ^ (1 - α)
            + brkC α * u ^ (2 - 2 * α)) := by
      rw [← setLIntegral_congr (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := R / 4))]
      refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      rw [momProfile, if_neg (by simpa using hu.2)]
    rw [hcongr]
    calc ∫⁻ u in Ioo 0 (R / 4), ENNReal.ofReal (16 * R * lipC α R * u ^ (1 - α)
            + brkC α * u ^ (2 - 2 * α))
        ≤ ∫⁻ u in Ioc 0 (R / 4), ENNReal.ofReal (16 * R * lipC α R * u ^ (1 - α)
            + brkC α * u ^ (2 - 2 * α)) := lintegral_mono_set Ioo_subset_Ioc_self
      _ = ∫⁻ u in Ioc 0 (R / 4), (ENNReal.ofReal (16 * R * lipC α R * u ^ (1 - α))
            + ENNReal.ofReal (brkC α * u ^ (2 - 2 * α))) := by
          refine setLIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
          have hu0 : (0 : ℝ) < u := hu.1
          exact ENNReal.ofReal_add (by positivity) (by positivity)
      _ = (∫⁻ u in Ioc 0 (R / 4), ENNReal.ofReal (16 * R * lipC α R * u ^ (1 - α)))
            + ∫⁻ u in Ioc 0 (R / 4), ENNReal.ofReal (brkC α * u ^ (2 - 2 * α)) :=
          lintegral_add_left hmA _
      _ = ENNReal.ofReal (16 * R * lipC α R) * ENNReal.ofReal ((R / 4) ^ (2 - α) / (2 - α))
            + ENNReal.ofReal (brkC α) * ENNReal.ofReal ((R / 4) ^ (3 - 2 * α) / (3 - 2 * α)) := by
          rw [show (∫⁻ u in Ioc 0 (R / 4), ENNReal.ofReal (16 * R * lipC α R * u ^ (1 - α)))
              = ENNReal.ofReal (16 * R * lipC α R)
                * ∫⁻ u in Ioc 0 (R / 4), ENNReal.ofReal (u ^ (1 - α)) from by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            exact setLIntegral_congr_fun measurableSet_Ioc
              fun u _ => ENNReal.ofReal_mul hA,
            show (∫⁻ u in Ioc 0 (R / 4), ENNReal.ofReal (brkC α * u ^ (2 - 2 * α)))
              = ENNReal.ofReal (brkC α)
                * ∫⁻ u in Ioc 0 (R / 4), ENNReal.ofReal (u ^ (2 - 2 * α)) from by
            rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            exact setLIntegral_congr_fun measurableSet_Ioc
              fun u _ => ENNReal.ofReal_mul hB,
            lintegral_Ioc_rpow (p := 1 - α) (c := R / 4) (by linarith) hR4.le,
            lintegral_Ioc_rpow (p := 2 - 2 * α) (c := R / 4) (by linarith) hR4.le,
            show (1 - α + 1 : ℝ) = 2 - α from by ring,
            show (2 - 2 * α + 1 : ℝ) = 3 - 2 * α from by ring]
  have htail : ∫⁻ u in Ioi (R / 4), momProfile α R M u
      = ENNReal.ofReal (4 * M) * ENNReal.ofReal (-(R / 4) ^ (-α) / (-α)) := by
    have hcongr : ∫⁻ u in Ioi (R / 4), momProfile α R M u
        = ∫⁻ u in Ioi (R / 4), ENNReal.ofReal (4 * M * u ^ (-(1 + α))) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      rw [momProfile, if_pos (le_of_lt hu)]
    rw [hcongr, show (∫⁻ u in Ioi (R / 4), ENNReal.ofReal (4 * M * u ^ (-(1 + α))))
        = ENNReal.ofReal (4 * M) * ∫⁻ u in Ioi (R / 4), ENNReal.ofReal (u ^ (-(1 + α))) from by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_congr_fun measurableSet_Ioi
        fun u _ => ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * M),
      lintegral_Ioi_rpow (p := -(1 + α)) (c := R / 4) (by linarith) hR4,
      show (-(1 + α) + 1 : ℝ) = -α from by ring]
  have hsplit : ∫⁻ u in Ioi 0, momProfile α R M u
      = (∫⁻ u in Ioc 0 (R / 4), momProfile α R M u) + ∫⁻ u in Ioi (R / 4), momProfile α R M u := by
    rw [← Ioc_union_Ioi_eq_Ioi hR4.le, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  have hfin : ∫⁻ u in Ioi 0, momProfile α R M u < ⊤ := by
    rw [hsplit, htail]
    refine lt_of_le_of_lt (add_le_add hcore le_rfl) ?_
    refine ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨?_, ?_⟩, ?_⟩ <;>
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hcomp : ∫⁻ t : ℝ, momBound α R M t = 2 * ∫⁻ u in Ioi 0, momProfile α R M u := by
    simp only [momBound]
    exact lintegral_comp_abs (momProfile α R M)
  rw [hcomp]
  exact ENNReal.mul_lt_top (by simp) hfin

/-! ### The moment hypothesis -/

private theorem measurableSet_shell (R s : ℝ) :
    MeasurableSet {z : Fin 2 → ℝ | |diamondNorm z - R| ≤ s} := by
  have hpre : {z : Fin 2 → ℝ | |diamondNorm z - R| ≤ s}
      = (fun z => |diamondNorm z - R|) ⁻¹' Iic s := by
    ext z; simp
  rw [hpre]
  exact (continuous_abs.comp (continuous_diamondNorm.sub continuous_const)).measurable
    measurableSet_Iic

private theorem enorm_secondDiff_mul (α : ℝ) (K : (Fin 2 → ℝ) → ℝ) (j : Fin 2)
    (z : Fin 2 → ℝ) (t : ℝ) :
    ‖secondDiff K j z t * min 1 ‖z‖ * |t| ^ (-(1 + α))‖ₑ
      = ENNReal.ofReal (|secondDiff K j z t| * min 1 ‖z‖ * |t| ^ (-(1 + α))) := by
  rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_mul,
    abs_of_nonneg (le_min zero_le_one (norm_nonneg z)),
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]

/-- **The inner integral at a fixed step.** -/
private theorem lintegral_z_le {α R : ℝ} (hα : 1 < α) (hα' : α < 2) (hR : 0 < R) (j : Fin 2)
    (t : ℝ) :
    ∫⁻ z : Fin 2 → ℝ,
        ENNReal.ofReal (|secondDiff (truncBase α R) j z t| * min 1 ‖z‖ * |t| ^ (-(1 + α)))
      ≤ momBound α R (∫ z, truncBase α R z) t := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hTint : Integrable (truncBase α R) := integrable_truncBase hα0 hα' hR
  have hMnn : 0 ≤ ∫ z, truncBase α R z := integral_nonneg (truncBase_nonneg α R)
  have hMl : ∫⁻ z, ENNReal.ofReal (truncBase α R z)
      = ENNReal.ofReal (∫ z, truncBase α R z) :=
    (ofReal_integral_eq_lintegral_ofReal hTint (ae_of_all _ (truncBase_nonneg α R))).symm
  have hw : (0 : ℝ) ≤ |t| ^ (-(1 + α)) := Real.rpow_nonneg (abs_nonneg t) _
  rw [momBound, momProfile]
  by_cases hcase : R / 4 ≤ |t|
  · rw [if_pos hcase]
    obtain ⟨a, ha⟩ : ∃ a : Fin 2 → ℝ, a = t • Pi.single j (1 : ℝ) := ⟨_, rfl⟩
    have hsd : ∀ z, secondDiff (truncBase α R) j z t
        = truncBase α R (z + a) + truncBase α R (z - a) - 2 * truncBase α R z := fun z => by
      rw [ha]; rfl
    have hm1 : Measurable fun z : Fin 2 → ℝ => ENNReal.ofReal (truncBase α R (z + a)) :=
      ENNReal.measurable_ofReal.comp ((measurable_truncBase α R).comp (measurable_id.add_const a))
    have hm2 : Measurable fun z : Fin 2 → ℝ => ENNReal.ofReal (truncBase α R (z - a)) :=
      ENNReal.measurable_ofReal.comp ((measurable_truncBase α R).comp (measurable_id.sub_const a))
    have hm12 : Measurable fun z : Fin 2 → ℝ =>
        ENNReal.ofReal (truncBase α R (z + a)) + ENNReal.ofReal (truncBase α R (z - a)) :=
      hm1.add hm2
    have hI1 : ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (truncBase α R (z + a))
        = ENNReal.ofReal (∫ z, truncBase α R z) := by
      rw [lintegral_add_right_eq_self (fun z => ENNReal.ofReal (truncBase α R z)) a, hMl]
    have hI2 : ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (truncBase α R (z - a))
        = ENNReal.ofReal (∫ z, truncBase α R z) := by
      rw [lintegral_sub_right_eq_self (fun z => ENNReal.ofReal (truncBase α R z)) a, hMl]
    have hI3 : ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (2 * truncBase α R z)
        = ENNReal.ofReal (2 * ∫ z, truncBase α R z) := by
      rw [show (fun z : Fin 2 → ℝ => ENNReal.ofReal (2 * truncBase α R z))
          = fun z : Fin 2 → ℝ => ENNReal.ofReal 2 * ENNReal.ofReal (truncBase α R z) from
        funext fun z => ENNReal.ofReal_mul (by norm_num),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hMl,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hpt : ∀ z : Fin 2 → ℝ,
        ENNReal.ofReal (|secondDiff (truncBase α R) j z t| * min 1 ‖z‖ * |t| ^ (-(1 + α)))
          ≤ ENNReal.ofReal (|t| ^ (-(1 + α)))
            * (ENNReal.ofReal (truncBase α R (z + a)) + ENNReal.ofReal (truncBase α R (z - a))
              + ENNReal.ofReal (2 * truncBase α R z)) := by
      intro z
      have h1 := truncBase_nonneg α R (z + a)
      have h2 := truncBase_nonneg α R (z - a)
      have h3 := truncBase_nonneg α R z
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hw]
      refine ENNReal.ofReal_le_ofReal ?_
      have habs : |secondDiff (truncBase α R) j z t|
          ≤ truncBase α R (z + a) + truncBase α R (z - a) + 2 * truncBase α R z := by
        rw [hsd z, abs_le]
        constructor <;> linarith
      calc |secondDiff (truncBase α R) j z t| * min 1 ‖z‖ * |t| ^ (-(1 + α))
          ≤ (truncBase α R (z + a) + truncBase α R (z - a) + 2 * truncBase α R z) * 1
              * |t| ^ (-(1 + α)) := by
            refine mul_le_mul_of_nonneg_right ?_ hw
            exact mul_le_mul habs (min_le_left _ _) (le_min zero_le_one (norm_nonneg _))
              (by linarith)
        _ = |t| ^ (-(1 + α))
              * (truncBase α R (z + a) + truncBase α R (z - a) + 2 * truncBase α R z) := by ring
    calc ∫⁻ z : Fin 2 → ℝ,
          ENNReal.ofReal (|secondDiff (truncBase α R) j z t| * min 1 ‖z‖ * |t| ^ (-(1 + α)))
        ≤ ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (|t| ^ (-(1 + α)))
            * (ENNReal.ofReal (truncBase α R (z + a)) + ENNReal.ofReal (truncBase α R (z - a))
              + ENNReal.ofReal (2 * truncBase α R z)) := lintegral_mono hpt
      _ = ENNReal.ofReal (|t| ^ (-(1 + α)))
            * ∫⁻ z : Fin 2 → ℝ, (ENNReal.ofReal (truncBase α R (z + a))
              + ENNReal.ofReal (truncBase α R (z - a)) + ENNReal.ofReal (2 * truncBase α R z)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (|t| ^ (-(1 + α))) * ENNReal.ofReal (4 * ∫ z, truncBase α R z) := by
          rw [lintegral_add_left hm12 _, lintegral_add_left hm1 _, hI1, hI2, hI3,
            ← ENNReal.ofReal_add hMnn hMnn,
            ← ENNReal.ofReal_add (by linarith) (by linarith),
            show (∫ z, truncBase α R z) + (∫ z, truncBase α R z)
                + 2 * ∫ z, truncBase α R z = 4 * ∫ z, truncBase α R z from by ring]
      _ = ENNReal.ofReal (4 * (∫ z, truncBase α R z) * |t| ^ (-(1 + α))) := by
          rw [← ENNReal.ofReal_mul hw]
          congr 1
          ring
  · rw [if_neg hcase]
    rw [not_le] at hcase
    by_cases ht0 : t = 0
    · have h0 : ∀ z : Fin 2 → ℝ,
          ENNReal.ofReal (|secondDiff (truncBase α R) j z t| * min 1 ‖z‖ * |t| ^ (-(1 + α)))
            = 0 := by
        intro z
        rw [ht0]
        simp
      rw [lintegral_congr h0, lintegral_zero]
      simp
    · have htpos : (0 : ℝ) < |t| := abs_pos.2 ht0
      have htR : |t| < R := by linarith
      have hL : (0 : ℝ) ≤ lipC α R := (lipC_pos hα0 hR).le
      have hBc : (0 : ℝ) ≤ brkC α := brkC_nonneg hα hα'
      have hmind : Measurable
          ({w : Fin 2 → ℝ | |diamondNorm w - R| ≤ |t|}.indicator
            fun _ => ENNReal.ofReal (2 * lipC α R * |t|)) :=
        measurable_const.indicator (measurableSet_shell R |t|)
      have haemem : ∀ᵐ z : Fin 2 → ℝ, z (j + 1) ≠ 0 := by
        rw [MeasureTheory.ae_iff]
        simpa using volume_coord_eq_zero (j + 1)
      have hae : ∀ᵐ z : Fin 2 → ℝ,
          ENNReal.ofReal (|secondDiff (truncBase α R) j z t| * min 1 ‖z‖ * |t| ^ (-(1 + α)))
            ≤ ENNReal.ofReal (|t| ^ (-(1 + α)))
              * ({w : Fin 2 → ℝ | |diamondNorm w - R| ≤ |t|}.indicator
                  (fun _ => ENNReal.ofReal (2 * lipC α R * |t|)) z
                + ENNReal.ofReal (|(brk α |z j| |z (j + 1)| |t|)|
                    * (|z j| + |z (j + 1)|))) := by
        filter_upwards [haemem] with z hzn
        have hkey := enorm_secondDiff_truncBase_le hα0 hR j hzn hcase
        rw [show |secondDiff (truncBase α R) j z t| * min 1 ‖z‖ * |t| ^ (-(1 + α))
            = |t| ^ (-(1 + α)) * (|secondDiff (truncBase α R) j z t| * min 1 ‖z‖) from by ring,
          ENNReal.ofReal_mul hw]
        gcongr
      have hshellI : ∫⁻ z : Fin 2 → ℝ,
          {w : Fin 2 → ℝ | |diamondNorm w - R| ≤ |t|}.indicator
            (fun _ => ENNReal.ofReal (2 * lipC α R * |t|)) z
          ≤ ENNReal.ofReal (2 * lipC α R * |t|) * ENNReal.ofReal (8 * R * |t|) := by
        rw [lintegral_indicator (measurableSet_shell R |t|), setLIntegral_const]
        exact mul_le_mul' le_rfl (volume_shell_le (abs_nonneg t) htR)
      have e1 : |t| ^ (-(1 + α)) * (2 * lipC α R * |t| * (8 * R * |t|))
          = 16 * R * lipC α R * |t| ^ (1 - α) := by
        have h : |t| ^ 2 * |t| ^ (-(1 + α)) = |t| ^ (1 - α) := by
          rw [← Real.rpow_two |t|, ← Real.rpow_add htpos,
            show (2 : ℝ) + -(1 + α) = 1 - α from by ring]
        calc |t| ^ (-(1 + α)) * (2 * lipC α R * |t| * (8 * R * |t|))
            = 16 * R * lipC α R * (|t| ^ 2 * |t| ^ (-(1 + α))) := by ring
          _ = 16 * R * lipC α R * |t| ^ (1 - α) := by rw [h]
      have e2 : |t| ^ (-(1 + α)) * (brkC α * |t| ^ (3 - α)) = brkC α * |t| ^ (2 - 2 * α) := by
        have h : |t| ^ (3 - α) * |t| ^ (-(1 + α)) = |t| ^ (2 - 2 * α) := by
          rw [← Real.rpow_add htpos, show (3 - α) + -(1 + α) = 2 - 2 * α from by ring]
        calc |t| ^ (-(1 + α)) * (brkC α * |t| ^ (3 - α))
            = brkC α * (|t| ^ (3 - α) * |t| ^ (-(1 + α))) := by ring
          _ = brkC α * |t| ^ (2 - 2 * α) := by rw [h]
      calc ∫⁻ z : Fin 2 → ℝ,
            ENNReal.ofReal (|secondDiff (truncBase α R) j z t| * min 1 ‖z‖ * |t| ^ (-(1 + α)))
          ≤ ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (|t| ^ (-(1 + α)))
              * ({w : Fin 2 → ℝ | |diamondNorm w - R| ≤ |t|}.indicator
                  (fun _ => ENNReal.ofReal (2 * lipC α R * |t|)) z
                + ENNReal.ofReal (|(brk α |z j| |z (j + 1)| |t|)|
                    * (|z j| + |z (j + 1)|))) := lintegral_mono_ae hae
        _ = ENNReal.ofReal (|t| ^ (-(1 + α)))
              * ∫⁻ z : Fin 2 → ℝ,
                ({w : Fin 2 → ℝ | |diamondNorm w - R| ≤ |t|}.indicator
                    (fun _ => ENNReal.ofReal (2 * lipC α R * |t|)) z
                  + ENNReal.ofReal (|(brk α |z j| |z (j + 1)| |t|)|
                      * (|z j| + |z (j + 1)|))) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal (|t| ^ (-(1 + α)))
              * ((∫⁻ z : Fin 2 → ℝ, {w : Fin 2 → ℝ | |diamondNorm w - R| ≤ |t|}.indicator
                    (fun _ => ENNReal.ofReal (2 * lipC α R * |t|)) z)
                + ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (|(brk α |z j| |z (j + 1)| |t|)|
                    * (|z j| + |z (j + 1)|))) := by
            rw [lintegral_add_left hmind _]
        _ ≤ ENNReal.ofReal (|t| ^ (-(1 + α)))
              * (ENNReal.ofReal (2 * lipC α R * |t|) * ENNReal.ofReal (8 * R * |t|)
                + ENNReal.ofReal (brkC α * |t| ^ (3 - α))) := by
            gcongr
            exact lintegral_abs_brk_mul_le hα hα' htpos j
        _ = ENNReal.ofReal (16 * R * lipC α R * |t| ^ (1 - α)
              + brkC α * |t| ^ (2 - 2 * α)) := by
            rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * lipC α R * |t|), mul_add,
              ← ENNReal.ofReal_mul hw, ← ENNReal.ofReal_mul hw,
              ← ENNReal.ofReal_add (by rw [e1]; positivity) (by rw [e2]; positivity), e1, e2]

/-- **The moment hypothesis for the truncated diamond base.** The two-sided restriction
`1 < α < 3/2` is sharp: the `t`-integral of the homogeneous piece converges at infinity only for
`α > 1` and at the origin only for `α < 3/2`. -/
theorem jumpMoment_truncBase_of_lt {α R : ℝ} (hα : 1 < α) (hα' : α < 3 / 2) (hR : 0 < R) :
    JumpMoment α (truncBase α R) := by
  intro j
  have hm : Measurable fun p : ℝ × (Fin 2 → ℝ) =>
      secondDiff (truncBase α R) j p.2 p.1 * min 1 ‖p.2‖ * |p.1| ^ (-(1 + α)) :=
    ((measurable_secondDiff_snd (measurable_truncBase α R) j).mul
      (measurable_const.min (measurable_norm.comp measurable_snd))).mul
      ((continuous_abs.measurable.pow_const _).comp measurable_fst)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc (∫⁻ p, ‖Function.uncurry (fun (t : ℝ) (z : Fin 2 → ℝ) =>
          secondDiff (truncBase α R) j z t * min 1 ‖z‖ * |t| ^ (-(1 + α))) p‖ₑ
        ∂((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))))
      = ∫⁻ t : ℝ, ∫⁻ z, ‖secondDiff (truncBase α R) j z t * min 1 ‖z‖ * |t| ^ (-(1 + α))‖ₑ :=
        lintegral_prod _ hm.enorm.aemeasurable
    _ = ∫⁻ t : ℝ, ∫⁻ z : Fin 2 → ℝ,
          ENNReal.ofReal (|secondDiff (truncBase α R) j z t| * min 1 ‖z‖
            * |t| ^ (-(1 + α))) :=
        lintegral_congr fun t =>
          lintegral_congr fun z => enorm_secondDiff_mul α (truncBase α R) j z t
    _ ≤ ∫⁻ t : ℝ, momBound α R (∫ z, truncBase α R z) t :=
        lintegral_mono fun t => lintegral_z_le hα (by linarith) hR j t
    _ < ⊤ :=
        lintegral_momBound_lt_top hα hα' hR (integral_nonneg (truncBase_nonneg α R))

/-- **The moment hypothesis for the `α = 6/5`, `R = 7/4` truncated diamond base**, the one
hypothesis `CenteredMaximal.Fractional.jumpMoment_fracKernel` leaves open. -/
theorem jumpMoment_truncBase : JumpMoment (6 / 5) (truncBase (6 / 5) (7 / 4)) :=
  jumpMoment_truncBase_of_lt (by norm_num) (by norm_num) (by norm_num)

/-- **The moment hypothesis for the comparison kernel**, unconditionally. -/
theorem jumpMoment_fracKernel' : JumpMoment (6 / 5) fracKernel :=
  jumpMoment_fracKernel jumpMoment_truncBase

/-- **The merged generator representation of the comparison kernel**, unconditionally. -/
theorem hKgen_fracKernel' {ψ : (Fin 2 → ℝ) → ℝ} (hψ : IsTestFunction ψ) :
    (∫ x, fracKernel x * jumpGen (6 / 5) ψ x) = ∫ y, fracDensity y * (ψ y - ψ 0) :=
  hKgen_fracKernel jumpMoment_fracKernel' hψ

/-- **The Lévy moment of the comparison density**, unconditionally. -/
theorem integrable_fracDensity_mul_min_one' :
    Integrable fun z => fracDensity z * min 1 ‖z‖ :=
  integrable_fracDensity_mul_min_one jumpMoment_fracKernel'

end CenteredMaximal.Fractional

end

end
