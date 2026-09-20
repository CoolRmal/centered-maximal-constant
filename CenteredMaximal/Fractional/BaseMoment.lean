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
`truncBase (6/5) (7/4)`. This file discharges it.

## Main results

* `jumpMoment_truncBase_of_lt`: `JumpMoment α (truncBase α R)` for `1 < α < 3/2` and `0 < R`;
* `jumpMoment_truncBase`: the `α = 6/5`, `R = 7/4` instance;
* `jumpMoment_fracKernel'`, `hKgen_fracKernel'`, `integrable_fracDensity_mul_min_one'`: the
  hypothesis-free forms of the three consequences isolated by `FracRepresentation`.
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

/-- Translating the half-line: `∫₀^∞ g(m + v) dv = ∫_m^∞ g(t) dt`. -/
private theorem lintegral_Ioi_comp_add (g : ℝ → ℝ≥0∞) (m : ℝ) :
    ∫⁻ v in Ioi 0, g (m + v) = ∫⁻ t in Ioi m, g t := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_add_left_eq_self (fun t => (Ioi m).indicator g t) m]
  refine lintegral_congr fun v => ?_
  simp [indicator_apply]

/-- `∫₀^∞ (v + m)^p dv = −m^{p+1}/(p+1)` for `p < −1` and `0 < m`. -/
private theorem lintegral_Ioi_zero_add_rpow {p m : ℝ} (hp : p < -1) (hm : 0 < m) :
    ∫⁻ v in Ioi 0, ENNReal.ofReal ((v + m) ^ p) = ENNReal.ofReal (-m ^ (p + 1) / (p + 1)) := by
  calc ∫⁻ v in Ioi 0, ENNReal.ofReal ((v + m) ^ p)
      = ∫⁻ t in Ioi m, ENNReal.ofReal (t ^ p) := by
        rw [← lintegral_Ioi_comp_add (fun t : ℝ => ENNReal.ofReal (t ^ p)) m]
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

end CenteredMaximal.Fractional

end

end
