/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Comparison.Reduction
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# From a pointwise bound at every scale to the kernel weak type bound

The weak type `(1, 1)` bound for the kernel maximal operator
`M_K f (x) = sup_{s > 0} ∫ K_s(x - y) |f(y)| dy` is derived here from a bound at each scale
separately, which is what a covering argument produces: for every bounded, nonnegative, compactly
supported measurable `f` and every level `λ > 0` there is an exceptional set `Ω` of measure at most
`M ∫ f / λ`, where `M = ∫ K`, such that for each scale `s > 0` the dilation average
`∫ K_s(x - y) f(y) dy` is at most `λ` for almost every `x ∉ Ω`.

The null set is allowed to depend on the scale, so passing to the supremum over all scales is the
content of this file: the supremum is reduced to the countably many rational scales, using that the
dilation average of a bounded function varies continuously with the scale.

* `lintegral_comp_smul`, `lintegral_enorm_dilate`: the change of variables `z ↦ r • z` in a
  Lebesgue integral on the plane, and the `L¹` invariance `‖K_s‖₁ = ‖K‖₁` of dilation;
* `tendsto_lintegral_enorm_dilate_sub`: **`L¹` continuity of dilation**, `‖K_r − K_s‖₁ → 0` as
  `r → s⁺`; for a continuous kernel with compact support this is dominated convergence, and a
  general integrable kernel is approximated in `L¹` by such kernels;
* `kernelMaximal_eq_iSup_rat`: for a bounded `f` the supremum over all positive scales is already
  attained along the positive rationals, because the two averages at scales `r` and `s` differ by
  at most `Mf ‖K_r − K_s‖₁`, uniformly in `x`;
* `mul_volume_le_of_bounded`: the weak type inequality at one level for one bounded nonnegative
  measurable `f`, discarding the countably many exceptional null sets at once;
* `isKernelWeakTypeBound_of_pointwise`: the main transfer, extended to every integrable `f` and
  every level `α ∈ [0, ∞]` through the truncations `trunc |f| n`, which increase to `|f|`.

The file is interface driven: it takes the per-scale bound as a hypothesis and produces
`IsKernelWeakTypeBound K (ENNReal.ofReal (∫ x, K x))`, independently of how that bound is obtained.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace CenteredMaximal

variable {K L : (Fin 2 → ℝ) → ℝ}

/-! ### Scaling -/

/-- Scaling the variable in a Lebesgue integral on the plane by `r ≠ 0` multiplies it by
`(r²)⁻¹`. -/
theorem lintegral_comp_smul (g : (Fin 2 → ℝ) → ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    ∫⁻ z, g (r • z) = ENNReal.ofReal ((r ^ 2)⁻¹) * ∫⁻ z, g z := by
  have he : ∫⁻ z, g (r • z) = ∫⁻ z, g z ∂(Measure.map (fun z : Fin 2 → ℝ => r • z) volume) :=
    (lintegral_map_equiv g
      (Homeomorph.smul (isUnit_iff_ne_zero.2 hr.ne').unit).toMeasurableEquiv).symm
  rw [he, Measure.map_addHaar_smul volume hr.ne', lintegral_smul_measure]
  congr 2
  rw [Module.finrank_fin_fun, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r ^ 2)⁻¹)]

/-- The dilation of a difference is the difference of the dilations. -/
theorem dilate_sub (K L : (Fin 2 → ℝ) → ℝ) (s : ℝ) (x : Fin 2 → ℝ) :
    dilate K s x - dilate L s x = dilate (fun z => K z - L z) s x := by
  simp [dilate, mul_sub]

/-- Dilation preserves the `L¹` norm: `‖K_s‖₁ = ‖K‖₁`. -/
theorem lintegral_enorm_dilate (L : (Fin 2 → ℝ) → ℝ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ z, ‖dilate L s z‖ₑ = ∫⁻ z, ‖L z‖ₑ := by
  have h : ∀ z, ‖dilate L s z‖ₑ = ENNReal.ofReal ((s ^ 2)⁻¹) * ‖L (s⁻¹ • z)‖ₑ := fun z => by
    rw [dilate, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (s ^ 2)⁻¹),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (s ^ 2)⁻¹)]
  rw [lintegral_congr h, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_comp_smul (fun z => ‖L z‖ₑ) (inv_pos.2 hs), ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (s ^ 2)⁻¹)]
  rw [inv_pow, inv_inv, inv_mul_cancel₀ (by positivity : (s : ℝ) ^ 2 ≠ 0), ENNReal.ofReal_one,
    one_mul]

/-- The `L¹` distance between two kernels is invariant under simultaneous dilation. -/
theorem lintegral_enorm_dilate_sub_dilate (K L : (Fin 2 → ℝ) → ℝ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ z, ‖dilate K s z - dilate L s z‖ₑ = ∫⁻ z, ‖K z - L z‖ₑ := by
  simp only [dilate_sub]
  exact lintegral_enorm_dilate _ hs

/-- A dilation of an integrable kernel is integrable. -/
theorem integrable_dilate (hK : Integrable K) {s : ℝ} (hs : 0 < s) : Integrable (dilate K s) :=
  (hK.comp_smul (inv_ne_zero hs.ne')).const_mul _

/-- The reflected translate of a dilation of an integrable kernel is integrable. -/
theorem integrable_dilate_sub (hK : Integrable K) {s : ℝ} (hs : 0 < s) (x : Fin 2 → ℝ) :
    Integrable fun y => dilate K s (x - y) :=
  (integrable_dilate hK hs).comp_sub_left x

/-! ### `L¹` continuity of the dilation family -/

/-- For a continuous kernel with compact support the dilations converge in `L¹`:
`‖g_r − g_s‖₁ → 0` as `r → s⁺`. The dilations are all supported in a fixed cube and uniformly
bounded for `r` between `s` and `2s`, so this is dominated convergence. -/
private theorem tendsto_lintegral_enorm_dilate_sub_of_continuous {g : (Fin 2 → ℝ) → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun r : ℝ => ∫⁻ z, ‖dilate g r z - dilate g s z‖ₑ) (𝓝[>] s) (𝓝 0) := by
  have hgcpt : IsCompact (tsupport g) := hgc
  obtain ⟨A₀, hA₀⟩ := hgcpt.isBounded.subset_closedBall (0 : Fin 2 → ℝ)
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  set A : ℝ := max A₀ 0
  have hA0 : 0 ≤ A := le_max_right _ _
  have hA : tsupport g ⊆ closedBall 0 A :=
    hA₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  -- the dilations vanish far from the origin
  have hdil : ∀ {t : ℝ}, 0 < t → ∀ z : Fin 2 → ℝ, t * A < ‖z‖ → dilate g t z = 0 := by
    intro t ht z hz
    have hw : A < ‖t⁻¹ • z‖ := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg ht.le, ← div_eq_inv_mul, lt_div_iff₀ ht,
        mul_comm]
      exact hz
    have : g (t⁻¹ • z) = 0 := by
      by_contra hne
      exact absurd (mem_closedBall_zero_iff.1 (hA (subset_closure (Function.mem_support.2 hne))))
        (not_le.2 hw)
    rw [dilate, this, mul_zero]
  -- and they are uniformly bounded for `t ≥ s`
  have hbdd : ∀ {t : ℝ}, s ≤ t → ∀ z : Fin 2 → ℝ, |dilate g t z| ≤ C * (s ^ 2)⁻¹ := by
    intro t hst z
    have ht : 0 < t := hs.trans_le hst
    have h1 : |g (t⁻¹ • z)| ≤ C := by simpa [Real.norm_eq_abs] using hC (t⁻¹ • z)
    have h2 : (t ^ 2)⁻¹ ≤ (s ^ 2)⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      nlinarith
    rw [dilate, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t ^ 2)⁻¹)]
    nlinarith [abs_nonneg (g (t⁻¹ • z)), inv_pos.2 (by positivity : (0 : ℝ) < t ^ 2)]
  have hcont : ∀ t : ℝ, Continuous (dilate g t) := fun t => by
    unfold dilate
    exact (hg.comp (continuous_const_smul t⁻¹)).const_mul _
  set bound : (Fin 2 → ℝ) → ℝ≥0∞ :=
    (closedBall (0 : Fin 2 → ℝ) (2 * s * A)).indicator
      fun _ => ENNReal.ofReal (2 * C * (s ^ 2)⁻¹) with hbound
  have key := tendsto_lintegral_filter_of_dominated_convergence' (μ := volume)
    (F := fun (r : ℝ) (z : Fin 2 → ℝ) => ‖dilate g r z - dilate g s z‖ₑ)
    (f := fun _ => (0 : ℝ≥0∞)) (l := 𝓝[>] s) bound
    (Eventually.of_forall fun r => (((hcont r).sub (hcont s)).enorm.measurable).aemeasurable)
    (eventually_of_mem (Ioo_mem_nhdsGT (by linarith : s < 2 * s)) fun r hr =>
      Eventually.of_forall fun z => ?_) ?_ (Eventually.of_forall fun z => ?_)
  · simpa using key
  · -- the pointwise domination
    by_cases hzB : z ∈ closedBall (0 : Fin 2 → ℝ) (2 * s * A)
    · rw [hbound, Set.indicator_of_mem hzB, Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := hbdd hr.1.le z
      have h2 := hbdd (le_refl s) z
      calc |dilate g r z - dilate g s z| ≤ |dilate g r z| + |dilate g s z| := abs_sub _ _
        _ ≤ 2 * C * (s ^ 2)⁻¹ := by linarith
    · have hz : 2 * s * A < ‖z‖ := by
        simpa [mem_closedBall_zero_iff, not_le] using hzB
      have e1 : dilate g r z = 0 := hdil (hs.trans hr.1) z (by nlinarith [hr.2])
      have e2 : dilate g s z = 0 := hdil hs z (by nlinarith)
      rw [e1, e2, sub_self, enorm_zero]
      exact zero_le
  · -- the dominating function is integrable
    rw [hbound, lintegral_indicator_const measurableSet_closedBall]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  · -- the pointwise convergence
    have h1 : ContinuousAt (fun r : ℝ => (r ^ 2)⁻¹) s :=
      (continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 hs.ne')
    have h2 : ContinuousAt (fun r : ℝ => g (r⁻¹ • z)) s :=
      hg.continuousAt.comp ((continuousAt_inv₀ hs.ne').smul continuousAt_const)
    have h3 : Tendsto (fun r : ℝ => dilate g r z - dilate g s z) (𝓝 s) (𝓝 0) := by
      have h : Tendsto (fun r : ℝ => (r ^ 2)⁻¹ * g (r⁻¹ • z) - dilate g s z) (𝓝 s)
          (𝓝 ((s ^ 2)⁻¹ * g (s⁻¹ • z) - dilate g s z)) := (h1.mul h2).sub continuousAt_const
      rw [show ((s : ℝ) ^ 2)⁻¹ * g (s⁻¹ • z) - dilate g s z = 0 from sub_self _] at h
      exact h
    have h4 : Tendsto (fun r : ℝ => ‖dilate g r z - dilate g s z‖ₑ) (𝓝 s) (𝓝 0) := by
      simpa [Function.comp_def] using (continuous_enorm.tendsto (0 : ℝ)).comp h3
    exact h4.mono_left nhdsWithin_le_nhds

/-- The triangle inequality for the `L¹` distance, in `ℝ≥0∞` form. -/
private theorem lintegral_enorm_sub_le_add {a b c : (Fin 2 → ℝ) → ℝ}
    (hab : AEMeasurable (fun z => a z - b z) volume) :
    ∫⁻ z, ‖a z - c z‖ₑ ≤ (∫⁻ z, ‖a z - b z‖ₑ) + ∫⁻ z, ‖b z - c z‖ₑ := by
  rw [← lintegral_add_left' hab.enorm]
  refine lintegral_mono fun z => ?_
  calc ‖a z - c z‖ₑ = ‖(a z - b z) + (b z - c z)‖ₑ := by rw [sub_add_sub_cancel]
    _ ≤ ‖a z - b z‖ₑ + ‖b z - c z‖ₑ := enorm_add_le _ _

/-- **`L¹` continuity of dilation.** For an integrable kernel the `L¹` distance `‖K_r − K_s‖₁`
tends to `0` as `r` decreases to `s`. A continuous kernel with compact support is handled by
dominated convergence, and a general integrable kernel is approximated by one in `L¹`, using that
dilation is an `L¹` isometry. -/
theorem tendsto_lintegral_enorm_dilate_sub (hK : Integrable K) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun r : ℝ => ∫⁻ z, ‖dilate K r z - dilate K s z‖ₑ) (𝓝[>] s) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := by simp [hε.ne']
  obtain ⟨g, hgc, hgK, hgcont, hgint⟩ := hK.exists_hasCompactSupport_lintegral_sub_le hε3
  have hthird : ε / 3 + (ε / 3 + ε / 3) = ε := by
    rw [show ε / 3 + (ε / 3 + ε / 3) = 3 * (ε / 3) by ring,
      ENNReal.mul_div_cancel (by simp) (by simp)]
  have hgK' : ∫⁻ z, ‖g z - K z‖ₑ ≤ ε / 3 := by
    refine le_of_eq_of_le (lintegral_congr fun z => ?_) hgK
    rw [← enorm_neg, neg_sub]
  filter_upwards [ENNReal.tendsto_nhds_zero.1
      (tendsto_lintegral_enorm_dilate_sub_of_continuous hgcont hgc hs) (ε / 3)
      (by simpa using hε3.bot_lt), self_mem_nhdsWithin] with r hr hrs
  have hr0 : 0 < r := hs.trans hrs
  have hm : ∀ {t : ℝ}, 0 < t → AEMeasurable (fun z => dilate K t z - dilate g t z) volume :=
    fun ht => ((integrable_dilate hK ht).sub (integrable_dilate hgint ht)).1.aemeasurable
  calc ∫⁻ z, ‖dilate K r z - dilate K s z‖ₑ
      ≤ (∫⁻ z, ‖dilate K r z - dilate g r z‖ₑ) + ∫⁻ z, ‖dilate g r z - dilate K s z‖ₑ :=
        lintegral_enorm_sub_le_add (hm hr0)
    _ ≤ (∫⁻ z, ‖dilate K r z - dilate g r z‖ₑ)
          + ((∫⁻ z, ‖dilate g r z - dilate g s z‖ₑ) + ∫⁻ z, ‖dilate g s z - dilate K s z‖ₑ) := by
        gcongr
        exact lintegral_enorm_sub_le_add
          ((integrable_dilate hgint hr0).sub (integrable_dilate hgint hs)).1.aemeasurable
    _ ≤ ε / 3 + (ε / 3 + ε / 3) := by
        rw [lintegral_enorm_dilate_sub_dilate _ _ hr0, lintegral_enorm_dilate_sub_dilate _ _ hs]
        gcongr
    _ = ε := hthird

/-! ### The supremum over rational scales -/

/-- Changing the scale changes the dilation average of a bounded function by at most `Mf` times
the `L¹` distance between the two dilations. -/
private theorem lintegral_dilate_le_add (hK : Integrable K) {f : (Fin 2 → ℝ) → ℝ} {Mf : ℝ}
    (hfm : AEMeasurable f volume) (hfb : ∀ y, ‖f y‖ ≤ Mf) {r s : ℝ} (hr : 0 < r)
    (x : Fin 2 → ℝ) :
    (∫⁻ y, ENNReal.ofReal (dilate K s (x - y)) * ‖f y‖ₑ) ≤
      (∫⁻ y, ENNReal.ofReal (dilate K r (x - y)) * ‖f y‖ₑ) +
        ENNReal.ofReal Mf * ∫⁻ z, ‖dilate K r z - dilate K s z‖ₑ := by
  have hfe : ∀ y, ‖f y‖ₑ ≤ ENNReal.ofReal Mf := fun y => by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hfb y)
  have hstep : ∀ y, ENNReal.ofReal (dilate K s (x - y)) * ‖f y‖ₑ ≤
      ENNReal.ofReal (dilate K r (x - y)) * ‖f y‖ₑ
        + ‖dilate K r (x - y) - dilate K s (x - y)‖ₑ * ENNReal.ofReal Mf := fun y => by
    have h1 : ENNReal.ofReal (dilate K s (x - y)) ≤ ENNReal.ofReal (dilate K r (x - y))
        + ‖dilate K r (x - y) - dilate K s (x - y)‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs]
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
      have := neg_abs_le (dilate K r (x - y) - dilate K s (x - y))
      linarith
    calc ENNReal.ofReal (dilate K s (x - y)) * ‖f y‖ₑ
        ≤ (ENNReal.ofReal (dilate K r (x - y))
            + ‖dilate K r (x - y) - dilate K s (x - y)‖ₑ) * ‖f y‖ₑ := by gcongr
      _ = ENNReal.ofReal (dilate K r (x - y)) * ‖f y‖ₑ
            + ‖dilate K r (x - y) - dilate K s (x - y)‖ₑ * ‖f y‖ₑ := add_mul _ _ _
      _ ≤ _ := by gcongr; exact hfe y
  have hmeas : AEMeasurable (fun y => ENNReal.ofReal (dilate K r (x - y)) * ‖f y‖ₑ) volume :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (integrable_dilate_sub hK hr x).1.aemeasurable).mul hfm.enorm
  calc ∫⁻ y, ENNReal.ofReal (dilate K s (x - y)) * ‖f y‖ₑ
      ≤ ∫⁻ y, (ENNReal.ofReal (dilate K r (x - y)) * ‖f y‖ₑ
          + ‖dilate K r (x - y) - dilate K s (x - y)‖ₑ * ENNReal.ofReal Mf) :=
        lintegral_mono hstep
    _ = (∫⁻ y, ENNReal.ofReal (dilate K r (x - y)) * ‖f y‖ₑ)
          + ∫⁻ y, ‖dilate K r (x - y) - dilate K s (x - y)‖ₑ * ENNReal.ofReal Mf :=
        lintegral_add_left' hmeas _
    _ = _ := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          lintegral_sub_left_eq_self (fun z => ‖dilate K r z - dilate K s z‖ₑ) x, mul_comm]

/-- **The supremum over rational scales.** For a bounded almost everywhere measurable `f` the
supremum over all positive scales defining the kernel maximal operator is already attained along
the positive rationals: by `tendsto_lintegral_enorm_dilate_sub` the dilation average varies
continuously with the scale, uniformly in `x`. -/
theorem kernelMaximal_eq_iSup_rat (hK : Integrable K) {f : (Fin 2 → ℝ) → ℝ} {Mf : ℝ}
    (hfm : AEMeasurable f volume) (hfb : ∀ y, ‖f y‖ ≤ Mf) (x : Fin 2 → ℝ) :
    kernelMaximal K f x =
      ⨆ q : {q : ℚ // 0 < q}, ∫⁻ y, ENNReal.ofReal (dilate K ((q : ℚ) : ℝ) (x - y)) * ‖f y‖ₑ := by
  refine le_antisymm (iSup₂_le fun s hs => ?_)
    (iSup_le fun q => le_kernelMaximal K f x (by exact_mod_cast q.2))
  have hMf : (0 : ℝ) ≤ Mf := (norm_nonneg _).trans (hfb x)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have htend : Tendsto (fun r : ℝ => ENNReal.ofReal Mf * ∫⁻ z, ‖dilate K r z - dilate K s z‖ₑ)
      (𝓝[>] s) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal Mf)
      (tendsto_lintegral_enorm_dilate_sub hK hs) (Or.inr ENNReal.ofReal_ne_top)
    simpa using h
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (ENNReal.tendsto_nhds_zero.1 htend ε (ENNReal.coe_pos.2 hε))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (mem_Ioi.1 hu)
  have hq0 : (0 : ℝ) < ((q : ℚ) : ℝ) := hs.trans hq1
  refine le_trans (lintegral_dilate_le_add hK hfm hfb hq0 x)
    (add_le_add ?_ (hsub ⟨hq1, hq2⟩))
  exact le_iSup (fun q : {q : ℚ // 0 < q} =>
    ∫⁻ y, ENNReal.ofReal (dilate K ((q : ℚ) : ℝ) (x - y)) * ‖f y‖ₑ)
    ⟨q, by exact_mod_cast hq0⟩

/-! ### The weak type bound for a bounded function -/

/-- The dilations of a nonnegative kernel are nonnegative. -/
theorem dilate_nonneg (hK₀ : 0 ≤ K) {s : ℝ} (hs : 0 < s) (x : Fin 2 → ℝ) : 0 ≤ dilate K s x :=
  mul_nonneg (by positivity) (by simpa using Pi.le_def.1 hK₀ (s⁻¹ • x))

/-- The kernel maximal operator only sees the size of `f`. -/
theorem kernelMaximal_congr (K : (Fin 2 → ℝ) → ℝ) {f g : (Fin 2 → ℝ) → ℝ}
    (h : ∀ y, ‖f y‖ₑ = ‖g y‖ₑ) (x : Fin 2 → ℝ) : kernelMaximal K f x = kernelMaximal K g x :=
  le_antisymm (kernelMaximal_mono K (fun y => (h y).le) x)
    (kernelMaximal_mono K (fun y => (h y).ge) x)

/-- The kernel maximal operator is unchanged by modifying `f` on a null set. -/
theorem kernelMaximal_congr_ae (K : (Fin 2 → ℝ) → ℝ) {f g : (Fin 2 → ℝ) → ℝ}
    (h : f =ᵐ[volume] g) (x : Fin 2 → ℝ) : kernelMaximal K f x = kernelMaximal K g x := by
  refine iSup_congr fun s => iSup_congr fun _ => lintegral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

/-- The integral of a function is at most its `L¹` norm, with the convention that the integral of
a function that is not integrable vanishes. -/
private theorem ofReal_integral_le_lintegral_enorm (f : (Fin 2 → ℝ) → ℝ) :
    ENNReal.ofReal (∫ x, f x) ≤ ∫⁻ x, ‖f x‖ₑ := by
  by_cases hf : Integrable f volume
  · rw [← ofReal_integral_norm_eq_lintegral_enorm hf]
    exact ENNReal.ofReal_le_ofReal (integral_mono hf hf.norm fun x => Real.le_norm_self (f x))
  · rw [integral_undef hf]
    simp

/-- **The weak type bound for one function.** If `Ω` is an exceptional set off which every
dilation average of a bounded nonnegative measurable `f` is at most `λ`, and `|Ω| ≤ M ∫ f / λ`,
then `λ |{M_K f > λ}| ≤ M ‖f‖₁`: by `kernelMaximal_eq_iSup_rat` only the countably many rational
scales matter, so the countably many exceptional null sets can be discarded at once. -/
theorem mul_volume_le_of_bounded (hK₀ : 0 ≤ K) (hKint : Integrable K) {f : (Fin 2 → ℝ) → ℝ}
    {Mf lam : ℝ} (hfm : Measurable f) (hf₀ : ∀ x, 0 ≤ f x) (hfM : ∀ x, f x ≤ Mf)
    (hlam : 0 < lam) {Ω : Set (Fin 2 → ℝ)}
    (hΩvol : volume Ω ≤ ENNReal.ofReal ((∫ x, K x) * (∫ x, f x) / lam))
    (hΩpt : ∀ s : ℝ, 0 < s → ∀ᵐ x, x ∉ Ω → (∫ y, dilate K s (x - y) * f y) ≤ lam) :
    ENNReal.ofReal lam * volume {x | ENNReal.ofReal lam < kernelMaximal K f x} ≤
      ENNReal.ofReal (∫ x, K x) * ∫⁻ x, ‖f x‖ₑ := by
  have hfn : ∀ y, ‖f y‖ ≤ Mf := fun y => by rw [Real.norm_of_nonneg (hf₀ y)]; exact hfM y
  -- the dilation average is the Lebesgue integral of a nonnegative product
  have hconv : ∀ s : ℝ, 0 < s → ∀ x, (∫⁻ y, ENNReal.ofReal (dilate K s (x - y)) * ‖f y‖ₑ)
      = ENNReal.ofReal (∫ y, dilate K s (x - y) * f y) := by
    intro s hs x
    have hint : Integrable fun y => dilate K s (x - y) * f y :=
      (integrable_dilate_sub hKint hs x).mul_bdd hfm.aestronglyMeasurable
        (Eventually.of_forall hfn)
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun y => mul_nonneg (dilate_nonneg hK₀ hs _) (hf₀ y))]
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal (hf₀ y), ENNReal.ofReal_mul (dilate_nonneg hK₀ hs _)]
  -- combining the countably many rational scales
  have hae : ∀ᵐ x, x ∉ Ω → kernelMaximal K f x ≤ ENNReal.ofReal lam := by
    have hrat : ∀ᵐ x, ∀ q : {q : ℚ // 0 < q}, x ∉ Ω →
        (∫⁻ y, ENNReal.ofReal (dilate K ((q : ℚ) : ℝ) (x - y)) * ‖f y‖ₑ)
          ≤ ENNReal.ofReal lam := by
      rw [ae_all_iff]
      intro q
      have hq : (0 : ℝ) < ((q : ℚ) : ℝ) := by exact_mod_cast q.2
      filter_upwards [hΩpt _ hq] with x hx hxΩ
      rw [hconv _ hq x]
      exact ENNReal.ofReal_le_ofReal (hx hxΩ)
    filter_upwards [hrat] with x hx hxΩ
    rw [kernelMaximal_eq_iSup_rat hKint hfm.aemeasurable hfn x]
    exact iSup_le fun q => hx q hxΩ
  -- so the level set is contained in `Ω` up to a null set
  have hvol : volume {x | ENNReal.ofReal lam < kernelMaximal K f x} ≤ volume Ω := by
    refine le_trans (measure_mono (fun x hx => ?_)) (le_trans (measure_union_le Ω
      {x | ¬ (x ∉ Ω → kernelMaximal K f x ≤ ENNReal.ofReal lam)}) ?_)
    · by_cases hxΩ : x ∈ Ω
      · exact Or.inl hxΩ
      · exact Or.inr fun hcon => absurd (hcon hxΩ) (not_le.2 hx)
    · rw [ae_iff.1 hae, add_zero]
  have hM0 : (0 : ℝ) ≤ ∫ x, K x :=
    integral_nonneg fun x => by simpa using Pi.le_def.1 hK₀ x
  calc ENNReal.ofReal lam * volume {x | ENNReal.ofReal lam < kernelMaximal K f x}
      ≤ ENNReal.ofReal lam * ENNReal.ofReal ((∫ x, K x) * (∫ x, f x) / lam) := by
        gcongr
        exact hvol.trans hΩvol
    _ = ENNReal.ofReal ((∫ x, K x) * (∫ x, f x)) := by
        rw [← ENNReal.ofReal_mul hlam.le]
        congr 1
        field_simp
    _ = ENNReal.ofReal (∫ x, K x) * ENNReal.ofReal (∫ x, f x) := ENNReal.ofReal_mul hM0
    _ ≤ ENNReal.ofReal (∫ x, K x) * ∫⁻ x, ‖f x‖ₑ := by
        gcongr
        exact ofReal_integral_le_lintegral_enorm f

/-! ### Truncations -/

/-- The truncation of `h` at height and radius `n + 1`. -/
private def trunc (h : (Fin 2 → ℝ) → ℝ) (n : ℕ) : (Fin 2 → ℝ) → ℝ :=
  (closedBall (0 : Fin 2 → ℝ) ((n : ℝ) + 1)).indicator fun x => min (h x) ((n : ℝ) + 1)

variable {h : (Fin 2 → ℝ) → ℝ}

private theorem measurable_trunc (hh : Measurable h) (n : ℕ) : Measurable (trunc h n) :=
  (hh.min measurable_const).indicator measurableSet_closedBall

private theorem trunc_nonneg (hh₀ : ∀ x, 0 ≤ h x) (n : ℕ) (x : Fin 2 → ℝ) : 0 ≤ trunc h n x :=
  Set.indicator_nonneg (fun y _ => le_min (hh₀ y) (by positivity)) x

private theorem trunc_le (hh₀ : ∀ x, 0 ≤ h x) (n : ℕ) (x : Fin 2 → ℝ) : trunc h n x ≤ h x := by
  by_cases hx : x ∈ closedBall (0 : Fin 2 → ℝ) ((n : ℝ) + 1)
  · rw [trunc, Set.indicator_of_mem hx]
    exact min_le_left _ _
  · rw [trunc, Set.indicator_of_notMem hx]
    exact hh₀ x

private theorem trunc_le_bound (n : ℕ) (x : Fin 2 → ℝ) : trunc h n x ≤ (n : ℝ) + 1 := by
  by_cases hx : x ∈ closedBall (0 : Fin 2 → ℝ) ((n : ℝ) + 1)
  · rw [trunc, Set.indicator_of_mem hx]
    exact min_le_right _ _
  · rw [trunc, Set.indicator_of_notMem hx]
    positivity

private theorem trunc_eq_zero {n : ℕ} {x : Fin 2 → ℝ} (hx : (n : ℝ) + 1 < ‖x‖) :
    trunc h n x = 0 :=
  Set.indicator_of_notMem (by simpa [mem_closedBall_zero_iff, not_le] using hx) _

private theorem trunc_mono (hh₀ : ∀ x, 0 ≤ h x) (x : Fin 2 → ℝ) :
    Monotone fun n : ℕ => trunc h n x := by
  intro n m hnm
  show trunc h n x ≤ trunc h m x
  have hnm' : ((n : ℝ) + 1) ≤ ((m : ℝ) + 1) := by
    have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.2 hnm
    linarith
  by_cases hx : x ∈ closedBall (0 : Fin 2 → ℝ) ((n : ℝ) + 1)
  · have hx' : x ∈ closedBall (0 : Fin 2 → ℝ) ((m : ℝ) + 1) :=
      closedBall_subset_closedBall hnm' hx
    simp only [trunc, Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    exact min_le_min_left _ hnm'
  · rw [trunc, Set.indicator_of_notMem hx]
    exact trunc_nonneg hh₀ m x

private theorem enorm_trunc_le (hh₀ : ∀ x, 0 ≤ h x) (n : ℕ) (x : Fin 2 → ℝ) :
    ‖trunc h n x‖ₑ ≤ ‖h x‖ₑ := by
  rw [Real.enorm_eq_ofReal (trunc_nonneg hh₀ n x), Real.enorm_eq_ofReal (hh₀ x)]
  exact ENNReal.ofReal_le_ofReal (trunc_le hh₀ n x)

private theorem enorm_trunc_mono (hh₀ : ∀ x, 0 ≤ h x) (x : Fin 2 → ℝ) :
    Monotone fun n : ℕ => ‖trunc h n x‖ₑ := by
  intro n m hnm
  show ‖trunc h n x‖ₑ ≤ ‖trunc h m x‖ₑ
  rw [Real.enorm_eq_ofReal (trunc_nonneg hh₀ n x), Real.enorm_eq_ofReal (trunc_nonneg hh₀ m x)]
  exact ENNReal.ofReal_le_ofReal (trunc_mono hh₀ x hnm)

private theorem iSup_enorm_trunc (hh₀ : ∀ x, 0 ≤ h x) (x : Fin 2 → ℝ) :
    ⨆ n, ‖trunc h n x‖ₑ = ‖h x‖ₑ := by
  refine le_antisymm (iSup_le fun n => enorm_trunc_le hh₀ n x) ?_
  obtain ⟨n, hn⟩ := exists_nat_ge (max ‖x‖ (h x))
  have hx : x ∈ closedBall (0 : Fin 2 → ℝ) ((n : ℝ) + 1) := by
    rw [mem_closedBall_zero_iff]
    have := (le_max_left ‖x‖ (h x)).trans hn
    linarith
  have hmin : min (h x) ((n : ℝ) + 1) = h x := by
    have := (le_max_right ‖x‖ (h x)).trans hn
    exact min_eq_left (by linarith)
  refine le_trans (le_of_eq ?_) (le_iSup (fun n : ℕ => ‖trunc h n x‖ₑ) n)
  rw [trunc, Set.indicator_of_mem hx, hmin]

/-! ### The main transfer -/

/-- **From a pointwise bound at every scale to the kernel weak type bound.** Suppose that for every
bounded, nonnegative, compactly supported measurable `f` and every level `λ > 0` there is an
exceptional set `Ω` with `|Ω| ≤ M ∫ f / λ` such that off `Ω` every dilation average of `f` is at
most `λ`, almost everywhere for each scale separately. Then `M = ∫ K` is a weak type `(1, 1)`
bound for the kernel maximal operator of `K`.

The scales are reduced to the countably many rational ones by `kernelMaximal_eq_iSup_rat`, so the
exceptional null sets can be discarded all at once (`mul_volume_le_of_bounded`); a general
integrable `f` is then reached through the truncations `trunc |f| n`, which increase to `|f|`. -/
theorem isKernelWeakTypeBound_of_pointwise (hK₀ : 0 ≤ K) (hKint : Integrable K)
    (hbound : ∀ (f : (Fin 2 → ℝ) → ℝ) (Mf b : ℝ), Measurable f → (∀ x, 0 ≤ f x) →
      (∀ x, f x ≤ Mf) → (∀ x, b < ‖x‖ → f x = 0) → 0 < b → ∀ lam : ℝ, 0 < lam →
      ∃ Ω : Set (Fin 2 → ℝ), MeasurableSet Ω ∧
        volume Ω ≤ ENNReal.ofReal ((∫ x, K x) * (∫ x, f x) / lam) ∧
        ∀ s : ℝ, 0 < s → ∀ᵐ x, x ∉ Ω → (∫ y, dilate K s (x - y) * f y) ≤ lam) :
    IsKernelWeakTypeBound K (ENNReal.ofReal (∫ x, K x)) := by
  -- the bound for a bounded, nonnegative, compactly supported measurable function
  have step : ∀ (g : (Fin 2 → ℝ) → ℝ) (Mg b : ℝ), Measurable g → (∀ x, 0 ≤ g x) →
      (∀ x, g x ≤ Mg) → (∀ x, b < ‖x‖ → g x = 0) → 0 < b → ∀ lam : ℝ, 0 < lam →
      ENNReal.ofReal lam * volume {x | ENNReal.ofReal lam < kernelMaximal K g x} ≤
        ENNReal.ofReal (∫ x, K x) * ∫⁻ x, ‖g x‖ₑ := by
    intro g Mg b hgm hg₀ hgM hgb hb lam hlam
    obtain ⟨Ω, -, hΩvol, hΩpt⟩ := hbound g Mg b hgm hg₀ hgM hgb hb lam hlam
    exact mul_volume_le_of_bounded hK₀ hKint hgm hg₀ hgM hlam hΩvol hΩpt
  intro f hf α
  -- a nonnegative measurable function with the same maximal function and the same `L¹` norm
  obtain ⟨h, hhm, hh₀, hmax, hlint⟩ :
      ∃ h : (Fin 2 → ℝ) → ℝ, Measurable h ∧ (∀ x, 0 ≤ h x) ∧
        (∀ x, kernelMaximal K f x = kernelMaximal K h x) ∧ ∫⁻ x, ‖f x‖ₑ = ∫⁻ x, ‖h x‖ₑ := by
    refine ⟨fun x => ‖hf.1.mk f x‖, Measurable.norm hf.1.measurable_mk, fun x => norm_nonneg _,
      fun x => ?_, lintegral_congr_ae ?_⟩
    · exact (kernelMaximal_congr_ae K hf.1.ae_eq_mk x).trans
        (kernelMaximal_congr K (fun y => by simp) x)
    · filter_upwards [hf.1.ae_eq_mk] with x hx
      simp [hx]
  rcases eq_or_ne α 0 with rfl | hα0
  · simp
  rcases eq_or_ne α ⊤ with rfl | hαtop
  · have hempty : {x | (⊤ : ℝ≥0∞) < kernelMaximal K f x} = ∅ := by
      ext x
      simp
    rw [hempty, measure_empty, mul_zero]
    exact zero_le
  obtain ⟨lam, hlam, rfl⟩ : ∃ lam : ℝ, 0 < lam ∧ α = ENNReal.ofReal lam :=
    ⟨α.toReal, ENNReal.toReal_pos hα0 hαtop, (ENNReal.ofReal_toReal hαtop).symm⟩
  -- the maximal functions of the truncations increase to the maximal function of `h`
  have hkm : ∀ x, kernelMaximal K h x = ⨆ n, kernelMaximal K (trunc h n) x := by
    intro x
    refine le_antisymm (iSup₂_le fun s hs => ?_)
      (iSup_le fun n => kernelMaximal_mono K (enorm_trunc_le hh₀ n) x)
    have hmeas : ∀ n : ℕ, AEMeasurable
        (fun y => ENNReal.ofReal (dilate K s (x - y)) * ‖trunc h n y‖ₑ) volume := fun n =>
      (ENNReal.measurable_ofReal.comp_aemeasurable
        (integrable_dilate_sub hKint hs x).1.aemeasurable).mul
          (measurable_trunc hhm n).aemeasurable.enorm
    have hmono : ∀ y : Fin 2 → ℝ, Monotone fun n : ℕ =>
        ENNReal.ofReal (dilate K s (x - y)) * ‖trunc h n y‖ₑ := fun y n m hnm =>
      mul_le_mul_right (enorm_trunc_mono hh₀ y hnm) _
    have hrw : (∫⁻ y, ENNReal.ofReal (dilate K s (x - y)) * ‖h y‖ₑ)
        = ⨆ n, ∫⁻ y, ENNReal.ofReal (dilate K s (x - y)) * ‖trunc h n y‖ₑ := by
      rw [← lintegral_iSup' (f := fun (n : ℕ) (y : Fin 2 → ℝ) =>
        ENNReal.ofReal (dilate K s (x - y)) * ‖trunc h n y‖ₑ) hmeas
        (Eventually.of_forall hmono)]
      exact lintegral_congr fun y => by rw [← ENNReal.mul_iSup, iSup_enorm_trunc hh₀ y]
    rw [hrw]
    exact iSup_mono fun n => le_kernelMaximal K (trunc h n) x hs
  have hset : {x | ENNReal.ofReal lam < kernelMaximal K f x}
      = ⋃ n, {x | ENNReal.ofReal lam < kernelMaximal K (trunc h n) x} := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion, hmax x, hkm x, lt_iSup_iff]
  have hsets : Monotone fun n : ℕ => {x | ENNReal.ofReal lam < kernelMaximal K (trunc h n) x} :=
    fun n m hnm x hx =>
      lt_of_lt_of_le hx (kernelMaximal_mono K (fun y => enorm_trunc_mono hh₀ y hnm) x)
  rw [hset, hsets.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun n => ?_
  refine le_trans (step (trunc h n) ((n : ℝ) + 1) ((n : ℝ) + 1) (measurable_trunc hhm n)
    (trunc_nonneg hh₀ n) (trunc_le_bound n) (fun x hx => trunc_eq_zero hx) (by positivity)
    lam hlam) ?_
  rw [hlint]
  gcongr
  exact enorm_trunc_le hh₀ n _

end CenteredMaximal
