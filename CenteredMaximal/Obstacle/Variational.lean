/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.BoundedFunctional
public import CenteredMaximal.Analysis.EnergyDensity
public import CenteredMaximal.Obstacle.Functional

/-!
# The variational inequality and the two-sided bound on the obstacle minimiser

Fix `0 < α < 2`, `0 < κ` and an obstacle `f : ℝ² → ℝ` which is measurable, nonnegative, bounded
and compactly supported, and let `u` be a minimiser of the obstacle functional
`Φ(v) = ½ E(v, v) + κ ‖v‖₁ − ∫ f v` over the nonnegative elements of the energy space `H_α` of
finite `L¹` norm, as produced by `CenteredMaximal.exists_isMinOn_nonnegCone`. This file derives the
first-order variational inequality and the two-sided distributional bound `f − κ ≤ L u ≤ f`, and
packages the latter as a density `σ = f − L u` with values in `[0, κ]`.

* `jumpEnergy_ne_top_of_bounds`, `jumpEnergy_ne_top_of_isTestFunction`: a **test function has
  finite energy**. A smooth compactly supported `φ` is bounded by `M` and globally Lipschitz
  (`ContDiff.lipschitzWith_of_hasCompactSupport`), so the squared increment along `t e_j` is at
  most `max (L², 4 M²) min (t², 1)` (`sq_sub_le_max_mul_min`) and vanishes unless one of the two
  endpoints lies in a fixed cube; Tonelli
  (`lintegral_mul_add_comp_add_smul_single`) and the integrability of `min (t², 1) |t|^{−(1+α)}`
  from `CenteredMaximal.Analysis.EnergyDensity` then bound the energy. `EnergySpace.ofTestFunction`
  is the corresponding element of `H_α`, with `EnergySpace.coeFn_ofTestFunction` and the
  additivity and homogeneity lemmas `EnergySpace.ofTestFunction_add`,
  `EnergySpace.ofTestFunction_smul`;
* `EnergySpace.jumpForm_coeFn_add_right`, ...: bilinearity of the jump form on `H_α`, read off the
  energy inner product through `EnergySpace.jumpForm_eq`; `toReal_l1Norm`, `l1Norm_le_of_ae_le`,
  `l1Norm_ofTestFunction`: the `L¹` norm on the positive cone;
* `variational_inequality`: **the first-order variational inequality**. Along the segment
  `w(t) = u + t (v − u)`, which stays in the cone and has `‖w(t)‖₁ = (1 − t) ‖u‖₁ + t ‖v‖₁`, the
  functional is `Φ(u) + t A + t²/2 E(v − u, v − u)` with
  `A = E(u, v − u) + κ (‖v‖₁ − ‖u‖₁) − ∫ f (v − u)`, so minimality forces `A ≥ 0`;
* `jumpForm_add_le_of_isTestFunction`: **positive variations**, the competitor `v = u + φ` for a
  nonnegative test function `φ`, i.e. `L u ≥ f − κ`;
* `jumpForm_le_integral_mul_of_isTestFunction`: **the competitor argument**, i.e. `L u ≤ f`. For
  `t > 0` the competitor is `u − d` with `d = min (u, t φ) = t φ − w` and `w = (t φ − u)₊`; the
  Markov truncation inequality `EnergySpace.jumpForm_posPart_self_le` gives
  `E(w, w) ≤ E(t φ − u, w)`, and Cauchy–Schwarz together with `le_sub_mul_of_sq_le_mul` gives
  `E(u, d) ≥ t E(u, φ) − t²/4 E(φ, φ)`; since `0 ≤ d ≤ t φ` the source term costs at most
  `t ∫ f φ`, so dividing by `t` and letting `t → 0⁺` finishes;
* `isBoundedPositiveFunctional_source_sub_jumpForm`, `exists_density`: **the capped density**. The
  functional `T φ = ∫ f φ − E(u, φ)` is additive, homogeneous, nonnegative and bounded by
  `κ ∫ φ` on test functions, so `CenteredMaximal.Analysis.BoundedFunctional` represents it by a
  measurable `σ` with `0 ≤ σ ≤ κ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal RealInnerProductSpace

namespace CenteredMaximal

/-- `L²(ℝ²)` with respect to Lebesgue measure. -/
local notation "L²" => Lp ℝ 2 (volume : Measure (Fin 2 → ℝ))

open EnergySpace

variable {α κ : ℝ} {f φ ψ : (Fin 2 → ℝ) → ℝ}

/-! ### Test functions have finite energy -/

/-- The pointwise bound on a squared increment of a function bounded by `M` whose increment over a
displacement of size `|s|` is at most `L |s|`: it is at most `max (L², 4 M²) min (s², 1)`. -/
theorem sq_sub_le_max_mul_min {L M a b s : ℝ} (hab : |a - b| ≤ L * |s|) (ha : |a| ≤ M)
    (hb : |b| ≤ M) : (a - b) ^ 2 ≤ max (L ^ 2) (4 * M ^ 2) * min (s ^ 2) 1 := by
  have h₁ : (a - b) ^ 2 ≤ L ^ 2 * s ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (a - b)) hab 2
    rwa [sq_abs, mul_pow, sq_abs] at h
  have h₂ : (a - b) ^ 2 ≤ 4 * M ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (a - b))
      (abs_le.2 ⟨by linarith [(abs_le.1 ha).1, (abs_le.1 hb).2],
        by linarith [(abs_le.1 ha).2, (abs_le.1 hb).1]⟩ : |a - b| ≤ 2 * M) 2
    rw [sq_abs] at h
    nlinarith [h]
  rcases le_total (s ^ 2) 1 with hs | hs
  · rw [min_eq_left hs]
    exact h₁.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg s))
  · rw [min_eq_right hs, mul_one]
    exact h₂.trans (le_max_right _ _)

/-- **Tonelli** for an integrand which is a function of the increment `t` times the sum of the
values of a weight at the two endpoints of the jump: the `x`-integral of each term is the integral
of the weight, by translation invariance. -/
theorem lintegral_mul_add_comp_add_smul_single {G : ℝ → ℝ≥0∞} (hG : Measurable G)
    {χ : (Fin 2 → ℝ) → ℝ≥0∞} (hχ : Measurable χ) (j : Fin 2) :
    ∫⁻ p : (Fin 2 → ℝ) × ℝ, G p.2 * (χ p.1 + χ (p.1 + p.2 • Pi.single j 1)) =
      (∫⁻ t, G t) * (2 * ∫⁻ x, χ x) := by
  have hm1 : Measurable fun p : (Fin 2 → ℝ) × ℝ => G p.2 * χ p.1 :=
    (hG.comp measurable_snd).mul (hχ.comp measurable_fst)
  have hm2 : Measurable fun p : (Fin 2 → ℝ) × ℝ => G p.2 * χ (p.1 + p.2 • Pi.single j 1) :=
    (hG.comp measurable_snd).mul (hχ.comp (measurable_fst.add (measurable_snd.smul_const _)))
  have h1 : ∫⁻ p : (Fin 2 → ℝ) × ℝ, G p.2 * χ p.1 = (∫⁻ t, G t) * ∫⁻ x, χ x := by
    calc ∫⁻ p : (Fin 2 → ℝ) × ℝ, G p.2 * χ p.1
        = ∫⁻ t : ℝ, ∫⁻ x, G t * χ x := by
          rw [Measure.volume_eq_prod]; exact lintegral_prod_symm _ hm1.aemeasurable
      _ = ∫⁻ t : ℝ, G t * ∫⁻ x, χ x := lintegral_congr fun _ => lintegral_const_mul _ hχ
      _ = _ := lintegral_mul_const _ hG
  have h2 : ∫⁻ p : (Fin 2 → ℝ) × ℝ, G p.2 * χ (p.1 + p.2 • Pi.single j 1) =
      (∫⁻ t, G t) * ∫⁻ x, χ x := by
    have key : ∀ t : ℝ, ∫⁻ x, G t * χ (x + t • Pi.single j 1) = G t * ∫⁻ x, χ x := fun t => by
      have hm : Measurable fun x : Fin 2 → ℝ => χ (x + t • Pi.single j 1) :=
        hχ.comp (measurable_id.add_const _)
      rw [lintegral_const_mul _ hm, lintegral_add_right_eq_self χ (t • Pi.single j 1)]
    calc ∫⁻ p : (Fin 2 → ℝ) × ℝ, G p.2 * χ (p.1 + p.2 • Pi.single j 1)
        = ∫⁻ t : ℝ, ∫⁻ x, G t * χ (x + t • Pi.single j 1) := by
          rw [Measure.volume_eq_prod]; exact lintegral_prod_symm _ hm2.aemeasurable
      _ = ∫⁻ t : ℝ, G t * ∫⁻ x, χ x := lintegral_congr key
      _ = _ := lintegral_mul_const _ hG
  calc ∫⁻ p : (Fin 2 → ℝ) × ℝ, G p.2 * (χ p.1 + χ (p.1 + p.2 • Pi.single j 1))
      = ∫⁻ p : (Fin 2 → ℝ) × ℝ, (G p.2 * χ p.1 + G p.2 * χ (p.1 + p.2 • Pi.single j 1)) :=
        lintegral_congr fun _ => mul_add _ _ _
    _ = (∫⁻ p : (Fin 2 → ℝ) × ℝ, G p.2 * χ p.1) +
          ∫⁻ p : (Fin 2 → ℝ) × ℝ, G p.2 * χ (p.1 + p.2 • Pi.single j 1) :=
        lintegral_add_left hm1 _
    _ = _ := by rw [h1, h2]; ring

/-- A bounded function with increment bound `L |t|` supported in the cube `Q(0, r)` has finite
jump energy when `0 < α < 2`: the squared increment is at most `max (L², 4 M²) min (t², 1)` and
vanishes unless one endpoint lies in the cube, so the energy is at most
`2 |Q(0, r)| max (L², 4 M²) ∫ min (t², 1) |t|^{−(1+α)} dt`, which is finite since `1 − α > −1`
near the origin and `−(1 + α) < −1` at infinity. -/
theorem jumpEnergy_ne_top_of_bounds (hα : 0 < α) (hα' : α < 2) {u : (Fin 2 → ℝ) → ℝ}
    {L M r : ℝ} (hr : 0 ≤ r) (hlip : ∀ x y, |u x - u y| ≤ L * ‖x - y‖) (hbd : ∀ x, |u x| ≤ M)
    (hsupp : ∀ x, x ∉ closedBall (0 : Fin 2 → ℝ) r → u x = 0) : jumpEnergy α u ≠ ⊤ := by
  have hC0 : (0 : ℝ) ≤ max (L ^ 2) (4 * M ^ 2) := le_max_of_le_left (sq_nonneg L)
  have hGm : Measurable fun t : ℝ =>
      ENNReal.ofReal (max (L ^ 2) (4 * M ^ 2) * (min (t ^ 2) 1 * |t| ^ (-(1 + α)))) :=
    (measurable_const.mul (((measurable_id.pow_const 2).min measurable_const).mul
      (measurable_id.abs.pow_const _))).ennreal_ofReal
  have hχm : Measurable ((closedBall (0 : Fin 2 → ℝ) r).indicator (1 : (Fin 2 → ℝ) → ℝ≥0∞)) :=
    measurable_one.indicator measurableSet_closedBall
  have hGfin : (∫⁻ t : ℝ, ENNReal.ofReal
      (max (L ^ 2) (4 * M ^ 2) * (min (t ^ 2) 1 * |t| ^ (-(1 + α))))) ≠ ⊤ := by
    calc ∫⁻ t : ℝ, ENNReal.ofReal
          (max (L ^ 2) (4 * M ^ 2) * (min (t ^ 2) 1 * |t| ^ (-(1 + α))))
        = ∫⁻ t : ℝ, ENNReal.ofReal (max (L ^ 2) (4 * M ^ 2)) *
            ENNReal.ofReal (min (t ^ 2) 1 * |t| ^ (-(1 + α))) :=
          lintegral_congr fun _ => ENNReal.ofReal_mul hC0
      _ = ENNReal.ofReal (max (L ^ 2) (4 * M ^ 2)) *
            ∫⁻ t : ℝ, ENNReal.ofReal (min (t ^ 2) 1 * |t| ^ (-(1 + α))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (lintegral_min_sq_one_mul_rpow_lt_top hα hα').ne
  -- the pointwise bound on the integrand of each coordinate summand
  have hpt : ∀ (j : Fin 2) (p : (Fin 2 → ℝ) × ℝ),
      ENNReal.ofReal ((u (p.1 + p.2 • Pi.single j 1) - u p.1) ^ 2 * |p.2| ^ (-(1 + α))) ≤
        ENNReal.ofReal (max (L ^ 2) (4 * M ^ 2) * (min (p.2 ^ 2) 1 * |p.2| ^ (-(1 + α)))) *
          ((closedBall (0 : Fin 2 → ℝ) r).indicator 1 p.1 +
            (closedBall (0 : Fin 2 → ℝ) r).indicator 1 (p.1 + p.2 • Pi.single j 1)) := by
    intro j p
    have hw : (0 : ℝ) ≤ |p.2| ^ (-(1 + α)) := Real.rpow_nonneg (abs_nonneg _) _
    by_cases hz : u (p.1 + p.2 • Pi.single j 1) - u p.1 = 0
    · rw [hz]
      simp
    have hind : (1 : ℝ≥0∞) ≤ (closedBall (0 : Fin 2 → ℝ) r).indicator 1 p.1 +
        (closedBall (0 : Fin 2 → ℝ) r).indicator 1 (p.1 + p.2 • Pi.single j 1) := by
      by_cases hx : p.1 ∈ closedBall (0 : Fin 2 → ℝ) r
      · simp [Set.indicator_of_mem hx]
      by_cases hy : p.1 + p.2 • Pi.single j 1 ∈ closedBall (0 : Fin 2 → ℝ) r
      · simp [Set.indicator_of_mem hy]
      refine absurd ?_ hz
      rw [hsupp _ hy, hsupp _ hx, sub_zero]
    have hnorm : ‖p.1 + p.2 • Pi.single j 1 - p.1‖ = |p.2| := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one]
    calc ENNReal.ofReal ((u (p.1 + p.2 • Pi.single j 1) - u p.1) ^ 2 * |p.2| ^ (-(1 + α)))
        ≤ ENNReal.ofReal (max (L ^ 2) (4 * M ^ 2) * (min (p.2 ^ 2) 1 * |p.2| ^ (-(1 + α)))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          refine (mul_le_mul_of_nonneg_right (sq_sub_le_max_mul_min
            (hnorm ▸ hlip (p.1 + p.2 • Pi.single j 1) p.1) (hbd _) (hbd _)) hw).trans_eq ?_
          ring
      _ = ENNReal.ofReal (max (L ^ 2) (4 * M ^ 2) *
            (min (p.2 ^ 2) 1 * |p.2| ^ (-(1 + α)))) * 1 := (mul_one _).symm
      _ ≤ _ := by gcongr
  unfold jumpEnergy
  refine (ENNReal.sum_lt_top.2 fun j _ => ?_).ne
  refine (lintegral_mono (hpt j)).trans_lt ?_
  rw [lintegral_mul_add_comp_add_smul_single hGm hχm j,
    lintegral_indicator_one measurableSet_closedBall]
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hGfin)
    (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.2 (volume_closedBall_ne_top hr)))

/-- **Test functions have finite energy**: a smooth function with compact support is bounded and
globally Lipschitz, so `jumpEnergy_ne_top_of_bounds` applies. -/
theorem jumpEnergy_ne_top_of_isTestFunction (hα : 0 < α) (hα' : α < 2)
    (hφ : IsTestFunction φ) : jumpEnergy α φ ≠ ⊤ := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) hφ.2 hφ.1 (by simp)
  obtain ⟨M, hM⟩ := hφ.2.exists_bound_of_continuous hφ.continuous
  have hcomp : IsCompact (tsupport φ) := hφ.2
  obtain ⟨r, hr⟩ := hcomp.isBounded.subset_closedBall (0 : Fin 2 → ℝ)
  refine jumpEnergy_ne_top_of_bounds hα hα' (L := L) (M := M) (r := max r 0)
    (le_max_right _ _) (fun x y => ?_) (fun x => ?_) fun x hx => ?_
  · have h := hL.dist_le_mul x y
    rwa [Real.dist_eq, dist_eq_norm] at h
  · rw [← Real.norm_eq_abs]
    exact hM x
  · exact image_eq_zero_of_notMem_tsupport fun h =>
      hx (closedBall_subset_closedBall (le_max_left _ _) (hr h))

/-- A test function lies in `L²`: it is bounded and has compact support. -/
theorem memLp_two_of_isTestFunction (hφ : IsTestFunction φ) :
    MemLp φ 2 (volume : Measure (Fin 2 → ℝ)) := by
  obtain ⟨M, hM⟩ := hφ.2.exists_bound_of_continuous hφ.continuous
  exact hφ.2.memLp_of_bound hφ.continuous.aestronglyMeasurable M (ae_of_all _ hM)

/-- A test function is integrable. -/
theorem integrable_of_isTestFunction (hφ : IsTestFunction φ) :
    Integrable φ (volume : Measure (Fin 2 → ℝ)) :=
  hφ.continuous.integrable_of_hasCompactSupport hφ.2

namespace EnergySpace

/-- A test function as an element of the energy space. -/
def ofTestFunction (hα : 0 < α) (hα' : α < 2) (hφ : IsTestFunction φ) : EnergySpace α :=
  mk ((memLp_two_of_isTestFunction hφ).toLp φ) <| by
    rw [jumpEnergy_congr_ae α (memLp_two_of_isTestFunction hφ).coeFn_toLp]
    exact jumpEnergy_ne_top_of_isTestFunction hα hα' hφ

/-- The energy-space element of a test function is almost everywhere the test function. -/
theorem coeFn_ofTestFunction (hα : 0 < α) (hα' : α < 2) (hφ : IsTestFunction φ) :
    ⇑(ofTestFunction hα hα' hφ) =ᵐ[volume] φ :=
  (memLp_two_of_isTestFunction hφ).coeFn_toLp

/-- Two elements of the energy space with almost everywhere equal functions are equal. -/
theorem eq_of_coeFn_ae {u v : EnergySpace α} (h : ⇑u =ᵐ[volume] ⇑v) : u = v :=
  ext (Lp.ext_iff.2 h)

/-- The energy-space element of a sum of test functions is the sum of the elements. -/
theorem ofTestFunction_add (hα : 0 < α) (hα' : α < 2) (hφ : IsTestFunction φ)
    (hψ : IsTestFunction ψ) : ofTestFunction hα hα' (hφ.add hψ) =
      ofTestFunction hα hα' hφ + ofTestFunction hα hα' hψ := by
  refine eq_of_coeFn_ae ?_
  filter_upwards [coeFn_ofTestFunction hα hα' (hφ.add hψ),
    Lp.coeFn_add ((ofTestFunction hα hα' hφ : L²)) ((ofTestFunction hα hα' hψ : L²)),
    coeFn_ofTestFunction hα hα' hφ, coeFn_ofTestFunction hα hα' hψ] with x h h' h₁ h₂
  rw [h, show ⇑(ofTestFunction hα hα' hφ + ofTestFunction hα hα' hψ) x =
    ⇑(ofTestFunction hα hα' hφ) x + ⇑(ofTestFunction hα hα' hψ) x from h', h₁, h₂,
    Pi.add_apply]

/-- The energy-space element of a scalar multiple of a test function is the multiple. -/
theorem ofTestFunction_smul (hα : 0 < α) (hα' : α < 2) (c : ℝ) (hφ : IsTestFunction φ) :
    ofTestFunction hα hα' (hφ.smul c) = c • ofTestFunction hα hα' hφ := by
  refine eq_of_coeFn_ae ?_
  filter_upwards [coeFn_ofTestFunction hα hα' (hφ.smul c),
    Lp.coeFn_smul c ((ofTestFunction hα hα' hφ : L²)), coeFn_ofTestFunction hα hα' hφ]
    with x h h' h₁
  rw [h, show ⇑(c • ofTestFunction hα hα' hφ) x = c * ⇑(ofTestFunction hα hα' hφ) x from h', h₁,
    Pi.smul_apply, smul_eq_mul]

/-- A nonnegative test function gives an element of the positive cone. -/
theorem ofTestFunction_mem_nonnegCone (hα : 0 < α) (hα' : α < 2) (hφ : IsTestFunction φ)
    (hφ0 : ∀ x, 0 ≤ φ x) : ofTestFunction hα hα' hφ ∈ nonnegCone α := by
  rw [mem_nonnegCone_iff_ae]
  filter_upwards [coeFn_ofTestFunction hα hα' hφ] with x hx
  rw [Pi.zero_apply, hx]
  exact hφ0 x

end EnergySpace


namespace EnergySpace

/-! ### Coercion and bilinearity lemmas -/

/-- The function of a sum is almost everywhere the sum of the functions. -/
theorem coeFn_add_ae (u v : EnergySpace α) : ⇑(u + v) =ᵐ[volume] fun x => u x + v x :=
  Lp.coeFn_add (u : L²) (v : L²)

/-- The function of a difference is almost everywhere the difference of the functions. -/
theorem coeFn_sub_ae (u v : EnergySpace α) : ⇑(u - v) =ᵐ[volume] fun x => u x - v x :=
  Lp.coeFn_sub (u : L²) (v : L²)

/-- The function of a scalar multiple is almost everywhere the scalar multiple. -/
theorem coeFn_smul_ae (c : ℝ) (u : EnergySpace α) : ⇑(c • u) =ᵐ[volume] fun x => c * u x :=
  Lp.coeFn_smul c (u : L²)

/-- The jump form is additive in the second argument on the energy space. -/
theorem jumpForm_coeFn_add_right (u v w : EnergySpace α) :
    jumpForm α ⇑u ⇑(v + w) = jumpForm α ⇑u ⇑v + jumpForm α ⇑u ⇑w := by
  rw [jumpForm_eq, jumpForm_eq, jumpForm_eq, inner_add_right, toLp_add, inner_add_right]
  ring

/-- The jump form is subtractive in the second argument on the energy space. -/
theorem jumpForm_coeFn_sub_right (u v w : EnergySpace α) :
    jumpForm α ⇑u ⇑(v - w) = jumpForm α ⇑u ⇑v - jumpForm α ⇑u ⇑w := by
  rw [jumpForm_eq, jumpForm_eq, jumpForm_eq, inner_sub_right, toLp_sub, inner_sub_right]
  ring

/-- The jump form is odd in the second argument on the energy space. -/
theorem jumpForm_coeFn_neg_right (u v : EnergySpace α) :
    jumpForm α ⇑u ⇑(-v) = -jumpForm α ⇑u ⇑v := by
  rw [jumpForm_eq, jumpForm_eq, inner_neg_right, toLp_neg, inner_neg_right]
  ring

/-- The jump form is homogeneous in the second argument on the energy space. -/
theorem jumpForm_coeFn_smul_right (c : ℝ) (u v : EnergySpace α) :
    jumpForm α ⇑u ⇑(c • v) = c * jumpForm α ⇑u ⇑v := by
  rw [jumpForm_eq, jumpForm_eq, real_inner_smul_right, toLp_smul, real_inner_smul_right]
  ring

/-- The jump form is subtractive in the first argument on the energy space. -/
theorem jumpForm_coeFn_sub_left (u v w : EnergySpace α) :
    jumpForm α ⇑(u - v) ⇑w = jumpForm α ⇑u ⇑w - jumpForm α ⇑v ⇑w := by
  rw [jumpForm_comm, jumpForm_coeFn_sub_right, jumpForm_comm α ⇑w ⇑u, jumpForm_comm α ⇑w ⇑v]

/-- The jump form is homogeneous in the first argument on the energy space. -/
theorem jumpForm_coeFn_smul_left (c : ℝ) (u v : EnergySpace α) :
    jumpForm α ⇑(c • u) ⇑v = c * jumpForm α ⇑u ⇑v := by
  rw [jumpForm_comm, jumpForm_coeFn_smul_right, jumpForm_comm α ⇑v ⇑u]

end EnergySpace

/-! ### The `L¹` norm on the positive cone -/

/-- An energy-space element of finite `L¹` norm is integrable. -/
theorem integrable_of_l1Norm_ne_top {u : EnergySpace α} (hu : l1Norm u ≠ ⊤) :
    Integrable ⇑u volume :=
  ⟨Lp.aestronglyMeasurable (u : L²), hasFiniteIntegral_iff_enorm.2 (lt_top_iff_ne_top.2 hu)⟩

/-- An integrable energy-space element has finite `L¹` norm. -/
theorem l1Norm_ne_top_of_integrable {u : EnergySpace α} (hu : Integrable ⇑u volume) :
    l1Norm u ≠ ⊤ :=
  (hasFiniteIntegral_iff_enorm.1 hu.2).ne

/-- On the positive cone the real `L¹` norm is the integral. -/
theorem toReal_l1Norm {u : EnergySpace α} (hu : u ∈ nonnegCone α) :
    (l1Norm u).toReal = ∫ x, u x := by
  have h : ∫ x, ‖u x‖ = ∫ x, u x := by
    refine integral_congr_ae ?_
    filter_upwards [nonneg_ae_of_mem_nonnegCone hu] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
  rw [← h, integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable (u : L²)), l1Norm]

/-- The `L¹` norm is monotone for the almost everywhere order on nonnegative elements. -/
theorem l1Norm_le_of_ae_le {u v : EnergySpace α} (hu : ∀ᵐ x ∂volume, 0 ≤ u x)
    (huv : ∀ᵐ x ∂volume, u x ≤ v x) : l1Norm u ≤ l1Norm v := by
  refine lintegral_mono_ae ?_
  filter_upwards [hu, huv] with x h₁ h₂
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal ((abs_of_nonneg h₁).trans_le (h₂.trans (le_abs_self _)))

/-- A test function has finite `L¹` norm in the energy space. -/
theorem l1Norm_ofTestFunction_ne_top (hα : 0 < α) (hα' : α < 2) (hφ : IsTestFunction φ) :
    l1Norm (ofTestFunction hα hα' hφ) ≠ ⊤ :=
  l1Norm_ne_top_of_integrable
    ((integrable_of_isTestFunction hφ).congr (coeFn_ofTestFunction hα hα' hφ).symm)

/-- The `L¹` norm of a nonnegative test function is its integral. -/
theorem l1Norm_ofTestFunction (hα : 0 < α) (hα' : α < 2) (hφ : IsTestFunction φ)
    (hφ0 : ∀ x, 0 ≤ φ x) :
    l1Norm (ofTestFunction hα hα' hφ) = ENNReal.ofReal (∫ x, φ x) := by
  rw [← ENNReal.ofReal_toReal (l1Norm_ofTestFunction_ne_top hα hα' hφ),
    toReal_l1Norm (ofTestFunction_mem_nonnegCone hα hα' hφ hφ0)]
  exact congrArg ENNReal.ofReal (integral_congr_ae (coeFn_ofTestFunction hα hα' hφ))

/-! ### The variational inequality -/

/-- **The first-order variational inequality**: along the segment from the minimiser `u` to an
admissible competitor `v` the obstacle functional is
`Φ(u) + t A + t²/2 E(v − u, v − u)` with `A` the displayed expression, so minimality forces
`A ≥ 0`. -/
theorem variational_inequality (hf : MemLp f 2 volume) {u : EnergySpace α}
    (hu : u ∈ nonnegCone α) (hufin : l1Norm u ≠ ⊤)
    (hmin : ∀ v ∈ nonnegCone α, l1Norm v ≠ ⊤ → obstacleFun α κ f u ≤ obstacleFun α κ f v)
    {v : EnergySpace α} (hv : v ∈ nonnegCone α) (hvfin : l1Norm v ≠ ⊤) :
    0 ≤ jumpForm α ⇑u ⇑(v - u) + κ * ((l1Norm v).toReal - (l1Norm u).toReal) -
      ∫ x, f x * (v x - u x) := by
  have hQ0 : 0 ≤ jumpForm α ⇑(v - u) ⇑(v - u) := jumpForm_self_nonneg α _
  have hsub : ∫ x, f x * ⇑(v - u) x = ∫ x, f x * (v x - u x) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_sub_ae v u] with x hx
    rw [hx]
  -- the expansion of the functional along the segment
  have hkey : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      0 ≤ t * (jumpForm α ⇑u ⇑(v - u) + κ * ((l1Norm v).toReal - (l1Norm u).toReal) -
        ∫ x, f x * (v x - u x)) + t ^ 2 / 2 * jumpForm α ⇑(v - u) ⇑(v - u) := by
    intro t ht0 ht1
    have hw : u + t • (v - u) = (1 - t) • u + t • v := by module
    have hcone : u + t • (v - u) ∈ nonnegCone α := by
      rw [hw]
      exact convex_nonnegCone hu hv (by linarith) ht0 (by ring)
    have hfin₁ : ENNReal.ofReal (1 - t) * l1Norm u ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hufin
    have hfin₂ : ENNReal.ofReal t * l1Norm v ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvfin
    have hl1 : l1Norm (u + t • (v - u)) =
        ENNReal.ofReal (1 - t) * l1Norm u + ENNReal.ofReal t * l1Norm v := by
      rw [hw, l1Norm_add (smul_mem_nonnegCone (by linarith) hu) (smul_mem_nonnegCone ht0 hv),
        l1Norm_smul (by linarith), l1Norm_smul ht0]
    have hl1fin : l1Norm (u + t • (v - u)) ≠ ⊤ := by
      rw [hl1]
      exact ENNReal.add_ne_top.2 ⟨hfin₁, hfin₂⟩
    have hl1real : (l1Norm (u + t • (v - u))).toReal =
        (1 - t) * (l1Norm u).toReal + t * (l1Norm v).toReal := by
      rw [hl1, ENNReal.toReal_add hfin₁ hfin₂, ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal ht0]
    have hquad : jumpForm α ⇑(u + t • (v - u)) ⇑(u + t • (v - u)) =
        jumpForm α ⇑u ⇑u + 2 * t * jumpForm α ⇑u ⇑(v - u) +
          t ^ 2 * jumpForm α ⇑(v - u) ⇑(v - u) := by
      have h := jumpForm_smul_add_smul (α := α) 1 t u (v - u)
      rw [one_smul] at h
      rw [h]
      ring
    have hsrc : ∫ x, f x * ⇑(u + t • (v - u)) x =
        (∫ x, f x * u x) + t * ∫ x, f x * (v x - u x) := by
      have h : sourceFunctional α hf (u + t • (v - u)) =
          sourceFunctional α hf u + t * sourceFunctional α hf (v - u) := by
        rw [map_add, map_smul, smul_eq_mul]
      rw [sourceFunctional_apply, sourceFunctional_apply, sourceFunctional_apply, hsub] at h
      exact h
    have hstep := hmin _ hcone hl1fin
    rw [obstacleFun, obstacleFun, hquad, hl1real, hsrc] at hstep
    have hring : t * (jumpForm α ⇑u ⇑(v - u) + κ * ((l1Norm v).toReal - (l1Norm u).toReal) -
          ∫ x, f x * (v x - u x)) + t ^ 2 / 2 * jumpForm α ⇑(v - u) ⇑(v - u) =
        ((jumpForm α ⇑u ⇑u + 2 * t * jumpForm α ⇑u ⇑(v - u) +
              t ^ 2 * jumpForm α ⇑(v - u) ⇑(v - u)) / 2 +
            κ * ((1 - t) * (l1Norm u).toReal + t * (l1Norm v).toReal) -
            ((∫ x, f x * u x) + t * ∫ x, f x * (v x - u x))) -
          (jumpForm α ⇑u ⇑u / 2 + κ * (l1Norm u).toReal - ∫ x, f x * u x) := by ring
    rw [hring]
    linarith [hstep]
  -- let `t` tend to zero
  by_contra hcon
  have hA : jumpForm α ⇑u ⇑(v - u) + κ * ((l1Norm v).toReal - (l1Norm u).toReal) -
      ∫ x, f x * (v x - u x) < 0 := not_le.1 hcon
  have hden : (0 : ℝ) < jumpForm α ⇑(v - u) ⇑(v - u) + 1 := by linarith
  have ht : 0 < min 1 (-(jumpForm α ⇑u ⇑(v - u) + κ * ((l1Norm v).toReal - (l1Norm u).toReal) -
      ∫ x, f x * (v x - u x)) / (jumpForm α ⇑(v - u) ⇑(v - u) + 1)) :=
    lt_min one_pos (div_pos (by linarith) hden)
  have hle : min 1 (-(jumpForm α ⇑u ⇑(v - u) + κ * ((l1Norm v).toReal - (l1Norm u).toReal) -
        ∫ x, f x * (v x - u x)) / (jumpForm α ⇑(v - u) ⇑(v - u) + 1)) *
      (jumpForm α ⇑(v - u) ⇑(v - u) + 1) ≤
      -(jumpForm α ⇑u ⇑(v - u) + κ * ((l1Norm v).toReal - (l1Norm u).toReal) -
        ∫ x, f x * (v x - u x)) := by
    rw [← le_div_iff₀ hden]
    exact min_le_right _ _
  nlinarith [hkey _ ht.le (min_le_left _ _), ht, hle, hQ0, hA, mul_le_mul_of_nonneg_left hle ht.le]

/-! ### Positive variations -/

/-- **Positive variations**: testing the variational inequality against `u + φ` for a nonnegative
test function `φ` is the distributional lower bound `L u ≥ f − κ`. -/
theorem jumpForm_add_le_of_isTestFunction (hα : 0 < α) (hα' : α < 2) (hf : MemLp f 2 volume)
    {u : EnergySpace α} (hu : u ∈ nonnegCone α) (hufin : l1Norm u ≠ ⊤)
    (hmin : ∀ v ∈ nonnegCone α, l1Norm v ≠ ⊤ → obstacleFun α κ f u ≤ obstacleFun α κ f v)
    (hφ : IsTestFunction φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    ∫ x, f x * φ x ≤ jumpForm α ⇑u ⇑(ofTestFunction hα hα' hφ) + κ * ∫ x, φ x := by
  set P := ofTestFunction hα hα' hφ with hP
  have hPcone : P ∈ nonnegCone α := hP ▸ ofTestFunction_mem_nonnegCone hα hα' hφ hφ0
  have hPfin : l1Norm P ≠ ⊤ := hP ▸ l1Norm_ofTestFunction_ne_top hα hα' hφ
  have hvcone : u + P ∈ nonnegCone α := by
    rw [mem_nonnegCone, toLp_add]
    exact add_nonneg hu hPcone
  have hvfin : l1Norm (u + P) ≠ ⊤ := by
    rw [l1Norm_add hu hPcone]
    exact ENNReal.add_ne_top.2 ⟨hufin, hPfin⟩
  have hvar := variational_inequality hf hu hufin hmin hvcone hvfin
  have hl1 : (l1Norm (u + P)).toReal - (l1Norm u).toReal = ∫ x, φ x := by
    rw [l1Norm_add hu hPcone, ENNReal.toReal_add hufin hPfin, hP,
      l1Norm_ofTestFunction hα hα' hφ hφ0, ENNReal.toReal_ofReal (integral_nonneg hφ0)]
    ring
  have hint : ∫ x, f x * (⇑(u + P) x - ⇑u x) = ∫ x, f x * φ x := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_add_ae u P, hP ▸ coeFn_ofTestFunction hα hα' hφ] with x h₁ h₂
    rw [h₁, h₂]
    ring
  rw [add_sub_cancel_left u P, hl1, hint] at hvar
  linarith [hvar]

/-! ### The competitor argument -/

/-- The elementary inequality behind the competitor argument: if `c² ≤ a b` with `a`, `b`
nonnegative and `t ≥ 0`, then `b − t c ≥ −t² a / 4`, since `(√b − t √a / 2)² ≥ 0`. -/
theorem le_sub_mul_of_sq_le_mul {a b c t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ^ 2 ≤ a * b)
    (ht : 0 ≤ t) : -(t ^ 2 * a / 4) ≤ b - t * c := by
  have h₁ : c ≤ √a * √b := by
    rcases le_or_gt c 0 with h | h
    · exact h.trans (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    · rw [← Real.sqrt_mul ha]
      calc c = √(c ^ 2) := (Real.sqrt_sq h.le).symm
        _ ≤ √(a * b) := Real.sqrt_le_sqrt hc
  nlinarith [sq_nonneg (√b - t * √a / 2), Real.sq_sqrt ha, Real.sq_sqrt hb,
    mul_le_mul_of_nonneg_left h₁ ht]

/-- **The competitor argument**: for `t > 0` the competitor `u − min(u, tφ)` is admissible, and
with `w = (tφ − u)₊` the truncation inequality `E(w, w) ≤ E(tφ − u, w)` and Cauchy–Schwarz give
`t E(u, φ) − t²/4 E(φ, φ) ≤ t ∫ f φ`. Dividing by `t` and letting `t → 0⁺` is the distributional
upper bound `L u ≤ f`. -/
theorem jumpForm_le_integral_mul_of_isTestFunction (hα : 0 < α) (hα' : α < 2) (hκ : 0 ≤ κ)
    (hf : MemLp f 2 volume) (hf0 : ∀ x, 0 ≤ f x) {u : EnergySpace α} (hu : u ∈ nonnegCone α)
    (hufin : l1Norm u ≠ ⊤)
    (hmin : ∀ v ∈ nonnegCone α, l1Norm v ≠ ⊤ → obstacleFun α κ f u ≤ obstacleFun α κ f v)
    (hφ : IsTestFunction φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    jumpForm α ⇑u ⇑(ofTestFunction hα hα' hφ) ≤ ∫ x, f x * φ x := by
  set P := ofTestFunction hα hα' hφ with hP
  have hPae : ⇑P =ᵐ[volume] φ := hP ▸ coeFn_ofTestFunction hα hα' hφ
  have hfP : Integrable (fun x => f x * φ x) volume :=
    hf.integrable_mul (memLp_two_of_isTestFunction hφ)
  -- for every `t > 0` the competitor argument gives a quadratic bound
  have hmain : ∀ t : ℝ, 0 < t →
      t * (jumpForm α ⇑u ⇑P - ∫ x, f x * φ x) ≤ t ^ 2 / 4 * jumpForm α ⇑P ⇑P := by
    intro t ht
    obtain ⟨d, hd⟩ : ∃ z, z = EnergySpace.inf u (t • P) := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ z, z = EnergySpace.posPart (t • P - u) := ⟨_, rfl⟩
    have htP : ⇑(t • P) =ᵐ[volume] fun x => t * φ x := by
      filter_upwards [coeFn_smul_ae t P, hPae] with x h₁ h₂
      rw [h₁, h₂]
    have hdae : ⇑d =ᵐ[volume] fun x => min (u x) (t * φ x) := by
      filter_upwards [hd ▸ coeFn_inf u (t • P), htP] with x h₁ h₂
      rw [h₁, h₂]
    have hwae : ⇑w =ᵐ[volume] fun x => max (t * φ x - u x) 0 := by
      filter_upwards [hw ▸ EnergySpace.coeFn_posPart (t • P - u), coeFn_sub_ae (t • P) u, htP]
        with x h₁ h₂ h₃
      rw [h₁]
      simp only [CenteredMaximal.posPart, h₂, h₃]
    -- the splitting `min (u, tφ) = tφ − (tφ − u)₊`
    have hdw : d = t • P - w := by
      refine eq_of_coeFn_ae ?_
      filter_upwards [hdae, coeFn_sub_ae (t • P) w, htP, hwae] with x h₁ h₂ h₃ h₄
      rw [h₁, h₂, h₃, h₄]
      rcases le_total (u x) (t * φ x) with h | h
      · rw [min_eq_left h, max_eq_left (by linarith)]
        ring
      · rw [min_eq_right h, max_eq_right (by linarith)]
        ring
    have hdcone : d ∈ nonnegCone α := by
      rw [mem_nonnegCone_iff_ae]
      filter_upwards [hdae, nonneg_ae_of_mem_nonnegCone hu] with x h₁ h₂
      rw [Pi.zero_apply, h₁]
      exact le_min h₂ (mul_nonneg ht.le (hφ0 x))
    have hdleu : ∀ᵐ x ∂volume, ⇑d x ≤ ⇑u x := by
      filter_upwards [hdae] with x h₁
      rw [h₁]
      exact min_le_left _ _
    have hdfin : l1Norm d ≠ ⊤ := ne_top_of_le_ne_top hufin
      (l1Norm_le_of_ae_le (nonneg_ae_of_mem_nonnegCone hdcone) hdleu)
    have hudcone : u - d ∈ nonnegCone α := by
      rw [mem_nonnegCone_iff_ae]
      filter_upwards [coeFn_sub_ae u d, hdleu] with x h₁ h₂
      rw [Pi.zero_apply, h₁]
      linarith
    have hudfin : l1Norm (u - d) ≠ ⊤ := by
      refine ne_top_of_le_ne_top hufin
        (l1Norm_le_of_ae_le (nonneg_ae_of_mem_nonnegCone hudcone) ?_)
      filter_upwards [coeFn_sub_ae u d, nonneg_ae_of_mem_nonnegCone hdcone] with x h₁ h₂
      rw [h₁]
      linarith
    -- (a) the variational inequality for the competitor `u − d`
    have hvar := variational_inequality hf hu hufin hmin hudcone hudfin
    have hsum : (l1Norm (u - d)).toReal - (l1Norm u).toReal = -(l1Norm d).toReal := by
      have h : l1Norm u = l1Norm (u - d) + l1Norm d := by
        rw [← l1Norm_add hudcone hdcone, sub_add_cancel]
      rw [h, ENNReal.toReal_add hudfin hdfin]
      ring
    have hintd : ∫ x, f x * (⇑(u - d) x - ⇑u x) = -∫ x, f x * ⇑d x := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_sub_ae u d] with x hx
      rw [hx]
      ring
    rw [show u - d - u = -d by abel, jumpForm_coeFn_neg_right, hsum, hintd] at hvar
    -- (b) and (c) the truncation inequality and Cauchy–Schwarz
    have hbc : jumpForm α ⇑w ⇑w ≤ t * jumpForm α ⇑P ⇑w - jumpForm α ⇑u ⇑w := by
      have h := EnergySpace.jumpForm_posPart_self_le (t • P - u)
      rw [← hw] at h
      rwa [jumpForm_coeFn_sub_left, jumpForm_coeFn_smul_left] at h
    have hud : jumpForm α ⇑u ⇑d = t * jumpForm α ⇑u ⇑P - jumpForm α ⇑u ⇑w := by
      rw [hdw, jumpForm_coeFn_sub_right, jumpForm_coeFn_smul_right]
    have hcs : jumpForm α ⇑P ⇑w ^ 2 ≤ jumpForm α ⇑P ⇑P * jumpForm α ⇑w ⇑w :=
      jumpForm_sq_le_of_aemeasurable α (Lp.aestronglyMeasurable (P : L²)).aemeasurable
        (Lp.aestronglyMeasurable (w : L²)).aemeasurable P.jumpEnergy_ne_top w.jumpEnergy_ne_top
    have hlow := le_sub_mul_of_sq_le_mul (jumpForm_self_nonneg α ⇑P)
      (jumpForm_self_nonneg α ⇑w) hcs ht.le
    -- (d) the source term is controlled by `t ∫ f φ`
    have hfdle : ∫ x, f x * ⇑d x ≤ t * ∫ x, f x * φ x := by
      rw [← integral_const_mul]
      refine integral_mono_ae (hf.integrable_mul (Lp.memLp (d : L²))) (hfP.const_mul t) ?_
      filter_upwards [hdae] with x hx
      calc f x * ⇑d x ≤ f x * (t * φ x) :=
            mul_le_mul_of_nonneg_left (hx ▸ min_le_right _ _) (hf0 x)
        _ = t * (f x * φ x) := by ring
    have hκd : 0 ≤ κ * (l1Norm d).toReal := mul_nonneg hκ ENNReal.toReal_nonneg
    linarith [hvar, hbc, hud, hlow, hfdle, hκd]
  -- let `t` tend to zero
  by_contra hcon
  have hδ : 0 < jumpForm α ⇑u ⇑P - ∫ x, f x * φ x := sub_pos.2 (not_le.1 hcon)
  have hden : (0 : ℝ) < jumpForm α ⇑P ⇑P + 1 := by linarith [jumpForm_self_nonneg α ⇑P]
  obtain ⟨t, hti⟩ : ∃ z : ℝ, z = 2 * (jumpForm α ⇑u ⇑P - ∫ x, f x * φ x) /
    (jumpForm α ⇑P ⇑P + 1) := ⟨_, rfl⟩
  have ht : 0 < t := hti ▸ div_pos (by linarith) hden
  have hteq : t * (jumpForm α ⇑P ⇑P + 1) = 2 * (jumpForm α ⇑u ⇑P - ∫ x, f x * φ x) := by
    rw [hti]
    field_simp
  nlinarith [hmain t ht, ht, hδ, congrArg (fun z : ℝ => t * z) hteq, sq_nonneg t,
    mul_pos ht hδ]

/-! ### The capped density -/

/-- The jump form against a test function only sees its almost everywhere class. -/
theorem jumpForm_coeFn_ofTestFunction (hα : 0 < α) (hα' : α < 2) (hφ : IsTestFunction φ)
    (v : EnergySpace α) : jumpForm α ⇑v ⇑(ofTestFunction hα hα' hφ) = jumpForm α ⇑v φ :=
  jumpForm_congr_ae α Filter.EventuallyEq.rfl (coeFn_ofTestFunction hα hα' hφ)

/-- **The functional `T φ = ∫ f φ − E(u, φ)` is positive and bounded by `κ ∫ φ`**: additivity and
homogeneity are the bilinearity of the jump form and linearity of the integral, positivity is the
competitor argument and the bound is the positive variation. -/
theorem isBoundedPositiveFunctional_source_sub_jumpForm (hα : 0 < α) (hα' : α < 2) (hκ : 0 ≤ κ)
    (hf : MemLp f 2 volume) (hf0 : ∀ x, 0 ≤ f x) {u : EnergySpace α} (hu : u ∈ nonnegCone α)
    (hufin : l1Norm u ≠ ⊤)
    (hmin : ∀ v ∈ nonnegCone α, l1Norm v ≠ ⊤ → obstacleFun α κ f u ≤ obstacleFun α κ f v) :
    IsBoundedPositiveFunctional volume (fun φ => (∫ x, f x * φ x) - jumpForm α ⇑u φ) κ where
  map_add φ ψ hφ hψ := by
    have hiφ : Integrable (fun x => f x * φ x) volume :=
      hf.integrable_mul (memLp_two_of_isTestFunction hφ)
    have hiψ : Integrable (fun x => f x * ψ x) volume :=
      hf.integrable_mul (memLp_two_of_isTestFunction hψ)
    have h₁ : ∫ x, f x * (φ + ψ) x = (∫ x, f x * φ x) + ∫ x, f x * ψ x := by
      rw [← integral_add hiφ hiψ]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [Pi.add_apply]
      ring
    show (∫ x, f x * (φ + ψ) x) - jumpForm α ⇑u (φ + ψ) =
      ((∫ x, f x * φ x) - jumpForm α ⇑u φ) + ((∫ x, f x * ψ x) - jumpForm α ⇑u ψ)
    rw [h₁, jumpForm_add_right α (measurable_coeFn u) hφ.continuous.measurable
      hψ.continuous.measurable u.jumpEnergy_ne_top
      (jumpEnergy_ne_top_of_isTestFunction hα hα' hφ)
      (jumpEnergy_ne_top_of_isTestFunction hα hα' hψ)]
    ring
  map_smul c φ hφ := by
    have h₁ : ∫ x, f x * (c • φ) x = c * ∫ x, f x * φ x := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    show (∫ x, f x * (c • φ) x) - jumpForm α ⇑u (c • φ) =
      c * ((∫ x, f x * φ x) - jumpForm α ⇑u φ)
    rw [h₁, jumpForm_smul_right]
    ring
  map_nonneg φ hφ hφ0 := by
    show 0 ≤ (∫ x, f x * φ x) - jumpForm α ⇑u φ
    rw [sub_nonneg, ← jumpForm_coeFn_ofTestFunction hα hα' hφ]
    exact jumpForm_le_integral_mul_of_isTestFunction hα hα' hκ hf hf0 hu hufin hmin hφ hφ0
  map_le φ hφ hφ0 := by
    have h := jumpForm_add_le_of_isTestFunction hα hα' hf hu hufin hmin hφ hφ0
    rw [jumpForm_coeFn_ofTestFunction hα hα' hφ] at h
    show (∫ x, f x * φ x) - jumpForm α ⇑u φ ≤ κ * ∫ x, φ x
    linarith [h]

/-- **The capped density**: the distribution `σ = f − L u` of a minimiser of the obstacle
functional is represented by a measurable function with values in `[0, κ]`, by the
Riesz–Markov–Kakutani and Radon–Nikodym theorems of
`CenteredMaximal.Analysis.BoundedFunctional`. -/
theorem exists_density (hα : 0 < α) (hα' : α < 2) (hκ : 0 ≤ κ) (hf : MemLp f 2 volume)
    (hf0 : ∀ x, 0 ≤ f x) {u : EnergySpace α} (hu : u ∈ nonnegCone α) (hufin : l1Norm u ≠ ⊤)
    (hmin : ∀ v ∈ nonnegCone α, l1Norm v ≠ ⊤ → obstacleFun α κ f u ≤ obstacleFun α κ f v) :
    ∃ σ : (Fin 2 → ℝ) → ℝ, Measurable σ ∧ (∀ x, 0 ≤ σ x) ∧ (∀ x, σ x ≤ κ) ∧
      ∀ (φ : (Fin 2 → ℝ) → ℝ) (hφ : IsTestFunction φ), ∫ x, σ x * φ x =
        (∫ x, f x * φ x) - jumpForm α ⇑u ⇑(ofTestFunction hα hα' hφ) := by
  obtain ⟨σ, hσm, hσ, hσT⟩ := (isBoundedPositiveFunctional_source_sub_jumpForm
    hα hα' hκ hf hf0 hu hufin hmin).exists_density
  refine ⟨σ, hσm, fun x => (hσ x).1, fun x => (hσ x).2, fun φ hφ => ?_⟩
  rw [jumpForm_coeFn_ofTestFunction hα hα' hφ]
  exact (hσT φ hφ).symm

end CenteredMaximal
