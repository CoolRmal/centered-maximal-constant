/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.EnergySpace
public import CenteredMaximal.Analysis.Gagliardo
public import CenteredMaximal.Analysis.WeakCompact
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# The obstacle functional and the existence of a minimiser

Fix `α κ : ℝ` with `0 < α` and `0 < κ`, and an obstacle `f : ℝ² → ℝ` which is measurable,
nonnegative, bounded by `Mf` and supported in the cube `Q(0, b)`. The obstacle functional on the
energy space `H_α` of `CenteredMaximal.Analysis.EnergySpace` is
`Φ(u) = ½ E(u, u) + κ ‖u‖₁ − ∫ f u`, and this file proves that `Φ` attains its minimum on the set
of nonnegative elements of `H_α` of finite `L¹` norm.

* `l1Norm`: the `L¹` norm as an element of `[0, ∞]`, with `l1Norm_congr`, `l1Norm_add` (additivity
  on the positive cone), `l1Norm_smul` and `l1Norm_eq_iSup`: it is the increasing limit of the
  local `L¹` norms over the cubes `Q(0, n)` (monotone convergence);
* `ballFunctional`: the continuous linear functional `u ↦ ∫_{Q(0,n)} u`; on the positive cone the
  local `L¹` norm is its `ENNReal.ofReal` (`setLIntegral_enorm_eq_ofReal`), so that
  `l1Norm_eq_iSup_ballFunctional` exhibits `l1Norm` as a supremum of weakly continuous functions
  and `lowerSemicontinuousOn_l1Norm` gives weak lower semicontinuity on the cone;
* `convexOn_jumpForm_self`, `continuous_jumpForm_self`: the quadratic form `u ↦ E(u, u)` is convex
  — by the expansion `E(au + bv) = a² E(u) + 2ab E(u,v) + b² E(v)` and `E(u − v) ≥ 0` — and
  continuous, hence weakly lower semicontinuous;
* `sourceFunctional`: the continuous linear functional `u ↦ ∫ f u`, using `memLp_two_of_bounded`;
* `obstacleFun`, `admissible`: the functional and the admissible sets, with
  `exists_admissible_of_obstacleFun_nonpos`: **coercivity**, the sublevel set `{Φ ≤ 0}` of the cone
  is admissible for explicit constants, by the local `L¹` bound of
  `CenteredMaximal.Analysis.Gagliardo` and Young's inequality (`coercivity_real`);
* `convex_admissible`, `isClosed_admissible`, `isBounded_admissible`,
  `isCompact_toWeakSpace_image_admissible`: the admissible sets are weakly compact;
* `exists_isMinOn_admissible`, `exists_isMinOn_nonnegCone`: the **direct method**, and the removal
  of the artificial constraints by coercivity.
-/

@[expose] public section

noncomputable section

open Bornology MeasureTheory Metric Set
open scoped ENNReal RealInnerProductSpace

namespace CenteredMaximal

/-- `L²(ℝ²)` with respect to Lebesgue measure. -/
local notation "L²" => Lp ℝ 2 (volume : Measure (Fin 2 → ℝ))

open EnergySpace

/-! ### The functional and the admissible sets -/

/-- The `L¹` norm of an energy-space element, as an element of `[0, ∞]`. -/
def l1Norm {α : ℝ} (u : EnergySpace α) : ℝ≥0∞ := ∫⁻ x, ‖u x‖ₑ

/-- The obstacle functional `½ E(u,u) + κ‖u‖₁ − ∫ f u`; meaningful only when `l1Norm u ≠ ⊤`. -/
def obstacleFun (α κ : ℝ) (f : (Fin 2 → ℝ) → ℝ) (u : EnergySpace α) : ℝ :=
  jumpForm α u u / 2 + κ * (l1Norm u).toReal - ∫ x, f x * u x

/-- The admissible set: nonnegative, `L¹` norm at most `L`, energy at most `E₀`. -/
def admissible (α : ℝ) (L E₀ : ℝ) : Set (EnergySpace α) :=
  {u | u ∈ nonnegCone α ∧ l1Norm u ≤ ENNReal.ofReal L ∧ jumpForm α u u ≤ E₀}

variable {α κ : ℝ} {f : (Fin 2 → ℝ) → ℝ}

/-- The function underlying an element of the energy space is measurable. -/
theorem measurable_coeFn (u : EnergySpace α) : Measurable ⇑u :=
  (Lp.stronglyMeasurable (u : L²)).measurable

/-- The zero of the energy space is almost everywhere zero. -/
theorem coeFn_zero_ae (α : ℝ) : ⇑(0 : EnergySpace α) =ᵐ[volume] (0 : (Fin 2 → ℝ) → ℝ) :=
  Lp.coeFn_zero ℝ 2 (volume : Measure (Fin 2 → ℝ))

/-- Elements of the positive cone are almost everywhere nonnegative. -/
theorem nonneg_ae_of_mem_nonnegCone {u : EnergySpace α} (hu : u ∈ nonnegCone α) :
    ∀ᵐ x ∂volume, 0 ≤ u x := by
  filter_upwards [mem_nonnegCone_iff_ae.1 hu] with x hx using hx

/-! ### The `L¹` norm -/

/-- The `L¹` norm only depends on the almost everywhere class. -/
theorem l1Norm_congr {u v : EnergySpace α} (h : ⇑u =ᵐ[volume] ⇑v) : l1Norm u = l1Norm v :=
  lintegral_congr_ae (h.mono fun _ hx => by simp only [hx])

/-- The `L¹` norm is additive on the positive cone. -/
theorem l1Norm_add {u v : EnergySpace α} (hu : u ∈ nonnegCone α) (hv : v ∈ nonnegCone α) :
    l1Norm (u + v) = l1Norm u + l1Norm v := by
  simp only [l1Norm]
  rw [← lintegral_add_left (measurable_coeFn u).enorm fun x => ‖v x‖ₑ]
  refine lintegral_congr_ae ?_
  filter_upwards [Lp.coeFn_add (u : L²) (v : L²), nonneg_ae_of_mem_nonnegCone hu,
    nonneg_ae_of_mem_nonnegCone hv] with x hx hu' hv'
  rw [show ⇑(u + v) x = ⇑u x + ⇑v x from hx, Real.enorm_eq_ofReal_abs,
    Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_nonneg hu', abs_of_nonneg hv',
    abs_of_nonneg (add_nonneg hu' hv'), ENNReal.ofReal_add hu' hv']

/-- The `L¹` norm is homogeneous for nonnegative scalars. -/
theorem l1Norm_smul {c : ℝ} (hc : 0 ≤ c) (u : EnergySpace α) :
    l1Norm (c • u) = ENNReal.ofReal c * l1Norm u := by
  simp only [l1Norm]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c (u : L²)] with x hx
  rw [show ⇑(c • u) x = c * ⇑u x from hx, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
    abs_mul, abs_of_nonneg hc, ENNReal.ofReal_mul hc]

/-- The `L¹` norm of zero vanishes. -/
@[simp]
theorem l1Norm_zero : l1Norm (0 : EnergySpace α) = 0 := by
  have h : l1Norm (0 : EnergySpace α) = ∫⁻ _ : Fin 2 → ℝ, (0 : ℝ≥0∞) :=
    lintegral_congr_ae ((coeFn_zero_ae α).mono fun _ hx => by
      simp only [hx, Pi.zero_apply, enorm_zero])
  rw [h, lintegral_zero]

/-- **Monotone convergence**: the `L¹` norm is the increasing limit of the local `L¹` norms over
the cubes `Q(0, n)`. -/
theorem l1Norm_eq_iSup (u : EnergySpace α) :
    l1Norm u = ⨆ n : ℕ, ∫⁻ x in closedBall (0 : Fin 2 → ℝ) n, ‖u x‖ₑ := by
  have hmeas : ∀ n : ℕ,
      Measurable ((closedBall (0 : Fin 2 → ℝ) n).indicator fun x => ‖u x‖ₑ) :=
    fun _ => (measurable_coeFn u).enorm.indicator measurableSet_closedBall
  have hmono : Monotone fun n : ℕ =>
      (closedBall (0 : Fin 2 → ℝ) n).indicator fun x => ‖u x‖ₑ := by
    intro m n hmn x
    exact indicator_le_indicator_of_subset
      (closedBall_subset_closedBall (by exact_mod_cast hmn)) (fun _ => zero_le) x
  calc l1Norm u
      = ∫⁻ x, ⨆ n : ℕ, (closedBall (0 : Fin 2 → ℝ) n).indicator (fun x => ‖u x‖ₑ) x := by
        refine lintegral_congr fun x => ?_
        obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
        refine le_antisymm (le_iSup_of_le n ?_) (iSup_le fun _ => indicator_le_self _ _ x)
        rw [indicator_of_mem (by simpa [mem_closedBall, dist_eq_norm] using hn)]
    _ = ⨆ n : ℕ, ∫⁻ x, (closedBall (0 : Fin 2 → ℝ) n).indicator (fun x => ‖u x‖ₑ) x :=
        lintegral_iSup hmeas hmono
    _ = _ := iSup_congr fun _ => lintegral_indicator measurableSet_closedBall _

/-! ### The local `L¹` norms as continuous linear functionals -/

/-- The cube `Q(0, r)` has finite volume. -/
theorem volume_closedBall_ne_top {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall (0 : Fin 2 → ℝ) r) ≠ ⊤ := by
  rw [volume_closedBall_eq _ hr]
  exact ENNReal.ofReal_ne_top

/-- The local `L¹` norm of an element of the energy space over a cube is finite. -/
theorem setLIntegral_enorm_ne_top (u : EnergySpace α) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ x in closedBall (0 : Fin 2 → ℝ) r, ‖u x‖ₑ ≠ ⊤ := by
  have : IsFiniteMeasure (volume.restrict (closedBall (0 : Fin 2 → ℝ) r)) :=
    isFiniteMeasure_restrict.2 (volume_closedBall_ne_top hr)
  exact (hasFiniteIntegral_iff_enorm.1
    (((Lp.memLp (u : L²)).restrict _).integrable one_le_two).2).ne

/-- On the positive cone the local `L¹` norm over a cube is the integral of the function. -/
theorem setLIntegral_enorm_eq_ofReal {u : EnergySpace α} (hu : u ∈ nonnegCone α) {r : ℝ}
    (hr : 0 ≤ r) : ∫⁻ x in closedBall (0 : Fin 2 → ℝ) r, ‖u x‖ₑ =
      ENNReal.ofReal (∫ x in closedBall (0 : Fin 2 → ℝ) r, u x) := by
  have h1 : ∫ x in closedBall (0 : Fin 2 → ℝ) r, u x
      = ∫ x in closedBall (0 : Fin 2 → ℝ) r, ‖u x‖ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (nonneg_ae_of_mem_nonnegCone hu)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
  rw [h1, integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable (u : L²)).restrict,
    ENNReal.ofReal_toReal (setLIntegral_enorm_ne_top u hr)]

/-- The continuous linear functional `u ↦ ∫_{Q(0,n)} u` on the energy space. -/
def ballFunctional (α : ℝ) (n : ℕ) : EnergySpace α →L[ℝ] ℝ :=
  (innerSL ℝ (indicatorConstLp 2 measurableSet_closedBall
    (volume_closedBall_ne_top (r := (n : ℝ)) (Nat.cast_nonneg n)) (1 : ℝ))).comp (toLpCLM α)

/-- The functional `ballFunctional α n` is the integral over the cube `Q(0, n)`. -/
theorem ballFunctional_apply (α : ℝ) (n : ℕ) (u : EnergySpace α) :
    ballFunctional α n u = ∫ x in closedBall (0 : Fin 2 → ℝ) n, u x :=
  L2.inner_indicatorConstLp_one measurableSet_closedBall _ (u : L²)

/-- On the positive cone the `L¹` norm is a supremum of continuous linear functionals. -/
theorem l1Norm_eq_iSup_ballFunctional {u : EnergySpace α} (hu : u ∈ nonnegCone α) :
    l1Norm u = ⨆ n : ℕ, ENNReal.ofReal (ballFunctional α n u) := by
  rw [l1Norm_eq_iSup]
  refine iSup_congr fun n => ?_
  rw [setLIntegral_enorm_eq_ofReal hu (Nat.cast_nonneg n), ballFunctional_apply]

/-- Each local `L¹` norm is weakly continuous as an `ℝ≥0∞`-valued function. -/
theorem continuous_ofReal_ballFunctional (α : ℝ) (n : ℕ) :
    Continuous ((fun u : EnergySpace α => ENNReal.ofReal (ballFunctional α n u)) ∘
      (toWeakSpace ℝ (EnergySpace α)).symm) :=
  ENNReal.continuous_ofReal.comp (ballFunctional α n).continuous_comp_toWeakSpace_symm

/-! ### Lower semicontinuity of the `L¹` norm -/

/-- A function that agrees on a set with a lower semicontinuous function is lower semicontinuous
on that set. -/
theorem lowerSemicontinuousOn_of_eqOn {X β : Type*} [TopologicalSpace X] [Preorder β]
    {g h : X → β} {s : Set X} (hh : LowerSemicontinuous h) (hgh : EqOn g h s) :
    LowerSemicontinuousOn g s := by
  intro x hx y hy
  rw [hgh hx] at hy
  filter_upwards [(hh x y hy).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x' h1 h2
  rwa [hgh h2]

/-- The `L¹` norm is weakly lower semicontinuous on every subset of the positive cone. -/
theorem lowerSemicontinuousOn_l1Norm {K : Set (EnergySpace α)} (hK : K ⊆ nonnegCone α) :
    LowerSemicontinuousOn (l1Norm ∘ (toWeakSpace ℝ (EnergySpace α)).symm)
      (toWeakSpace ℝ (EnergySpace α) '' K) := by
  refine lowerSemicontinuousOn_of_eqOn (lowerSemicontinuous_iSup_comp_toWeakSpace_symm
    (F := fun (n : ℕ) (u : EnergySpace α) => ENNReal.ofReal (ballFunctional α n u))
    (continuous_ofReal_ballFunctional α)) ?_
  rintro w ⟨v, hv, rfl⟩
  simp only [Function.comp_apply, LinearEquiv.symm_apply_apply]
  exact l1Norm_eq_iSup_ballFunctional (hK hv)

/-- Multiplying the real part of a finite lower semicontinuous `ℝ≥0∞`-valued function by a
nonnegative constant preserves lower semicontinuity. -/
theorem lowerSemicontinuousOn_const_mul_toReal {X : Type*} [TopologicalSpace X] {g : X → ℝ≥0∞}
    {s : Set X} (hg : LowerSemicontinuousOn g s) (hfin : ∀ x ∈ s, g x ≠ ⊤) {c : ℝ} (hc : 0 ≤ c) :
    LowerSemicontinuousOn (fun x => c * (g x).toReal) s := by
  intro x hx y hy
  have hy' : y < c * (g x).toReal := hy
  rcases lt_or_ge y 0 with hy0 | hy0
  · filter_upwards [self_mem_nhdsWithin] with x' _
    exact hy0.trans_le (mul_nonneg hc ENNReal.toReal_nonneg)
  · have hc' : 0 < c := by
      rcases hc.lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at hy'
        linarith
    have h1 : ENNReal.ofReal (y / c) < g x := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal (div_nonneg hy0 hc) (hfin x hx), div_lt_iff₀ hc',
        mul_comm]
      exact hy'
    filter_upwards [hg x hx _ h1, self_mem_nhdsWithin] with x' h2 h3
    have h2' : ENNReal.ofReal (y / c) < g x' := h2
    rw [ENNReal.ofReal_lt_iff_lt_toReal (div_nonneg hy0 hc) (hfin x' h3), div_lt_iff₀ hc',
      mul_comm] at h2'
    exact h2'

/-! ### The quadratic form -/

/-- The quadratic expansion `E(au + bv) = a² E(u,u) + 2ab E(u,v) + b² E(v,v)`. -/
theorem jumpForm_smul_add_smul (a b : ℝ) (u v : EnergySpace α) :
    jumpForm α ⇑(a • u + b • v) ⇑(a • u + b • v) =
      a ^ 2 * jumpForm α u u + 2 * (a * b) * jumpForm α u v + b ^ 2 * jumpForm α v v := by
  rw [jumpForm_eq (a • u + b • v) (a • u + b • v), jumpForm_eq u u, jumpForm_eq u v,
    jumpForm_eq v v]
  simp only [toLp_add, toLp_smul, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm (v : L²) (u : L²), real_inner_comm v u]
  ring

/-- The jump form on the diagonal is convex: the difference
`a E(u,u) + b E(v,v) − E(au + bv)` equals `ab E(u − v, u − v) ≥ 0`. -/
theorem convexOn_jumpForm_self (α : ℝ) :
    ConvexOn ℝ univ fun u : EnergySpace α => jumpForm α u u := by
  refine ⟨convex_univ, fun u _ v _ a b ha hb hab => ?_⟩
  have h0 : 0 ≤ jumpForm α ⇑((1 : ℝ) • u + (-1 : ℝ) • v) ⇑((1 : ℝ) • u + (-1 : ℝ) • v) :=
    jumpForm_self_nonneg α _
  rw [jumpForm_smul_add_smul (α := α) 1 (-1) u v] at h0
  simp only [smul_eq_mul]
  rw [jumpForm_smul_add_smul a b u v]
  have hab' : b = 1 - a := by linarith
  subst hab'
  nlinarith [mul_nonneg ha hb, h0]

/-- The jump form on the diagonal is continuous: it is the difference of the squares of the energy
norm and the `L²` norm. -/
theorem continuous_jumpForm_self (α : ℝ) :
    Continuous fun u : EnergySpace α => jumpForm α u u := by
  have h : (fun u : EnergySpace α => jumpForm α u u)
      = fun u : EnergySpace α => ‖u‖ ^ 2 - ‖(u : L²)‖ ^ 2 := by
    funext u
    rw [norm_sq_eq]
    ring
  rw [h]
  exact (continuous_norm.pow 2).sub ((toLpCLM α).continuous.norm.pow 2)

/-- The jump form of zero vanishes. -/
@[simp]
theorem jumpForm_self_zero (α : ℝ) :
    jumpForm α ⇑(0 : EnergySpace α) ⇑(0 : EnergySpace α) = 0 := by
  rw [jumpForm_congr_ae α (coeFn_zero_ae α) (coeFn_zero_ae α)]
  simp [jumpForm]

/-- The squared `L²` norm as a lower Lebesgue integral. -/
theorem norm_toLp_sq_eq (u : EnergySpace α) :
    ‖(u : L²)‖ ^ 2 = (∫⁻ x, ENNReal.ofReal (u x ^ 2)).toReal := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [Real.inner_apply]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => mul_self_nonneg (⇑u x))
    ((Lp.aestronglyMeasurable (u : L²)).mul (Lp.aestronglyMeasurable (u : L²)))]
  simp only [← pow_two]

/-! ### The source term -/

/-- A bounded measurable function supported in a cube lies in `L²`. -/
theorem memLp_two_of_bounded (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {Mf : ℝ}
    (hfM : ∀ x, f x ≤ Mf) {b : ℝ} (hfb : ∀ x, b < ‖x‖ → f x = 0) : MemLp f 2 volume := by
  refine (HasCompactSupport.intro (isCompact_closedBall (0 : Fin 2 → ℝ) b) fun x hx =>
      hfb x (by simpa [mem_closedBall, dist_eq_norm] using hx)).memLp_of_bound
    hf.aestronglyMeasurable Mf (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
  exact hfM x

/-- The continuous linear functional `u ↦ ∫ f u` on the energy space. -/
def sourceFunctional (α : ℝ) {f : (Fin 2 → ℝ) → ℝ} (hf : MemLp f 2 volume) :
    EnergySpace α →L[ℝ] ℝ :=
  (innerSL ℝ (hf.toLp f)).comp (toLpCLM α)

/-- The functional `sourceFunctional` is the pairing with the obstacle. -/
theorem sourceFunctional_apply (α : ℝ) (hf : MemLp f 2 volume) (u : EnergySpace α) :
    sourceFunctional α hf u = ∫ x, f x * u x := by
  have h : sourceFunctional α hf u = ⟪(hf.toLp f : L²), (u : L²)⟫ := rfl
  rw [h, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [Real.inner_apply, hx]

/-- Pulling a nonnegative real factor of `2` out of a product in `[0, ∞]`. -/
theorem ofReal_two_mul_mul {p : ℝ} (hp : 0 ≤ p) (q : ℝ) :
    2 * ENNReal.ofReal p * ENNReal.ofReal q = ENNReal.ofReal (2 * p * q) := by
  rw [ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 2 * p),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

/-! ### Coercivity -/

/-- The real form of the local `L¹` bound of `CenteredMaximal.Analysis.Gagliardo` on the positive
cone: the square of the local `L¹` norm over `Q(0, b)` is controlled by the energy plus a small
multiple of the square of the `L¹` norm. -/
theorem sq_setIntegral_le_of_mem_nonnegCone (hα : 0 < α) {u : EnergySpace α}
    (hu : u ∈ nonnegCone α) (hufin : l1Norm u ≠ ⊤) {b R : ℝ} (hb : 0 < b) (hbR : b ≤ R) :
    (∫ x in closedBall (0 : Fin 2 → ℝ) b, u x) ^ 2 ≤
      2 * ((2 * b) ^ 2 * (2 * R) ^ (2 + α) / (2 * R) ^ 2) * (4 * (2 + α) / (1 + α)) *
          jumpForm α u u + 2 * (b / R) ^ 4 * (l1Norm u).toReal ^ 2 := by
  have hR0 : 0 < R := hb.trans_le hbR
  have hC0 : (0 : ℝ) ≤ (2 * b) ^ 2 * (2 * R) ^ (2 + α) / (2 * R) ^ 2 := by positivity
  have hcα0 : (0 : ℝ) < 4 * (2 + α) / (1 + α) := div_pos (by linarith) (by linarith)
  have hρ0 : (0 : ℝ) ≤ (b / R) ^ 4 := by positivity
  have hJ0 : 0 ≤ jumpForm α u u := jumpForm_self_nonneg α _
  have hn0 : (0 : ℝ) ≤ (l1Norm u).toReal := ENNReal.toReal_nonneg
  have ha0 : (0 : ℝ) ≤ ∫ x in closedBall (0 : Fin 2 → ℝ) b, u x :=
    integral_nonneg_of_ae (ae_restrict_of_ae (nonneg_ae_of_mem_nonnegCone hu))
  have hG : gagliardo α ⇑u ≤ ENNReal.ofReal (4 * (2 + α) / (1 + α) * jumpForm α u u) := by
    refine (gagliardo_le_jumpEnergy (measurable_coeFn u) hα).trans ?_
    rw [jumpEnergy_eq u, ← ENNReal.ofReal_mul hcα0.le]
  have hN : (∫⁻ x, ‖u x‖ₑ) = ENNReal.ofReal (l1Norm u).toReal :=
    (ENNReal.ofReal_toReal hufin).symm
  have heq : 2 * ENNReal.ofReal ((2 * b) ^ 2 * (2 * R) ^ (2 + α) / (2 * R) ^ 2) *
        ENNReal.ofReal (4 * (2 + α) / (1 + α) * jumpForm α u u) +
        2 * ENNReal.ofReal ((b / R) ^ 4) * ENNReal.ofReal (l1Norm u).toReal ^ 2 =
      ENNReal.ofReal (2 * ((2 * b) ^ 2 * (2 * R) ^ (2 + α) / (2 * R) ^ 2) *
        (4 * (2 + α) / (1 + α)) * jumpForm α u u + 2 * (b / R) ^ 4 * (l1Norm u).toReal ^ 2) := by
    rw [← ENNReal.ofReal_pow hn0, ofReal_two_mul_mul hC0, ofReal_two_mul_mul hρ0,
      ← ENNReal.ofReal_add
        (mul_nonneg (by linarith) (mul_nonneg hcα0.le hJ0))
        (mul_nonneg (by linarith) (sq_nonneg _))]
    congr 1
    ring
  have hmain : ENNReal.ofReal ((∫ x in closedBall (0 : Fin 2 → ℝ) b, u x) ^ 2) ≤
      ENNReal.ofReal (2 * ((2 * b) ^ 2 * (2 * R) ^ (2 + α) / (2 * R) ^ 2) *
        (4 * (2 + α) / (1 + α)) * jumpForm α u u + 2 * (b / R) ^ 4 * (l1Norm u).toReal ^ 2) := by
    rw [← heq]
    calc ENNReal.ofReal ((∫ x in closedBall (0 : Fin 2 → ℝ) b, u x) ^ 2)
        = (∫⁻ x in closedBall (0 : Fin 2 → ℝ) b, ‖u x‖ₑ) ^ 2 := by
          rw [setLIntegral_enorm_eq_ofReal hu hb.le, ENNReal.ofReal_pow ha0]
      _ ≤ 2 * ENNReal.ofReal ((2 * b) ^ 2 * (2 * R) ^ (2 + α) / (2 * R) ^ 2) * gagliardo α ⇑u +
            2 * ENNReal.ofReal ((b / R) ^ 4) * (∫⁻ x, ‖u x‖ₑ) ^ 2 :=
          setLIntegral_enorm_closedBall_sq_le (measurable_coeFn u) hα.le hb hbR
      _ ≤ _ := by
          rw [hN]
          exact add_le_add (mul_le_mul_right hG _) le_rfl
  rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmain

/-- **Young's inequality** in the coercivity estimate: if the local `L¹` norm `a` obeys
`a² ≤ K J + 2 ε n²` with `ε = κ² / (8 (Mf + 1)²)`, and if `½ J + κ n ≤ fu ≤ Mf a`, then both `J`
and `n` are bounded in terms of `Mf² K`. -/
theorem coercivity_real {κ Mf K ε J n a fu : ℝ} (hκ : 0 < κ) (hMf : 0 ≤ Mf) (hK : 0 ≤ K)
    (hJ : 0 ≤ J) (hn : 0 ≤ n) (ha : 0 ≤ a) (hε : ε = κ ^ 2 / (8 * (Mf + 1) ^ 2))
    (hkey : a ^ 2 ≤ K * J + 2 * ε * n ^ 2) (hfu : fu ≤ Mf * a)
    (hobs : J / 2 + κ * n - fu ≤ 0) : J / 4 + κ / 2 * n ≤ Mf ^ 2 * K := by
  have hMf1 : (0 : ℝ) < Mf + 1 := by linarith
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hsqrt : √(2 * ε) = κ / (2 * (Mf + 1)) := by
    rw [show 2 * ε = (κ / (2 * (Mf + 1))) ^ 2 by rw [hε]; field_simp; ring]
    exact Real.sqrt_sq (div_nonneg hκ.le (by linarith))
  have hrhs : 0 ≤ √(K * J) + √(2 * ε) * n :=
    add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hn)
  have h1 : a ≤ √(K * J) + √(2 * ε) * n := by
    have hsq : a ^ 2 ≤ (√(K * J) + √(2 * ε) * n) ^ 2 := by
      have e1 : √(K * J) ^ 2 = K * J := Real.sq_sqrt (mul_nonneg hK hJ)
      have e2 : √(2 * ε) ^ 2 = 2 * ε := Real.sq_sqrt (by linarith)
      have e3 : (√(K * J) + √(2 * ε) * n) ^ 2
          = K * J + 2 * (√(K * J) * (√(2 * ε) * n)) + 2 * ε * n ^ 2 := by
        rw [add_sq, mul_pow, e1, e2]
        ring
      have h4 : 0 ≤ √(K * J) * (√(2 * ε) * n) :=
        mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hn)
      rw [e3]
      linarith
    calc a = √(a ^ 2) := (Real.sqrt_sq ha).symm
      _ ≤ √((√(K * J) + √(2 * ε) * n) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = _ := Real.sqrt_sq hrhs
  have h2 : Mf * √(K * J) ≤ J / 4 + Mf ^ 2 * K := by
    have e2 : √J ^ 2 = J := Real.sq_sqrt hJ
    have e3 : √K ^ 2 = K := Real.sq_sqrt hK
    rw [Real.sqrt_mul hK J]
    nlinarith [sq_nonneg (√J / 2 - Mf * √K), Real.sqrt_nonneg J, Real.sqrt_nonneg K]
  have h3 : Mf * (√(2 * ε) * n) ≤ κ / 2 * n := by
    rw [hsqrt, show Mf * (κ / (2 * (Mf + 1)) * n) = Mf / (Mf + 1) * (κ / 2) * n by
      field_simp]
    refine mul_le_mul_of_nonneg_right ?_ hn
    exact (mul_le_mul_of_nonneg_right ((div_le_one hMf1).2 (by linarith))
      (by linarith : (0 : ℝ) ≤ κ / 2)).trans_eq (one_mul _)
  nlinarith [mul_le_mul_of_nonneg_left h1 hMf, h2, h3, hfu, hobs]

/-- The pairing with the obstacle is bounded by `Mf` times the local `L¹` norm over `Q(0, b)`. -/
theorem integral_mul_le_of_mem_nonnegCone (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {Mf : ℝ}
    (hfM : ∀ x, f x ≤ Mf) {b : ℝ} (hb : 0 < b) (hfb : ∀ x, b < ‖x‖ → f x = 0)
    {u : EnergySpace α} (hu : u ∈ nonnegCone α) :
    ∫ x, f x * u x ≤ Mf * ∫ x in closedBall (0 : Fin 2 → ℝ) b, u x := by
  have hint : IntegrableOn (⇑u) (closedBall (0 : Fin 2 → ℝ) b) volume :=
    ⟨(Lp.aestronglyMeasurable (u : L²)).restrict, hasFiniteIntegral_iff_enorm.2
      (lt_top_iff_ne_top.2 (setLIntegral_enorm_ne_top u hb.le))⟩
  have hintM : IntegrableOn (fun x => Mf * u x) (closedBall (0 : Fin 2 → ℝ) b) volume :=
    hint.const_mul Mf
  have hg : Integrable ((closedBall (0 : Fin 2 → ℝ) b).indicator fun x => Mf * u x) volume :=
    hintM.integrable_indicator measurableSet_closedBall
  have hbdd : ∀ᵐ x ∂volume, ‖f x * u x‖ ≤
      (closedBall (0 : Fin 2 → ℝ) b).indicator (fun x => Mf * u x) x := by
    filter_upwards [nonneg_ae_of_mem_nonnegCone hu] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf0 x), abs_of_nonneg hx]
    by_cases hxB : x ∈ closedBall (0 : Fin 2 → ℝ) b
    · rw [indicator_of_mem hxB]
      exact mul_le_mul_of_nonneg_right (hfM x) hx
    · rw [indicator_of_notMem hxB,
        hfb x (by simpa [mem_closedBall, dist_eq_norm] using hxB), zero_mul]
  have hfui : Integrable (fun x => f x * u x) volume :=
    hg.mono' (hf.aestronglyMeasurable.mul (Lp.aestronglyMeasurable (u : L²))) hbdd
  calc ∫ x, f x * u x
      ≤ ∫ x, (closedBall (0 : Fin 2 → ℝ) b).indicator (fun x => Mf * u x) x :=
        integral_mono_ae hfui hg (hbdd.mono fun _ h => (Real.le_norm_self _).trans h)
    _ = Mf * ∫ x in closedBall (0 : Fin 2 → ℝ) b, u x := by
        rw [integral_indicator measurableSet_closedBall, integral_const_mul]

/-- **Coercivity**: the nonnegative elements of finite `L¹` norm at which the obstacle functional
is nonpositive lie in an admissible set, for constants depending only on `α`, `κ`, `Mf` and `b`. -/
theorem exists_admissible_of_obstacleFun_nonpos (hα : 0 < α) (hκ : 0 < κ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {Mf : ℝ} (hfM : ∀ x, f x ≤ Mf) {b : ℝ} (hb : 0 < b)
    (hfb : ∀ x, b < ‖x‖ → f x = 0) :
    ∃ L E₀ : ℝ, 0 < L ∧ 0 < E₀ ∧ ∀ u ∈ nonnegCone α, l1Norm u ≠ ⊤ →
      obstacleFun α κ f u ≤ 0 → u ∈ admissible α L E₀ := by
  have hMf : 0 ≤ Mf := (hf0 0).trans (hfM 0)
  have hMf1 : (0 : ℝ) < Mf + 1 := by linarith
  obtain ⟨ε, hε⟩ : ∃ e : ℝ, e = κ ^ 2 / (8 * (Mf + 1) ^ 2) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨R, hR⟩ : ∃ r : ℝ, r = max b (b / ε) := ⟨_, rfl⟩
  have hbR : b ≤ R := hR ▸ le_max_left _ _
  have hR0 : 0 < R := hb.trans_le hbR
  have hRε : (b / R) ^ 4 ≤ ε := by
    refine (pow_le_of_le_one (by positivity) ((div_le_one hR0).2 hbR) four_ne_zero).trans ?_
    rw [div_le_iff₀ hR0]
    calc b = ε * (b / ε) := by field_simp
      _ ≤ ε * R := by
          refine mul_le_mul_of_nonneg_left ?_ hε0.le
          rw [hR]
          exact le_max_right _ _
  obtain ⟨K, hK⟩ : ∃ k : ℝ, k = 2 * ((2 * b) ^ 2 * (2 * R) ^ (2 + α) / (2 * R) ^ 2) *
      (4 * (2 + α) / (1 + α)) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    have hcα0 : (0 : ℝ) < 4 * (2 + α) / (1 + α) := div_pos (by linarith) (by linarith)
    rw [hK]
    positivity
  have hD0 : (0 : ℝ) ≤ Mf ^ 2 * K := by positivity
  have hL0 : (0 : ℝ) < 2 * (Mf ^ 2 * K) / κ + 1 := by
    have : (0 : ℝ) ≤ 2 * (Mf ^ 2 * K) / κ := div_nonneg (by linarith) hκ.le
    linarith
  refine ⟨2 * (Mf ^ 2 * K) / κ + 1, 4 * (Mf ^ 2 * K) + 1, hL0, by linarith, ?_⟩
  intro u hu hufin hu0
  have hn0 : (0 : ℝ) ≤ (l1Norm u).toReal := ENNReal.toReal_nonneg
  have hJ0 : 0 ≤ jumpForm α u u := jumpForm_self_nonneg α _
  have ha0 : (0 : ℝ) ≤ ∫ x in closedBall (0 : Fin 2 → ℝ) b, u x :=
    integral_nonneg_of_ae (ae_restrict_of_ae (nonneg_ae_of_mem_nonnegCone hu))
  have hkey : (∫ x in closedBall (0 : Fin 2 → ℝ) b, u x) ^ 2 ≤
      K * jumpForm α u u + 2 * ε * (l1Norm u).toReal ^ 2 := by
    refine (sq_setIntegral_le_of_mem_nonnegCone hα hu hufin hb hbR).trans ?_
    rw [hK]
    have h1 : 2 * (b / R) ^ 4 * (l1Norm u).toReal ^ 2 ≤ 2 * ε * (l1Norm u).toReal ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    linarith
  have hobs : jumpForm α u u / 2 + κ * (l1Norm u).toReal - ∫ x, f x * u x ≤ 0 := hu0
  have hcoer := coercivity_real hκ hMf hK0 hJ0 hn0 ha0 hε hkey
    (integral_mul_le_of_mem_nonnegCone hf hf0 hfM hb hfb hu) hobs
  have hkn : (0 : ℝ) ≤ κ / 2 * (l1Norm u).toReal := mul_nonneg (by linarith) hn0
  have hnle : (l1Norm u).toReal ≤ 2 * (Mf ^ 2 * K) / κ := by
    rw [le_div_iff₀ hκ]
    linarith
  refine ⟨hu, ?_, by linarith⟩
  rw [← ENNReal.ofReal_toReal hufin]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ### Weak compactness of the admissible sets -/

/-- Nonnegative multiples of elements of the positive cone stay in the cone. -/
theorem smul_mem_nonnegCone {c : ℝ} (hc : 0 ≤ c) {u : EnergySpace α} (hu : u ∈ nonnegCone α) :
    c • u ∈ nonnegCone α := by
  rw [mem_nonnegCone_iff_ae] at hu ⊢
  filter_upwards [hu, Lp.coeFn_smul c (u : L²)] with x hx hx'
  rw [Pi.zero_apply] at hx ⊢
  rw [show ⇑(c • u) x = c * ⇑u x from hx']
  exact mul_nonneg hc hx

/-- The zero function is admissible as soon as the energy bound is nonnegative. -/
theorem zero_mem_admissible (α : ℝ) {L E₀ : ℝ} (hE₀ : 0 ≤ E₀) :
    (0 : EnergySpace α) ∈ admissible α L E₀ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_nonnegCone, toLp_zero]
  · rw [l1Norm_zero]
    exact zero_le
  · rw [jumpForm_self_zero]
    exact hE₀

/-- The admissible set is convex. -/
theorem convex_admissible (α : ℝ) (L E₀ : ℝ) : Convex ℝ (admissible α L E₀) := by
  intro u hu v hv a b ha hb hab
  have hau : a • u ∈ nonnegCone α := smul_mem_nonnegCone ha hu.1
  have hbv : b • v ∈ nonnegCone α := smul_mem_nonnegCone hb hv.1
  refine ⟨convex_nonnegCone hu.1 hv.1 ha hb hab, ?_, ?_⟩
  · rw [l1Norm_add hau hbv, l1Norm_smul ha, l1Norm_smul hb]
    calc ENNReal.ofReal a * l1Norm u + ENNReal.ofReal b * l1Norm v
        ≤ ENNReal.ofReal a * ENNReal.ofReal L + ENNReal.ofReal b * ENNReal.ofReal L :=
          add_le_add (mul_le_mul_right hu.2.1 _) (mul_le_mul_right hv.2.1 _)
      _ = ENNReal.ofReal L := by
          rw [← add_mul, ← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one, one_mul]
  · have h := (convexOn_jumpForm_self α).2 (mem_univ u) (mem_univ v) ha hb hab
    simp only [smul_eq_mul] at h
    calc jumpForm α ⇑(a • u + b • v) ⇑(a • u + b • v)
        ≤ a * jumpForm α u u + b * jumpForm α v v := h
      _ ≤ a * E₀ + b * E₀ :=
          add_le_add (mul_le_mul_of_nonneg_left hu.2.2 ha)
            (mul_le_mul_of_nonneg_left hv.2.2 hb)
      _ = E₀ := by rw [← add_mul, hab, one_mul]

/-- The admissible set is closed: the `L¹` constraint is a sublevel set of a supremum of continuous
functions, hence of a lower semicontinuous function. -/
theorem isClosed_admissible (α : ℝ) (L E₀ : ℝ) : IsClosed (admissible α L E₀) := by
  have h : admissible α L E₀ = (nonnegCone α ∩
      (fun u : EnergySpace α => ⨆ n : ℕ, ENNReal.ofReal (ballFunctional α n u)) ⁻¹'
        Iic (ENNReal.ofReal L)) ∩
      ((fun u : EnergySpace α => jumpForm α u u) ⁻¹' Iic E₀) := by
    ext u
    simp only [admissible, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · exact fun hu =>
        ⟨⟨hu.1, (l1Norm_eq_iSup_ballFunctional hu.1).symm.trans_le hu.2.1⟩, hu.2.2⟩
    · exact fun hu =>
        ⟨hu.1.1, (l1Norm_eq_iSup_ballFunctional hu.1.1).trans_le hu.1.2, hu.2⟩
  rw [h]
  refine IsClosed.inter (isClosed_nonnegCone.inter ?_)
    (isClosed_Iic.preimage (continuous_jumpForm_self α))
  exact (lowerSemicontinuous_iSup fun n => (ENNReal.continuous_ofReal.comp
    (ballFunctional α n).continuous).lowerSemicontinuous).isClosed_preimage _

/-- The admissible set is bounded in the energy norm: the `L²` norm is controlled by the
interpolation inequality of `CenteredMaximal.Analysis.Gagliardo` with `ρ = 1`. -/
theorem isBounded_admissible (hα : 0 < α) {L E₀ : ℝ} (hL : 0 ≤ L) (hE₀ : 0 ≤ E₀) :
    IsBounded (admissible α L E₀) := by
  obtain ⟨cα, hcα⟩ : ∃ c : ℝ, c = 4 * (2 + α) / (1 + α) := ⟨_, rfl⟩
  have hcα0 : 0 < cα := hcα ▸ div_pos (by linarith) (by linarith)
  obtain ⟨D, hD⟩ : ∃ d : ℝ, d = cα * E₀ / 2 + L ^ 2 / 2 := ⟨_, rfl⟩
  have he1 : ∀ z : ℝ, (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 4) * ENNReal.ofReal z
      = ENNReal.ofReal (z / 2) := by
    intro z
    rw [ofReal_two_mul_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    congr 1
    ring
  have hcαE : (0 : ℝ) ≤ cα * E₀ := mul_nonneg hcα0.le hE₀
  have hD0 : 0 ≤ D := by
    rw [hD]
    nlinarith [sq_nonneg L]
  refine isBounded_iff_forall_norm_le.2 ⟨√(D + E₀), fun u hu => ?_⟩
  have hgag : ∫⁻ x, ENNReal.ofReal (u x ^ 2) ≤ ENNReal.ofReal D := by
    have hstep := lintegral_sq_le_gagliardo_add (measurable_coeFn u) hα.le (ρ := 1) one_pos
    rw [Real.one_rpow, one_pow, show (1 : ℝ) / (4 * 1) = 1 / 4 by norm_num] at hstep
    have hG : gagliardo α ⇑u ≤ ENNReal.ofReal (cα * E₀) := by
      refine (gagliardo_le_jumpEnergy (measurable_coeFn u) hα).trans ?_
      rw [← hcα, jumpEnergy_eq u, ← ENNReal.ofReal_mul hcα0.le]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hu.2.2 hcα0.le)
    have hN : (∫⁻ x, ‖u x‖ₑ) ^ 2 ≤ ENNReal.ofReal (L ^ 2) := by
      rw [ENNReal.ofReal_pow hL]
      exact pow_le_pow_left' hu.2.1 2
    refine hstep.trans ((add_le_add (mul_le_mul_right hG _) (mul_le_mul_right hN _)).trans ?_)
    rw [he1, he1, ← ENNReal.ofReal_add (by linarith) (by positivity), hD]
  have hL2 : ‖(u : L²)‖ ^ 2 ≤ D := by
    rw [norm_toLp_sq_eq u, ← ENNReal.toReal_ofReal hD0]
    exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgag)
      ENNReal.ofReal_ne_top).2 hgag
  have hnorm : ‖u‖ ^ 2 ≤ D + E₀ := by
    rw [norm_sq_eq]
    exact add_le_add hL2 hu.2.2
  calc ‖u‖ = √(‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg u)).symm
    _ ≤ √(D + E₀) := Real.sqrt_le_sqrt hnorm

/-- The admissible set is weakly compact. -/
theorem isCompact_toWeakSpace_image_admissible (hα : 0 < α) {L E₀ : ℝ} (hL : 0 ≤ L)
    (hE₀ : 0 ≤ E₀) : IsCompact (toWeakSpace ℝ (EnergySpace α) '' admissible α L E₀) :=
  (convex_admissible α L E₀).isCompact_toWeakSpace_image (isClosed_admissible α L E₀)
    (isBounded_admissible hα hL hE₀)

/-! ### Existence of a minimiser -/

/-- The obstacle functional is weakly lower semicontinuous on the admissible sets. -/
theorem lowerSemicontinuousOn_obstacleFun (hκ : 0 ≤ κ) (hf : MemLp f 2 volume) (L E₀ : ℝ) :
    LowerSemicontinuousOn (obstacleFun α κ f ∘ (toWeakSpace ℝ (EnergySpace α)).symm)
      (toWeakSpace ℝ (EnergySpace α) '' admissible α L E₀) := by
  have hconv : ConvexOn ℝ univ
      fun u : EnergySpace α => jumpForm α u u / 2 - sourceFunctional α hf u := by
    refine ⟨convex_univ, fun u _ v _ a b ha hb hab => ?_⟩
    have h := (convexOn_jumpForm_self α).2 (mem_univ u) (mem_univ v) ha hb hab
    simp only [smul_eq_mul] at h ⊢
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    linarith
  have hcont : Continuous
      fun u : EnergySpace α => jumpForm α u u / 2 - sourceFunctional α hf u :=
    ((continuous_jumpForm_self α).div_const 2).sub (sourceFunctional α hf).continuous
  have h1 : LowerSemicontinuousOn
      ((fun u : EnergySpace α => jumpForm α u u / 2 - sourceFunctional α hf u) ∘
        (toWeakSpace ℝ (EnergySpace α)).symm)
      (toWeakSpace ℝ (EnergySpace α) '' admissible α L E₀) :=
    lowerSemicontinuousOn_of_eqOn
      (hconv.lowerSemicontinuous_comp_toWeakSpace_symm hcont.lowerSemicontinuous) (eqOn_refl _ _)
  have h2 : LowerSemicontinuousOn
      (fun w => κ * ((l1Norm ∘ (toWeakSpace ℝ (EnergySpace α)).symm) w).toReal)
      (toWeakSpace ℝ (EnergySpace α) '' admissible α L E₀) := by
    refine lowerSemicontinuousOn_const_mul_toReal
      (lowerSemicontinuousOn_l1Norm fun _ hv => hv.1) ?_ hκ
    rintro w ⟨v, hv, rfl⟩
    rw [Function.comp_apply, LinearEquiv.symm_apply_apply]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hv.2.1
  have hsum : obstacleFun α κ f ∘ (toWeakSpace ℝ (EnergySpace α)).symm = fun w =>
      ((fun u : EnergySpace α => jumpForm α u u / 2 - sourceFunctional α hf u) ∘
        (toWeakSpace ℝ (EnergySpace α)).symm) w
      + κ * ((l1Norm ∘ (toWeakSpace ℝ (EnergySpace α)).symm) w).toReal := by
    funext w
    simp only [Function.comp_apply, obstacleFun, sourceFunctional_apply]
    ring
  rw [hsum]
  exact h1.add h2

/-- The obstacle functional vanishes at zero. -/
@[simp]
theorem obstacleFun_zero (α κ : ℝ) (f : (Fin 2 → ℝ) → ℝ) : obstacleFun α κ f 0 = 0 := by
  have h : ∫ x, f x * ⇑(0 : EnergySpace α) x = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [coeFn_zero_ae α] with x hx
    simp only [hx, Pi.zero_apply, mul_zero]
  simp only [obstacleFun, jumpForm_self_zero, l1Norm_zero, h, ENNReal.toReal_zero, mul_zero,
    add_zero, zero_div, sub_zero]

/-- **Direct method**: the obstacle functional attains its minimum on every admissible set. -/
theorem exists_isMinOn_admissible (hα : 0 < α) (hκ : 0 ≤ κ) (hf : MemLp f 2 volume) {L E₀ : ℝ}
    (hL : 0 ≤ L) (hE₀ : 0 ≤ E₀) :
    ∃ u ∈ admissible α L E₀, IsMinOn (obstacleFun α κ f) (admissible α L E₀) u :=
  exists_isMinOn_of_isCompact_toWeakSpace_image ⟨0, zero_mem_admissible α hE₀⟩
    (isCompact_toWeakSpace_image_admissible hα hL hE₀)
    (lowerSemicontinuousOn_obstacleFun hκ hf L E₀)

/-- **Existence of a minimiser**: the obstacle functional attains its minimum over all nonnegative
elements of the energy space of finite `L¹` norm. -/
theorem exists_isMinOn_nonnegCone (hα : 0 < α) (hκ : 0 < κ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {Mf : ℝ} (hfM : ∀ x, f x ≤ Mf) {b : ℝ} (hb : 0 < b)
    (hfb : ∀ x, b < ‖x‖ → f x = 0) :
    ∃ u, u ∈ nonnegCone α ∧ l1Norm u ≠ ⊤ ∧ ∀ v ∈ nonnegCone α, l1Norm v ≠ ⊤ →
      obstacleFun α κ f u ≤ obstacleFun α κ f v := by
  obtain ⟨L, E₀, hL, hE₀, hcoer⟩ :=
    exists_admissible_of_obstacleFun_nonpos hα hκ hf hf0 hfM hb hfb
  obtain ⟨u, huA, hmin⟩ := exists_isMinOn_admissible (f := f) hα hκ.le
    (memLp_two_of_bounded hf hf0 hfM hfb) hL.le hE₀.le
  have hu0 : obstacleFun α κ f u ≤ 0 := by
    have h := isMinOn_iff.1 hmin 0 (zero_mem_admissible α hE₀.le)
    rwa [obstacleFun_zero] at h
  refine ⟨u, huA.1, ne_top_of_le_ne_top ENNReal.ofReal_ne_top huA.2.1, fun v hv hvfin => ?_⟩
  rcases le_or_gt (obstacleFun α κ f v) 0 with h | h
  · exact isMinOn_iff.1 hmin v (hcoer v hv hvfin h)
  · exact hu0.trans h.le

end CenteredMaximal
