/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# The jump energy of the coordinate generator

The generator `A = −|D_u|^α − |D_v|^α` on the plane `ℝ²` has, up to a positive normalisation
constant `c_α / 2` which is kept out of the definitions, the symmetric jump Dirichlet form
`E(u, v) = ∑_j ∫_{ℝ²} ∫_ℝ (u(x + t e_j) − u(x)) (v(x + t e_j) − v(x)) |t|^{−1−α} dt dx`.
This file defines the corresponding energy `jumpEnergy α u = E(u, u)` with values in `[0, ∞]` and
the polarised form `jumpForm α u v` as a Bochner integral, and proves the inequalities used by the
obstacle construction:

* `jumpEnergy_smul`, `jumpEnergy_add_le`, `jumpEnergy_neg`, `jumpEnergy_eq_sub`: scaling, the
  quasi-triangle inequality `E(u + v) ≤ 2 (E(u) + E(v))`, and the change of variables
  `x ↦ x − t e_j`;
* `integrable_jumpFormIntegrand`: the polarised integrand is integrable when both energies are
  finite;
* `jumpForm_comm`, `jumpForm_add_left`, `jumpForm_smul_left`, `jumpForm_neg_left`, ...:
  bilinearity of the form on functions of finite energy, and `jumpForm_self`: the form is the
  energy on the diagonal;
* `jumpForm_sq_le`: the Cauchy–Schwarz inequality `E(u, v)² ≤ E(u, u) E(v, v)`, by the
  discriminant of `λ ↦ E(u + λ v, u + λ v) ≥ 0`;
* `jumpEnergy_posPart_le`, `jumpForm_posPart_self_le`: truncation does not increase the energy,
  and the Markov inequality `E(u₊, u₊) ≤ E(u, u₊)`;
* `jumpEnergy_inf_le`: `E(min u v) ≤ E(u) + E(v)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace CenteredMaximal

/-- The unnormalised jump energy `∑_j ∫∫ (u(x + t e_j) − u(x))² |t|^{−1−α} dt dx`, in `[0, ∞]`. -/
def jumpEnergy (α : ℝ) (u : (Fin 2 → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ j : Fin 2, ∫⁻ p : (Fin 2 → ℝ) × ℝ,
    ENNReal.ofReal ((u (p.1 + p.2 • Pi.single j 1) - u p.1) ^ 2 * |p.2| ^ (-(1 + α)))

/-- The polarised jump form `∑_j ∫∫ (u(x + t e_j) − u(x)) (v(x + t e_j) − v(x)) |t|^{−1−α}`, a
Bochner integral (zero if the integrand is not integrable, following Mathlib's convention). -/
def jumpForm (α : ℝ) (u v : (Fin 2 → ℝ) → ℝ) : ℝ :=
  ∑ j : Fin 2, ∫ p : (Fin 2 → ℝ) × ℝ,
    (u (p.1 + p.2 • Pi.single j 1) - u p.1) * (v (p.1 + p.2 • Pi.single j 1) - v p.1) *
      |p.2| ^ (-(1 + α))

/-- The positive part `x ↦ max (u x) 0` of a function on the plane. -/
def posPart (u : (Fin 2 → ℝ) → ℝ) : (Fin 2 → ℝ) → ℝ := fun x => max (u x) 0

/-! ### Measurability and pointwise inequalities -/

/-- The coordinate increment `(x, t) ↦ u(x + t e_j) − u(x)` is measurable. -/
theorem measurable_jumpDiff {u : (Fin 2 → ℝ) → ℝ} (hu : Measurable u) (j : Fin 2) :
    Measurable fun p : (Fin 2 → ℝ) × ℝ => u (p.1 + p.2 • Pi.single j 1) - u p.1 :=
  (hu.comp (measurable_fst.add (measurable_snd.smul_const _))).sub (hu.comp measurable_fst)

/-- The jump weight `(x, t) ↦ |t|^{−(1+α)}` is measurable. -/
theorem measurable_jumpWeight (α : ℝ) :
    Measurable fun p : (Fin 2 → ℝ) × ℝ => |p.2| ^ (-(1 + α)) :=
  measurable_snd.abs.pow_const _

/-- The jump weight `|t|^{−(1+α)}` is nonnegative. -/
theorem jumpWeight_nonneg (α : ℝ) (p : (Fin 2 → ℝ) × ℝ) : 0 ≤ |p.2| ^ (-(1 + α)) :=
  Real.rpow_nonneg (abs_nonneg _) _

/-- The integrand of the jump energy is measurable. -/
theorem measurable_jumpIntegrand (α : ℝ) {u : (Fin 2 → ℝ) → ℝ} (hu : Measurable u) (j : Fin 2) :
    Measurable fun p : (Fin 2 → ℝ) × ℝ =>
      ENNReal.ofReal ((u (p.1 + p.2 • Pi.single j 1) - u p.1) ^ 2 * |p.2| ^ (-(1 + α))) :=
  (((measurable_jumpDiff hu j).pow_const 2).mul (measurable_jumpWeight α)).ennreal_ofReal

/-- The integrand of the jump form is measurable. -/
theorem measurable_jumpFormIntegrand (α : ℝ) {u v : (Fin 2 → ℝ) → ℝ} (hu : Measurable u)
    (hv : Measurable v) (j : Fin 2) :
    Measurable fun p : (Fin 2 → ℝ) × ℝ =>
      (u (p.1 + p.2 • Pi.single j 1) - u p.1) * (v (p.1 + p.2 • Pi.single j 1) - v p.1) *
        |p.2| ^ (-(1 + α)) :=
  ((measurable_jumpDiff hu j).mul (measurable_jumpDiff hv j)).mul (measurable_jumpWeight α)

/-- `|a b| w ≤ a² w + b² w` for `w ≥ 0`. -/
theorem abs_mul_abs_mul_le (a b : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    |a| * |b| * w ≤ a ^ 2 * w + b ^ 2 * w := by
  have h := two_mul_le_add_sq |a| |b|
  rw [sq_abs, sq_abs] at h
  nlinarith [mul_le_mul_of_nonneg_right h hw,
    mul_nonneg (mul_nonneg (abs_nonneg a) (abs_nonneg b)) hw]

/-- Truncation is `1`-Lipschitz: `(a₊ − b₊)² ≤ (a − b)²`. -/
theorem sq_max_sub_max_le (a b : ℝ) : (max a 0 - max b 0) ^ 2 ≤ (a - b) ^ 2 := by
  rw [← sq_abs (max a 0 - max b 0), ← sq_abs (a - b)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_max_sub_max_le_abs a b 0) 2

/-- The pointwise Markov inequality `(a₊ − b₊)² ≤ (a − b) (a₊ − b₊)`: the mixed term
`(a − a₊ − (b − b₊)) (a₊ − b₊)` is nonnegative. -/
theorem sq_max_sub_max_le_mul (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 ≤ (a - b) * (max a 0 - max b 0) := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb <;>
    simp only [max_eq_left ha, max_eq_right ha, max_eq_left hb, max_eq_right hb] <;> nlinarith

/-- Taking minima is `1`-Lipschitz in each argument:
`(min a b − min c d)² ≤ (a − c)² + (b − d)²`. -/
theorem sq_min_sub_min_le (a b c d : ℝ) : (min a b - min c d) ^ 2 ≤ (a - c) ^ 2 + (b - d) ^ 2 := by
  rw [← sq_abs (min a b - min c d), ← sq_abs (a - c), ← sq_abs (b - d)]
  calc |min a b - min c d| ^ 2 ≤ max |a - c| |b - d| ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_min_sub_min_le_max a b c d) 2
    _ ≤ |a - c| ^ 2 + |b - d| ^ 2 := by
        rcases le_total |a - c| |b - d| with h | h
        · rw [max_eq_right h]; nlinarith [sq_nonneg |a - c|]
        · rw [max_eq_left h]; nlinarith [sq_nonneg |b - d|]

/-! ### The energy -/

/-- Scaling: `E(c u) = c² E(u)`. -/
theorem jumpEnergy_smul (α : ℝ) (c : ℝ) (u : (Fin 2 → ℝ) → ℝ) :
    jumpEnergy α (c • u) = ENNReal.ofReal (c ^ 2) * jumpEnergy α u := by
  unfold jumpEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun p => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg c)]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The energy is even: `E(−u) = E(u)`. -/
theorem jumpEnergy_neg (α : ℝ) (u : (Fin 2 → ℝ) → ℝ) : jumpEnergy α (-u) = jumpEnergy α u := by
  unfold jumpEnergy
  refine Finset.sum_congr rfl fun j _ => lintegral_congr fun p => ?_
  congr 2
  simp only [Pi.neg_apply]
  ring

/-- The quasi-triangle inequality `E(u + v) ≤ 2 (E(u) + E(v))`, from `(a + b)² ≤ 2 a² + 2 b²`. -/
theorem jumpEnergy_add_le (α : ℝ) {u : (Fin 2 → ℝ) → ℝ} (hu : Measurable u)
    (v : (Fin 2 → ℝ) → ℝ) : jumpEnergy α (u + v) ≤ 2 * (jumpEnergy α u + jumpEnergy α v) := by
  unfold jumpEnergy
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← lintegral_add_left (measurable_jumpIntegrand α hu j),
    ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
  refine lintegral_mono fun p => ?_
  simp only [Pi.add_apply]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [mul_nonneg (sq_nonneg ((u (p.1 + p.2 • Pi.single j 1) - u p.1) -
    (v (p.1 + p.2 • Pi.single j 1) - v p.1))) (jumpWeight_nonneg α p)]

/-- A function of finite energy has every coordinate summand finite. -/
theorem lintegral_jumpIntegrand_lt_top {α : ℝ} {u : (Fin 2 → ℝ) → ℝ} (hu : jumpEnergy α u ≠ ⊤)
    (j : Fin 2) :
    ∫⁻ p : (Fin 2 → ℝ) × ℝ,
      ENNReal.ofReal ((u (p.1 + p.2 • Pi.single j 1) - u p.1) ^ 2 * |p.2| ^ (-(1 + α))) < ⊤ :=
  ENNReal.lt_top_of_sum_ne_top hu (Finset.mem_univ j)

/-- The change of variables `x ↦ x − t e_j` at fixed `t`: the energy can be computed with the
backward increments `u(x) − u(x − t e_j)`. -/
theorem jumpEnergy_eq_sub (α : ℝ) {u : (Fin 2 → ℝ) → ℝ} (hu : Measurable u) :
    jumpEnergy α u = ∑ j : Fin 2, ∫⁻ p : (Fin 2 → ℝ) × ℝ,
      ENNReal.ofReal ((u p.1 - u (p.1 - p.2 • Pi.single j 1)) ^ 2 * |p.2| ^ (-(1 + α))) := by
  unfold jumpEnergy
  refine Finset.sum_congr rfl fun j _ => ?_
  have hmeas : Measurable fun p : (Fin 2 → ℝ) × ℝ =>
      ENNReal.ofReal ((u p.1 - u (p.1 - p.2 • Pi.single j 1)) ^ 2 * |p.2| ^ (-(1 + α))) :=
    ((((hu.comp measurable_fst).sub
      (hu.comp (measurable_fst.sub (measurable_snd.smul_const _)))).pow_const 2).mul
      (measurable_jumpWeight α)).ennreal_ofReal
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ (measurable_jumpIntegrand α hu j).aemeasurable,
    lintegral_prod_symm _ hmeas.aemeasurable]
  refine lintegral_congr fun t => ?_
  -- translation invariance `x ↦ x + t e_j` of Lebesgue measure at fixed `t`
  have h := lintegral_add_right_eq_self (μ := volume)
    (fun x : Fin 2 → ℝ => ENNReal.ofReal ((u x - u (x - t • Pi.single j 1)) ^ 2 * |t| ^ (-(1 + α))))
    (t • Pi.single j 1)
  simp only [add_sub_cancel_right] at h
  exact h

/-! ### Integrability of the integrands -/

/-- The integrand `(Δ_j u)² |t|^{−(1+α)}` of a finite jump energy is integrable. -/
theorem integrable_jumpIntegrand {α : ℝ} {u : (Fin 2 → ℝ) → ℝ} (hu : Measurable u)
    (hu' : jumpEnergy α u ≠ ⊤) (j : Fin 2) :
    Integrable fun p : (Fin 2 → ℝ) × ℝ =>
      (u (p.1 + p.2 • Pi.single j 1) - u p.1) ^ 2 * |p.2| ^ (-(1 + α)) := by
  refine ⟨(((measurable_jumpDiff hu j).pow_const 2).mul
    (measurable_jumpWeight α)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun p => by positivity)]
  exact lintegral_jumpIntegrand_lt_top hu' j

/-- The polarised integrand `(Δ_j u) (Δ_j v) |t|^{−(1+α)}` is integrable when both energies are
finite, by `|a b| ≤ a² + b²`. -/
theorem integrable_jumpFormIntegrand {α : ℝ} {u v : (Fin 2 → ℝ) → ℝ} (hu : Measurable u)
    (hv : Measurable v) (hu' : jumpEnergy α u ≠ ⊤) (hv' : jumpEnergy α v ≠ ⊤) (j : Fin 2) :
    Integrable fun p : (Fin 2 → ℝ) × ℝ =>
      (u (p.1 + p.2 • Pi.single j 1) - u p.1) * (v (p.1 + p.2 • Pi.single j 1) - v p.1) *
        |p.2| ^ (-(1 + α)) := by
  refine ((integrable_jumpIntegrand hu hu' j).add (integrable_jumpIntegrand hv hv' j)).mono'
    (measurable_jumpFormIntegrand α hu hv j).aestronglyMeasurable (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (jumpWeight_nonneg α p), Pi.add_apply]
  exact abs_mul_abs_mul_le _ _ (jumpWeight_nonneg α p)

/-! ### The polarised form -/

/-- The jump form is symmetric. -/
theorem jumpForm_comm (α : ℝ) (u v : (Fin 2 → ℝ) → ℝ) : jumpForm α u v = jumpForm α v u := by
  unfold jumpForm
  refine Finset.sum_congr rfl fun _ _ => ?_
  congr 1
  funext p
  ring

/-- The jump form is nonnegative on the diagonal. -/
theorem jumpForm_self_nonneg (α : ℝ) (u : (Fin 2 → ℝ) → ℝ) : 0 ≤ jumpForm α u u :=
  Finset.sum_nonneg fun _ _ =>
    integral_nonneg fun p => mul_nonneg (mul_self_nonneg _) (jumpWeight_nonneg α p)

/-- The jump form is homogeneous in the first argument. -/
theorem jumpForm_smul_left (α : ℝ) (c : ℝ) (u v : (Fin 2 → ℝ) → ℝ) :
    jumpForm α (c • u) v = c * jumpForm α u v := by
  unfold jumpForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  congr 1
  funext p
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The jump form is homogeneous in the second argument. -/
theorem jumpForm_smul_right (α : ℝ) (c : ℝ) (u v : (Fin 2 → ℝ) → ℝ) :
    jumpForm α u (c • v) = c * jumpForm α u v := by
  rw [jumpForm_comm, jumpForm_smul_left, jumpForm_comm]

/-- The jump form is odd in the first argument. -/
theorem jumpForm_neg_left (α : ℝ) (u v : (Fin 2 → ℝ) → ℝ) :
    jumpForm α (-u) v = -jumpForm α u v := by
  unfold jumpForm
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_neg]
  congr 1
  funext p
  simp only [Pi.neg_apply]
  ring

/-- The jump form is odd in the second argument. -/
theorem jumpForm_neg_right (α : ℝ) (u v : (Fin 2 → ℝ) → ℝ) :
    jumpForm α u (-v) = -jumpForm α u v := by
  rw [jumpForm_comm, jumpForm_neg_left, jumpForm_comm]

/-- The jump form is additive in the first argument on functions of finite energy. -/
theorem jumpForm_add_left (α : ℝ) {u v w : (Fin 2 → ℝ) → ℝ} (hu : Measurable u)
    (hv : Measurable v) (hw : Measurable w) (hu' : jumpEnergy α u ≠ ⊤) (hv' : jumpEnergy α v ≠ ⊤)
    (hw' : jumpEnergy α w ≠ ⊤) : jumpForm α (u + v) w = jumpForm α u w + jumpForm α v w := by
  unfold jumpForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_add (integrable_jumpFormIntegrand hu hw hu' hw' j)
    (integrable_jumpFormIntegrand hv hw hv' hw' j)]
  congr 1
  funext p
  simp only [Pi.add_apply]
  ring

/-- The jump form is additive in the second argument on functions of finite energy. -/
theorem jumpForm_add_right (α : ℝ) {u v w : (Fin 2 → ℝ) → ℝ} (hu : Measurable u)
    (hv : Measurable v) (hw : Measurable w) (hu' : jumpEnergy α u ≠ ⊤) (hv' : jumpEnergy α v ≠ ⊤)
    (hw' : jumpEnergy α w ≠ ⊤) : jumpForm α u (v + w) = jumpForm α u v + jumpForm α u w := by
  rw [jumpForm_comm, jumpForm_add_left α hv hw hu hv' hw' hu', jumpForm_comm, jumpForm_comm α w]

/-- The jump form is subtractive in the first argument on functions of finite energy. -/
theorem jumpForm_sub_left (α : ℝ) {u v w : (Fin 2 → ℝ) → ℝ} (hu : Measurable u)
    (hv : Measurable v) (hw : Measurable w) (hu' : jumpEnergy α u ≠ ⊤) (hv' : jumpEnergy α v ≠ ⊤)
    (hw' : jumpEnergy α w ≠ ⊤) : jumpForm α (u - v) w = jumpForm α u w - jumpForm α v w := by
  rw [sub_eq_add_neg, jumpForm_add_left α hu hv.neg hw hu' (jumpEnergy_neg α v ▸ hv') hw',
    jumpForm_neg_left, sub_eq_add_neg]

/-- On the diagonal, the jump form of a function of finite energy is its energy. -/
theorem jumpForm_self (α : ℝ) {u : (Fin 2 → ℝ) → ℝ} (hu : Measurable u)
    (hu' : jumpEnergy α u ≠ ⊤) : ENNReal.ofReal (jumpForm α u u) = jumpEnergy α u := by
  unfold jumpForm jumpEnergy
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ =>
    integral_nonneg fun p => mul_nonneg (mul_self_nonneg _) (jumpWeight_nonneg α p)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_jumpFormIntegrand hu hu hu' hu' j)
    (ae_of_all _ fun p => mul_nonneg (mul_self_nonneg _) (jumpWeight_nonneg α p))]
  refine lintegral_congr fun p => ?_
  rw [sq]

/-- The energy of `u + c v` is finite when the energies of `u` and `v` are. -/
theorem jumpEnergy_add_smul_ne_top (α : ℝ) {u v : (Fin 2 → ℝ) → ℝ} (hu : Measurable u)
    (hu' : jumpEnergy α u ≠ ⊤) (hv' : jumpEnergy α v ≠ ⊤) (c : ℝ) :
    jumpEnergy α (u + c • v) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (jumpEnergy_add_le α hu (c • v))
  rw [jumpEnergy_smul]
  exact ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    (ENNReal.add_ne_top.2 ⟨hu', ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv'⟩)

/-- The Cauchy–Schwarz inequality `E(u, v)² ≤ E(u, u) E(v, v)` for functions of finite energy:
the quadratic `λ ↦ E(u + λ v, u + λ v) = E(v, v) λ² + 2 E(u, v) λ + E(u, u)` is nonnegative, so
its discriminant is nonpositive. -/
theorem jumpForm_sq_le (α : ℝ) {u v : (Fin 2 → ℝ) → ℝ} (hu : Measurable u) (hv : Measurable v)
    (hu' : jumpEnergy α u ≠ ⊤) (hv' : jumpEnergy α v ≠ ⊤) :
    jumpForm α u v ^ 2 ≤ jumpForm α u u * jumpForm α v v := by
  have key : ∀ x : ℝ,
      0 ≤ jumpForm α v v * (x * x) + 2 * jumpForm α u v * x + jumpForm α u u := fun x => by
    have hx : Measurable (x • v) := hv.const_mul x
    have hx' : jumpEnergy α (x • v) ≠ ⊤ := by
      rw [jumpEnergy_smul]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv'
    have h := jumpForm_self_nonneg α (u + x • v)
    rw [jumpForm_add_left α hu hx (hu.add hx) hu' hx' (jumpEnergy_add_smul_ne_top α hu hu' hv' x),
      jumpForm_add_right α hu hu hx hu' hu' hx', jumpForm_add_right α hx hu hx hx' hu' hx',
      jumpForm_smul_left, jumpForm_smul_right, jumpForm_smul_right, jumpForm_smul_left,
      jumpForm_comm α v u] at h
    nlinarith [h]
  have h := discrim_le_zero key
  rw [discrim] at h
  nlinarith [h]

/-! ### Truncation -/

/-- The positive part of a measurable function is measurable. -/
theorem measurable_posPart {u : (Fin 2 → ℝ) → ℝ} (hu : Measurable u) : Measurable (posPart u) :=
  hu.max measurable_const

/-- Truncation does not increase the energy: `E(u₊) ≤ E(u)`. -/
theorem jumpEnergy_posPart_le (α : ℝ) (u : (Fin 2 → ℝ) → ℝ) :
    jumpEnergy α (posPart u) ≤ jumpEnergy α u := by
  unfold jumpEnergy
  refine Finset.sum_le_sum fun j _ => lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_right (sq_max_sub_max_le _ _) (jumpWeight_nonneg α p)

/-- The Markov truncation inequality `E(u₊, u₊) ≤ E(u, u₊)` for a function of finite energy. -/
theorem jumpForm_posPart_self_le (α : ℝ) {u : (Fin 2 → ℝ) → ℝ} (hu : Measurable u)
    (hu' : jumpEnergy α u ≠ ⊤) :
    jumpForm α (posPart u) (posPart u) ≤ jumpForm α u (posPart u) := by
  have hp' : jumpEnergy α (posPart u) ≠ ⊤ := ne_top_of_le_ne_top hu' (jumpEnergy_posPart_le α u)
  unfold jumpForm
  refine Finset.sum_le_sum fun j _ => integral_mono
    (integrable_jumpFormIntegrand (measurable_posPart hu) (measurable_posPart hu) hp' hp' j)
    (integrable_jumpFormIntegrand hu (measurable_posPart hu) hu' hp' j) fun p => ?_
  refine mul_le_mul_of_nonneg_right ?_ (jumpWeight_nonneg α p)
  rw [← sq]
  exact sq_max_sub_max_le_mul _ _

/-- Taking the minimum of two functions is controlled by the sum of the energies:
`E(min u v) ≤ E(u) + E(v)`. -/
theorem jumpEnergy_inf_le (α : ℝ) {u v : (Fin 2 → ℝ) → ℝ} (hu : Measurable u) :
    jumpEnergy α (fun x => min (u x) (v x)) ≤ jumpEnergy α u + jumpEnergy α v := by
  unfold jumpEnergy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← lintegral_add_left (measurable_jumpIntegrand α hu j)]
  refine lintegral_mono fun p => ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← add_mul]
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (sq_min_sub_min_le _ _ _ _) (jumpWeight_nonneg α p))

end CenteredMaximal
