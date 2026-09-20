/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.KernelMass
public import CenteredMaximal.Transfer.JumpTransfer

/-!
# Three gaps in the assembly of the `α = 6/5` upper bound

The comparison kernel `fracKernel` of `CenteredMaximal.Fractional.KernelMass` is a **list** sum
over the `1201` cells of `fracCells`, while the generator computation
`CenteredMaximal.Fractional.jumpGen_splineSum` is stated for a **`Finset`** sum. This file bridges
the two, and proves the two analytic facts that the transfer lemma
`CenteredMaximal.convolution_le_of_eq_zero_fp` asks of a generator density.

## Main results

* `nodup_fracCells_keys`: the `1201` cell indices of `fracCells` are pairwise distinct. This is a
  *structural* proof, not a computation: the unordered pair of absolute values `diamondInv` is an
  invariant of the eight-element diamond action, it is constant on each `diamondOrbit`, and it
  separates the `169` representatives, so distinct representatives generate disjoint orbits.
* `fracKernel_eq_finsetSum`: the resulting rewriting of `fracKernel` as a `Finset` sum over
  `fracCellFinset` with coefficients `fracCellCoeff`, in exactly the shape `jumpGen_splineSum`
  consumes. `fracCellFinset_card` records that the finite set really does have `1201` elements,
  and `jumpGen_fracKernel_sub_base` feeds the bridge straight into `jumpGen_splineSum`.
* `integrable_diamondRpow_mul_min_one`: **the Lévy moment condition for the model singularity**,
  `∫ diamondNorm z ^ (-p) · min(1, ‖z‖) dz < ∞` for `2 < p < 3`. Both bounds are sharp for this
  integrand: near the origin the radial integral is `∫₀¹ 4 t^{2−p} dt`, which converges iff
  `p < 3`, and at infinity it is `∫₁^∞ 4 t^{1−p} dt`, which converges iff `p > 2`. The generator
  density of `fracKernel` behaves like `r^{−12/5}` at the origin and like `r^{−11/5}` at infinity,
  and `12/5` and `11/5` both lie in `(2, 3)`, so the hypothesis covers it
  (`integrable_diamondRpow_mul_min_one_twelve_fifths`). The general weight `min(1, ‖z‖^θ)` needs
  `2 < p < 2 + θ` and is `integrable_diamondRpow_mul_min_one_rpow`; `integrable_mul_min_one_of_le`
  and `integrable_mul_min_one_rpow_of_le` transfer both to any density dominated by
  `A (r^{−p} + r^{−q})`.
* `hgconv_of_modulus`: **a sufficient condition for the joint integrability hypothesis `hgconv`**
  of `convolution_le_of_eq_zero_fp`. It cannot follow from `u ∈ L¹` alone; what makes it work is an
  `L¹` modulus of continuity `∫ |u(· − z) − u| ≤ C min(1, ‖z‖^θ)` on `u`, together with the
  matching moment `∫ g(z) min(1, ‖z‖^θ) dz < ∞` on the density.

## Method

The orbit bookkeeping is arranged so that no `decide` ever touches the `1201` cells, only the `169`
representatives: `fracOrbits_repr` checks `i ≥ j ≥ 0` for the representatives and
`nodup_fracOrbits_keys` checks that their index pairs are distinct, both `169`-element kernel
computations that take a fraction of a second. Everything else is `List.nodup_flatMap` plus the
invariant lemma `diamondInv_of_mem_diamondOrbit`, and each `diamondOrbit` is duplicate-free for
free because it is a `List.dedup`.

The moment condition is proved by a single radial majorant: the integrand is dominated by
`diamondNorm z ^ (1 − p)` on the unit diamond and by `diamondNorm z ^ (−p)` outside it, and the
radial formula `CenteredMaximal.Cauchy.lintegral_comp_diamondNorm` turns the `ℝ≥0∞`-integral of
that majorant into `∫_{(0,1]} 4 t^{2−p} dt + ∫_{(1,∞)} 4 t^{1−p} dt`, both of which are evaluated
by `intervalIntegral.intervalIntegrable_rpow'` and `integrableOn_Ioi_rpow_of_lt`.

For `hgconv` the product integral is turned round by `lintegral_prod_symm` so that the `x`-fibre
comes first; on that fibre the test function is replaced by its sup bound and the modulus of
continuity applies, leaving the `z`-integral `∫ g(z) min(1, ‖z‖^θ) dz`.
-/

@[expose] public section

open MeasureTheory Set
open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### The invariant of the diamond action -/

/-- The invariant of the eight-element diamond action (the two independent sign flips and the
swap) on an index pair: the unordered pair `{|i|, |j|}` of absolute values, written as the ordered
pair `(max, min)`. It is constant on orbits and it recovers the orbit representative. -/
def diamondInv (p : ℤ × ℤ) : ℤ × ℤ := (max |p.1| |p.2|, min |p.1| |p.2|)

/-- Every orbit is duplicate-free, being a `List.dedup`. -/
theorem nodup_diamondOrbit (i j : ℤ) : (diamondOrbit i j).Nodup := List.nodup_dedup _

/-- **The invariant is constant on an orbit and returns the representative.** Each of the eight
listed images of `(i, j)` has the same pair of absolute values `{i, j}` as `(i, j)` itself, and
for a representative, `i ≥ j ≥ 0`, so the maximum is `i` and the minimum is `j`. -/
theorem diamondInv_of_mem_diamondOrbit {i j : ℤ} (hj : 0 ≤ j) (hji : j ≤ i) {p : ℤ × ℤ}
    (hp : p ∈ diamondOrbit i j) : diamondInv p = (i, j) := by
  have hi : (0 : ℤ) ≤ i := hj.trans hji
  rw [diamondOrbit, List.mem_dedup] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [diamondInv, abs_of_nonneg hi, abs_of_nonneg hj, max_eq_left hji, min_eq_right hji,
      max_eq_right hji, min_eq_left hji]

set_option maxRecDepth 20000 in
/-- **The `169` entries of `fracOrbits` really are orbit representatives**: each satisfies
`i ≥ j ≥ 0`. -/
theorem fracOrbits_repr : ∀ o ∈ fracOrbits, 0 ≤ o.2.1 ∧ o.2.1 ≤ o.1 := by decide

set_option maxRecDepth 20000 in
/-- **The `169` representatives have pairwise distinct index pairs.** This is the only place where
the certificate data is inspected by the kernel, and it is a `169`-element check. -/
theorem nodup_fracOrbits_keys : (fracOrbits.map fun o => ((o.1, o.2.1) : ℤ × ℤ)).Nodup := by decide

/-! ### The cells of the certificate are pairwise distinct -/

/-- Forgetting the coefficients turns the cell list into the concatenation of the orbits. -/
theorem fracCells_map_fst :
    fracCells.map Prod.fst = fracOrbits.flatMap fun o => diamondOrbit o.1 o.2.1 := by
  simp [fracCells, List.map_flatMap, List.map_map, Function.comp_def]

/-- **The `1201` cell indices of the certificate are pairwise distinct.** Each orbit is
duplicate-free because it is a `List.dedup`, and two orbits generated by different representatives
are disjoint because `diamondInv` is constant on each and separates the representatives. -/
theorem nodup_fracCells_keys : (fracCells.map Prod.fst).Nodup := by
  rw [fracCells_map_fst, List.nodup_flatMap]
  refine ⟨fun o _ => nodup_diamondOrbit _ _, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ (List.pairwise_map.1 nodup_fracOrbits_keys)
  intro a b ha hb hne p hpa hpb
  obtain ⟨ha0, ha1⟩ := fracOrbits_repr a ha
  obtain ⟨hb0, hb1⟩ := fracOrbits_repr b hb
  exact hne ((diamondInv_of_mem_diamondOrbit ha0 ha1 hpa).symm.trans
    (diamondInv_of_mem_diamondOrbit hb0 hb1 hpb))

/-- The cell list itself is duplicate-free. -/
theorem nodup_fracCells : fracCells.Nodup := nodup_fracCells_keys.of_map _

/-- Selecting one key out of a list with pairwise distinct keys. -/
private theorem listSum_ite_eq :
    ∀ l : List ((ℤ × ℤ) × ℤ), (l.map Prod.fst).Nodup → ∀ p ∈ l,
      (l.map fun q => if q.1 = p.1 then q.2 else 0).sum = p.2 := by
  intro l
  induction l with
  | nil => intro _ p hp; cases hp
  | cons a t ih =>
      intro hl p hp
      rw [List.map_cons, List.nodup_cons] at hl
      obtain ⟨hnot, ht⟩ := hl
      rw [List.map_cons, List.sum_cons]
      rcases List.mem_cons.1 hp with rfl | hpt
      · rw [if_pos rfl, List.sum_eq_zero, add_zero]
        intro x hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
        exact if_neg fun h => hnot (List.mem_map.2 ⟨q, hq, h⟩)
      · rw [if_neg fun h => hnot (List.mem_map.2 ⟨p, hpt, h.symm⟩), zero_add, ih ht p hpt]

/-- The finite set of the `1201` spline cells of the certificate. -/
def fracCellFinset : Finset (ℤ × ℤ) := fracCells.toFinset.image Prod.fst

/-- The coefficient numerator attached to a cell, as a function of the cell alone. -/
def fracCellCoeff (ij : ℤ × ℤ) : ℤ := (fracCells.map fun p => if p.1 = ij then p.2 else 0).sum

/-- `fracCellCoeff` returns the recorded coefficient of every cell of the certificate. -/
theorem fracCellCoeff_eq {p : (ℤ × ℤ) × ℤ} (hp : p ∈ fracCells) : fracCellCoeff p.1 = p.2 :=
  listSum_ite_eq fracCells nodup_fracCells_keys p hp

/-- A cell of the certificate is determined by its index. -/
theorem injOn_fst_fracCells : Set.InjOn Prod.fst (fracCells.toFinset : Set ((ℤ × ℤ) × ℤ)) := by
  intro p hp q hq h
  have hp' : p ∈ fracCells := List.mem_toFinset.1 (by simpa using hp)
  have hq' : q ∈ fracCells := List.mem_toFinset.1 (by simpa using hq)
  refine Prod.ext h ?_
  rw [← fracCellCoeff_eq hp', ← fracCellCoeff_eq hq', h]

/-- **The certificate really has `1201` distinct cells.** -/
theorem fracCellFinset_card : fracCellFinset.card = 1201 := by
  rw [fracCellFinset, Finset.card_image_of_injOn injOn_fst_fracCells,
    List.toFinset_card_of_nodup nodup_fracCells, fracCells_length]

noncomputable section

/-- **The comparison kernel as a `Finset` sum.** This is the shape that
`CenteredMaximal.Fractional.jumpGen_splineSum` consumes; the list sum of `fracKernel` becomes a
sum over `fracCellFinset` because the cell indices are pairwise distinct. -/
theorem fracKernel_eq_finsetSum (z : Fin 2 → ℝ) :
    fracKernel z = fracBaseCoeff * truncBase (6 / 5) (7 / 4) z
      + ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
          (bspline (16 * z 0 - ij.1) * bspline (16 * z 1 - ij.2)) := by
  rw [fracKernel, add_right_inj, fracCellFinset, Finset.sum_image injOn_fst_fracCells,
    List.sum_toFinset _ nodup_fracCells]
  exact congrArg List.sum (List.map_congr_left fun p hp => by rw [fracCellCoeff_eq hp])
/-- **The generator of the spline part of the comparison kernel.** Because the cell indices are
distinct, the list sum of `fracKernel` is the `Finset` sum `jumpGen_splineSum` consumes, and the
generator of the spline part is the corresponding sum of single-cell generators. This is the form
the `α = 6/5` positivity check is stated against. -/
theorem jumpGen_fracKernel_sub_base (z : Fin 2 → ℝ) :
    jumpGen (6 / 5) (fun w => fracKernel w - fracBaseCoeff * truncBase (6 / 5) (7 / 4) w) z
      = ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
          ((16 : ℝ) ^ (6 / 5 : ℝ) *
            (jumpGen1 (6 / 5) bspline (16 * z 0 - ij.1) * bspline (16 * z 1 - ij.2)
              + bspline (16 * z 0 - ij.1) * jumpGen1 (6 / 5) bspline (16 * z 1 - ij.2))) := by
  have hcongr : (fun w : Fin 2 → ℝ => fracKernel w - fracBaseCoeff * truncBase (6 / 5) (7 / 4) w)
      = fun w => ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
          (bspline (16 * w 0 - ij.1) * bspline (16 * w 1 - ij.2)) := by
    funext w
    rw [fracKernel_eq_finsetSum w]
    ring
  rw [hcongr]
  exact jumpGen_splineSum (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _ z

/-! ### The Lévy moment condition for the model singularity

The transfer lemma `CenteredMaximal.convolution_le_of_eq_zero_fp` needs
`Integrable fun z => g z * min 1 ‖z‖` of the generator density `g`, and `hgconv_of_modulus` below
needs the same with the weight `min(1, ‖z‖^θ)` of a fractional modulus of continuity. For a density
comparable to a power of the diamond radius both are an exact pair of inequalities on the exponent,
derived here: splitting the radial integral of `lintegral_comp_diamondNorm` at `t = 1` leaves
`∫_{(0,1]} 4 t^{1+θ−p} dt`, which converges iff `1 + θ − p > −1`, i.e. `p < 2 + θ`, and
`∫_{(1,∞)} 4 t^{1−p} dt`, which converges iff `1 − p < −1`, i.e. `p > 2`. -/

/-- The radial majorant of the moment integrand: `t^{θ−p}` on the unit diamond, where
`min(1, ‖z‖^θ) ≤ ‖z‖^θ ≤ (diamondNorm z)^θ`, and `t^{−p}` outside it, where
`min(1, ‖z‖^θ) ≤ 1`. -/
private def momProfile (p θ t : ℝ) : ℝ := if t ≤ 1 then t ^ (θ - p) else t ^ (-p)

private theorem measurable_momProfile (p θ : ℝ) : Measurable (momProfile p θ) :=
  Measurable.ite (measurableSet_Iic (a := (1 : ℝ))) (measurable_id.pow_const _)
    (measurable_id.pow_const _)

/-- The moment integrand is dominated by its radial majorant. -/
private theorem momIntegrand_le {θ : ℝ} (hθ : 0 < θ) (p : ℝ) (z : Fin 2 → ℝ) :
    diamondNorm z ^ (-p) * min 1 (‖z‖ ^ θ) ≤ momProfile p θ (diamondNorm z) := by
  have hz0 : 0 ≤ diamondNorm z := diamondNorm_nonneg z
  have hpow : 0 ≤ diamondNorm z ^ (-p) := Real.rpow_nonneg hz0 _
  unfold momProfile
  split
  · rcases eq_or_lt_of_le hz0 with h0 | h0
    · have hz : z = 0 := diamondNorm_eq_zero_iff.1 h0.symm
      rw [hz, norm_zero, Real.zero_rpow hθ.ne', min_eq_right zero_le_one, mul_zero]
      exact Real.rpow_nonneg (diamondNorm_nonneg 0) _
    · have hle : min 1 (‖z‖ ^ θ) ≤ diamondNorm z ^ θ := (min_le_right _ _).trans
        (Real.rpow_le_rpow (norm_nonneg z) (norm_le_diamondNorm z) hθ.le)
      refine (mul_le_mul_of_nonneg_left hle hpow).trans_eq ?_
      rw [show θ - p = -p + θ from by ring, Real.rpow_add h0]
  · refine (mul_le_mul_of_nonneg_left (min_le_left 1 (‖z‖ ^ θ)) hpow).trans_eq ?_
    rw [mul_one]

/-- **The radial majorant has finite mass exactly when `2 < p < 2 + θ`.** -/
private theorem lintegral_momProfile_lt_top {p θ : ℝ} (hp : 2 < p) (hp' : p < 2 + θ) :
    ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (momProfile p θ (diamondNorm z)) < ⊤ := by
  have hhead : ∫⁻ t in Ioc (0 : ℝ) 1,
      4 * ENNReal.ofReal t * ENNReal.ofReal (momProfile p θ t) < ⊤ := by
    have hint : IntegrableOn (fun t : ℝ => 4 * t ^ (1 + (θ - p))) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        ((intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul 4)
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun t : ℝ => 4 * t ^ (1 + (θ - p)) :=
      ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
        have : (0 : ℝ) ≤ t := ht.1.le
        positivity
    have hcong : ∫⁻ t in Ioc (0 : ℝ) 1, 4 * ENNReal.ofReal t * ENNReal.ofReal (momProfile p θ t)
        = ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (4 * t ^ (1 + (θ - p))) := by
      refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      have ht0 : (0 : ℝ) < t := ht.1
      have hmul : t * t ^ (θ - p) = t ^ (1 + (θ - p)) := by
        rw [Real.rpow_add ht0, Real.rpow_one]
      have hprof : momProfile p θ t = t ^ (θ - p) := if_pos ht.2
      rw [hprof, ← hmul, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ENNReal.ofReal_mul ht0.le, ENNReal.ofReal_ofNat]
      ring
    rw [hcong, ← ofReal_integral_eq_lintegral_ofReal hint hnn]
    exact ENNReal.ofReal_lt_top
  have htail : ∫⁻ t in Ioi (1 : ℝ),
      4 * ENNReal.ofReal t * ENNReal.ofReal (momProfile p θ t) < ⊤ := by
    have hint : IntegrableOn (fun t : ℝ => 4 * t ^ (1 - p)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul 4
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun t : ℝ => 4 * t ^ (1 - p) :=
      ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
        have : (0 : ℝ) ≤ t := (zero_lt_one.trans ht).le
        positivity
    have hcong : ∫⁻ t in Ioi (1 : ℝ), 4 * ENNReal.ofReal t * ENNReal.ofReal (momProfile p θ t)
        = ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (4 * t ^ (1 - p)) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
      have hmul : t ^ (-p) * t = t ^ (1 - p) := by
        rw [show (1 : ℝ) - p = -p + 1 from by ring, Real.rpow_add ht0, Real.rpow_one]
      have hprof : momProfile p θ t = t ^ (-p) := if_neg (not_le.2 (mem_Ioi.1 ht))
      rw [hprof, ← hmul, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _), ENNReal.ofReal_ofNat]
      ring
    rw [hcong, ← ofReal_integral_eq_lintegral_ofReal hint hnn]
    exact ENNReal.ofReal_lt_top
  rw [lintegral_comp_diamondNorm (g := fun t : ℝ => ENNReal.ofReal (momProfile p θ t))
      (ENNReal.measurable_ofReal.comp (measurable_momProfile p θ)),
    ← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1),
    lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same]
  exact ENNReal.add_lt_top.2 ⟨hhead, htail⟩

/-- **The Lévy moment condition for the model singularity, with a fractional weight.** For
`0 < θ` and `2 < p < 2 + θ` the function `z ↦ diamondNorm z ^ (−p) · min(1, ‖z‖^θ)` is integrable
on the plane. Both bounds are sharp for this integrand: `p < 2 + θ` is what makes the singularity
at the origin integrable after the gain of `θ` powers from `min(1, ‖z‖^θ) ≤ ‖z‖^θ`, and `p > 2` is
what makes the tail integrable. -/
theorem integrable_diamondRpow_mul_min_one_rpow {p θ : ℝ} (hθ : 0 < θ) (hp : 2 < p)
    (hp' : p < 2 + θ) :
    Integrable fun z : Fin 2 → ℝ => diamondNorm z ^ (-p) * min 1 (‖z‖ ^ θ) := by
  refine ⟨((measurable_diamondNorm.pow_const _).mul
    (measurable_const.min (measurable_norm.pow_const _))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (.of_forall fun z =>
    mul_nonneg (Real.rpow_nonneg (diamondNorm_nonneg z) _)
      (le_min zero_le_one (Real.rpow_nonneg (norm_nonneg z) θ)))]
  refine lt_of_le_of_lt (lintegral_mono fun z => ?_) (lintegral_momProfile_lt_top hp hp')
  exact ENNReal.ofReal_le_ofReal (momIntegrand_le hθ p z)

/-- **The Lévy moment condition for the model singularity.** For `2 < p < 3` the function
`z ↦ diamondNorm z ^ (−p) · min(1, ‖z‖)` is integrable on the plane; this is the `θ = 1` case of
`integrable_diamondRpow_mul_min_one_rpow`, and it is exactly the hypothesis `hgmom` of
`CenteredMaximal.convolution_le_of_eq_zero_fp`. The generator density of `fracKernel` has
`p = 12/5` at the origin and `p = 11/5` at infinity, both inside `(2, 3)`. -/
theorem integrable_diamondRpow_mul_min_one {p : ℝ} (hp : 2 < p) (hp' : p < 3) :
    Integrable fun z : Fin 2 → ℝ => diamondNorm z ^ (-p) * min 1 ‖z‖ := by
  have h := integrable_diamondRpow_mul_min_one_rpow (θ := 1) one_pos hp (by linarith)
  simpa only [Real.rpow_one] using h

/-- **The moment condition for any density caught between two model singularities.** A density
behaving like `r^{−p}` at the origin and like `r^{−q}` at infinity, with both exponents in
`(2, 2 + θ)`, is dominated by `A (r^{−p} + r^{−q})`, and that is enough. Our generator density has
`p = 12/5` and `q = 11/5`, and the relevant weights are `θ = 1` for `hgmom` and `θ = 3/5` for the
modulus of continuity. -/
theorem integrable_mul_min_one_rpow_of_le {g : (Fin 2 → ℝ) → ℝ} {A p q θ : ℝ} (hgm : Measurable g)
    (hg₀ : ∀ z, 0 ≤ g z) (hθ : 0 < θ) (hp : 2 < p) (hp' : p < 2 + θ) (hq : 2 < q)
    (hq' : q < 2 + θ) (hg : ∀ z, g z ≤ A * (diamondNorm z ^ (-p) + diamondNorm z ^ (-q))) :
    Integrable fun z : Fin 2 → ℝ => g z * min 1 (‖z‖ ^ θ) := by
  have hmaj : Integrable fun z : Fin 2 → ℝ =>
      A * (diamondNorm z ^ (-p) * min 1 (‖z‖ ^ θ))
        + A * (diamondNorm z ^ (-q) * min 1 (‖z‖ ^ θ)) :=
    ((integrable_diamondRpow_mul_min_one_rpow hθ hp hp').const_mul A).add
      ((integrable_diamondRpow_mul_min_one_rpow hθ hq hq').const_mul A)
  have hm : Measurable fun z : Fin 2 → ℝ => g z * min 1 (‖z‖ ^ θ) :=
    hgm.mul (measurable_const.min (measurable_norm.pow_const _))
  refine hmaj.mono' hm.aestronglyMeasurable (.of_forall fun z => ?_)
  have hmin0 : 0 ≤ min 1 (‖z‖ ^ θ) := le_min zero_le_one (Real.rpow_nonneg (norm_nonneg z) θ)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg₀ z) hmin0)]
  nlinarith [mul_le_mul_of_nonneg_right (hg z) hmin0]

/-- The `θ = 1` specialisation, in the shape `hgmom` of `convolution_le_of_eq_zero_fp` asks for. -/
theorem integrable_mul_min_one_of_le {g : (Fin 2 → ℝ) → ℝ} {A p q : ℝ} (hgm : Measurable g)
    (hg₀ : ∀ z, 0 ≤ g z) (hp : 2 < p) (hp' : p < 3) (hq : 2 < q) (hq' : q < 3)
    (hg : ∀ z, g z ≤ A * (diamondNorm z ^ (-p) + diamondNorm z ^ (-q))) :
    Integrable fun z : Fin 2 → ℝ => g z * min 1 ‖z‖ := by
  have h := integrable_mul_min_one_rpow_of_le (θ := 1) hgm hg₀ one_pos hp (by linarith) hq
    (by linarith) hg
  simpa only [Real.rpow_one] using h

/-- The moment condition at the exponent `12/5` of the origin, with the weight `min(1, ‖z‖)`. -/
theorem integrable_diamondRpow_mul_min_one_twelve_fifths :
    Integrable fun z : Fin 2 → ℝ => diamondNorm z ^ (-(12 / 5 : ℝ)) * min 1 ‖z‖ :=
  integrable_diamondRpow_mul_min_one (by norm_num) (by norm_num)

/-- The moment condition at the exponent `11/5` of infinity, with the weight `min(1, ‖z‖)`. -/
theorem integrable_diamondRpow_mul_min_one_eleven_fifths :
    Integrable fun z : Fin 2 → ℝ => diamondNorm z ^ (-(11 / 5 : ℝ)) * min 1 ‖z‖ :=
  integrable_diamondRpow_mul_min_one (by norm_num) (by norm_num)

/-- **The moment condition at `θ = 3/5` and the origin exponent `12/5`**, the numerical case of
`hgconv_of_modulus` for the obstacle solution: the radial exponent is
`1 − 12/5 + 3/5 = −4/5 > −1`, so the integral converges. -/
theorem integrable_diamondRpow_mul_min_one_rpow_twelve_fifths :
    Integrable fun z : Fin 2 → ℝ =>
      diamondNorm z ^ (-(12 / 5 : ℝ)) * min 1 (‖z‖ ^ (3 / 5 : ℝ)) :=
  integrable_diamondRpow_mul_min_one_rpow (by norm_num) (by norm_num) (by norm_num)

/-- **The moment condition at `θ = 3/5` and the infinity exponent `11/5`**: the radial exponent of
the tail is `1 − 11/5 = −6/5 < −1`. -/
theorem integrable_diamondRpow_mul_min_one_rpow_eleven_fifths :
    Integrable fun z : Fin 2 → ℝ =>
      diamondNorm z ^ (-(11 / 5 : ℝ)) * min 1 (‖z‖ ^ (3 / 5 : ℝ)) :=
  integrable_diamondRpow_mul_min_one_rpow (by norm_num) (by norm_num) (by norm_num)

/-! ### A sufficient condition for the joint integrability hypothesis `hgconv`

`CenteredMaximal.convolution_le_of_eq_zero_fp` asks for the joint integrability, in `(x, z)`, of
`g z ((u (x − z) − u x) w x)` for every test function `w`. This cannot be deduced from `u ∈ L¹`
alone: the `z`-integral of `|u(· − z) − u|` must go to zero fast enough as `z → 0` to beat the
singularity of `g`. A fractional `L¹` modulus of continuity on `u`, which is what the obstacle
solution has, is exactly the right input. -/

/-- **`hgconv` from an `L¹` modulus of continuity.** If the increments of `u` satisfy
`∫ |u(x − z) − u x| dx ≤ C min(1, ‖z‖^θ)` and the density carries the matching moment
`∫ g(z) min(1, ‖z‖^θ) dz < ∞`, then the joint integrability hypothesis `hgconv` of
`CenteredMaximal.convolution_le_of_eq_zero_fp` holds. Tonelli turns the product integral round so
that the `x`-fibre comes first; there `w` is replaced by its sup bound and the modulus applies,
leaving the `z`-integral to `hgmom`.

For the certificate this is used with `θ = 3/5`, half the fractional order: with
`g ∼ r^{−12/5}` the radial exponent near the origin is `1 − 12/5 + 3/5 = −4/5 > −1`, so the moment
converges — see `integrable_diamondRpow_mul_min_one_rpow_twelve_fifths`. Proving that the obstacle
solution *has* this modulus of continuity is a separate matter, not addressed here. -/
theorem hgconv_of_modulus {g u : (Fin 2 → ℝ) → ℝ} {θ C : ℝ} (hC : 0 ≤ C) (hgm : Measurable g)
    (hg₀ : ∀ z, 0 ≤ g z) (hum : Measurable u) (huint : Integrable u)
    (hmod : ∀ z, ∫ x, |u (x - z) - u x| ≤ C * min 1 (‖z‖ ^ θ))
    (hgmom : Integrable fun z => g z * min 1 (‖z‖ ^ θ)) :
    ∀ w : (Fin 2 → ℝ) → ℝ, IsTestFunction w →
      Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        g p.2 * ((u (p.1 - p.2) - u p.1) * w p.1)) (volume.prod volume) := by
  intro w hw
  obtain ⟨Cw, hCw⟩ := hw.continuous.bounded_above_of_compact_support hw.2
  have hmin0 : ∀ z : Fin 2 → ℝ, 0 ≤ min 1 (‖z‖ ^ θ) := fun z =>
    le_min zero_le_one (Real.rpow_nonneg (norm_nonneg z) θ)
  have hFm : Measurable fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      g p.2 * ((u (p.1 - p.2) - u p.1) * w p.1) :=
    (hgm.comp measurable_snd).mul
      (((hum.comp (measurable_fst.sub measurable_snd)).sub (hum.comp measurable_fst)).mul
        (hw.continuous.measurable.comp measurable_fst))
  refine ⟨hFm.aestronglyMeasurable, ?_⟩
  have hmom : ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (g z * min 1 (‖z‖ ^ θ)) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal
      (.of_forall fun z => mul_nonneg (hg₀ z) (hmin0 z))).1 hgmom.hasFiniteIntegral
  have hbound : ∀ z : Fin 2 → ℝ,
      ∫⁻ x : Fin 2 → ℝ, ‖g z * ((u (x - z) - u x) * w x)‖ₑ
        ≤ ENNReal.ofReal Cw * ENNReal.ofReal C * ENNReal.ofReal (g z * min 1 (‖z‖ ^ θ)) := by
    intro z
    have hv : Integrable fun x : Fin 2 → ℝ => u (x - z) - u x := (huint.comp_sub_right z).sub huint
    have hstep : ∀ x : Fin 2 → ℝ, ‖g z * ((u (x - z) - u x) * w x)‖ₑ
        ≤ (‖g z‖ₑ * ENNReal.ofReal Cw) * ‖u (x - z) - u x‖ₑ := by
      intro x
      have hwx : ‖w x‖ₑ ≤ ENNReal.ofReal Cw := by
        rw [← ofReal_norm (w x)]
        exact ENNReal.ofReal_le_ofReal (hCw x)
      calc ‖g z * ((u (x - z) - u x) * w x)‖ₑ
          = ‖g z‖ₑ * (‖u (x - z) - u x‖ₑ * ‖w x‖ₑ) := by rw [enorm_mul, enorm_mul]
        _ ≤ ‖g z‖ₑ * (‖u (x - z) - u x‖ₑ * ENNReal.ofReal Cw) := by gcongr
        _ = (‖g z‖ₑ * ENNReal.ofReal Cw) * ‖u (x - z) - u x‖ₑ := by ring
    calc ∫⁻ x : Fin 2 → ℝ, ‖g z * ((u (x - z) - u x) * w x)‖ₑ
        ≤ ∫⁻ x : Fin 2 → ℝ, (‖g z‖ₑ * ENNReal.ofReal Cw) * ‖u (x - z) - u x‖ₑ :=
          lintegral_mono hstep
      _ = (‖g z‖ₑ * ENNReal.ofReal Cw) * ∫⁻ x : Fin 2 → ℝ, ‖u (x - z) - u x‖ₑ :=
          lintegral_const_mul' _ _ (by finiteness)
      _ = (‖g z‖ₑ * ENNReal.ofReal Cw) * ENNReal.ofReal (∫ x, ‖u (x - z) - u x‖) := by
          rw [ofReal_integral_norm_eq_lintegral_enorm hv]
      _ ≤ (‖g z‖ₑ * ENNReal.ofReal Cw) * ENNReal.ofReal (C * min 1 (‖z‖ ^ θ)) := by
          gcongr
          simpa only [Real.norm_eq_abs] using hmod z
      _ = ENNReal.ofReal Cw * ENNReal.ofReal C * ENNReal.ofReal (g z * min 1 (‖z‖ ^ θ)) := by
          rw [Real.enorm_eq_ofReal (hg₀ z), ENNReal.ofReal_mul hC, ENNReal.ofReal_mul (hg₀ z)]
          ring
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm' _ hFm.enorm]
  calc ∫⁻ z : Fin 2 → ℝ, ∫⁻ x : Fin 2 → ℝ, ‖g z * ((u (x - z) - u x) * w x)‖ₑ
      ≤ ∫⁻ z : Fin 2 → ℝ,
          ENNReal.ofReal Cw * ENNReal.ofReal C * ENNReal.ofReal (g z * min 1 (‖z‖ ^ θ)) :=
        lintegral_mono hbound
    _ = ENNReal.ofReal Cw * ENNReal.ofReal C *
          ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (g z * min 1 (‖z‖ ^ θ)) :=
        lintegral_const_mul' _ _ (by finiteness)
    _ < ⊤ := ENNReal.mul_lt_top (by finiteness) hmom

end

end CenteredMaximal.Fractional

end
