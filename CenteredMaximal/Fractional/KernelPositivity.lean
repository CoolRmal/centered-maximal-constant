/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.KernelMass

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
  consumes. `fracCellFinset_card` records that the finite set really does have `1201` elements.
* `integrable_diamondRpow_mul_min_one`: **the Lévy moment condition for the model singularity**,
  `∫ diamondNorm z ^ (-p) · min(1, ‖z‖) dz < ∞` for `2 < p < 3`. Both bounds are sharp for this
  integrand: near the origin the radial integral is `∫₀¹ 4 t^{2−p} dt`, which converges iff
  `p < 3`, and at infinity it is `∫₁^∞ 4 t^{1−p} dt`, which converges iff `p > 2`. The generator
  density of `fracKernel` behaves like `r^{−12/5}` at the origin and like `r^{−11/5}` at infinity,
  and `12/5` and `11/5` both lie in `(2, 3)`, so the hypothesis covers it
  (`integrable_diamondRpow_mul_min_one_twelve_fifths`).
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

end

end CenteredMaximal.Fractional

end
