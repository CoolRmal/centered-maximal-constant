/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.KernelMass
public import CenteredMaximal.Fractional.MajorPoly

/-!
# The three global inputs of the majorization certificate

The majorization certificate of the `α = 6/5` comparison kernel `fracKernel` reduces the two
pointwise bounds `0 ≤ K` and `1 ≤ K` on the unit diamond to finitely many polynomial bounds on
triangles.  Three facts are needed *before* any triangle is inspected, and this file proves them.

## Main results

* `rpow_neg_tangent`: **the convexity minorant**, the mathematical heart of the certificate.  For
  `1 ≤ α` and `q, r > 0`,
  `q ^ (-α) + α · q ^ (-α-1) · (q - r) ≤ r ^ (-α)`:
  the tangent line to the convex decreasing function `r ↦ r ^ (-α)` at any radius `q` lies below
  it everywhere.  Since the diamond radius `r = |z₀| + |z₁|` is *affine* on a triangle inside one
  quadrant, this replaces the base of the kernel by an affine function with no loss at `r = q` —
  which is what makes the certificate exact.  The proof is Bernoulli's inequality
  `one_add_mul_self_le_rpow_one_add` applied to `y⁻¹`, whose error term is `α (y-1)²/y`
  (`one_sub_mul_le_rpow_neg`); no derivative and no convexity API is used.
* `tangent_sub_le_truncBase`: the same bound for the truncated base `(r^{-α} − R^{-α})₊`, which is
  only larger than `r^{-α} − R^{-α}`.
* `fracKernel_abs`: **the diamond symmetry.**  `K z = K (|z₀|, |z₁|)`, so only the closed first
  quadrant has to be certified.  The base is a function of `diamondNorm` alone, and the spline part
  is invariant because `β` is even (`bspline_neg`) and the cell list `fracCells` is carried into a
  permutation of itself by each of the two sign flips — a structural fact about `diamondOrbit`,
  proved with `List.dedup_map_of_injective` and four transpositions, with no `decide` on the `1201`
  cells.
* `fracKernel_eq_zero_of_le`: **the exterior region.**  `K` vanishes on `diamondNorm z ≥ 7/4`.
  The base vanishes because `7/4` is its truncation radius, and every spline cell vanishes because
  `|i| + |j| ≤ 24` over all `1201` cells (a `169`-row check on the orbit representatives), while a
  nonzero `β(16z₀ − i) β(16z₁ − j)` forces `16 (|z₀| + |z₁|) < 4 + |i| + |j| ≤ 28`.
-/

@[expose] public section

noncomputable section

open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### The convexity minorant -/

/-- **Bernoulli's inequality at a negative exponent.**  For `1 ≤ α` and `y > 0`,
`1 - α (y - 1) ≤ y ^ (-α)`: the tangent line at `y = 1` to the convex function `y ↦ y ^ (-α)`.
The proof applies the standard Bernoulli inequality to `y⁻¹`, which overshoots the tangent line by
exactly `α (y - 1)² / y`. -/
theorem one_sub_mul_le_rpow_neg {α : ℝ} (hα : 1 ≤ α) {y : ℝ} (hy : 0 < y) :
    1 - α * (y - 1) ≤ y ^ (-α) := by
  have hyi : 0 < y⁻¹ := inv_pos.2 hy
  have hs : (-1 : ℝ) ≤ y⁻¹ - 1 := by linarith
  have hb := one_add_mul_self_le_rpow_one_add hs hα
  rw [show (1 : ℝ) + (y⁻¹ - 1) = y⁻¹ from by ring, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le] at hb
  have hgap : 1 + α * (y⁻¹ - 1) - (1 - α * (y - 1)) = α * (y - 1) ^ 2 / y := by
    field_simp
    ring
  have hnn : 0 ≤ α * (y - 1) ^ 2 / y := by positivity
  linarith

/-- **The convexity minorant of the diamond power.**  For `1 ≤ α` and positive radii `q` and `r`,
the tangent line to `r ↦ r ^ (-α)` at `q` lies below the function:
`q ^ (-α) + α q ^ (-α-1) (q - r) ≤ r ^ (-α)`, with equality at `r = q`.

This is what the certificate spends on the base of the kernel.  On a triangle contained in one
quadrant the diamond radius `r = |z₀| + |z₁|` is an affine function of the coordinates, so the
left-hand side is affine, and taking `q` to be the largest radius on the triangle makes the
minorant exact at the far edge — where, on the triangles that meet the support boundary
`r = 7/4`, the certificate has no slack at all. -/
theorem rpow_neg_tangent {α : ℝ} (hα : 1 ≤ α) {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    q ^ (-α) + α * q ^ (-α - 1) * (q - r) ≤ r ^ (-α) := by
  have hqa : 0 < q ^ (-α) := Real.rpow_pos_of_pos hq _
  have hy : 0 < r / q := div_pos hr hq
  have hstep := one_sub_mul_le_rpow_neg hα hy
  have hsplit : r ^ (-α) = q ^ (-α) * (r / q) ^ (-α) := by
    rw [Real.div_rpow hr.le hq.le, mul_div_cancel₀]
    exact (Real.rpow_pos_of_pos hq _).ne'
  have hq1 : q ^ (-α - 1) = q ^ (-α) / q := by
    rw [Real.rpow_sub hq, Real.rpow_one]
  have hmul : q ^ (-α) * (1 - α * (r / q - 1)) ≤ q ^ (-α) * (r / q) ^ (-α) :=
    mul_le_mul_of_nonneg_left hstep hqa.le
  have hexp : q ^ (-α) * (1 - α * (r / q - 1)) = q ^ (-α) + α * (q ^ (-α) / q) * (q - r) := by
    field_simp
    ring
  rw [hsplit, hq1, ← hexp]
  exact hmul

/-- **The convexity minorant for the truncated base.**  The truncated base
`(r^{-α} − R^{-α})₊` is at least `r^{-α} − R^{-α}`, so the tangent minorant of `rpow_neg_tangent`
bounds it below after subtracting `R^{-α}`. -/
theorem tangent_sub_le_truncBase {α R : ℝ} (hα : 1 ≤ α) {z : Fin 2 → ℝ}
    (hz : 0 < diamondNorm z) {q : ℝ} (hq : 0 < q) :
    q ^ (-α) + α * q ^ (-α - 1) * (q - diamondNorm z) - R ^ (-α) ≤ truncBase α R z := by
  have h := rpow_neg_tangent hα hq hz
  have h2 : diamondNorm z ^ (-α) - R ^ (-α) ≤ truncBase α R z := le_max_left _ _
  linarith

/-! ### The diamond symmetry of the cell list -/

/-- Negating the first index of a cell. -/
def negFst (p : ℤ × ℤ) : ℤ × ℤ := (-p.1, p.2)

/-- Negating the second index of a cell. -/
def negSnd (p : ℤ × ℤ) : ℤ × ℤ := (p.1, -p.2)

theorem negFst_injective : Function.Injective negFst := by
  intro p q h
  simp only [negFst, Prod.mk.injEq, neg_inj] at h
  exact Prod.ext h.1 h.2

theorem negSnd_injective : Function.Injective negSnd := by
  intro p q h
  simp only [negSnd, Prod.mk.injEq, neg_inj] at h
  exact Prod.ext h.1 h.2

/-- Two adjacent transpositions of a list, with a permutation of the tail. -/
private theorem perm_swap2 {α : Type*} (a b : α) {t t' : List α} (h : t.Perm t') :
    (b :: a :: t).Perm (a :: b :: t') :=
  (List.Perm.swap a b t).trans ((h.cons b).cons a)

/-- Exchanging two adjacent blocks of length two, with a permutation of the tail. -/
private theorem perm_blocks {α : Type*} (a b c d : α) {t t' : List α} (h : t.Perm t') :
    (c :: d :: a :: b :: t).Perm (a :: b :: c :: d :: t') := by
  have h1 : (c :: d :: a :: b :: t).Perm (a :: b :: c :: d :: t) :=
    List.Perm.append_right t (List.perm_append_comm (l₁ := [c, d]) (l₂ := [a, b]))
  exact h1.trans ((((h.cons d).cons c).cons b).cons a)

/-- **Negating the first index permutes an orbit.**  The eight listed images of `(i, j)` are
carried into each other in adjacent pairs, and `List.dedup` of a permutation is a permutation. -/
theorem perm_diamondOrbit_negFst (i j : ℤ) :
    ((diamondOrbit i j).map negFst).Perm (diamondOrbit i j) := by
  rw [diamondOrbit, ← List.dedup_map_of_injective negFst_injective]
  refine List.Perm.dedup ?_
  simp only [List.map_cons, List.map_nil, negFst, neg_neg]
  exact perm_swap2 _ _ (perm_swap2 _ _ (perm_swap2 _ _ (perm_swap2 _ _ (List.Perm.refl []))))

/-- **Negating the second index permutes an orbit.**  Here the eight images are carried into each
other by exchanging adjacent blocks of two. -/
theorem perm_diamondOrbit_negSnd (i j : ℤ) :
    ((diamondOrbit i j).map negSnd).Perm (diamondOrbit i j) := by
  rw [diamondOrbit, ← List.dedup_map_of_injective negSnd_injective]
  refine List.Perm.dedup ?_
  simp only [List.map_cons, List.map_nil, negSnd, neg_neg]
  exact perm_blocks _ _ _ _ (perm_blocks _ _ _ _ (List.Perm.refl []))

/-- Negating the first index of a cell, coefficient included. -/
def flipFst (p : (ℤ × ℤ) × ℤ) : (ℤ × ℤ) × ℤ := (negFst p.1, p.2)

/-- Negating the second index of a cell, coefficient included. -/
def flipSnd (p : (ℤ × ℤ) × ℤ) : (ℤ × ℤ) × ℤ := (negSnd p.1, p.2)

private theorem perm_flipAux {f : ℤ × ℤ → ℤ × ℤ}
    (hf : ∀ i j : ℤ, ((diamondOrbit i j).map f).Perm (diamondOrbit i j)) :
    (fracCells.map fun p => (f p.1, p.2)).Perm fracCells := by
  rw [fracCells, List.map_flatMap]
  refine List.Perm.flatMap_left _ fun o _ => ?_
  have h := (hf o.1 o.2.1).map fun q : ℤ × ℤ => (q, o.2.2)
  rw [List.map_map] at h
  simpa [Function.comp_def] using h

/-- **The cell list is carried into a permutation of itself by the first sign flip.** -/
theorem perm_fracCells_flipFst : (fracCells.map flipFst).Perm fracCells :=
  perm_flipAux perm_diamondOrbit_negFst

/-- **The cell list is carried into a permutation of itself by the second sign flip.** -/
theorem perm_fracCells_flipSnd : (fracCells.map flipSnd).Perm fracCells :=
  perm_flipAux perm_diamondOrbit_negSnd

/-! ### The symmetry of the kernel -/

/-- The spline part of the kernel, as a function of the two scaled coordinates. -/
def splineSum (a b : ℝ) : ℝ :=
  (fracCells.map fun p =>
    fracCoeff p.2 * (bspline (a - p.1.1) * bspline (b - p.1.2))).sum

/-- Reflecting the argument of the B-spline moves the sign onto the cell index. -/
private theorem bspline_neg_shift (c : ℤ) (x : ℝ) :
    bspline (-x - (c : ℝ)) = bspline (x - ((-c : ℤ) : ℝ)) := by
  rw [show x - ((-c : ℤ) : ℝ) = -(-x - (c : ℝ)) from by push_cast; ring, bspline_neg]

/-- The spline part is even in its first argument. -/
theorem splineSum_neg_fst (a b : ℝ) : splineSum (-a) b = splineSum a b := by
  have h : ∀ p : (ℤ × ℤ) × ℤ,
      fracCoeff p.2 * (bspline (-a - p.1.1) * bspline (b - p.1.2))
        = ((fun q : (ℤ × ℤ) × ℤ =>
            fracCoeff q.2 * (bspline (a - q.1.1) * bspline (b - q.1.2))) ∘ flipFst) p := by
    intro p
    simp only [Function.comp_apply, flipFst, negFst]
    rw [bspline_neg_shift p.1.1 a]
  rw [splineSum, splineSum, List.map_congr_left fun p _ => h p, ← List.map_map]
  exact (perm_fracCells_flipFst.map _).sum_eq

/-- The spline part is even in its second argument. -/
theorem splineSum_neg_snd (a b : ℝ) : splineSum a (-b) = splineSum a b := by
  have h : ∀ p : (ℤ × ℤ) × ℤ,
      fracCoeff p.2 * (bspline (a - p.1.1) * bspline (-b - p.1.2))
        = ((fun q : (ℤ × ℤ) × ℤ =>
            fracCoeff q.2 * (bspline (a - q.1.1) * bspline (b - q.1.2))) ∘ flipSnd) p := by
    intro p
    simp only [Function.comp_apply, flipSnd, negSnd]
    rw [bspline_neg_shift p.1.2 b]
  rw [splineSum, splineSum, List.map_congr_left fun p _ => h p, ← List.map_map]
  exact (perm_fracCells_flipSnd.map _).sum_eq

theorem splineSum_abs (a b : ℝ) : splineSum |a| |b| = splineSum a b := by
  rcases abs_cases a with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rcases abs_cases b with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
    rw [ha, hb] <;>
    simp only [splineSum_neg_fst, splineSum_neg_snd]

/-- The kernel written through `splineSum`. -/
theorem fracKernel_eq (z : Fin 2 → ℝ) :
    fracKernel z = fracBaseCoeff * truncBase (6 / 5) (7 / 4) z + splineSum (16 * z 0) (16 * z 1) :=
  rfl

/-- **The diamond symmetry.**  The kernel is unchanged by replacing each coordinate by its
absolute value, so the certificate only has to cover the closed first quadrant. -/
theorem fracKernel_abs (z : Fin 2 → ℝ) : fracKernel z = fracKernel fun i => |z i| := by
  have hd : diamondNorm (fun i => |z i|) = diamondNorm z := by
    simp only [diamondNorm, abs_abs]
  rw [fracKernel_eq, fracKernel_eq, truncBase, truncBase, hd]
  congr 1
  rw [show (16 : ℝ) * |z 0| = |16 * z 0| from by rw [abs_mul]; norm_num,
    show (16 : ℝ) * |z 1| = |16 * z 1| from by rw [abs_mul]; norm_num, splineSum_abs]

/-! ### The exterior region -/

set_option maxRecDepth 20000 in
/-- The `169` orbit representatives satisfy `i ≥ j ≥ 0`. -/
theorem fracOrbits_repr' : ∀ o ∈ fracOrbits, 0 ≤ o.2.1 ∧ o.2.1 ≤ o.1 := by decide

set_option maxRecDepth 20000 in
/-- **The support radius of the spline part**: every orbit representative has `i + j ≤ 24`, so
every cell of the certificate has `|i| + |j| ≤ 24`. -/
theorem fracOrbits_sum_le : ∀ o ∈ fracOrbits, o.1 + o.2.1 ≤ 24 := by decide

/-- The pair of absolute values is constant on an orbit. -/
theorem absAdd_of_mem_diamondOrbit {i j : ℤ} (hj : 0 ≤ j) (hji : j ≤ i) {p : ℤ × ℤ}
    (hp : p ∈ diamondOrbit i j) : |p.1| + |p.2| = i + j := by
  have hi : (0 : ℤ) ≤ i := hj.trans hji
  rw [diamondOrbit, List.mem_dedup] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [abs_of_nonneg hi, abs_of_nonneg hj] <;> ring

/-- **Every cell of the certificate lies within `|i| + |j| ≤ 24`.** -/
theorem fracCells_absAdd_le {p : (ℤ × ℤ) × ℤ} (hp : p ∈ fracCells) : |p.1.1| + |p.1.2| ≤ 24 := by
  rw [fracCells, List.mem_flatMap] at hp
  obtain ⟨o, ho, hp⟩ := hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  obtain ⟨h0, h1⟩ := fracOrbits_repr' o ho
  rw [absAdd_of_mem_diamondOrbit h0 h1 hq]
  exact fracOrbits_sum_le o ho

/-- A nonzero value of the B-spline forces its argument into `(−2, 2)`. -/
theorem abs_lt_two_of_bspline_ne_zero {x : ℝ} (h : bspline x ≠ 0) : |x| < 2 := by
  rw [abs_lt]
  refine ⟨?_, ?_⟩
  · by_contra hc
    exact h (bspline_of_le_neg_two (by linarith [not_lt.1 hc]))
  · by_contra hc
    exact h (bspline_of_two_le (not_lt.1 hc))

/-- **The kernel vanishes outside the diamond of radius `7/4`.**  The truncated base vanishes
there by definition, and a spline cell `(i, j)` can only contribute where
`16 (|z₀| + |z₁|) < 4 + |i| + |j| ≤ 28`. -/
theorem fracKernel_eq_zero_of_le {z : Fin 2 → ℝ} (hz : 7 / 4 ≤ diamondNorm z) :
    fracKernel z = 0 := by
  have hr : (0 : ℝ) < diamondNorm z := by linarith
  have hbase : truncBase (6 / 5 : ℝ) (7 / 4) z = 0 := by
    refine max_eq_right (sub_nonpos.2 ?_)
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hz (by norm_num)
  have hsp : ∀ x ∈ fracCells.map (fun p : (ℤ × ℤ) × ℤ =>
      fracCoeff p.2 * (bspline (16 * z 0 - p.1.1) * bspline (16 * z 1 - p.1.2))), x = 0 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    have hijZ : |p.1.1| + |p.1.2| ≤ 24 := fracCells_absAdd_le hp
    have hijR : |(p.1.1 : ℝ)| + |(p.1.2 : ℝ)| ≤ 24 := by
      have hc : ((|p.1.1| + |p.1.2| : ℤ) : ℝ) ≤ ((24 : ℤ) : ℝ) := Int.cast_le.2 hijZ
      push_cast at hc
      exact hc
    by_cases h0 : bspline (16 * z 0 - (p.1.1 : ℝ)) = 0
    · rw [h0, zero_mul, mul_zero]
    by_cases h1 : bspline (16 * z 1 - (p.1.2 : ℝ)) = 0
    · rw [h1, mul_zero, mul_zero]
    exfalso
    have b0 := abs_lt_two_of_bspline_ne_zero h0
    have b1 := abs_lt_two_of_bspline_ne_zero h1
    have e0 := abs_sub_abs_le_abs_sub (16 * z 0) ((p.1.1 : ℤ) : ℝ)
    have e1 := abs_sub_abs_le_abs_sub (16 * z 1) ((p.1.2 : ℤ) : ℝ)
    have a0 : |16 * z 0| = 16 * |z 0| := by rw [abs_mul]; norm_num
    have a1 : |16 * z 1| = 16 * |z 1| := by rw [abs_mul]; norm_num
    rw [a0] at e0
    rw [a1] at e1
    have hdn : diamondNorm z = |z 0| + |z 1| := rfl
    rw [hdn] at hz
    linarith
  rw [fracKernel, hbase, mul_zero, zero_add, List.sum_eq_zero hsp]

end CenteredMaximal.Fractional

end

end
