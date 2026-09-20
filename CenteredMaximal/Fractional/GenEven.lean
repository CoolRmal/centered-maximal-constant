/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.KernelPositivity
public import CenteredMaximal.Fractional.MajorBase

/-!
# The generator of the spline part is even in each coordinate separately

`CenteredMaximal.Fractional.fracKernel_abs` reduces the two pointwise bounds on the comparison
kernel to the closed first quadrant, because the kernel is unchanged by replacing each coordinate
by its absolute value.  Its spline half rests on `splineSum_abs`, the evenness of the **plain**
spline sum `∑ c_{ij} β(a − i) β(b − j)`.  The `α = 6/5` certificate, however, is not a statement
about the kernel: it is a statement about the *generator* of the kernel, whose spline half is the
sum of single-cell generators

`∑ c_{ij} (β^{(α)}(u − i) β(v − j) + β(u − i) β^{(α)}(v − j))`,   `β^{(α)} = jumpGen1 (6/5) β`,

produced by `jumpGen_fracKernel_sub_base`.  This is a *different* function of `(u, v)`, and
`splineSum_abs` says nothing about it.  The leaf certificates are stated on the grid coordinates
`u = 16 z₀`, `v = 16 z₁` of the closed first quadrant, so the assembly needs precisely the
generator analogue `splineGen |u| |v| = splineGen u v`, and that is what this file supplies.

## Why evenness of the generator needs no analysis

The one nontrivial input is that `jumpGen1 α φ` is even whenever `φ` is.  This is *not* an
integrability statement and needs no hypothesis beyond the symmetry of `φ`.  Writing
`jumpGen1 α φ x = ∫ (φ(x + s) + φ(x − s) − 2 φ(x)) |s|^{−(1+α)} ds`, the substitutions
`−x + s = −(x − s)`, `−x − s = −(x + s)` and the evenness of `φ` turn the integrand at `−x` into
the integrand at `x` *for every single `s`*: the second difference is symmetric in `±s`, so
reflecting the base point merely exchanges the two forward and backward increments.  The two
integrands are therefore equal as functions, and the two integrals are equal by `congrArg` alone —
no integrability side condition, and in particular the identity holds even at points and exponents
where both Bochner integrals are junk-valued `0`.  Once that is known, the cell bookkeeping is
identical to `splineSum_neg_fst` / `splineSum_neg_snd`: the reflection moves the sign onto the cell
index, and `perm_fracCells_flipFst` / `perm_fracCells_flipSnd` say that the sign flip permutes the
`1201` cells of the certificate.

## Main results

* `jumpGen1_neg_of_even`: **the jump generator of an even function is even**, by pointwise equality
  of the two integrands.
* `splineGen`, `splineGen_eq_finsetSum`: the spline half of the generator as a **list** sum over
  `fracCells`, exactly parallel to `splineSum`, together with its identification with the
  `Finset` sum over `fracCellFinset` that `jumpGen_fracKernel_sub_base` and the leaf lemmas use.
  The list form is what makes the permutation argument available; the `Finset` form is what the
  rest of the development consumes.
* `splineGen_neg_fst`, `splineGen_neg_snd`, `splineGen_abs`: **the generator symmetry.**  The
  last is the form the certificate consumes, matching `splineSum_abs` for the plain spline sum.
-/

@[expose] public section

noncomputable section

open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### The jump generator of an even function -/

/-- **The jump generator of an even function is even.**  The second difference
`φ(x + s) + φ(x − s) − 2 φ(x)` is symmetric in `s`, so replacing `x` by `−x` and using
`φ(−y) = φ(y)` exchanges the forward and backward increments and fixes the base term: the two
integrands agree at every `s`.  Hence no integrability hypothesis is needed. -/
theorem jumpGen1_neg_of_even {α : ℝ} {φ : ℝ → ℝ} (hφ : ∀ y : ℝ, φ (-y) = φ y) (x : ℝ) :
    CenteredMaximal.jumpGen1 α φ (-x) = CenteredMaximal.jumpGen1 α φ x := by
  have h : ∀ s : ℝ, (φ (-x + s) + φ (-x - s) - 2 * φ (-x)) * |s| ^ (-(1 + α))
      = (φ (x + s) + φ (x - s) - 2 * φ x) * |s| ^ (-(1 + α)) := by
    intro s
    rw [show -x + s = -(x - s) from by ring, show -x - s = -(x + s) from by ring, hφ (x - s),
      hφ (x + s), hφ x]
    ring
  simp only [CenteredMaximal.jumpGen1]
  exact congrArg _ (funext h)

/-! ### The spline half of the generator -/

/-- **The spline half of the generator of the comparison kernel**, as a list sum over the `1201`
cells of the certificate.  Each cell contributes the generator of its tensor product, which by the
product rule for a second-order difference operator is `β^{(α)} ⊗ β + β ⊗ β^{(α)}`.  The arguments
are the grid coordinates `u = 16 z₀`, `v = 16 z₁`. -/
def splineGen (u v : ℝ) : ℝ :=
  (fracCells.map fun p => fracCoeff p.2 *
    (jumpGen1 (6 / 5) bspline (u - p.1.1) * bspline (v - p.1.2)
      + bspline (u - p.1.1) * jumpGen1 (6 / 5) bspline (v - p.1.2))).sum

/-- **The spline half of the generator as a `Finset` sum.**  The cell indices of `fracCells` are
pairwise distinct (`nodup_fracCells_keys`), so the list sum collapses onto `fracCellFinset` with
the coefficient function `fracCellCoeff`; this is the shape produced by
`jumpGen_fracKernel_sub_base` and consumed by the leaf lemmas. -/
theorem splineGen_eq_finsetSum (u v : ℝ) :
    splineGen u v = ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
      (jumpGen1 (6 / 5) bspline (u - ij.1) * bspline (v - ij.2)
        + bspline (u - ij.1) * jumpGen1 (6 / 5) bspline (v - ij.2)) := by
  rw [fracCellFinset, Finset.sum_image injOn_fst_fracCells,
    List.sum_toFinset _ nodup_fracCells, splineGen]
  exact congrArg List.sum (List.map_congr_left fun p hp => by rw [fracCellCoeff_eq hp])

/-! ### The generator symmetry -/

/-- Reflecting the argument of the B-spline moves the sign onto the cell index.  This restates the
private helper of `CenteredMaximal.Fractional.MajorBase`. -/
private theorem bspline_neg_shift (c : ℤ) (x : ℝ) :
    bspline (-x - (c : ℝ)) = bspline (x - ((-c : ℤ) : ℝ)) := by
  rw [show x - ((-c : ℤ) : ℝ) = -(-x - (c : ℝ)) from by push_cast; ring, bspline_neg]

/-- The same shift rule for the one-dimensional generator of the B-spline, which is even because
`β` is (`bspline_neg`) and `jumpGen1_neg_of_even`. -/
private theorem jumpGen1_bspline_neg_shift (c : ℤ) (x : ℝ) :
    jumpGen1 (6 / 5) bspline (-x - (c : ℝ)) = jumpGen1 (6 / 5) bspline (x - ((-c : ℤ) : ℝ)) := by
  rw [show x - ((-c : ℤ) : ℝ) = -(-x - (c : ℝ)) from by push_cast; ring,
    jumpGen1_neg_of_even bspline_neg]

/-- **The spline half of the generator is even in its first argument.**  The reflection moves the
sign onto the first cell index, and `perm_fracCells_flipFst` says that the resulting relabelling
permutes the cells of the certificate. -/
theorem splineGen_neg_fst (u v : ℝ) : splineGen (-u) v = splineGen u v := by
  have h : ∀ p : (ℤ × ℤ) × ℤ,
      fracCoeff p.2 * (jumpGen1 (6 / 5) bspline (-u - p.1.1) * bspline (v - p.1.2)
          + bspline (-u - p.1.1) * jumpGen1 (6 / 5) bspline (v - p.1.2))
        = ((fun q : (ℤ × ℤ) × ℤ =>
            fracCoeff q.2 * (jumpGen1 (6 / 5) bspline (u - q.1.1) * bspline (v - q.1.2)
              + bspline (u - q.1.1) * jumpGen1 (6 / 5) bspline (v - q.1.2))) ∘ flipFst) p := by
    intro p
    simp only [Function.comp_apply, flipFst, negFst]
    rw [bspline_neg_shift p.1.1 u, jumpGen1_bspline_neg_shift p.1.1 u]
  rw [splineGen, splineGen, List.map_congr_left fun p _ => h p, ← List.map_map]
  exact (perm_fracCells_flipFst.map _).sum_eq

/-- **The spline half of the generator is even in its second argument**, by the same argument with
`perm_fracCells_flipSnd`. -/
theorem splineGen_neg_snd (u v : ℝ) : splineGen u (-v) = splineGen u v := by
  have h : ∀ p : (ℤ × ℤ) × ℤ,
      fracCoeff p.2 * (jumpGen1 (6 / 5) bspline (u - p.1.1) * bspline (-v - p.1.2)
          + bspline (u - p.1.1) * jumpGen1 (6 / 5) bspline (-v - p.1.2))
        = ((fun q : (ℤ × ℤ) × ℤ =>
            fracCoeff q.2 * (jumpGen1 (6 / 5) bspline (u - q.1.1) * bspline (v - q.1.2)
              + bspline (u - q.1.1) * jumpGen1 (6 / 5) bspline (v - q.1.2))) ∘ flipSnd) p := by
    intro p
    simp only [Function.comp_apply, flipSnd, negSnd]
    rw [bspline_neg_shift p.1.2 v, jumpGen1_bspline_neg_shift p.1.2 v]
  rw [splineGen, splineGen, List.map_congr_left fun p _ => h p, ← List.map_map]
  exact (perm_fracCells_flipSnd.map _).sum_eq

/-- **The form the certificate consumes.**  Since the generator is even in each grid coordinate
separately, it only has to be certified on the closed first quadrant `u, v ≥ 0`, exactly as
`splineSum_abs` does for the plain spline sum. -/
theorem splineGen_abs (u v : ℝ) : splineGen |u| |v| = splineGen u v := by
  rcases abs_cases u with ⟨hu, _⟩ | ⟨hu, _⟩ <;> rcases abs_cases v with ⟨hv, _⟩ | ⟨hv, _⟩ <;>
    rw [hu, hv] <;>
    simp only [splineGen_neg_fst, splineGen_neg_snd]

end CenteredMaximal.Fractional

end

end
