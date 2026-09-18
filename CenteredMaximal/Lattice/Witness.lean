/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Lattice.Constants
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred

/-!
# Level-one witnesses for the weighted lattice

The atom with index `(c, r) ∈ ℤ²` sits at `(c · hgap, r · vgap)` and has mass `colWeight c`,
which is `1` for even `c` and `heavy` for odd `c`. A *witness* for the point `(x, y)` is a side
`L ≥ 1` and a finite set `A` of atoms, all within sup-distance `L/2` of `(x, y)`, of total mass at
least `L²`: the closed square of side `L` centred at `(x, y)` then has average at least `1`.

Six explicit witnesses cover the quarter cell `[0, hgap] × [0, vgap/2]` except one open slot
(`exists_isWitness_of_nonneg`). Reflections in the two axes and translations by the period
`(2 hgap, vgap)` preserve the atom masses, so they transport witnesses to the whole plane.
-/

@[expose] public section

noncomputable section

open Finset

namespace CenteredMaximal.Lattice

/-- The mass of an atom in column `c`: `1` if `c` is even, `heavy` if `c` is odd. -/
def colWeight (c : ℤ) : ℝ := if Even c then 1 else heavy

/-- `(L, A)` witnesses level one at `(x, y)`: `L ≥ 1`, the atoms of `A` have total mass at least
`L²`, and every atom of `A` lies in the closed square of side `L` centred at `(x, y)`. -/
def IsWitness (x y L : ℝ) (A : Finset (ℤ × ℤ)) : Prop :=
  1 ≤ L ∧ L ^ 2 ≤ ∑ p ∈ A, colWeight p.1 ∧
    ∀ p ∈ A, |p.1 * hgap - x| ≤ L / 2 ∧ |p.2 * vgap - y| ≤ L / 2

/-- The atoms that a witness for a point of the period cell with index `(k, l)` may use. -/
def nearBox (k l : ℤ) : Finset (ℤ × ℤ) :=
  Icc (2 * k - 2) (2 * k + 2) ×ˢ Icc (l - 1) (l + 1)

/-- Reflection of atom indices in the vertical axis. -/
def negFst : ℤ × ℤ ≃ ℤ × ℤ := (Equiv.neg ℤ).prodCongr (Equiv.refl ℤ)

/-- Reflection of atom indices in the horizontal axis. -/
def negSnd : ℤ × ℤ ≃ ℤ × ℤ := (Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)

theorem colWeight_neg (c : ℤ) : colWeight (-c) = colWeight c := by
  sorry

theorem colWeight_add_two_mul (c k : ℤ) : colWeight (c + 2 * k) = colWeight c := by
  sorry

theorem IsWitness.neg_fst {x y L : ℝ} {A : Finset (ℤ × ℤ)} (hw : IsWitness x y L A) :
    IsWitness (-x) y L (A.map negFst.toEmbedding) := by
  sorry

theorem IsWitness.neg_snd {x y L : ℝ} {A : Finset (ℤ × ℤ)} (hw : IsWitness x y L A) :
    IsWitness x (-y) L (A.map negSnd.toEmbedding) := by
  sorry

theorem IsWitness.translate {x y L : ℝ} {A : Finset (ℤ × ℤ)} (hw : IsWitness x y L A)
    (k l : ℤ) :
    IsWitness (x + 2 * k * hgap) (y + l * vgap) L (A.map (Equiv.addRight (2 * k, l)).toEmbedding) := by
  sorry

theorem map_negFst_subset_nearBox {A : Finset (ℤ × ℤ)} (hA : A ⊆ nearBox 0 0) :
    A.map negFst.toEmbedding ⊆ nearBox 0 0 := by
  sorry

theorem map_negSnd_subset_nearBox {A : Finset (ℤ × ℤ)} (hA : A ⊆ nearBox 0 0) :
    A.map negSnd.toEmbedding ⊆ nearBox 0 0 := by
  sorry

theorem map_addRight_subset_nearBox {A : Finset (ℤ × ℤ)} (hA : A ⊆ nearBox 0 0) (k l : ℤ) :
    A.map (Equiv.addRight (2 * k, l)).toEmbedding ⊆ nearBox k l := by
  sorry

/-! ### The six witnesses -/

/-- The light atom at the origin, side `1`. -/
theorem isWitness_light {x y : ℝ} (hx : |x| ≤ 1 / 2) (hy : |y| ≤ 1 / 2) :
    IsWitness x y 1 {(0, 0)} := by
  sorry

/-- Heavy, light, heavy atoms in two rows, side `2 hgap + 1`. -/
theorem isWitness_hlh2 {x y : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) (hy : 1 / 2 ≤ y)
    (hy' : y ≤ vgap / 2) :
    IsWitness x y (2 * hgap + 1) {(-1, 0), (0, 0), (1, 0), (-1, 1), (0, 1), (1, 1)} := by
  sorry

/-- A light and a heavy atom in one row, side `root`. -/
theorem isWitness_lh1 {x y : ℝ} (hx : 1 / 2 ≤ x) (hx' : x ≤ root / 2) (hy : 0 ≤ y)
    (hy' : y ≤ root / 2) :
    IsWitness x y root {(0, 0), (1, 0)} := by
  sorry

/-- A light and a heavy atom in two rows, side `sideLH2`. -/
theorem isWitness_lh2 {x y : ℝ} (hx : 1 / 2 ≤ x) (hx' : x ≤ sideLH2 / 2)
    (hy : vgap - sideLH2 / 2 ≤ y) (hy' : y ≤ vgap / 2) :
    IsWitness x y sideLH2 {(0, 0), (1, 0), (0, 1), (1, 1)} := by
  sorry

/-- One heavy atom, side `sideH1`. -/
theorem isWitness_h1 {x y : ℝ} (hx : hgap - sideH1 / 2 ≤ x) (hx' : x ≤ hgap) (hy : 0 ≤ y)
    (hy' : y ≤ sideH1 / 2) :
    IsWitness x y sideH1 {(1, 0)} := by
  sorry

/-- Light, heavy, light atoms in two rows, side `sideLHL2`. -/
theorem isWitness_lhl2 {x y : ℝ} (hx : 2 * hgap - sideLHL2 / 2 ≤ x) (hx' : x ≤ hgap)
    (hy : vgap - sideLHL2 / 2 ≤ y) (hy' : y ≤ vgap / 2) :
    IsWitness x y sideLHL2 {(0, 0), (1, 0), (2, 0), (0, 1), (1, 1), (2, 1)} := by
  sorry

/-! ### Coverage -/

/-- The six witnesses cover the quarter cell `[0, hgap] × [0, vgap/2]` except the open slot
`(root/2, 2 hgap - sideLHL2/2) × (sideH1/2, vgap - sideLH2/2)`. -/
theorem exists_isWitness_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hx' : x ≤ hgap) (hy : 0 ≤ y)
    (hy' : y ≤ vgap / 2)
    (hslot : ¬ (root / 2 < x ∧ x < 2 * hgap - sideLHL2 / 2 ∧ sideH1 / 2 < y ∧
      y < vgap - sideLH2 / 2)) :
    ∃ L A, A ⊆ nearBox 0 0 ∧ IsWitness x y L A := by
  sorry

/-- Coverage of the period cell centred at the origin, by reflection of the quarter cell. -/
theorem exists_isWitness_of_abs {x y : ℝ} (hx : |x| ≤ hgap) (hy : |y| ≤ vgap / 2)
    (hslot : ¬ (root / 2 < |x| ∧ |x| < 2 * hgap - sideLHL2 / 2 ∧ sideH1 / 2 < |y| ∧
      |y| < vgap - sideLH2 / 2)) :
    ∃ L A, A ⊆ nearBox 0 0 ∧ IsWitness x y L A := by
  sorry

end CenteredMaximal.Lattice
