/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Statement

/-!
# The constants of the weighted lattice

The extremal configuration is the periodic measure with columns at `x = i * hgap`, carrying mass
`1` for even `i` and mass `heavy` for odd `i`, and rows at `y = j * vgap` of unit weight. Its
parameters are determined by three edge collisions of witness rectangles; they reduce to the single
quadratic `3 u² - 4 u - 6 = 0` for `u = root = (2 + √22)/3`:

* `heavy = u² - 1 = (17 + 4√22)/9`, so a light and a heavy atom together weigh `u²`;
* `hgap = (1 + u)/2 = (5 + √22)/6` and `vgap = hgap + 1 = (11 + √22)/6`.

The witness squares use the sides `1`, `u`, `sideH1 = √heavy`, `sideLH2 = √2 · u`,
`sideLHL2 = √(2 (2 + heavy))` and `2 hgap + 1`. The level set misses, in each quadrant of the
period cell, one open slot of width `slotW` and height `slotH`, and
`phi = (2 hgap vgap - 4 slotW slotH) / (1 + heavy)`.

All numerical facts are proved from rational enclosures of `√2` and `√22`.
-/

@[expose] public section

noncomputable section

namespace CenteredMaximal.Lattice

/-- `u = (2 + √22)/3`, the positive root of `3u² - 4u - 6 = 0`. -/
def root : ℝ := (2 + √22) / 3

/-- The heavy mass `w = u² - 1 = (17 + 4√22)/9`. -/
def heavy : ℝ := root ^ 2 - 1

/-- The column spacing `h = (1 + u)/2 = (5 + √22)/6`. -/
def hgap : ℝ := (1 + root) / 2

/-- The row spacing `V = h + 1 = (11 + √22)/6`. -/
def vgap : ℝ := hgap + 1

/-- Side of the witness made of one heavy atom: `√w`. -/
def sideH1 : ℝ := √heavy

/-- Side of the witness made of a light and a heavy atom in two rows: `√(2(1 + w)) = √2 · u`. -/
def sideLH2 : ℝ := √2 * root

/-- Side of the witness made of light, heavy, light atoms in two rows: `√(2(2 + w))`. -/
def sideLHL2 : ℝ := √(2 * (2 + heavy))

/-- Width of the uncovered slot: `2h - √(2(2 + w))/2 - u/2`. -/
def slotW : ℝ := 2 * hgap - sideLHL2 / 2 - root / 2

/-- Height of the uncovered slot: `V - √(2(1 + w))/2 - √w/2`. -/
def slotH : ℝ := vgap - sideLH2 / 2 - sideH1 / 2

/-! ### Exact identities -/

theorem sqrt22_sq : √22 ^ 2 = 22 := by
  sorry

/-- `3u² - 4u - 6 = 0`. -/
theorem root_quadratic : 3 * root ^ 2 - 4 * root - 6 = 0 := by
  sorry

theorem two_mul_hgap_sub_one : 2 * hgap - 1 = root := by
  sorry

theorem one_add_heavy : 1 + heavy = root ^ 2 := by
  sorry

theorem vgap_eq : vgap = hgap + 1 := rfl

/-- The side `2h + 1` of the heavy–light–heavy two-row witness squares to its mass. -/
theorem two_mul_hgap_add_one_sq : (2 * hgap + 1) ^ 2 = 2 * (heavy + 1 + heavy) := by
  sorry

theorem sideLH2_sq : sideLH2 ^ 2 = 2 * (1 + heavy) := by
  sorry

theorem sideH1_sq : sideH1 ^ 2 = heavy := by
  sorry

theorem sideLHL2_sq : sideLHL2 ^ 2 = 2 * (1 + heavy + 1) := by
  sorry

/-! ### Numerical facts -/

theorem root_gt : (2.23 : ℝ) < root := by
  sorry

theorem root_lt : root < (2.2304 : ℝ) := by
  sorry

theorem heavy_pos : 0 < heavy := by
  sorry

theorem one_le_sideH1 : 1 ≤ sideH1 := by
  sorry

theorem one_le_root : 1 ≤ root := by
  sorry

theorem root_le_sideLH2 : root ≤ sideLH2 := by
  sorry

theorem vgap_le_sideLH2 : vgap ≤ sideLH2 := by
  sorry

theorem two_mul_vgap_le_root_add_sideLH2 : 2 * vgap ≤ root + sideLH2 := by
  sorry

theorem two_mul_hgap_le_sideLHL2 : 2 * hgap ≤ sideLHL2 := by
  sorry

theorem vgap_le_sideLHL2 : vgap ≤ sideLHL2 := by
  sorry

theorem vgap_sub_le_sideH1 : 2 * vgap - sideLHL2 ≤ sideH1 := by
  sorry

theorem four_mul_hgap_sub_le_sideLH2 : 4 * hgap - sideLHL2 ≤ sideLH2 := by
  sorry

theorem slotW_pos : 0 < slotW := by
  sorry

theorem slotH_pos : 0 < slotH := by
  sorry

theorem hgap_pos : 0 < hgap := by
  sorry

/-- `Φ` is the covered area per unit mass: the cell has area `2 h V`, the four slots have
area `slotW · slotH` each, and a cell carries mass `1 + w`. -/
theorem phi_eq : phi = (2 * hgap * vgap - 4 * slotW * slotH) / (1 + heavy) := by
  sorry

end CenteredMaximal.Lattice
