/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Lattice.Smear

/-!
# The lower bound `Φ ≤ c₂`

The period cell `cell = [-hgap, hgap) × [-vgap/2, vgap/2)` minus the four open slots is `goodSet`;
it has area at least `2 hgap vgap - 4 slotW slotH`, and every point of it has a level-one witness
using atoms of the neighbouring cells (`exists_isWitness_of_abs`). The `(2N + 1)²` translates
`goodCopy k l`, `|k|, |l| ≤ N`, are disjoint and lie in the level set of `smeared N ε` at height
`1 - 2ε`, while `‖smeared N ε‖₁ ≤ (2N + 3)² (1 + heavy)`. With `ε = 1 / (2N + 3)` a weak type bound
`C` therefore satisfies `C ≥ ((2N + 1)/(2N + 3))³ Φ`, and `N → ∞` gives `C ≥ Φ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace CenteredMaximal.Lattice

/-- The period cell `[-hgap, hgap) × [-vgap/2, vgap/2)`. -/
def cell : Set (Fin 2 → ℝ) :=
  univ.pi fun i => Ico (![-hgap, -vgap / 2] i) (![hgap, vgap / 2] i)

/-- The four open slots, one in each quadrant, missed by the witnesses. -/
def slots : Set (Fin 2 → ℝ) :=
  {z | root / 2 < |z 0| ∧ |z 0| < 2 * hgap - sideLHL2 / 2 ∧ sideH1 / 2 < |z 1| ∧
    |z 1| < vgap - sideLH2 / 2}

/-- The witnessed part of the period cell. -/
def goodSet : Set (Fin 2 → ℝ) := cell \ slots

/-- The period vector of the cell with index `(k, l)`. -/
def shift (k l : ℤ) : Fin 2 → ℝ := ![2 * k * hgap, l * vgap]

/-- The translate of `goodSet` into the cell with index `(k, l)`. -/
def goodCopy (k l : ℤ) : Set (Fin 2 → ℝ) := (fun z => -shift k l + z) ⁻¹' goodSet

theorem measurableSet_goodSet : MeasurableSet goodSet := by
  sorry

theorem volume_goodSet_ge :
    ENNReal.ofReal (2 * hgap * vgap - 4 * (slotW * slotH)) ≤ volume goodSet := by
  sorry

theorem volume_goodCopy (k l : ℤ) : volume (goodCopy k l) = volume goodSet := by
  sorry

theorem pairwiseDisjoint_goodCopy :
    (univ : Set (ℤ × ℤ)).PairwiseDisjoint fun p => goodCopy p.1 p.2 := by
  sorry

theorem exists_isWitness_of_mem_goodCopy {k l : ℤ} {z : Fin 2 → ℝ} (hz : z ∈ goodCopy k l) :
    ∃ L A, A ⊆ nearBox k l ∧ IsWitness (z 0) (z 1) L A := by
  sorry

theorem nearBox_subset_atomBox {N : ℕ} {k l : ℤ} (hk : |k| ≤ N) (hl : |l| ≤ N) :
    nearBox k l ⊆ atomBox N := by
  sorry

/-- The level set of `smeared N ε` at height `1 - 2ε` contains `(2N + 1)²` disjoint copies of
`goodSet`. -/
theorem ofReal_le_volume_levelSet (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal ((2 * N + 1) ^ 2 * (2 * hgap * vgap - 4 * (slotW * slotH))) ≤
      volume {z | ENNReal.ofReal (1 - 2 * ε) < maximalFunction (smeared N ε) z} := by
  sorry

/-- A weak type bound is at least `((2N + 1)/(2N + 3))³ Φ` for every `N`. -/
theorem ofReal_mul_phi_le {C : ℝ≥0∞} (hC : IsWeakTypeBound 2 C) (N : ℕ) :
    ENNReal.ofReal (((2 * N + 1) / (2 * N + 3)) ^ 3 * phi) ≤ C := by
  sorry

/-- Every weak type bound in dimension two is at least `Φ`. -/
theorem ofReal_phi_le {C : ℝ≥0∞} (hC : IsWeakTypeBound 2 C) : ENNReal.ofReal phi ≤ C := by
  sorry

end CenteredMaximal.Lattice
