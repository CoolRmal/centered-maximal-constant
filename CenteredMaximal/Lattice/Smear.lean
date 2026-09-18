/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Basic
public import CenteredMaximal.Lattice.Witness

/-!
# Smearing the lattice into an integrable function

The measure is truncated to the atoms `atomBox N` and each atom of mass `m` at `p` is replaced by
`m ε⁻²` times the indicator of the closed square of side `ε` centred at `p`. The resulting function
`smeared N ε` is integrable, with `‖smeared N ε‖₁` equal to the total mass of the kept atoms.

If `(L, A)` witnesses level one at `z` and every atom of `A` is kept, the square of side `L + ε`
centred at `z` contains the smeared mass of every atom of `A`, so the maximal function at `z` is at
least `L² / (L + ε)² ≥ (1 + ε)⁻² > 1 - 2ε` (`lt_maximalFunction_smeared`). This is the device of
Aldaz (2000, Lemma 1.1) and of the brief's page 4, with weighted atoms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Finset
open scoped ENNReal

namespace CenteredMaximal.Lattice

/-- The position `(c · hgap, r · vgap)` of the atom with index `(c, r)`. -/
def atom (p : ℤ × ℤ) : Fin 2 → ℝ := ![p.1 * hgap, p.2 * vgap]

/-- The atoms kept at scale `N`: columns `-2N-2, …, 2N+2` and rows `-N-1, …, N+1`. -/
def atomBox (N : ℕ) : Finset (ℤ × ℤ) :=
  Icc (-2 * (N : ℤ) - 2) (2 * N + 2) ×ˢ Icc (-(N : ℤ) - 1) (N + 1)

/-- The truncated lattice with each atom smeared over the closed square of side `ε`. -/
def smeared (N : ℕ) (ε : ℝ) (z : Fin 2 → ℝ) : ℝ :=
  ∑ p ∈ atomBox N, colWeight p.1 / ε ^ 2 * (closedBall (atom p) (ε / 2)).indicator 1 z

theorem colWeight_pos (c : ℤ) : 0 < colWeight c := by
  sorry

theorem smeared_nonneg (N : ℕ) (ε : ℝ) (z : Fin 2 → ℝ) : 0 ≤ smeared N ε z := by
  sorry

theorem integrable_smeared (N : ℕ) {ε : ℝ} (hε : 0 < ε) : Integrable (smeared N ε) := by
  sorry

/-- The columns of `atomBox N` carry total mass `(2N + 3) + (2N + 2) · heavy`. -/
theorem sum_colWeight_Icc (N : ℕ) :
    ∑ c ∈ Icc (-2 * (N : ℤ) - 2) (2 * N + 2), colWeight c = (2 * N + 3) + (2 * N + 2) * heavy := by
  sorry

theorem sum_colWeight_atomBox_le (N : ℕ) :
    ∑ p ∈ atomBox N, colWeight p.1 ≤ (2 * N + 3) ^ 2 * (1 + heavy) := by
  sorry

theorem lintegral_smeared (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ z, ‖smeared N ε z‖ₑ = ENNReal.ofReal (∑ p ∈ atomBox N, colWeight p.1) := by
  sorry

/-- The square of side `L + ε` about a witnessed point carries the smeared mass of the witness. -/
theorem ofReal_sq_le_setLIntegral_smeared {N : ℕ} {ε : ℝ} (hε : 0 < ε) {z : Fin 2 → ℝ} {L : ℝ}
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ atomBox N) (hw : IsWitness (z 0) (z 1) L A) :
    ENNReal.ofReal (L ^ 2) ≤ ∫⁻ y in closedBall z ((L + ε) / 2), ‖smeared N ε y‖ₑ := by
  sorry

/-- At a witnessed point the maximal function of the smeared lattice exceeds `1 - 2ε`. -/
theorem lt_maximalFunction_smeared {N : ℕ} {ε : ℝ} (hε : 0 < ε) {z : Fin 2 → ℝ} {L : ℝ}
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ atomBox N) (hw : IsWitness (z 0) (z 1) L A) :
    ENNReal.ofReal (1 - 2 * ε) < maximalFunction (smeared N ε) z := by
  sorry

end CenteredMaximal.Lattice
