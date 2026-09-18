/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Basic
public import CenteredMaximal.Lattice.Witness
public import Mathlib.MeasureTheory.Integral.IntegrableOn

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
  unfold colWeight
  split_ifs
  exacts [one_pos, heavy_pos]

theorem smeared_nonneg (N : ℕ) (ε : ℝ) (z : Fin 2 → ℝ) : 0 ≤ smeared N ε z :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (div_nonneg (colWeight_pos _).le (sq_nonneg _))
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem integrable_smeared (N : ℕ) (ε : ℝ) : Integrable (smeared N ε) := by
  refine integrable_finsetSum _ fun p _ => Integrable.const_mul ?_ _
  exact (integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const measure_closedBall_lt_top.ne)

/-- Consecutive columns `0, …, 2m` carry mass `(m + 1) + m · heavy`. -/
theorem sum_range_colWeight (m : ℕ) :
    ∑ n ∈ Finset.range (2 * m + 1), colWeight n = (m + 1) + m * heavy := by
  induction m with
  | zero => simp [colWeight]
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    have h₁ : colWeight ((2 * m + 1 : ℕ) : ℤ) = heavy := by
      simp [colWeight, parity_simps]
    have h₂ : colWeight ((2 * m + 1 + 1 : ℕ) : ℤ) = 1 := by
      simp [colWeight, parity_simps]
    rw [h₁, h₂]
    push_cast
    ring

/-- The columns of `atomBox N` carry total mass `(2N + 3) + (2N + 2) · heavy`. -/
theorem sum_colWeight_Icc (N : ℕ) :
    ∑ c ∈ Icc (-2 * (N : ℤ) - 2) (2 * N + 2), colWeight c = (2 * N + 3) + (2 * N + 2) * heavy := by
  rw [Int.Icc_eq_finset_map, Finset.sum_map,
    show (2 * (N : ℤ) + 2 + 1 - (-2 * N - 2)).toNat = 2 * (2 * N + 2) + 1 by omega]
  have h : ∀ n : ℕ, colWeight (-2 * (N : ℤ) - 2 + n) = colWeight n := fun n => by
    rw [show -2 * (N : ℤ) - 2 + n = n + 2 * (-(N : ℤ) - 1) by ring, colWeight_add_two_mul]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply, h,
    sum_range_colWeight]
  push_cast
  ring

theorem sum_colWeight_atomBox (N : ℕ) :
    ∑ p ∈ atomBox N, colWeight p.1 = (2 * N + 3) * ((2 * N + 3) + (2 * N + 2) * heavy) := by
  have hcard : (Icc (-(N : ℤ) - 1) (N + 1)).card = 2 * N + 3 := by
    rw [Int.card_Icc]
    omega
  have hrow : ∀ c ∈ Icc (-2 * (N : ℤ) - 2) (2 * N + 2),
      ∑ r ∈ Icc (-(N : ℤ) - 1) (N + 1), colWeight (c, r).1 = (2 * N + 3) * colWeight c := by
    intro c _
    simp only [Finset.sum_const, hcard, nsmul_eq_mul]
    push_cast
    ring
  rw [atomBox, Finset.sum_product, Finset.sum_congr rfl hrow, ← Finset.mul_sum, sum_colWeight_Icc]

theorem sum_colWeight_atomBox_le (N : ℕ) :
    ∑ p ∈ atomBox N, colWeight p.1 ≤ (2 * N + 3) ^ 2 * (1 + heavy) := by
  rw [sum_colWeight_atomBox]
  nlinarith [heavy_pos, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

theorem ofReal_mul_indicator_one {s : Set (Fin 2 → ℝ)} (a : ℝ) (z : Fin 2 → ℝ) :
    ENNReal.ofReal (a * s.indicator 1 z) = s.indicator (fun _ => ENNReal.ofReal a) z := by
  by_cases hz : z ∈ s <;> simp [hz]

theorem enorm_smeared (N : ℕ) (ε : ℝ) (z : Fin 2 → ℝ) :
    ‖smeared N ε z‖ₑ = ∑ p ∈ atomBox N,
      (closedBall (atom p) (ε / 2)).indicator (fun _ => ENNReal.ofReal (colWeight p.1 / ε ^ 2)) z := by
  rw [Real.enorm_eq_ofReal (smeared_nonneg N ε z), smeared, ENNReal.ofReal_sum_of_nonneg]
  · simp_rw [ofReal_mul_indicator_one]
  · exact fun _ _ => mul_nonneg (div_nonneg (colWeight_pos _).le (sq_nonneg _))
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

/-- A smeared atom has integral equal to its mass. -/
theorem ofReal_div_sq_mul_volume {ε : ℝ} (hε : 0 < ε) (p : ℤ × ℤ) :
    ENNReal.ofReal (colWeight p.1 / ε ^ 2) * volume (closedBall (atom p) (ε / 2)) =
      ENNReal.ofReal (colWeight p.1) := by
  rw [volume_closedBall_eq _ (by positivity), ← ENNReal.ofReal_mul
    (div_nonneg (colWeight_pos _).le (sq_nonneg _))]
  congr 1
  field_simp

theorem lintegral_smeared (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ z, ‖smeared N ε z‖ₑ = ENNReal.ofReal (∑ p ∈ atomBox N, colWeight p.1) := by
  simp_rw [enorm_smeared]
  rw [lintegral_finsetSum _ fun _ _ => measurable_const.indicator measurableSet_closedBall,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => (colWeight_pos _).le]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [lintegral_indicator_const measurableSet_closedBall, ofReal_div_sq_mul_volume hε]

/-- The square of side `L + ε` about a witnessed point carries the smeared mass of the witness. -/
theorem ofReal_sq_le_setLIntegral_smeared {N : ℕ} {ε : ℝ} (hε : 0 < ε) {z : Fin 2 → ℝ} {L : ℝ}
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ atomBox N) (hw : IsWitness (z 0) (z 1) L A) :
    ENNReal.ofReal (L ^ 2) ≤ ∫⁻ y in closedBall z ((L + ε) / 2), ‖smeared N ε y‖ₑ := by
  obtain ⟨hL, hm, hd⟩ := hw
  have hsub : ∀ p ∈ A, closedBall (atom p) (ε / 2) ⊆ closedBall z ((L + ε) / 2) := by
    intro p hp
    apply closedBall_subset_closedBall'
    have : dist (atom p) z ≤ L / 2 := by
      rw [dist_pi_le_iff (by linarith)]
      intro i
      fin_cases i
      · simpa [atom, Real.dist_eq] using (hd p hp).1
      · simpa [atom, Real.dist_eq] using (hd p hp).2
    linarith
  calc ENNReal.ofReal (L ^ 2) ≤ ENNReal.ofReal (∑ p ∈ A, colWeight p.1) :=
        ENNReal.ofReal_le_ofReal hm
    _ = ∑ p ∈ A, ENNReal.ofReal (colWeight p.1) :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => (colWeight_pos _).le
    _ = ∑ p ∈ A, ∫⁻ y in closedBall z ((L + ε) / 2), (closedBall (atom p) (ε / 2)).indicator
          (fun _ => ENNReal.ofReal (colWeight p.1 / ε ^ 2)) y := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [lintegral_indicator_const measurableSet_closedBall,
          Measure.restrict_apply measurableSet_closedBall, Set.inter_eq_left.2 (hsub p hp),
          ofReal_div_sq_mul_volume hε]
    _ = ∫⁻ y in closedBall z ((L + ε) / 2), ∑ p ∈ A, (closedBall (atom p) (ε / 2)).indicator
          (fun _ => ENNReal.ofReal (colWeight p.1 / ε ^ 2)) y :=
        (lintegral_finsetSum _ fun _ _ => measurable_const.indicator measurableSet_closedBall).symm
    _ ≤ ∫⁻ y in closedBall z ((L + ε) / 2), ‖smeared N ε y‖ₑ := by
        refine lintegral_mono fun y => ?_
        rw [enorm_smeared]
        exact Finset.sum_le_sum_of_subset hA

/-- At a witnessed point the maximal function of the smeared lattice exceeds `1 - 2ε`. -/
theorem lt_maximalFunction_smeared {N : ℕ} {ε : ℝ} (hε : 0 < ε) {z : Fin 2 → ℝ} {L : ℝ}
    {A : Finset (ℤ × ℤ)} (hA : A ⊆ atomBox N) (hw : IsWitness (z 0) (z 1) L A) :
    ENNReal.ofReal (1 - 2 * ε) < maximalFunction (smeared N ε) z := by
  have hL : 1 ≤ L := hw.1
  have hr : 0 < (L + ε) / 2 := by linarith
  refine lt_of_lt_of_le ?_ (le_maximalFunction _ z hr)
  rw [volume_closedBall_eq z hr.le]
  calc ENNReal.ofReal (1 - 2 * ε) < ENNReal.ofReal (L ^ 2 / (L + ε) ^ 2) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by positivity), lt_div_iff₀ (by positivity)]
        have hL₁ : 0 ≤ L - 1 := by linarith
        nlinarith [mul_nonneg (mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ L)) hL₁,
          mul_nonneg (sq_nonneg ε) hL₁, pow_pos hε 2, pow_pos hε 3]
    _ = (ENNReal.ofReal ((2 * ((L + ε) / 2)) ^ 2))⁻¹ * ENNReal.ofReal (L ^ 2) := by
        rw [show (2 * ((L + ε) / 2)) ^ 2 = (L + ε) ^ 2 by ring,
          ENNReal.ofReal_div_of_pos (by positivity), ENNReal.div_eq_inv_mul]
    _ ≤ _ := by
        gcongr
        exact ofReal_sq_le_setLIntegral_smeared hε hA hw

end CenteredMaximal.Lattice
