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

theorem mem_cell {z : Fin 2 → ℝ} :
    z ∈ cell ↔ (-hgap ≤ z 0 ∧ z 0 < hgap) ∧ (-(vgap / 2) ≤ z 1 ∧ z 1 < vgap / 2) := by
  simp [cell, Fin.forall_fin_two, neg_div]

theorem measurableSet_slots : MeasurableSet slots := by
  have h₀ : Measurable fun z : Fin 2 → ℝ => |z 0| :=
    (continuous_abs.comp (continuous_apply 0)).measurable
  have h₁ : Measurable fun z : Fin 2 → ℝ => |z 1| :=
    (continuous_abs.comp (continuous_apply 1)).measurable
  exact (measurableSet_lt measurable_const h₀).inter ((measurableSet_lt h₀ measurable_const).inter
    ((measurableSet_lt measurable_const h₁).inter (measurableSet_lt h₁ measurable_const)))

theorem measurableSet_goodSet : MeasurableSet goodSet :=
  (MeasurableSet.univ_pi fun _ => measurableSet_Ico).diff measurableSet_slots

theorem volume_cell : volume cell = ENNReal.ofReal (2 * hgap * vgap) := by
  rw [cell, Real.volume_pi_Ico, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← ENNReal.ofReal_mul (by linarith [hgap_pos])]
  congr 1
  ring

private theorem mem_union_of_abs {a b x : ℝ} (ha : a < |x|) (hb : |x| < b) :
    x ∈ Ioo a b ∪ Ioo (-b) (-a) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx] at ha hb
    exact Or.inl ⟨ha, hb⟩
  · rw [abs_of_neg hx] at ha hb
    exact Or.inr ⟨by linarith, by linarith⟩

theorem volume_slots_le :
    volume slots ≤ (ENNReal.ofReal slotW + ENNReal.ofReal slotW) *
      (ENNReal.ofReal slotH + ENNReal.ofReal slotH) := by
  set I := Ioo (root / 2) (2 * hgap - sideLHL2 / 2) ∪ Ioo (-(2 * hgap - sideLHL2 / 2)) (-(root / 2))
  set J := Ioo (sideH1 / 2) (vgap - sideLH2 / 2) ∪ Ioo (-(vgap - sideLH2 / 2)) (-(sideH1 / 2))
  have hsub : slots ⊆ univ.pi ![I, J] := by
    rintro z ⟨h₁, h₂, h₃, h₄⟩
    simp only [Set.mem_univ_pi, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨mem_union_of_abs h₁ h₂, mem_union_of_abs h₃ h₄⟩
  have hI : volume I ≤ ENNReal.ofReal slotW + ENNReal.ofReal slotW := by
    refine (measure_union_le _ _).trans (le_of_eq ?_)
    rw [Real.volume_Ioo, Real.volume_Ioo, slotW]
    congr 2
    all_goals ring
  have hJ : volume J ≤ ENNReal.ofReal slotH + ENNReal.ofReal slotH := by
    refine (measure_union_le _ _).trans (le_of_eq ?_)
    rw [Real.volume_Ioo, Real.volume_Ioo, slotH]
    congr 2
    all_goals ring
  calc volume slots ≤ volume (univ.pi ![I, J]) := measure_mono hsub
    _ = volume I * volume J := by
        rw [volume_pi_pi, Fin.prod_univ_two]
        rfl
    _ ≤ _ := by gcongr

theorem area_pos : 0 < 2 * hgap * vgap - 4 * (slotW * slotH) := by
  have hW : slotW < 0.3904 := by
    unfold slotW
    linarith [hgap_lt, sideLHL2_gt, root_gt]
  have hH : slotH < 0.0437 := by
    unfold slotH
    linarith [vgap_lt, sideLH2_gt, sideH1_gt]
  nlinarith [mul_lt_mul'' hW hH slotW_pos.le slotH_pos.le,
    mul_lt_mul'' hgap_gt vgap_gt (by norm_num) (by norm_num)]

theorem volume_goodSet_ge :
    ENNReal.ofReal (2 * hgap * vgap - 4 * (slotW * slotH)) ≤ volume goodSet := by
  have hW := slotW_pos.le
  have hH := slotH_pos.le
  calc ENNReal.ofReal (2 * hgap * vgap - 4 * (slotW * slotH))
      = ENNReal.ofReal (2 * hgap * vgap) - (ENNReal.ofReal slotW + ENNReal.ofReal slotW) *
          (ENNReal.ofReal slotH + ENNReal.ofReal slotH) := by
        rw [← ENNReal.ofReal_add hW hW, ← ENNReal.ofReal_add hH hH,
          ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_sub _ (by positivity)]
        congr 1
        ring
    _ ≤ volume cell - volume slots := by
        rw [volume_cell]
        gcongr
        exact volume_slots_le
    _ ≤ volume goodSet := le_measure_sdiff

theorem volume_goodCopy (k l : ℤ) : volume (goodCopy k l) = volume goodSet :=
  measure_preimage_add volume (-shift k l) goodSet

theorem measurableSet_goodCopy (k l : ℤ) : MeasurableSet (goodCopy k l) :=
  measurableSet_goodSet.preimage (measurable_const_add _)

theorem mem_goodCopy {k l : ℤ} {z : Fin 2 → ℝ} :
    z ∈ goodCopy k l ↔ ![z 0 - 2 * k * hgap, z 1 - l * vgap] ∈ goodSet := by
  have : -shift k l + z = ![z 0 - 2 * k * hgap, z 1 - l * vgap] := by
    ext i
    fin_cases i <;> simp [shift] <;> ring
  rw [goodCopy, Set.mem_preimage, this]

/-- Integers `a, b` with `|a t - b t| < t` for some `t > 0` are equal. -/
private theorem int_eq_of_mul_sub_lt {a b : ℤ} {t : ℝ} (ht : 0 < t) (h₁ : a * t - b * t < t)
    (h₂ : b * t - a * t < t) : a = b := by
  have h₃ : ((a - b : ℤ) : ℝ) < 1 := by
    push_cast
    nlinarith
  have h₄ : ((b - a : ℤ) : ℝ) < 1 := by
    push_cast
    nlinarith
  have h₅ : a - b < 1 := by exact_mod_cast h₃
  have h₆ : b - a < 1 := by exact_mod_cast h₄
  omega

theorem pairwiseDisjoint_goodCopy :
    (univ : Set (ℤ × ℤ)).PairwiseDisjoint fun p => goodCopy p.1 p.2 := by
  rintro ⟨k, l⟩ - ⟨k', l'⟩ - hne
  refine Set.disjoint_left.2 fun z hz hz' => hne ?_
  rw [mem_goodCopy] at hz hz'
  have hc := mem_cell.1 hz.1
  have hc' := mem_cell.1 hz'.1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc hc'
  have hh := hgap_pos
  have hv : 0 < vgap := by linarith [vgap_gt]
  have hk : k = k' := int_eq_of_mul_sub_lt (t := 2 * hgap) (by linarith) (by linarith)
    (by linarith)
  have hl : l = l' := int_eq_of_mul_sub_lt (t := vgap) hv (by linarith) (by linarith)
  rw [hk, hl]

theorem exists_isWitness_of_mem_goodCopy {k l : ℤ} {z : Fin 2 → ℝ} (hz : z ∈ goodCopy k l) :
    ∃ L A, A ⊆ nearBox k l ∧ IsWitness (z 0) (z 1) L A := by
  rw [mem_goodCopy] at hz
  obtain ⟨hcell, hslot⟩ := hz
  have hc := mem_cell.1 hcell
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  have hslot' : ¬ (root / 2 < |z 0 - 2 * k * hgap| ∧ |z 0 - 2 * k * hgap| < 2 * hgap - sideLHL2 / 2 ∧
      sideH1 / 2 < |z 1 - l * vgap| ∧ |z 1 - l * vgap| < vgap - sideLH2 / 2) := by
    simpa [slots] using hslot
  obtain ⟨L, A, hA, hw⟩ := exists_isWitness_of_abs (abs_le.2 ⟨hc.1.1, hc.1.2.le⟩)
    (abs_le.2 ⟨hc.2.1, hc.2.2.le⟩) hslot'
  refine ⟨L, _, map_addRight_subset_nearBox hA k l, ?_⟩
  simpa using hw.translate k l

theorem nearBox_subset_atomBox {N : ℕ} {k l : ℤ} (hk : |k| ≤ N) (hl : |l| ≤ N) :
    nearBox k l ⊆ atomBox N := by
  obtain ⟨hk₁, hk₂⟩ := abs_le.1 hk
  obtain ⟨hl₁, hl₂⟩ := abs_le.1 hl
  exact Finset.product_subset_product (Finset.Icc_subset_Icc (by omega) (by omega))
    (Finset.Icc_subset_Icc (by omega) (by omega))

/-- The level set of `smeared N ε` at height `1 - 2ε` contains `(2N + 1)²` disjoint copies of
`goodSet`. -/
theorem ofReal_le_volume_levelSet (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal ((2 * N + 1) ^ 2 * (2 * hgap * vgap - 4 * (slotW * slotH))) ≤
      volume {z | ENNReal.ofReal (1 - 2 * ε) < maximalFunction (smeared N ε) z} := by
  set S := Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N
  have hcard : S.card = (2 * N + 1) ^ 2 := by
    rw [Finset.card_product, Int.card_Icc]
    have : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
    rw [this, sq]
  have hsub : (⋃ p ∈ S, goodCopy p.1 p.2) ⊆
      {z | ENNReal.ofReal (1 - 2 * ε) < maximalFunction (smeared N ε) z} := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨p, hp, hz⟩ := hz
    obtain ⟨hk, hl⟩ := Finset.mem_product.1 hp
    obtain ⟨L, A, hA, hw⟩ := exists_isWitness_of_mem_goodCopy hz
    exact lt_maximalFunction_smeared hε (hA.trans (nearBox_subset_atomBox
      (abs_le.2 (Finset.mem_Icc.1 hk)) (abs_le.2 (Finset.mem_Icc.1 hl)))) hw
  calc ENNReal.ofReal ((2 * N + 1) ^ 2 * (2 * hgap * vgap - 4 * (slotW * slotH)))
      = ∑ _p ∈ S, ENNReal.ofReal (2 * hgap * vgap - 4 * (slotW * slotH)) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← ENNReal.ofReal_natCast]
        push_cast
        rfl
    _ ≤ ∑ p ∈ S, volume (goodCopy p.1 p.2) :=
        Finset.sum_le_sum fun p _ => (volume_goodCopy p.1 p.2).symm ▸ volume_goodSet_ge
    _ = volume (⋃ p ∈ S, goodCopy p.1 p.2) :=
        (measure_biUnion_finset (pairwiseDisjoint_goodCopy.subset (Set.subset_univ _))
          fun p _ => measurableSet_goodCopy p.1 p.2).symm
    _ ≤ _ := measure_mono hsub

/-- A weak type bound is at least `((2N + 1)/(2N + 3))³ Φ` for every `N`. -/
theorem ofReal_mul_phi_le {C : ℝ≥0∞} (hC : IsWeakTypeBound 2 C) (N : ℕ) :
    ENNReal.ofReal (((2 * N + 1) / (2 * N + 3)) ^ 3 * phi) ≤ C := by
  set ε : ℝ := 1 / (2 * N + 3) with hε_def
  have hε : 0 < ε := by positivity
  set q : ℝ := (2 * N + 1) / (2 * N + 3) with hq_def
  have hq : 1 - 2 * ε = q := by
    rw [hε_def, hq_def]
    field_simp
    ring
  have hq₀ : 0 ≤ q := by positivity
  have hX := area_pos
  have hD : 0 < (2 * N + 3) ^ 2 * (1 + heavy) := by
    have := heavy_pos
    positivity
  have key := hC (smeared N ε) (integrable_smeared N ε) (ENNReal.ofReal (1 - 2 * ε))
  rw [lintegral_smeared N hε] at key
  have h₂ : ENNReal.ofReal (q * ((2 * N + 1) ^ 2 * (2 * hgap * vgap - 4 * (slotW * slotH)))) ≤
      C * ENNReal.ofReal ((2 * N + 3) ^ 2 * (1 + heavy)) :=
    calc ENNReal.ofReal (q * ((2 * N + 1) ^ 2 * (2 * hgap * vgap - 4 * (slotW * slotH))))
        = ENNReal.ofReal q *
            ENNReal.ofReal ((2 * N + 1) ^ 2 * (2 * hgap * vgap - 4 * (slotW * slotH))) :=
          ENNReal.ofReal_mul hq₀
      _ ≤ ENNReal.ofReal (1 - 2 * ε) *
            volume {z | ENNReal.ofReal (1 - 2 * ε) < maximalFunction (smeared N ε) z} := by
          rw [← hq]
          gcongr
          exact ofReal_le_volume_levelSet N hε
      _ ≤ C * ENNReal.ofReal (∑ p ∈ atomBox N, colWeight p.1) := key
      _ ≤ C * ENNReal.ofReal ((2 * N + 3) ^ 2 * (1 + heavy)) := by
          gcongr
          exact sum_colWeight_atomBox_le N
  calc ENNReal.ofReal (q ^ 3 * phi)
      = ENNReal.ofReal (q * ((2 * N + 1) ^ 2 * (2 * hgap * vgap - 4 * (slotW * slotH)))) /
          ENNReal.ofReal ((2 * N + 3) ^ 2 * (1 + heavy)) := by
        rw [← ENNReal.ofReal_div_of_pos hD, phi_eq, hq_def]
        congr 1
        have := heavy_pos
        field_simp
    _ ≤ C := ENNReal.div_le_of_le_mul h₂

/-- `(2N + 1)/(2N + 3) → 1`. -/
theorem tendsto_ratio : Tendsto (fun N : ℕ => ((2 * N + 1) / (2 * N + 3) : ℝ)) atTop (𝓝 1) := by
  have hlow : Tendsto (fun N : ℕ => (1 - 1 / ((N : ℝ) + 1) : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun N => ?_)
    (fun N => ?_)
  · have hN : (0 : ℝ) ≤ N := N.cast_nonneg
    have h : (1 : ℝ) - 1 / (N + 1) = N / (N + 1) := by
      field_simp
      ring
    rw [h, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · have hN : (0 : ℝ) ≤ N := N.cast_nonneg
    rw [div_le_one (by positivity)]
    linarith

/-- Every weak type bound in dimension two is at least `Φ`. -/
theorem ofReal_phi_le {C : ℝ≥0∞} (hC : IsWeakTypeBound 2 C) : ENNReal.ofReal phi ≤ C := by
  have hlim : Tendsto (fun N : ℕ => ((2 * N + 1) / (2 * N + 3) : ℝ) ^ 3 * phi) atTop (𝓝 phi) := by
    simpa using (tendsto_ratio.pow 3).mul_const phi
  exact le_of_tendsto' (ENNReal.tendsto_ofReal hlim) (ofReal_mul_phi_le hC)

end CenteredMaximal.Lattice
