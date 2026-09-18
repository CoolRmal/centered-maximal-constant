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
  simp [colWeight]

theorem colWeight_add_two_mul (c k : ℤ) : colWeight (c + 2 * k) = colWeight c := by
  simp [colWeight, Int.even_add, parity_simps]

theorem IsWitness.neg_fst {x y L : ℝ} {A : Finset (ℤ × ℤ)} (hw : IsWitness x y L A) :
    IsWitness (-x) y L (A.map negFst.toEmbedding) := by
  obtain ⟨hL, hm, hd⟩ := hw
  refine ⟨hL, by simpa [negFst, colWeight_neg] using hm, ?_⟩
  simp only [Finset.mem_map, Equiv.coe_toEmbedding, forall_exists_index, and_imp]
  rintro _ p hp rfl
  obtain ⟨h₁, h₂⟩ := hd p hp
  simp only [negFst, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.neg_apply,
    Equiv.refl_apply, Int.cast_neg]
  rw [show -(p.1 : ℝ) * hgap - -x = -((p.1 : ℝ) * hgap - x) by ring, abs_neg]
  exact ⟨h₁, h₂⟩

theorem IsWitness.neg_snd {x y L : ℝ} {A : Finset (ℤ × ℤ)} (hw : IsWitness x y L A) :
    IsWitness x (-y) L (A.map negSnd.toEmbedding) := by
  obtain ⟨hL, hm, hd⟩ := hw
  refine ⟨hL, by simpa [negSnd] using hm, ?_⟩
  simp only [Finset.mem_map, Equiv.coe_toEmbedding, forall_exists_index, and_imp]
  rintro _ p hp rfl
  obtain ⟨h₁, h₂⟩ := hd p hp
  simp only [negSnd, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.neg_apply,
    Equiv.refl_apply, Int.cast_neg]
  rw [show -(p.2 : ℝ) * vgap - -y = -((p.2 : ℝ) * vgap - y) by ring, abs_neg]
  exact ⟨h₁, h₂⟩

theorem IsWitness.translate {x y L : ℝ} {A : Finset (ℤ × ℤ)} (hw : IsWitness x y L A)
    (k l : ℤ) :
    IsWitness (x + 2 * k * hgap) (y + l * vgap) L
      (A.map (Equiv.addRight ((2 * k, l) : ℤ × ℤ)).toEmbedding) := by
  obtain ⟨hL, hm, hd⟩ := hw
  refine ⟨hL, by simpa [colWeight_add_two_mul] using hm, ?_⟩
  simp only [Finset.mem_map, Equiv.coe_toEmbedding, forall_exists_index, and_imp]
  rintro _ p hp rfl
  obtain ⟨h₁, h₂⟩ := hd p hp
  constructor
  · simpa [show ((p.1 : ℝ) + 2 * k) * hgap - (x + 2 * k * hgap) = p.1 * hgap - x by ring]
      using h₁
  · simpa [show ((p.2 : ℝ) + l) * vgap - (y + l * vgap) = p.2 * vgap - y by ring] using h₂

theorem map_negFst_subset_nearBox {A : Finset (ℤ × ℤ)} (hA : A ⊆ nearBox 0 0) :
    A.map negFst.toEmbedding ⊆ nearBox 0 0 := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.1 hq
  have := hA hp
  simp only [nearBox, Finset.mem_product, Finset.mem_Icc] at this ⊢
  simp only [negFst, Equiv.coe_toEmbedding, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    Equiv.neg_apply, Equiv.refl_apply]
  omega

theorem map_negSnd_subset_nearBox {A : Finset (ℤ × ℤ)} (hA : A ⊆ nearBox 0 0) :
    A.map negSnd.toEmbedding ⊆ nearBox 0 0 := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.1 hq
  have := hA hp
  simp only [nearBox, Finset.mem_product, Finset.mem_Icc] at this ⊢
  simp only [negSnd, Equiv.coe_toEmbedding, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    Equiv.neg_apply, Equiv.refl_apply]
  omega

theorem map_addRight_subset_nearBox {A : Finset (ℤ × ℤ)} (hA : A ⊆ nearBox 0 0) (k l : ℤ) :
    A.map (Equiv.addRight ((2 * k, l) : ℤ × ℤ)).toEmbedding ⊆ nearBox k l := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.1 hq
  have := hA hp
  simp only [nearBox, Finset.mem_product, Finset.mem_Icc] at this ⊢
  simp only [Equiv.coe_toEmbedding, Equiv.coe_addRight, Prod.fst_add, Prod.snd_add]
  omega

/-! ### The six witnesses -/

/-- The light atom at the origin, side `1`. -/
theorem isWitness_light {x y : ℝ} (hx : |x| ≤ 1 / 2) (hy : |y| ≤ 1 / 2) :
    IsWitness x y 1 {(0, 0)} := by
  refine ⟨le_rfl, by simp [colWeight], ?_⟩
  simpa [abs_neg] using And.intro hx hy

/-- Heavy, light, heavy atoms in two rows, side `2 hgap + 1`. -/
theorem isWitness_hlh2 {x y : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) (hy : 1 / 2 ≤ y)
    (hy' : y ≤ vgap / 2) :
    IsWitness x y (2 * hgap + 1) {(-1, 0), (0, 0), (1, 0), (-1, 1), (0, 1), (1, 1)} := by
  have hh := hgap_pos
  refine ⟨by linarith, ?_, ?_⟩
  · simp [colWeight, two_mul_hgap_add_one_sq]
    linarith
  · simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    push_cast
    simp only [abs_le, vgap] at *
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_, ?_⟩,
      ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- A light and a heavy atom in one row, side `root`. -/
theorem isWitness_lh1 {x y : ℝ} (hx : 1 / 2 ≤ x) (hx' : x ≤ root / 2) (hy : 0 ≤ y)
    (hy' : y ≤ root / 2) :
    IsWitness x y root {(0, 0), (1, 0)} := by
  have h₁ := two_mul_hgap_sub_one
  have h₂ := one_le_root
  refine ⟨h₂, ?_, ?_⟩
  · simp [colWeight, ← one_add_heavy]
  · simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    push_cast
    simp only [abs_le]
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- A light and a heavy atom in two rows, side `sideLH2`. -/
theorem isWitness_lh2 {x y : ℝ} (hx : 1 / 2 ≤ x) (hx' : x ≤ sideLH2 / 2)
    (hy : vgap - sideLH2 / 2 ≤ y) (hy' : y ≤ vgap / 2) :
    IsWitness x y sideLH2 {(0, 0), (1, 0), (0, 1), (1, 1)} := by
  have h₁ := two_mul_hgap_sub_one
  have h₂ := root_le_sideLH2
  have h₃ := one_le_root
  have h₄ := vgap_le_sideLH2
  have h₅ := hgap_pos
  have h₆ := vgap_gt
  refine ⟨by linarith, ?_, ?_⟩
  · simp [colWeight, sideLH2_sq]
    linarith
  · simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    push_cast
    simp only [abs_le]
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;>
      linarith

/-- One heavy atom, side `sideH1`. -/
theorem isWitness_h1 {x y : ℝ} (hx : hgap - sideH1 / 2 ≤ x) (hx' : x ≤ hgap) (hy : 0 ≤ y)
    (hy' : y ≤ sideH1 / 2) :
    IsWitness x y sideH1 {(1, 0)} := by
  have h₁ := one_le_sideH1
  refine ⟨h₁, by simp [colWeight, sideH1_sq], ?_⟩
  simp only [Finset.mem_singleton, forall_eq]
  push_cast
  simp only [abs_le]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- Light, heavy, light atoms in two rows, side `sideLHL2`. -/
theorem isWitness_lhl2 {x y : ℝ} (hx : 2 * hgap - sideLHL2 / 2 ≤ x) (hx' : x ≤ hgap)
    (hy : vgap - sideLHL2 / 2 ≤ y) (hy' : y ≤ vgap / 2) :
    IsWitness x y sideLHL2 {(0, 0), (1, 0), (2, 0), (0, 1), (1, 1), (2, 1)} := by
  have h₁ := two_mul_hgap_le_sideLHL2
  have h₂ := vgap_le_sideLHL2
  have h₃ := hgap_pos
  have h₄ := hgap_gt
  have h₅ := vgap_gt
  refine ⟨by linarith, ?_, ?_⟩
  · simp [colWeight, sideLHL2_sq, show Even (2 : ℤ) from even_two]
    linarith
  · simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    push_cast
    simp only [abs_le]
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_, ?_⟩,
      ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-! ### Coverage -/

/-- Explicit atom sets lie in `nearBox 0 0`. -/
private theorem subset_nearBox_zero {A : Finset (ℤ × ℤ)}
    (h : ∀ p ∈ A, -2 ≤ p.1 ∧ p.1 ≤ 2 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1) : A ⊆ nearBox 0 0 := by
  intro p hp
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h p hp
  simp only [nearBox, Finset.mem_product, Finset.mem_Icc]
  omega

/-- The six witnesses cover the quarter cell `[0, hgap] × [0, vgap/2]` except the open slot
`(root/2, 2 hgap - sideLHL2/2) × (sideH1/2, vgap - sideLH2/2)`. -/
theorem exists_isWitness_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hx' : x ≤ hgap) (hy : 0 ≤ y)
    (hy' : y ≤ vgap / 2)
    (hslot : ¬ (root / 2 < x ∧ x < 2 * hgap - sideLHL2 / 2 ∧ sideH1 / 2 < y ∧
      y < vgap - sideLH2 / 2)) :
    ∃ L A, A ⊆ nearBox 0 0 ∧ IsWitness x y L A := by
  have e₁ := two_mul_hgap_sub_one
  have e₂ := one_le_root
  have e₃ := root_le_sideLH2
  have e₄ := two_mul_vgap_le_root_add_sideLH2
  have e₅ := one_le_sideH1
  have e₆ := vgap_sub_le_sideH1
  have e₇ := four_mul_hgap_sub_le_sideLH2
  by_cases h₁ : x ≤ 1 / 2
  · by_cases h₂ : y ≤ 1 / 2
    · exact ⟨1, _, subset_nearBox_zero (by simp),
        isWitness_light (abs_le.2 ⟨by linarith, h₁⟩) (abs_le.2 ⟨by linarith, h₂⟩)⟩
    · exact ⟨_, _, subset_nearBox_zero (by simp), isWitness_hlh2 hx h₁ (by linarith) hy'⟩
  by_cases h₃ : x ≤ root / 2
  · by_cases h₄ : y ≤ root / 2
    · exact ⟨_, _, subset_nearBox_zero (by simp), isWitness_lh1 (by linarith) h₃ hy h₄⟩
    · exact ⟨_, _, subset_nearBox_zero (by simp),
        isWitness_lh2 (by linarith) (by linarith) (by linarith) hy'⟩
  by_cases h₅ : y ≤ sideH1 / 2
  · exact ⟨_, _, subset_nearBox_zero (by simp), isWitness_h1 (by linarith) hx' hy h₅⟩
  by_cases h₆ : 2 * hgap - sideLHL2 / 2 ≤ x
  · exact ⟨_, _, subset_nearBox_zero (by simp), isWitness_lhl2 h₆ hx' (by linarith) hy'⟩
  have h₇ : vgap - sideLH2 / 2 ≤ y := by
    by_contra h₇
    exact hslot ⟨by linarith, by linarith, by linarith, by linarith⟩
  exact ⟨_, _, subset_nearBox_zero (by simp),
    isWitness_lh2 (by linarith) (by linarith) h₇ hy'⟩

/-- Coverage of the period cell centred at the origin, by reflection of the quarter cell. -/
theorem exists_isWitness_of_abs {x y : ℝ} (hx : |x| ≤ hgap) (hy : |y| ≤ vgap / 2)
    (hslot : ¬ (root / 2 < |x| ∧ |x| < 2 * hgap - sideLHL2 / 2 ∧ sideH1 / 2 < |y| ∧
      |y| < vgap - sideLH2 / 2)) :
    ∃ L A, A ⊆ nearBox 0 0 ∧ IsWitness x y L A := by
  obtain ⟨L, A, hA, hw⟩ := exists_isWitness_of_nonneg (abs_nonneg x) hx (abs_nonneg y) hy hslot
  rcases le_or_gt 0 x with hx₀ | hx₀ <;> rcases le_or_gt 0 y with hy₀ | hy₀
  · rw [abs_of_nonneg hx₀, abs_of_nonneg hy₀] at hw
    exact ⟨L, A, hA, hw⟩
  · rw [abs_of_nonneg hx₀, abs_of_neg hy₀] at hw
    exact ⟨L, _, map_negSnd_subset_nearBox hA, by simpa using hw.neg_snd⟩
  · rw [abs_of_neg hx₀, abs_of_nonneg hy₀] at hw
    exact ⟨L, _, map_negFst_subset_nearBox hA, by simpa using hw.neg_fst⟩
  · rw [abs_of_neg hx₀, abs_of_neg hy₀] at hw
    exact ⟨L, _, map_negSnd_subset_nearBox (map_negFst_subset_nearBox hA),
      by simpa using hw.neg_fst.neg_snd⟩

end CenteredMaximal.Lattice
