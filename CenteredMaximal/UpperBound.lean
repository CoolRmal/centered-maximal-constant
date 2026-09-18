/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Basic
public import Mathlib.MeasureTheory.Covering.Vitali

/-!
# The upper bound `c_d ≤ 2ᵈ`

Let `E = {M f > α}`. Every `x ∈ E` is the centre of a cube `Q_x` with `α |Q_x| < ∫_{Q_x} |f|`;
these cubes have bounded radii. Mathlib's Vitali lemma with enlargement `τ > 1` selects a disjoint
subfamily such that every `Q_x` meets a selected `Q_b` with `r_x ≤ τ r_b`. Then the *centre*
`x` lies in the cube of radius `(1 + τ) r_b` about `b`; covering only the centres is what saves
the factor `3ᵈ` of the uncentred argument. Summing over the disjoint selected cubes gives
`α |E| ≤ (1 + τ)ᵈ ‖f‖₁`, and letting `τ → 1` gives `2ᵈ` (Tao, 245A Notes 5, Exercise 42, whose
hint notes that one needs an epsilon of room).
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal Topology

namespace CenteredMaximal

variable {d : ℕ}

/-- In dimension `0` the space is a point, and `1` is a weak type bound. -/
theorem isWeakTypeBound_one_of_dim_zero : IsWeakTypeBound 0 1 := by
  intro f _ α
  have hM : ∀ x, maximalFunction f x ≤ ∫⁻ y, ‖f y‖ₑ := fun x => iSup₂_le fun r hr => by
    rw [volume_closedBall_eq x hr.le, pow_zero, ENNReal.ofReal_one, inv_one, one_mul]
    exact setLIntegral_le_lintegral _ _
  rcases Set.eq_empty_or_nonempty {x | α < maximalFunction f x} with hE | ⟨x, hx⟩
  · simp [hE]
  have huniv : (univ : Set (Fin 0 → ℝ)) = closedBall 0 1 :=
    (Set.eq_univ_of_forall fun y => by
      rw [Subsingleton.elim y 0]
      exact mem_closedBall_self zero_le_one).symm
  have hvol : volume {x | α < maximalFunction f x} ≤ 1 := by
    calc volume {x | α < maximalFunction f x} ≤ volume (univ : Set (Fin 0 → ℝ)) :=
          measure_mono (subset_univ _)
      _ = 1 := by
          rw [huniv, volume_closedBall_eq _ zero_le_one, pow_zero, ENNReal.ofReal_one]
  calc α * volume {x | α < maximalFunction f x} ≤ α * 1 := by gcongr
    _ ≤ 1 * ∫⁻ y, ‖f y‖ₑ := by
        rw [mul_one, one_mul]
        exact (hx.trans_le (hM x)).le

/-- A cube whose volume times `α ∈ (0, ∞)` stays below a finite `K` has radius at most
`max 1 (K / α)`, in positive dimension. -/
theorem radius_le_of_mul_volume_lt (hd : 0 < d) {α K : ℝ≥0∞} (hα : 0 < α) (hα' : α ≠ ∞)
    (hK : K ≠ ∞) {x : Fin d → ℝ} {r : ℝ} (hr : 0 < r) (h : α * volume (closedBall x r) < K) :
    r ≤ max 1 (K / α).toReal := by
  by_contra hlt
  rw [not_le] at hlt
  have h₁ : 1 < r := (le_max_left _ _).trans_lt hlt
  have h₂ : (K / α).toReal < r := (le_max_right _ _).trans_lt hlt
  have h₃ : K / α ≤ volume (closedBall x r) := by
    rw [volume_closedBall_eq x hr.le, ← ENNReal.ofReal_toReal (ENNReal.div_ne_top hK hα.ne')]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (K / α).toReal ≤ 2 * r := by linarith
      _ ≤ (2 * r) ^ d := le_self_pow₀ (by linarith) hd.ne'
  have h₄ : α * (K / α) ≤ α * volume (closedBall x r) := by gcongr
  rw [ENNReal.mul_div_cancel hα.ne' hα'] at h₄
  exact h.not_ge h₄

/-- The Vitali argument with an epsilon of room: `α |{M f > α}| ≤ (1 + τ)ᵈ ‖f‖₁` for `τ > 1`. -/
theorem mul_volume_le_of_one_lt (hd : 0 < d) {f : (Fin d → ℝ) → ℝ} (hf : Integrable f)
    (α : ℝ≥0∞) {τ : ℝ} (hτ : 1 < τ) :
    α * volume {x | α < maximalFunction f x} ≤ ENNReal.ofReal ((1 + τ) ^ d) * ∫⁻ x, ‖f x‖ₑ := by
  set K := ∫⁻ x, ‖f x‖ₑ with hK_def
  have hK : K ≠ ∞ := (hasFiniteIntegral_iff_enorm.1 hf.2).ne
  rcases eq_or_ne α 0 with rfl | hα₀
  · simp
  rcases eq_or_ne α ∞ with rfl | hαt
  · simp
  have hα : 0 < α := pos_iff_ne_zero.2 hα₀
  set E := {x | α < maximalFunction f x}
  have hex : ∀ x ∈ E, ∃ r, 0 < r ∧
      α * volume (closedBall x r) < ∫⁻ y in closedBall x r, ‖f y‖ₑ := by
    intro x hx
    obtain ⟨r, hr, hlt⟩ := exists_lt_average_of_lt_maximalFunction hx
    refine ⟨r, hr, ?_⟩
    have hv₀ : volume (closedBall x r) ≠ 0 := by
      rw [volume_closedBall_eq x hr.le]
      exact ENNReal.ofReal_ne_zero_iff.2 (by positivity)
    rwa [← ENNReal.div_eq_inv_mul, ENNReal.lt_div_iff_mul_lt (Or.inl hv₀)
      (Or.inl measure_closedBall_lt_top.ne)] at hlt
  choose! ρ hρ₀ hρ using hex
  have hR : ∀ x ∈ E, ρ x ≤ max 1 (K / α).toReal := fun x hx =>
    radius_le_of_mul_volume_lt hd hα hαt hK (hρ₀ x hx)
      ((hρ x hx).trans_le (setLIntegral_le_lintegral _ _))
  obtain ⟨u, huE, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun x => closedBall x (ρ x)) E ρ τ hτ (fun x hx => (hρ₀ x hx).le) _ hR
    fun x hx => ⟨x, mem_closedBall_self (hρ₀ x hx).le⟩
  have hu : u.Countable := hdisj.countable_of_nonempty_interior fun x hx =>
    ⟨x, interior_maximal ball_subset_closedBall isOpen_ball (mem_ball_self (hρ₀ x (huE hx)))⟩
  have hcover : E ⊆ ⋃ b ∈ u, closedBall b ((1 + τ) * ρ b) := by
    intro a ha
    obtain ⟨b, hbu, ⟨z, hza, hzb⟩, hab⟩ := hcov a ha
    refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
    rw [mem_closedBall] at hza hzb ⊢
    calc dist a b ≤ dist z a + dist z b := dist_triangle_left a b z
      _ ≤ (1 + τ) * ρ b := by linarith
  have hvol : volume E ≤
      ENNReal.ofReal ((1 + τ) ^ d) * ∑' b : u, volume (closedBall (b : Fin d → ℝ) (ρ b)) :=
    calc volume E ≤ volume (⋃ b ∈ u, closedBall b ((1 + τ) * ρ b)) := measure_mono hcover
      _ ≤ ∑' b : u, volume (closedBall (b : Fin d → ℝ) ((1 + τ) * ρ b)) :=
          measure_biUnion_le volume hu _
      _ = ∑' b : u, ENNReal.ofReal ((1 + τ) ^ d) *
            volume (closedBall (b : Fin d → ℝ) (ρ b)) := by
          congr 1
          ext b
          have hb := hρ₀ b (huE b.2)
          rw [volume_closedBall_eq _ (by positivity), volume_closedBall_eq _ hb.le,
            ← ENNReal.ofReal_mul (by positivity), mul_left_comm, mul_pow]
      _ = _ := ENNReal.tsum_mul_left
  have hint : α * ∑' b : u, volume (closedBall (b : Fin d → ℝ) (ρ b)) ≤ K :=
    calc α * ∑' b : u, volume (closedBall (b : Fin d → ℝ) (ρ b))
        = ∑' b : u, α * volume (closedBall (b : Fin d → ℝ) (ρ b)) := ENNReal.tsum_mul_left.symm
      _ ≤ ∑' b : u, ∫⁻ y in closedBall (b : Fin d → ℝ) (ρ b), ‖f y‖ₑ :=
          ENNReal.tsum_le_tsum fun b => (hρ b (huE b.2)).le
      _ = ∫⁻ y in ⋃ b ∈ u, closedBall b (ρ b), ‖f y‖ₑ :=
          (lintegral_biUnion hu (fun _ _ => measurableSet_closedBall) hdisj _).symm
      _ ≤ K := setLIntegral_le_lintegral _ _
  calc α * volume E
      ≤ α * (ENNReal.ofReal ((1 + τ) ^ d) *
          ∑' b : u, volume (closedBall (b : Fin d → ℝ) (ρ b))) := by gcongr
    _ = ENNReal.ofReal ((1 + τ) ^ d) *
          (α * ∑' b : u, volume (closedBall (b : Fin d → ℝ) (ρ b))) := by ring
    _ ≤ ENNReal.ofReal ((1 + τ) ^ d) * K := by gcongr

/-- `2ᵈ` is a weak type bound in dimension `d`. -/
theorem isWeakTypeBound_two_pow (d : ℕ) : IsWeakTypeBound d (2 ^ d) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simpa using isWeakTypeBound_one_of_dim_zero
  intro f hf α
  have hK : ∫⁻ x, ‖f x‖ₑ ≠ ∞ := (hasFiniteIntegral_iff_enorm.1 hf.2).ne
  have hpow : Tendsto (fun τ : ℝ => ENNReal.ofReal ((1 + τ) ^ d)) (𝓝[>] 1) (𝓝 (2 ^ d)) := by
    have h : Tendsto (fun τ : ℝ => (1 + τ) ^ d) (𝓝 1) (𝓝 (2 ^ d)) := by
      have hc : Continuous fun τ : ℝ => (1 + τ) ^ d := by fun_prop
      simpa [one_add_one_eq_two] using hc.tendsto 1
    have h' := ENNReal.tendsto_ofReal (h.mono_left (nhdsWithin_le_nhds (s := Ioi 1)))
    rwa [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat] at h'
  exact ge_of_tendsto (ENNReal.Tendsto.mul_const hpow (Or.inr hK))
    (eventually_nhdsWithin_of_forall fun τ hτ => mul_volume_le_of_one_lt hd hf α hτ)

end CenteredMaximal
