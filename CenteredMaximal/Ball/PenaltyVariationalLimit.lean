/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.PenaltyCompactness
public import Mathlib.Tactic

/-!
# Variational inequality at a weak penalty limit

A negative-part penalization gives a variational inequality against every positive test.
Weak convergence preserves this inequality because the Dirichlet form is nonnegative on
diagonal differences. Vanishing negative parts ensure that the limit itself is nonnegative.
-/

@[expose] public section
open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped RealInnerProductSpace ENNReal
noncomputable section
namespace CenteredMaximal.Ball

private instance l2PosSMulMonoForVariationalLimit
    {X : Type*} [MeasurableSpace X] {μ : Measure X} :
    PosSMulMono ℝ (Lp ℝ 2 μ) where
  smul_le_smul_of_nonneg_left := by
    intro a ha f g hfg
    rw [← Lp.coeFn_le] at hfg ⊢
    filter_upwards [hfg, Lp.coeFn_smul a f, Lp.coeFn_smul a g]
      with x hx hf hg
    rw [hf, hg]
    exact mul_le_mul_of_nonneg_left hx ha

/-- Weak limits preserve variational inequalities for a nonnegative bilinear form,
using weak lower semicontinuity of the quadratic energy. -/
theorem variational_inequality_of_weak_penalty_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (B : H →L[ℝ] H →L[ℝ] ℝ) (source : H →L[ℝ] ℝ)
    (u : ℕ → H) (U : H) (χ : ℕ → ℕ)
    (hweak : Tendsto (fun k => toWeakSpace ℝ H (u (χ k))) atTop
      (𝓝 (toWeakSpace ℝ H U)))
    (hBpos : ∀ w : H, 0 ≤ B w w)
    {C : Set H}
    (hVI : ∀ k (V : H), V ∈ C →
      source (V - u k) ≤ B (u k) (V - u k)) :
    ∀ V : H, V ∈ C → source (V - U) ≤ B U (V - U) := by
  intro V hVC
  have hweak_eval (ℓ : H →L[ℝ] ℝ) :
      Tendsto (fun k => ℓ (u (χ k))) atTop (𝓝 (ℓ U)) := by
    have hc := ℓ.continuous_comp_toWeakSpace_symm
    have h := hc.continuousAt.tendsto.comp hweak
    simpa [Function.comp_def] using h
  have hleft : Tendsto (fun k => source (V - u (χ k))) atTop
      (𝓝 (source (V - U))) := by
    simp_rw [map_sub]
    exact tendsto_const_nhds.sub (hweak_eval source)
  have hright : Tendsto
      (fun k => B (u (χ k)) (V - U) - B U (u (χ k) - U)) atTop
      (𝓝 (B U (V - U))) := by
    have hterm₁ := hweak_eval (B.flip (V - U))
    have hterm₂ : Tendsto (fun k => B U (u (χ k) - U)) atTop (𝓝 0) := by
      simp_rw [map_sub]
      convert (hweak_eval (B U)).sub_const (B U U) using 1
      simp
    convert hterm₁.sub hterm₂ using 1 <;> simp
  have hineq : ∀ k,
      source (V - u (χ k)) ≤
        B (u (χ k)) (V - U) - B U (u (χ k) - U) := by
    intro k
    have h := hVI (χ k) V hVC
    have hpos := hBpos (u (χ k) - U)
    have hform : B (u (χ k) - U) (u (χ k) - U) =
        B (u (χ k)) (u (χ k) - U) - B U (u (χ k) - U) := by
      simp
    have hdir : B (u (χ k)) (V - u (χ k)) =
        B (u (χ k)) (V - U) - B (u (χ k)) (u (χ k) - U) := by
      have : V - u (χ k) = (V - U) - (u (χ k) - U) := by abel
      rw [this, map_sub]
    rw [hform] at hpos
    rw [hdir] at h
    linarith
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hineq)

/-- Vanishing negative parts and weak convergence force a nonnegative limit. -/
theorem nonneg_of_weak_limit_and_negPart_tendsto_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (J : H →L[ℝ] Lp ℝ 2 μ)
    (u : ℕ → H) (U : H) (χ : ℕ → ℕ)
    (hweak : Tendsto (fun k => toWeakSpace ℝ H (u (χ k))) atTop
      (𝓝 (toWeakSpace ℝ H U)))
    (hneg : Tendsto (fun k => Lp.negPart (J (u (χ k)))) atTop (𝓝 0)) :
    0 ≤ J U := by
  let z : ℕ → Lp ℝ 2 μ := fun k => J (u (χ k)) + Lp.negPart (J (u (χ k)))
  have hzpos : ∀ k, 0 ≤ z k := by
    intro k
    rw [← Lp.coeFn_nonneg]
    filter_upwards [Lp.coeFn_add (J (u (χ k))) (Lp.negPart (J (u (χ k)))),
      Lp.coeFn_negPart_eq_max (J (u (χ k)))] with x hsum hneg'
    rw [hsum]
    simp only [Pi.zero_apply, Pi.add_apply, hneg']
    have hle : -((J (u (χ k)) x : ℝ)) ≤ max (-((J (u (χ k)) x : ℝ))) 0 :=
      le_max_left _ _
    linarith
  have hJweak : Tendsto
      (fun k => toWeakSpace ℝ (Lp ℝ 2 μ) (J (u (χ k)))) atTop
      (𝓝 (toWeakSpace ℝ (Lp ℝ 2 μ) (J U))) := by
    have hc := (WeakSpace.map J).continuous
    convert hc.tendsto (toWeakSpace ℝ H U) |>.comp hweak using 1 <;> rfl
  have hnegweak : Tendsto
      (fun k => toWeakSpace ℝ (Lp ℝ 2 μ) (Lp.negPart (J (u (χ k))))) atTop
      (𝓝 (0 : WeakSpace ℝ (Lp ℝ 2 μ))) := by
    have hc := (toWeakSpaceCLM ℝ (Lp ℝ 2 μ)).continuous
    convert hc.tendsto (0 : Lp ℝ 2 μ) |>.comp hneg using 1 <;> rfl
  have hzweak : Tendsto (fun k => toWeakSpace ℝ (Lp ℝ 2 μ) (z k)) atTop
      (𝓝 (toWeakSpace ℝ (Lp ℝ 2 μ) (J U))) := by
    convert hJweak.add hnegweak using 1 <;> simp [z]
  have hCweak : IsClosed
      (toWeakSpace ℝ (Lp ℝ 2 μ) '' Set.Ici (0 : Lp ℝ 2 μ)) :=
    (convex_Ici (0 : Lp ℝ 2 μ)).isClosed_toWeakSpace_image isClosed_Ici
  have hmem := hCweak.mem_of_tendsto hzweak
    (Eventually.of_forall fun k => ⟨z k, hzpos k, rfl⟩)
  rcases hmem with ⟨v, hv, heq⟩
  have : v = J U := (toWeakSpace ℝ (Lp ℝ 2 μ)).injective heq
  simpa [this] using hv

/-- The negative-part penalty is nonnegative on a variation toward a positive state. -/
theorem inner_negPart_sub_nonneg
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (x y : Lp ℝ 2 μ) (hy : 0 ≤ y) :
    0 ≤ ⟪Lp.negPart x, y - x⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [(Lp.coeFn_nonneg y).2 hy, Lp.coeFn_sub y x,
    Lp.coeFn_negPart_eq_max x] with z hyz hsub hnegz
  simp only [Pi.zero_apply] at hyz
  rw [hsub, hnegz]
  simp only [Pi.sub_apply, Real.inner_apply, Pi.zero_apply]
  by_cases hx : 0 ≤ (x z : ℝ)
  · rw [max_eq_right (neg_nonpos.mpr hx)]
    simp
  · have hx' : (x z : ℝ) < 0 := lt_of_not_ge hx
    rw [max_eq_left (neg_nonneg.mpr hx'.le)]
    exact mul_nonneg (neg_nonneg.mpr hx'.le) (sub_nonneg.mpr (by linarith))

/-- Every penalized equation yields the obstacle variational inequality against positive tests. -/
theorem variational_inequality_of_penalized_equation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (J : H →L[ℝ] Lp ℝ 2 μ) (source : H →L[ℝ] ℝ)
    (u : H) (weight : ℝ) (hweight : 0 ≤ weight)
    (heq : ∀ V, B u V = source V + weight * ⟪Lp.negPart (J u), J V⟫_ℝ)
    (V : H) (hV : 0 ≤ J V) :
    source (V - u) ≤ B u (V - u) := by
  rw [heq]
  have hpen := inner_negPart_sub_nonneg (J u) (J V) hV
  have hpen' : 0 ≤ ⟪Lp.negPart (J u), J (V - u)⟫_ℝ := by
    simpa only [map_sub] using hpen
  exact le_add_of_nonneg_right (mul_nonneg hweight hpen')

end CenteredMaximal.Ball
