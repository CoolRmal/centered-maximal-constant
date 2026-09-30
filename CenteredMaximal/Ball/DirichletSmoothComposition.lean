/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.DirichletLattice
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Tactic

/-!
# Smooth scalar composition in the Dirichlet space

Smooth one-Lipschitz scalar functions fixing zero act on `H₀¹(Ω)`. The value coordinate is
the scalar composition and each weak-gradient coordinate obeys the chain rule. The proof
passes from compactly supported smooth test functions to `H₀¹` using its closure definition
and dominated convergence in `L²`.
-/

@[expose] public section
open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal NNReal
noncomputable section
namespace CenteredMaximal.Ball.DirichletSobolev
variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- Smooth, one-Lipschitz functions fixing zero act on the Dirichlet space with the
expected coordinatewise chain rule. -/
theorem exists_mem_H01_smooth_comp {V : H1amb Ω} (hV : V ∈ H01 Ω)
    {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hLip : LipschitzWith 1 F) (hF0 : F 0 = 0)
    (hderiv : ∀ t, ‖deriv F t‖ ≤ 1) :
    ∃ W ∈ H01 Ω,
      (((W 0 : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
        =ᵐ[volume.restrict Ω] fun x => F (V 0 x : ℝ)) ∧
      ∀ i : Fin d,
        (((W i.succ : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
          =ᵐ[volume.restrict Ω] fun x => deriv F (V 0 x : ℝ) * (V i.succ x : ℝ)) := by
  classical
  have hVcl : V ∈ closure ((Submodule.span ℝ (testGraphSet Ω) : Submodule ℝ (H1amb Ω)) :
      Set (H1amb Ω)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hV
  obtain ⟨X, hXmem, hXt⟩ := mem_closure_iff_seq_limit.mp hVcl
  have hXmem' : ∀ n, X n ∈ testGraphSet Ω := fun n => by
    have := hXmem n
    rw [span_testGraphSet] at this
    exact this
  choose φ hφ hXφ using hXmem'
  set v : EuclideanSpace ℝ (Fin d) → ℝ := fun x => (V 0 x : ℝ) with hvdef
  set g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ := fun i x => (V i.succ x : ℝ) with hgdef
  have hvm : MemLp v 2 (volume.restrict Ω) := Lp.memLp _
  have hgm : ∀ i, MemLp (g i) 2 (volume.restrict Ω) := fun i => Lp.memLp _
  have hXcoord : Tendsto (fun n => (X n).ofLp) atTop (𝓝 V.ofLp) :=
    ((PiLp.continuous_ofLp 2 fun _ : Fin (d + 1) => L2D Ω).tendsto V).comp hXt
  have hX0 : Tendsto (fun n => X n 0) atTop (𝓝 (V 0)) := tendsto_pi_nhds.mp hXcoord 0
  have hXi : ∀ i : Fin d, Tendsto (fun n => eLpNorm (partialD i (φ n) - g i) 2
      (volume.restrict Ω)) atTop (𝓝 0) := by
    intro i
    have h1 : Tendsto (fun n => X n i.succ) atTop (𝓝 (V i.succ)) :=
      tendsto_pi_nhds.mp hXcoord i.succ
    have h2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp h1
    refine h2.congr fun n => eLpNorm_congr_ae ?_
    have e : X n i.succ = (hφ n).partialCls i := by rw [hXφ n, IsTestFn.testGraph_succ]
    rw [e]
    filter_upwards [((hφ n).memLp_partialD i).coeFn_toLp] with x hx
    simp only [IsTestFn.partialCls, Pi.sub_apply, hgdef, hx]
  have hmeas : TendstoInMeasure (volume.restrict Ω) φ atTop v := by
    have hX0' : Tendsto (fun n => eLpNorm (φ n - v) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
      have h2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hX0
      refine h2.congr fun n => eLpNorm_congr_ae ?_
      have e : X n 0 = (hφ n).testCls := by rw [hXφ n, IsTestFn.testGraph_zero]
      rw [e]
      filter_upwards [(hφ n).mem_lp.coeFn_toLp] with x hx
      simp only [IsTestFn.testCls, Pi.sub_apply, hvdef, hx]
    exact tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hX0'
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  let ψ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun j => φ (ns j)
  have hψ : ∀ j, IsTestFn Ω (ψ j) := fun j => hφ (ns j)
  let θ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun j => F ∘ ψ j
  have hθ : ∀ j, IsTestFn Ω (θ j) := fun j => (hψ j).comp_smooth hF hF0
  have hθgrad : ∀ j i x, partialD i (θ j) x = deriv F (ψ j x) * partialD i (ψ j) x :=
    fun j i x => partialD_comp_smooth (hψ j).1 hF i x
  have hθ0 (j : ℕ) : (hθ j).testCls =
      hLip.compLp hF0 ((hψ j).testCls) := by
    apply Lp.ext
    filter_upwards [(hθ j).mem_lp.coeFn_toLp, (hψ j).mem_lp.coeFn_toLp,
      hLip.coeFn_compLp hF0 ((hψ j).testCls)] with x ha hb hc
    calc
      ((hθ j).testCls x : ℝ) = θ j x := ha
      _ = F (((hψ j).testCls x : ℝ)) := by simp [θ, ψ, IsTestFn.testCls, hb]
      _ = (hLip.compLp hF0 ((hψ j).testCls) x : ℝ) := hc.symm
  let w0 : L2D Ω := hLip.compLp hF0 (V 0)
  have hw0 : (w0 : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => F (v x) := hLip.coeFn_compLp hF0 (V 0)
  have hderivcont : Continuous (deriv F) := hF.continuous_deriv (by simp)
  have hwm : ∀ i, MemLp (fun x => deriv F (v x) * g i x) 2 (volume.restrict Ω) := by
    intro i
    have hm : AEStronglyMeasurable (fun x => deriv F (v x) * g i x)
        (volume.restrict Ω) :=
      (hderivcont.comp_aestronglyMeasurable hvm.aestronglyMeasurable).mul
        (hgm i).aestronglyMeasurable
    refine (hgm i).of_le hm ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    simpa only [Real.norm_eq_abs, one_mul] using
      mul_le_mul_of_nonneg_right (hderiv (v x)) (abs_nonneg _)
  let w : H1amb Ω := WithLp.toLp 2 (Fin.cons w0 fun i => (hwm i).toLp _)
  have hw0' : ((w 0 : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => F (v x) := by simpa [w] using hw0
  have hwi : ∀ i, ((w i.succ : L2D Ω) : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x => deriv F (v x) * g i x := by
    intro i
    simpa [w] using (hwm i).coeFn_toLp
  have hψ0 : Tendsto (fun j => (hψ j).testCls) atTop (𝓝 (V 0)) := by
    convert hX0.comp hns.tendsto_atTop using 1
    funext j
    change (hφ (ns j)).testCls = X (ns j) 0
    rw [hXφ (ns j), IsTestFn.testGraph_zero]
  have hθ0t : Tendsto (fun j => (hθ j).testCls) atTop (𝓝 w0) := by
    have hcomp := ((hLip.continuous_compLp hF0).tendsto (V 0)).comp hψ0
    convert hcomp using 1
    funext j
    exact (hθ0 j).symm
  have hθit : ∀ i : Fin d,
      Tendsto (fun j => (hθ j).partialCls i) atTop (𝓝 ((hwm i).toLp _)) := by
    intro i
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun j => partialD i (θ j)) (fun j => (hθ j).memLp_partialD i)
      (fun x => deriv F (v x) * g i x) (hwm i)).mpr
    let A : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
      fun j x => deriv F (ψ j x) * (partialD i (ψ j) x - g i x)
    let B : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
      fun j x => (deriv F (ψ j x) - deriv F (v x)) * g i x
    have hsplit : ∀ j, (partialD i (θ j) - fun x => deriv F (v x) * g i x)
        = A j + B j := by
      intro j
      funext x
      simp only [Pi.sub_apply, Pi.add_apply, A, B, hθgrad]
      ring
    have hAm : ∀ j, AEStronglyMeasurable (A j) (volume.restrict Ω) := fun j =>
      (hderivcont.comp (hψ j).continuous).aestronglyMeasurable.mul
        (((hψ j).continuous_partialD i).aestronglyMeasurable.sub
          (hgm i).aestronglyMeasurable)
    have hBm : ∀ j, AEStronglyMeasurable (B j) (volume.restrict Ω) := fun j =>
      ((hderivcont.comp (hψ j).continuous).aestronglyMeasurable.sub
        (hderivcont.comp_aestronglyMeasurable hvm.aestronglyMeasurable)).mul
          (hgm i).aestronglyMeasurable
    have hAt : Tendsto (fun j => eLpNorm (A j) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        ((hXi i).comp hns.tendsto_atTop) (fun _ => zero_le) fun j => ?_
      refine eLpNorm_mono (hAm j) fun x => ?_
      simp only [A, Pi.sub_apply, ψ, Real.norm_eq_abs, abs_mul]
      calc
        |deriv F (φ (ns j) x)| * |partialD i (φ (ns j)) x - g i x|
            ≤ 1 * |partialD i (φ (ns j)) x - g i x| := by
              gcongr
              simpa only [Real.norm_eq_abs] using hderiv (φ (ns j) x)
        _ = |partialD i (φ (ns j)) x - g i x| := one_mul _
    have hBt : Tendsto (fun j => eLpNorm (B j) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
      have hBbound (j : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
          ‖B j x‖ ≤ ‖(2 : ℝ) * g i x‖ := by
        have hdiff : ‖deriv F (ψ j x) - deriv F (v x)‖ ≤ 2 := by
          calc
            ‖deriv F (ψ j x) - deriv F (v x)‖
                ≤ ‖deriv F (ψ j x)‖ + ‖deriv F (v x)‖ := norm_sub_le _ _
            _ ≤ 1 + 1 := add_le_add (hderiv _) (hderiv _)
            _ = 2 := by norm_num
        simp only [B, norm_mul]
        simpa only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
          mul_le_mul_of_nonneg_right hdiff (norm_nonneg (g i x))
      have hBoundMem : MemLp (fun x => (2 : ℝ) * g i x) 2 (volume.restrict Ω) :=
        (hgm i).const_mul 2
      have hrepr : ∀ j, eLpNorm (B j) 2 (volume.restrict Ω) =
          (∫⁻ x, ‖B j x‖ₑ ^ (2 : ℝ) ∂(volume.restrict Ω)) ^ (1 / (2 : ℝ)) := by
        intro j
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
          (hBm j),
          ENNReal.toReal_ofNat]
      simp only [hrepr]
      have hlim : Tendsto
          (fun j => ∫⁻ x, ‖B j x‖ₑ ^ (2 : ℝ) ∂(volume.restrict Ω)) atTop
          (𝓝 (∫⁻ _, (0 : ℝ≥0∞) ∂(volume.restrict Ω))) := by
        refine tendsto_lintegral_of_dominated_convergence'
          (fun x => ‖(2 : ℝ) * g i x‖ₑ ^ (2 : ℝ))
          (fun j => (hBm j).enorm.pow_const _)
          (fun j => Eventually.of_forall fun x => ?_) ?_ ?_
        · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe,
            ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
          exact hBbound j x
        · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero
            ENNReal.ofNat_ne_top hBoundMem).ne
        · filter_upwards [hae] with x hx
          have hderivpoint : Tendsto (fun j => deriv F (ψ j x)) atTop
              (𝓝 (deriv F (v x))) := (hderivcont.tendsto (v x)).comp hx
          have hBpoint : Tendsto (fun j => B j x) atTop (𝓝 0) := by
            have hconst : Tendsto (fun _ : ℕ => deriv F (v x)) atTop
                (𝓝 (deriv F (v x))) := tendsto_const_nhds
            have ht := (hderivpoint.sub hconst).mul_const (g i x)
            simpa only [B, sub_self, zero_mul] using ht
          have henorm : Tendsto (fun j => ‖B j x‖ₑ) atTop (𝓝 0) := by
            simpa only [Function.comp_def, enorm_zero] using
              ((continuous_enorm.tendsto (0 : ℝ)).comp hBpoint)
          have ht := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp
            henorm
          have htwo : (0 : ℝ) < 2 := by norm_num
          simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos htwo] using ht
      rw [lintegral_zero] at hlim
      have ht := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hlim
      have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
      simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos hhalf] using ht
    have hsum := hAt.add hBt
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => zero_le) fun j => ?_
    rw [hsplit j]
    exact eLpNorm_add_le one_le_two
  have hwmem : w ∈ H01 Ω := by
    refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto (b := atTop) ?_
      (Eventually.of_forall fun j => by
        exact (Submodule.span ℝ (testGraphSet Ω)).le_topologicalClosure
          (Submodule.subset_span ⟨θ j, hθ j, rfl⟩))
    have hgraph : (fun j => (hθ j).testGraph) =
        fun j => WithLp.toLp 2 (Fin.cons (hθ j).testCls
          fun i => (hθ j).partialCls i) := rfl
    rw [hgraph]
    refine ((PiLp.continuous_toLp 2 fun _ : Fin (d + 1) => L2D Ω).tendsto _).comp
      (tendsto_pi_nhds.mpr fun j => ?_)
    induction j using Fin.cases with
    | zero => simpa only [Fin.cons_zero, w, PiLp.toLp_apply] using hθ0t
    | succ i => simpa only [Fin.cons_succ, w, PiLp.toLp_apply] using hθit i
  exact ⟨w, hwmem, hw0', hwi⟩

/-- Dominated pointwise convergence to zero implies convergence in `L²`. The bound is
itself an `L²` function, so this works on domains of infinite measure too. -/
theorem tendsto_eLpNorm_two_zero_of_dominated {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {F : ℕ → α → ℝ} {bound : α → ℝ}
    (hboundLp : MemLp bound 2 μ)
    (hFmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound : ∀ n x, ‖F n x‖ ≤ ‖bound x‖)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 μ) atTop (𝓝 0) := by
  have hrepr : ∀ n, eLpNorm (F n) 2 μ =
      (∫⁻ x, ‖F n x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := fun n => by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (hFmeas n),
      ENNReal.toReal_ofNat]
  simp only [hrepr]
  have hlim : Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ (2 : ℝ) ∂μ) atTop
      (𝓝 (∫⁻ _, (0 : ℝ≥0∞) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence'
      (fun x => ‖bound x‖ₑ ^ (2 : ℝ))
      (fun n => (hFmeas n).enorm.pow_const _)
      (fun n => Eventually.of_forall fun x => ?_) ?_ ?_
    · refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe,
        ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
      exact hbound n x
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero
        ENNReal.ofNat_ne_top hboundLp).ne
    · filter_upwards [hpoint] with x hx
      have henorm : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
        simpa only [Function.comp_def, enorm_zero] using
          ((continuous_enorm.tendsto (0 : ℝ)).comp hx)
      have ht := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp henorm
      have htwo : (0 : ℝ) < 2 := by norm_num
      simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos htwo] using ht
  rw [lintegral_zero] at hlim
  have ht := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0).comp hlim
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos hhalf] using ht
end CenteredMaximal.Ball.DirichletSobolev
