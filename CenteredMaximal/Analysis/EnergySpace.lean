/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.JumpEnergy
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpOrder

/-!
# The energy Hilbert space of the coordinate generator

For `α : ℝ` the energy space `H_α = {u ∈ L²(ℝ²) : E(u, u) < ∞}` of the jump energy
`E = jumpEnergy α` is a real Hilbert space for the inner product
`⟪u, v⟫_H = ⟪u, v⟫_{L²} + E(u, v)`. This file constructs it.

* `jumpEnergy_congr_ae`, `jumpForm_congr_ae`: the energy and the form only depend on the almost
  everywhere class, since the shift `(x, t) ↦ x + t e_j` and the projection `(x, t) ↦ x` are
  quasi-measure-preserving (`quasiMeasurePreserving_add_smul_single`); this lets the lemmas of
  `CenteredMaximal.Analysis.JumpEnergy` be used for a.e.-measurable functions
  (`jumpForm_add_left_of_aemeasurable`, ...);
* `energySubmodule`, `EnergySpace`: the subspace `{u | jumpEnergy α u ≠ ⊤}` of `L²`, and the type
  synonym carrying the energy norm; `EnergySpace.toLp`, `EnergySpace.toLpCLM` are the inclusion
  into `L²`, of norm at most one (`EnergySpace.norm_toLp_le`);
* `EnergySpace.inner_def`, `EnergySpace.norm_sq_eq`, `EnergySpace.jumpForm_eq`,
  `EnergySpace.jumpEnergy_eq`: the inner product, the norm and the form in the energy space;
* `EnergySpace.nonnegCone`: the closed convex cone of nonnegative functions,
  `EnergySpace.posPart`, `EnergySpace.inf`: truncation and minimum, with the Markov inequality
  `EnergySpace.jumpForm_posPart_self_le`;
* `jumpEnergy_le_liminf`: Fatou's lemma for the energy, and the instance
  `CompleteSpace (EnergySpace α)`: a Cauchy sequence converges in `L²`, a subsequence converges
  almost everywhere, and Fatou's lemma shows that the limit has finite energy and that the
  energies of the differences tend to zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace CenteredMaximal

/-- `L²(ℝ²)` with respect to Lebesgue measure. -/
local notation "L²" => Lp ℝ 2 (volume : Measure (Fin 2 → ℝ))

/-! ### Invariance under almost everywhere modification -/

/-- The shift `(x, t) ↦ x + t e_j` is quasi-measure-preserving from the product of Lebesgue
measures to Lebesgue measure: each section `x ↦ x + t e_j` is a translation. -/
theorem quasiMeasurePreserving_add_smul_single (j : Fin 2) :
    Measure.QuasiMeasurePreserving (fun p : (Fin 2 → ℝ) × ℝ => p.1 + p.2 • Pi.single j 1)
      volume volume := by
  have hm : Measurable fun p : (Fin 2 → ℝ) × ℝ => p.1 + p.2 • Pi.single j 1 :=
    measurable_fst.add (measurable_snd.smul_const _)
  refine ⟨hm, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply hm hs, Measure.volume_eq_prod, Measure.prod_apply_symm (hm hs)]
  have : ∀ t : ℝ, volume ((fun x : Fin 2 → ℝ => (x, t)) ⁻¹'
      ((fun p : (Fin 2 → ℝ) × ℝ => p.1 + p.2 • Pi.single j 1) ⁻¹' s)) = 0 := fun t => by
    have h := measure_preimage_add_right (volume : Measure (Fin 2 → ℝ)) (t • Pi.single j 1) s
    rw [hs0] at h
    exact h
  simp [this]

/-- The projection `(x, t) ↦ x` is quasi-measure-preserving. -/
theorem quasiMeasurePreserving_prod_fst :
    Measure.QuasiMeasurePreserving (Prod.fst : (Fin 2 → ℝ) × ℝ → Fin 2 → ℝ) volume volume :=
  Measure.quasiMeasurePreserving_fst

/-- The jump energy only depends on the almost everywhere class. -/
theorem jumpEnergy_congr_ae (α : ℝ) {u v : (Fin 2 → ℝ) → ℝ} (h : u =ᵐ[volume] v) :
    jumpEnergy α u = jumpEnergy α v := by
  unfold jumpEnergy
  refine Finset.sum_congr rfl fun j _ => lintegral_congr_ae ?_
  filter_upwards [(quasiMeasurePreserving_add_smul_single j).ae h,
    quasiMeasurePreserving_prod_fst.ae h] with p h₁ h₂
  rw [h₁, h₂]

/-- The jump form only depends on the almost everywhere classes. -/
theorem jumpForm_congr_ae (α : ℝ) {u u' v v' : (Fin 2 → ℝ) → ℝ} (hu : u =ᵐ[volume] u')
    (hv : v =ᵐ[volume] v') : jumpForm α u v = jumpForm α u' v' := by
  unfold jumpForm
  refine Finset.sum_congr rfl fun j _ => integral_congr_ae ?_
  filter_upwards [(quasiMeasurePreserving_add_smul_single j).ae hu,
    quasiMeasurePreserving_prod_fst.ae hu, (quasiMeasurePreserving_add_smul_single j).ae hv,
    quasiMeasurePreserving_prod_fst.ae hv] with p h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

/-- The energy of the zero function vanishes. -/
theorem jumpEnergy_zero (α : ℝ) : jumpEnergy α 0 = 0 := by
  unfold jumpEnergy
  simp

/-! ### Almost everywhere measurable functions -/

/-- A measurable representative of an a.e.-measurable function has the same energy. -/
theorem jumpEnergy_mk (α : ℝ) {u : (Fin 2 → ℝ) → ℝ} (hu : AEMeasurable u volume) :
    jumpEnergy α (hu.mk u) = jumpEnergy α u :=
  (jumpEnergy_congr_ae α hu.ae_eq_mk).symm

/-- `jumpEnergy_add_le` for an a.e.-measurable function. -/
theorem jumpEnergy_add_le_of_aemeasurable (α : ℝ) {u : (Fin 2 → ℝ) → ℝ}
    (hu : AEMeasurable u volume) (v : (Fin 2 → ℝ) → ℝ) :
    jumpEnergy α (u + v) ≤ 2 * (jumpEnergy α u + jumpEnergy α v) := by
  rw [jumpEnergy_congr_ae α (hu.ae_eq_mk.add EventuallyEq.rfl), ← jumpEnergy_mk α hu]
  exact jumpEnergy_add_le α hu.measurable_mk v

/-- `jumpForm_add_left` for a.e.-measurable functions. -/
theorem jumpForm_add_left_of_aemeasurable (α : ℝ) {u v w : (Fin 2 → ℝ) → ℝ}
    (hu : AEMeasurable u volume) (hv : AEMeasurable v volume) (hw : AEMeasurable w volume)
    (hu' : jumpEnergy α u ≠ ⊤) (hv' : jumpEnergy α v ≠ ⊤) (hw' : jumpEnergy α w ≠ ⊤) :
    jumpForm α (u + v) w = jumpForm α u w + jumpForm α v w := by
  rw [jumpForm_congr_ae α (hu.ae_eq_mk.add hv.ae_eq_mk) hw.ae_eq_mk,
    jumpForm_congr_ae α hu.ae_eq_mk hw.ae_eq_mk, jumpForm_congr_ae α hv.ae_eq_mk hw.ae_eq_mk]
  exact jumpForm_add_left α hu.measurable_mk hv.measurable_mk hw.measurable_mk
    ((jumpEnergy_mk α hu).trans_ne hu') ((jumpEnergy_mk α hv).trans_ne hv')
    ((jumpEnergy_mk α hw).trans_ne hw')

/-- `jumpForm_self` for an a.e.-measurable function. -/
theorem jumpForm_self_of_aemeasurable (α : ℝ) {u : (Fin 2 → ℝ) → ℝ} (hu : AEMeasurable u volume)
    (hu' : jumpEnergy α u ≠ ⊤) : ENNReal.ofReal (jumpForm α u u) = jumpEnergy α u := by
  rw [jumpForm_congr_ae α hu.ae_eq_mk hu.ae_eq_mk, ← jumpEnergy_mk α hu]
  exact jumpForm_self α hu.measurable_mk ((jumpEnergy_mk α hu).trans_ne hu')

/-- `jumpForm_sq_le` for a.e.-measurable functions. -/
theorem jumpForm_sq_le_of_aemeasurable (α : ℝ) {u v : (Fin 2 → ℝ) → ℝ}
    (hu : AEMeasurable u volume) (hv : AEMeasurable v volume) (hu' : jumpEnergy α u ≠ ⊤)
    (hv' : jumpEnergy α v ≠ ⊤) : jumpForm α u v ^ 2 ≤ jumpForm α u u * jumpForm α v v := by
  rw [jumpForm_congr_ae α hu.ae_eq_mk hv.ae_eq_mk, jumpForm_congr_ae α hu.ae_eq_mk hu.ae_eq_mk,
    jumpForm_congr_ae α hv.ae_eq_mk hv.ae_eq_mk]
  exact jumpForm_sq_le α hu.measurable_mk hv.measurable_mk ((jumpEnergy_mk α hu).trans_ne hu')
    ((jumpEnergy_mk α hv).trans_ne hv')

/-- `jumpForm_posPart_self_le` for an a.e.-measurable function. -/
theorem jumpForm_posPart_self_le_of_aemeasurable (α : ℝ) {u : (Fin 2 → ℝ) → ℝ}
    (hu : AEMeasurable u volume) (hu' : jumpEnergy α u ≠ ⊤) :
    jumpForm α (posPart u) (posPart u) ≤ jumpForm α u (posPart u) := by
  have h : posPart u =ᵐ[volume] posPart (hu.mk u) :=
    hu.ae_eq_mk.mono fun x hx => by simp only [posPart, hx]
  rw [jumpForm_congr_ae α h h, jumpForm_congr_ae α hu.ae_eq_mk h]
  exact jumpForm_posPart_self_le α hu.measurable_mk ((jumpEnergy_mk α hu).trans_ne hu')

/-- `jumpEnergy_inf_le` for an a.e.-measurable function. -/
theorem jumpEnergy_inf_le_of_aemeasurable (α : ℝ) {u : (Fin 2 → ℝ) → ℝ}
    (hu : AEMeasurable u volume) (v : (Fin 2 → ℝ) → ℝ) :
    jumpEnergy α (fun x => min (u x) (v x)) ≤ jumpEnergy α u + jumpEnergy α v := by
  have h : (fun x => min (u x) (v x)) =ᵐ[volume] fun x => min (hu.mk u x) (v x) :=
    hu.ae_eq_mk.mono fun x hx => by simp only [hx]
  rw [jumpEnergy_congr_ae α h, ← jumpEnergy_mk α hu]
  exact jumpEnergy_inf_le α hu.measurable_mk

/-! ### Fatou's lemma -/

/-- **Fatou's lemma** for the jump energy: the energy of an almost everywhere limit is at most
the lower limit of the energies. -/
theorem jumpEnergy_le_liminf (α : ℝ) {f : ℕ → (Fin 2 → ℝ) → ℝ} {g : (Fin 2 → ℝ) → ℝ}
    (hf : ∀ i, Measurable (f i)) (hg : Measurable g)
    (hfg : ∀ᵐ x ∂volume, Tendsto (fun i => f i x) atTop (𝓝 (g x))) :
    jumpEnergy α g ≤ liminf (fun i => jumpEnergy α (f i)) atTop := by
  -- the integrand, summed over the two coordinates
  obtain ⟨I, hI⟩ : ∃ I : ((Fin 2 → ℝ) → ℝ) → (Fin 2 → ℝ) × ℝ → ℝ≥0∞, ∀ u p, I u p =
      ∑ j : Fin 2, ENNReal.ofReal ((u (p.1 + p.2 • Pi.single j 1) - u p.1) ^ 2 *
        |p.2| ^ (-(1 + α))) := ⟨_, fun _ _ => rfl⟩
  have hE : ∀ u : (Fin 2 → ℝ) → ℝ, Measurable u → jumpEnergy α u = ∫⁻ p, I u p := fun u hu => by
    simp only [hI]
    exact (lintegral_finsetSum _ fun j _ => measurable_jumpIntegrand α hu j).symm
  have hmeas : ∀ i, Measurable fun p => I (f i) p := fun i => by
    simp only [hI]
    exact Finset.measurable_sum _ fun j _ => measurable_jumpIntegrand α (hf i) j
  -- pointwise convergence of the integrands, almost everywhere
  have hconv : ∀ᵐ p ∂(volume : Measure ((Fin 2 → ℝ) × ℝ)),
      Tendsto (fun i => I (f i) p) atTop (𝓝 (I g p)) := by
    filter_upwards [ae_all_iff.2 fun j => (quasiMeasurePreserving_add_smul_single j).ae hfg,
      quasiMeasurePreserving_prod_fst.ae hfg] with p h₁ h₂
    simp only [hI]
    exact tendsto_finsetSum _ fun j _ =>
      ENNReal.tendsto_ofReal ((((h₁ j).sub h₂).pow 2).mul_const _)
  rw [hE g hg, show (fun i => jumpEnergy α (f i)) = fun i => ∫⁻ p, I (f i) p from
    funext fun i => hE _ (hf i)]
  calc ∫⁻ p, I g p = ∫⁻ p, liminf (fun i => I (f i) p) atTop :=
        lintegral_congr_ae (hconv.mono fun p hp => hp.liminf_eq.symm)
    _ ≤ liminf (fun i => ∫⁻ p, I (f i) p) atTop := lintegral_liminf_le hmeas

/-! ### The energy space -/

/-- The functions of finite jump energy form a subspace of `L²(ℝ²)`. -/
def energySubmodule (α : ℝ) : Submodule ℝ L² where
  carrier := {u | jumpEnergy α u ≠ ⊤}
  add_mem' {u v} hu hv := by
    show jumpEnergy α ⇑(u + v) ≠ ⊤
    rw [jumpEnergy_congr_ae α (Lp.coeFn_add u v)]
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.add_ne_top.2 ⟨hu, hv⟩))
      (jumpEnergy_add_le_of_aemeasurable α (Lp.aestronglyMeasurable u).aemeasurable v)
  zero_mem' := by
    show jumpEnergy α ⇑(0 : L²) ≠ ⊤
    rw [jumpEnergy_congr_ae α (Lp.coeFn_zero ℝ 2 (volume : Measure (Fin 2 → ℝ))),
      jumpEnergy_zero]
    exact ENNReal.zero_ne_top
  smul_mem' c {u} hu := by
    show jumpEnergy α ⇑(c • u) ≠ ⊤
    rw [jumpEnergy_congr_ae α (Lp.coeFn_smul c u), jumpEnergy_smul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu

/-- Membership in the subspace of finite energy. -/
theorem mem_energySubmodule {α : ℝ} {u : L²} : u ∈ energySubmodule α ↔ jumpEnergy α u ≠ ⊤ :=
  Iff.rfl

/-- The energy space `H_α`: the functions of finite jump energy in `L²(ℝ²)`. It is a type
synonym of `energySubmodule α`, so that it carries the energy norm and not the `L²` norm. -/
def EnergySpace (α : ℝ) : Type := energySubmodule α

namespace EnergySpace

variable {α : ℝ}

/-- The additive group structure of the energy space is that of the submodule. -/
instance : AddCommGroup (EnergySpace α) := inferInstanceAs (AddCommGroup (energySubmodule α))

/-- The module structure of the energy space is that of the submodule. -/
instance : Module ℝ (EnergySpace α) := inferInstanceAs (Module ℝ (energySubmodule α))

/-- The underlying `L²` function of an element of the energy space. -/
@[coe] def toLp (u : EnergySpace α) : L² := (u : energySubmodule α).1

/-- Elements of the energy space coerce to their `L²` functions. -/
instance : CoeOut (EnergySpace α) L² := ⟨toLp⟩

/-- Elements of the energy space coerce to functions on the plane, through `L²`. -/
instance : CoeFun (EnergySpace α) fun _ => (Fin 2 → ℝ) → ℝ := ⟨fun u => ⇑(toLp u)⟩

/-- An element of the energy space from an `L²` function of finite energy. -/
def mk (u : L²) (hu : jumpEnergy α u ≠ ⊤) : EnergySpace α := (⟨u, hu⟩ : energySubmodule α)

/-- The underlying `L²` function of `mk u hu` is `u`. -/
@[simp]
theorem toLp_mk (u : L²) (hu : jumpEnergy α u ≠ ⊤) : (mk u hu : L²) = u := rfl

/-- Elements of the energy space have finite energy. -/
theorem jumpEnergy_ne_top (u : EnergySpace α) : jumpEnergy α u ≠ ⊤ := (u : energySubmodule α).2

/-- Elements of the energy space have finite energy. -/
theorem jumpEnergy_lt_top (u : EnergySpace α) : jumpEnergy α u < ⊤ :=
  lt_top_iff_ne_top.2 u.jumpEnergy_ne_top

/-- The inclusion into `L²` is additive. -/
@[simp]
theorem toLp_add (u v : EnergySpace α) : ((u + v : EnergySpace α) : L²) = (u : L²) + v := rfl

/-- The inclusion into `L²` is homogeneous. -/
@[simp]
theorem toLp_smul (c : ℝ) (u : EnergySpace α) :
    ((c • u : EnergySpace α) : L²) = c • (u : L²) := rfl

/-- The inclusion into `L²` preserves zero. -/
@[simp]
theorem toLp_zero : ((0 : EnergySpace α) : L²) = 0 := rfl

/-- The inclusion into `L²` preserves negation. -/
@[simp]
theorem toLp_neg (u : EnergySpace α) : ((-u : EnergySpace α) : L²) = -(u : L²) := rfl

/-- The inclusion into `L²` preserves subtraction. -/
@[simp]
theorem toLp_sub (u v : EnergySpace α) : ((u - v : EnergySpace α) : L²) = (u : L²) - v := rfl

/-- The inclusion into `L²` is injective. -/
theorem toLp_injective : Function.Injective (toLp : EnergySpace α → L²) :=
  fun _ _ h => Subtype.ext h

/-- Two elements of the energy space with the same `L²` function are equal. -/
@[ext]
theorem ext {u v : EnergySpace α} (h : (u : L²) = v) : u = v := toLp_injective h

/-- Elements of `L²` are a.e.-measurable. -/
private theorem aemeasurable_coeFn (u : L²) : AEMeasurable u volume :=
  (Lp.aestronglyMeasurable u).aemeasurable

/-- The inclusion into `L²`, as a linear map. -/
def toLpₗ (α : ℝ) : EnergySpace α →ₗ[ℝ] L² where
  toFun := toLp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The linear inclusion into `L²` is the inclusion. -/
@[simp]
theorem toLpₗ_apply (u : EnergySpace α) : toLpₗ α u = u := rfl

/-! ### The inner product -/

/-- The energy inner product `⟪u, v⟫ = ⟪u, v⟫_{L²} + E(u, v)`. -/
instance : Inner ℝ (EnergySpace α) := ⟨fun u v => ⟪(u : L²), v⟫ + jumpForm α u v⟩

/-- The energy inner product is the `L²` inner product plus the jump form. -/
theorem inner_def (u v : EnergySpace α) : ⟪u, v⟫ = ⟪(u : L²), v⟫ + jumpForm α u v := rfl

/-- The energy norm `‖u‖² = ‖u‖²_{L²} + E(u, u)`. -/
instance : NormedAddCommGroup (EnergySpace α) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (EnergySpace α) _ _ _
    { toInner := inferInstance
      conj_inner_symm := fun u v => by
        rw [RCLike.conj_to_real, inner_def, inner_def, real_inner_comm, jumpForm_comm]
      re_inner_nonneg := fun u => by
        rw [RCLike.re_to_real, inner_def]
        exact add_nonneg real_inner_self_nonneg (jumpForm_self_nonneg α u)
      add_left := fun u v w => by
        rw [inner_def, inner_def, inner_def, toLp_add, inner_add_left,
          jumpForm_congr_ae α (Lp.coeFn_add (u : L²) v) EventuallyEq.rfl,
          jumpForm_add_left_of_aemeasurable α (aemeasurable_coeFn _) (aemeasurable_coeFn _)
            (aemeasurable_coeFn _) u.jumpEnergy_ne_top v.jumpEnergy_ne_top w.jumpEnergy_ne_top]
        ring
      smul_left := fun u v c => by
        rw [RCLike.conj_to_real, inner_def, inner_def, toLp_smul, real_inner_smul_left,
          jumpForm_congr_ae α (Lp.coeFn_smul c (u : L²)) EventuallyEq.rfl, jumpForm_smul_left]
        ring
      definite := fun u hu => by
        rw [inner_def] at hu
        have h := jumpForm_self_nonneg α u
        have h' := real_inner_self_nonneg (x := (u : L²))
        have h0 : ⟪(u : L²), u⟫ = 0 := by linarith
        exact ext (inner_self_eq_zero.1 h0) }

/-- The energy space is a real inner product space. -/
instance : InnerProductSpace ℝ (EnergySpace α) := InnerProductSpace.ofCore _

/-- The energy norm: `‖u‖² = ‖u‖²_{L²} + E(u, u)`. -/
theorem norm_sq_eq (u : EnergySpace α) : ‖u‖ ^ 2 = ‖(u : L²)‖ ^ 2 + jumpForm α u u := by
  rw [← real_inner_self_eq_norm_sq u, inner_def, real_inner_self_eq_norm_sq]

/-- The jump form is the difference of the two inner products. -/
theorem jumpForm_eq (u v : EnergySpace α) : jumpForm α u v = ⟪u, v⟫ - ⟪(u : L²), v⟫ := by
  rw [inner_def]
  ring

/-- The energy of an element of the energy space is the jump form on the diagonal. -/
theorem jumpEnergy_eq (u : EnergySpace α) : jumpEnergy α u = ENNReal.ofReal (jumpForm α u u) :=
  (jumpForm_self_of_aemeasurable α (aemeasurable_coeFn _) u.jumpEnergy_ne_top).symm

/-- The energy of `u - v`, in `L²` coordinates. -/
theorem jumpEnergy_toLp_sub (u v : EnergySpace α) :
    jumpEnergy α (⇑u - ⇑v) = ENNReal.ofReal (jumpForm α ⇑(u - v) ⇑(u - v)) := by
  rw [← jumpEnergy_congr_ae α (Lp.coeFn_sub (u : L²) v), ← toLp_sub, jumpEnergy_eq]

/-- The jump form on the diagonal is at most the squared energy norm. -/
theorem jumpForm_self_le_norm_sq (u : EnergySpace α) : jumpForm α u u ≤ ‖u‖ ^ 2 := by
  rw [norm_sq_eq]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- The inclusion into `L²` has norm at most one. -/
theorem norm_toLp_le (u : EnergySpace α) : ‖(u : L²)‖ ≤ ‖u‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_sq_eq]
  exact le_add_of_nonneg_right (jumpForm_self_nonneg α u)

/-- The inclusion into `L²`, as a continuous linear map. -/
def toLpCLM (α : ℝ) : EnergySpace α →L[ℝ] L² :=
  (toLpₗ α).mkContinuous 1 fun u => by
    rw [one_mul, toLpₗ_apply]
    exact norm_toLp_le u

/-- The continuous linear inclusion into `L²` is the inclusion. -/
@[simp]
theorem toLpCLM_apply (u : EnergySpace α) : toLpCLM α u = u := rfl

/-! ### The positive cone and truncation -/

/-- The cone of nonnegative functions in the energy space. -/
def nonnegCone (α : ℝ) : Set (EnergySpace α) := {u | 0 ≤ (u : L²)}

/-- Membership in the positive cone. -/
theorem mem_nonnegCone {u : EnergySpace α} : u ∈ nonnegCone α ↔ 0 ≤ (u : L²) := Iff.rfl

/-- Membership in the positive cone is almost everywhere nonnegativity. -/
theorem mem_nonnegCone_iff_ae {u : EnergySpace α} : u ∈ nonnegCone α ↔ 0 ≤ᵐ[volume] ⇑u :=
  (Lp.coeFn_nonneg _).symm

/-- The positive cone is convex. -/
theorem convex_nonnegCone : Convex ℝ (nonnegCone α) := by
  intro u hu v hv a b ha hb _
  rw [mem_nonnegCone_iff_ae] at hu hv ⊢
  simp only [toLp_add, toLp_smul]
  filter_upwards [hu, hv, Lp.coeFn_add (a • (u : L²)) (b • (v : L²)),
    Lp.coeFn_smul a (u : L²), Lp.coeFn_smul b (v : L²)] with x hu hv h₁ h₂ h₃
  rw [Pi.zero_apply] at hu hv ⊢
  rw [h₁, Pi.add_apply, h₂, h₃, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha hu) (mul_nonneg hb hv)

/-- The positive cone is closed. -/
theorem isClosed_nonnegCone : IsClosed (nonnegCone α) := by
  have : nonnegCone α = toLpCLM α ⁻¹' Set.Ici 0 := rfl
  rw [this]
  exact isClosed_Ici.preimage (toLpCLM α).continuous

/-- The positive part `u₊ = max u 0`, of finite energy by `jumpEnergy_posPart_le`. -/
def posPart (u : EnergySpace α) : EnergySpace α :=
  mk (Lp.posPart (u : L²)) <| by
    refine ne_top_of_le_ne_top u.jumpEnergy_ne_top ?_
    rw [jumpEnergy_congr_ae α (Lp.coeFn_posPart (u : L²))]
    exact jumpEnergy_posPart_le α u

/-- The `L²` function of the positive part. -/
@[simp]
theorem toLp_posPart (u : EnergySpace α) : (u.posPart : L²) = Lp.posPart (u : L²) := rfl

/-- The positive part is almost everywhere `max u 0`. -/
theorem coeFn_posPart (u : EnergySpace α) :
    ⇑u.posPart =ᵐ[volume] CenteredMaximal.posPart u :=
  Lp.coeFn_posPart (u : L²)

/-- The positive part lies in the positive cone. -/
theorem posPart_mem_nonnegCone (u : EnergySpace α) : u.posPart ∈ nonnegCone α := by
  rw [mem_nonnegCone_iff_ae]
  filter_upwards [coeFn_posPart u] with x hx
  rw [Pi.zero_apply, hx]
  exact le_max_right _ _

/-- The Markov inequality `E(u₊, u₊) ≤ E(u, u₊)` in the energy space. -/
theorem jumpForm_posPart_self_le (u : EnergySpace α) :
    jumpForm α u.posPart u.posPart ≤ jumpForm α u u.posPart := by
  rw [jumpForm_congr_ae α (coeFn_posPart u) (coeFn_posPart u),
    jumpForm_congr_ae α EventuallyEq.rfl (coeFn_posPart u)]
  exact jumpForm_posPart_self_le_of_aemeasurable α (aemeasurable_coeFn _) u.jumpEnergy_ne_top

/-- The pointwise minimum `min u v`, of finite energy by `jumpEnergy_inf_le`. -/
def inf (u v : EnergySpace α) : EnergySpace α :=
  mk ((u : L²) ⊓ v) <| by
    refine ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨u.jumpEnergy_ne_top, v.jumpEnergy_ne_top⟩) ?_
    rw [jumpEnergy_congr_ae α (Lp.coeFn_inf (u : L²) v)]
    exact jumpEnergy_inf_le_of_aemeasurable α (aemeasurable_coeFn _) v

/-- The `L²` function of the minimum. -/
@[simp]
theorem toLp_inf (u v : EnergySpace α) : (u.inf v : L²) = (u : L²) ⊓ v := rfl

/-- The minimum is almost everywhere the pointwise minimum. -/
theorem coeFn_inf (u v : EnergySpace α) : ⇑(u.inf v) =ᵐ[volume] fun x => min (u x) (v x) :=
  Lp.coeFn_inf (u : L²) v

/-! ### Completeness -/

/-- Fatou's lemma for the energy of `w - v`, where `v` is the almost everywhere limit of a
sequence in `L²`. -/
private theorem jumpEnergy_sub_le_liminf {u : ℕ → L²} {v : L²}
    (h : ∀ᵐ x ∂volume, Tendsto (fun i => u i x) atTop (𝓝 (v x))) (w : L²) :
    jumpEnergy α (⇑w - ⇑v) ≤ liminf (fun i => jumpEnergy α (⇑w - ⇑(u i))) atTop := by
  have hu := fun i => aemeasurable_coeFn (u i)
  have hv := aemeasurable_coeFn v
  have hw := aemeasurable_coeFn w
  have hconv : ∀ᵐ x ∂volume, Tendsto (fun i => (hw.mk w - (hu i).mk (u i)) x) atTop
      (𝓝 ((hw.mk w - hv.mk v) x)) := by
    filter_upwards [h, (ae_all_iff (p := fun x i => u i x = (hu i).mk (u i) x)).2
      fun i => (hu i).ae_eq_mk, hv.ae_eq_mk, hw.ae_eq_mk] with x hx hux hvx hwx
    simp only [Pi.sub_apply, ← hux, ← hvx, ← hwx]
    exact hx.const_sub _
  rw [jumpEnergy_congr_ae α (hw.ae_eq_mk.sub hv.ae_eq_mk),
    show (fun i => jumpEnergy α (⇑w - ⇑(u i))) = fun i => jumpEnergy α (hw.mk w - (hu i).mk (u i))
      from funext fun i => jumpEnergy_congr_ae α (hw.ae_eq_mk.sub (hu i).ae_eq_mk)]
  exact jumpEnergy_le_liminf α (fun i => hw.measurable_mk.sub (hu i).measurable_mk)
    (hw.measurable_mk.sub hv.measurable_mk) hconv

/-- The `L²` projections of a Cauchy sequence in the energy space form a Cauchy sequence. -/
theorem cauchySeq_toLp {u : ℕ → EnergySpace α} (hu : CauchySeq u) :
    CauchySeq fun n => (u n : L²) :=
  (toLpCLM α).lipschitz.uniformContinuous.comp_cauchySeq hu

/-- Along a Cauchy sequence in the energy space, the jump forms of the differences are eventually
small. -/
private theorem exists_jumpForm_sub_lt {u : ℕ → EnergySpace α} (hu : CauchySeq u) {ε : ℝ}
    (hε : 0 < ε) : ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, jumpForm α ⇑(u m - u n) ⇑(u m - u n) < ε := by
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu (√ε) (Real.sqrt_pos.2 hε)
  refine ⟨N, fun m hm n hn => (jumpForm_self_le_norm_sq _).trans_lt ?_⟩
  rw [← dist_eq_norm]
  exact (Real.lt_sqrt dist_nonneg).1 (hN m hm n hn)

/-- Fatou's lemma along an almost everywhere convergent subsequence: the energies of `u n - v`
are eventually small. -/
private theorem exists_jumpEnergy_sub_le {u : ℕ → EnergySpace α} (hu : CauchySeq u) {v : L²}
    {ns : ℕ → ℕ} (hns : StrictMono ns)
    (hae : ∀ᵐ x ∂volume, Tendsto (fun i => (u (ns i) : L²) x) atTop (𝓝 (v x))) {ε : ℝ}
    (hε : 0 < ε) : ∃ N : ℕ, ∀ n ≥ N, jumpEnergy α (⇑(u n) - ⇑v) ≤ ENNReal.ofReal ε := by
  obtain ⟨N, hN⟩ := exists_jumpForm_sub_lt hu hε
  refine ⟨N, fun n hn => (jumpEnergy_sub_le_liminf hae (u n : L²)).trans
    (liminf_le_of_frequently_le' ((eventually_atTop.2 ⟨N, fun i hi => ?_⟩).frequently))⟩
  rw [jumpEnergy_toLp_sub]
  exact ENNReal.ofReal_le_ofReal (hN n hn (ns i) (hi.trans hns.le_apply)).le

/-- The energy space is complete: a Cauchy sequence converges in `L²`, a subsequence converges
almost everywhere, and Fatou's lemma shows that the limit has finite energy and that the energies
of the differences tend to zero. -/
instance : CompleteSpace (EnergySpace α) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete (cauchySeq_toLp hu)
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  -- the limit has finite energy
  obtain ⟨N₀, hN₀⟩ := exists_jumpEnergy_sub_le hu hns hae one_pos
  have hvE : jumpEnergy α v ≠ ⊤ := by
    have h₁ : jumpEnergy α (⇑v - ⇑(u N₀)) ≠ ⊤ := by
      rw [← neg_sub, jumpEnergy_neg]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hN₀ N₀ le_rfl)
    have h₂ := jumpEnergy_add_le_of_aemeasurable α (aemeasurable_coeFn (u N₀ : L²))
      (⇑v - ⇑(u N₀))
    rw [add_sub_cancel] at h₂
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.add_ne_top.2 ⟨(u N₀).jumpEnergy_ne_top, h₁⟩)) h₂
  refine ⟨mk v hvE, ?_⟩
  -- convergence in the energy norm: both terms of `‖u n - v‖²` tend to zero
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hL : Tendsto (fun n => ‖(u n : L²) - v‖ ^ 2) atTop (𝓝 0) := by
    have h := (tendsto_iff_norm_sub_tendsto_zero.1 hv).pow 2
    rwa [zero_pow two_ne_zero] at h
  have hJ : Tendsto (fun n => jumpForm α ⇑(u n - mk v hvE) ⇑(u n - mk v hvE)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_jumpEnergy_sub_le hu hns hae (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (jumpForm_self_nonneg α _)]
    have h := hN n hn
    rw [← toLp_mk v hvE, jumpEnergy_toLp_sub, ENNReal.ofReal_le_ofReal_iff (half_pos hε).le] at h
    linarith
  have hsq : Tendsto (fun n => ‖u n - mk v hvE‖ ^ 2) atTop (𝓝 0) := by
    have h := hL.add hJ
    rw [add_zero] at h
    refine h.congr fun n => ?_
    rw [norm_sq_eq, toLp_sub, toLp_mk]
  refine ((Real.continuous_sqrt.tendsto' 0 0 Real.sqrt_zero).comp hsq).congr fun n => ?_
  simp only [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]

end EnergySpace

end CenteredMaximal
