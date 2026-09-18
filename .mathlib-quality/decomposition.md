# Decomposition

## Skeleton location

Every declaration below exists in the repository with `:= by sorry` (commit `5a6444f`), and
`lake build CenteredMaximal Challenge Solution` succeeds with only `sorry` warnings.

Source keys are those of `plan.md`. `[P §n]` quotes `docs/PROOF.md`, the informal proof written for
this development; for the lower bound it is the primary source, because the result is new. Quotes
from copyrighted third-party texts are kept short.

Prior-B2 log: `.mathlib-quality/b2_log.jsonl` is empty (new project); no leaf matches a prior B2.

---

## Result 1: `weakTypeConstant_le_two_pow : weakTypeConstant d ≤ 2 ^ d`

### Plain-English proof
[P §2]: choose for each `x ∈ E = {M f > α}` a cube with `α |Q_x| < ∫_{Q_x} |f|`; radii are bounded;
Vitali with enlargement `τ > 1` gives a disjoint countable subfamily whose `(1 + τ)`-enlargements
contain all centres; sum; let `τ → 1`. Dimension `0` separately.

Source structure: [T] Lemma 39 (Vitali-type covering lemma, finite families, greedy) and Exercise 42.
Mathlib's `Vitali.exists_disjoint_subfamily_covering_enlargement` replaces Lemma 39 for arbitrary
families at the cost of `τ > 1`, which is exactly the "epsilon of room" of the Exercise 42 hint.

- **U0** (internal): `isWeakTypeBound_two_pow` — `UpperBound.lean`. Composition: `d = 0` by U1 and
  `IsWeakTypeBound.mono` (`1 ≤ 2⁰`); `d > 0` by U3 for every `τ ∈ (1, 2)` and `ge_of_tendsto` along
  `𝓝[>] 1`. *Attacks:* composition — U3 holds for each `τ > 1` and the right side is continuous in
  `τ` when `‖f‖₁ < ∞` (integrable) ✓; edge `α = ⊤` gives an empty level set ✓; `α = 0` trivial ✓.
- **U1** (leaf, mathlib): `isWeakTypeBound_one_of_dim_zero`. Source quote [P §2.1]: "`ℝ⁰` is a point
  of measure `1`, every cube is the whole space, and `M f = ‖f‖₁`." Discharge:
  `Real.volume_pi_closedBall` (card 0 gives `ofReal 1`), `Subsingleton` of `Fin 0 → ℝ`,
  `iSup₂_le`. *Attacks:* [1] counterexample: volume of `Fin 0 → ℝ` is `Measure.pi` over an empty
  index, a Dirac mass of total mass 1 ✓. [2] edge: `α = ⊤` ⇒ empty set ✓. [3] source drift: the
  statement asks only for bound `1` ✓.
- **U2** (leaf, mathlib): `radius_le_of_mul_volume_lt`. Quote [P §2.2]: "If `2r ≥ 1` then
  `(2r)ᵈ ≥ 2r`, so in all cases `r ≤ max(1, K/α)`." Discharge: `volume_closedBall_eq`,
  `le_self_pow₀`, `ENNReal.ofReal_le_ofReal`, `ENNReal.lt_div_iff_mul_lt`. *Attacks:* [1] edge
  `d = 0` would be false (volume `1`), excluded by `hd` ✓; [2] `K/α = ⊤` excluded by `hK`, `hα` ✓;
  [3] statement uses `r ≤ max 1 _`, weaker than `2r ≤ …` (safe) ✓.
- **U3** (internal): `mul_volume_le_of_one_lt`. Quote [P §2.3]: "A common point `z` gives
  `|a - b| ≤ r_a + r_b ≤ (1 + τ) r_b`: the *centre* `a` lies in `Q(b, (1 + τ) r_b)`." Discharge
  chain: `exists_lt_average_of_lt_maximalFunction` → `choose` radii → U2 bound →
  `Vitali.exists_disjoint_subfamily_covering_enlargement` (verified type: `(B : ι → Set α)
  (t : Set ι) (δ : ι → ℝ) (τ : ℝ), 1 < τ → (∀ a ∈ t, 0 ≤ δ a) → ∀ R, (∀ a ∈ t, δ a ≤ R) →
  (∀ a ∈ t, (B a).Nonempty) → ∃ u ⊆ t, u.PairwiseDisjoint B ∧ ∀ a ∈ t, ∃ b ∈ u,
  (B a ∩ B b).Nonempty ∧ δ a ≤ τ * δ b`) → `PairwiseDisjoint.countable_of_nonempty_interior` →
  `measure_biUnion_le` → `volume_closedBall_eq` → `lintegral_biUnion` →
  `setLIntegral_le_lintegral`. *Attacks:* [1] composition: the level set need not be measurable;
  only `measure_mono` and `measure_biUnion_le` (outer-measure lemmas) are used on it ✓. [2] edge:
  `E = ∅` ⇒ `u = ∅`, sums zero ✓. [3] discharge: the Vitali lemma allows an arbitrary index set
  `t`, here `E ⊆ Fin d → ℝ` itself ✓.

## Result 2: `ofReal_phi_le_weakTypeConstant_two : ENNReal.ofReal phi ≤ weakTypeConstant 2`

### Plain-English proof
[P §§3–6]. Witnesses on a quarter cell (six types), symmetry to the cell and its translates,
smearing into `L¹`, disjoint copies in the level set, weak type inequality with `α = 1 - 2ε`,
`ε = 1/(2N + 3)`, and `N → ∞`.

Source structure: the lower-bound principle and finite-mass passage are [B] pages 2 and 4 (which
follow [A] Lemma 1.1); quote [B p. 4]: "For a genuine L¹ test, replace every atom p by
ε⁻²1_{p+[−ε/2,ε/2]²} and sum". The weighted configuration, the witnesses and the coverage are new
([P §4], discovered in [R]).

### Constants (`Lattice/Constants.lean`) — leaves, all discharged by `norm_num`, `nlinarith`,
`Real.sq_sqrt`, `Real.sqrt_le_sqrt`, `Real.lt_sqrt`, `Real.sqrt_lt'`

| leaf | quote [P §3] | attack notes |
|---|---|---|
| `sqrt22_sq`, `root_quadratic` | "the positive root of `3u² - 4u - 6 = 0`" | exact: `9u² = 26 + 4√22`; checked numerically in [R] |
| `two_mul_hgap_sub_one`, `one_add_heavy` | "`w = u² - 1`", "`h = (1 + u)/2`" | definitional (`ring`) |
| `two_mul_hgap_add_one_sq` | "`(2h + 1)² = 2(1 + 2w)` is equivalent to `3u² - 4u - 6 = 0`" | `(u+2)² - (4u² - 2) = -(3u² - 4u - 6)` ✓ |
| `sideLH2_sq`, `sideH1_sq`, `sideLHL2_sq` | "`√2·u = √(2(1 + w))`" | need `0 ≤ heavy`, `0 ≤ 2(2 + w)` ✓ |
| `root_gt`, `root_lt`, bounds | "each follows from `4.69 < √22 < 4.691` and `1.414 < √2 < 1.4143`" | margins recomputed below |
| `vgap_le_sideLH2` | "`V ≤ √2 u`" | `2.6152 ≤ 3.153` ✓ |
| `two_mul_vgap_le_root_add_sideLH2` | "`2V ≤ u + √2 u`" | `5.2304 ≤ 5.383` ✓ |
| `two_mul_hgap_le_sideLHL2`, `vgap_le_sideLHL2` | "`2h ≤ √(2(2+w))`, `V ≤ √(2(2+w))`" | `3.2304 ≤ 3.45` ✓ |
| `vgap_sub_le_sideH1` | "`2V - √(2(2+w)) ≤ √w`" | `1.7804 ≤ 1.99` ✓ |
| `four_mul_hgap_sub_le_sideLH2` | "`4h - √(2(2+w)) ≤ √2 u`" | `3.0108 ≤ 3.153` ✓ |
| `slotW_pos`, `slotH_pos` | "`a > 0`, `b > 0`" | `a ≥ 0.386`, `b ≥ 0.0408` ✓ (tightest margin) |
| `one_le_sideH1`, `one_le_root` | "`1 ≤ √w`" | `w ≥ 3.97` ✓ |
| `phi_eq` | "`Φ = (2hV - 4ab)/(1 + w)`" | needs `√(2(2+w)) = √(70+8√22)/3`, `√w = √(17+4√22)/3`, `√2·√22 = 2√11`; all exact |

*Attacks on the numeric table:* [1] each inequality re-evaluated at 60 digits in [R] ✓; [2] the
enclosures used are strictly inside the true values with the stated margins ✓; [3] source drift:
the Lean statements are the ones used verbatim in [P §4.2] ✓.

### Witnesses (`Lattice/Witness.lean`)

- **W-sym** (leaves): `colWeight_neg`, `colWeight_add_two_mul`, `IsWitness.neg_fst`, `.neg_snd`,
  `.translate`, three `…_subset_nearBox`. Quote [P §4.3]: "The masses are invariant under `c ↦ -c`
  and `c ↦ c + 2k`." Discharge: `Int.even_neg`, `Int.even_add`, `Finset.sum_map`, `abs_neg`,
  `ring_nf`. *Attacks:* [1] parity: `Even (c + 2k) ↔ Even c` ✓; [2] the sum over a mapped finset
  needs an embedding — `Equiv.toEmbedding` ✓; [3] edge `A = ∅` fails `1 ≤ L ≤ L² ≤ 0`, but
  `IsWitness` with empty `A` is simply never produced ✓.
- **W1–W6** (leaves): `isWitness_light`, `_hlh2`, `_lh1`, `_lh2`, `_h1`, `_lhl2`. Quote [P §4.1]:
  "In each case the mass equals `L²` exactly, and the distance conditions reduce to the stated
  ranges together with the inequalities of Section 3." Discharge: `Finset.sum_insert`,
  `colWeight` evaluation, `abs_le`, `linarith` with the Constants leaves. *Attacks:* [1] each
  distance condition re-derived by hand in the table of [P §4.1] (including the row `V` for
  `y ≤ V/2`) ✓; [2] edge: `x = 1/2` belongs to both light and lh1 ranges; both valid ✓;
  [3] hypothesis test: hlh2 needs `0 ≤ x` (column `h`) — kept ✓.
- **W-cov** (internal): `exists_isWitness_of_nonneg`, `exists_isWitness_of_abs`. Quote [P §4.2]:
  "Every `(x, y)` with `0 ≤ x ≤ h`, `0 ≤ y ≤ V/2` outside the open slot … has one of the six
  witnesses". Composition: the case split of [P §4.2]; then `neg_fst`/`neg_snd` by the signs of
  `x`, `y`. *Attacks:* [1] the boundary `x = u/2` is handled by the second case (closed) ✓;
  [2] points on the slot boundary are covered (slot is open) ✓; [3] numerical cross-check: the
  exploratory evaluator found the level set to be exactly the cell minus these slots ✓.

### Smearing (`Lattice/Smear.lean`)

- **S1** (leaves): `colWeight_pos`, `smeared_nonneg`, `integrable_smeared`. Discharge:
  `integrable_finset_sum`, `Integrable.const_mul`, `integrableOn_const`,
  `measure_closedBall_lt_top`. *Attacks:* `ε > 0` needed for finite `ε⁻²` (hypothesis kept) ✓.
- **S2** (leaf): `sum_colWeight_Icc`. Quote [P §5]: "`‖smeared N ε‖₁` is the total kept mass
  `(2N + 3)((2N + 3) + (2N + 2)w)`". Discharge: induction on `N` with `Finset.sum_Ioc_consecutive`
  style splitting, or `Int.Icc_eq_finset_map` and `Finset.sum_range_succ`. *Attacks:* count check
  `N = 0`: columns `-2..2`, weights `1, w, 1, w, 1` = `3 + 2w` ✓.
- **S3** (leaf): `lintegral_smeared`. Discharge: `Real.enorm_eq_ofReal`,
  `ENNReal.ofReal_sum_of_nonneg`, `lintegral_finsetSum`, `lintegral_indicator_const`,
  `volume_closedBall_eq`. *Attacks:* [1] `(2·(ε/2))² = ε²` ✓; [2] overlapping squares are fine
  (linearity) ✓; [3] `ε` must be positive ✓.
- **S4** (leaves): `ofReal_sq_le_setLIntegral_smeared`, `lt_maximalFunction_smeared`. Quote
  [P §5]: "the square of side `L + ε` centred at `z` contains the whole smeared square of every atom
  of `A`, so its integral is at least `L²`". Discharge: `closedBall_subset_closedBall'`,
  `dist_pi_le_iff`, `Finset.sum_le_sum_of_subset_of_nonneg`, `Measure.restrict_apply`,
  `le_maximalFunction`. *Attacks:* [1] `L ≥ 1` is needed for the uniform bound — it is part of
  `IsWitness` ✓; [2] `(1 - 2ε)(1 + ε)² < 1` for `ε > 0` ✓; [3] when `1 - 2ε < 0` the claim is
  `0 < M f z`, still true ✓.

### Assembly (`Lattice/LowerBound.lean`)

- **L1** (leaves): `measurableSet_goodSet`, `volume_goodSet_ge`, `volume_goodCopy`,
  `pairwiseDisjoint_goodCopy`, `nearBox_subset_atomBox`. Quote [P §6]: "`goodSet = cell \ slots`
  has area at least `|cell| - 4ab`", "Its translates … are pairwise disjoint (the cells are
  half-open)". Discharge: `le_measure_diff`, `measure_union_le`, `Real.volume_pi_Ico`,
  `Real.volume_pi_Ioo`, `measure_preimage_add`, integer arithmetic for disjointness.
  *Attacks:* [1] slots are open boxes covered by four boxes of volume `ab` ✓; [2] disjointness uses
  `|2(k - k') h| < 2h ⇒ k = k'` ✓; [3] `volume` on `Fin 2 → ℝ` is add-left-invariant ✓.
- **L2** (internal): `exists_isWitness_of_mem_goodCopy` = W-cov + `translate` +
  `map_addRight_subset_nearBox`.
- **L3** (internal): `ofReal_le_volume_levelSet` = L1 + L2 + S4 + `measure_biUnion_finset` +
  `Int.card_Icc`.
- **L4** (internal): `ofReal_mul_phi_le` = weak type inequality at `α = ofReal (1 - 2ε)` with
  `ε = 1/(2N + 3)`, S3 + S2 bound + L3 + `phi_eq`; algebra `q (2N+1)² / (2N+3)² = q³`.
  *Attack:* `1 - 2ε = (2N + 1)/(2N + 3) > 0` ✓.
- **L5** (internal): `ofReal_phi_le` — `ge_of_tendsto'` with `q_N ≥ 1 - 1/(N + 1) → 1`.

## Result 3: `weakTypeConstant_two_gt` — assembly of `lt_phi` and Result 2.

## Result 4: `lt_phi`, `phi_lt` — proved in `Numerics.lean`.

## Feasibility

Every leaf is discharged by named Mathlib lemmas (verified to exist with the expected types in
`scratch` checks, 18 Sep 2026) or by linear/nonlinear arithmetic on explicit enclosures. There are no
API gaps. Estimated size: Constants ~200 lines, Witness ~250, Smear ~200, LowerBound ~250,
UpperBound ~200, Basic ~60 — comparable to [P], whose sections 2–6 are about 150 lines of prose.
