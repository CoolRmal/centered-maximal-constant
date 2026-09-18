# Development plan: the weak type constant of the centred maximal operator over cubes

## Goal

`Challenge.lean` (Mathlib imports only) defines

* `maximalFunction f x = ⨆ r > 0, (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖f y‖ₑ`
  on `Fin d → ℝ` (sup norm, so balls are axis-parallel cubes);
* `IsWeakTypeBound d C := ∀ f, Integrable f → ∀ α, α * volume {x | α < maximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ`;
* `weakTypeConstant d := sInf {C | IsWeakTypeBound d C}`;
* `phi`, the explicit radical expression `1.68550999…`;

and states, as the compared declarations,

```lean
theorem weakTypeConstant_le_two_pow (d : ℕ) : weakTypeConstant d ≤ 2 ^ d
theorem ofReal_phi_le_weakTypeConstant_two : ENNReal.ofReal phi ≤ weakTypeConstant 2
theorem weakTypeConstant_two_gt : ENNReal.ofReal (1685 / 1000) < weakTypeConstant 2
theorem lt_phi : (1685 / 1000 : ℝ) < phi          -- proved inside Challenge.lean
theorem phi_lt : phi < 1686 / 1000                -- proved inside Challenge.lean
```

Gates: leanprover/comparator with axioms `propext`, `Quot.sound`, `Classical.choice`; no
`native_decide`, `Lean.ofReduceBool`, `admit` or `axiom`; every file under 1 500 lines and lines
under 100 characters; Palomar metadata (`formalization.yaml`, licence, README, literature account).

## References

| key | reference | used for |
|---|---|---|
| [P] | `docs/PROOF.md` (this repository) | the whole argument; the lower bound is original |
| [T] | T. Tao, *245A Notes 5: Differentiation theorems*, Exercise 42 and Lemma 39 | the `2ᵈ` upper bound |
| [V] | Mathlib `Vitali.exists_disjoint_subfamily_covering_enlargement` | the covering step |
| [A] | J. M. Aldaz, Czechoslovak Math. J. 50 (2000) 103–112, Lemma 1.1 and Prop. 1.4 | smearing device; previous record `1.6212` |
| [B] | the research brief *Improving the planar centered maximal constant* (18 Sep 2026), pages 2–4 | lower-bound principle, finite-mass passage, seed `1.66856` |
| [R] | `exploration/REPORT.md` | discovery of the configuration, exact certificate, literature search |

## Mathlib inventory

| concept | Mathlib | action |
|---|---|---|
| centred maximal function over cubes, weak type constant | none (Carleson project and Tau Ceti have non-sharp versions, not in Mathlib) | define in `Statement.lean` / `Challenge.lean` |
| cubes | `Metric.closedBall` in `Fin d → ℝ` (sup norm) | use directly |
| cube volume | `Real.volume_pi_closedBall` | use |
| Vitali covering with enlargement `τ > 1` | `Vitali.exists_disjoint_subfamily_covering_enlargement` | use |
| countability of disjoint families with interior | `Set.PairwiseDisjoint.countable_of_nonempty_interior` | use |
| measure / integral over countable unions | `measure_biUnion_le`, `lintegral_biUnion`, `measure_biUnion_finset` | use |
| boxes | `Real.volume_pi_Ico`, `Real.volume_pi_Ioo` | use |
| translation invariance | `measure_preimage_add` | use |
| square-root enclosures | `Real.lt_sqrt`, `Real.sqrt_lt'` | use |

## File structure

```
Challenge.lean                         statement (Mathlib imports only) + proof of 1.685 < Φ < 1.686
Solution.lean                          the five compared theorems, from the development
CenteredMaximal/Statement.lean         the challenge definitions, verbatim
CenteredMaximal/Basic.lean             API: averages ≤ maximal function, cube volume, sInf lemmas
CenteredMaximal/Numerics.lean          1.685 < Φ < 1.686 (same proof as the challenge)
CenteredMaximal/UpperBound.lean        c_d ≤ 2ᵈ
CenteredMaximal/Lattice/Constants.lean u, w, h, V, witness sides, slot, identities, phi_eq
CenteredMaximal/Lattice/Witness.lean   colWeight, IsWitness, six witnesses, coverage, symmetries
CenteredMaximal/Lattice/Smear.lean     the smeared lattice: integrability, L¹ norm, maximal bound
CenteredMaximal/Lattice/LowerBound.lean cell, slots, copies, level-set volume, Φ ≤ C
```

## Dependency graph

```
Statement ─ Basic ─┬─ UpperBound ──────────────────────────────┐
                   │                                           ├─ Solution
Statement ─ Numerics ──────────────────────────────────────────┤
Statement ─ Constants ─ Witness ─┬─ Smear ─ LowerBound ────────┘
                         Basic ──┘
```

## Generality decisions

* The upper bound is stated for every `d : ℕ`, including `d = 0` (a point), which needs a separate
  two-line case because Vitali needs bounded radii.
* The lower bound is specific to `d = 2` and to one explicit configuration: this is the research
  content, not a general theorem.
* `α` ranges over all of `[0, ∞]` in `IsWeakTypeBound`, so no side conditions on `α` hide in the
  definition; `α = 0` and `α = ∞` are trivially fine.
* `f` is real-valued and integrable, as in the classical definition; the maximal function is
  `ℝ≥0∞`-valued so that it is defined for every `f`.
* The witness predicate is coordinatewise (`|c h - x| ≤ L/2 ∧ |r V - y| ≤ L/2`) rather than a
  distance in `Fin 2 → ℝ`, so the geometry is linear arithmetic; `dist_pi_le_iff` converts once.

## Deviation from the `/develop` procedure

The user asked for the whole formalization to be carried out in one session and pushed as it goes,
so the plan is executed immediately rather than waiting for approval, and closely related one-line
lemmas share a ticket (each still a separate single-conclusion declaration).
