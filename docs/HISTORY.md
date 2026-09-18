# How the result was found

This document records the provenance of the configuration and of the constant `Φ`. The exploratory
programs, the exact certificate and the full report are kept outside this repository; none of them is
part of the Lean proof.

## 1. The starting point

The project began from a research brief, *Improving the planar centered maximal constant*
(18 September 2026), supplied by the maintainer. The brief:

* recalled Aldaz's bound `c₂ ≥ 3/4 - √2/4 + √6/2 = 1.62119…` (Czechoslovak Math. J. 50 (2000),
  Proposition 1.4 with `n = 2`), obtained from a rectangular lattice of unit Dirac masses with
  spacings `3/2` and `(1 + √2)/2`;
* proposed and proved the seed `c₂ ≥ 3(2 + √6)/8 = 1.66856…`, a unit lattice with spacings `3/2` and
  `(2 + √6)/4` whose level-one set covers the whole period cell;
* set out the periodic-to-finite reduction, an exact block-rectangle evaluator for the level set of a
  rectangular lattice, and the suggestion to try periodic motifs with weights.

The brief makes no novelty claim for the seed. The brief is not included in this repository.

## 2. The unit rectangular lattice is exhausted at the seed

An independent audit of every claim in the brief (twelve agents, exact algebra) found no error. An
exact evaluator for the level-one area `F(H, V)` of the unit lattice `HZ × VZ` was implemented twice
(one blind reimplementation from the brief alone; the two agree bit for bit). Sweeps over
`H ∈ [1, 8]`, `V ∈ [0.2, 3]` found the seed as the global maximum; a branch-and-bound with exact
rational box bounds, together with the brief's piecewise-bilinear breakpoint argument near the seed,
certified `max F = 3(2 + √6)/8` on `{1 ≤ H ≤ 8, 0.2 ≤ V ≤ H}`. This restricted optimality statement
is not formalized in Lean.

## 3. Weights open the gap

Periodic *product* measures `μ_X ⊗ μ_Y`, with several weighted points per period on each axis, keep
the block-witness structure of the brief: a square captures a run of consecutive columns and a run of
consecutive rows, and the level set is an exact finite union of rectangles. A Nelder–Mead search
with random restarts over seventeen such families converged in every family able to express it to
one configuration:

* columns at spacing `h = (5 + √22)/6` with masses alternating `1, w, 1, w, …`,
  `w = (17 + 4√22)/9`;
* rows at spacing `V = (11 + √22)/6 = h + 1` with unit masses;

giving `Φ = 1.68550999335552518466528…`. Its parameters are fixed by three edge collisions of
witness rectangles, all equivalent to `3u² - 4u - 6 = 0` for `u = √(1 + w) = (2 + √22)/3`.

Searches over non-product motifs (unit-weight two-atom motifs; weighted two- and three-atom motifs,
checkerboard weights, the optimum plus a free extra atom; about 60 000 completed restarts) found
nothing above `Φ`; every optimum at or near `Φ` was this configuration in disguise. Unit-weight
motifs with three or four atoms per cell were not searched substantially. No optimality is claimed.

## 4. Certification before formalization

* An exact rational certificate proves `c₂ ≥ 1.685509993355498` at
  12-decimal rational parameters (twelve witness types, 22 rectangles, exact union area, then the
  finite-mass passage).
* A symbolic computation gives the exact area; `Φ` has an irreducible
  minimal polynomial of degree 16 and the closed form stated in `Challenge.lean`.
* Six independent referee agents attacked the certificate (witness principle, weighted finite-mass
  passage, line-by-line code audit with independent union-area algorithms, a recomputation from the
  definition of the measure alone at 60 digits, the exact algebra, and a whole-chain sceptic). All
  six concluded that the claim holds; the cosmetic corrections they raised are adopted.

## 5. The Lean proof

The Lean proof simplifies the certificate: by the reflection symmetry of the lattice it needs only
six witnesses on a quarter of the period cell and only the lower bound `|goodSet| ≥ 2hV - 4ab` for
the covered area, not its exact value. `docs/PROOF.md` gives the argument step by step.
