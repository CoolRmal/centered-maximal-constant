# Ticket board

Each proof ticket fills the `sorry`s of the listed declarations; statements are those already in the
skeleton (commit `5a6444f`), and the proof sketches are those of `decomposition.md` and
`docs/PROOF.md`. Related one-line lemmas share a ticket.

| ticket | file | declarations | depends on | status |
|---|---|---|---|---|
| T01 | Basic | `le_maximalFunction`, `exists_lt_average_of_lt_maximalFunction`, `volume_closedBall_eq`, `IsWeakTypeBound.mono`, `weakTypeConstant_le`, `le_weakTypeConstant` | — | done |
| CLEANUP-1 | Basic | `/cleanup` | T01 | done |
| T02 | Lattice/Constants | exact identities (`sqrt22_sq` … `sideLHL2_sq`) | — | done |
| T03 | Lattice/Constants | numerical bounds (`root_gt` … `hgap_pos`) | T02 | done |
| T04 | Lattice/Constants | `phi_eq` | T02 | done |
| CLEANUP-2 | Lattice/Constants | `/cleanup` | T02–T04 | done |
| T05 | Lattice/Witness | symmetry lemmas and `…_subset_nearBox` | CLEANUP-2 | done |
| T06 | Lattice/Witness | six witnesses | CLEANUP-2 | done |
| T07 | Lattice/Witness | `exists_isWitness_of_nonneg`, `exists_isWitness_of_abs` | T05, T06 | done |
| CLEANUP-3 | Lattice/Witness | `/cleanup` | T07 | done |
| T08 | Lattice/Smear | `colWeight_pos`, `smeared_nonneg`, `integrable_smeared` | T01 | done |
| T09 | Lattice/Smear | `sum_colWeight_Icc`, `sum_colWeight_atomBox_le`, `lintegral_smeared` | T08 | done |
| T10 | Lattice/Smear | `ofReal_sq_le_setLIntegral_smeared`, `lt_maximalFunction_smeared` | T08, CLEANUP-3 | done |
| CLEANUP-4 | Lattice/Smear | `/cleanup` | T10 | done |
| T11 | Lattice/LowerBound | `measurableSet_goodSet`, `ofReal_le_volume_goodSet`, `volume_goodCopy` | CLEANUP-4 | done |
| T12 | Lattice/LowerBound | `pairwiseDisjoint_goodCopy`, `exists_isWitness_of_mem_goodCopy`, `nearBox_subset_atomBox` | T11 | done |
| T13 | Lattice/LowerBound | `ofReal_le_volume_levelSet` | T12 | done |
| CLEANUP-5 | Lattice/LowerBound | `/cleanup` | T13 | done |
| T14 | Lattice/LowerBound | `ofReal_mul_phi_le`, `ofReal_phi_le` (milestone) | CLEANUP-5, T04 | done |
| T15 | UpperBound | `isWeakTypeBound_zero_one`, `radius_le_of_mul_volume_lt` | T01 | done |
| T16 | UpperBound | `mul_volume_le_of_one_lt` | T15 | done |
| T17 | UpperBound | `isWeakTypeBound_two_pow` (milestone) | T16 | done |
| CLEANUP-6 | UpperBound | `/cleanup` | T17 | done |
| CLEANUP-ALL | all | `/cleanup-all`, comparator run in CI | T14, CLEANUP-6 | done |
| T18 | metadata | `formalization.yaml`, README with literature account, `docs/HISTORY.md` | CLEANUP-ALL | done |
| CLEANUP-FINAL | all | final review (`/pre-submit` checklist) | T18 | open |
