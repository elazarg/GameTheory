# S-ZERO: constant-sum correlation proof spine

Title: Constant-sum correlation proof spine
Family ID: S-ZERO
Pinned roots: `GameTheory/Concepts/ZeroSum/ConstantSumCorrelated.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `a829d9d`
Canonical destination: `GameTheory.Core.BinaryCorrelated`; `GameTheory.Examples.Classic`
Domain contract / decision: D4-D5, D8-D10
Owner: Wave 2 / zero and constant sum
Status: in progress; 11 binary-correlation proof-spine declarations reviewed
Last verified: 2026-08-02

This bounded ledger claims the binary Matching-Pennies-like proof spine from
the predecessor constant-sum correlation file. It does not claim the earlier
general constant-sum value theorems. The successor states the result directly
on the canonical two-player `GameForm`, exact finite laws, and ordinary
`IsCorrelatedEq`; it therefore needs neither a `KernelGame` wrapper nor
boundedness and `Finite Outcome` premises.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/ZeroSum/ConstantSumCorrelated.lean` | `profilePairEquiv` | def | adapt | `GameTheory.GameForm.MatchingPenniesLike.profile`; `encodeProfile`; `profile_encodeProfile`; `encodeProfile_profile` | focused Core build (1,738 jobs) | The two inverse maps are exposed at the canonical dependent profile type; a second bundled label object is unnecessary. |
| same | `expect_eq_sum_profilePair` | theorem | adapt | `GameTheory.GameForm.MatchingPenniesLike.expect_eq_sum_profile` | focused Core build (1,738 jobs) | Reindexes an exact finite-law expectation over the four Boolean profiles without installing global strategy finiteness. |
| same | `correlatedEu_eq_sum_profilePair` | theorem | subsumed | `GameTheory.expectedUtility_outcomeLaw`; `GameTheory.GameForm.MatchingPenniesLike.expect_eq_sum_profile` | focused Core build (1,738 jobs) | Correlated expected utility is the composition of the general outcome-law identity and the binary reindexing theorem. |
| same | `update_profile_truePlayer` | theorem | adapt | `GameTheory.GameForm.MatchingPenniesLike.update_profile_zero` | focused Core build (1,738 jobs) | Canonical player zero replaces the predecessor's Boolean-to-player relabeling. |
| same | `update_profile_falsePlayer` | theorem | adapt | `GameTheory.GameForm.MatchingPenniesLike.update_profile_one` | focused Core build (1,738 jobs) | Canonical player one replaces the predecessor's Boolean-to-player relabeling. |
| same | `ce_prob_true_true_ge_true_false` | theorem | subsumed | `GameTheory.GameForm.MatchingPenniesLike.correlatedEq_profile_prob_eq_quarter` | focused Core build (1,738 jobs) | The private obedience inequality is retained inside the checked four-deviation proof. |
| same | `ce_prob_true_false_ge_false_false` | theorem | subsumed | `GameTheory.GameForm.MatchingPenniesLike.correlatedEq_profile_prob_eq_quarter` | focused Core build (1,738 jobs) | The private obedience inequality is retained inside the checked four-deviation proof. |
| same | `ce_prob_false_false_ge_false_true` | theorem | subsumed | `GameTheory.GameForm.MatchingPenniesLike.correlatedEq_profile_prob_eq_quarter` | focused Core build (1,738 jobs) | The private obedience inequality is retained inside the checked four-deviation proof. |
| same | `ce_prob_false_true_ge_true_true` | theorem | subsumed | `GameTheory.GameForm.MatchingPenniesLike.correlatedEq_profile_prob_eq_quarter` | focused Core build (1,738 jobs) | The private obedience inequality is retained inside the checked four-deviation proof. |
| same | `correlated_eq_profile_prob_eq_quarter` | theorem | adapt | `GameTheory.GameForm.MatchingPenniesLike.correlatedEq_profile_prob_eq_quarter` | focused Core build (1,738 jobs); axiom audit | Four recommendation-dependent deviations form the same mass-inequality cycle, and exact-law normalization makes every mass one quarter. |
| same | `correlated_eq_unique` | theorem | adapt | `GameTheory.GameForm.MatchingPenniesLike.correlatedEq_unique`; `GameTheory.Examples.matchingPennies_correlatedEq_unique` | focused example build (1,741 jobs); axiom audit | General uniqueness plus the concrete table-game consumer; the target is the canonical independent `FinDist.pi` law. |

Attribution: the pinned file supplies the four obedience deviations, their
cyclic mass inequalities, the normalization argument, and the extensional
uniqueness proof. The successor reuses that proof plan over exact finite laws
while specializing players to the public canonical `Fin 2` interface and
retaining dependent descriptive action carriers.

Validation:

```text
lake build GameTheory.Core.BinaryCorrelated GameTheory.Examples.Classic
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
lake build
```

A temporary module importing `GameTheory.Examples.Classic` ran `#print axioms`
on the profile reindexing theorem, the quarter-mass theorem, general uniqueness,
and both concrete Matching Pennies characterizations. Every declaration
reported only `propext`, `Classical.choice`, and `Quot.sound`.
The full reachability audit preserved every positive and negative boundary
probe, and the full project build completed in 3,367 jobs.
