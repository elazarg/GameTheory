# S-MIX: binary mixed-equilibrium calculus

Title: Binary mixed-equilibrium calculus
Family ID: S-MIX
Pinned roots: `GameTheory/Concepts/Mixed/BinaryMixed.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `66125a5`
Canonical destination: `GameTheory.Core.BinaryMixed`; `GameTheory.Examples.Classic`
Domain contract / decision: D4-D5, D8-D10
Owner: Wave 2 / mixed equilibrium
Status: in progress; 15 proof-spine declarations reviewed
Last verified: 2026-08-02

This bounded ledger claims the semantic proof spine needed for the exact
half/half characterization. It does not yet claim the predecessor file's
broader label plumbing, uniform-profile wrappers, or balanced-game API. The
successor fixes the canonical player type at `Fin 2`, permits dependent
descriptive action carriers through per-player Boolean equivalences, and works
over exact finite laws without PMF or boundedness premises.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Mixed/BinaryMixed.lean` | `MatchingPenniesLike` | structure | adapt | `GameTheory.GameForm.MatchingPenniesLike` | focused Core build (1,721 jobs) | The semantic payoff pattern survives; arbitrary player relabeling is omitted because the canonical theorem is natively two-player and action labels remain dependent. |
| same | `mixedEu_true_formula_of_bounded` | theorem | subsumed | `GameTheory.GameForm.MatchingPenniesLike.mixedExpectedUtility_zero` | focused Core build (1,721 jobs) | Exact finite support makes the polynomial identity unconditional. |
| same | `mixedEu_false_formula_of_bounded` | theorem | subsumed | `GameTheory.GameForm.MatchingPenniesLike.mixedExpectedUtility_one` | focused Core build (1,721 jobs) | The opposite-payoff polynomial needs no bound. |
| same | `mixedEu_true_formula` | theorem | adapt | `GameTheory.GameForm.MatchingPenniesLike.mixedExpectedUtility_zero` | focused Core build (1,721 jobs) | Canonical expected utility over `GameForm.mixed`. |
| same | `mixedEu_false_formula` | theorem | adapt | `GameTheory.GameForm.MatchingPenniesLike.mixedExpectedUtility_one` | focused Core build (1,721 jobs) | Canonical expected utility over `GameForm.mixed`. |
| same | `deviationGain_true_true_formula_of_bounded` | theorem | subsumed | `mixedExpectedUtility_zero`; `probTrue_update_pure_true`; `probTrue_update_of_ne` | focused Core build (1,721 jobs) | The named unconditional polynomial plus coordinate laws computes the same gain; no second gain API is retained. |
| same | `deviationGain_true_false_formula_of_bounded` | theorem | subsumed | `mixedExpectedUtility_zero`; `probTrue_update_pure_false`; `probTrue_update_of_ne` | focused Core build (1,721 jobs) | Same checked theorem chain for the false-labeled deviation. |
| same | `deviationGain_false_true_formula_of_bounded` | theorem | subsumed | `mixedExpectedUtility_one`; `probTrue_update_pure_true`; `probTrue_update_of_ne` | focused Core build (1,721 jobs) | Same checked theorem chain for player one. |
| same | `deviationGain_false_false_formula_of_bounded` | theorem | subsumed | `mixedExpectedUtility_one`; `probTrue_update_pure_false`; `probTrue_update_of_ne` | focused Core build (1,721 jobs) | Same checked theorem chain for player one's false-labeled deviation. |
| same | `mixedGain_true_true_formula` | theorem | subsumed | `mixedExpectedUtility_zero`; `probTrue_update_pure_true`; `probTrue_update_of_ne` | focused Core build (1,721 jobs) | The predecessor's derived gain definition is not recreated. |
| same | `mixedGain_true_false_formula` | theorem | subsumed | `mixedExpectedUtility_zero`; `probTrue_update_pure_false`; `probTrue_update_of_ne` | focused Core build (1,721 jobs) | Exact finite-law chain retains the mathematical equality. |
| same | `mixedGain_false_true_formula` | theorem | subsumed | `mixedExpectedUtility_one`; `probTrue_update_pure_true`; `probTrue_update_of_ne` | focused Core build (1,721 jobs) | Exact finite-law chain retains the mathematical equality. |
| same | `mixedGain_false_false_formula` | theorem | subsumed | `mixedExpectedUtility_one`; `probTrue_update_pure_false`; `probTrue_update_of_ne` | focused Core build (1,721 jobs) | Exact finite-law chain retains the mathematical equality. |
| same | `mixed_nash_iff_half_of_bounded@613` | theorem | subsumed | `GameTheory.GameForm.MatchingPenniesLike.isNash_iff_half` | focused Core build (1,721 jobs); axiom audit | Preference and finite-law semantics remove the boundedness premise. |
| same | `mixed_nash_iff_half@669` | theorem | adapt | `GameTheory.GameForm.MatchingPenniesLike.isNash_iff_half`; `GameTheory.Examples.matchingPennies_mixed_isNash_iff_half` | focused example build (1,740 jobs); axiom audit | General canonical theorem plus the concrete Matching Pennies consumer; no `IsNashMixed` wrapper. |

Attribution: the pinned file supplies the binary-label proof strategy, the two
expected-utility polynomials, the four unilateral-deviation inequalities, and
the `nlinarith` closure of the exact characterization. The successor retains
that mathematics while eliminating the `KernelGame`, PMF, bounded-utility,
player-reindexing, and parallel mixed-equilibrium surfaces from this slice.

Validation:

```text
lake build GameTheory.Core.BinaryMixed
lake build GameTheory.Examples.Classic
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
lake build
```

A temporary module importing `GameTheory.Examples.Classic` ran `#print axioms`
on `FinDist.prob_le_one`, both mixed-utility polynomials, the general exact-Nash
characterization, and its Matching Pennies consumer. Every declaration
reported only `propext`, `Classical.choice`, and `Quot.sound`.
The full reachability audit preserved every boundary probe and source budget,
and the full project build completed in 3,366 jobs.
