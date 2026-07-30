# F4: one-shot deviation iff subgame perfection

Title: Well-founded information-local one-shot deviation principle
Family ID: F4
Pinned roots: `GameTheory/Languages/EFG/OneShotDeviation.lean`; declaration
`EFGGame.IsSubgamePerfectEq` in
`GameTheory/Languages/EFG/Refinements.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: working tree based on `f23e3ef`
Canonical destination: `GameTheory.Protocol.SubgamePerfect`
Domain contract / decision: D6, EXP-021, EXP-025, EXP-036
Owner: Wave 1 / sequential theory
Status: complete for the frozen semantic theorem; language wrappers remain
with L-EFG
Last verified: 2026-07-30

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `Languages/EFG/Refinements.lean` | `EFGGame.IsSubgamePerfectEq` | definition | adapt | `InformationModel.IsSubgamePerfect` | EXP-036; full build | Quantifies over every complete history and every whole information-local replacement policy; no subtree evaluator. |
| `Languages/EFG/OneShotDeviation.lean` | `HasNoOneShotDeviation` | definition | adapt | `InformationModel.HasNoProfitableOneShotDeviation` | EXP-036; off-path probe | The successor deviation is a typed legal choice followed by the original profile. |
| same | `IsOneShotOptimalAtEveryNode` | definition | retired | EXP-036 history recursion | source comparison | Syntax-recursive duplicate of the reachability presentation; no independent mathematical payload. |
| same | `IsOneShotOptimalAtEveryNode.of_reachBy` | theorem | retired | EXP-036 history recursion | source comparison | Structural traversal helper for the retired presentation. |
| same | `hasNoOneShotDeviation_iff_everyNode` | theorem | retired | EXP-036 history recursion | source comparison | Representation-conversion theorem made unnecessary by defining the stable predicate on histories once. |
| same | `spe_hasNoOneShotDeviation` | theorem | adapt | `hasNoProfitableOneShotDeviation_of_isSubgamePerfect` | EXP-036; axiom audit | The exact converse-facing no-revisit assumption is `ActsOnceWhereItMatters`. |
| same | `nash_of_noOSD_of_bounded` | theorem | subsumed | `isSubgamePerfect_of_hasNoProfitableOneShotDeviation` | EXP-036; generic theorem | The successor directly proves whole-policy optimality at every history and needs no bounded-utility hypothesis. |
| same | `nash_of_noOSD` | theorem | subsumed | `isSubgamePerfect_of_hasNoProfitableOneShotDeviation` | EXP-036; generic theorem | The finite-outcome wrapper disappears because every transition law already has finite support. |
| same | `hasNoOneShotDeviation_spe_of_bounded` | theorem | subsumed | `isSubgamePerfect_of_hasNoProfitableOneShotDeviation` | EXP-036; generic theorem | Stronger stable result over arbitrary real terminal payoff. |
| same | `hasNoOneShotDeviation_spe` | theorem | subsumed | `isSubgamePerfect_of_hasNoProfitableOneShotDeviation` | EXP-036; generic theorem | No finite-outcome wrapper is required. |
| same | `oneShotDeviation_iff_spe_of_bounded` | theorem | adapt | `isSubgamePerfect_iff_hasNoProfitableOneShotDeviation` | EXP-036; phase 2/3 audits | The successor theorem is well-founded, information-local, and quantified over off-path histories. |
| same | `oneShotDeviation_iff_spe` | theorem | subsumed | `isSubgamePerfect_iff_hasNoProfitableOneShotDeviation` | EXP-036; full build and axiom audit | The finite-outcome convenience theorem is strictly weaker than the stable successor. |

Attribution: the predecessor's structural induction and persistent local
replacement argument motivated the two implications. The successor reuses the
accepted Protocol transition law, history carrier, no-revisit condition, and
profile update operation; it does not copy the predecessor's tree evaluator or
subgame syntax.

Validation:

```text
lake build GameTheory.Protocol.SubgamePerfect GameTheory.Tests.SubgamePerfect
lake build
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
```

The focused axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. The test proves that the incumbent is optimal against every whole
replacement policy from the initial history while failing subgame perfection
at an explicitly off-path decision history.
