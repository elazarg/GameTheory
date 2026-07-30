# T2: EFG behavioral/mixed correspondence

Title: Perfect-recall EFGs expose both Kuhn directions over canonical history laws
Family ID: T2 / F3
Pinned root: all nine declarations in `GameTheory/Languages/EFG/Kuhn.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `6766dfb`
Canonical destinations: `GameTheory.Protocol.Information`;
`GameTheory.Languages.EFG.Kuhn`
Domain contract / decision: D0, D2, D6, D7, D9; post-architecture gate W1-G
Owner: Wave 1 / EFG and Kuhn recovery
Status: complete
Last verified: 2026-07-30

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `Languages/EFG/Kuhn.lean` | `EFG.kuhn_behavioral_to_mixed_runDist` | theorem | adapt | `InformationModel.runMixed_toMixed` | EXP-017; hostile repeated-information test | The successor proves equality of full history laws on the canonical runner under the sharper `ActsOnceWhereItMatters` condition. |
| same | `EFG.kuhn_behavioral_to_mixed_evalDist` | theorem | subsumed | exact history-law equality, then `Game.kuhn_behavioral_to_mixed_outcomeLaw` | focused build; outcome-map wrapper | The generic pushforward corollary covers every retained outcome map instead of only the old tree evaluator. |
| same | `EFG.kuhn_behavioral_to_mixed` | theorem | adapt | `Game.kuhn_behavioral_to_mixed` | two-decision EFG integration test | The witness is the independent product of local laws over the canonical contingent-plan carrier. |
| same | `EFG.kuhn_behavioral_to_mixed_pr` | theorem | adapt | `Game.kuhn_behavioral_to_mixed`; `Game.kuhn_historyLaws` | D6 sharp-hypothesis split | The successor narrows the assumptions by stating no-revisit separately from recall. An EFG consumer discharges both rather than hiding absent-mindedness inside a stronger language-specific recall name. |
| same | `EFG.kuhn_behavioral_to_mixed_udist` | theorem | adapt | `Game.kuhn_behavioral_to_mixed_outcomeLaw`; `Game.kuhn_behavioral_to_mixed_expectedUtility` | focused build; arbitrary history utility probe | The successor generalizes the conclusion: exact history law yields arbitrary pushforwards and expected utility for every player. |
| same | `EFG.kuhn_mixed_to_behavioral_core` | private theorem | subsumed | `InformationModel.runMixed_toBehavioralWith` | EXP-018 | Conditioning, support, and fallback work is integrated once at the Protocol layer. |
| same | `EFG.compiledCore_runEq_to_evalDistEq` | private theorem | retired | no bridge required | D6 one execution semantics | The successor theorem already speaks about the canonical history runner, so no second run/evaluation bridge remains. |
| same | `EFG.kuhn_mixed_to_behavioral` | theorem | adapt | `Game.kuhn_mixed_to_behavioral` | perfect-recall two-decision EFG integration test | `PerfectRecall` supplies the weaker `ConstrainsAlike` fact actually consumed by the canonical conditioning proof. |
| same | `EFG.kuhn_mixed_to_behavioral_udist` | theorem | adapt | `Game.kuhn_mixed_to_behavioral_outcomeLaw`; `Game.kuhn_mixed_to_behavioral_expectedUtility` | focused build; axiom audit | The successor generalizes from utility distribution to full history-law equality before forgetting to utility. |

Attribution: the two Kuhn directions, the product-of-local-laws witness, and
the conditional behavioral reading come from the pinned EFG/Kuhn development.
The successor retains those mathematical ideas while replacing
`GameTree`/`ObsModelCore`/`PMF` with the already accepted
`ExecutionProtocol`/`InformationModel`/`FinDist` semantics. The expensive proof
was recovered at the Protocol layer in EXP-017 and EXP-018; this delivery adds
only the truthful EFG specialization.

Validation:

```text
lake build GameTheory.Languages.EFG.Kuhn
lake build GameTheory.Tests.EFGKuhn
lake build
pwsh -NoProfile -File scripts/phase0-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
```

The EFG test reuses the hostile two-vote protocol from
`GameTheory.Tests.Randomized`. Its signal records the first action before the
second decision, so perfect recall and no relevant information-state revisit
are both proved rather than assumed. A new tree-shapedness proof packages that
same protocol as an EFG. The test then checks both constructive directions,
equality of realizable history-law sets, and arbitrary history-dependent
expected utility through the EFG surface.

The public wrapper contains no second runner, generic certificate, direct
`Function.update`, source-level transport token, placeholder, `native_decide`,
custom axiom, Analysis import, or EFG-specific equilibrium predicate.
