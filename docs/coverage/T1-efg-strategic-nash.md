# T1: EFG strategic extraction and Nash transfer

Title: Information-local EFG contingent plans compile to pure and mixed Nash
Family ID: T1
Pinned roots: all declarations in
`GameTheory/Languages/Bridges/EFG_NFG.lean`, plus the mixed-Nash lift
`KernelGame.GameIsomorphism.mixedExtension_isNash_iff` in
`GameTheory/Concepts/Mixed/GameMorphism.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `ff1b27b`
Canonical destination: `GameTheory.Languages.EFG.Strategic`
Domain contract / decision: D0, D4, D5, D6, D7; post-architecture gate W1-F
Owner: Wave 1 / EFG strategic transfer
Status: complete
Last verified: 2026-07-30

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `Languages/Bridges/EFG_NFG.lean` | `EFGGame.toNFGGame` | definition | adapt | `Languages.EFG.Game.toGameForm` | focused and full builds | The successor compiles information-local contingent plans directly to the accepted stochastic `GameForm`; chance remains in the outcome law instead of being collapsed into a payoff-vector outcome. |
| same | `EFGGame.toNFGGame_eu` | theorem | adapt | `Languages.EFG.Game.isNash_toGameForm_iff` | nonconstant-payoff pure-Nash probe; axiom audit | The named compiler evaluation law is reused inside an exact native-run Nash characterization rather than introducing a second expected-utility game. |
| same | `EFGGame.toNFGGameDet` | definition | retired | `Languages.EFG.Game.toGameForm` | D6 one execution semantics | The stochastic form already specializes to deterministic transitions; a second deterministic compiler would be parallel semantics. |
| same | `toNFGGameDet_outcomeKernel` | theorem | subsumed | `Languages.EFG.Game.toGameForm_play` | focused build | The one compiler law covers stochastic and deterministic EFGs. |
| same | `EFGGame.toNFGGameDet_morphism` | definition | retired | direct named law | D7 | The generic certificate level was rejected; this isolated identity bridge enables no theorem beyond the direct evaluation law. |
| `Concepts/Mixed/GameMorphism.lean` | `GameIsomorphism.mixedExtension_isNash_iff` | theorem | adapt | `Languages.EFG.Game.isNash_mixed_toGameForm_iff` | profitable-deviation mixed probe; axiom audit | The successor uses the one accepted `GameForm.mixed` and ordinary `IsNash`, exposing the exact `runMixed` inequality without a morphism hierarchy. |

The predecessor contains no named pure- or mixed-Nash transfer for the EFG
bridge. Phase 0 therefore froze those two results as new successor obligations
rather than crediting a generic morphism. The successor statement will not
define an EFG-specific equilibrium predicate: each theorem characterizes the
existing `IsNash` directly in the native `run` or `runMixed` vocabulary.

Attribution: the predecessor's direct strategic-form expected-utility equality
and mixed-lift idea are retained. The representation changes from
`KernelGame`/`NFGGame`/`PMF` to the accepted
`InformationModel.toGameForm`/`GameForm.mixed`/`FinDist` path.

Validation:

```text
lake build GameTheory.Languages.EFG.Strategic
lake build GameTheory.Analysis.Protocol.EFGStrategicTest
lake build
pwsh -NoProfile -File scripts/phase0-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
```

`ContingentPlan` is a transparent specialization of the canonical
information-local `Policy`, and `contingentPlanFintype` derives an enumeration
only from explicit finite information/menu capabilities. The two transfer
proofs each use the generic `isNash_iff` and reduce in two proof lines, below
Phase 0's 15-line pure and 25-line mixed budgets.

The hostile fixture is the existing fair hidden-bit EFG. Utility is one exactly
when the terminal action is `false`, so it is nonconstant. The always-false
contingent plan is Nash. A genuine `1 / 2`–`1 / 2` mix of the always-false and
always-true plans has value `1 / 2` and is not Nash: deviating to the point mass
on always-false raises value to one. The test lives under `Analysis` because it
reuses that root's EFG fixture; moving it outside was rejected by the boundary
audit before completion.

The focused axiom audit for both transfer theorems and both hostile conclusions
reports only `propext`, `Classical.choice`, and `Quot.sound`. The public language
module contains no direct `Function.update`, source-level transport token,
placeholder, `native_decide`, custom axiom, or forbidden import.
