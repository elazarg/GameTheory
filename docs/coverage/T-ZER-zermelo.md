# T-ZER: Zermelo backward induction

Title: Zermelo backward induction for perfect-information extensive forms
Family ID: T-ZER
Pinned root: `GameTheory/Theorems/Zermelo.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `bc5c5ba8234da345c6b998d3510418e62de98684`
Canonical destination: `GameTheory.Protocol.Zermelo`; transparent `GameTheory.Languages.EFG.Zermelo` wrapper
Domain contract / decision: D6 execution/information separation; F4 one-shot-deviation principle; `Protocol.Backward` continues to evaluate fixed choosers only
Owner: Wave 3 sequential recovery
Status: complete; 5/5 declarations reviewed, with no deferred rows
Last verified: 2026-08-03

The pinned file has three clusters: syntax-specific sibling-subtree
disjointness, a constructive no-one-shot-deviation theorem, and bounded or
finite-outcome existence wrappers. The successor keeps only the mathematics:
it maximizes finite local `InformationModel.Choice` carriers by well-founded
history recursion, assembles one information-local contingent-plan profile,
proves its Bellman value and one-shot optimality after every history, and uses
the existing one-shot-to-SPE theorem. Chance remains the protocol transition
law, off-path play is covered, and neither bounded utility nor finite states,
players, histories, or outcomes are required.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Theorems/Zermelo.lean` | `perfectInfo_disjoint_subtrees` | theorem | retired | `InformationModel.SeparatesDecisionHistories` | Pinned source comparison; `Protocol.Zermelo` profile-assembly proof | This was structural recursion machinery for v1's node/subtree policy representation. The successor states perfect information directly on canonical complete histories and defines no second subtree evaluator. |
| same | `perfectInfo_disjoint_chance_subtrees` | theorem | retired | canonical Protocol chance transition | Pinned source comparison; chance-root hostile witness | Chance is a nondegenerate `ExecutionProtocol.step` at an idle state, so no chance node owns a policy coordinate and no sibling-subtree transport lemma survives. |
| same | `exists_noOSD` | theorem | adapt | `InformationModel.backwardProfile_hasNoProfitableOneShotDeviation` | focused build; Bellman/profile equality and finite-max theorem chain | The result is language-independent and stronger in carrier generality while retaining finite local choices, single-mover play, well-foundedness, and strong perfect information. |
| same | `zermelo_of_bounded` | theorem | subsumed | `InformationModel.exists_isSubgamePerfect`; `EFG.Game.exists_isSubgamePerfect` | focused build; existing one-shot-to-SPE theorem | The successor proves pure SPE existence for arbitrary real history utility, so no boundedness wrapper is needed. |
| same | `zermelo` | theorem | subsumed | `InformationModel.exists_isSubgamePerfect`; `EFG.Game.exists_isSubgamePerfect` | focused build; hostile chance/off-path EFG witness | Finite outcomes were used only to obtain boundedness in v1. The successor needs neither assumption and avoids `Fintype.ofFinite`. |

Disposition count: 1 adapt, 2 subsumed, 2 retired.

Attribution: declaration names, paths, and theorem clusters are from pinned
`GameTheory/Theorems/Zermelo.lean`. The successor theorem chain was checked
through `GameTheory.Protocol.Zermelo`, `GameTheory.Protocol.SubgamePerfect`,
and the transparent `GameTheory.Languages.EFG.Zermelo` specialization; no
theorem was credited by name similarity.

Validation:

```text
lake build GameTheory.Protocol.Zermelo
lake build GameTheory.Languages.EFG.Zermelo
lake build GameTheory.Tests.EFGZermelo
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```
