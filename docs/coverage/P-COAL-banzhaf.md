# P-COAL: Banzhaf and Shapley--Shubik power indices

Title: Probabilistic Banzhaf value and simple-game power
Family ID: P-COAL
Pinned root: `GameTheory/Cooperative/CoalitionalGame/Banzhaf.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `98c7cf1`
Canonical destination: `GameTheory.CoalitionalGame` in `Cooperative.Banzhaf`
Domain contract / decision: D9; post-architecture P-COAL BFS gate
Owner: Wave 4 / cooperative games
Status: complete; all 11 declarations adapted with no deferred rows
Last verified: 2026-08-09

The successor defines both power indices on the canonical
`CoalitionalGame`.  The finite enumeration belongs to the value operation,
not the game carrier, while simple-game assumptions form a theorem-local
certificate.  The opt-in Cooperative leaf therefore adds no parallel voting
game, allocation, marginal-contribution, or Shapley surface.  The hostile
three-agent majority fixture is simple, has raw Banzhaf power one half for a
designated agent, and Shapley--Shubik power one third for every agent.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Cooperative/CoalitionalGame/Banzhaf.lean` | `probabilisticBanzhafValue` | def | adapt | `CoalitionalGame.probabilisticBanzhafValue` | focused Cooperative build | Returns the canonical `Allocation`; remains explicitly unnormalized. |
| same | `probabilisticBanzhafValue_null` | theorem | adapt | same name | focused Cooperative build | Reuses canonical `IsNull`. |
| same | `filter_notMem_eq_powerset_compl` | theorem | port | same name | focused Cooperative build | Exact finite coalition-enumeration identity. |
| same | `card_filter_notMem` | theorem | port | same name | focused Cooperative build | Denominator is the actual number of coalitions of the other agents. |
| same | `probabilisticBanzhafValue_additive` | theorem | adapt | `probabilisticBanzhafValue_add` | focused Cooperative build | Reuses canonical coalitional-game addition. |
| same | `probabilisticBanzhafValue_scalar` | theorem | adapt | `probabilisticBanzhafValue_smul` | focused Cooperative build | Reuses canonical scalar multiplication and naming. |
| same | `IsSimpleGame` | structure | adapt | `CoalitionalGame.IsSimpleGame` | majority-game fixture | Boolean values, monotonicity, and a winning grand coalition are a certificate, not stored base semantics. |
| same | `shapleyShubikIndex` | def | adapt | `CoalitionalGame.shapleyShubikIndex` | focused Cooperative build | Transparent specialization of the one Shapley value. |
| same | `shapleyShubikIndex_sum_eq_one` | theorem | adapt | same name | focused Cooperative build | Follows from canonical Shapley efficiency and the simple-game certificate. |
| same | `shapleyShubikIndex_null` | theorem | adapt | same name | focused Cooperative build | Follows from the canonical Shapley null-agent theorem. |
| same | `unanimityGame_singleton_probabilisticBanzhafValue` | theorem | adapt | same name | focused Cooperative build | Generic normalization witness for a pivotal singleton. |

Attribution: the predecessor supplied the full probabilistic Banzhaf and
simple-game theorem family.  The successor ports that mathematics onto the
already validated coalitional and Shapley owners, replacing its probability
support import with direct finite averaging.

This bounded ledger does not close P-COAL.  Convex games and core nonemptiness,
Bondareva balancedness, additive and weighted-majority examples, and cost of
stability remain separate BFS gates.  They must continue to use the canonical
characteristic function and allocation rather than reconstructing the pinned
`CoalGame` wrapper.

The null, additivity, singleton-unanimity, majority Banzhaf, and
Shapley--Shubik fixture theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`.  Source checks find no raw
`Function.update`, source transport, placeholder, custom axiom, native
evaluation, or build-output command.

Validation:

```text
lake build GameTheory.Cooperative.Banzhaf GameTheory.Tests.Banzhaf GameTheory.Cooperative
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected -SkipReachability
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
lake build
git diff --check
```
