# M-BAYES: finite-support revelation principle

Title: Canonical finite-support revelation principle
Family ID: M-BAYES
Pinned roots: `GameTheory/Mechanism/Bayesian/RevelationPrinciple.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `028fb91`
Canonical destination: `GameTheory.BayesianGame.toDirectMechanism` and
`GameTheory.BayesianGame.revelation_principle`, opt-in through `GameTheory.Mechanism`
Domain contract / decision: D4, D5, D8; validated F5/F6 Bayesian split
Owner: Post-architecture Wave 2 / mature Bayesian-mechanism recovery
Status: complete for the pinned revelation file; 6/6 declarations reviewed
Last verified: 2026-08-08

The predecessor introduced a second general-mechanism structure, a raw
type-contingent strategy profile, and a duplicate ex-ante BNE predicate.  The
successor observes that these are exactly the existing `BayesianGame`, its
canonical signature-bound profile, and ordinary `IsNash`.  The induced direct
mechanism retains true types separately from reported types and uses only
`Profile.update`.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Mechanism/Bayesian/RevelationPrinciple.lean` | `GeneralMechanism` | structure | subsumed | `GameTheory.BayesianGame` | focused build; hostile nonidentity plan | Type/action/payoff data already have a canonical owner, with the prior supplied by the game rather than a later predicate. |
| same | `StrategyProfile` | def | subsumed | `Profile B.signature` | focused build | Type-contingent plans remain bound to the Bayesian signature. |
| same | `payoff` | def | subsumed | `BayesianGame.payoff`; `BayesianGame.actionsOf` | focused build | Realized payoff evaluation is the existing game data applied to the plan's realized actions. |
| same | `IsBNE` | def | retired | `IsNash B.toForm (euPreference B.utility)` | D4/D5 single-equilibrium rule | The predecessor's second ex-ante inequality is exactly the canonical Nash characterization. |
| same | `toDirect` | def | adapt | `BayesianGame.toDirectMechanism` | focused build; truthful and deviation commuting laws | Reports are types; the original plan is applied to reports while utility continues to read true types. |
| same | `revelation_principle` | theorem | adapt | `BayesianGame.revelation_principle` | hostile nonidentity-plan test; axiom audit | Canonical Nash of the original plan implies canonical truthful Nash of the induced direct mechanism, without type-carrier finiteness. |

## Validation

```text
lake build GameTheory.Mechanism.Revelation GameTheory.Tests.Revelation GameTheory.Mechanism
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected -SkipReachability
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
```

The hostile Boolean game has a fair private type and a visibly nonidentity
equilibrium plan that flips the type.  In the induced direct mechanism,
truthful reporting applies that flip and pays two, while the false type's
opposite report pays zero.  This rules out an identity-plan or constant-payoff
proof.  The broader M-BAYES family remains partial: the next critical workflow
is a finite persuasion/information-design theorem.
