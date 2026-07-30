# F6: incentive compatibility gives truthful Bayes-Nash

Title: Direct mechanisms compile truthfulness to ordinary Bayesian Nash
Family ID: F6
Pinned roots: the IC/BIC and Bayesian compiler cluster in
`GameTheory/Mechanism/Bayesian/MechanismDesign.lean`, through
`isIC_implies_truthful_bayesNash`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `dd20631`
Canonical destination: `GameTheory.Languages.BayesianMechanism`
Domain contract / decision: D4, D5, D8; post-architecture gate W1-E
Owner: Wave 1 / Bayesian mechanisms
Status: complete for the frozen F6 theorem; welfare, participation, revelation,
and information-design declarations remain M-BAYES
Last verified: 2026-07-30

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `Mechanism/Bayesian/MechanismDesign.lean` | `Mechanism` | structure | adapt | `Languages.BayesianMechanism` | focused and full builds | The successor separates true types, reports, outcome, and true-type-dependent utility. |
| same | `isIC` | definition | adapt | `BayesianMechanism.IsIncentiveCompatible` | hostile Boolean mechanism | Truth weakly dominates every report for every true type and opponents' report profile. |
| same | `isBIC` | definition | retired | ordinary `IsNash` of `toBayesianGame.toForm` | D4 single-concept rule | No second Bayesian equilibrium predicate. |
| same | `isIC_implies_isBIC` | theorem | subsumed | `isNash_truthfulPlan_of_isIncentiveCompatible` | focused build; axiom audit | The stronger public result goes directly to the canonical equilibrium target. |
| same | `inducedBayesianGame` | definition | adapt | `BayesianMechanism.toBayesianGame` | focused build; hostile probe | Reports are actions; utility reads true types separately. |
| same | `truthful` | definition | adapt | `BayesianMechanism.truthfulPlan` | focused build; hostile probe | Each own type maps to its truthful report. |
| same | `update_truthful_apply` | theorem | adapt | `actionsOf_update_truthfulPlan` | focused build; source audit | Uses `Profile.update` and stays inside the compiler proof. |
| same | `isIC_implies_truthful_bayesNash` | theorem | adapt | `isNash_truthfulPlan_of_isIncentiveCompatible` | hostile Boolean mechanism; axiom audit | The frozen F6 theorem, stated with ordinary `IsNash`. |
| same | `isStrategyProof` | definition | retired | `IsIncentiveCompatible` | duplicate synonym | One public predicate is sufficient. |
| same | `isStrategyProof_iff_isIC` | theorem | retired | definitional duplicate | duplicate synonym | No compatibility alias. |
| same | `isBIC_of_truthful_bayesNash` | theorem | retired | public target is already `IsNash` | D4 single-concept rule | There is no wrapper to unfold back into. |

This bounded F6 inventory covers the IC/compiler/equilibrium cluster, including
its duplicate synonyms and converse wrapper. The later social-welfare,
individual-rationality, revelation, and information-design declarations are
not silently credited; they remain in the broader M-BAYES inventory.

The predecessor's mechanism payoff depends only on the reported profile, so a
misreport can accidentally change the type used to evaluate the deviator. The
successor does not copy that conflation: utility receives the true type profile
and the chosen outcome separately. The existing complete-information
`Languages.Mechanism` remains the right consumer when utility is fixed rather
than privately typed.

Validation:

```text
lake build GameTheory.Languages.BayesianMechanism GameTheory.Tests.BayesianMechanism
lake build GameTheory.Core.BayesCorrelated GameTheory.Tests.BayesCorrelated
lake build
pwsh -NoProfile -File scripts/phase0-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
```

The hostile mechanism has a fair Boolean true type, Boolean reports, and payoff
one exactly when the selected report equals the true type. Its pointwise IC
proof covers arbitrary reports; an explicit false-type deviation proves truth
pays one while lying pays zero. The compiler yields ordinary Nash, and F5 then
turns the truthful recommendation law into a BCE.

The focused trust audit for the compiler theorem and its BCE consumer reports
only `propext`, `Classical.choice`, and `Quot.sound`. The language source
contains no direct `Function.update`, source-level transport token,
placeholder, `native_decide`, or custom axiom.
