# F5: Bayes-Nash outcome laws are Bayes-correlated

Title: Finite recommendation laws, obedience, and the Bayes-Nash outcome transfer
Family ID: F5
Pinned roots: the recommendation-law and information-structure cluster in
`GameTheory/Mechanism/Bayesian/BayesCorrelatedEq.lean`, through
`InformationStructure.BayesNash.outcomeLaw_bayesCorrelatedEq`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `dd20631`
Canonical destination: `GameTheory.Core.BayesCorrelated`
Domain contract / decision: D4, D5, D6; post-architecture gate W1-E
Owner: Wave 1 / Bayesian correlation
Status: complete for the frozen F5 theorem; complete-information correlation
specializations remain S-CORR
Last verified: 2026-07-30

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `Mechanism/Bayesian/BayesCorrelatedEq.lean` | `TypeProfile` | abbreviation | subsumed | dependent function already used by `BayesianGame.prior` | source comparison | No duplicate alias is required. |
| same | `ActionProfile` | abbreviation | subsumed | `Profile B.actionSignature` | source comparison | Uses the canonical signature-owned profile shape. |
| same | `RecommendationLaw` | abbreviation | adapt | `BayesianGame.RecommendationLaw` | focused and full builds | A `FinDist` over type/action profiles. |
| same | `BayesPlausible` | definition | adapt | `BayesianGame.IsBayesPlausible` | focused build | Type marginal equals the accepted common prior. |
| same | `ObedienceDeviation` | abbreviation | adapt | `BayesianGame.ObedienceDeviation` | focused build | Reads only own type and recommended action. |
| same | `recommendedEU` | definition | adapt | `BayesianGame.recommendedValue` | focused build | Uses `BayesianGame.payoff` directly. |
| same | `strategyRecommendationLaw` | definition | adapt | `BayesianGame.strategyRecommendationLaw` | focused build | Deterministic recommendations induced by a contingent plan. |
| same | `strategyRecommendationLaw_bayesPlausible` | theorem | adapt | `BayesianGame.strategyRecommendationLaw_isBayesPlausible` | focused build | Finite-law marginal calculation. |
| same | `recommendedEU_strategyRecommendationLaw` | theorem | adapt | `BayesianGame.recommendedValue_strategyRecommendationLaw` | focused build; axiom audit | The deterministic law has the plan's ordinary expected utility. |
| same | `InformationStructure` | structure | adapt | `BayesianGame.InformationStructure` | focused build | A joint finite law over types and private signals with the right marginal. |
| same | `InformationStructure.inducedBayesianGame` | definition | adapt | same name | focused build; hostile probe | Player `i` sees only `(own type, own signal)`. |
| same | `InformationStructure.outcomeLaw` | definition | adapt | same name | focused build; hostile probe | Pushes the information law through the induced plan. |
| same | `InformationStructure.outcomeLaw_bayesPlausible` | theorem | adapt | `outcomeLaw_isBayesPlausible` | focused build | Exact type-marginal preservation. |
| same | `applyObedienceDeviation` | definition | adapt | `BayesianGame.applyObedienceDeviation` | source audit | Uses `Profile.update`; no direct `Function.update`. |
| same | `deviatingEU` | definition | adapt | `BayesianGame.deviatingValue` | focused build | Expected payoff under the obedience deviation. |
| same | `BayesCorrelatedEq` | definition | adapt | `BayesianGame.IsBayesCorrelatedEq` | focused build | Bayes plausibility plus obedience. |
| same | `deviatingEU_strategyRecommendationLaw` | theorem | adapt | `BayesianGame.deviatingValue_strategyRecommendationLaw` | focused build | An obedience rule becomes the corresponding contingent-plan deviation. |
| same | `BayesNash.strategyRecommendationLaw_bayesCorrelatedEq` | theorem | adapt | `BayesianGame.isBayesCorrelatedEq_strategyRecommendationLaw_of_isNash` | compiled-mechanism integration probe; axiom audit | Ordinary Nash induces a deterministic BCE without a second Bayesian equilibrium predicate. |
| same | `InformationStructure.recommendedEU_outcomeLaw` | theorem | adapt | `recommendedValue_outcomeLaw` | focused build | Expected-value commuting law. |
| same | `InformationStructure.deviatingEU_outcomeLaw` | theorem | adapt | `deviatingValue_outcomeLaw` | focused build | Deviation commuting law. |
| same | `InformationStructure.BayesNash.outcomeLaw_bayesCorrelatedEq` | theorem | adapt | `InformationStructure.isBayesCorrelatedEq_outcomeLaw_of_isNash` | nondegenerate private-signal probe; axiom audit | The frozen F5 transfer, stated using ordinary `IsNash`. |

The complete-information BCE/CE equivalence and information-design material
later in the pinned file remain S-CORR and mechanism-design recovery. F5 is the
finite recommendation/obedience substrate and the information-structure
outcome-law theorem.

Attribution: the predecessor's marginal and deviation-commuting calculations
are retained. The successor replaces the universal game hub, `PMF`, and the
second `BayesNash` predicate with `BayesianGame`, `FinDist`, `Profile.update`,
and ordinary `IsNash`.

Validation:

```text
lake build GameTheory.Core.BayesCorrelated GameTheory.Tests.BayesCorrelated
lake build GameTheory.Languages.BayesianMechanism GameTheory.Tests.BayesianMechanism
lake build
pwsh -NoProfile -File scripts/phase0-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
```

The private-signal probe uses a fair Boolean type, a signal that repeats that
type, and payoff one exactly when action matches type. Both states have
probability `1 / 2`. The matching plan is ordinary Nash and its outcome law is
Bayes-correlated. A second probe compiles the truthful mechanism from F6 and
feeds its Nash theorem directly into the deterministic recommendation-law
theorem.

The focused trust audit for both F5 transfer theorems and the integrated F6
consumer reports only `propext`, `Classical.choice`, and `Quot.sound`. The new
stable source contains no direct `Function.update`, source-level transport
token, placeholder, `native_decide`, or custom axiom.
