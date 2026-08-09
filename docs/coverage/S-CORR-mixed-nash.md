# S-CORR: mixed Nash and correlated equilibrium

Title: Mixed Nash and correlated equilibrium
Family ID: S-CORR
Pinned roots: `GameTheory/Concepts/Correlation/CorrelatedNashMixed.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: working tree based on `6c80cea`
Canonical destination: `GameTheory.Core.Form`; `GameTheory.Core.Utility`;
`GameTheory.Core.Mixed`; `GameTheory.Core.CorrelatedDominance`
Domain contract / decision: D4-D5, D8-D10, D19, EXP-047
Owner: Wave 2 / correlation
Status: complete bounded file; 12/12 reviewed, no deferred rows
Last verified: 2026-08-09

The predecessor file coupled the mathematical bridge to countable PMFs,
bounded real utilities, and a `KernelGame`-local correlated-utility surface.
The successor works over exact finite laws. Its general theorem preserves the
complete outcome law and therefore needs neither a utility nor boundedness;
the expected-utility identities remain available independently for consumers
that need scalar calculations.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Correlation/CorrelatedNashMixed.lean` | `correlatedEu_pure` | theorem | subsumed | `GameTheory.GameForm.outcomeLaw_pure`; `GameTheory.expectedUtility_pure` | focused build (1,739 jobs) | The finite-law equality is preference-independent; expected utility is then a direct specialization. |
| same | `correlatedEu_eq_expect_eu_of_bounded` | theorem | subsumed | `GameTheory.expectedUtility_outcomeLaw` | focused build (1,739 jobs) | Exact finite support removes the predecessor's boundedness premise. |
| same | `correlatedEu_eq_expect_eu` | theorem | adapt | `GameTheory.expectedUtility_outcomeLaw` | focused build (1,739 jobs) | The canonical theorem is unconditional and does not need a stored finite outcome capability. |
| same | `correlatedEu_constantDeviationDistribution_eq_expect_update_of_bounded` | theorem | subsumed | `GameTheory.expectedUtility_outcomeLaw_map` | focused build (1,739 jobs) | Instantiate the generic profile map with the named constant coordinate response; no separate deviation-distribution API survives. |
| same | `correlatedEu_constantDeviationDistribution_eq_expect_update` | theorem | adapt | `GameTheory.expectedUtility_outcomeLaw_map` | focused build (1,739 jobs) | Same theorem chain, without boundedness or a parallel correlated-utility definition. |
| same | `correlatedEu_unilateralDeviationDistribution_eq_expect_update_of_bounded` | theorem | subsumed | `GameTheory.expectedUtility_outcomeLaw_map` | focused build (1,739 jobs) | Recommendation-dependent coordinate replacement is one profile map; finite expectation is unconditional. |
| same | `correlatedEu_unilateralDeviationDistribution_eq_expect_update` | theorem | adapt | `GameTheory.expectedUtility_outcomeLaw_map` | focused build (1,739 jobs) | The scalar identity is retained at the generic law layer. |
| same | `IsCorrelatedEq.conditional_obedience` | theorem | adapt | `GameTheory.IsCorrelatedEq.conditional_obedience` | relative-dominance hostile fixture; focused build | Canonical `FinDist.condOn` removes carrier finiteness and PMF mass plumbing. |
| same | `unilateralDeviationDistribution_pmfPi` | theorem | adapt | `GameTheory.GameForm.pi_map_recommendation` | focused build (1,739 jobs); axiom audit | Exact coordinate-map law over the canonical independent `FinDist.pi`; no countable PMF wrapper. |
| same | `mixed_nash_isCorrelatedEq_of_bounded` | theorem | subsumed | `GameTheory.IsNash.isCorrelatedEq_pi` | focused build (1,739 jobs); axiom audit | The successor is preference-parametric and hence strictly stronger than the bounded expected-utility theorem. |
| same | `mixed_nash_isCorrelatedEq` | theorem | adapt | `GameTheory.IsNash.isCorrelatedEq_pi`; `GameTheory.Examples.matchingPennies_fair_isCorrelatedEq` | focused build (1,739 jobs); axiom audit | General bridge plus the pinned language family's concrete Matching Pennies consumer. |
| same | `IsCorrelatedEq.support_avoids_dominated_relative` | theorem | adapt | `GameTheory.IsCorrelatedEq.support_avoids_strictlyDominatedOn` | relative-not-global hostile fixture; focused build | Uses the canonical product-set `StrictlyDominatesOn`, ready for later IESDS induction. |

Attribution: the pinned file supplies the independent-product deviation identity,
the mixed-Nash-to-CE proof plan, and the conditional-obedience and support
obligations. The successor reuses the mathematics while replacing PMF
boundedness plumbing with exact finite-law equalities and the sole canonical
equilibrium predicates.

The two formerly deferred rows now live in the focused
`Core.CorrelatedDominance` theorem leaf.  Its positive-mass recommendation
fixture and relative-not-global dominance counterexample ensure that neither
result has silently collapsed to unconditional obedience or unrestricted
dominance.

Validation:

```text
lake build GameTheory.Core.Form GameTheory.Core.Utility GameTheory.Core.Mixed GameTheory.Core.CheapTalkRandomization GameTheory.Examples.Classic
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected -SkipReachability
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
lake build
```

A temporary module importing `GameTheory.Examples.Classic` ran `#print axioms`
on both finite-law identities, the independent-coordinate law, the general
bridge, and the Matching Pennies consumer. Every declaration reported only
`propext`, `Classical.choice`, and `Quot.sound`.
The original mixed-bridge focused build completed in 1,739 jobs.  After the
conditional-obedience and dominated-support rows were recovered, the full
structural and coverage audits both reported `VERIFIED=1`, the sampled trust
profile remained `propext`, `Classical.choice`, and `Quot.sound`, and the
warning-clean default build completed all 3,534 jobs.
