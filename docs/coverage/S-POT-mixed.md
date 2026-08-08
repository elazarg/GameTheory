# S-POT: mixed exact-potential extension

Title: Canonical finite-law extension of exact potentials
Family ID: S-POT
Pinned root: `GameTheory/Concepts/Potential/MixedPotential.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `dd4960b`
Canonical destination: `GameTheory.Core.MixedPotential`
Domain contract / decision: D4-D5, D10
Owner: Wave 2 / potential and learning
Status: partial; exact-potential core recovered, weighted-potential rows deferred
Last verified: 2026-08-09

The successor keeps the reusable mathematical heart of the predecessor: a
pure-profile potential extends by expectation under the canonical independent
`FinDist` law, and exact utility/potential differences survive arbitrary mixed
unilateral changes.  It does not reproduce the predecessor's PMF-product
helper or its synthetic identical-interest `KernelGame`; those existed to
transport comparisons between parallel game evaluators that the greenfield
`UtilityGame`/mixed-form design no longer has.  Weighted potential statements
remain deferred until a weighted potential definition earns a native owner.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Potential/MixedPotential.lean` | `mixedPotential` | def | adapt | `GameTheory.UtilityGame.mixedPotential` | focused Core/test build | Expectation under `FinDist.pi`; no PMF wrapper. |
| same | `expect_pmfPi_update_pure` | theorem | subsumed | `GameTheory.GameForm.pi_map_recommendation` plus `FinDist.expect_map` | mixed pure-difference proof | The general canonical product/pushforward law is stronger than the potential-specific helper. |
| same | `mixedPotential_update` | theorem | adapt | `GameTheory.UtilityGame.mixedPotential_update` | focused Core/test build | Affinity follows from the canonical `pi_update_mixed` law. |
| same | `IsExactPotential.mixedExtension_pure_diff` | theorem | adapt | `GameTheory.UtilityGame.IsExactPotential.mixed_pure_diff` | fair-coin coordination witness | Removes finite strategy/outcome assumptions. |
| same | `IsExactPotential.mixedExtension_isExactPotential` | theorem | adapt | `GameTheory.UtilityGame.IsExactPotential.mixed` | focused Core/test build; axiom audit | Proves arbitrary randomized-deviation exactness through the sole mixed form. |
| same | `IsWeightedExactPotential.mixedExtension_pure_diff` | theorem | deferred | S-POT weighted-potential gate | ownership classification | No weighted-potential definition has yet earned a native owner. |
| same | `IsWeightedExactPotential.mixedExtension_update_diff` | theorem | deferred | S-POT weighted-potential gate | ownership classification | Depends on the same missing positive-weight semantics. |
| same | `finitePotentialTeamGame` | def | retired | direct `UtilityGame.mixedPotential` semantics | design comparison | The synthetic comparison game is unnecessary when mixed play and expected utility are canonical. |
| same | `finitePotentialTeamGame_Strategy` | theorem | subsumed | retired constructor | design comparison | Projection fact for retired compatibility machinery. |
| same | `finitePotentialTeamGame_utility` | theorem | subsumed | retired constructor | design comparison | Projection fact for retired compatibility machinery. |
| same | `finitePotentialTeamGame_outcomeKernel` | theorem | subsumed | retired constructor | design comparison | The greenfield form already owns one outcome law. |
| same | `finitePotentialTeamGame_isTeamGame` | theorem | subsumed | `GameTheory.IsTeamGame.isExactPotential` | existing Core theorem | Identical interests directly supply an exact potential at any form. |
| same | `finitePotentialTeamGame_eu` | theorem | subsumed | `GameTheory.expectedUtility_pure` | existing Core theorem | No synthetic evaluator is required. |
| same | `finitePotentialTeamGame_mixedExtension_eu` | theorem | subsumed | `GameTheory.UtilityGame.mixedPotential` | definitional successor semantics | Mixed potential is already the required expectation. |
| same | `finitePotentialTeamGame_mixedExtension_eu_self` | theorem | subsumed | `GameTheory.UtilityGame.mixedPotential` | definitional successor semantics | The duplicate self-typed wrapper disappears with the retired constructor. |
| same | `finitePotentialTeamGame_isExactPotential` | theorem | subsumed | `GameTheory.IsTeamGame.isExactPotential` | existing Core theorem | Team exactness is form-generic. |
| same | `IsWeightedExactPotential.mixedExtension_le_iff_finitePotentialTeamGame` | theorem | deferred | S-POT weighted-potential gate | ownership classification | Direct weighted comparison will replace the retired team-game transport if the gate passes. |
| same | `IsWeightedExactPotential.mixedExtension_isBestResponse_iff_finitePotentialTeamGame` | theorem | deferred | S-POT weighted-potential gate | ownership classification | Best response must remain the canonical `IsBestResponse`. |
| same | `IsExactPotential.mixedExtension_le_iff_finitePotentialTeamGame` | theorem | subsumed | `GameTheory.UtilityGame.IsExactPotential.mixed_update_diff` | direct difference identity | Comparison equivalence is immediate from equality of utility and potential differences; no surrogate game is needed. |
| same | `IsExactPotential.mixedExtension_isBestResponse_iff_finitePotentialTeamGame` | theorem | subsumed | `GameTheory.UtilityGame.IsExactPotential.mixed` | canonical exact-potential mixed form | Consumers reason directly with canonical mixed best responses. |
| same | `IsTeamGame.mixedExtension` | theorem | subsumed | `GameTheory.IsTeamGame` | definition inspection | Team-game status depends only on the utility function, which the mixed form does not replace. |
| same | `IsTeamGame.mixedExtension_isExactPotential` | theorem | subsumed | `GameTheory.IsTeamGame.isExactPotential` at `G.form.mixed` | existing Core theorem | The form-generic theorem specializes transparently. |

Attribution: the pinned file supplies the expected-potential construction and
the proof idea that pointwise exact-potential differences can be integrated.
The successor reuses that mathematics over `FinDist.pi`, factors expectation
subtraction into the general probability layer, and avoids the PMF-product and
synthetic-team-game transport apparatus.

Validation:

```text
lake build GameTheory.Core.MixedPotential GameTheory.Tests.MixedPotential GameTheory.Core
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```

The hostile fixture has two players and actions, a nonconstant coordination
potential, and one fair mixed coordinate.  Its mixed potential is exactly
`1/2`, while the coordinated pure profile has potential `1`; the generic pure
and randomized difference theorems therefore cannot pass through a constant
potential or payoff.
