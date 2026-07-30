# D-EVOL: static evolutionary stability

Title: Static evolutionary stability and canonical Nash bridge
Family ID: D-EVOL
Pinned roots: `GameTheory/Concepts/Classes/EvolutionaryStability.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: working tree based on `ae8e3f1`
Canonical destination: `GameTheory.Evolutionary`
Domain contract / decision: D17, EXP-044
Owner: Wave 1 / evolutionary ownership
Status: complete
Last verified: 2026-07-30

The pinned family is entirely static: nine declarations over a real
two-argument payoff kernel. No population state, trajectory, replicator
equation, simplex invariant, or convergence theorem occurs in its scope.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `Concepts/Classes/EvolutionaryStability.lean` | `IsESS` | definition | adapt | `GameTheory.Evolutionary.IsESS` | EXP-044/D17; focused build | Separate stable domain definition; stores no game form, population law, or capability. |
| same | `IsNSS` | definition | adapt | `GameTheory.Evolutionary.IsNSS` | EXP-044/D17 | Neutral tie-break comparison over the same payoff kernel. |
| same | `IsESS.isNSS` | theorem | adapt | `GameTheory.Evolutionary.IsESS.isNSS` | focused build | Direct static implication. |
| same | `IsESS.nash_condition` | theorem | adapt | `GameTheory.Evolutionary.IsESS.nash_condition` | focused build | Exposes the first ESS clause without defining another Nash predicate. |
| same | `IsESS.stability` | theorem | adapt | `GameTheory.Evolutionary.IsESS.stability` | focused build | Exposes the nonvacuous distinct-mutant tie-break clause. |
| same | `isESS_of_strict_nash` | theorem | adapt | `GameTheory.Evolutionary.isESS_of_strict_nash` | focused build | Strict symmetric payoff condition implies ESS. |
| same | `IsESS.strict_against_other_ess` | theorem | adapt | `GameTheory.Evolutionary.IsESS.strict_against_other_ess` | focused build | Proved order-theoretically without dynamics or topology. |
| same | `symmetricEU` | definition | adapt | `GameTheory.Evolutionary.symmetricUtility`; `GameTheory.Evolutionary.symmetricForm` | D4/D17 | The old utility-only constructor becomes separate utility data over a canonical utility-free deterministic form. |
| same | `IsESS.isNash_symmetric` | theorem | adapt | `GameTheory.Evolutionary.IsESS.isNash_symmetric` | EXP-044/D17; axiom audit | Uses the sole public `IsNash`, `euPreference`, and canonical unilateral deviations. |

Attribution: the pinned family supplies the ESS/NSS definitions, elementary
proof plan, payoff orientation, and symmetric-Nash target. The successor
removes the old universal `KernelGame.ofEU` dependency while preserving the
mathematics through the canonical form/preference split.

Validation:

```text
lake build GameTheory.Evolutionary
lake build
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
```

The focused build completes in 1,722 jobs and the full build in 3,349. The
stable root has 119 nonblank lines, zero forbidden imports/source tokens, and
only the standard `propext`, `Classical.choice`, and `Quot.sound` axiom
profile. All positive, negative, and reverse-dependency probes pass. EXP-044's
hostile Boolean witness remains experimental and proves the ESS stability
clause is not vacuous.
