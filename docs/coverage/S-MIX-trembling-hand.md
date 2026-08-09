# S-MIX: trembling-hand perfection

Title: Canonical perturbations and trembling-hand perfection
Family ID: S-MIX
Pinned roots: `GameTheory/Concepts/Mixed/TremblingHand.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `c201670`
Canonical destination: `GameTheory.Core.TremblingHand` and `GameTheory.Analysis.TremblingHand`
Domain contract / decision: D5, D12, EXP-071, D38
Owner: Wave 1 / equilibrium refinement
Status: partial; all 26 declarations classified, the 20-row perturbation/perfection spine is promoted, and 6 alternative limit predicates are deferred
Last verified: 2026-08-09

The successor separates topology-free perturbation data and restricted
equilibrium from analytic convergence.  Perturbed equilibrium reuses the sole
`IsEquilibrium` predicate through a constrained unilateral deviation scheme.
The flagship theorem proves every full-support mixed Nash profile is
trembling-hand perfect; fair Matching Pennies is the nondegenerate witness.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Mixed/TremblingHand.lean` | `MixedProfile` | abbrev | subsumed | `Profile F.sig.mixed` | canonical mixed form | No parallel mixed-profile carrier. |
| same | `Perturbation` | abbrev | adapt | `GameForm.Perturbation` | focused Core build | Uses real `FinDist.prob` bounds; no PMF/ENNReal leak. |
| same | `FullyMixed` | def | subsumed | `∀ i, (profile i).FullSupport` | D2 finite-law owner | Full support remains a property of each canonical law. |
| same | `ConvergesPointwise` | def | adapt | `Analysis.MixedProfileConvergesPointwise` | focused Analysis build | Topology appears only in Analysis. |
| same | `StrategyRespectsPerturbation` | def | adapt | `GameForm.StrategyRespectsPerturbation` | focused Core build | Coordinatewise real lower bound. |
| same | `RespectsPerturbation` | def | adapt | `GameForm.RespectsPerturbation` | focused Core build | Canonical signature-bound profile. |
| same | `Perturbation.Positive` | def | adapt | `GameForm.Perturbation.Positive` | focused Core build | Strict real positivity is clearer than nonzero ENNReal. |
| same | `Perturbation.ConvergesToZero` | def | adapt | `Analysis.PerturbationConvergesToZero` | focused Analysis build | One-way topology boundary. |
| same | `FullyMixed.apply` | theorem | subsumed | `FinDist.FullSupport.apply` | existing finite-law theorem | The coordinate law owns support membership. |
| same | `ConvergesPointwise.apply` | theorem | subsumed | `Analysis.MixedProfileConvergesPointwise` | definition builds | The successor predicate is already pointwise in the player. |
| same | `RespectsPerturbation.apply` | theorem | adapt | `GameForm.RespectsPerturbation.apply` | focused Core build | Named projection retained. |
| same | `Perturbation.Positive.fullyMixed_of_respects` | theorem | adapt | `GameForm.Perturbation.Positive.fullSupport_of_respects` | focused Core build | Produces canonical `FinDist.FullSupport` for each player. |
| same | `IsLimitOfFullyMixedEqFor` | def | deferred | S-MIX alternative-limit BFS gate | D38 continuation | Do not conflate the weaker fully-mixed-equilibrium limit with perturbation perfection. |
| same | `IsLimitOfFullyMixedNash` | def | deferred | S-MIX alternative-limit BFS gate | D38 continuation | Expected-utility specialization waits on the same gate. |
| same | `IsLimitOfFullyMixedεNash` | def | deferred | S-MIX alternative-limit BFS gate | D38 continuation | Vanishing approximate equilibrium is useful but distinct breadth. |
| same | `IsPerturbedEqFor` | def | adapt | `GameForm.IsPerturbedEq` | canonical deviation scheme | Preference-parametric and defined through `IsEquilibrium`. |
| same | `IsPerturbedEq` | def | adapt | `GameForm.IsPerturbedEq (euPreference utility)` | focused Core build | Familiar EU specialization needs no second definition. |
| same | `IsTremblingHandPerfectFor` | def | adapt | `GameForm.IsTremblingHandPerfect` | focused Analysis build | Preference-parametric analytic owner. |
| same | `IsTremblingHandPerfect` | def | adapt | `UtilityGame.IsTremblingHandPerfect` | focused Analysis build | Transparent expected-utility specialization. |
| same | `isLimitOfFullyMixedEqFor_iff` | theorem | deferred | S-MIX alternative-limit BFS gate | D38 continuation | Projection follows when the predicate is admitted. |
| same | `isLimitOfFullyMixedNash_iff` | theorem | deferred | S-MIX alternative-limit BFS gate | D38 continuation | Same bounded gate. |
| same | `isLimitOfFullyMixedεNash_iff` | theorem | deferred | S-MIX alternative-limit BFS gate | D38 continuation | Same bounded gate. |
| same | `isPerturbedEqFor_iff` | theorem | adapt | `GameForm.isPerturbedEq_iff` | focused Core build | Exposes the restricted unilateral replacement form. |
| same | `IsPerturbedEqFor.fullyMixed` | theorem | adapt | `GameForm.Perturbation.Positive.fullSupport_of_respects` | focused Core build | Uses the feasibility projection of the canonical predicate. |
| same | `isTremblingHandPerfectFor_iff` | theorem | adapt | `GameForm.isTremblingHandPerfect_iff` | focused Analysis build | Exact certificate presentation. |
| same | `isTremblingHandPerfect_iff` | theorem | adapt | `UtilityGame.isTremblingHandPerfect_iff` | focused Analysis build | Transparent EU-to-generic specialization. |

Attribution: the predecessor supplied the perturbation certificate shape and
pointwise convergence interface.  The successor retains that mathematics while
replacing PMF/ENNReal representation exposure, raw function updates, and a
parallel Nash-shaped definition with `FinDist`, `Profile.update`, and the
canonical deviation/equilibrium spine.

Validation:

```text
lake build GameTheory.Core.TremblingHand GameTheory.Analysis.TremblingHand GameTheory.Analysis.TremblingHandTest
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
lake build
git diff --check
```

The Matching Pennies fixture proves both actions have positive mass at the fair
profile, reuses its existing mixed-Nash certificate, and packages the resulting
trembling-hand theorem together with the machine-checked absence of any pure
Nash equilibrium.
