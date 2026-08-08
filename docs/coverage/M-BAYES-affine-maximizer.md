# M-BAYES: affine maximizers

Title: Positive-weight affine maximizers and Clarke payments
Family ID: M-BAYES
Pinned roots: `GameTheory/Mechanism/Bayesian/AffineMaximizer.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `1563bb7`
Canonical destination: `GameTheory.Mechanism.AffineMaximizer`, producing
`GameTheory.Mechanism.QuasiLinearMechanism`
Domain contract / decision: D4, D5, D8, D9; EXP-066/D33
Owner: Post-architecture Wave 2 / mature Bayesian-mechanism recovery
Status: complete for the pinned affine-maximizer file; 13/13 declarations reviewed
Last verified: 2026-08-08

The successor bundles only the type, valuation, weight, and bias data shared by
affine-maximizer consumers.  Finiteness is requested by objective aggregation
and maximization operations, not stored in the data.  The generated mechanism
uses D33's canonical quasilinear owner, and its DSIC theorem therefore targets
the existing Bayesian direct-mechanism incentive predicate.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Mechanism/Bayesian/AffineMaximizer.lean` | `affineObjective` | def | adapt | `AffineMaximizer.objective` | hostile unequal-weight objectives | Aggregation requests finite players only at the operation. |
| same | `affineChoice` | def | adapt | `AffineMaximizer.choose` | both hostile report profiles select their strict maximizer | Alternative finiteness and nonemptiness remain operation-local. |
| same | `affineChoice_max` | theorem | adapt | `AffineMaximizer.objective_le_choose` | focused build; strict hostile branches | Same finite maximizer certificate. |
| same | `othersWelfare` | def | adapt | `AffineMaximizer.othersObjective` | exact hostile pivot calculation | Keeps the alternative bias with the other-player objective. |
| same | `pivotWelfare` | def | adapt | `AffineMaximizer.pivotObjective` | hostile pivot value `1/2` | Finite alternative supremum remains local. |
| same | `affineMaximizer` | def | adapt | `AffineMaximizer.toQuasiLinearMechanism` | report-sensitive allocation and payment | Produces the D33 owner instead of a parallel mechanism type. |
| same | `othersWelfare_independentOfCoordinate` | theorem | adapt | `AffineMaximizer.othersObjective_update` | canonical-update proof | The obsolete generic coordinate-independence wrapper becomes the exact update law consumed here. |
| same | `othersWelfare_eq_of_agree` | theorem | adapt | `AffineMaximizer.othersObjective_eq_of_agree` | focused build | Retains extensional independence under agreement off the named player. |
| same | `affineMaximizer_wUtil` | theorem | adapt | `AffineMaximizer.weight_mul_trueUtility` | strict hostile utility values | Strengthened to arbitrary fixed opponent reports required by canonical IC. |
| same | `affineMaximizer_payment_nonneg` | theorem | adapt | `AffineMaximizer.payment_nonneg` | positive hostile payment and generic specialization | Clarke externalities yield no subsidy for each positive-weight player. |
| same | `affineMaximizer_isDSIC` | theorem | adapt | `AffineMaximizer.toQuasiLinearMechanism_isDSIC` | hostile DSIC and axiom audit | Proves the stronger canonical fixed-opponent-report inequality without another equilibrium predicate. |
| same | `vcg` | def | adapt | `AffineMaximizer.vcgMechanism` | focused build | Unit weights and zero bias transparently specialize the same constructor. |
| same | `vcg_isDSIC` | theorem | adapt | `AffineMaximizer.vcgMechanism_isDSIC` | hostile value specialization | Reuses the affine DSIC theorem; distinct from the more general Groves-offset `VCGSetup`. |

## Validation

```text
lake build GameTheory.Mechanism.AffineMaximizer GameTheory.Tests.AffineMaximizer GameTheory.Mechanism
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected -SkipReachability
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
lake build
```

The hostile Boolean mechanism has two players and alternatives, weights two
and one, and a `1/2` bias for the true alternative.  Changing the first report
moves the unique objective maximizer and changes its payment from `1/4` to
zero.  For the two possible true types, truthful utilities are respectively
`7/4` and `2`, while the opposite reports give `0` and `-1/4`.  The fixture
specializes DSIC, weak monotonicity, payment nonnegativity, and the unit-weight
VCG corollary.

The focused root build completes warning-free in 1,751 jobs and the full build
in 3,455.  Phase 2 structural and exact coverage audits both report
`VERIFIED=1`; exact accounting rises to 1,931 declarations.  Sampled flagship
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.  The opt-in
Mechanism root exposes the new owner and theorem, while the main umbrella
continues to reject them.
