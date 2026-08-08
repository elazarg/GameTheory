# M-BAYES: quasilinear weak monotonicity

Title: Quasilinear direct mechanisms and weak monotonicity
Family ID: M-BAYES
Pinned roots: `GameTheory/Mechanism/Bayesian/Monotonicity.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `c1e3781`
Canonical destination: `GameTheory.Mechanism.QuasiLinearMechanism`, opt-in
through `GameTheory.Mechanism`
Domain contract / decision: D4, D5, D8, D9; EXP-066/D33
Owner: Post-architecture Wave 2 / mature Bayesian-mechanism recovery
Status: complete for the pinned monotonicity file; 5/5 declarations reviewed
Last verified: 2026-08-08

The successor keeps the allocation/payment decomposition needed by the
mathematics but defines DSIC transparently through the canonical Bayesian
direct-mechanism incentive predicate.  Base data stores no finiteness, prior,
probability law, equilibrium, or Groves certificate.  The theorem uses only
canonical `Profile.update`; the existing VCG setup is a downstream consumer.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Mechanism/Bayesian/Monotonicity.lean` | `SCFWithPayments` | structure | adapt | `GameTheory.Mechanism.QuasiLinearMechanism` | EXP-066/D33; focused build | Independent player, type, and alternative universes; no stored capabilities. |
| same | `SCFWithPayments.utility` | def | adapt | `QuasiLinearMechanism.trueUtility` | strict hostile utility comparison | Retains true own type separately from the report profile. |
| same | `SCFWithPayments.IsDSIC` | def | adapt | `QuasiLinearMechanism.IsDSIC` | canonical-IC bridge; hostile negative control | The familiar name abbreviates `BayesianMechanism.IsIncentiveCompatible`; it does not create another solution concept. |
| same | `SCFWithPayments.IsWeaklyMonotone` | def | adapt | `QuasiLinearMechanism.IsWeaklyMonotone` | strict hostile witness | Raw `Function.update` is replaced by the sole canonical profile update. |
| same | `SCFWithPayments.weaklyMonotone_of_dsic` | theorem | adapt | `QuasiLinearMechanism.weaklyMonotone_of_isDSIC` | focused build; axiom audit | The two opposite canonical incentive constraints cancel nonconstant report-sensitive payments. |

## Validation

```text
lake build GameTheory.Mechanism.QuasiLinear GameTheory.Tests.QuasiLinearMechanism GameTheory.Mechanism.VCG GameTheory.Mechanism
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected -SkipReachability
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
lake build
```

The hostile Boolean mechanism has two players, types, and alternatives.  The
first player's report changes the chosen alternative and payment, and its false
type loses strictly from `2` to `-1` by deviating.  Weak monotonicity is strict.
Reversing allocation while retaining the same nonconstant valuation and
payment data creates a profitable deviation and refutes DSIC.  This closes the
pinned monotonicity file without claiming affine-maximizer or Myerson coverage.
