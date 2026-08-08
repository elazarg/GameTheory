# M-BAYES: truthful mechanism welfare and participation

Title: Truthful welfare and explicit ex-post participation
Family ID: M-BAYES
Pinned roots: the welfare/participation tail of
`GameTheory/Mechanism/Bayesian/MechanismDesign.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `40d7a4e`
Canonical destination: `GameTheory.Languages.BayesianMechanism`, extended by
`GameTheory.Mechanism.BayesianWelfare`
Domain contract / decision: D4, D5, D8; validated F6 Bayesian compiler
Owner: Post-architecture Wave 2 / mature Bayesian-mechanism recovery
Status: complete for the four welfare/participation declarations; together
with F6, the pinned mechanism-design file is 15/15 reviewed
Last verified: 2026-08-08

The successor evaluates welfare and participation at the mechanism's explicit
truthful report profile while retaining true types separately. Outside options
remain visible parameters. The leaf adds no mechanism structure, equilibrium
predicate, prior, or stored finite capability.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Mechanism/Bayesian/MechanismDesign.lean` | `Mechanism.socialWelfare` | def | adapt | `BayesianMechanism.truthfulSocialWelfare` | unequal two-player hostile utilities | The aggregate is explicitly truthful and requests player finiteness only at the operation. |
| same | `Mechanism.IsIndividuallyRational` | def | adapt | `BayesianMechanism.IsExPostIndividuallyRational` | accepted and rejected nonzero outside options | The name records the predecessor's ex-post quantification over every realized type profile. |
| same | `Mechanism.IsNonNegative` | def | adapt | `BayesianMechanism.IsExPostNonnegative` | positive hostile truthful utilities | Zero normalization remains a transparent specialization, not the only participation surface. |
| same | `Mechanism.IsNonNegative_iff` | theorem | adapt | `BayesianMechanism.isExPostNonnegative_iff` | focused build | Definitional equivalence to the explicit zero outside option. |

## Validation

```text
lake build GameTheory.Mechanism.BayesianWelfare GameTheory.Tests.BayesianWelfare GameTheory.Mechanism
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected -SkipReachability
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
```

The hostile Boolean-player mechanism encodes truth by flipping each Boolean
type, rather than relying on identity reports. Truthful utilities are unequal
(`2` and `1`) and sum to `3`. An outside-option profile `(3/2, 1/2)` is
accepted, while raising the second option to `3/2` refutes ex-post individual
rationality. This prevents the result from passing through zero-normalized or
constant-utility shortcuts.
