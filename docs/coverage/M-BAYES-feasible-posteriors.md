# M-BAYES: feasible posterior laws

Title: Single-agent and joint finite posterior feasibility
Family ID: M-BAYES
Pinned roots: `GameTheory/Mechanism/Bayesian/FeasiblePosteriors.lean` and
`GameTheory/Mechanism/Bayesian/JointFeasiblePosteriors.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `3bb2e2b`
Canonical destination: `GameTheory.PosteriorLaw` and
`GameTheory.JointPosteriorLaw`, opt-in through `GameTheory.Mechanism`
Domain contract / decision: D2, D9; validated finite information-design owner
Owner: Post-architecture Wave 2 / mature Bayesian-mechanism recovery
Status: complete for both pinned files; 19/19 declarations reviewed
Last verified: 2026-08-08

The successor replaces both PMF layers by the canonical `FinDist`: a posterior
law is `FinDist (FinDist State)`, its mean is monadic bind, and its coupling is
bind followed by map. Carrier finiteness is never stored. Joint feasibility
retains v1's honest one-way theorem—feasibility implies marginal Bayes
plausibility—and adds common full revelation as a nontrivial feasible witness.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Mechanism/Bayesian/FeasiblePosteriors.lean` | `meanPosterior` | def | adapt | `PosteriorLaw.mean` | focused build | The mean is `law.bind id` at the canonical finite-support layer. |
| same | `meanPosterior_apply` | theorem | adapt | `PosteriorLaw.prob_mean` | focused build | Real point mass is expressed as finite-support expectation rather than exposed `ENNReal` tsum. |
| same | `IsBayesPlausible` | def | adapt | `PosteriorLaw.IsBayesPlausible` | full-revelation hostile law | Scoped naming avoids collision with the canonical Bayesian-game plausibility predicate. |
| same | `posteriorCoupling` | def | adapt | `PosteriorLaw.coupling` | two diagonal hostile events | Draw a posterior, then a state from it. |
| same | `posteriorCoupling_apply` | theorem | adapt | `PosteriorLaw.prob_coupling` | both diagonal events have probability `1/2` | Uses the public real-mass interface. |
| same | `posteriorCoupling_snd` | theorem | adapt | `PosteriorLaw.map_snd_coupling` | hostile marginal theorem | The belief marginal is the original posterior law. |
| same | `posteriorCoupling_fst` | theorem | adapt | `PosteriorLaw.map_fst_coupling` | focused build | The state marginal is the mean posterior. |
| same | `isBayesPlausible_iff_coupling_fst` | theorem | adapt | `PosteriorLaw.isBayesPlausible_iff_map_fst_coupling` | hostile prior marginal | Canonical-coupling feasibility is exactly the mean condition. |
| same | `isBayesPlausible_uninformative` | theorem | port | `PosteriorLaw.isBayesPlausible_uninformative` | focused build | Point mass at the prior. |
| same | `isBayesPlausible_fullRevelation` | theorem | port | `PosteriorLaw.isBayesPlausible_fullRevelation` | two distinct supported beliefs | Prior pushed to state point masses. |
| same | `isBayesPlausible_bind` | theorem | adapt | `PosteriorLaw.isBayesPlausible_bind` | focused build | Randomizing among laws with the same mean preserves plausibility. |
| same | `isBayesPlausible_bind_pointwise` | theorem | adapt | `PosteriorLaw.isBayesPlausible_bind_pointwise` | focused build | Sequential splitting preserves the prior. |
| `GameTheory/Mechanism/Bayesian/JointFeasiblePosteriors.lean` | `agentMarginal` | def | adapt | `JointPosteriorLaw.agentMarginal` | two-player hostile law | Pushforward to one player's posterior. |
| same | `posteriorCoupling_pure` | theorem | adapt | `PosteriorLaw.coupling_pure` | focused build | Canonical coupling of one fixed belief. |
| same | `IsJointBayesPlausible` | def | adapt | `JointPosteriorLaw.IsBayesPlausible` | both hostile player marginals | Each marginal has the common prior as mean. |
| same | `IsJointFeasible` | def | adapt | `JointPosteriorLaw.IsFeasible` | common full-revelation coupling | State, profile, and per-player coupling marginals are explicit. |
| same | `IsJointFeasible.bayesPlausible_agentMarginal` | theorem | adapt | `JointPosteriorLaw.IsFeasible.agentMarginal_isBayesPlausible` | two-player hostile specialization | Necessary marginal condition only; no converse is claimed. |
| same | `IsJointFeasible.isJointBayesPlausible` | theorem | adapt | `JointPosteriorLaw.IsFeasible.isBayesPlausible` | focused build | Packages the per-player theorem. |
| same | `isJointFeasible_uninformative` | theorem | adapt | `JointPosteriorLaw.isFeasible_uninformative` | focused build | Retains v1's non-vacuity witness; the successor also proves `isFeasible_fullRevelation`. |

## Validation

```text
lake build GameTheory.Mechanism.FeasiblePosteriors GameTheory.Mechanism.JointFeasiblePosteriors GameTheory.Tests.FeasiblePosteriors GameTheory.Tests.JointFeasiblePosteriors GameTheory.Mechanism
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected -SkipReachability
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
```

The single-agent hostile law fully reveals a fair Boolean state. It supports
the two distinct point-mass beliefs and its canonical coupling assigns
probability `1/2` to each matching state/belief pair. The joint hostile law has
two players who both learn that state; it supports two belief profiles, is
realized by one common-state coupling, and has Bayes-plausible marginals for
both players. These witnesses rule out constant posterior laws and independent
per-player fake couplings.
