# D-LEARN: fictitious-play trajectory core

Title: Canonical finite-support fictitious-play state and recurrence
Family ID: D-LEARN
Pinned root: `GameTheory/Concepts/Learning/FictitiousPlay.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `bb4a55b`
Canonical destination: `GameTheory.Core.FictitiousPlay`; convergence in `GameTheory.Analysis.Learning`
Domain contract / decision: D4-D5, D10, D21
Owner: Wave 2 / learning
Status: complete; topology-free trajectory and analytic limit package recovered
Last verified: 2026-08-09

The predecessor's structural fictitious-play layer mixed finite-horizon
probability with pointwise limit arguments over `PMF`.  The successor splits at
the actual dependency seam.  Core owns empirical `FinDist` marginals, their
running-average law, and a fictitious-play predicate that is definitionally an
obligation in the canonical mixed-game `IsBestResponse` vocabulary.  The two
limit theorems live in the opt-in Analysis consumer, backed by the shared
finite-law convergence leaf; they are neither weakened into finite
combinatorics nor duplicated over another law type.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Learning/FictitiousPlay.lean` | `empiricalMarginal` | def | adapt | `GameTheory.UtilityGame.empiricalMarginal` | focused Core/test build | Replaces `PMF.uniformOfFintype.bind pure` by the canonical `FinDist.uniformFin.map`. |
| same | `empiricalMarginal_apply_toReal` | theorem | adapt | `GameTheory.UtilityGame.empiricalMarginal_prob` | focused Core/test build; half-mass witness | `FinDist.prob` is already real-valued, so no representation coercion remains. |
| same | `empiricalMarginal_apply_toReal_range` | theorem | subsumed | `GameTheory.UtilityGame.empiricalMarginal_prob` | exact `Fin T` count plus hostile `T = 2` specialization | The range formulation exposed predecessor implementation detail rather than a second mathematical fact. |
| same | `empiricalMarginal_succ_apply_toReal` | theorem | subsumed | `GameTheory.UtilityGame.empiricalMarginal_succ_expect` | nonconstant three-round witness | The expectation recurrence strictly generalizes the pointwise statement by choosing an indicator observable. |
| same | `empiricalMarginal_succ_expect` | theorem | adapt | `GameTheory.UtilityGame.empiricalMarginal_succ_expect` | focused build; `false,true,false` gives `1/3` | Uses unconditional finite-support expectation and stores no carrier finiteness. |
| same | `belief` | def | adapt | `GameTheory.UtilityGame.empiricalBelief` | focused Core/test build | A belief is the ordinary profile of canonical mixed strategies. |
| same | `IsFictitiousPlay` | def | adapt | `GameTheory.UtilityGame.IsFictitiousPlay` | constant coordination history witness | Reuses `IsBestResponse G.form.mixed (euPreference G.utility)` instead of a parallel payoff comparison. |
| same | `frequently_play_eq_of_belief_converges` | theorem | adapt | `GameTheory.UtilityGame.frequently_play_eq_of_empiricalMarginal_converges` | focused Analysis build; standard axiom audit | Uses real-valued `FinDist.prob`; positive limiting support still forces infinitely many plays. |
| same | `isFictitiousPlay_limit_isNash` | theorem | adapt | `GameTheory.UtilityGame.IsFictitiousPlay.limit_isNash` | focused Analysis/test build | Product/expectation continuity is factored through `Analysis.FiniteLaw`; the target is the sole canonical mixed `IsNash`. |

Attribution: the pinned file supplies the empirical-marginal construction,
running-average identities, best-response recurrence, and convergence proof
plan.  The successor keeps those mathematical roles while replacing `PMF`,
raw `Function.update`, and the predecessor's separate mixed evaluator with the
already validated `FinDist`, `Profile.update`, mixed extension, and response
APIs.

Validation:

```text
lake build GameTheory.Core.FictitiousPlay GameTheory.Tests.FictitiousPlay GameTheory.Analysis.FictitiousPlayTest GameTheory.Core
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```

The hostile consumer separates two risks: an alternating path checks a
non-point-mass half/third empirical law and the successor recurrence, while a
constant coordination path proves `IsFictitiousPlay` by transporting the
ordinary pure Nash witness through `IsNash.purify` and
`isNash_iff_isBestResponse`.  Thus neither the probability layer nor the
best-response predicate can pass merely because the fixture is constant.  The
Analysis consumer then proves coordinatewise belief convergence and exercises
the public limit-to-Nash theorem without introducing a second law or
equilibrium predicate.
