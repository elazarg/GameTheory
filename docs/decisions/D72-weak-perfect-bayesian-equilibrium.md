# D72: weak PBE composes terminal rationality and on-path Bayes consistency

- **Status:** adopted
- **Date:** 2026-10-28
- **Experiment IDs:** [EXP-165](../ExperimentLog.md)

## Question and competing designs

The library already has a behavioral assessment with history-supported
beliefs, terminal whole-policy sequential rationality, positive-mass Bayes
consistency, and analytic Kreps-Wilson consistency. Which combination should
receive the public weak perfect Bayesian equilibrium name?

1. Compose terminal sequential rationality and Bayes' rule at every
   positive-mass decision information site.
2. Reuse sequential equilibrium, requiring a common limit of fully mixed
   Bayes assessments even at unreached sites.
3. Require Bayes' rule in every proper subgame, including subgames that the
   equilibrium strategy never reaches.

The first is the adopted weak-PBE meaning. The other two strengthen off-path
belief restrictions and cannot be interchangeable spellings for it. There is
no unqualified `IsPerfectBayesianEquilibrium` name: a stronger PBE requires a
separate mathematical specification and consumer.

## Mathematical scope and references

Weak PBE uses sequential rationality at every decision information site,
including unreached sites. All comparisons replace the player's whole
continuation policy and retain the actual-law integration guards. Bayes' rule
is required only where the information site's reach mass is positive. At a
null site the belief must still be a PMF on precisely that information-history
fiber, and the prescribed continuation must be optimal under it.

This is the weak condition, not the stronger multistage observed-action PBE of
[Fudenberg and Tirole (1991), *Perfect Bayesian equilibrium and sequential
equilibrium*](https://doi.org/10.1016/0022-0531(91)90155-W). The distinction
between positive-reach consistency and stronger off-path restrictions is also
discussed in [Bonanno (2016), *Exploring the Gap between Perfect Bayesian
Equilibrium and Sequential Equilibrium*](https://doi.org/10.3390/g7040035).

## Representative slice and kill conditions

The hidden-bit control exits before a chance continuation. An off-path belief
concentrated on the false bit makes the prescribed false guess optimal, while
the actual continuation law makes another guess strictly better at its
proper-subgame root. Root exit remains optimal against every whole-policy
replacement. A successful control proves both the weak assessment and failure
of canonical proper-subgame perfection for its induced pure strategy.

Reject the composition if it needs a new evaluator or belief carrier, leaks
Analysis into Protocol, weakens whole-policy rationality, or cannot express
the separating control. Reject the proposed naming if the weak predicate
silently requires the stronger off-path consistency of either alternative.

## Public API and limitations

`Protocol.WeakPBE` owns `BehavioralAssessment.IsWeakPBE`, transparently composing
the existing predicates. `Languages.EFG.WeakPBE` is an explicit solution leaf;
EFG syntax imports no solution concepts. Analytic refinement and finite
existence stay in explicit `Analysis.Protocol` leaves.

The sequential-equilibrium implication preserves the existing finite
information-history-fiber premise of the limit-to-Bayes theorem. Finite-history
existence inherits decision recall, finite players, total legal fallback
policies and terminal-play certification from sequential existence. The weak
definition itself needs neither finite histories nor a tremble sequence.
The root-incentive consequence reuses the existing decision-recall
decomposition for utilities factoring through a finite observation carrier;
it does not assert an unrestricted infinite-utility theorem.

Bayesian Nash and Bayesian incentive compatibility retain their canonical
`IsNash` expressions, made searchable in the capability matrix. The separate
ex-post addition specializes Nash at every realized type profile, including
profiles of zero prior mass; its expectation bridge is ordinary theorem
delivery rather than evidence for this naming decision.

## Result

Accept the composition. EXP-165 proves a weak assessment whose prescribed
strategy fails the existing proper-subgame predicate: the guessing site has
zero root reach, yet the actual subgame values are `-1` and `-1/2`. Thus both
stronger alternatives would reject an assessment that the weak name must
admit. A nonconstant hidden-bit consumer verifies the sequential-equilibrium
bridge; separate controls reject an irrational continuation and a wrong belief
at a site of mass one. Finite existence also applies to a decision-recall
model that lacks perfect recall. No new evaluator, belief carrier, or analytic
dependency in Protocol was needed. Exact commands and structural verification
are recorded in EXP-165.
