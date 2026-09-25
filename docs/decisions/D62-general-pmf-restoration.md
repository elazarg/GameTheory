# D62: general discrete PMF semantics

- **Status:** adopted
- **Date:** 2026-09-24; adopted 2026-09-25
- **Evidence:** [EXP-122–141](../ExperimentLog.md)
- **Design and acceptance gates:** [PMFRestorationDesign](../PMFRestorationDesign.md)

## Decision

Use ordinary Mathlib PMF for discrete game and protocol semantics. Finite
support belongs on the operations and theorems that need it, rather than on
every outcome law, strategy, deviation, or belief. Remove the parallel
`FinDist` operation algebra. A bundled finite-support witness needs a concrete
consumer that justifies it.

Real expected utility requires integration of the actual compared laws.
Bounded payoffs are one sufficient condition, not a field of every game.
Undefined expectations must neither become zero-valued payoffs nor remove
deviations from equilibrium tests. Standalone interim values require only
integration on the observed event; ex-ante comparisons require integration
of the whole deviation law.

Strict dominance does not by itself certify a defined incumbent payoff: on a
singleton action carrier it holds vacuously. Its expected-utility equilibrium
consequences therefore require incumbent integration explicitly (EXP-124).

Finite-average repeated equilibrium uses the law obtained by sampling a stage
uniformly and then sampling that stage's outcome. Its expected utility equals
the average of stage expectations, and its integration requirement concerns
exactly those stages. An optional outcome represents the empty horizon's zero
payoff. This preserves canonical approximate Nash without requiring defined
payoffs at unrelated profiles or introducing another equilibrium predicate
(EXP-134). Infinite discounted payoff retains the separate stage and series
requirements described below.

Stationary stochastic Bellman semantics uses the actual one-step law of joint
action and next state. Realized utility combines the stage payoff with the
discounted continuation value. This leaves the semantic predicate independent
of state finiteness or integration at unrelated action profiles; canonical Nash
supplies the actual comparison requirements. EXP-138 distinguishes an unused
divergent joint action from an undefined unilateral deviation. Finite-state
compactness belongs to the existence proof, and a guarded pure-play identity
recovers its scalar auxiliary formula.

Preserve probability-free signatures, typed information, recommendation-local
deviations, and the single equilibrium predicate. Use ordinary measures where
a discrete PMF cannot represent the relevant probability law, with
measurability assumptions local to the operation.

## Alternatives and rationale

1. **Direct PMF semantics.** Recovers the general discrete scope of v1 and
   reuses Mathlib/v1 mathematics. Explicit integration requirements expose the
   domain of payoff comparisons. Selected.
2. **Parallel finite and countable game hierarchies.** Duplicates forms,
   protocols, and equilibrium definitions. Rejected.
3. **An abstract probability carrier.** Introduces abstraction before a
   concrete consumer justifies it. D3's rejection still applies.

The [v1 inventory](../PMFRestorationV1Inventory.md) identifies general bounded
expectation, convergence, conditioning, and finite-index product arguments.
The [impact survey](../PMFRestorationImpactSurvey.md) establishes that the
finite-support default restricts public semantic types throughout the library;
it is not merely an executable representation choice.

## Evidence that determines the boundaries

- EXP-122–124 exhibit infinite-support laws and a divergent nonnegative payoff
  whose real `tsum` is zero by totalization. This requires guarded real
  expectation and rules out silently reusing the finite-law evaluator.
- EXP-125 and EXP-128 separate finite strategic choices from stochastic
  outcomes: backward construction and finite-strategy Nash can use infinite
  outcome support and unbounded integrable payoffs. Their integration premises
  concern actual play laws.
- EXP-126 rules out one PMF realizing uniform marginals on `Fin (n + 1)` at
  every natural-number site, even without independence. A bounded execution
  horizon therefore does not justify arbitrary PMF predrawing of policies.
  EXP-127 uses an ordinary product measure for forward policy realization;
  the discrete sampling construction retains its finite-site premises.
- EXP-136 uses target-local finite marginals to read arbitrary independent
  policy measures behaviorally, under countable measurable local choices.
  Infinitely many sites can be reachable within two rounds. A nonatomic law
  with correlated policy coordinates preserves every finite prefix despite
  having no PMF representation and no global finite site cover.
- EXP-135 separates probability-free knowledge on arbitrary Setoid cells from
  PMF scalar posteriors. Exact and quantitative agreement need no global full
  support or finite carriers. Null-public exact agreement follows from the
  zero scalar posterior convention; knowledge-to-positive-belief implications
  still require positive cell mass where evaluated.
- EXP-130 separates a defined local interim value from a divergent ex-ante
  payoff. Finite type spaces are not necessary for the general interim
  comparison theorem when every whole-plan deviation has integrable utility.
- EXP-131 refutes unconditional arbitrary-mixture transfer: individually
  integrable, nonimproving source deviations can have a mixture with divergent
  negative payoff. The actual target-deviation integration requirement is
  therefore substantive, even when the source profile is Nash.
- EXP-132 refutes unconditional independent-to-correlated rationalizability
  inclusion for general PMFs. A strategy survives every independent-belief
  round but is eliminated by a mixed dominator in the first correlated round.
  Every conditional payoff row and column is integrable; their joint payoff
  law is not. The inclusion theorem needs joint-law integration, which finite
  strategy spaces derive from integration of pure play.
- EXP-133 separates integration within a stage from summability over time.
  Every stage on an exponentially growing action path has integrable geometric
  noise, but its half-discounted expected-payoff series diverges. Discounted
  values therefore require both actual stage integration and summability of
  the weighted expected-stage series. A single expectation over a random time
  is not an interchangeable definition: its absolute integration can impose
  a stronger requirement on realized payoffs.
- EXP-139 separates actual net-payoff integration from separate reward/payment
  integration, and message-weighted scores from unweighted utilities. A
  positive-probability message can have a defined score despite a divergent
  unweighted payoff. Undefined actual alternatives refute receiver and agent
  optimality. Posterior-law splitting works for infinite-support laws of
  beliefs, without finite state or message carriers.
- EXP-140 transports actual payoff integration along exact native/compiled
  MAID assignment-law equality. Infinite chance values require no finite value
  carrier or all-profile integration assumption on Nash equivalence. A defined
  incumbent with an undefined actual deviation is non-Nash in both forms.
- EXP-141 separates countability of a PMF's support from countability of all
  legal histories. Discrete history coordinates and measurable product
  projections suffice for the canonical Ionescu–Tulcea construction and its
  chronological marginals, even with real-valued legal actions. Separate
  path-coherence results retain their own measurable-event hypotheses.
- EXP-137 identifies numerical mixed ESS/NSS with defined fitness comparisons
  at every sufficiently small positive invasion share. On the full PMF mutant
  space, these actual comparisons force all-pair payoff integration: mutant
  diagonals and half-mixtures control every cross encounter. A resident beating
  every distinct mutant in the first-order test can still fail stability
  because a mutant's invasion fitness diverges.

The experiment log owns commands, measurements, and reproduction artifacts.
The [delivery ledger](../DeliveryLedger.md) owns implementation status.

## Acceptance and rejection criteria

P0–P4 require products and conditioning, canonical static and sequential
consumers with genuine infinite support, full-policy continuation comparisons,
finite-specialization preservation, and recovery of finite existence and
executable correctness. Whole-library validation is part of acceptance.

Reject hidden finiteness, undefined real payoff comparisons, omitted
deviations, unjustified history normalization, duplicate semantics, weakened
sequential consistency, or infinite-space existence inferred from finite
compactness. Preserve the finite-fuel counterexample and the distinction
between discrete outcomes and infinite-path measures.

## Consequences for other decisions

Supersede D2's finite-support semantic default and D3's restriction of countable
laws to an extension layer. Their finite-law implementation evidence remains
relevant to finite operations. Preserve D3's concrete-probability choice,
D11's measure boundary, and D12's dependency direction.

EXP-129 shows that canonical Mathlib map/filter imports already expose the old
simplex and polynomial proxy symbols. Semantic import checks therefore target
actual project Analysis and external fixed-point dependencies. Executable and
probability-free restrictions remain stronger. Audit raw weight conversion and
expectation arithmetic at explicitly named owners rather than banning PMF
from public semantic types.
