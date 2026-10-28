# GameTheory and MathEconLib comparison

MathEconLib complements GameTheory most strongly in continuous-probability
game theory, analytic auction theory, and matching with contracts. GameTheory
has broader developed coverage of sequential, repeated, and stochastic games,
learning, and certified finite computation. Selective theorem recovery and
shared mathematical infrastructure offer more immediate value than merging
their semantic foundations.

## Scope and evidence

Review date: 28 October 2026. The source snapshots are:

- MathEconLib: [`58f602847d7f131994d32ca7a8cc1af35b7e2dbe`][mec-snapshot].
- GameTheory: `8ac0ef93e09f435e99163cbcc7201361674d66de`, with supported
  workflows and remainders taken from the [delivery ledger](DeliveryLedger.md),
  [capability matrix](CapabilityMatrix.md), and
  [delivery plan](PostArchitectureDeliveryPlan.md).

The comparison covers definitions, representative theorem statements, source
organization, tests, and verification tooling. MathEconLib has 129 library
source files and 170 Lean sources across the reviewed checkout. Those counts
describe the inspection scope, not mathematical completeness. Both snapshots
use Lean/Mathlib 4.35.0 and Apache-2.0 licensing.

The recommendations below are proposed follow-ups. They do not change
GameTheory delivery statuses or reserve work ahead of the active dependency
queue. This review introduces no new semantic API or architecture experiment.

Implementation follow-up: EXP-169/[D75](decisions/D75-single-parameter-envelope.md)
recovers the scalar DSIC envelope, payment uniqueness, monotone-allocation
implementability, and expected-payment chain on the existing GameTheory
mechanism. EXP-170/[D76](decisions/D76-interim-envelope-revenue.md) extends the
chain to interval-wide interim incentives and actual expected receipts for
independent discrete types, with a separate canonical supported-type BNE
bridge. The comparison below retains its original source snapshots.

## Coverage comparison

| Area | MathEconLib | GameTheory |
|---|---|---|
| Equilibrium foundations | Arbitrary states, deviation relations, and ordered rewards; equilibrium preservation and reflection maps. | Utility-free stochastic game forms, preferences over outcome laws, and local deviations lifted linearly to profile laws. |
| Continuous games | Probability-measure mixed strategies; mixed Nash existence for continuous real payoffs on nonempty compact metrizable action spaces with finitely many players. | Discrete PMFs on arbitrary carriers, including infinite support. General measurable games and infinite-action equilibrium existence remain separate work. |
| Bayesian games | Measurable strategies, conditional beliefs, and an almost-everywhere interim characterization on standard Borel spaces. | General discrete priors, whole-plan deviations, canonical BNE, ex-post equilibrium, and Protocol compilation. |
| Auctions and pricing | Envelope identities, payment uniqueness, symmetric-IPV revenue equivalence, order statistics, and posted-price optimization. | Groves/VCG, reserves, combinatorial allocation, exact knapsack mechanisms, and topology-free single-parameter algebra. Analytic envelope theory remains a named remainder. |
| Matching | Choice functions, substitutability, many-to-many contracts, fixed-point lattices, and completion-based existence. | Ordinal and responsive capacitated matching, deferred acceptance, proposer strategyproofness, and rural-hospitals results including exact underfilled cohorts under the stated strict-ranking assumptions. |
| Dynamic games and learning | No development comparable to GameTheory's sequential, repeated, stochastic, and regret-learning families was found in the reviewed tree. | Established families with individually documented existence, realization, monitoring, and infinite-path boundaries. |
| Certified computation | A computable classical deferred-acceptance development accompanies the mathematical matching theory. | Rational algorithms and correctness, exact Nash certificates, and optional machine-certified NP/PPAD classifications. |

MathEconLib evidence: [strategic existence][mec-existence],
[measurable interim equivalence][mec-interim],
[payment identities][mec-payment], [revenue equivalence][mec-revenue],
[contract fixed points][mec-contracts], [stable-outcome order][mec-order], and
[computable deferred acceptance][mec-da]. GameTheory's corresponding owners
and precise limits are indexed in the local ledger and capability matrix.

Matching illustrates why neither library dominates the other. MathEconLib's
contract model supports general choice behavior and many-to-many markets;
its stable-existence result under substitutability and set-form irrelevance
of rejected contracts requires no finite contract carrier. GameTheory's
responsive model is narrower but supplies specialized algorithmic incentive
and rural-hospitals conclusions. Generality of the market definition and
depth of a specialized theorem family are separate advantages.

## Semantic differences affecting reuse

### Equilibrium structure and information

MathEconLib's `EquilibriumProblem S I V` contains a deviation relation
`I → S → S → Prop` and rewards `I → S → V`. Its equilibrium predicate requires
each directly admitted alternative's reward to be at most the incumbent's.
`GameMorphism.transport` lifts target deviations to source deviations;
`GameComorphism.pullback` maps source deviations into target deviations.
These are useful, small transport interfaces. For partially ordered rewards,
the equilibrium inequality also excludes incomparable rewards; the source
explicitly distinguishes this from absence of strict improvement.
([Source][mec-equilibrium])

GameTheory's [deviation scheme](../GameTheory/Core/Deviation.lean) instead
restricts a deviation's input to its members' own recommendations and lifts
its action to profile laws by `bind`. These types enforce information
locality and law-linearity. MathEconLib's arbitrary relation does not itself
enforce either invariant. Replacing the canonical owner with that relation
would therefore require separate enforcement of properties currently
guaranteed by construction.

### Integrability and infinite expected utility

MathEconLib's `IsMixedNash` and measurable `IsBNE` require integrable incumbent
payoffs and quantify over unilateral deviations with integrable resulting
payoffs. The bare `mixedNashProblem.IsEquilibrium` and
`bneProblem.IsEquilibrium` omit the incumbent-integrability requirement.
Their integrals are total Lean operations, so a nonintegrable payoff has
integral zero. The economic predicates add the necessary incumbent guard.
([Mixed source][mec-mixed], [BNE source][mec-bne])

GameTheory's [expected-utility preference](../GameTheory/Core/ExpectedUtility.lean)
compares extended expectations. Defined positive and negative infinite values
remain comparable. A law whose positive and negative parts both have infinite
expectation fails its comparison; it does not disappear from the deviation
quantifier. Consequently, the two libraries' unbounded equilibrium concepts
need an explicit semantic bridge. Integrability of every actual compared law
provides a natural common domain; any transport must also match the strategies,
laws, and permitted deviations.

MathEconLib already has [integrability regressions][mec-integrability] covering
nonintegrable incumbents, constant-shift failures of raw integral equilibria,
and the distinction between guarded mixed equilibrium and the raw integral
extension. The difference above is a documented modeling choice, not an
unreported proof hole.

### Almost-everywhere and pointwise incentives

MathEconLib's measurable interim converse uses standard Borel type/action
spaces and one conull set on which every action's conditional payoff is
integrable. Its almost-everywhere conclusion compares every action
simultaneously. This is substantial measurable-selection mathematics, beyond
conditioning on positive-mass discrete types. ([Source][mec-interim])

Its quasilinear `IsBICOn` is pointwise on declared type/report sets relative to
selected conditional beliefs. At null types those beliefs contain extra data
not determined by the prior. The existing `IsBIC.isBNE` theorem states the
forward implication with joint measurability and incumbent integrability;
it does not identify pointwise BIC with almost-everywhere BNE.
([Source][mec-bic])

### The scope of analytic auction results

The payment sufficiency result rules out deviations to actions selected for
other types. It does not by itself cover every original action outside the
strategy's range. Reflection to unrestricted action optimality needs an
appropriate coverage argument. Revenue equivalence separately requests
measurability and integrability of realized payments.
([Payment source][mec-payment], [revenue source][mec-revenue])

Posted-price optimality compares feasible posted prices under a single-crossing
sign condition. The source explicitly separates that result from optimization
over general monotone sale rules, haggling, and ironing. These limits should
survive any recovery into GameTheory. ([Source][mec-pricing])

## Recommendations for GameTheory

1. **Recover analytic single-parameter results first when this family enters
   the delivery queue.** Use the envelope and payment proofs against the
   existing [single-parameter owner](../GameTheory/Mechanism/SingleParameter.lean).
   Keep analytic imports under `Analysis`; keep report intervals, allocation
   bounds, and integrability local to the results that need them. The first
   consumer should derive a payment identity and uniqueness, with a nearby
   example separating report-range deviations from arbitrary actions. Extend
   to expected revenue only after the realized-payment bridge is proved.

2. **Use contract matching to extend the supported choice domain.** Start with
   a market whose contract terms or choice behavior cannot be represented by
   individual rankings plus responsive quotas. Reuse the choice-function and
   fixed-point proof ideas, and prove the responsive specialization agrees
   with the existing matching semantics. Preserve current DA, strategyproofness,
   and underfilled-cohort consumers. Admission of a broader owner requires its
   own dependency-gated validation; this comparison does not settle it.

3. **Treat measurable Bayesian games and compact-action mixed existence as a
   separate architectural task.** A diffuse prior or mixed action law is not
   a PMF on an uncountable carrier. Use a consumer needing such a law to test
   the measurable semantics, selection assumptions, and equilibrium bridge.
   Do not generalize the probability carrier throughout the library merely
   to make the external theorem statements fit.

4. **Borrow focused verification techniques.** Consider declaration-type pins
   for a small set of important public contracts and source-elaboration axiom
   auditing of anonymous examples. Preserve the existing warning-clean,
   source-boundary, and transitive-axiom requirements. API pins should detect
   unintended changes without creating compatibility aliases or freezing a
   refuted statement.

5. **Reuse narrow mathematical dependencies.** Search Mathlib first and assess
   the independent selection, fixed-point, and order lemmas for upstreaming or
   shared maintenance. Measure import closure and build cost before accepting
   a dependency. Importing the MathEconLib umbrella into the semantic core
   would bring a much wider surface than any proposed recovery needs.

## Recommendations for MathEconLib

1. **Make the integrable-deviation convention visible in client entry points.**
   The source documentation and regressions already explain it. Carry that
   explanation into user-facing examples: use `IsMixedNash` and `IsBNE` for
   economic equilibrium claims, and reserve the bare equilibrium problems
   for generic reasoning. Document the all-compared-laws-integrable domain
   when presenting equivalence with unrestricted unilateral payoff
   inequalities. Add extended-expectation siblings only for a concrete model
   that needs them, with a proved relation to the existing predicates.

2. **Preserve information restrictions when adding correlated or sequential
   concepts.** GameTheory's local deviation kernels are a useful reference.
   Ensure a correlated deviation cannot inspect another player's
   recommendation, and verify that lifting to laws respects mixtures. An
   arbitrary state relation can express such restrictions, but does not
   enforce them automatically. Keep preservation and reflection directions
   explicit when an action translation omits available actions.

3. **Reduce the recorded fixed-point maintenance debt.** The Schauder file
   identifies itself as original auto-formalization output outside the normal
   review discipline and disables several style linters. Clean and review
   that dependency in bounded changes, retaining theorem interfaces and the
   transitive-axiom checks. Introduce a warning budget that rejects increases,
   then move cleaned modules toward warnings as failures. Existing warnings
   are maintenance evidence, not evidence of invalid kernel proofs.
   ([Schauder source][mec-schauder], [warning report][mec-warnings])

4. **Use GameTheory's specialized matching results as recovery targets.**
   Compare the classical DA interfaces against GameTheory's
   [proposer strategyproofness](../GameTheory/Cooperative/GaleShapley/Strategyproof.lean)
   and [responsive rural-hospitals results](../GameTheory/Cooperative/Matching/RuralHospitals.lean).
   Establish each target under the appropriate strictness and responsiveness
   assumptions before extending it to broader choice domains. General
   contract-count invariance alone does not establish equality of every
   underfilled hospital's partner set.

5. **Publish a workflow matrix with exact theorem boundaries.** Retain the
   current explicit scope distinctions for payment identities, pointwise BIC,
   revenue equivalence, pricing, and finite affiliation results. For each
   workflow, identify a narrow import, a useful positive consumer, a nearby
   rejected case, and any named remainder. Document the existing area imports
   alongside the broad umbrella and measure client costs before changing the
   default import policy.

## Shared opportunities

A first interoperability comparison should use finite games where all payoffs
are integrable. Match the action profiles and outcome laws, then prove that
the two canonical Nash statements agree. This provides a small semantic check
without deciding the treatment of infinite expectation or diffuse laws.
Any resulting interface must respect GameTheory's prohibition on permanent
migration adapters and duplicate semantic owners.

The most promising shared mathematical work is in measurable selection,
fixed points, and choice/order theory. The libraries already agree on keeping
regularity assumptions close to their use and separating mechanisms,
valuations, and priors. Shared maintenance or Mathlib contributions should
retain those boundaries. Source reuse should preserve Apache-2.0 attribution
and applicable notices.

## Verification record

- Read the pinned MathEconLib source and representative GameTheory owners,
  together with the delivery documents. No independent full MathEconLib build
  was run for this comparison.
- Ran the source-token phase of MathEconLib's proof-integrity scanner over all
  170 discovered Lean sources: no forbidden proof tokens. This scan does not
  replace compiled transitive-axiom checking.
- Inspected [CI run 40620190317][mec-ci] for merged PR #259's head
  `3db7bc375797ed0ef1dcfe09279394ea2d727124`. Its build and project
  proof-integrity steps succeeded. This is CI evidence for that PR head,
  distinct from an independent verification of the merge snapshot.
- The [PR report][mec-pr] records 3,995 compiled declarations and 347
  source-elaboration declarations across 170 sources with zero integrity
  violations. Its [warning report][mec-warnings] records 80 warnings:
  76 library, four tests, and zero examples.

[mec-snapshot]: https://github.com/matheconlib/matheconlib/tree/58f602847d7f131994d32ca7a8cc1af35b7e2dbe
[mec-equilibrium]: https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/GameTheory/Equilibrium/Problem.lean
[mec-existence]: https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/GameTheory/Strategic/Existence.lean
[mec-mixed]: https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/GameTheory/Strategic/Mixed.lean
[mec-bne]: https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/GameTheory/Strategic/Bayesian/Measurable/PureBNE.lean
[mec-interim]: https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/GameTheory/Strategic/Bayesian/Measurable/InterimConverse.lean
[mec-bic]: https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/Mechanism/Core/BayesianIC.lean
[mec-payment]: https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/SingleParameter/Payment.lean
[mec-revenue]: https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/Auction/RevenueEquivalence.lean
[mec-pricing]: https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/ValueDistribution/PostedPriceOptimality.lean
[mec-contracts]: https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/Matching/Contracts/StableFixedPoints.lean
[mec-order]: https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/Matching/Contracts/StableOrder.lean
[mec-da]: https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/Matching/Classical/Marriage/DeferredAcceptanceComputable.lean
[mec-integrability]: https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLibTest/GameTheory/Integrability.lean
[mec-schauder]: https://github.com/matheconlib/matheconlib/blob/58f602847d7f131994d32ca7a8cc1af35b7e2dbe/MathEconLib/ForMathlib/Schauder.lean
[mec-ci]: https://github.com/matheconlib/matheconlib/actions/runs/40620190317
[mec-pr]: https://github.com/matheconlib/matheconlib/pull/259
[mec-warnings]: https://github.com/matheconlib/matheconlib/pull/259#issuecomment-6459120000
