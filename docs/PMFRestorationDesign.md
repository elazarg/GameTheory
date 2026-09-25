# Restore general discrete probability semantics

Status: implemented and validated, 2026-09-25.
[D62](decisions/D62-general-pmf-restoration.md) records the adopted decision.
EXP-122–141 cover the source surveys, canonical hostile slices, consumer
recovery, and whole-library acceptance. The
[delivery ledger](DeliveryLedger.md) and [worklog](PMFRestorationWorklog.md)
own current status and validation details.

## Design and evidence

Restore ordinary Mathlib `PMF` as the canonical discrete law in `GameForm`,
preferences, deviations, protocol transitions, behavioral policies, and
beliefs. Finite support is a hypothesis on an ordinary PMF where an operation
needs it; remove the parallel `FinDist` operation algebra. A bundled
certificate is justified only by a concrete consumer, not by migration cost.
Preserve the current signature/information separation,
typed histories, and single equilibrium predicate. Do not introduce a
permanent parallel `PMFGameForm`, a compatibility layer, or a probability
typeclass.

This corrects a loss of expressive scope relative to v1. The v1 core accepted
PMFs with infinite support; the FinDist baseline could not. D2 deliberately chose
finite support to obtain unconditional real expectations, and then compared
two representations of finite laws. Those experiments did not compare the
semantic cost of excluding general discrete laws. Finite support is useful
for that specialization, but need not constrain ordinal game semantics or
bounded expected utilities. It also does not make arbitrary real-valued PMFs
executable; the rational algorithm layer remains separate.

The supporting surveys are:

- [v1 inventory](PMFRestorationV1Inventory.md): exact declarations, assumptions,
  and Mathlib overlap at the peeled `v1-final` commit
  `02898a2d8b918f9b106a683420ca78c99867560e`.
- [Current impact survey](PMFRestorationImpactSurvey.md): semantic owners,
  dependency fanout, finite capabilities, and audit consequences at baseline
  `1dba33272108204204758c6eaa5ef8ce49a428c5`.
- [Semantic review](PMFRestorationSemanticsReview.md): integrability, dependent
  execution, infinite Bayes fibers, full-policy deviations, and convergence.

V1 already proves substantial general mathematics: bounded expectation and
bind/Fubini, bounded pointwise convergence, positive-event conditioning, and
finite-index dependent products of arbitrary PMFs. Mathlib already owns the
basic PMF monad and conditioning. Reuse these proofs before creating new
infrastructure. A source count does not establish that most migration work is
done: several v1 product marginalization and disintegration theorems still
require finite coordinate carriers, and their consumers use the old types.
V1's totalized expectation API and weak default sequential consistency should
not be restored as the public meaning of expected utility or sequential
equilibrium.

## Canonical ownership

The table specifies target types, not declarations already implemented.

| Owner | Target | Assumptions that remain local |
|---|---|---|
| `GameSignature`, `Profile`, `Profile.update` | Unchanged probability-free carriers and replacement | Existing dependent-profile transport boundary |
| `GameForm.play`, `outcomeLaw` | `Profile sig → PMF sig.Outcome`; bind arbitrary PMF profile laws | No finite carrier or support premise |
| `WeakPreference` | `Ranking Agent (PMF Outcome)` | Preference laws are hypotheses |
| `DeviationScheme.actLocal`, `apply`, `IsEquilibrium` | PMF replacements and status-quo laws | Existing finite deviating coalition, recommendation locality and law-linearity |
| Mixed strategy formation | PMFs on strategies, independent finite-index product | Finite player index on independent product construction |
| `ExecutionProtocol.step` and runners | PMF transitions and bounded-run laws | Support-sensitive legality, terminal-first recursion; no finite branching premise |
| `BehavioralPolicy`, assessment beliefs, `Context.outcome` | PMFs on legal choices, typed history fibers, and continuation outcomes | Legal total policies; information-set conditions on operations needing them |
| Bayesian, MAID, stochastic, monitoring laws | PMF priors, node laws, transitions, and signals | Domain-specific premises on the corresponding theorem |
| Finite algorithms and finite simplex bridges | Ordinary PMFs with local finite-support/carrier hypotheses; explicit executable enumerations | Finiteness only where sums, enumeration, or compactness need it |

Finite player products can have infinite-support factors. An infinite product
of nondegenerate coordinates generally needs a measure, even with only
countably many coordinates. Arbitrary carrier types remain allowed: each PMF
itself has countable support, so no ambient `Countable` instance belongs in
`GameForm` or `ExecutionProtocol`.

General discrete PMFs do not cover nonatomic continuous laws or general laws
on infinite paths. Keep the existing `PolicyMeasure` bridge and the D11
measure/path boundary; do not force such laws through PMF. Fixed horizon also
does not imply finitely many histories when branching is infinite.

For `PolicyMeasure`, distinguish forward and reverse reading. A product measure
built from PMF coordinates has PMF finite marginals even on infinite action
carriers. An arbitrary policy measure need not: an action marginal may be
nonatomic. Reverse reading therefore requires atomicity or countable measurable
local choices. EXP-136 establishes the latter boundary without finite global
site covers, including both unilateral hybrid laws. General PMF restoration
does not license an unrestricted `Measure → PMF` conversion.

Implementation latitude: the user authorizes measure-theoretic generalization
when its downstream effects are controlled. In particular, an expectation
bridge may reuse Mathlib integration rather than reconstruct its calculus.
Any proposal to put measurable spaces or measurable kernels into canonical
game/protocol data must first measure that wider impact. The present discrete
PMF target is the current scope choice, not a prohibition on a
better measured generalization.

## Expected utility without accidental zero payoffs

EXP-123/124 establish one operation-local notion of finite real expectation,
independently of games. The canonical foundation signatures are:

```lean
def PayoffIntegrable (μ : PMF Ω) (u : Ω → ℝ) : Prop :=
  Summable (fun ω => (μ ω).toReal * |u ω|)

noncomputable def expect (μ : PMF Ω) (u : Ω → ℝ)
    (_h : PayoffIntegrable μ u) : ℝ :=
  ∑' ω, (μ ω).toReal * u ω
```

The discrete weighted-sum owner
needs no measurable-space field on game data. Prove equivalence with Mathlib
integrability in the separate discrete-measure bridge. Keep one value under
that equivalence. Supply proof-irrelevance, support congruence, pure/map/bind,
monotonicity, and finite-support agreement lemmas. A bound on the payoff over
the law's support is sufficient; a global bound is convenient for all laws.
For unbounded bind, require absolute integrability of the joint weighted
payoff, not merely an integrability fact for each conditional separately.

The finite-expected-utility preference on ordinary PMFs is guarded:
both laws must have finite expectation and their certified values must satisfy
the comparison. Schematically,

```lean
euPreference u i preferred alternative :=
  ∃ hp : PayoffIntegrable preferred (u i),
  ∃ ha : PayoffIntegrable alternative (u i),
    expect alternative (u i) ha ≤ expect preferred (u i) hp
```

This remains a specialization of `WeakPreference` and the existing
`IsEquilibrium`. It is a relation on all laws, with reflexivity on its
integrable domain; it is not an unconditional total preorder on all PMFs.
An inadmissible deviation makes its comparison fail. It is never removed from
the deviation quantifier. Global boundedness gives a total expected-utility
preference and all the usual order laws. For unbounded utility, theorems
requiring these laws must certify all feasible compared laws. Applications
that intend infinite values need an explicitly different value/preference
semantics; a real expectation cannot supply those values.

Do not infer incumbent integrability from a vacuous equilibrium quantifier:
an empty deviation type supplies no comparison proof. Any EU theorem promising
a defined incumbent payoff must carry its admissibility explicitly, alongside
the hypotheses covering all compared deviations.

Similarly, keep `Context`'s law-producing outcome and continuation fields,
make `value` require integrability, and give rationality the certificate for
the incumbent and every allowed candidate. The equivalence with absence of
profitable deviations must assume that entire comparison family is
integrable: otherwise undefined values cannot be interpreted as unprofitable.
Do not put boundedness into every game's semantic data. Finite laws discharge
these obligations automatically, preserving their expected-value comparisons.

Preservation has two scopes. Evaluating the same finite laws and the same
deviations gives the same values and propositions. On infinite strategy
carriers, enlarging finite-support mixed strategies or deviations to arbitrary
PMFs changes the quantified domain; equilibrium equivalence for arbitrary
preferences does not follow. State any transfer across that enlargement with
its actual boundedness, convexity, or continuity hypotheses and prove it.
Finite-carrier specialization has no such domain enlargement and must recover
the existing finite existence statements exactly.

EXP-122 proves why this matters. Its geometric law has positive mass at every
natural number. Reward `2^(n+1)` has weighted term one at every `n`, infinite
nonnegative expectation, and nonsummable real weighted payoffs. Lean's
unrestricted real `tsum` nevertheless returns zero. A Bochner integral is
also totalized, so replacing `tsum` with an unguarded integral is insufficient.

## Sequential semantics

Use Mathlib's support-dependent bind to build the existing typed history
runner with PMF transitions. Reprove support/reach characterization,
composition, terminal absorption, and finite-law specialization before moving
information-local conditioning. Reuse one runner throughout compilers and
assessment continuations.

Beliefs are PMFs on the existing information-history subtype. For infinite
fibers, reach weights must define a finite event mass before normalization.
The history-antichain condition supplies disjoint first arrivals; prove their
sum is at most one, including variable depths. Positive mass gives the Bayes
PMF. At zero mass, Bayes imposes no ratio; the consistency predicate, not a
fallback normalization, determines off-path restrictions.

Retain full behavioral-policy replacement for sequential rationality and
the current perturbation-limit consistency. V1's default on-path Bayes
consistency is weaker. A full-support PMF can exist on a countably infinite
menu, using a full-support reference law rather than a uniform law.
Nonempty menus alone do not provide full support, and uncountable menus
cannot have fully supported PMFs. Probability-zero chance edges are not made
reachable by player trembles.

Bounded payoff convergence can reuse v1's theorem: pointwise convergence to
a normalized PMF supports convergence of bounded expectations. Unbounded
payoffs require additional control such as uniform integrability. Neither
this fact nor the PMF type yields compactness or equilibrium existence on
infinite strategy spaces. Preserve D61's finite existence theorem under its
actual finite-dimensional hypotheses and prove it uses the generalized
canonical predicate.

Fuel is independent of finite support. Keep it in the bounded runner. Expose
terminal-game equilibrium using a certified sufficient horizon and prove
independence of that choice. Almost-sure termination without a uniform bound
requires stopping semantics; it is not a reason to assert arbitrary-fuel
equilibrium. Retain the existing fuel-two/fuel-three counterexample.

## Dependency gates and acceptance

Implementation coverage and acceptance evidence are summarized in
[PMFRestorationWorklog](PMFRestorationWorklog.md).

Each gate gets its own experiment and changes its owning ledger row only on
compiled evidence. Before broad migration, take the smallest hostile static
and sequential slice through the proposed operations. Experimental definitions
may be temporary, but cannot become a second stable semantic hierarchy.

Implementation refinement (EXP-124): after the probability and dependent
execution pilot, finish P1/P2 on the canonical owners themselves. A parallel
experimental information/policy/assessment framework would duplicate too much
of the actual architecture to provide stronger evidence. This changes the
location of the validation work, not its acceptance conditions; broad theorem
recovery waits for the corresponding dependency gate.

| Gate | Work and source reuse | Required hostile acceptance |
|---|---|---|
| P0: probability infrastructure | Mathlib PMF; v1 bounded expectation, finite-index products and conditioning; current finite bridges | Infinite-support factors with proved marginals; positive-event conditioning and disintegration on positive-mass fibers with zero-mass irrelevance; guarded map/bind expectation; finite agreement; divergent-payoff rejection |
| P1: core vertical slice | Canonical form, preferences, deviations, mixed formation and EU | Countably supported outcome and mixed/joint profile laws through Nash and CE/CCE; preserved recommendation locality; no hidden finite carrier; old finite examples express the same propositions |
| P2: sequential vertical slice | Canonical PMF runner, typed information, beliefs and full-policy continuation | Countable legal actions followed by countable chance; infinitely many histories in a variable-depth information antichain; correct Bayes and bounded continuation; off-path whole-policy deviations; horizon independence |
| P3: semantic cutover and consumers | In-place canonical owners; language compilers, Bayesian priors, MAID, stochastic and monitored prefixes | Infinite-support laws actually reach the public APIs; finite-policy product-measure marginals remain correct for infinite action carriers; finite witnesses remain exact specializations |
| P4: finite and analytic recovery | Current simplex/existence/algorithm layers; general bounded convergence from v1 | Finite Nash and D61 sequential existence; rational verifier correctness; pointwise fully mixed countable approximation; all prior counterexamples preserved; full build, lint, and architecture audits |

Do not claim a bounded horizon gives a finite counterfactual site cover: a
single infinitely branching transition can violate that premise. Preserve
finite covers where the realization theorem uses them, and distinguish the
general PMF semantics from broader measure realization. EXP-126 proves the
all-site PMF obstruction; EXP-127 tests removal of the cover only for the
ordinary policy measure's forward law.

P0's compiled infrastructure now includes general dependent products and
marginals, positive-fiber reconstruction and subtype posteriors, guarded map,
general integrable bind/Fubini, and mixture algebra. The hostile pilots prove
genuine infinite support and the divergence control. The guarded canonical EU
constructor, static equilibrium consumers, and the complete hostile sequential
slice now pass EXP-123/124, completing P0–P2. Canonical execution, extraction,
typed histories, randomized choice, and information-local policies use PMFs.
EXP-125 also completes law-first backward evaluation and the exact guarded
Zermelo constructor, including infinite chance and the finite fixtures.
P3–P4 also pass: the original consumer families, finite existence statements,
executable correctness, public lint, architecture audits, and unrestricted
library build are recovered. EXP-129 records final integration evidence.

Source-impact measurements identify 335 of 500 baseline Lean files mentioning
`FinDist`, and 424 transitive authored importers of its module. They measure
review scope, not required edits or delivery time. Therefore validate P0/P1/P2
in isolation before the broad cutover. At cutover, integrate all affected
consumers until the public build is green; do not freeze half of a duplicate
hierarchy merely to keep a smaller patch compiling.

## Audit and rejection criteria

D2's finite-support *default* and the discrete portion of the D3 extension
policy must be revised at promotion. D3's rejection of a universal probability
monad survives, as do D11's measurable boundary and D12's one-way imports.
Permit PMF as a public semantic type and replace the blanket PMF-token ban
with explicit ownership of weight algebra, summability, and measure bridges.
Continue to audit raw `toReal`/`ENNReal` plumbing, allowing it only at named
owners justified by their operations. Keep the executable layer separate.

The source audit implements the public PMF policy above, names the probability
and experiment owners, and rejects any return of the retired FinDist carrier.
EXP-129 records the reviewed representation counts and final expected-value
checks. Forbidden transport, import, placeholder, and executable-layer budgets
remain unchanged.

Reject or revise a migration that tests only finite laws on infinite carriers,
silently interprets undefined real payoffs, drops difficult deviations,
normalizes a history sum without event-mass justification, replaces strong
consistency with on-path Bayes, duplicates canonical concepts, leaks casts to
consumers, or extrapolates finite existence to infinite spaces. Record failed
slices before revising the design. A probability-only pilot cannot discharge
the game and information gates.
