# Post-architecture delivery plan

Status: active successor-native queue.

The architecture is settled. Delivery now proceeds by dependency depth and
compiled theorem evidence. The authoritative status index is
[`DeliveryLedger.md`](DeliveryLedger.md); recognizable public workflows are in
[`CapabilityMatrix.md`](CapabilityMatrix.md); discriminating examples are in
[`SupportEvidenceMatrix.md`](SupportEvidenceMatrix.md).

## 1. Admission rules

A work package enters the stable library only when it has:

1. one semantic owner at the lowest sufficient layer;
2. a hostile example capable of falsifying the intended theorem;
3. a positive consumer through the canonical API;
4. explicit assumptions on the operation or theorem that needs them;
5. a focused warning-clean build and relevant structural checks; and
6. an updated delivery row in the same change as the evidence.

Architecture-sensitive choices require a measured experiment and decision
record before their public API freezes. Routine theorem recovery after a gate
passes needs no new experiment.

### Review-to-delivery rules

The two repository-wide reviews sharpen how those admission rules are applied:

- treat a reported missing theorem as a falsifiable hypothesis, not an API
  specification; build the smallest hostile model before queueing the theorem;
- measure coverage by a useful canonical workflow with a positive witness, a
  nearby rejection, and a downstream consumer—not declaration-for-declaration
  ancestry or names alone;
- state the exact mathematical and bibliographic scope of standard names;
  familiar terminology does not license a stronger theorem or attribution;
- distinguish correctness corrections from optional breadth in the ledger, so
  an absent but false or unused bridge cannot keep a sound family `partial`;
  and
- keep implementation-loop checks source-level and narrow; run deep
  reachability and full-library audits only at integration or release gates.

## 2. Active dependency queue

### A. Proper-subgame semantics boundary — resolved

EXP-075/D42 corrected textbook SPE to quantify whole-policy deviations only at
information-set-closed roots. EXP-078 then machine-refuted the proposed
single-information-state one-shot characterization, even for finite,
well-founded, perfect-recall play with no information-state revisit. The
initial history can be the only proper-subgame root while profitable policy
changes require complementary changes at two information states.

No duplicate one-shot SPE predicate will be added. Historywise one-shot
optimality, finite assessment-local optimality, and proper-subgame SPE retain
their distinct scopes. A future restricted theorem needs a named consumer and
a premise that explicitly excludes the EXP-078 counterexample.

### B. Unilateral Kuhn realization and Nash transfer — resolved

`Protocol.Strategic` now owns the exact updated-law theorems at the lowest
sufficient semantic layer. They realize either an arbitrary behavioral or
mixed deviation while every nondeviator keeps the canonical induced policy.
The EFG surface specializes those laws and transfers expected-utility Nash in
both directions under perfect recall.

`Tests.EFGKuhnNash` is the hostile consumer: two players move sequentially,
the deviator may use a genuine mixed strategy, the other player's action
changes the terminal law, and a coordination equilibrium crosses both Nash
transfer directions. No-revisit remains an internal consequence of perfect
recall rather than a duplicated public premise.

### C. Repeated public-monitoring breadth — core resolved

Recover, in order:

1. **complete:** individual and pairwise monitoring rank, numerical rank, and
   the exact bridge from each deviation row to the canonical one-signal
   history law; the hostile fixture proves pairwise rank two under perfect
   action observation and rejects a constant monitor;
2. **complete:** finite-support APS decomposition and self-generation over the
   existing continuation/payoff API; a two-state Prisoner's Dilemma witness
   uses signal-contingent reward/punishment, rejects constant cooperative
   continuation, and reaches an actual PPE payoff;
3. **gated breadth:** public randomization only if it has a concrete signal-law
   consumer; and
4. **separate breadth:** monitored uniform results without introducing an
   infinite finite-support path law.

PPE remains canonical discounted Nash after every public history. Monitoring
rank remains an explicitly one-period informativeness condition, linked to
repeated play through finite prefix probabilities. Any new one-shot theorem
must reuse the canonical PPE predicate.

The recursive package covers pure public strategies and the greatest bounded
self-generating characterization of PPE payoffs. It does not claim the
constrained-efficiency or bang-bang results of Abreu--Pearce--Stacchetti, and
public lotteries are not silently folded into the decomposition operator.

### D. FOSG strategic and counterfactual analysis — transfer/support resolved

Priority: eligible now that B fixes the strategic-transfer boundary; keep its
strategic-transfer slice separate from the counterfactual/CFR package.

Separate packages:

- **complete:** strategic/utility transfer through explicit-order
  serialization; the two-player simultaneous witness transports behavioral
  Nash through both player orders and transports a profitable-deviation
  control;
- **complete:** whole-round boundary support, exact continuation laws from an
  arbitrary supplied boundary, support-by-erasure, and terminal-support
  equivalence; the simultaneous witness has a positive terminal history and
  rejects terminal support before play;
- **complete:** canonical counterfactual reach and continuation coefficients;
  actual reach remains `InformationModel.historyReachProbability`, the
  one-step coefficient is an exact continuation mass, and a two-step hostile
  consumer checks recursive multiplication;
- **complete:** whole-policy and pure-action counterfactual regret, with an
  exact scaled identity to canonical Bayes continuation deviation gain,
  perfect-recall and weaker-certificate sign theorems, and exact profitable and
  harmful controls; and
- **complete:** local cumulative regret matching at one information site,
  including arbitrary-law installation, a pointwise Protocol realization
  interface, the finite bound `t * infDist^2 <= (2M)^2`, asymptotic local
  convergence, and an update that puts all mass on the profitable action;
- **complete:** generic realization of that pointwise interface at
  all-nonterminal no-revisit decision fibers, with perfect recall discharging
  no-revisit, a genuine two-stage consumer, and an explicit global-failure
  control; and
- **complete:** a coordinated two-site deviation whose
  first local term is zero and decisive off-path term is one; alternative own
  reach recovers the exact root gain while baseline reach is machine-refuted;
  and
- **complete:** the generic bounded common-depth single-site root bridge,
  perfect-recall and action-facing corollaries, and a finite topological
  telescope whose canonical behavioral-run consumer recovers that exact unit
  coordinated gain; and
- **complete:** finite-family root-regret aggregation, including the exact
  Cesaro bridge, a simultaneous two-site D46 process, an exact D48 per-round
  root identity, conditional root convergence from both ordinary local norm
  bounds, and a fixed non-learning trajectory with persistent unit regret; and
- **complete:** deviation-uniform finite root aggregation and convergence,
  public payoff-range discharge of all local vector bounds, all four
  payoff-relevant pure plans in the hostile topological schedule, and exact
  compilation to canonical fixed-strategy external regret and its time
  average, with `1` and `-1` controls; and
- **complete:** reusable two-player zero-sum cancellation from both canonical
  external regrets to every pure and mixed empirical saddle gap and canonical
  `IsεNash`, tested on a correlated exact-equilibrium trace and a nonzero
  gap-`2` control; and
- **complete:** a same-trace two-player Protocol learning consumer: both D46
  laws move, both initial canonical regrets equal `1`, the shared saddle gap is
  `2`, and D50 plus D51 gives empirical-marginal canonical `IsεNash` with
  vanishing tolerance; and
- **complete:** a genuinely multi-site Bayesian Protocol consumer: two
  positive-probability type sites per player share one four-coordinate
  recurrence, D50 controls every complete contingent plan on one induced law,
  D51 gives canonical empirical `IsεNash` with vanishing tolerance, the
  initial complete-plan saddle gap is `2`, and at least one law moves at every
  type; and
- **next:** extract reusable finite schedule synthesis only after a second
  topology exposes its invariants. Arbitrary behavioral replacements and
  unequal-depth information fibers remain separate gates.

Do not merge these packages into the FOSG syntax root or hide serialization
order behind choice. The coefficient package counts because its continuation
law is canonical and its recursive factorization has hostile consumers. The
explicit one-shot and same-depth Bayesian schedules now supply both sides of
the static zero-sum saddle-gap theorem. This is not yet a general CFR
exploitability surface: reusable schedule synthesis, arbitrary behavioral
replacements, and unequal-depth fibers remain explicit later gates.

### E. Intrinsic selected-solution strategic form — resolved

EXP-079/D43 compiles a uniquely solvable intrinsic model at a caller-supplied
nature value directly to the canonical static form. An agent deviation replaces
one complete information-local rule and then re-solves the whole closed loop.
The causal sender–receiver witness proves truthful Nash and rejects a control
whose sender-only deviation changes the receiver downstream.

Nature lotteries, temporal execution, and behavioral/mixed strategy are
separate gates. Do not add them merely to make Intrinsic resemble Protocol.

### F. MAID strategic relevance

The promoted MAID compiler now has a multi-player, multi-site deviation and
Nash witness. The semantic target of relevance pruning is now complete:
`ObservationPruning` defines a smaller site-local policy domain, expands it by
source owner, preserves native and compiled laws under every accepted order,
and exposes the profile-local certificate under which reduced Nash remains Nash
against the full deviation space. A fair chance-signal witness must show both
the safe payoff-irrelevant removal and the nearby value-of-information failure;
mere non-factorization of a policy is not a safety test.

The exact local-utility graph view, the one-site
continuation-factorization-to-coverage bridge, canonical effective-parent
point-mass factorization, division-free finite conditional independence,
cast-free dependent enumeration, parent-closed cylinder marginalization,
ancestral-moral factor partitions, explicit-retained latent sums, and dependent
rank-one score assembly now survive their hostile experiments. The next
same-language gate identifies the moral scores and their table marginals with
the four query cylinder masses. Complete that finite-BN global-Markov layer
before claiming the
Koller--Milch graphical criterion discharges full-deviation coverage. Keep
requisite observation
(whether a realized parent value is needed by a rule) separate from strategic
relevance (whether another decision's rule is strategically live). Do not
report either graphical package as complete merely because the semantic
pruning target or graph-free bridge exists.

### G. Static mature-family rotation

These packages may proceed independently once their owner imports remain
fixed:

- secure equilibrium and remaining dominance/elimination results;
- weighted-potential theory;
- general security and constant-sum correlation;
- Sen and median-voter social choice;
- convex-game Shapley-in-core and the balancedness converse;
- matching optimality/strategyproofness; and
- egalitarian and Kalai–Smorodinsky bargaining.

Each package needs its own theorem-level consumer. Shared general mathematics
belongs in Mathlib when available, otherwise in `GameTheory.Math` only after a
live game-theoretic consumer exists.

Independent rationalizability is complete through the existing mixed-product
law: iterated product-belief best response has a Nash-survival theorem and a
strict three-player separation from correlated rationalizability.

### H. Mechanism and algorithm extensions

Independent packages:

- analytic envelope identities above the stable single-parameter algebra;
- monotonicity and critical payments for any truthful knapsack approximation;
- mixed, correlated, informational, VCG, price, and attainment extensions of
  the stable weak-undominance implementation surface;
- envy-cycle and maximin-share fair division; and
- richer contract or information-design timing only with a typed consumer.

The general Groves theory now lives in `Mechanism.Groves`, with a non-auction
public-choice consumer and a canonical DSIC bridge. The remaining second-price
presentations document and test their distinct tie-breaking scopes.

EXP-097/D54 adds the smallest implementation-theory seam justified by a real
cross-domain client pattern: `GameForm.recordProfile`, additive profile
transfers, and target implementation under canonical weak undominance. It does
not restore `KernelGame` or parameterize over arbitrary solution sets. Each
additional solution concept or analytic price theorem remains an independent
consumer-gated package.

The present greedy knapsack approximation is not a mechanism. All-pay support
is arithmetic, not an auction model.

## 3. Stable boundaries

- `GameTheory.Core` owns static forms, preferences, deviations, equilibrium,
  and the smallest shared foundations.
- `GameTheory.Protocol` owns execution, histories, information, policies,
  assessments, and strategic extraction.
- `GameTheory.Languages` owns syntax and named compilers; syntax imports no
  solution concepts.
- `GameTheory.Finite` owns executable finite algorithms; correctness connects
  them to real-valued proof semantics.
- `GameTheory.Mechanism` owns coordinated incentive and transfer domains over
  canonical forms, utilities, responses, and equilibrium predicates.
- `GameTheory.Repeated` and `GameTheory.Stochastic` use finite histories and
  finite-support transitions without claiming an infinite path law.
- `GameTheory.Analysis` imports stable semantic roots in one direction for
  topology, convexity, fixed points, and convergence.
- `GameTheory.Math` contains independently reusable mathematics justified by a
  live consumer.
- Frontier may import stable modules; stable modules never import Frontier or
  Challenges.

## 4. Verification policy

During iteration, run the narrowest relevant Lean file or Lake target. Run a
full warning-clean build when imports, package configuration, public roots, or
a delivery gate changes. The Phase 2 and Phase 3 audits default to fast
source-level checks; their `-DeepReachability` mode is reserved for CI and
release gates because it launches many independent Lean processes. A namespace
or import change must update affected positive reachability declarations and
probe roots in the same commit. Deep probes report each root/declaration result
in addition to aggregate expectations so integration failures can be audited
as a complete set rather than one serial mismatch at a time.

Every completed package records:

- exact files and theorems changed;
- positive and falsifying evidence;
- the focused and full commands run where applicable;
- any axiom check required by the trust surface; and
- the updated row in `DeliveryLedger.md`.

Support claims must never rest only on `True`, `Iff.rfl`, an impossible
premise, an elaboration-only declaration, or Experimental evidence.

## 5. V2 branch cutover and v1 capability recovery

The successor is published from the canonical `GameTheory` repository as a
history-preserving `v2` branch. The original main tree is retained at the
`v1-final` tag. Main is not moved until a clean hosted build and the release
reachability gates pass on `v2`.

The public transition is capability-based. [`V1CapabilityMap.md`](V1CapabilityMap.md)
redirects recognizable v1 workflows to their successor owners, queues useful
missing mathematics, and records deliberate retirements. It is not a source
compatibility promise.

Before moving `main`, run a bounded **potential-client usefulness gate**. This
is not a port of any known client and it does not preserve v1 declarations.
Known research clients may supply hostile proof patterns, but the artifacts
must state field-standard mathematics over the canonical v2 owners and remain
useful to an unrelated caller. Cover both individual fields and the bridges
that real developments need: language-to-semantics compilation,
execution-to-equilibrium, learning-to-static solution, and
algorithm-to-certificate. Each hostile slice must include a nontrivial positive
consumer, a falsifying or boundary control, and a count of representation
bookkeeping exposed in the public proof. A successful slice may justify a thin
proved-equivalent proof view; it never justifies a second runner, probability
semantics, or solution predicate. Record design competitions and kill
conditions in `ExperimentLog.md`, and graduate an interface only after the
experiment identifies a stable invariant rather than a single client's syntax.

Recovery proceeds in three dependency-gated waves:

1. **Established-owner recovery:** secure equilibrium and constant-sum
   correlation; Sen and median voter; convex-game core and cost of stability;
   matching optimality, rural hospitals, lattice, and strategyproofness;
   alternative bargaining solutions; envy-cycle EF1 and maximin share.
2. **Bounded analytic/domain experiments:** Myerson envelope identities;
   divisible cake cutting; monitored public randomization; absent-minded
   values; delegation/liquid democracy; and finite-game flow decomposition.
3. **Research frontier:** OpenGame admission only after a representative
   composition theorem and external semantic comparison. The v1 hierarchy is
   not imported wholesale.

For each workflow, port the proof idea rather than the old declaration graph.
Name the canonical owner, verify the mathematical scope, exercise a hostile
positive witness and a nondegenerate control, and update the owning ledger and
capability row with the compiled consumer. Stop rather than introduce a
second runner, solution predicate, probability hierarchy, compatibility alias,
or abstraction without another consumer.

Iteration uses narrow builds and the fast structural audits. A full build is
required at each recovered family gate; compiler reachability remains a hosted
CI/release check rather than part of the local implementation loop.
