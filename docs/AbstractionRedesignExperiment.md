# Abstraction building-block experiment

Status: thirteen items are complete, including twelve investigations and one
ownership consolidation; the cross-domain investigation
continues. Finite-menu representation, local scalarization, parametric
optimality, simultaneous feasible choice and a complete scoped exchange slice
extend the initial six-item results below.
The goal is reusable building blocks for the library and economic theory,
with later MathEconLib extraction in view. Every collected slice
passes full integration audits. Selected theorem-level and guarded-comparison
changes are adopted; the binary-only mixture proposal is refuted, and new
context, coalition and arena structures are not admitted. This is a scoped
building-block result, not completion of every future abstraction theorem.

The post-slice consolidation and remaining discriminating questions are in
[MathEconBuildingBlocks.md](MathEconBuildingBlocks.md). Item 12 is a read-only
dependency/ownership consolidation, not a new architecture experiment: five
accepted mathematical owners depend only on Mathlib, and the simultaneous
feasible-choice owner adds the explicit analytic fixed-point dependency.

Item 13 / EXP-184 validates direct conditional and backward composition under
explicit actual-prior comparison laws, with whole-policy admissibility kept
separate. A total transitive law ranking strictly reverses two strict conditional
choices before observation; non-EU possibility comparisons supply the positive
arbitrary-PMF clients but fail strict cancellation. The prototypes remain
experimental and establish chooser-level rather than imperfect-information
policy composition. See [D89](decisions/D89-conditional-and-dynamic-comparison.md).

Item 01 selects direct preference-generic exact-law proofs after comparing the
existing coverage API on the same statements. See [D78](decisions/D78-preference-generic-exact-law-bridges.md)
and EXP-173 for measurements and limits.

Item 02 selects guarded relation-based response definitions and direct
finite-range improvement-rank hypotheses. The partial-preference and
singleton-strategy controls delimit the assumptions; numerical potential and
congestion consumers remain supported. See
[D79](decisions/D79-ordinal-response-and-improvement-ranks.md) and EXP-174.
No new ordinal-potential structure is admitted.

Item 03 refutes binary convexity as sufficient for arbitrary PMF mixture
closure, even for a total preorder. Its direct client prototypes retain
separate sources of expectation-definedness and remain experimental. See
[D80](decisions/D80-binary-and-countable-mixture-closure.md) and EXP-175.
Item 04 selects the independent `Math.GuardedOptimality` predicate and makes
numerical local optimality an exact specialization. A stochastic nonnumeric
consumer, nonbijective law coverage and concrete undefined/infinite-value
controls pass. The relation-valued Context record remains experimental;
higher sequential APIs keep their existing numerical semantics. See
[D81](decisions/D81-guarded-protocol-comparison.md) and EXP-176.
Item 05 selects actual-law, member-local comparison theorems while preserving
the existing strong-Nash and matching meanings. Fixed strict unanimity does
not turn its no-gain relation into a preorder; a valid responsive blocker can
harm a nonconsenting incumbent. See
[D82](decisions/D82-local-coalition-comparison-and-consent.md) and EXP-177.
No first-class coalition problem is admitted.

Item 06 retains the existing local-kernel interface. The fixed matching
replacement is realized with two consenters, three affected coordinates and
four total coordinates, preserving a genuine spectator law. A law-aware
operation failing mixture linearity is a rejection control, not a requiring
game client. See [D83](decisions/D83-local-kernels-and-affected-coordinates.md)
and EXP-178. No general matching compilation or global expressivity result is
claimed.

The question is which small building blocks make independently useful
generalizations cheap on the existing semantics. The starting evidence is
[Abstraction analysis](AbstractionAnalysis.md) and
[Survey evidence](SurveyEvidence.md). Their classifications are hypotheses to
test, not a target architecture to implement rung by rung. EXP-173 owns the
first comparison and its observations in [ExperimentLog.md](ExperimentLog.md).

## Result of the initial investigation

| Selected building block or boundary | Evidence |
| --- | --- |
| Exact laws and explicit deviation coverage support preference-generic bridges without a new transport wrapper. | EXP-173 / D78; Kuhn and Bayesian consumers. |
| Bare law preferences support strict response and improvement dynamics; local comparability and finite-range preorder ranks supply the existence path. | EXP-174 / D79; non-EU, partial-preference, singleton and infinite-profile controls. |
| Binary mixing is weaker than arbitrary PMF comparison closure; full weak comparison and exclusion of strict gain spend different guards. | EXP-175 / D80; total-preorder counterexample and scoped client prototypes. |
| Probability-independent guarded optimality separates admissibility from comparison, while numerical Context remains its exact specialization. | EXP-176 / D81; production coverage, stochastic belief and undefined/infinite-value controls. |
| Actual-member comparability is sufficient for strong-Nash agreement; weak rejection and strict blocking retain distinct meanings under partial preferences. | EXP-177 / D82; joint deviation, fixed-coalition and responsive-matching controls. |
| Consenting judges and affected coordinates must be distinguished; the existing kernel interface handles the tested displacement without weakening locality or bind linearity. | EXP-178 / D83; proper affected subset, spectator law and whole-law rejection control. |

No universal judgment ladder, Mixable record, coalition problem, broader arena,
probability abstraction or certificate hierarchy is adopted. The original
surveys remain hypotheses and motivation; these experiments narrow what has
actually been validated. The final full audit passes 3,873 default and 4,772
validation jobs, public lint and transitive standard-axiom checks.

Further promotion requires a concrete consumer: a stable non-EU mixture client
must select the exact closure/guard law; a higher sequential generalization
must identify a useful theorem while preserving terminal and belief semantics;
and a broader arena must show an unmet operation or measured failure of the
current representation. Adjacent theorem families and a complete matching
compiler were not part of these accepted slices. The governing delivery order
remains `PostArchitectureDeliveryPlan.md` and the status index remains
`DeliveryLedger.md`.

## Cross-domain continuation

The first six items tested generalization within existing game semantics.
The next stage tests both directions between economic primitives: preferences
induce feasible choices, and observed menu choices may rationalize preferences.
Extraction means independence from game forms, lotteries and utility scalars;
it does not mean adding a new shared problem record or changing another library.

**Item 07 / EXP-179: finite-menu choice (complete, D84).** Compare direct feasible greatest
elements, maximal elements, and a correspondence of selected alternatives.
Test whether feasibility, nonempty choice on every nonempty finite menu, and
the weak axiom of revealed preference reconstruct a total transitive relation
and exactly its greatest-element correspondence. Preserve ties and allow an
infinite ambient alternative type. Search Mathlib first; use its maximal-element
theorems rather than reprove general finite-order mathematics.

Clients must include the canonical best-response comparison and an independent
economic allocation or incentive client. Budget-menu and bundle examples may
serve as experimental evidence, not claims of an existing demand API or a
MathEconLib migration. Hostile controls must distinguish greatest from maximal
under incomplete preferences, feasible choice from guarded comparison without
candidate membership, and a correspondence of tied bundles from the union of
their contents. A restricted family of budget menus must not be silently
treated as all finite menus. Stop or narrow if representation requires a new
numerical score, global finite carrier, arbitrary tie breaking, or changes to
existing equilibrium/expectation guards.

The result selects the probability-free `Math.FiniteChoice` theorem layer.
Feasible, nonempty choice with the correspondence weak axiom is exactly
greatest choice under a complete preorder, on all finite menus of an arbitrary
ambient type. Rank finite existence now reuses this owner and Mathlib's maximal
theorem; canonical best-response and knapsack allocation adapters pass.
Three genuine lottery choices prove that this representation need not be
expected utility. Partial-preference and tied-bundle controls delimit latent
identification and bundle flattening. Full audit passes 3,874 default and
4,776 validation jobs, lint and transitive standard-axiom checks. See
[D84](decisions/D84-finite-menu-choice-and-revealed-preference.md).

Later questions remain consumer-gated: endogenous feasible sets and fixed-point
existence; welfare aggregation and interpersonal scale; information and dynamic
choice consistency. These are possible investigations, not adopted interfaces
or a breadth-first delivery queue.

**Item 08 / EXP-180: scalarization (complete, D85).** Test whether a feasible
maximizer is Pareto maximal when each strict improvement of that incumbent
raises the scalar objective. Compare with Mathlib's global monotone transport.
Use existing Groves sums and bargaining products, keeping weights, disagreement
and feasibility with their owners. Positive gains at the bargaining incumbent
must suffice without global positivity. Keep zero/negative weights, objective
biases, infeasible incumbents and zero-product dominated ties as rejection
controls. Ordinal efficiency and the choice of a cardinal social objective
must remain distinct.

The result selects one small `Math.Scalarization` theorem over preorders.
Groves reported-welfare maximization implies maximality of attainable reported
valuation vectors before transfers. A canonical Nash-product solution with
positive incumbent gains is fully Pareto efficient, even on a feasible domain
where the product is not globally strictly monotone. The original weak-Pareto
theorem remains unconditional; an IR zero-product dominated solution refutes
using participation alone for the stronger conclusion. Actual biased canonical
choices, zero/negative weights, positive rescaling and infeasible-incumbent
controls delimit the statement. Full audit passes 3,875 default and 4,779
validation jobs, public lint and transitive standard-axiom checks. See
[D85](decisions/D85-local-scalarization-and-pareto-maximality.md).

### Consequence for field-wide building blocks

The evidence now supports separate operations for domain-guarded comparison,
feasible menu choice and preference reconstruction, and maximality from a
selected objective. Their mathematical owners import only Mathlib. Strategic
coverage, expectations, institutional feasibility, reported valuations and
bargaining disagreement remain with their domain owners. This makes later
shared mathematical-economics extraction possible without assuming that a
single record can represent all those meanings.

Items 09 and 10 validate an endogenous feasible correspondence boundary:
the allowed menu may depend on prices, the incumbent profile or other agents.
Their concrete clients separate feasibility, approximation of alternatives
and simultaneous existence. These results do not identify a field-wide
native constraint or market-clearing representation. The
all-finite-menu representation must not be applied to restricted budget data
without its missing domain hypotheses, nor may fixed-simplex existence be
advertised as general-equilibrium existence. Information-dependent choice and
stronger representation theorems remain independent later questions. These
gates continue the investigation; the eleven completed investigations do not claim
an architecture for the entire field is settled.

**Item 09 / EXP-181: parametric feasible choice (complete, D86).** Separate closed
feasibility from the ability to approximate feasible alternatives as parameters
change. Test a closed feasible-argmax graph theorem with lower hemicontinuity
and a jointly continuous objective, independently of compactness and convexity.
Use an actual varying consumption budget and one existing fixed-simplex
consumer. Preserve a concrete economic failure of the closed-graph-only
proposal. This is not full Berge or endogenous-game equilibrium existence;
`Core.ConstrainedNash` continues to mean payoff-threshold filtering.

The selected `Math.ParametricOptimality` theorem needs neither compactness,
convexity, nonempty values nor first countability for closedness of maximizers.
Its score codomain is an arbitrary linearly ordered topological space with
closed order. The production local-lottery proof consumes its constant-menu
specialization. A changing divisible budget supplies continuous feasible
recovery and separate compact existence, even for a satiation utility.
The zero-income/free-good budget has a closed graph, upper hemicontinuity and
nonempty compact convex uniformly bounded values, but its optimizer graph
fails closedness and lower hemicontinuity fails. The extra graph law therefore
has independent content. Full audit passes 3,876 default and 4,782 validation
jobs, public lint and transitive standard-axiom checks. See
[D86](decisions/D86-parametric-feasible-optimality.md).

The next dependency gate concerns simultaneous optimality with endogenous
menus, such as two consumers sharing one unit of capacity. Compare local
affordable optimization with ordinary Nash filtered by a feasible-profile
predicate before admitting any generalized-game representation. Retain
per-agent objectives rather than introducing a summed social objective to
fit a fixed-point interface.

**Item 10 / EXP-182: simultaneous feasible choice (complete, D87).** Compare
ordinary Nash filtered by feasibility with local affordable optimization in
a shared-capacity quantity game. Test a per-coordinate fixed-point theorem
using the closed-argmax result, lower hemicontinuity and quasiconcavity on each
actual menu. The old local-lottery theorem must remain an exact specialization;
no aggregate social objective or generalized-game record is pre-approved.

The selected analytic theorem works on a compact convex product envelope,
with each menu nonempty, closed-graph and lower hemicontinuous and each real
objective jointly continuous and quasiconcave on its own menu. Menu compactness
and convex maximizers are derived. The finite-simplex local-lottery theorem
is an exact specialization; no second bespoke construction is retained there.
The independent changing-menu family admits arbitrary continuous quasiconcave
objectives. Its own-quantity instance reaches the canonical deterministic
interval-strategy game through explicit affordable-menu and comparison bridges.
Every affordable local optimum fills capacity; every ordinary Nash profile
violates it. Continuous square scores separately refute convexity of
maximizers without the objective-geometry premise. Full audit passes 3,876
default and 4,786 validation jobs, public lint and transitive standard-axiom
checks. See [D87](decisions/D87-simultaneous-feasible-choice.md).

This admits a mathematical existence operation, not a new universal game or
economic-problem structure. Chosen admissibility, available alternatives,
regularity of available sets and per-coordinate objective geometry remain
separate. Their owners can later be extracted into shared mathematical
economics without making all native domains instances of one stored object.
Broader native constraints and stronger preference representations remain
independently requiring later clients. Item 11 tests price formation and
market clearing on one complete bounded-to-unbounded exchange slice.

**Item 11 / EXP-183: exchange economy (complete, D88).** Connect price-dependent
budgets, individual choice, excess-demand price response and market clearing
for two goods and two consumers with unit endowments of each good. Permit zero
price coordinates, preserve tied demands, and distinguish capped from full
budget optimality. Test continuous concave strictly monotone utilities; retain
zero-income, satiation and cap-binding rejection controls. A complete slice
must remove the auxiliary consumption cap after proving clearing. No generic
market record or interpersonal consumer objective is pre-approved.

The scoped existence theorem supplies normalized prices and full-budget
competitive equilibrium for two consumers and two goods with unit endowments
of each good. Utilities are continuous on the ambient `ℝ²` and concave and
strictly monotone on the nonnegative cone; a conflicting linear-preference
instance proves the assumptions are inhabited concretely. Prices may have
zero coordinates in the fixed-point domain, while wealth remains one.

The selected stable addition is `Math.LinearBudget`: positive continuous
wealth and fixed-bundle continuity of linear costs give lower hemicontinuity
by radial feasible recovery, without compactness or positive-price assumptions.
Existing simultaneous feasible choice supplies capped demand and a physical
excess-demand price response. Separate residual top-up accounting proves
clearing; proved resource bounds then make the cap inactive, and Mathlib's
concave local-to-global theorem supplies full-budget optimality.

Controls prove that tied individual demands need not clear, that a cap-binding
clearing price-response point can fail full-budget optimality, and that
satiation can leave an uncleared fixed point. Native market definitions and
the exchange existence theorem remain experimental/test evidence, with no
generic market record admitted. Full audit passes 3,877 default and 4,792
validation jobs, public lint and transitive standard-axiom checks. See
[D88](decisions/D88-exchange-budgets-and-market-clearing.md).

This validates composition of the small mathematical operations across game
and exchange consumers. It does not settle a field-wide economic data model.
General endowments need new accounting; weaker preference hypotheses need
their own preservation proof; stable market interfaces and MathEconLib
extraction remain future consumer-gated decisions.

## Constraints and alternatives

The accepted defaults remain [D5](decisions/D5-deviation-and-equilibrium.md),
[D7](decisions/D7-certificate-stratification.md),
[D8](decisions/D8-minimal-transformations.md), and
[D60](decisions/D60-noninvertible-strategic-transfer.md). In particular:

- `IsEquilibrium` owns equilibrium of a law; response and dominance keep their
  profile-quantified meanings.
- Locality and law-linearity remain enforced by `DeviationScheme`'s type and
  its `bind` construction. An arbitrary law transformer would lose both.
- Direct theorem hypotheses and existing coverage are the baseline. New
  records, probability interfaces, certificate hierarchies, or category
  instances must earn admission independently; none follows from naming levels.
- General PMF semantics and actual-law expectation-definedness survive every
  specialization. Finiteness belongs to operations requiring it.

Invariance under re-encoding is diagnostic evidence. It neither constructs a
generalized definition nor proves that a theorem descends to a proposed level.
The distinction between outcome utility and a relation on lottery laws matters:
mixed Nash can be defined for arbitrary lottery preferences even when a
particular existence or representation argument needs expected utility.

## Branch and integration discipline

The collecting branch is `codex/experiment-abstraction-building-blocks`.
Commit the two survey documents and this plan there. Each item starts from the
latest accepted collecting tip on
`codex/experiment-abstraction-item-NN-<subject>`. Preserve item branches as
evidence; merge successful, warning-clean slices back into the collecting
branch. A rejected design is a useful outcome: integrate its documented result
and necessary counterexample, without promoting its rejected API.

Use this checkout only, with no worktrees. Independent analysis or drafting may
run in parallel in disjoint files or ignored `.codex/scratch/` folders. Branch
switching, tracked integration edits, and compilation are serialized. Stop all
edits before each build. Commit and push small reviewable checkpoints, naming
unvalidated checkpoints explicitly; branch publication is not API admission.
Keep unrelated user changes out of experiment commits.

## Item 01: preference-independent bridge transfer

**Question.** Can law equalities and unilateral coverage generalize real
language bridges without a new transport structure or a deviation bijection?

Compare three concrete implementations of the same generalized statements:

1. Direct bridge-local proofs using the named honest and updated-law theorems.
2. Existing `IsNash.of_coverage`, supplying equality-induced comparison
   implications for the source and target preferences.
3. A direct generic law-coverage theorem, only if the first two expose repeated
   useful work. Its hypotheses must cover every target deviation; equality of
   honest laws alone is insufficient. Compare its total cost against (2).

The target clients are both directions of the EFG behavioral/mixed Kuhn Nash
transfer and a second bridge with different policy or outcome shape, initially
Bayesian-to-Protocol or native MAID compilation. The generalized statements
quantify over a `WeakPreference`; bridges changing outcome carriers use the
existing preference pullback along an outcome map. Existing expected-utility
consequences must follow as specializations, with their original mathematical
scope. Do not infer same-epsilon utility transfer from a generic ordinal
theorem without supplying its slack comparison.

Kuhn conversions need not be inverses as strategies: coverage of deviated laws
is the required property. Do not impose a deviation equivalence merely to fit
the survey sketch. No CE/CCE transport follows from profile-dependent Nash
coverage; those concepts require recommendation-local coverage.

**Hostile controls.** Use a genuinely mixed deviation and a nonconstant law
affected by the other player's strategy. Exercise different outcome carriers
in the second client where available. Preserve or reuse a negative control
where honest laws agree but an extra target deviation breaks equilibrium.
Demonstrate a non-expected-utility preference consumer so the new quantifier is
used. Existing Kuhn and bridge fixtures remain downstream consumers.

**Admission.** Choose the smallest implementation which preserves the
statements and passes the shared checks below. A successful result can be
"existing coverage is sufficient"; it need not add a generic theorem. Record
which bridge facts remain genuinely language-specific, and which surveyed
claims were narrowed or refuted.

## Item gates and outcomes

| Item | Question and target | Required evidence before admission |
| --- | --- | --- |
| 02: ordinal response (accepted, EXP-174/D79) | Can strict Nash, improvement paths, and an ordinal-potential existence theorem use `Ranking` and explicit order laws? | A nonnumeric preference consumer; expected-utility specialization with its definedness guard; partial-preference separation; finite maximization assumptions stated precisely. Generalize one dependency chain before adding adjacent concepts such as properness. |
| 03: mixture closure (binary-only refuted, EXP-175/D80) | Which law is sufficient for mixed dominance and pure-deviation reduction? | Separate binary mixing, finite iteration, and closure under arbitrary PMF `bind`. Test infinite-support mixtures and retain actual compared-law expectation premises. Compare named hypotheses with a proposed reusable law; do not call binary convexity countable betweenness. |
| 04: Protocol judgment (local comparison accepted, EXP-176/D81) | Can comparison of continuation laws be separated from numerical continuation evaluation? | Preserve candidate and alternative expectation-definedness in the numerical specialization; a nonnumeric local-optimality consumer; existing terminal rationality, Bayes consistency, and proper-subgame semantics preserved. Historywise one-shot results must retain their exact scope and the recorded SPE counterexamples. |
| 05: coalition judgment (local agreement accepted, EXP-177/D82) | Does strict unanimity provide useful shared transport for strong Nash and matching? | Incomparability example distinguishing absence of strict gain from weak equilibrium; nonempty-coalition policy; per-member quantifiers; agreement under explicit totality. Any change of meaning requires a decision, not a silent restatement. |
| 06: arena and deviations (existing interface retained, EXP-178/D83) | Is a more general deviation carrier needed by a named client? | A client the current local scheme cannot express, plus explicit locality and law-linearity enforcement or a demonstrated boundary explaining why they do not apply. Re-run the recommendation-spying and nonmember-coordinate controls. Compare with a separate consumer-local interface before replacing the static core. |

These are investigation gates, not a promise to add six interfaces. Reorder or
stop after an item when its evidence changes the useful next question. Items
03–06 require fresh competing designs and an experiment reservation before
architecture-sensitive implementation begins. EXP-173 does not pre-approve
their APIs. Ordinal recovery needs a new design experiment only if it changes
accepted foundations rather than generalizing on the settled API.

## Measurements and validation contract

Before editing each slice, record its baseline commit and inspect the actual
declarations and Mathlib APIs. Keep alternative probes and raw diagnostics in
ignored `.codex/scratch/`, never in `.lake/`. Compile one definition or theorem
at a time after inspecting its goal. Rebuild changed imports before downstream
single-file checks.

Measure declaration, construction, and client nonblank lines separately;
charge shared infrastructure once and report cold and reused costs. Compare
equivalent statements, include actual-law guards equally, and retain failed
alternatives. Use at least three alternating serialized runs for elaboration
comparisons; distinguish import-inclusive process time from command time.
Record exact commands, dependency/toolchain identity, and medians.

The D7/D60 budgets are the initial rejection thresholds for new bundled
abstractions: declaration plus construction above twice the direct baseline,
or more than 25% elaboration overhead, rejects or narrows admission. A new
record also needs two independent consumers or checked composition and must
enable a theorem not already supplied by the existing concrete surface.
Theorem-only alternatives should demonstrate reduced duplication or genuinely
useful generality without importing an unused abstraction. Do not conceal a
failed cold-cost budget behind shorter client code.

Every accepted slice needs a positive canonical consumer, a nearby rejection,
preservation of the old specialization, no new trusted axioms or proof holes,
and no forbidden dependency or source-level transport plumbing. Run:

```text
lake --iofail build <changed-owner-and-consumer-targets>
python scripts/audit.py --source-only
```

When adding, moving, or deleting authored modules, update both lint and axiom
drivers, clear deleted modules' generated build artifacts, then rebuild the
lint driver before `lake lint`. Run the appropriate transitive axiom checks for
the changed scope. Full audit belongs at an integration gate or when imports
or package configuration change, rather than each proof iteration.

Record observations and outcomes in the owning EXP entry; synthesize adopted
architectural consequences in a decision record citing that entry. Update the
owning [delivery ledger](DeliveryLedger.md) row in the same integration commit
as the evidence. This plan tracks questions and gates; the ledger tracks
delivered capability. Keep experiment and decision identifiers out of stable
Lean docstrings.
