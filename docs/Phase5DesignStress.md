# Phase 5: stressing the design under theorem load

Status: named queue complete; retained as a standing design-stress protocol.

Phases 0–3 asked whether the architecture survives hostile slices. Phase 4 asked
whether ordinary mathematics goes through on it. This phase asks the question
that decides what the library costs over its lifetime: **when the next important
theorem arrives, does it land cheaply, or does it need machinery the design
should have made unnecessary?**

The test for a design choice here is not whether a theorem can be proved on it.
It is whether a theorem *from a part of the subject that has not been built yet*
can be stated without a parallel copy of something that already exists.

## The cost question, measured rather than feared

The concern that opened the phase was that the old library needed roughly four
and a half thousand lines of mathematics above the fixed-point dependency, and
that the same bill might come due again. It does not, and the reason is worth
recording because it is not the reason one would guess.

Those lines were never spent on equilibrium existence. Measured by import, in
the pinned snapshot:

| v1 module | lines | what consumes it |
|---|---:|---|
| `FixedPoint/Scarf` | 2554 | **nothing** |
| `LinearProgramming` | — | **nothing** |
| `SchauderFixedPoint` → `FixedPoint/KKM` | 444 | envy-free cake cutting, and nothing else |
| `Simplex` → `Minimax/Loomis` | ~1200 | Loomis's theorem, and through it Perron–Frobenius |
| `SimplexApproximation` | 134 | the folk theorem, all five importers |

Equilibrium existence in v1 went a different way entirely — Brouwer, via
`ProductSimplexBrouwer`, `NashExistenceMixed`, and `NashExistence`: **842
lines**. The same theorem here is **320**, because Kakutani applies directly to
the best-reply correspondence and the finite-support law type already presents a
point of the simplex.

So the bill is real but it is attached to *specific theorems* — fair division,
Loomis, the folk theorem — rather than to the architecture. The lesson for this
phase is that "will we need those lines" is the wrong question. The right one is
which upcoming theorems carry their own irreducible mathematics, and which are
paying a tax the design could remove.

## Findings

### The preference vocabulary was about lotteries by accident

Recorded as [EXP-024](ExperimentLog.md). Thirteen of the sixteen declarations in
`Core/Preference.lean` were relation algebra nailed to `FinDist Outcome`, which
none of them used; and every one of them was agent-indexed, so a *social*
ranking — one ranking, no agent — could not borrow any of it.

Nothing had asked, because every theorem to that point compared laws. Social
choice asks immediately: it ranks alternatives, and there is no probability
anywhere in it.

The repair splits the vocabulary rather than duplicating it. `Rank` states each
law for one comparison over an arbitrary carrier; `Preference` states it as that
law holding for every agent, and is definitionally that. The library rebuilt
with no downstream edit at all, because currying makes the new definitions defeq
to the old.

The downstream theorem is the Condorcet paradox, in `Examples/Voting.lean`:
three voters in rotation, each total and transitive, whose majority ranking
cycles. Individual rationality and social irrationality now read in the same
words.

Delegating to Mathlib was measured and rejected. Its bare-relation `Transitive`,
`Reflexive`, and `Total` are deprecated in favour of typeclasses, and a
preference here must stay an argument — one carrier is routinely studied under
several preferences at once.

### Arrow forced the semantic split to become a physical one

Recorded as [EXP-027](ExperimentLog.md). Arrow's theorem now runs from
unrestricted profiles of linear weak rankings through collective rationality,
strict Pareto, and IIA to an exact dictator. The public statement uses
`Ranking`, `Rank.Linear`, and `Rank.strict`; the Geanakoplos pivotal-voter proof
changes to strict relations only behind a private reflexive-closure bridge. The
pinned v1 proof supplied the theorem inventory and proof architecture without
restoring its parallel `PrefRel`/`PrefProfile`/`SWF` vocabulary.

The first reachability probe found the defect the Condorcet slice had missed.
The declarations were carrier-generic, but they still lived in
`Core/Preference.lean`, so importing `SocialChoice` quietly reached `FinDist`.
The repair gives relation algebra its own probability-free `Core/Rank.lean`;
lottery convexity and outcome-law relabeling stay in `Core/Preference.lean`.
Both `SocialChoice` and `Arrow` now reject the `FinDist` probe, and the Arrow
target's dependency closure fell from 1,715 to 842 jobs. The split is therefore
enforced by imports rather than described only by type signatures.

The three-voter/three-alternative witness shows the hypotheses are jointly
satisfiable, and the flagship's axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

### A coalitional game is not a game form, and that is the right answer

`Core/Coalitional.lean` states what each coalition can guarantee itself, the
core, and two theorems: a core allocation is individually rational, and the
three-player majority game has no core allocation at all.

The finding is the *absence* of reuse, and it is deliberate rather than a
failure. A coalitional game has no strategies, no play, and no outcome carrier,
so it is not a `GameForm` and forcing it into one would mean inventing a strategy
space nobody uses and an outcome nobody observes. The module says so where a
reader will meet it.

What is shared is the vocabulary of groups: a coalition is a `Finset Agent` for
the same reason it is one in a strong equilibrium's deviation, and the core's
condition has that deviation's shape — a group objects when it can do better by
itself. That is the correct amount of sharing, and it means `GameForm` is the
centre of the *non-cooperative* theory rather than of the subject.

The impossibility is the load-bearing half. Without it the core would look like
a solution concept rather than one that routinely fails to exist, which is the
fact every other cooperative concept is a response to.

EXP-028 supplies the other half. The Shapley allocation is the weighted sum of
marginal contributions on the same `CoalitionalGame`; finiteness remains a
capability of the operation, not a field of the game. Efficiency, symmetry,
the null-player law, and additivity are named properties of allocation rules,
and the unanimity-basis decomposition proves that those four properties
characterize the Shapley value uniquely.

The existing majority game is the discriminating witness. It still has no core
allocation, but symmetry and efficiency give every agent Shapley value `1/3`;
any allocation rule satisfying the four axioms agrees with that allocation.
No strategy, outcome, probability, `GameForm`, or generic certificate enters
the proof. The theorem therefore confirms the earlier absence-of-reuse finding:
the parallel primitive was not merely enough to state the core, but enough for
the cooperative theory's canonical always-existing value and its flagship
characterization.

`GameTheory.Tests.Shapley` builds in 1,070 jobs. `Shapley` rejects reachability
probes for `FinDist`, `GameForm`, and `Polynomial`, and both efficiency and the
characterization use only `propext`, `Classical.choice`, and `Quot.sound`.

### Bayesian syntax and interim theory separate at the right boundary

Recorded as [EXP-029](ExperimentLog.md). EXP-008's common-prior scope probe is
now stable in two physically separated core modules. `Core/Bayesian.lean`
contains only types, actions, the prior, payoff data, and the direct game-form
compiler. `Core/BayesianEquilibrium.lean` adds the prior-weighted interim value
and proves ordinary `IsNash` equivalent to optimality at every own type. The
game stores neither type finiteness nor decidable equality; those capabilities
appear only on the decomposition theorem that enumerates types.

`Languages/Bayesian.lean` imports the data module but not the equilibrium
module. Its two-step protocol draws the full type profile at chance, gives each
player a `View` carrying only its own type, and then asks all players to act
simultaneously. Local policies and contingent plans are exactly equivalent.
After two steps, the protocol-backed outcome law is the direct form's law
mapped entirely to completed outcomes. Thus the compiler knows nothing about
Nash, while the typed fair-bit test can transfer truthful Nash to the compiled
information-local form with the ordinary predicate.

This closes the ambiguity left by EXP-008. Bayesian games need coordinated
static and information presentations, but they do not need a second evaluator,
preference, or equilibrium concept. The split is architectural rather than
organizational: the language compiler cannot reach the solution-concept module
through its authored import graph.

### Repeated play shares histories with Protocol, not infinite-path laws

Recorded as [EXP-030](ExperimentLog.md). A history-dependent repeated strategy
now consumes the same chronological list of public stage profiles that the
finite Protocol bridge uses as its execution and information state. The first
candidate used a dependent `Fin t → Profile` history; merely identifying it with
the protocol prefix demanded proof-dependent transport. The hostile slice
therefore changed the foundational representation before any broad theorem
port: list length is the period, and native recursion and finite execution now
agree definitionally.

The three-stage coordination witness is deliberately history-dependent: every
player flips the previous public action, so the exact protocol law exercises
the accumulated history rather than only a horizon counter. Discounted utility
evaluates the deterministic native path, and the stationary-repetition theorem
concludes ordinary `IsNash` from an ordinary stage Nash hypothesis. There is no
repeated-specific equilibrium predicate and no stochastic law over an entire
infinite path.

The package split is now enforced. Basic and Discounted cannot reach Protocol;
the Protocol bridge cannot reach discounted payoff; positive probes show that
the bridge still consumes both `repeatedPlay` and `InformationModel`. Basic and
Discounted also reject all four `stdSimplex`/`Polynomial` probes. This validates
the stagewise/finite-prefix half of D11 and D12, not the folk theorem's analytic
geometry.

### The folk theorem needs a bridge, not a second repeated-game theory

Recorded as [EXP-031](ExperimentLog.md). The flagship now states that every
feasible payoff strictly above the opponent-minmax vector is approached by
normalized discounted payoffs of history-dependent Nash profiles in the
observable mixed-action repeated game. The conclusion uses the existing
`UtilityGame.mixed`, deterministic `repeatedPlay`, discounted utility, and
ordinary `IsNash`; it adds no repeated-equilibrium wrapper or law over an
infinite realized path.

The dependency split follows the mathematics. Bellman continuation, finite
periodic paths, discount-factor convergence, first-mismatch detection, and
trigger incentives are reusable stable repeated theory. Convex feasibility,
the opponent-minmax construction, and the existence theorem form the one-way
`GameTheory.Analysis.Repeated` bridge. Residual-floor denominator clearing is
game-independent and therefore lives in the separately audited
`GameTheoryMath` target. The 255-line unused ambient geometry and 328-line
general security hierarchy in the apparent v1 support closure were not ported.

The probes make the split physical. Basic, Discounted, and the public Repeated
root all reject `stdSimplex` and `Polynomial`; the bridge positively reaches a
trigger profile, opponent minmax, and the generic residual-floor construction,
but cannot reach Protocol; the math target cannot reach `UtilityGame`. Each
source bucket has zero transport tokens.

Prisoner's Dilemma is the honest witness. Mutual cooperation is feasible,
permanent defection bounds every mixed best response by one, and the theorem
produces sufficiently patient repeated Nash profiles whose payoff approaches
three. Thus the hypotheses are not merely a polished empty interface.

### Sequential consistency needs history beliefs and an analytic Protocol bridge

Recorded as [EXP-032](ExperimentLog.md). The predicted D12 collision is now
measured rather than hypothetical. Stable Protocol owns a topology-free limit
schema; `GameTheory.Analysis.Protocol` specializes it to pointwise convergence
of fully mixed, Bayes-consistent behavioral assessments. Protocol cannot reach
the specialization, while positive probes show that the bridge still consumes
stable rationality and Bayes consistency. It also rejects the fixed-point
geometry used by the static existence layer.

The first hostile finding was below topology. A model's `InfoState` is a total
domain for policies and may contain values no history reaches. Indexing beliefs
by every raw value would then require a probability law on an empty history
fiber and could make assessments uninhabited. Beliefs live over complete
histories because distinct histories can merge into one execution state; their
state projection satisfies the existing `BeliefOn` predicate. Strategies remain
the existing `BehavioralPolicy`, and rationality remains
`Context.IsLocallyOptimal`.

A vanishing Boolean tremble is the minimal analytic witness: every approximant
has full support, but the pointwise limit is pure. The limit topology therefore
does real work without a measurable infinite-path law.

This closed the generic boundary question, not the language theorem. EXP-033
subsequently tested the language carrier separately.

### Finite EFG is a transparent specialization, not a second semantics

Recorded as [EXP-033](ExperimentLog.md). The pinned EFG syntax and sequential
adapter are 452 and 560 nonblank lines. The hostile slice did not justify
rebuilding them: `GameTheory.Languages.EFG` is a 52-line transparent bundle of
the accepted execution and information objects with tree-shapedness and a
single-mover law. Its analytic adapter supplies finite history fibers and
canonical continuation contexts to the generic predicate.

Nature privately selects a Boolean value before one player acts. The two
decision histories are distinct, have positive belief, and share the same
information state. That example exposed two semantic gaps. Reached inactive,
chance, and terminal observations are not decision information sets, so
`InformationSite` now also witnesses a nonterminal history and a genuine menu
action. The nonterminal evidence is explicit because Protocol permits `active`
to be arbitrary after play stops. And comparing only the local mixed action is
not sequential rationality without a one-shot deviation theorem, so
alternatives are now whole continuation behavioral policies.

The adapter passes three negative syntax probes, three positive syntax-input
probes, and three positive bridge probes. This validates the presentation and
the proposition, not the exhibited assessment as an equilibrium and not an
existence theorem.

EXP-034 closes that last concrete gap without changing the architecture. A
fully mixed action law gives both decisions positive support; the actual
behavioral runner assigns each hidden decision history probability `1 / 2`;
stable `bayesBelief` normalizes those reach masses; and the constant assessment
sequence proves consistency. With zero continuation payoff, the assessment is
an actual sequential equilibrium.

EXP-035 closes the remaining nonconstant-payoff stress on the same carrier.
Terminal payoff is one exactly when the action matches nature's hidden bit.
The acting history fiber is equivalent to `Bool`, the canonical Bayes belief is
the fair mixture over those histories, and every whole replacement behavioral
policy has continuation value `1 / 2`. The resulting assessment is a
sequential equilibrium without a second evaluator or an EFG-specific
rationality predicate. This remains a concrete witness, not a general finite
EFG existence theorem.

EXP-036 closes the separate well-founded strategic gap in stable Protocol.
History-preserving backward recursion is joined to the existing forward runner,
and subgame perfection over every whole replacement policy and every history is
equivalent to the absence of profitable one-shot deviations under
`ActsOnceWhereItMatters`. The hostile probe is optimal from the initial history
but fails at an off-path decision, so the result cannot be confused with an
initial-Nash converse. EFG syntax inherits this semantic layer; a thin
EFG-facing theorem remains ordinary recovery work.

## Current stress queue

The named Phase 5 queue is exhausted. Further theorem families that challenge
a recorded boundary should be reserved as new experiments rather than treated
as unmeasured extensions of the decisions above.

This does not mean the frozen Phase 0 flagships, transfers, or v1 theorem
inventory are complete. Routine recovery against an already validated domain
contract is harvesting and needs attribution plus coverage accounting, not a
new experiment. A theorem that challenges ownership, representation,
dependency direction, or another recorded boundary re-enters this stress
protocol through a reserved experiment.

The mutable queue, frozen-obligation reconciliation, domain gates, mature
blind-spot program, and Frontier capacity rules now live in
[`PostArchitectureDeliveryPlan.md`](PostArchitectureDeliveryPlan.md). Current
pinned-v1 recovery status lives in
[`V1CoverageLedger.md`](V1CoverageLedger.md).
