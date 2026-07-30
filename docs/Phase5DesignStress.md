# Phase 5: stressing the design under theorem load

Status: open. The mode is neither validation nor harvesting.

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

## Axes not yet stressed

Each of these is a part of the subject the design has never been asked about,
listed with the choice it would put pressure on.

*Repeated play and the folk theorem.* Stresses the protocol layer's
composability, and needs limits — so it also tests whether the analytic boundary
is drawn in the right place, or whether a second class of theorem wants to live
above it.

*Sequential equilibrium.* Consistency is a limit of completely mixed behavioral
profiles, which puts topology on strategies rather than on outcomes — the first
thing that would want the analytic root to reach *down* into the protocol layer
rather than up from the static core. That theorem is a predicted D12
renegotiation, not an exception to the current boundary: before any
implementation, compete and measure a second one-way analytic bridge root that
imports Protocol and the required topology while Protocol itself remains
analysis-free. As with the static bridge, negative probes must keep the
dependency unreachable from Protocol and positive probes must show it is
actually reachable from the new root.
