# Uniform-Equilibrium Research and Formalization Method

## Purpose

This document is the stable coordination method for three distinct activities:

- [MathResearchMethod.md](methods/MathResearchMethod.md) — how mathematical claims are
  formulated, tested, proved, refuted, and made formalization-ready;
- [LeanFormalizationMethod.md](methods/LeanFormalizationMethod.md) — how stable
  mathematics is represented, checked, integrated, and used to expose new
  mathematical obligations;
- [ParallelResearchMethod.md](methods/ParallelResearchMethod.md) — how independent
  investigations are scoped and promoted when they become relevant.

The dated, changing theorem boundary and working hypotheses are in
[UniformEquilibriumCurrentFrontier.md](../../ephemeral/UniformEquilibriumCurrentFrontier.md).
The current strategic interpretation and the separate root-math/formal-adapter
queues are in
[UniformEquilibriumStrategicSynthesis.md](../../ephemeral/UniformEquilibriumStrategicSynthesis.md).
Detailed historical evidence remains in
[ProofScaffoldingReview.md](audits/ProofScaffoldingReview.md),
[LeanSettlementAudit.md](audits/LeanSettlementAudit.md), and the
[progress monitor](../../ephemeral/progress-monitor/).
Focused adversarial checks that may rely on repository context live in
[`reviews/`](../../ephemeral/reviews/); unlike the launch questions, these review packets need
not restate the whole model.

## Semantic waist

The stable endpoint of the project is the semantic constructor:

~~~text
there exists a payoff v such that, for every accuracy,
one profile delivers v and caps every unilateral deviation
uniformly over all sufficiently long horizons.
~~~

This is equivalent to existence of a uniform-equilibrium payoff. Analytic,
recursive, potential, occupation, and monitoring arguments are construction
languages for reaching this semantic waist.

No intermediate certificate is presumed universally complete merely because
it is convenient to compose or formalize. Different classes may reach the
semantic waist through different sound consumers.

## Three levels of claim

Every proposed architecture or certificate theorem is classified at three
separate levels:

| Level | Question |
|---|---|
| **Verification** | Does a supplied finite object imply delivery and uniform unilateral-deviation caps? |
| **Bounded synthesis** | For a fixed controller class, size bound, or update skeleton, can such an object be found or refuted? |
| **Strategy-class coverage** | Does every semantic uniform-equilibrium payoff admit an object in that class? |

A theorem at one level receives no automatic credit at either higher level.
In particular, an exact verifier for a fixed finite public architecture is not
an architecture producer, and a bounded-template synthesis theorem is not a
completeness theorem for unrestricted or private-history strategies.

The quantifier over accuracy is also explicit. A uniform-equilibrium payoff
may use a different profile or architecture for each requested accuracy; the
payoff target remains fixed. Architecture size may therefore depend on the
accuracy unless a stronger theorem proves otherwise.

For any proposed finite proof language, separate exact-object existence from
accuracy-indexed density. The root-relevant quantity is the infimum of the
full semantic deviation gap over all permitted object sizes, with every
boundary action such as Never retained. An exact zero, a bounded size, a
nonsingular witness, or convergence inside one fixed parameter space is an
additional theorem, not part of approximate production by default. Likewise,
a strategically convenient contracting subclass must be compared against its
noncontracting boundary before it is advertised as complete.

The strategy and observation class is part of every level. Public finite
state, private randomized finite memory, clock dependence, and unrestricted
behavior are not interchangeable representations without a proved compiler.

## Bidirectional workflow

~~~text
mathematical statement -> proof or exact counterexample
         |                         |
         v                         v
formalization packet         corrected search space
         |
         v
checked kernel -> actual-data adapter -> downstream consumer
         |
         +---- failed quantifier/interface/test ----> math question
~~~

Mathematics determines the statement. Lean tests its exact quantifiers,
dependencies, and composability. Lean may expose a missing theorem or false
interface, but it may not silently weaken a statement until it compiles.

## Mathematics-to-Lean handoff

A result is ready only when it contains:

1. a self-contained statement with the exact strategy and randomness model;
2. a complete proof or finite counterexample;
3. concrete input and output data rather than the desired conclusion hidden
   in a record field;
4. quantitative constants and the relevant expectation, conditioning,
   prefix, shift, restart, and stopping conventions;
5. positive and negative tests;
6. the actual data expected to supply its hypotheses;
7. the downstream theorem expected to consume its output.

For an equivalence or exhaustive alternative, the packet must additionally
identify the exact class over which necessity is claimed and expand every
invoked representation theorem. A standard theorem cited only by name may
justify mathematical confidence, but its hypotheses and multichain,
reachability, or information details must be exposed before Lean is asked to
freeze the converse.

## Lean-to-mathematics handoff

A mathematical blockage is returned as one self-contained question,
preferably with the smallest failed finite model. Definitional inconvenience,
missing library infrastructure, and mathematical gaps are classified
separately.

The formalization may refine a statement by exposing an omitted hypothesis.
It may not treat the refined conditional theorem as a solution of the original
unconditional problem.

## Progress accounting

Use four independent evidence seals:

| Seal | Evidence |
|---|---|
| M | rigorous mathematics or a rigorous counterexample |
| L | checked Lean declaration |
| A | checked adapter from actual source data |
| C | checked consumer producing semantic closure or a valid recursive output |

The record is append-only. Refutations supersede earlier claims without
erasing the knowledge gained. LOC, interface count, and conditional wrappers
do not earn closure credit.

The four seals are recorded at the claim level above. Thus a checked
fixed-architecture verifier can have `M+L+C` while the bounded producer and
strategy-class coverage claims remain open. Status prose must say which level
each seal belongs to.

When a later result refutes a calibration example or premise, correct the
claim at its source and mark downstream live summaries as superseded. A
historical record may retain the failed argument only when it is unmistakably
labelled false and the surviving lesson is stated separately.

## Scheduling discipline

Schedule by objective priority, not by the arrival time of an answer or file.
The default ordering criteria are:

1. dependency distance to the semantic waist and the number of downstream
   claims unblocked;
2. risk that a false premise is already being consumed;
3. value of a finite counterexample or regression theorem in protecting the
   interface;
4. mathematical readiness for honest formalization;
5. implementation cost and reversibility.

Recency is only a tie-breaker. A new answer enters the audit queue and may
change priorities when it supplies a load-bearing theorem or refutation, but
it does not automatically preempt an older upstream obligation.

Keep at least one Lean lane continuously assigned to the highest-priority
formalization-ready result while such results remain. When a bounded milestone
is build-clean, integrate and commit it immediately with a path-limited commit;
do not wait to bundle unrelated work or include another worker's staged files.
Formalization priority follows the same objective ordering as mathematics: a
recent representational result is not promoted ahead of an upstream
credibility or root-boundary theorem merely because it arrived last.

## Separation rule

Methodology files change only when the way research or formalization should be
conducted changes. New theorems, counterexamples, current priorities, candidate
invariants, and beliefs about the next attainable result belong in
`UniformEquilibriumCurrentFrontier.md` or another dated status document.
