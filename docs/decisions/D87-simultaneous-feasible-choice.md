# D87: simultaneous feasible choice without a generalized-game record

- **Status:** selected after complete focused validation; integration validation pending.
- **Date:** 2026-11-11
- **Experiment:** EXP-182

## Question and competing designs

Can existing mathematical building blocks express simultaneous optimality
when available choices depend on the other coordinates? Compare ordinary
Nash filtered by a feasible-profile predicate, direct affordable local
judgments, and a shared fixed-point theorem for feasible maximizers. Keep
the finite-simplex local-lottery theorem as a production consumer.

No new problem, choice, welfare or generalized-game record is proposed.
D5's law-equilibrium and recommendation locality remain unchanged; D12 keeps
the fixed-point dependency inside `Analysis`. The existing payoff-threshold
meaning of `Core.ConstrainedNash` is not repurposed.

## Native shared-capacity discriminator

Two players each choose a real quantity in `[0,1]` and value their own
quantity. The canonical deterministic `GameForm` retains both quantities;
its ordinary expected-utility Nash predicate and pure-law comparisons are
used unchanged. No finite enumeration of the interval is assumed.

Sharing one unit makes each player's affordable menu depend on the opponent's
quantity. The existing `Math.IsOptimalOn` expresses fixture-local optimality:
the incumbent is affordable, all allowed alternatives are affordable, and
none has a larger own quantity. The predicate is equivalent to the two
quantities summing to one. Ordinary product-game Nash instead makes both
quantities one, so no ordinary Nash profile meets the shared constraint.
The equal split is affordable and locally optimal but not ordinary Nash.

This refutes feasibility filtering as a replacement for endogenous available
deviations. It does not change the meaning of Nash or require a broader
law-transformer interface. The new condition has a profile-quantified local
choice shape and uses an existing judgment predicate.

## Shared analytic operation

`exists_feasibleChoice_fixedPoint` works in a finite product of finite-dimensional
real normed spaces, inside explicit nonempty compact convex outer sets.
Each coordinate has a nonempty feasible menu within its outer set, closed
feasibility graph, lower hemicontinuity and a jointly continuous real objective
quasiconcave on that menu. The parameter point stays fixed during comparison.

The theorem derives compact menus from closed fibers inside compact outer
sets. Quasiconcavity already supplies convex menus and convex maximizer sets;
neither fact is stored again as a redundant certificate. Mathlib supplies
compact maximizer existence and quasiconcavity calculus. The preceding
`Math.isClosed_feasibleMaximizers` supplies the coordinate graphs. Their
product then consumes the same external Kakutani theorem as before.

The outer product is an envelope, not necessarily the jointly feasible set.
For the quantity game it includes `(1,1)`; the fixed-point conclusion enforces
affordability separately. Nonempty menus are required at every envelope point.

The result is simultaneous feasible maximization, with one objective per
coordinate and no interpersonal sum. It is not by itself an assertion about
any particular game's incentives. Such a caller must prove its objective and
feasible alternatives match the native comparison semantics.

## Consumers and limits

The local-lottery theorem specializes the operation to constant simplex menus
and affine finite expected scores. Its public statement and existing terminal
and belief consumers must stay unchanged; its original bespoke fixed-point
construction is replaced rather than retained as another engine.

The quantity consumer proves each changing menu is `[0,1-opponentQuantity]`,
with continuous clipping recovering feasible alternatives. The shared theorem
constructs an analytic point, and explicit menu and score bridges recover
the canonical interval-strategy profile's guarded affordable judgments.
The separation from ordinary Nash is then a theorem about that same profile.
The analytic consumer also proves existence for arbitrary continuous
quasiconcave objectives on that changing-menu family; the explicit equal-split
witness is an independent control for the own-quantity instance, not a claim
that invoking Kakutani is needed to find that particular point.

Continuous scores alone do not imply convex maximizers: squared quantity on
`[-1,1]` maximizes at both endpoints but not their midpoint. The free-good
example from EXP-181 separately retains the lower-hemicontinuity failure.
Nonempty menus on the common product envelope are a genuine premise, not a
claim about every shared-resource or generalized game. No unrestricted
market-clearing theorem, mixed-law constrained equilibrium, infinite-dimensional
extension or stable generalized-game data representation is admitted.

## Validation and cost

Baseline `bbd5add1`; Lean 4.35.0 / Mathlib v4.35.0. The direct baseline is
the complete existing `exists_localChoice_fixedPoint` proof, not merely its
Kakutani call. Shared infrastructure, the specialized client and the independent
quantity construction are charged separately. Exact measurements and focused
and integration commands are recorded in EXP-182 before collection. No new
record candidate or performance advantage is claimed.

Using `scripts.audit.source_code` to mask comments and count nonblank lines,
the old production proof body has 92 lines and the specialization has 39.
The shared declaration and proof add 72 lines, giving a cold source footprint
of 111 rather than 92 for that one consumer. The independent quantity menu
definitions, hypotheses and family instantiations add 91 lines, charged
separately rather than hidden behind the short existence call. No speed or
elaboration advantage is claimed, and no record/certificate budget is being
amortized. The useful gain is replacing a bespoke proof by a genuine
changing-menu operation with an independent constraint-family consumer.

Exact commands:

```text
lake --iofail build GameTheory.Analysis.FeasibleChoiceFixedPoint
lake --iofail build GameTheory.Analysis.LocalChoiceFixedPoint GameTheory.Experimental.Exp182.SharedCapacity GameTheory.Analysis.FeasibleChoiceFixedPointTest
python scripts/audit.py --source-only
python scripts/audit.py
```

The standalone analytic theorem passes 3,194 strict build jobs; complete
production and consumer controls pass 3,655 jobs, and source checks pass.
The native fixture stays under `Experimental/Exp182`; the analytic consumer
lives under `Analysis/FeasibleChoiceFixedPointTest` to preserve D12's one-way
dependency boundary. Independent read-only semantic review accepts the
frozen-parameter semantics, derived compactness, per-coordinate objectives,
native game bridge and convexity rejection scope. Integration evidence is
recorded in EXP-182 before collection.
