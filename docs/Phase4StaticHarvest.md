# Phase 4: the static harvest

Status: complete. Seven theorem families and one language encoding recovered
against the accepted API, each instantiated, none requiring a change to it.

This status is scoped to the static harvest recorded here. It does not claim
that every deliverable originally listed under RFC Phase 4 is complete: the
exact frozen transfers T1, T3, and T4, the minimal public D8 transformation
surface, and several provisional domain probes remain delivery obligations.
They are reconciled explicitly in
[`PostArchitectureDeliveryPlan.md`](PostArchitectureDeliveryPlan.md) and
[`DeliveryLedger.md`](DeliveryLedger.md).

The mode here differs from the earlier phases. Those validated architecture by
pushing hostile slices at it; this one assumes the architecture and asks whether
ordinary mathematics goes through on it. The measure of success is therefore
*absence of friction*: no definition was widened, no interface was renegotiated,
and the only additions to the law type are general facts that had consumers in
the same commit.

## What was recovered

| Family | Where | The theorem that carries it |
|---|---|---|
| iterated strict dominance | `Core/Response.lean` | a strictly dominated strategy is never rationalizable, with nothing assumed about what beats it |
| Pareto comparisons | `Core/Response.lean` | a strong equilibrium is weakly Pareto efficient |
| the correlated hierarchy | `Core/Equilibrium.lean` | both correlated concepts are closed under mixing; Nash sits inside them |
| potential games | `Core/Potential.lean` | a finite potential game has a pure equilibrium |
| the mixed extension | `Core/Mixed.lean` | pure equilibria survive it, and a mixed equilibrium is indifferent across its own support |
| existence | `Analysis/Nash.lean` | every finite game has an equilibrium in mixed strategies |
| zero-sum values | `Core/ZeroSum.lean`, `Analysis/Minimax.lean` | a two-player zero-sum game has a value, and only one |

The first five are instantiated in `Examples/Classic.lean` on the Prisoner's
Dilemma, in the style the file already used: the finite frontend supplies one
computed fact and the semantic layer carries it the rest of the way. Cooperation
is strictly dominated *by computation*; that it is never rationalizable and
never played in equilibrium follows *by theorem*. The last two are instantiated
on matching pennies in `Analysis/Examples.lean`, which is inside the analytic
root because nothing outside it may import that root.

## Hypotheses that earn their place

Four hypotheses in this pass are not technical noise, and each is documented
where it appears rather than hidden behind an instance.

*A witness profile*, for "a dominant strategy is never strictly dominated". With
no profile at all, strict dominance is vacuous and every strategy dominates
every other, so the statement is false without an inhabitant. Lean rejected the
version without it.

*Convexity of the preference*, for closure of the correlated concepts under
mixing. Nothing forces a weak preference to respect mixing; expected utility
does, and that is proved rather than assumed.

*Expected utility specifically*, for survival of the mixed extension. A pure
equilibrium resists only pure deviations while the mixed game offers a law over
them, and what closes the gap is that the deviator's utility is the *average* of
the pure ones. A preference that does not respect averaging has no reason to
survive the embedding.

*A nonempty finite strategy set per player*, for existence. Finiteness is what
makes the polytope compact and the payoff polynomial; nonemptiness is what makes
it a polytope at all. A player with nothing to play has an empty simplex, and
the fixed-point theorem has nothing to say about an empty set.

## Where the theorems stop, stated rather than skirted

*Strong equilibrium gives only weak Pareto efficiency.* An equilibrium against
coalitions objects when every member gains; Pareto domination allows some
members to be indifferent, and is the stronger demand. The Prisoner's Dilemma
exhibits the gap: mutual defection is weakly Pareto efficient and is not Pareto
efficient.

*Nash equilibria are not convex.* Mixing two of them correlates the players,
which is exactly what a Nash profile may not do. The correlated concepts survive
because each compares a composition of the status quo against another
composition of the same status quo, and composition is affine in the law it
composes with.

*A potential buys existence and nothing else.* It constrains unilateral changes
only, so it says nothing about coalitions and nothing about efficiency.

*The fixed-point theorem exhibits nothing.* It produces an equilibrium and no
description of one — not which, not how many, not how to find it. Matching
pennies makes the division of labour visible: the frontend decides by
enumeration that it has no pure equilibrium, and the fixed-point argument
asserts without exhibiting that it has a mixed one. The executable frontend is
still the only thing here that computes an equilibrium.

## The analytic root

Everything that needs convexity or topology lives under `GameTheory/Analysis`,
which no other module imports. That is a boundary rather than a directory: a
file importing the fixed-point theorem can see all of `stdSimplex` and
`Polynomial`, the two constants the audit requires the core and the executable
frontend never to reach. Both the containment and the leak are measured — the
existing six absence probes still pass, and a seventh and eighth probe assert
that the analytic root does reach both, so the budget cannot quietly stop being
spent where it was allowed.

The root has four modules and one obligation each. `Simplex.lean` presents a
law on a finite carrier as a point of the standard simplex and recovers it,
which is where the dependency actually enters. `Payoff.lean` rewrites expected
utility as a polynomial in the weights, which is what makes it continuous and,
more importantly, affine in one player's own coordinates. `Nash.lean` applies
Kakutani's theorem to the best-reply correspondence.

`Minimax.lean` is the fourth and is deliberately three lines long. Sion's
theorem in Mathlib would have proved the same result independently; taking it
that way would have put the zero-sum theory above the analytic boundary for no
reason, since only *existence* needs a fixed point. So the definitions, the
correspondence between a zero-sum equilibrium and a saddle point, and the
uniqueness of the value all sit in `Core/ZeroSum.lean` with no topology
anywhere, and the analytic root contributes the one thing that cannot be had
without it.

## The mechanism-design encoding

`Languages/Mechanism.lean` is the capability-light static counterpart to the
sequential encodings. It contains only mechanism data and its structural
compiler; incentive and equilibrium results live in `Mechanism.Strategyproof`.

Its finding is a negative one, which is the useful kind here. Mechanism design
needed no new solution concept. In the coordinated solution leaf,
*strategyproofness is `IsDominantProfile`* of the induced game form with the
truthful profile substituted, and `isStrategyproof_iff` unfolds to the
pointwise inequality. No fake agents, no extension of the game form, and no
second notion of dominance are introduced.

The instance is the two-bidder second-price auction, where truthful bidding is
dominant, paired with the first-price auction, where it is refuted. The second
half is what makes the first informative: an encoding in which no report ever
mattered would satisfy the strategyproofness theorem and fail the refutation.

The concessions are listed in the module and are worth one summary line here:
two bidders rather than `n`, real-valued money — so neither the executable
frontend nor the existence theorem can touch these games — no revelation
principle, no participation or budget conditions, and the truthful profile
supplied as a parameter rather than derived.

## Additions to the law type

Five, each with a consumer in the same commit: composition is affine in the law
it composes with; an expectation is bounded by a bound its support respects; an
average that attains its bound attains it everywhere it looks; and the strict
version underneath that.

## Measurements

```text
lake build
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
```

| Measure | Value |
|---|---:|
| `GameTheory/Core` theorems | 108 |
| `GameTheory/Core` modules | 10 |
| interface changes required by the harvest | 0 |
| `sorry`, `admit`, `native_decide`, custom axioms | 0 |
| transport tokens added to the static layer | 0 |
| `GameTheory/Analysis` nonblank lines | 412 |
| language modules | 3 |
| transport tokens in the analytic root | 0 |
| modules outside the root importing it | 0 |
| absence probes still passing | 6 |
| reachability probes firing inside the root | 2 |

## Outstanding

- Whether any of the comparison design's four and a half thousand lines above the same dependency
  (Schauder, KKM, Scarf, the simplex approximation layer) is worth porting. The
  existence theorem here needed none of it, so the question is what *else* would
  need it, and nothing yet does.
