# D24: utility-game smoothness is a Core welfare operation

- **Status:** adopted and promoted
- **Date:** 2026-08-02
- **Experiment IDs:** EXP-052

## Decision / question

Where social welfare and Roughgarden smoothness belong relative to the
canonical `UtilityGame`, the opt-in congestion domain, and later robust
coarse-correlated-equilibrium consumers.

## Competing designs

1. Put aggregate expected utility, smoothness, and the pure Nash consequence
   in `GameTheory.Core.Welfare`; let domains import them one way.
2. Create a separate stable `GameTheory.Welfare` dependency root.
3. Define the first smoothness surface locally in `GameTheory.Congestion`.
4. Port the predecessor's generic optimum, best/worst-equilibrium, and
   price-of-anarchy ratio hierarchy together with smoothness.

Design 1 is adopted.  The three generic declarations use only canonical
expected utility, unilateral `Profile.update`, and `IsNash`.  A separate root
would isolate no additional dependency; congestion-local ownership would
duplicate a theorem meant for mechanisms and later CCE/no-regret consumers.
Design 4 adds total real division and extremum machinery before a theorem needs
them, and obscures the cost-to-negated-welfare convention at zero.

## Representative hostile slice

For finite-player atomic congestion games with nonnegative affine delays, the
experiment proves the integral Christodoulou--Koutsoupias inequality, aggregates
it into `(5/3, 1/3)` cost smoothness, translates it to `(5/3, -1/3)` utility
smoothness, and applies the generic Nash theorem to obtain the exact `5/2`
social-cost bound.  Pigou supplies an affine Nash witness of cost four against
an optimum of cost three; Braess supplies restricted and shortcut equilibria
of costs seven and eight, plus the destroyed split equilibrium.

## Measurements

| Measure | EXP-052 result |
|---|---|
| Mathlib overlap | no game-theoretic social-welfare, smoothness, or price-of-anarchy API found |
| `Core.Welfare` | 46 nonblank lines; three public declarations; direct import only `Core.Utility` |
| `Congestion.AffinePoA` | 140 nonblank lines; direct imports only `Congestion.Basic` and `Core.Welfare` |
| hostile examples | 210 nonblank lines; all 17 pinned declarations plus a named generic-bound consumer |
| focused public-root build | 1,744 jobs for `GameTheory.Core` and `GameTheory.Congestion` |
| full project build | 3,395 jobs |
| exact pinned accounting | foundational welfare row plus 4/4 smoothness, 8/8 affine PoA, and 17/17 examples reviewed |
| deferred rows | epsilon-CCE smoothness, exact CCE smoothness, and the affine correlated bound share one named finite-law gate |
| source hazards | zero placeholders, custom axioms, raw updates, transports, `Fintype.ofFinite`, or forbidden imports |
| axiom profile | `propext`, `Classical.choice`, and `Quot.sound` only |

## Kill condition

Reject Core ownership if the affine theorem needs a duplicate utility or Nash
predicate, stored finiteness, raw function update, a ratio API, Analysis or
Protocol, a domain-specific premise in the generic theorem, or a sign
convention that cannot state the cost result transparently.  Reject promotion
if the public umbrellas do not expose the intended leaves or the concrete
routing examples fail against the canonical profile/update API.

No kill condition fired.  Integration audit removed one avoidable tactic
import and required both promoted leaves to be reachable through their public
roots before the decision froze.

## Result and consequences

`GameTheory.Core.Welfare` owns only `UtilityGame.socialWelfare`,
`UtilityGame.IsSmooth`, and `UtilityGame.IsSmooth.nash_bound`.  Finiteness and
decidable equality remain assumptions on the operations that aggregate or
update.  The result is an inequality, not a possibly ill-behaved ratio.

`GameTheory.Congestion.AffinePoA` owns affine-delay and resource-aggregation
mathematics and the pure `5/2` theorem.  `GameTheory.Congestion.Examples` owns
the reader-facing Pigou and Braess witnesses.  The stable Core umbrella exports
the generic welfare surface; the opt-in Congestion umbrella exports the affine
theory without entering the main root.

The robust epsilon-CCE, exact CCE, and affine correlated-cost bounds remain one
explicit follow-up gate: define expected social welfare of a canonical
`FinDist` profile law and prove its compatibility with the existing
`IsεCoarseCorrelatedEq`/`IsCoarseCorrelatedEq` predicates.  This does not reopen
the pure API or justify the predecessor's generic ratio hierarchy.
