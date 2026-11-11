# D90: restricted budgets do not identify a complete ranking

- **Status:** nonidentification proved; keep ordinary menus and existing choice operations.
- **Date:** 2026-11-11
- **Experiment:** EXP-185

## Question and alternatives

Does observing demand at a fixed positive price vector for every wealth level
identify the ranking rationalized by all-finite-menu choice? Compare existing
filtered finite menus and `Math.FiniteChoice.best` with introducing a restricted
demand record that purports to recover the ranking. The question concerns
identification, not whether observations admit any rationalization.

## Hostile evidence

The alternatives are the six indivisible bundles `(x,y) ∈ ℕ²` with total
quantity at most two. Scores `u = 5x + 2y` and `v = 5x + 2y²` strictly value
a unit increment of either commodity. They define complete transitive rankings
and globally WARP-consistent greatest-element choice.

At prices `(1,1)`, the full correspondences agree for every real wealth:
negative wealth has no feasible alternative; wealth in `[0,1)` chooses zero;
`[1,2)` chooses `(1,0)`; wealth at least two chooses `(2,0)`. In particular,
this is an entire budget family, not one or two selected observations.
Nevertheless `u` strictly prefers `(1,1)` to `(0,2)`, whereas `v` reverses that
comparison. At prices `(2,1)` and wealth three, the actual optimal choices are
respectively the singleton `(1,1)` and the singleton `(0,2)`.

All choices use the canonical `FiniteChoice.best` on an actual affordability
filter, retaining every maximizing alternative. Both global correspondences
satisfy the existing weak axiom. Thus restricted observations fail to identify
this comparison even under consistent numerical rationalizations and positive
commodity increments. This does not refute rationalization existence, assert
failure of every richer observation domain, or establish a continuous, concave,
Afriat-style demand representation theorem.

## Decision and validation

No new choice or demand record is needed to express the observations, the
ambiguity, or the distinguishing budget. Observation-domain richness is a
hypothesis of a proposed representation theorem, not a field to hide inside
an abstraction. D84's binary/triple-menu requirements remain meaningful.
Native budgets and the counterexample stay experimental.

`Experimental.Exp185.RestrictedBudget` builds strictly in 958 jobs;
`python scripts/audit.py --source-only` passes. The full integration result
is recorded in EXP-185. No alternative record implementation was timed and no
performance advantage is claimed.
