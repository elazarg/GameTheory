# Family Survey: F7 (Value / Minimax / Welfare)

Input:

- [F7TheoremInventory.csv](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F7TheoremInventory.csv)
- [F7TheoremBlockMap.csv](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F7TheoremBlockMap.csv)
- [F7BlockCounts.json](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F7BlockCounts.json)
- [F7FileCounts.json](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F7FileCounts.json)

Theorem count in F7: 25

## Structural distribution (primary block)

- `B9` inequality/algebra transfer: 22
- `B7` recursive value/extremal argument: 2
- `B0` predicate decomposition: 1

Interpretation:

1. Most theorems are algebraic conversions among objective functionals (`eu`, welfare, constant-sum/zero-sum equalities).
2. The actual minimax core is concentrated in two theorems: `von_neumann_minimax` and `IsZeroSum.nash_interchangeable`.
3. A useful split for extraction is:
   - objective-rewrite layer (`B9`),
   - extremal-existence layer (`B7`).

## Highest-density files

1. `MinimaxTheorem.lean` (6)
2. `ConstantSum.lean` (4)
3. `PriceOfAnarchy.lean` (4)
4. `TeamGame.lean` (3)

## Reusable non-domain cores suggested by F7

## V1. Functional identity transport (`B9`)

Schema:

- if two objective functionals are pointwise affine-equivalent, optimization and comparison statements transfer directly.

## V2. Extremal sandwich (`B7`)

Schema:

- lower-bound guarantee + upper-bound cap + shared feasible witness yields equality of value bounds.

## V3. Saddle/fixed-point equivalence (`B7 + B9`)

Schema:

- a two-sided local optimality condition can be rewritten as a fixed-point relation once objective rewrites are normalized.

## Next action for F7

1. Extract one standalone extremal sandwich lemma independent of game-specific names.
2. Isolate a commutation-normalization lemma used by interchangeability (`update` cross-profile equality).
3. Link these with F3 backward-induction templates under one shared recursion interface.
