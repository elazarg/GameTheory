# P-COAL: balancedness from a core allocation

Title: Finite core allocations certify balancedness
Family ID: P-COAL
Pinned roots: `GameTheory/Cooperative/CoalitionalGame/Core.lean`; `GameTheory/Cooperative/CoalitionalGame/Bondareva.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `6181b57`
Canonical destination: `GameTheory.Core.Coalitional`; `GameTheory.Cooperative.Balancedness`
Domain contract / decision: D9; post-architecture P-COAL BFS gate
Owner: Wave 4 / cooperative games
Status: complete bounded package; all 5 declarations adapted with no deferred rows
Last verified: 2026-08-09

The successor keeps the characteristic-function game, allocations, payouts,
and core predicate in canonical Core.  The opt-in Cooperative leaf adds only
balanced collections, balanced games, and the finite double-counting theorem
that a core allocation certifies balancedness.  Finiteness remains an argument
capability of those definitions and the theorem; it is not stored in a game or
certificate structure.

This is exactly the direction proved by the pinned `Bondareva.lean`.  The
converse—balancedness implies a nonempty core—is explicitly absent from v1 and
requires a separate finite-dimensional Farkas/duality development.  This
ledger therefore does not claim the full Bondareva--Shapley equivalence or
close the cooperative domain gate.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Cooperative/CoalitionalGame/Core.lean` | `IsCore.efficient` | theorem | adapt | `GameTheory.IsInCore.efficient` | focused Core build | Named projection of canonical core efficiency. |
| same | `IsCore.coalition_rational` | theorem | adapt | `GameTheory.IsInCore.coalition_rational` | focused Core build | Named projection of every coalition constraint. |
| `GameTheory/Cooperative/CoalitionalGame/Bondareva.lean` | `IsBalancedCollection` | def | adapt | `CoalitionalGame.IsBalancedCollection` | pair-half fixture | Nonnegative weights cover each agent with total weight one; they are not probabilities. |
| same | `IsBalanced` | def | adapt | `CoalitionalGame.IsBalanced` | majority negative fixture | The weighted coalition worth is bounded above by grand-coalition worth. |
| same | `IsCore.isBalanced` | theorem | adapt | `GameTheory.IsInCore.isBalanced` | focused theorem/test build | Finite double counting uses only the canonical payout and core projections. |

Disposition count: 5 adapted.

The hostile `Fin 3` fixture gives weight `1 / 2` to each two-agent coalition
and zero to every other coalition.  Each agent is covered twice, so the
collection is balanced, but its total weight and its weighted worth in the
canonical majority game are both `3 / 2`, while the grand coalition is worth
`1`.  Thus the majority game is not balanced.  This catches probability
normalization, per-agent coverage, and inequality-orientation mistakes and
provides a second route to its already checked empty-core conclusion.

Attribution: the named core projections and balancedness theorem are adapted
from the two pinned files above.  The successor removes the duplicate
`CoalGame` wrapper and applies the proof directly to `CoalitionalGame`,
`Allocation`, `payout`, and `IsInCore`.

Validation: the focused Core, Balancedness, Cooperative-root, and hostile-test
targets build warning-free.  The structural audit reaches all five intended
inputs through `GameTheory.Cooperative`, rejects all five strategic,
probability, Protocol, measurable, and Analysis boundaries from the focused
leaf, and rejects the three opt-in balancedness names from the lightweight
`GameTheory` root.  The public theorem and hostile fixture depend only on
`propext`, `Classical.choice`, and `Quot.sound`.  Exact coverage returns
`VERIFIED=1` at 69 ledgers and 2,681/8,324 claimed rows.  The warning-clean
default build completes all 3,538 jobs.
