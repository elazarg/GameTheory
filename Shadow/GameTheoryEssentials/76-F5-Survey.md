# Family Survey: F5 (Dynamics / Dominance / Potential)

Input:

- [F5TheoremInventory.csv](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F5TheoremInventory.csv)
- [F5TheoremBlockMap.csv](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F5TheoremBlockMap.csv)
- [F5BlockCounts.json](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F5BlockCounts.json)
- [F5FileCounts.json](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F5FileCounts.json)

Theorem count in F5: 43

## Structural distribution (primary block)

- `B9` inequality/order transfer: 28
- `B0` relation/preorder algebra: 12
- `B7` well-founded/termination style: 2
- `B10` adapter/uncertain: 1

Interpretation:

1. Most of F5 is not probabilistic; it is order/inequality transport.
2. Dominance and best-response files are mostly relational algebra (`B0`) plus payoff inequalities (`B9`).
3. Potential/FIP files suggest a deeper `B7` core than raw counts indicate; many such lemmas are currently encoded as `B9` statements and should be re-expressed via descent templates.

## Highest-density files

1. `PotentialFIP.lean` (6)
2. `DominanceRelations.lean` (5)
3. `Regret.lean` (5)
4. `DominanceSolvable.lean` / `PotentialGame.lean` (4 each)

## Reusable non-domain cores suggested by F5

## D1. Relation-lifting algebra (`B0`)

Schema:

- reflexive/transitive closure and implication lifting for local comparison relations.

## D2. Improvement-step inequality kernel (`B9`)

Schema:

- “no improving step” ↔ equilibrium-like fixed condition.

## D3. Descent-to-termination bridge (`B7`)

Schema:

- strict decrease in ranking/potential + finite/well-founded state space ⇒ no infinite improvement chain.

## D4. Dominance elimination preservation (`B9 + B0`)

Schema:

- iterative elimination preserves selected solution predicates under monotonic relation assumptions.

## Next action for F5

1. Manual correction of rows where `B7` is hidden inside `B9`.
2. Extract one definition-free descent template from potential/FIP proofs.
3. Cross-link `D2` with analogous `B6` transfer skeleton in F4.

