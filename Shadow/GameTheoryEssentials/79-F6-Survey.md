# Family Survey: F6 (Mechanism / Auction / Social Choice)

Input:

- [F6Files.txt](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F6Files.txt)
- [F6TheoremInventory.csv](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F6TheoremInventory.csv)
- [F6TheoremBlockMap.csv](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F6TheoremBlockMap.csv)
- [F6BlockCounts.json](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F6BlockCounts.json)
- [F6FileCounts.json](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F6FileCounts.json)

Theorem count in F6: 29

## Structural distribution (primary block)

- `B9` incentive/inequality transport: 13
- `B5` representation/predicate transfer: 9
- `B0` relation/update algebra: 7

Interpretation:

1. The dominant shape is inequality transport, not domain-specific structure.
2. A large subset is representation-preservation:
   IC -> BIC, truthful reports -> equilibrium-like predicates, communication-form transfer.
3. Matching/social-choice portions are mostly relation closure and implication transport.

## Highest-density files

1. `SocialChoice.lean` (5)
2. `AllPayAuction.lean` (4)
3. `Matching.lean` (4)
4. `VickreyAuction.lean` (4)

## Reusable non-domain cores suggested by F6

## M1. Predicate transfer across interfaces (`B5`)

Schema:

- if representation map preserves objective comparisons, then incentive predicates transfer.

## M2. Truthfulness-to-stability transfer (`B9 + B6`)

Schema:

- local deviation non-improvement implies global fixed-point/no-profitable-deviation predicate.

## M3. Relation closure kernels (`B0`)

Schema:

- closure/monotonicity of pairwise preference/dominance relations implies global stability-style properties.

## Next action for F6

1. Manually review `B5` rows in `SocialChoice.lean` and `MechanismDesign.lean` for overgeneralization.
2. Extract one standalone transfer lemma for IC/BIC implication without mechanism naming.
3. Cross-link with F2 bridge modules to unify transfer assumptions.
