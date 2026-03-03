# Family Survey: F4 (Equilibrium / Existence / Correlation)

Input:

- [F4TheoremBlockMap.csv](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F4TheoremBlockMap.csv)
- [F4BlockCounts.json](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F4BlockCounts.json)
- [F4FileCounts.json](D:\workspace\games\GameTheory\Shadow\GameTheoryEssentials\F4FileCounts.json)

Theorem count in F4: 109

## Structural distribution (primary block)

- `B9` inequality/optimization algebra: 37
- `B1` distributional composition: 25
- `B6` fixed-point transfer: 13
- `B8` continuity transfer: 8
- `B10` adapter/wrapper or classification-uncertain: 26

Interpretation:

1. F4 is mostly algebraic inequality transfer (`B9`) and distributional rewrites (`B1`).
2. Existence proofs occupy a narrower but central `B6+B8` spine.
3. The `B10` portion should be reduced by theorem-level manual audits
   (many are likely wrappers around `B1/B9/B6`).

## Highest-density files

1. `NashExistenceMixed.lean` (32)
2. `SolutionConcepts.lean` (13)
3. `CorrelatedNashMixed.lean` (9)
4. `ApproximateNash.lean` / `Rationalizability.lean` (6 each)

## Reusable non-domain cores suggested by F4

## C1. Gain-inequality equivalence kernel (`B9`)

Schema:

- target predicate ↔ all local deviation gains `≤ 0`.

Use:

- Nash-style characterization files,
- strict/approximate/refinement variants.

## C2. Weighted-gain conservation (`B9 + B1`)

Schema:

- expected gain under current mixed law equals zero.

Use:

- fixed-point transfer proofs,
- regret-style bridge lemmas.

## C3. Normalized fixed-point transfer (`B6`)

Schema:

- fixed-point equation of normalized map ⇒ inequality constraints ⇒ target predicate.

Use:

- existence theorems in mixed strategy and related fixed-point modules.

## C4. Continuity transfer combinator (`B8`)

Schema:

- if base evaluators are continuous, map constructors preserve continuity.

Use:

- all approximation/Brouwer entry points.

## C5. Distributional rewrite bundle (`B1`)

Schema:

- canonicalization of `bind/map/pushforward/update` equalities used in equilibrium proofs.

Use:

- correlated equilibrium derivations,
- mixed-extension EU decomposition.

## Next action for F4

1. Manual audit of all `B10` rows in `F4TheoremBlockMap.csv`.
2. Promote `C1..C4` as explicit structural schemas (prose first).
3. Extract at most one one-shot lemma from `C1` or `C3`.

