# Math Bridge Essentials

Purpose:

- define a prose bridge from game-theoretic theorem shapes to game-free `Math` abstractions,
- keep extraction targets directly useful for `GameTheory`,
- enforce a stronger usefulness test: each abstraction must also be directly useful in at least one non-subset external field.

Reminder of roles:

- `GameTheory`: domain adapters and final domain statements.
- `Math`: domain-free reusable layer.
- `Shadow`: bridge analysis and extraction planning.

Bridge test (must pass all):

1. **GameTheory utility**: replacing at least one local helper proof in `GameTheory`.
2. **External utility**: immediately useful in a different field (program semantics, distributed protocols, control, optimization, etc.), not merely a game-theory subcase.
3. **No domain names**: statement does not mention players/strategies/equilibria.
4. **Minimal structure**: assumptions only where used.

Cross-field naming rule:

- any mnemonic term introduced in this track must list equivalent non-domain names.
- preferred format:
  - chosen name (this track),
  - structural meaning,
  - equivalent names in other fields.

Quick glossary:

- `Execution`: repeated composition of a transition map.
  - Also called: transition semantics, rollout, process evolution.
- `Projection`: map from full state/execution object to a reduced readout.
  - Also called: feature map, measurement map, view map, quotient key.
- `Transport`: moving a statement along a representation map.
  - Also called: refinement preservation, compilation correctness transfer.
- `Disintegration`: decompose-by-projection then recombine.
  - Also called: law of total probability, mixture decomposition.
- `Locality/Irrelevance`: coordinate-insensitivity under updates.
  - Also called: non-interference, frame property, dependency sparsity.
- `Descent`: strict decrease under a well-founded relation.
  - Also called: termination ranking, normalization descent.

Roadmap parts:

1. `10-ExecutionCore.md`
2. `20-ProjectionCore.md`
3. `30-RestrictionTransport.md`
4. `40-DisintegrationLayer.md`
5. `50-IterativeKernelLayer.md`
6. `60-LocalityIrrelevance.md`
7. `70-DescentWellFounded.md`
8. `80-OptimizationShell.md`
9. `90-GeometryEnvelope.md`
10. `100-IntegrationPass.md`
