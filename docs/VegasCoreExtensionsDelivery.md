# VegasCore extension recovery

Recover the reusable theorem families from `../VegasCore/GameTheoryExtensions`
into their canonical GameTheory owners, one validated slice per checkpoint.
Do not introduce an extension compatibility surface or a second definition of
an existing semantic concept. Preserve upstream attribution in `NOTICE`.

| Order | Slice | Status and evidence | Next obligation |
|---|---|---|---|
| 1 | Proportional Bayes transport | Supported: `Analysis.Protocol.BeliefTransport` scales site mass, cancels the multiplier in Bayes beliefs, and derives raw positive mass. Exact transport specializes the proportional theorem. Only finite movers are assumed; history carriers are arbitrary. The tremble reach-ratio consumer and existing restriction-extension consumer compile warning-free. | Terminal passage transport. |
| 2 | Depth-free action restrictions | Planned: replace common-depth conditioning by terminal passage, preserving the canonical extension API. | Unequal-depth concrete consumer; remove depth premises rather than add aliases. |
| 3 | Total variation and approximate transport | Planned: generic PMF error calculus, then protocol consumers. | Search Mathlib and reuse existing domination/expectation algebra. |
| 4 | Information-abstraction criteria | Planned: separate all-utility fact determination from fixed-payoff common maximizers. | Canonical decision semantics, separating examples and protocol correspondence. |
| 5 | Sanction feasibility and synthesis | Planned: incremental collection comparisons and rational least-deposit checker. | Separate executable finite checking from real correctness; signed coefficients where useful. |
| 6 | Component and pooled-agent completion | Planned: generalize prescribed/free agent completion. | Component-mixture optimality, pooled-member conditions and sequential consumers. |

Validation for the first slice:

```text
lake build GameTheory.Analysis.Protocol.BeliefTransport
lake build GameTheory.Analysis.Protocol.BeliefTransportTest
lake build GameTheory.Analysis.Protocol.RestrictionExtensionTest
```

The first consumer build exposed an identity-map simplification mismatch; an
explicit `change` and `PMF.map_id` resolve it without a transparency option.
