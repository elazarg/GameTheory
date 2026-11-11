# Mathematical economics building blocks

This is a consolidation and extraction map, not a claim that the field has a
universal data model. The accepted evidence is EXP-173 through EXP-186 and
decisions D78 through D92. The collecting branch is
`codex/experiment-abstraction-building-blocks`.

The named continuation gates are complete. The last three experiments refine
assumptions and semantic boundaries without requiring another stable owner.
The ordinary measure-valued consumer also reuses existing guarded comparison.
Architecture expansion has reached diminishing returns for this investigation;
the next concrete task is a scoped extraction build, not another hierarchy.
See [D92](decisions/D92-economic-extraction-boundary.md) for the decision,
specific MathEconLib consumers and conditions for reopening a gate.

## Accepted operations and ownership

| Operation | Current owner | What transfers to mathematical economics | Boundary |
| --- | --- | --- | --- |
| Guarded comparison and alternative coverage | `Math.GuardedOptimality` | Domain of evaluation, weak comparison, and alternative coverage are separate arguments. | Optimality does not imply that the incumbent belongs to the offered menu. |
| Finite-menu choice representation | `Math.FiniteChoice` | Feasible, nonempty, WARP-consistent choice on all finite menus is greatest-element choice for a total transitive relation. | Restricted budget observations and latent incomplete preferences need different hypotheses. |
| Scalarization to maximality | `Math.Scalarization` | Strict increase at the incumbent suffices to turn a feasible scalar maximizer into a maximal point. | A scalar objective is explicit; ordinal Pareto comparisons do not choose interpersonal weights. |
| Closed feasible-maximizer graph | `Math.ParametricOptimality` | Closed feasibility, lower hemicontinuity and continuous scores preserve maximizers at limits. | Existence, compactness and convexity are separate. |
| Positive linear-budget recovery | `Math.LinearBudget` | Radial recovery gives lower hemicontinuity with positive continuous wealth and section-continuous costs. | Zero wealth can fail; positive wealth is sufficient rather than necessary. |
| Simultaneous feasible maximizers | `Analysis.FeasibleChoiceFixedPoint` | Separate objectives and endogenous menus compose on a compact convex envelope. | The external fixed-point dependency stays explicit; native game, demand and clearing semantics are client obligations. |

An import-closure inspection on collecting checkpoint `164d13e0` finds that
each of the first five modules imports only Mathlib: none imports another
authored module. The last module's authored closure contains exactly itself
and `Math.ParametricOptimality`; its external roots are Mathlib and
FixedPointTheorems. Thus these operations have no semantic dependency on
profiles, deviations, protocols, utility preferences or an economic record.
This supports extraction of mathematics, not an immediate package move.

Existing `Core.Response`, `Protocol.Context`, Groves and bargaining concepts
remain domain-owned specializations or consumers. The experimental constrained
quantity game and exchange economy are evidence, not alternate stable economic
semantics. No parallel definition is needed simply to give economics familiar
names. Search Mathlib again before moving any independently reusable theorem
upstream.

## Continuation gates and outcomes

The continuation followed this dependency order:

1. **Information and dynamic choice.** Test whether conditional optimality
   composes before information is observed. Separate evaluation-domain closure
   from preservation of comparisons under the actual prior and continuation
   kernels. Include a total transitive non-EU preference that reverses a
   conditional comparison after mixing, and a non-EU positive consumer.
   EXP-184 / D89 completes this test: both strict conditional comparisons can
   reverse ex ante, while arbitrary-PMF possibility comparisons support two
   direct composition clients. Keep the prototypes experimental; no new Context
   record is justified. Information-local policy realization remains separate.
2. **Mixture requirements.** Use that consumer to distinguish full comparison
   preservation from weaker bound or no-strict-gain closure. EXP-175 already
   refutes binary closure as a substitute for arbitrary PMF closure. Do not
   repeat that failed competition under another name.
   EXP-184 also supplies the non-EU paired-comparison and bound-closure evidence:
   weak closure need not preserve strict comparisons or independence cancellation.
   This narrows required laws without admitting a universal mixture hierarchy.
3. **Restricted observations.** Test identification from a genuinely restricted
   menu family before extending the all-finite-menu representation theorem.
   Observational ambiguity is a possible answer, not a missing record to hide.
   EXP-185 / D90 proves ambiguity at a fixed positive price vector for every
   real wealth, despite two globally consistent rationalizations. A changed
   price budget distinguishes them. Existing menus suffice; general restricted
   rationalization existence is a separate theorem question.
4. **Institutional composition.** Test simultaneous bundle acceptance and the
   separation of consent from affected participants against existing matching
   and deviation operations. Require an operation the current APIs cannot
   express before admitting another arena.
   EXP-186 / D91 completes the quota/complement test against the pinned
   MathEconLib consumer: item WARP, bundle WARP and substitutes differ. Existing
   set maps express the examples and contraction supplies joint-to-singleton
   acceptance. Reuse MathEconLib's institutional owner rather than add a parallel
   GameTheory record.
5. **Economics extraction contract.** Consolidate the measured conclusions,
   named consumers, dependency roots and remaining domain obligations. General
   populations, endowments and weaker preferences warrant another experiment
   only if they expose a new semantic or compositional question.
   Item 16 checks the actual per-player integrable-deviation contract in the
   pinned MathEconLib source using `Tests.MeasureGuardedOptimality`. Arbitrary
   measure-valued choices fit the existing guarded predicate; the concrete
   countably supported probability-measure control distinguishes filtered
   deviations, inadmissible incumbents and raw totalized integrals. A defined
   negative-infinite expectation remains distinct from finite integrability.
   This is ordinary consumer validation, not another architecture experiment.

## Stopping rule

The investigation reaches diminishing architectural returns when the remaining
named clients use existing operations with local assumptions, the hostile
controls delimit those assumptions, and the unresolved tasks are theorem
coverage or domain-specific accounting. Record that outcome explicitly. A new
record, hierarchy or package split needs a demonstrated client benefit; more
formalized theorem families alone are not that evidence.

Before calling extraction ready, identify a real MathEconLib consumer and its
namespace/dependency requirements. No external repository has been changed or
validated by the present experiment. The shared mathematical layer is a
candidate extraction boundary, not evidence of external integration.

The pinned consumer revision is
`58f602847d7f131994d32ca7a8cc1af35b7e2dbe`. D92 names the actual bundle-choice,
contract-stability and measurable mixed-equilibrium APIs inspected there.
Dependency ownership and namespace selection remain part of the extraction
build; no fresh probability carrier or universal economic record is needed
merely because the consumer uses probability measures rather than PMFs.
