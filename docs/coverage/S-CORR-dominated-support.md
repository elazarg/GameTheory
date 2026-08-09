# S-CORR: strict dominance and correlated support

Title: Strict dominance, conditional obedience, and correlated support
Family ID: S-CORR
Pinned root: `GameTheory/Concepts/Correlation/CorrelationSaturation.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `17edfbb`
Canonical destination: `GameTheory.Core.CorrelatedDominance`
Domain contract / decision: D4, D5, D8-D10, D19
Owner: Wave 2 / correlation
Status: complete bounded file; 10/10 declarations reviewed, 8 deferred
Last verified: 2026-08-09

The selected mathematics is the topology-free interaction between correlation
and strict dominance.  The successor first proves conditional obedience for a
positive-probability recommendation, then excludes actions dominated relative
to a product set carrying the law's support.  Strictly dominant profiles pin
arbitrary CCE and CE laws as point masses.  No strategy carrier is finite.

The pinned file's remaining saturation vocabulary quantifies over public
signals selecting mixed Nash equilibria.  It is not introduced without a live
communication or correlation-regime consumer; those rows remain explicitly
deferred rather than becoming a parallel realization API.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Correlation/CorrelationSaturation.lean` | `strictDominant_isCoarseCorrelatedEq_iff` | theorem | adapt | `GameTheory.strictDominant_isCoarseCorrelatedEq_iff` | arbitrary-law Prisoner's Dilemma fixture | Finite support removes boundedness and all stored finiteness assumptions. |
| same | `strictDominant_isCorrelatedEq_iff` | theorem | adapt | `GameTheory.strictDominant_isCorrelatedEq_iff` | CE-to-CCE theorem chain; arbitrary-law fixture | The CE result is derived from the stronger CCE uniqueness statement. |
| same | `IsSaturatedFor` | def | deferred | D19/D-COMM selected public-signal realization consumer | public-signal gate | Do not freeze a correlation-regime abstraction only to preserve predecessor vocabulary. |
| same | `IsSaturatedFor.mono` | theorem | deferred | same public-signal realization gate | public-signal gate | Recovered with the definition if a consumer selects it. |
| same | `IsCorrelationSaturated` | def | deferred | same public-signal realization gate | public-signal gate | CE uniqueness itself is already available without the wrapper. |
| same | `IsCoarseCorrelationSaturated` | def | deferred | same public-signal realization gate | public-signal gate | CCE uniqueness itself is already available without the wrapper. |
| same | `IsCoarseCorrelationSaturated.isCorrelationSaturated` | theorem | deferred | same public-signal realization gate | public-signal gate | The underlying CE-to-CCE implication is canonical and live. |
| same | `strictDominant_isCoarseCorrelationSaturated` | theorem | deferred | same public-signal realization gate | public-signal gate | The substantive point-mass theorem is recovered; public realization waits for its consumer. |
| same | `strictDominant_isCorrelationSaturated` | theorem | deferred | same public-signal realization gate | public-signal gate | Same disposition as the coarse result. |
| same | `IsIESDSSolvable.isCorrelationSaturated` | theorem | deferred | S-DOM IESDS plus D19 public-signal realization gates | two named gates | Requires both the later elimination induction and a selected public-signal API. |

Disposition count: 2 adapted, 8 deferred.

The hostile two-player fixture makes player zero's `true` action strictly
dominate `false` only while player one's action is restricted to `false`.
Against the excluded opponent action `true`, the comparison reverses, and the
test proves global strict dominance false.  The pure CE at `(true, false)` has
support inside the allowed product and exercises conditional obedience and
relative support exclusion.  Separately, Prisoner's Dilemma proves that every
CCE and every CE law—not merely point masses supplied as input—is exactly the
mutual-defection point mass.

Attribution: the pinned `CorrelationSaturation.lean` supplies the strict-
dominance uniqueness statements.  Conditional obedience and relative support
exclusion are recovered from pinned `CorrelatedNashMixed.lean` and accounted in
[`S-CORR-mixed-nash.md`](S-CORR-mixed-nash.md).  The successor uses canonical
`FinDist.condOn`, `IsCorrelatedEq`, `IsCoarseCorrelatedEq`, `Profile.update`,
and `StrictlyDominatesOn` rather than its predecessor's PMF, bounded-utility,
and parallel game surfaces.

Validation: the focused probability, theorem-leaf, Core-root, hostile-test,
and Classic-example targets build warning-free.  The full structural audit
returns `VERIFIED=1`, reaches all four intended theorem inputs, and rejects all
three mixed-product, analytic-existence, and Protocol boundaries.  The two
probability helpers, four public theorem results, global-dominance negative
control, and Prisoner's Dilemma consumer depend only on `propext`,
`Classical.choice`, and `Quot.sound`.  Exact coverage returns `VERIFIED=1` at
67 ledgers and 2,637/8,324 claimed rows.  The warning-clean default build
completes all 3,534 jobs.
