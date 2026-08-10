# D27: knapsack half approximation returns a checked feasible allocation

- **Status:** adopted
- **Date:** 2026-08-02
- **Experiment IDs:** EXP-056

## Decision / question

How the pinned fractional/greedy knapsack family crosses the executable finite
boundary after its headline theorem was found to assume fractional optimality
and compare against the highest ambient bid even when that item is overweight.

## Competing designs

1. Reproduce the real-valued fractional allocation layer and require a caller
   to supply or prove its optimality.
2. Accept a caller-sorted list together with a density-order certificate.
3. Internally filter individually infeasible items, sort an explicit list by a
   division-free natural-number comparison, take the density prefix, construct
   the highest-value feasible singleton, and return the better actual
   allocation through a checked frontend.
4. Keep only the exact exponential solver and retire approximation entirely.

Design 3 is adopted.  The executable leaf owns data and computation only; its
correctness leaf verifies sorting, support, feasibility, and attainment; the
theorem leaf proves the ratio and imports the exact solver only for the final
optimal-value corollary.

## Representative hostile slice

EXP-056 uses capacity ten and five positive-weight items.  One item has weight
eleven and value one thousand, so the predecessor's ambient highest-bid term
would be infeasible.  Among eligible items, density greedy first takes the
weight-six/value-sixty item and stops at the next weight-five item, while the
weight-ten/value-ninety-five singleton is better.  The checked call succeeds,
returns some supported feasible `Finset`, and its welfare is certified within a
factor of two of `solveList` on the same explicit list.

## Measurements

| Measure | EXP-056 result |
|---|---|
| representative inventory | nine fractional rows plus 21 greedy/approximation rows; the predecessor never proves fractional-greedy optimality and its final theorem takes that fact as a premise |
| Mathlib overlap | executable merge sort and permutation/pairwise lemmas are reusable; no fractional-knapsack optimality theorem was found |
| executable assumptions | explicit duplicate-free list and strictly positive natural weights; no ambient `Fintype`, real division, or caller-trusted order |
| returned object | the better of an actual greedy-prefix `Finset` and an actual highest-value feasible singleton `Finset` |
| proof route | direct natural-number exchange at the first rejected item; cross multiplication only, with no fractional allocation or cast bridge |
| exhaustive pre-check | 3,119,265 small finite instances checked independently with no counterexample |
| pinned rows after classification | 33 adapt / 35 retired / 2 subsumed / 1 deferred; exact Myerson payment is the only remaining row |
| focused build | algorithm, structural correctness, and ratio theorem build as an 828-job target |
| source hazards | zero placeholders, custom axioms, raw updates, transport tokens, hidden `Fintype`, classical executable declarations, or analytic/game imports in the algorithm leaf |
| axiom profile | `propext`, `Classical.choice`, and `Quot.sound` only |
| boundary audit | executable approximation leaf rejects 7/7 real/game/probability/analytic probes; public knapsack root reaches 5/5 exact/approximation inputs; Phase 2 `VERIFIED=1` |
| full integration | full build 3,413 jobs; Phases 0/1/2/3 and coverage audits all pass their expected measurements |

## Kill conditions and result

Reject the design if zero weights or division are hidden behind defaults; if
sorting is noncomputable or the caller can lie about density order; if an
overweight singleton is compared; if the theorem names only an unattained
maximum value; if it compares against a different feasible class from the
exact solver; or if real, VCG, Protocol, or Analysis semantics leak into the
executable closure.

No kill condition fired.  The prediction was narrowed in an important way:
the filtered eligible list cannot support a sound ambient fractional-feasibility
bridge, because an overweight item may still be used fractionally.  Moreover,
the pinned source and Mathlib supplied no proof of fractional-greedy
optimality.  A direct integral exchange proof is both stronger for this API and
smaller: it partitions any feasible selection around the greedy prefix and
charges the suffix to the first rejected density plus omitted prefix weight.

## Result and consequences

`ApproximationAlgorithm` is a separately audited executable leaf.  Its
`approximate?` rejects duplicate or zero-weight raw inputs and internally
certifies the only ordering used by the theorem.  `ApproximationCorrectness`
owns the computation-to-proof bridge without importing the exact solver.
`Approximation` states `approximate?_half` for every supported feasible
selection and `solveList_welfare_le_two_mul_approximate?` for the exact optimum.

The public API has no fractional allocation type, ratio division, auction-data
wrapper, ambient highest-bid value, compatibility alias, or conditional
optimality premise.  The historical fractional intermediates are retired with
their reason recorded; their intended approximation result survives as a
kernel-checked theorem about the allocation the executable frontend actually
returns.
