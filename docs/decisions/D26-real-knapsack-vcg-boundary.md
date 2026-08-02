# D26: real knapsack uses finite-set semantics and canonical pivot VCG

- **Status:** adopted
- **Date:** 2026-08-02
- **Experiment IDs:** EXP-055

## Decision / question

How the pinned real-valued binary-knapsack semantics, welfare-maximizing
allocation, monotonicity, mechanism, and mature truthfulness cross D4/D5/D9
without duplicating the exact solver's aggregation, the auction report
signature, or a mechanism-specific equilibrium API.

## Competing designs

1. Preserve Boolean function allocations, ambient `[Fintype Agent]`, and the
   predecessor's single-parameter mechanism wrapper.
2. Use `Finset Agent` allocations and an explicit finite universe for semantic
   maximization, specializing to `Finset.univ` only at the mechanism boundary;
   instantiate the canonical `VCGSetup` and canonical ex-post Nash theorem.
3. Define real semantics by importing the natural exact solver and restating
   real-valued load and welfare in the mechanism layer.
4. Postpone every mechanism theorem until the analytic Myerson-envelope gate.

Design 2 is adopted.  Scalar-generic `aggregate`, `load`, and `welfare` live in
an independent leaf shared by the natural algorithm and real semantics.
`Basic` does not import `Algorithm`; `Mechanism` imports `Basic` and the
canonical VCG layer.  Only equality with the predecessor's exact
Myerson-envelope payment remains behind D11/M-BAYES.

## Representative hostile slice

EXP-055 maximizes reported real welfare over an explicit finite powerset,
packages feasibility in the VCG outcome subtype, proves monotonicity under
arbitrary classical tie choice, and uses the pivot offset obtained by setting
the bidder's own report to zero.  A two-agent unit-capacity witness makes the
full allocation infeasible, changes the offset from zero to three when only
the opponent's report changes, preserves it under every own-report
replacement, proves zero payment at a zero own report, and reaches canonical
truthful ex-post Nash.

The feasible outcome subtype is necessary rather than decorative:
`VCGSetup` efficiency quantifies over every value of `Outcome`, so taking
`Outcome := Finset Agent` would incorrectly require the allocation to dominate
infeasible alternatives.

## Measurements

| Measure | EXP-055 result |
|---|---|
| pinned rows moved by the slice | 20 newly adapted, one newly retired; family now 26 adapt / 12 retired / 2 subsumed / 31 deferred |
| stable split | scalar-free `Aggregate`; independent executable `Algorithm` and real `Basic`; `Mechanism` over `Basic` plus canonical VCG |
| capability placement | explicit `Finset Agent` universe in `Basic`; `[Fintype Agent]` only for full-universe mechanism operations |
| tie behavior | arbitrary chosen maximizer is monotone: a strict increase contradicts the two optimality inequalities if a selected bidder is dropped |
| normalization | pivot offset is own-report independent; `vcgPayment` is zero after an own report of zero |
| hostile witness | two unit-weight bidders, capacity one; opposing report changes pivot offset from `0` to `3`, own replacement leaves it at `3` |
| focused builds | `Basic` 1,724 jobs; `Mechanism` 1,725; hostile witness 1,726 |
| source hazards | zero raw updates, transports, hidden `Fintype`, placeholders, or custom axioms; executable leaves contain no classical section |
| axiom profile | `propext`, `Classical.choice`, and `Quot.sound` only |
| boundary audit | Aggregate rejects 8/8 real/game/analytic probes; Basic rejects 7/7 execution/VCG/Protocol/Analysis probes; mechanism reaches 6/6 canonical integration targets; Phase 2 `VERIFIED=1` |
| full integration | umbrella 1,728 jobs; full build 3,409 jobs; Phases 0/1/2/3 and coverage audits all `VERIFIED=1` |

## Kill conditions and result

Reject the design if it requires a second bid signature, mechanism, utility,
dominance, or DSIC predicate; if natural and real aggregation are duplicated;
if `Basic` depends on the executable solver or stores finiteness; if arbitrary
tie choice breaks monotonicity; if efficiency silently compares against
infeasible outcomes; if the Groves offset is a constant toy; or if Analysis or
Protocol leaks into the finite semantic closure.

No mathematical kill condition fired.  The first hostile draft did reveal two
real architectural defects before promotion: it duplicated the canonical bid
signature and separately defined real aggregation.  The stable split removes
both.  It also narrows `Outcome` to certified feasible allocations, exactly
matching the quantifier in canonical VCG efficiency.

## Result and consequences

`GameTheory.Mechanism.Knapsack.Basic` owns real public data, `Finset`
allocation semantics, explicit-universe feasible maximization, and the
feasible outcome subtype.  `GameTheory.Mechanism.Knapsack.Mechanism` owns the
full-universe allocation rule, numeric monotonicity, pivot-normalized
`VCGSetup`, efficiency and offset certificates, zero normalization, and the
canonical ex-post Nash theorem.  It uses
`GameTheory.Mechanism.Auction.BidProfile` and `Profile.update` directly.

The predecessor's `BinaryAllocation` is retired, not aliased.  Its Boolean
conversion becomes the transparent `indicator`, and its update identity is a
public `welfare_update` theorem over the canonical profile implementation.
The predecessor's exact payment rule remains deferred behind D11/M-BAYES:
zero normalization and monotonicity prepare that bridge but do not claim the
analytic envelope equality.

The 31 remaining knapsack rows are precisely the nine fractional rows, the
21 repaired greedy/approximation rows, and exact Myerson payment equality.
The next DFS gate is the repaired approximation theorem described by D25; it
must return an actual feasible allocation and cannot inherit the predecessor's
overweight-highest-bid defect.
