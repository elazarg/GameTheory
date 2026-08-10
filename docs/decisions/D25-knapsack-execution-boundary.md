# D25: executable knapsack takes an explicit item order

- **Status:** adopted for the exact natural solver; full knapsack gate narrowed
- **Date:** 2026-08-02
- **Experiment IDs:** EXP-054

## Decision / question

How the pinned binary-knapsack file's proof semantics, finite search,
natural-number solver, and approximation code cross the D9/D10 execution
boundary without hidden enumeration or a second mechanism API.

## Competing designs

1. Preserve Boolean function allocations and recover the finite universe from
   ambient `[Fintype Agent]`, as in the predecessor.
2. Represent an allocation by `Finset Agent`, pass a duplicate-free
   `List Agent` explicitly to executable algorithms, and state correctness
   against every feasible finite set supported by that list.
3. Exhaustively enumerate an explicit `Finset Agent` with `powerset`, filter
   feasible allocations, and use `List.argmax` as the executable solver.
4. Build an indexed array table with reconstruction data and prove an explicit
   time/space bound.

Design 2 is adopted for the first stable slice.  It preserves the
predecessor's exact skip/take recurrence while removing its Boolean-coordinate
updates, global finite-universe wrapper, and noncomputable public execution
entry point.  Design 3 remains a useful reference optimizer but does not test
the recursive correctness chain.  Design 4 is the honest route to a complexity
claim; the baseline supplied neither memoization nor a cost theorem, so it is not a
prerequisite for recovering the mathematical optimum result.

The naming distinction is substantive.  When every item fits, the recurrence
has `C(0) = 1` and `C(n) = 1 + 2 * C(n - 1)`, hence
`C(n) = 2^(n + 1) - 1` solver calls.  The predecessor implemented no cache or
table sharing.  The successor therefore does not retain any
`dynamicProgramming*` public name.

## Representative hostile slice

`GameTheory.Experimental.PostArchitecture.KnapsackBoundary` defines natural
load and welfare on `Finset Agent`, computes an exact allocation from an
explicit list and capacity, proves support, feasibility, and global optimality,
and evaluates a three-item instance whose optimum is `{0, 1}`.  Correctness
requires `List.Nodup` at the theorem, while execution itself needs only genuine
decidable equality.

## Measurements

| Measure | EXP-054 result |
|---|---|
| representative inventory | 71 declarations: 31 real/mechanism, 19 natural solver, 21 greedy/approximation |
| predecessor hazards | 45 raw `Function.update` occurrences; 19 noncomputable public definitions |
| predecessor execution seam | recursive kernel computes, but both finite-universe public wrappers are noncomputable |
| worst-case recurrence | `C(n) = 2^(n + 1) - 1` solver calls when every item fits; no memoization |
| Mathlib overlap | no existing `0/1` knapsack solver; `Finset.powerset` and `List.argmax` can supply a reference enumerator |
| hostile slice | 198 nonblank lines; three public correctness theorems; no stored `Fintype` |
| focused builds | hostile slice 799 jobs; promoted correctness leaf 800 jobs; mechanism umbrella 1,733 jobs |
| full build | 3,405 jobs |
| execution witness | compiled evaluation returns cardinality two; kernel `decide` proves the exact `{0, 1}` result |
| negative reachability | `Real.instAdd`, `PMF`, `MeasureTheory.Measure`, `stdSimplex`, and `Polynomial` all unreachable |
| promoted reachability audit | algorithm rejects 7/7 semantic/real/analytic probes; opt-in root reaches solver plus 2/2 headline correctness theorems |
| source hazards | no raw update, transport, `Fintype.ofFinite`, `open Classical`, `noncomputable`, placeholder, or custom axiom |
| axiom profile | `propext`, `Classical.choice`, and `Quot.sound` only |

## Kill condition

Reject the explicit-list surface if returning a `Finset` cannot execute, if
correctness needs hidden `Fintype`, classical choice in the algorithm, raw
coordinate update, real or analytic imports, user-visible transport, or if the
proved optimum ranges over a different allocation class than the solver
returns.  Require a different representation if reconstruction forces an
opaque list conversion at runtime.

No measured kill condition fired.  The algorithm source and evaluation use no
classical choice.  The correctness proofs have the project's standard
`propext`, `Classical.choice`, and `Quot.sound` axiom profile through the
Mathlib finite-set foundations; this is not runtime data or an algorithm
dependency.  `Finset.toList` itself is noncomputable in
the pinned toolchain, but the solver does not use that conversion: insertion,
membership, cardinality, equality, and the returned allocation all evaluate.
The API therefore returns the finite set and never promises an executable
arbitrary ordering of it.

## Result and consequences

Promote only the 19-declaration natural solver cluster under this decision.
Its stable algorithm leaf takes `weight`, `value`, the explicit item list, and
capacity; its correctness leaf owns support, feasibility, and optimality.  The
public name describes an exact skip/take solver, not a memoized dynamic program
or a complexity guarantee.  The predecessor rows are classified individually
as adapted, subsumed, or retired rather than credited as direct ports; in
particular, the noncomputable `dynamicProgramming*` wrappers are retired.

The other 52 pinned rows do not ride this decision silently:

- the 16 base real-valued semantic rows require a separate canonical
  finite-allocation/mechanism slice;
- the nine fractional rows, bid-update algebra row, and 21 greedy/approximation
  rows require a ratio-order and approximation experiment; the predecessor's
  headline half bound assumes rather than proves fractional optimality, takes
  the highest bid even when that item is infeasible, and concludes only a
  maximum of values rather than returning the better feasible allocation.  A
  repaired theorem must require positive weights, prefilter infeasible items,
  use the highest feasible singleton, certify ratio order, and select the
  actual returned `Finset`;
- the allocation rule and its monotonicity theorem belong in the next real
  semantic slice;
- mature truthfulness should be recovered topology-free through the existing
  canonical `Mechanism.GrovesSetup` with `Finset Agent` outcomes, while
  only equality to the predecessor's exact Myerson-envelope payment remains
  behind M-BAYES/D11.  The retired `SingleParameterMechanism` wrapper stack is
  not recreated.

The delivery audit must add a direct negative probe for the algorithm leaf and
a positive probe that the opt-in knapsack root reaches both the solver and its
correctness theorem.  The promoted probes pass at 7/7 rejected and 3/3 reached.
