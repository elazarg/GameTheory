# Fixed public controllers are verifiable but not known complete

| Status | Scope | Formalization | Complexity fence |
| --- | --- | --- | --- |
| `MIXED`, maturity `M+L/A?` | supplied finite public Markov controller skeleton and target | credibility soundness and much of semantic necessity landed; corrected rejection exhaustiveness incomplete | Q98 gives a source-conditional no-total-computable-node-bound result; not Lean-formalized |

For a fixed finite public Markov architecture, the strategic acceptance problem
reduces to finite gain--bias, reachability, occupation, and deviation checks.
With the combinatorial skeleton/support cells fixed, the remaining feasibility
conditions are finite linear or semialgebraic problems. This makes fixed-`K`
verification and bounded-template synthesis legitimate P2 work.

Three stronger conclusions are forbidden:

1. **finite-public completeness:** false as a root class; Big Match needs the
   combination of clock dependence and hidden randomized memory;
2. **a computable universal node bound:** Q98's source-conditional reduction
   rules this out for the stated unbounded public-controller existence
   language, but its internal bridge and source reduction are not formalized;
3. **private/clocked completeness:** open already in the two-player zero-sum
   boundary isolated by Q94.

The next production result is the corrected fixed-architecture rejection
alternative, including reachable-arena conventions and the cross-owner
recurrent witness. After that, fixed controller sizes may be synthesized or
rejected independently. Failure at size `K` says nothing about all sizes, and
enumeration has no certified stopping rule without an additional theorem.

Certificate complexity is metadata: fixed templates may admit ETR/LP
descriptions whose practical complexity depends on controller size, recursive
depth, branching, polynomial degree, bit size, and accuracy. It does not
replace the mathematical producer or become a new P0 route.
