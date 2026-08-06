# Essential APS singleton-flow certificate

This module family formalizes the finite certificate-facing part of the
essential APS approach of Ashkenazi-Golan, Krasikov, Rainer, and Solan,
*The APS approach for undiscounted quitting games* (International Journal of
Game Theory 55:19, 2026).

## Equation (3): algebraic convexification and path segments

Equation (3) in the paper displays both

```text
∃ λ ∈ [0,1], v ∈ E,  w = λ R_i + (1-λ) v
```

and

```text
co ({R_i} ∪ E).
```

For an arbitrary nonconvex `E`, the witness expression is only the union of
segments from `R_i` to individual points of `E`, whereas the full convex hull
also mixes several continuation points. The Lean API makes both notions
explicit instead of silently identifying them:

- `quittingEssentialAPSPrefix` is the literal full convex-hull expression;
- `quittingSegmentEssentialAPSPrefix` is the one-continuation path relation;
- `quittingSegmentEssentialAPSPrefix_subset` proves the always-valid inclusion.

The owner-indexed `quittingEssentialAPSOperator`, packets, restricted operator,
and greatest fixed-family construction use the full convex hull. Thus arbitrary
nonconvex carriers are convexified exactly where the APS operator requires it.

The segment relation remains necessary for execution. Lemmas 3.2, 4.5, and 4.7
in the paper select one continuation and one successor, and the finite-cycle
compiler supplies precisely such a sequence. A proper segment, with mass in
`(0,1)`, is proved to lie in the larger algebraic operator. No theorem claims
that every point created only by convexification is executable as a Flesch
absorption path.

## Lean layers

The implementation contains five layers:

1. `QuittingFleschSuccessor.lean` defines the exact asymmetric cross-sign
   successor graph in a normalization-independent form and derives graph edges
   from two consecutive positive singleton arcs under singleton genericity.
2. `QuittingEssentialAPS.lean` defines the full-convex-hull owner-indexed
   essential APS operator, the one-continuation segment subrelation, and its
   proper positive-mass refinement.
3. `QuittingEssentialAPSFixedPoint.lean` constructs the greatest algebraic
   fixed family inside an arbitrary supplied owner-indexed carrier.
4. `QuittingEssentialAPSRegression.lean` proves that a nontrivial affine
   segment self-loop can only use zero absorption mass.
5. `QuittingEssentialAPSCycle.lean` packages a supplied finite proper cycle,
   embeds its segment witnesses into the full algebraic operator, places its
   carrier in the restricted greatest fixed family, and invokes the existing
   singleton-flow mesh compiler to obtain a fixed-target uniform-equilibrium
   payoff.

The principal theorem entry points are:

- `quittingFleschSuccessor_of_consecutive_arcs`;
- `quittingSegmentEssentialAPSPrefix_subset`;
- `quittingEssentialAPSGreatestFamily_fixed`;
- `quittingEssentialAPS_zeroMassFixedPoint_regression`;
- `QuittingEssentialAPSCycleCertificate.isUniformEquilibriumPayoff`.

`QuittingEssentialAPSAll.lean` is the umbrella import and is part of the public
`GameTheory.lean` surface, so every implementation module is covered by the
repository import and axiom audits.

The result is deliberately conditional. It does not assert that every
convexified essential-APS fixed point is executable, that every sequentially
perfect Flesch absorption path is finite cyclic, or that every quitting
equilibrium belongs to the one-randomizer-at-a-time stratum. In particular,
the explicit positive hazards are executable progress witnesses that rule out
the operator's `p = 0` fixed-point pathology. Together with the change of owner
at every seam, they imply the opponent-contraction condition required by the
singleton-flow compiler; contraction is therefore a theorem, not independent
certificate data.
