# Multivalued essential-APS execution

This directory separates four kinds of data that must not be conflated:

1. `FiniteStronglyConnectedComponent` and `FiniteReachableSCC` are finite graph
   data for the exact Flesch successor relation. A graph route from the source
   to the SCC entry is not an executable APS route.
2. `IsQuittingEssentialAPSInternalSCCStep` is executable data: one successor,
   one mass in `[0,1)`, and the exact singleton-arc payoff equation.
3. `IsQuittingEssentialAPSSegmentSubinvariantOnSCC` is the positive producer
   hypothesis. It uses the existing segment owner-step operator, with all
   continuations restricted to the selected component.
4. `ChronologicalExecution` and `ChronologicalExecutionOutcome` retain one
   finite or infinite execution; the latter may instead retain a typed failure
   reached by an executable prefix.

The genuine game-facing theorem is
`quittingEssentialAPSSCC_execution_of_segmentSubinvariant`. It derives local
terminal-or-segment progress from segment subinvariance, converts a formal
mass-one segment to the terminal branch, and produces either one finite
absorbing execution or one coherent infinite exact segment path. The SCC does
not create that segment hypothesis; it supplies the owner region in which the
selected continuations must remain.

The quantitative charge layer is separate.
`quittingEssentialAPSChargedSegment_executionOutcome` classifies the relation
“there is an exact segment of mass at least `eta`.” Its obstruction branch is
intentional, and no theorem here derives a positive `eta` merely from the
finite owner graph. Conditional prefix-charge lemmas remain available once a
charged infinite path has actually been supplied.

The occupation regression is a semantic fence, not evidence for the positive
producer. It uses two disjoint closed recurrent classes: a globally balanced
half-half occupation cancels their signed charges, while a path starting in
either class cannot cross to the other. Global occupation balance is therefore
aggregate flow data, not an executable APS path.

This layer does not assert the survival contraction, punishment, or terminal-
to-uniform hypotheses required by the existing uniform-payoff compilers.
