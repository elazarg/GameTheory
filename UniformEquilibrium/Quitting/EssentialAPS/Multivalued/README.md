# Multivalued essential-APS SCC execution

This directory separates three kinds of data that must not be conflated:

1. `FiniteReachableSCC` is finite graph data for the exact Flesch successor
   relation. Its strong-connectivity witnesses remain inside the displayed
   carrier.
2. `IsQuittingEssentialAPSInternalSCCStep` is behavioral/executable data: one
   successor, one mass in `[0,1)`, and the exact singleton-arc payoff equation.
3. `ChronologicalExecutionOutcome` contains one finite or infinite execution,
   or a typed obstruction reached by a finite executable prefix.

The recurrent branch measures charge on the selected chronological path. The
occupation regression intentionally uses two disjoint closed recurrent classes:
a globally balanced half-half occupation cancels their signed charges, while a
path starting in either class cannot cross to the other. Consequently global
occupation balance is evidence about an aggregate flow, not an executable APS
path.

This layer is an execution producer. It does not assert the contraction,
punishment, or terminal-to-uniform hypotheses required by the existing
uniform-payoff compilers.
