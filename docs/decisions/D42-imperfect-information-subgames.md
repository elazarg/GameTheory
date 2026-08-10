# D42: subgame perfection uses information-set-closed roots

- **Status:** adopted and promoted
- **Date:** 2026-08-09
- **Experiment IDs:** EXP-075

## Decision

Protocol owns two distinct continuation predicates.

- `InformationModel.IsSubgameRoot history` states that every active,
  nonterminal decision information set met below `history` is wholly contained
  below it.
- `InformationModel.IsSubgamePerfect` compares every player's incumbent policy
  with every whole replacement policy only at those roots.
- `InformationModel.IsHistorywiseOptimal` performs the same comparison after
  every complete history.  It is intentionally stronger and implies
  `IsSubgamePerfect`.
- the well-founded one-shot-deviation equivalence characterizes
  `IsHistorywiseOptimal`, not general imperfect-information SPE.

The closure predicate is defined over canonical `ExecutionProtocol.History`,
`HistoryReaches`, activity, and `InformationModel.infoOf`.  It does not import
or reproduce EFG syntax.

## Competing designs

1. Keep historywise optimality under the SPE name.  Rejected: it treats a node
   inside a nonsingleton information set as the root of a subgame.
2. Expose SPE only for perfect-information models.  Rejected: the canonical
   information model already expresses the exact closure condition needed for
   imperfect-information subgames.
3. Define information-set-closed roots at Protocol and keep historywise
   optimality separately.  **Selected.**

## Representative slice and result

The hostile hidden-card protocol has two distinct decision histories after
nature's high and low deals.  The blind player has the same information state
at both.  The initial history satisfies `IsSubgameRoot`; a root at the high deal
does not, because its continuation contains the high node but excludes the
indistinguishable low node.  The proof uses trace-depth monotonicity of the
existing reachability relation to show that the two sibling histories cannot
reach one another.

The perfect-information control remains constructive.  Strong separation of
decision histories makes every history a subgame root, and the existing
Bellman profile is historywise optimal; therefore it remains a pure SPE.

## Kill condition and result

Reject the selected design if subgame closure needs language syntax, a second
subtree evaluator, a new strategy carrier, user-visible transport, or an
Analysis dependency; or if it cannot reject a root that cuts the hostile
information set while retaining the initial root.

No kill condition fired.  Focused Protocol, EFG, Zermelo, and hostile-test
builds completed warning-free.

## Consequences

The previous one-shot theorem remains available with accurate historywise
naming.  Textbook imperfect-information SPE now has the correct domain, but a
general one-shot characterization for it is not claimed: that theorem must
aggregate deviations at information sets within each proper subgame rather
than condition on an arbitrary hidden history.  Coverage and capability
records must report that remainder explicitly.
