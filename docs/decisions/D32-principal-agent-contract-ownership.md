# D32: finite hidden-action contracts use a native principal-agent branch

- **Status:** adopted; public promotion pending
- **Date:** 2026-08-03
- **Experiment ID:** EXP-065

## Decision / question

Whether the pinned moral-hazard model belongs directly in the opt-in
`GameTheory.Mechanism` branch over finite-support outcome laws, or should be
encoded as a one-player strategic form or specialized through auction data.

## Competing designs

1. Define capability-free `PrincipalAgent` data with an action-indexed
   `FinDist` outcome law, reward, and effort cost.  Treat an
   outcome-contingent payment as theorem input.
2. Manufacture a one- or two-player `GameForm` and state action optimality as
   Nash equilibrium.
3. Specialize the existing auction `QuasiLinear` or VCG setup.

Design 1 is adopted.  Hidden action in this slice is a single risk-neutral
agent's optimization after the principal has committed to a payment.  There is
no simultaneous strategic choice to justify dummy players, profiles, or a
duplicate equilibrium surface.  Auction allocation and report data are also
strictly richer and impose the wrong vocabulary.

## Representative hostile slice

EXP-065 uses Boolean actions and outcomes.  The safe action fails
deterministically at zero cost; the productive action costs one and succeeds
with probability one half.  Success rewards the principal by four.  Zero
payment uniquely favors the safe action, while a success bonus of three
uniquely favors the productive action.  Productive utility is `1/2`, so the
same contract accepts an explicit outside option of `1/4` and rejects `3/4`.

A second one-action fixture has positive cost and zero payment.  Its action is
trivially incentivized and the payment has limited liability, but the agent
rejects outside utility zero.  This refutes the premise-erased participation
claim and forces the public theorem to expose an acceptable fallback.

## Measurements

| Measure | EXP-065 result |
|---|---|
| direct import | only `GameTheory.Probability.FinDist` |
| candidate artifact | 167 nonblank lines; 37 declarations including witnesses |
| probability capability | finite support belongs to each action law; no finite outcome carrier |
| action capability | `[Finite Action] [Nonempty Action]` only on maximizer existence |
| stochasticity | productive outcome law is a non-point-mass fair mixture |
| source hazards | zero raw updates, transports, `Fintype.ofFinite`, placeholders, or custom axioms |
| axiom profile | `propext`, `Classical.choice`, and `Quot.sound` only |

The public promotion must still pass focused and root builds, architecture
audits, exact pinned-v1 accounting, and an independent integration review.

## Kill condition

Reject native ownership if the accounting or participation theorem needs a
strategic-game wrapper, if `FinDist` loses essential PMF mathematics, if the
base data needs stored finiteness or topology, if participation silently
normalizes the outside option to zero, or if the hostile fixture cannot
distinguish actions, contracts, and reservation utilities.

No kill condition fired.  Any later private-type/report model, principal
contract-selection game, Protocol compiler, measurable outcome law, or
executable optimizer is a named consumer with its own gate rather than a field
added to this foundation.

## Consequences for the public API

The public leaf will live under `GameTheory.Mechanism`, remain absent from the
main `GameTheory` umbrella, and expose one native `PrincipalAgent` concept.
Agent and outcome universes remain independent.  Expected payment, agent and
principal utilities, social surplus, incentive maximization, explicit
participation, and limited liability are defined directly over `FinDist`.

`IsIncentivized` is not advertised as Nash equilibrium.  The exact welfare
identity, classical finite-action maximizer existence, and participation from
an offered acceptable action form the gate.  The existence theorem makes no
executability claim.  A later strategic bridge, if earned, must use canonical
`GameForm`, `Profile.update`, and `IsNash` rather than changing these native
semantics.
