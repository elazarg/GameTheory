# D45: Relate counterfactual regret to canonical continuation deviations

- **Status:** adopted; decomposition and action-local package promoted
- **Date:** 2026-08-10
- **Experiment ID:** EXP-082

## Decision

Define counterfactual continuation value by summing over the existing
`InformationHistory` fiber, weighting each history by D44's canonical
`counterfactualReachProbability`, and evaluating the existing
`runBehavioralFrom` continuation after an ordinary behavioral-policy
replacement. Counterfactual regret is the difference from the prescribed
policy. Pure action regret is a transparent specialization through
`BehavioralPolicy.commit` at one information state.

The useful contract is not the definition alone. At a positive-mass history
antichain with common focal own reach, information mass times the ordinary
canonical Bayes continuation gain equals own reach times counterfactual
regret. Consequently the two quantities have the same positive deviations.
Perfect recall proves common own reach; `CommonPlayerReachAt` exposes the exact
weaker certificate for selected sites in models that do not claim global
recall.

## Competing designs

1. Use canonical Protocol histories, reach, continuation runner, Bayes belief,
   behavioral-policy replacement, and pure commitment.
2. Reuse only normalized assessment values and omit reach-sensitive values.
3. Compile a separate local game and decompose its deviation gain.
4. Restore native FOSG/CFR histories, values, regrets, or payoff semantics.

Design 1 is adopted. Design 2 loses the counterfactual coefficient under
normalization. Design 3 adds an unnecessary intermediary before the required
semantic identity. Design 4 duplicates owners already validated by D6, D32,
and D44.

## Hostile evidence

Nature selects one of two hidden histories in a shared decision information
site. Matching hidden `true` pays two and matching `false` pays one. Against a
fully mixed policy, committing to `true` has exact counterfactual regret
`1/4`; committing to `false` has exact regret `-1/4`. Thus the action-local
surface retains both a profitable replacement and a strictly harmful control.

The fixture proves common focal reach on the entire information fiber and uses
the weaker named certificate directly; it does not silently claim global
perfect recall. Separately, the generic proof identifies focal reach with the
probability of the existing `ownPlay` record, from which perfect recall
discharges the certificate. Positive canonical information mass proves that
the common focal factor is positive, so the familiar sign theorem needs no
extra reach premise.

The narrow source/consumer build completed 1,775 jobs and the stable aggregate
completed 1,776 jobs warning-free. Both fast expected architecture audits
report `VERIFIED=1`; the full build completed 3,585 jobs warning-free. Deep
reachability mode was not run.

## Kill conditions and result

Reject the package if its main theorem does not consume counterfactual reach;
if normalized beliefs erase the required reach factor; if repeated information
states are treated as perfect recall without proof; if the local quantity does
not characterize an ordinary canonical behavioral deviation gain; or if a
second runner, payoff, deviation, history, equilibrium predicate, raw update,
or stored global finiteness is needed. No kill condition fired.

The action-local specialization uses the existing transport-free
`BehavioralPolicy.commit`; the general whole-policy theorem remains useful for
continuation deviations. This is a regret decomposition, not a cumulative CFR
algorithm or a convergence theorem.

## Public API consequences

Add `GameTheory.Analysis.Protocol.CounterfactualRegret` to the opt-in Protocol
analysis root. Keep all declarations on generic `InformationModel`; FOSG gains
them through its existing Protocol interpretation rather than a native CFR
semantics.

The next gate is cumulative counterfactual regret over a repeated update trace
and a convergence theorem with a canonical exploitability or average-regret
consumer. It must use this action-local decomposition and include a
nonconvergent or positive-regret control; definition-shaped CFR coverage does
not count.
