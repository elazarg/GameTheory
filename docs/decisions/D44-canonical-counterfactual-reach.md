# D44: Derive counterfactual reach from canonical behavioral histories

- **Status:** adopted; coefficient and continuation package promoted
- **Date:** 2026-08-10
- **Experiment ID:** EXP-081

## Decision

Keep `InformationModel.historyReachProbability` as the sole actual history
reach semantics. Define only the focal action product and the complementary
counterfactual product on canonical `ExecutionProtocol.Trace`, and prove that
their product is the existing canonical reach probability.

One-step coefficients must be literal masses of the canonical
`runBehavioralFrom` continuation law. No FOSG-native history, runner, scalar
probability carrier, or bridge-specific equilibrium predicate is admitted.

## Competing designs

1. Factor the canonical behavioral joint and history laws.
2. Restore the retired FOSG runner and its recursive probability functions.
3. Introduce a second recursive actual trace weight beside
   `historyReachProbability`.
4. Defer every coefficient until a complete CFR theorem fixes the API.

Design 1 is adopted. The spike briefly implemented Design 3, then rejected it
when the existing canonical reach definition was found. Design 2 duplicates
accepted execution semantics. Design 4 would prevent a separately useful
continuation and regret interface from stabilizing.

## Hostile evidence

The simultaneous two-player fixture selects one joint and terminal transition.
Changing only the focal player's action mass from one to zero changes actual
history reach from one to zero while full counterfactual reach stays one.
Changing only the opponent makes that counterfactual reach zero, proving that
the nonfocal factor was retained rather than discarded.

The second fixture uses one player who is consulted twice at the same
information state and randomizes independently each time. Its two focal
factors are both `1/2`; recursive player reach and canonical history reach are
`1/4`, while counterfactual reach is one. This rejects an implementation that
merely renames the last one-step factor.

The narrow source/consumer build completed 1,738 jobs warning-free, both fast
expected audits report `VERIFIED=1`, and the full build completed 3,583 jobs
warning-free. Deep reachability mode was not run.

## Continuation and factorization results

`behavioralJoint_prob_eq_prod` derives local coordinate masses from
`FinDist.pi`. `runBehavioralFrom_one_prob_extend` proves that a joint and
transition coefficient is exactly the probability of the corresponding
canonical history extension. `historyReachProbability_extend` then proves the
full continuation equation from the actual runner.

`historyReachProbability_eq_player_mul_counterfactual` is the public semantic
payoff: canonical reach equals focal reach times counterfactual reach on every
indexed trace. `counterfactualReachProbability_eq_of_eq_off` proves invariance
under any change to the focal behavioral policy.

## Kill conditions and result

Reject the package if focal-policy changes alter counterfactual reach; if
opponent or chance mass disappears; if the recursive factors do not compute
the canonical history law; if a second runner, history, actual-reach concept,
or probability carrier is needed; or if no continuation theorem consumes the
coefficient. No kill condition fired. The attempted duplicate actual reach was
removed before promotion.

## Public API consequences

Add the opt-in `GameTheory.Analysis.Protocol.CounterfactualReach` leaf and
include it in `GameTheory.Analysis.Protocol`. Keep the definitions on generic
`InformationModel`, so FOSG uses them through its canonical Protocol semantics
rather than owning a parallel analysis layer.

This decision delivers coefficients and continuation identities, not CFR.
The next gate is a regret decomposition with a direct coefficient consumer;
CFR convergence follows only after that theorem fixes the needed update and
regret surface.
