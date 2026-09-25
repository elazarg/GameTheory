# D44: Derive counterfactual reach from canonical behavioral histories

- **Status:** adopted
- **Date:** 2026-08-10
- **Experiment ID:** EXP-081

## Decision

Keep `InformationModel.historyReachWeight` as the sole actual history reach
semantics. Define only the focal action product and the complementary
counterfactual product on canonical `ExecutionProtocol.Trace`, and prove that
their product is the existing canonical reach probability.

One-step coefficients must be literal masses of the canonical
`runBehavioralFrom` continuation law. No FOSG-native history, runner, scalar
probability carrier, or bridge-specific equilibrium predicate is admitted.

## Competing designs

1. Factor the canonical behavioral joint and history laws.
2. Restore the retired FOSG runner and its recursive probability functions.
3. Introduce a second recursive actual trace weight beside
   the canonical history reach atom.
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

EXP-081 records the artifacts and validation evidence for these controls.

## Continuation and factorization results

`behavioralJoint_prob_eq_prod` derives local coordinate masses from
the independent PMF product. `runBehavioralFrom_one_prob_extend` proves that a joint and
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

The coefficient and continuation interface is independent of a particular
regret algorithm. A CFR theorem must additionally connect its update rule to
regret decomposition; the reach factorization alone does not establish
convergence.

## Probability ownership

The exact-depth runner atom is the `ENNReal`-valued `historyReachWeight`,
owned by `Protocol.HistoryEvents`. Real counterfactual coefficients convert
that same atom at their numerical boundary; no parallel actual-reach
definition was restored. `Protocol.HistoryPathMass` supplies the generic
predecessor factor, replacing the duplicated extension case split.
The support-indexed injective pure-bind atom lemma belongs to game-independent
`Math.Probability.Support`.

The source audit names this numerical coefficient owner and its focused
`CounterfactualReachTest` fixture explicitly. The latter compares the canonical
reach atom's real value with the player/counterfactual factorization, including
the repeated-site value `1 / 4`; this conversion is part of the quantity being
tested. Other fixtures retain the ordinary PMF mass or guarded-expectation API.

The coefficient source has no Bayesian normalization dependency. PMF
restoration validation is recorded in the worklog and experiment log.
