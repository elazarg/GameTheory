# D43: Compile selected intrinsic solutions directly to the static core

- **Status:** adopted; fixed-nature pure strategic leaf approved
- **Date:** 2026-08-10
- **Experiment ID:** EXP-079

## Decision

For an intrinsic model with a unique-solvability certificate and a
caller-supplied nature value, compile agent-owned pure decision rules directly
to a `GameForm`. The deterministic outcome is the complete configuration whose
decision coordinates are the selected closed-loop solution. Utilities remain
external, and equilibrium is the canonical core `IsNash` predicate.

Do not choose a temporal Protocol execution merely to evaluate a closed-loop
profile. Do not define intrinsic-specific utility or equilibrium predicates.

## Competing designs

1. Direct selected-solution `GameForm` at a fixed nature value.
2. Temporal Protocol compilation before any utility or equilibrium question.
3. A native intrinsic utility/equilibrium hierarchy parallel to Core.

Design 1 is adopted. It preserves the native simultaneous fixed-point meaning
and reaches shared solution concepts with one deterministic outcome law.
Design 2 adds chronology that the tested question does not need. Design 3
duplicates the accepted form/preference/utility and deviation semantics.

## Hostile evidence

EXP-079 uses the causal Boolean signaling model: the sender observes nature,
and the receiver observes the sender decision. At nature `true`, truthful
signaling followed by copying is Nash. Under the control profile, both selected
decisions are false. Replacing only the sender's complete rule re-solves the
closed loop, changes the receiver decision too, and raises payoff from zero to
one. Thus the deviation coordinate is genuinely owner-local while its outcome
effect is not coordinate-local.

The 164-nonblank-line spike has 17 declarations and imports only stable
Intrinsic/Solution code plus `Core.Utility`. It needs no stored finiteness,
probability field, temporal runner, public transport, or trust exception.

## Kill conditions and result

Reject the direct compiler if the downstream fixed-point effect is invisible;
if compilation needs stored capabilities or temporal execution; if utility
must enter `Model`; or if a second solution predicate is needed. No kill
condition fired. The positive Nash witness and profitable-deviation control
both compile warning-free.

## Public API consequences

Add an opt-in `GameTheory.Languages.Intrinsic.Strategic` leaf containing:

- the intrinsic pure strategic signature;
- `Model.toGameForm` parameterized by `IsSolvable` and a nature value;
- the exact pure selected-configuration play law; and
- a canonical Nash iff exposing re-solved unilateral deviations.

Keep `Model` capability-light and utility-free. Nature lotteries, temporal
compilation, behavioral/mixed strategies, recall, and Kuhn results remain
separate measured gates.
