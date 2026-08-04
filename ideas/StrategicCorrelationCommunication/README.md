# Strategic correlation and communication

| Lifecycle | Verdict | Priority | Group decision |
|---|---|---|---|
| `ACTIVE` | `MIXED` | `P2` | Keep as a bounded interface audit: separate public randomness, private recommendations, deviation-safe signaling, and asymptotically negligible setup cost before proposing any compiler. |

This group asks when players can strategically manufacture a usable correlation resource from actions observed through public monitoring. The issue is not ordinary bit complexity. It is whether sampling preserves privacy and obedience, remains robust to unilateral deviations, and avoids irreversible payoff or state-transition costs.

| Claim | Status | Role |
|---|---|---|
| [Standard quitting has no live public communication channel](StandardQuittingHasNoLivePublicCommunicationChannel.md) | `PROVED (M+L), model-local` | Exact negative structural fact for the repository's standard quitting-game encoding. |
| [Public transcripts do not automatically implement private recommendations](PublicTranscriptsDoNotAutomaticallyImplementPrivateRecommendations.md) | `MIXED: distinction proved; general compiler question open` | Prevents public correlation from being silently identified with private contingent advice. |
| [Safe signaling actions may compile sunspot randomness](SafeSignalingActionsMayCompileSunspotRandomness.md) | `CONDITIONAL (M+L interfaces)` | Records the positive route and its transition, deviation, disclosure, and splice hypotheses. |
| [Fixed-target communication separation does not rule out retargeting](FixedTargetCommunicationSeparationDoesNotRuleOutRetargeting.md) | `PROVED (M+L), scope fence` | Keeps target-specific nonimplementation separate from existence of some equilibrium payoff. |
| [Device guarantees need quotient measurability on both sides](DeviceGuaranteesNeedQuotientMeasurabilityOnBothSides.md) | `M [reported]` unification; instances at `X`, `M+L` | Unifies three device failures — group-sum input-side, action-padding output-side, jointly-controlled-XOR factorization — and decides which repair of the padding converse is load-bearing. |
| [Fixed setup communication cost is asymptotically negligible](FixedSetupCommunicationCostIsAsymptoticallyNegligible.md) | `PROVED (M+L), accounting only` | Removes fixed finite prefix cost as a standalone Cesaro obstruction while preserving irreversibility and incentive caveats. |

## Group boundary

The current production library supplies exact one-step and finite-prefix interfaces, not a universal endogenous-correlation theorem. In particular, this group does **not** assert that arbitrary-behavior payoff gaps are semialgebraic, that a public coin is equivalent to a private recommendation device, or that a separator for one mediated target refutes ordinary uniform-equilibrium existence.

Three resources remain separate throughout: an exogenous public sunspot observed by all players; an autonomous private/history-dependent recommendation device with delayed disclosure; and a jointly controlled lottery used to de-correlate a public construction under extra safe-action hypotheses. None is silently substituted for another.

## Main consumers

- [Question 100: Endogenous/autonomous correlation compiler](../../questions/old/Question100-EndogenousAutonomousCorrelationCompiler.md)
- [Uniform-equilibrium pipeline](../../docs/uniform-equilibrium/PIPELINE.md), if a future compiler or impossibility theorem becomes a selected pipeline project
- The stochastic-game correlation and public-controller production modules linked from the individual claim files

## Group exit

Archive this group when its fences have been absorbed into the relevant question and theorem documentation, or promote it only after either (i) a compiler with explicit privacy, obedience, deviation, transition, and splice hypotheses lands, or (ii) a selectorwise impossibility theorem is proved. A further fixed-target example or a raw count of communication bits is not a promotion trigger.
