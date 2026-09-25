# D9: finiteness is a set of independent capabilities

- **Status:** accepted
- **Date:** 2026-07-26
- **Experiment IDs:** EXP-005, EXP-006, EXP-007; PMF scope under EXP-122–140

**Decision:** No monolithic `FiniteGame` assumption enters the semantic core.
Each operation and theorem carries only the finiteness it needs. Proof-oriented
statements use propositional finiteness where enumeration data is irrelevant;
the executable frontend carries and consistently uses its own `Fintype` and
`DecidableEq`.

## Capability table

These selected foundational operations separate carrier finiteness from
integration. "finite players" means `Fintype ι`; "decidable players" means
`DecidableEq ι`. The table does not list payoff integration or other
non-finiteness premises.

| Definition or theorem | finite players | finite strategies | finite outcomes | decidable players |
|---|---|---|---|---|
| `GameSignature`, `Profile`, `Subprofile` | no | no | no | no |
| `Profile.restrict` | no | no | no | no |
| `Profile.update`, `Profile.override` | no | no | no | yes |
| PMF operations and guarded expectation/tower laws | no | no | no | no |
| `independentProduct` over player laws | yes | no | no | no |
| `PMF.ofFintype` | no | finite carrier | n/a | no |
| `GameForm`, `GameForm.outcomeLaw` | no | no | no | no |
| `GameForm.mapOutcome` | no | no | no | no |
| `GameForm.mixed` | yes | no | no | no |
| `GameForm.mixed_play_purify`, `pi_update_mixed` | yes | no | no | yes |
| `DeviationScheme`, `actLocal_local` | no | no | no | no |
| `DeviationScheme.apply`, `IsEquilibrium` | no | no | no | yes |
| `IsNash`, `IsCoarseCorrelatedEq`, `IsCorrelatedEq`, `IsStrongNash` | no | no | no | yes |
| `expectedUtility`, `euPreference`, affine invariance | no | no | no | no |
| `isCoarseCorrelatedEq_randomized` | no | no | no | yes |
| `isNash_mixed_iff` | yes | no | no | yes |
| `IsBestResponse`, `WeaklyDominates`, `IsDominant` | no | no | no | yes |
| `IsCorrelatedRationalizable`, `IsNash.isCorrelatedRationalizable` | no | no | no | yes |
| `SurvivesAllPureEliminationRounds`, `IsNash.survivesAllPureEliminationRounds` | no | no | no | yes |
| `TableGame` and every boolean procedure | yes | yes | outcome = profile | yes |
| `mem_enumerateNash_iff`, `mem_pureSurvivors_iff` | yes | yes | — | yes |
| `verifyMixedNash_eq_true_iff` | yes | yes | — | yes |
| Bayesian `isNash_iff_interim` | no | no (types may also be infinite) | no | yes |

The equilibrium predicates themselves need no finite carriers. Finite player
enumeration is needed for the discrete independent product; a bounded play
horizon does not supply finite support or a finite information-site cover.
The executable frontend carries its finite strategy enumerations explicitly.
The general interim/ex-ante theorem needs integration of actual whole-plan
deviations, not finite type spaces.

Finite support is an operation-local hypothesis when a finite decomposition or
enumeration needs it. It is one sufficient condition for payoff integration.
General expectation and tower laws instead carry the integration certificates
their actual laws require; integration is not a field of every game.

## Kill condition

Introduce a bundled capability only if at least five adjacent public theorems
repeat exactly the same assumption set and the bundle reduces user work without
causing instance ambiguity. Repeated local hypotheses alone do not justify
storing enumeration data in semantic game structures. The executable
frontend's own fields supply its enumerations; proof theorems request their
capabilities separately.

## Result

The executable frontend's `actionFintype`/`actionDecEq` fields are the
authoritative instances throughout compilation and correctness proofs.
Executable modules may not replace them with `Fintype.ofFinite` or classical
enumerations; source and import audits enforce that boundary.

## Consequences for public API

Adding a theorem means adding its own capability hypotheses. A convenience
bundle for examples may be added later, but it is not the foundational game
type.
