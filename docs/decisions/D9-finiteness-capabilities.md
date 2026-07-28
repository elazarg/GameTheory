# D9: finiteness is a set of independent capabilities

- **Status:** accepted
- **Date:** 2026-07-26
- **Experiment IDs:** EXP-005, EXP-006, EXP-007

**Decision:** No monolithic `FiniteGame` assumption enters the semantic core.
Each operation and theorem carries only the finiteness it needs. Proof-oriented
statements use propositional finiteness where enumeration data is irrelevant;
the executable frontend carries and consistently uses its own `Fintype` and
`DecidableEq`.

## Capability table

This replaces the RFC's illustrative table with the assumptions actually used
by the Phase 2 slice. "finite players" means `Fintype ι`; "decidable players"
means `DecidableEq ι`.

| Definition or theorem | finite players | finite strategies | finite outcomes | decidable players |
|---|---|---|---|---|
| `GameSignature`, `Profile`, `Subprofile` | no | no | no | no |
| `Profile.restrict` | no | no | no | no |
| `Profile.update`, `Profile.override` | no | no | no | yes |
| `FinDist` operations, `expect`, `expect_bind` | no | no | no | no |
| `FinDist.pi` (independent product) | yes | no | no | no |
| `FinDist.sum_prob`, `FinDist.ofWeights` | no | finite carrier | n/a | no |
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
| `IsRationalizable`, `IsNash.isRationalizable` | no | no | no | yes |
| `TableGame` and every boolean procedure | yes | yes | outcome = profile | yes |
| `mem_enumerateNash_iff`, `mem_survivors_iff` | yes | yes | — | yes |
| `verifyMixedNash_eq_true_iff` | yes | yes | — | yes |
| Bayesian `isNash_iff_interim` | yes | no (finite types) | no | yes |

The three columns separate cleanly. The whole equilibrium family needs only
decidable players, because that is what branching on membership in
`Profile.override` requires. Finite players appear exactly where an independent
product is formed. Finite strategy carriers appear only in the executable
frontend and in the interim decomposition over a player's own type.

Finite *support* never appears as a hypothesis: it is a field of `FinDist`, so
`expect` and `expect_bind` are unconditional.

## Kill condition

Introduce a bundled capability only if at least five adjacent public theorems
repeat exactly the same assumption set and the bundle reduces user work without
causing instance ambiguity. The largest repeated set in the table is
`[Fintype ι] [DecidableEq ι]`, which is confined to the executable frontend
where those instances come from the game's own fields; bundling them into a
semantic structure would put enumeration data into proof semantics for no gain.

## Result

Accept. `Fintype.ofFinite` is used nowhere in the repository, which the audit
checks. The executable frontend's `actionFintype`/`actionDecEq` fields are the
authoritative instances throughout compilation and correctness proofs.

## Consequences for public API

Adding a theorem means adding its own capability hypotheses. A convenience
bundle for examples may be added later, but it is not the foundational game
type.
