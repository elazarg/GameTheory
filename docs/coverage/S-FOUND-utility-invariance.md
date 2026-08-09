# S-FOUND: positive-affine utility invariance

Title: Utility-scale invariance of Nash and dominance
Family ID: S-FOUND
Pinned root: `GameTheory/Concepts/Foundations/UtilityInvariance.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `ce09ac0`
Canonical destination: `GameTheory.Core.UtilityInvariance`
Domain contract / decision: D4-D5
Owner: Wave 2 / foundations recovery
Status: complete bounded file; 4/4 declarations reviewed
Last verified: 2026-08-09

The successor proves invariance from the existing law-level
`euPreference_affine` theorem.  It applies to every canonical `GameForm`,
including stochastic outcome laws, rather than reconstructing the predecessor's
deterministic expected-utility wrapper.

| Pinned path | Declaration | Kind | Disposition | Successor declaration | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Foundations/UtilityInvariance.lean` | `ofEU_nash_affine` | theorem | adapt | `GameTheory.isNash_affine` | focused Core/test build; positive-scale witness | Generic over canonical game forms and their outcome laws. |
| same | `ofEU_isDominant_affine` | theorem | adapt | `GameTheory.isDominant_affine` | focused Core/test build; dominant-action witness | Reuses the sole Core dominance predicate. |
| same | `ofEU_nash_shift` | theorem | adapt | `GameTheory.isNash_shift` | focused Core build | Player-specific shifts are the unit-scale specialization. |
| same | `ofEU_nash_scale` | theorem | adapt | `GameTheory.isNash_scale` | focused Core build; negative-scale control | The public hypothesis is strictly positive; the hostile fixture proves it cannot be weakened to arbitrary nonzero scale. |

Disposition count: 4 adapted.

Attribution: the pinned file supplies the four solution-concept invariance
statements.  The successor proof factors them through the already-canonical
finite-law affine expectation and preference lemmas, with no new equilibrium,
probability, or deterministic-game surface.

Validation: the focused utility-invariance leaf, hostile test, and Core-root
build completed 1,750 jobs warning-free.  On a binary one-player form, scale
`3` and shift `7` preserve both the Nash and dominant action, while scale `-1`
destroys the original Nash profile and makes the other action Nash.
The full reachability audit returned `VERIFIED=1`, reaching all four intended
Core inputs and rejecting all three Analysis/Protocol/stochastic-domain probes.
The two generic invariance theorems and three representative hostile facts
depend only on `propext`, `Classical.choice`, and `Quot.sound`.  Exact coverage
returned `VERIFIED=1`, and the warning-clean default build completed all 3,529
jobs.
