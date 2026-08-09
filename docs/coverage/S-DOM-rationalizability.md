# S-DOM: mixed and pure rationalizability

Title: Bernheim--Pearce rationalizability and pure-elimination separation
Family ID: S-DOM
Pinned roots: `GameTheory/Concepts/Dominance/DominanceSolvable.lean`;
`GameTheory/Concepts/Dominance/Rationalizability.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `18e947b`
Canonical destinations: `GameTheory.Core.Rationalizability`;
`GameTheory.Core.Response`; `GameTheory.Finite`
Domain contract / decision: D4, D5, D9, D10, D40; EXP-073
Owner: Wave 2 / static response
Status: complete bounded files; 21/21 selected declarations reviewed
Last verified: 2026-08-09

Standard rationalizability eliminates by finite-support mixed dominators and
owns the unqualified names.  The weaker pure iteration and D10 checker say
`pure` explicitly.  Both use canonical `GameForm`, `FinDist`, preferences, and
`Profile.update`; no compatibility alias or second equilibrium layer survives.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or chain | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Dominance/DominanceSolvable.lean` | `StrictlyDominatedByMixed` | def | adapt | `GameTheory.StrictlyDominatedByMixed` | EXP-073 hostile hedge | Uses canonical randomized outcome laws. |
| same | `StrictlyDominatedByMixed.not_best_response` | theorem | adapt | `GameTheory.StrictlyDominatedByMixed.not_isBestResponse` | focused Core build | Expected-utility linearity defeats the mixed dominator. |
| same | `StrictlyDominates.toStrictlyDominatedByMixed` | theorem | adapt | same name under `GameTheory` | focused Core build | A point mass is the pure special case. |
| `GameTheory/Concepts/Dominance/Rationalizability.lean` | `Survives` | def | adapt | `GameTheory.survivors` | mixed-round hostile witness | Unqualified survival is standard mixed elimination. |
| same | `Survives.prev` | theorem | subsumed | `GameTheory.survivors_antitone` | focused Core build | The set inclusion is the reusable elimination rule. |
| same | `Survives.mono` | theorem | adapt | `GameTheory.survivors_mono` | focused Core build | Arbitrary round monotonicity. |
| same | `IsRationalizable` | def | adapt | `GameTheory.IsRationalizable` | D40 | Survives every mixed round. |
| same | `IsNash.survives` | theorem | adapt | same name under `GameTheory` | focused Core build; axiom audit | Reuses randomized-deviation CCE linearity. |
| same | `IsNash.isRationalizable` | theorem | adapt | same name under `GameTheory` | focused Core build | Canonical Nash is the sole equilibrium input. |
| same | `dominantProfile_survives` | theorem | adapt | `GameTheory.dominantProfile_survives` | focused Core build | Dominant profile implies canonical Nash, then survival. |
| same | `IsDominant.isRationalizable` | theorem | adapt | same name under `GameTheory` | focused Core build | Other players' dominant filler remains explicit. |
| same | `IsRationalizable.not_globally_dominated` | theorem | adapt | `GameTheory.IsRationalizable.not_strictlyDominatedByMixed` | focused Core build | First-round elimination. |
| same | `IsStrictDominant.not_rationalizable_of_ne` | theorem | adapt | `GameTheory.IsStrictDominant.not_isRationalizable_of_ne` | focused Core build | Every distinct action has a point-mass dominator. |
| same | `SurvivesPure` | def | adapt | `GameTheory.pureSurvivors` | D40; pure checker witness | Weaker notion is explicit. |
| same | `SurvivesPure.prev` | theorem | subsumed | `GameTheory.pureSurvivors_antitone` | focused Core build | One-step inclusion. |
| same | `SurvivesPure.mono` | theorem | adapt | `GameTheory.pureSurvivors_mono` | focused Core build | Arbitrary round monotonicity. |
| same | `IsPureRationalizable` | def | adapt | `GameTheory.IsPureRationalizable` | D40 | No semantic overloading. |
| same | `IsNash.survivesPure` | theorem | adapt | same name under `GameTheory` | focused Core build | Preference-parametric strengthening. |
| same | `IsNash.isPureRationalizable` | theorem | adapt | same name under `GameTheory` | focused Core build | Preference-parametric strengthening. |
| same | `dominantProfile_survivesPure` | theorem | adapt | `GameTheory.dominantProfile_survivesPure` | focused Core build | Preference-parametric strengthening. |
| same | `IsDominant.isPureRationalizable` | theorem | adapt | same name under `GameTheory` | focused Core build | Preference-parametric strengthening. |

Disposition count: 19 adapted, 2 subsumed.

Attribution: the pinned files supply the mixed-dominance definition, the
Bernheim--Pearce survivor iteration, its pure comparison notion, and all
survival consequences.  D40 changes names and ownership only where needed to
make the mathematical distinction explicit.

Validation: the focused Core, Finite correctness, hostile test, Core root, and
Classic examples build completed 1,754 jobs warning-free.  In the hostile
three-action game, action two pays `3/4` against every column; no pure action
strictly dominates it, but the half/half mixture of actions zero and one pays
`1` everywhere.  It survives pure round one, including the executable D10
certificate, and fails standard mixed round one.
The full Phase 2 audit returned `VERIFIED=1`, reaching all six intended
rationalizability inputs and rejecting all three finite/Protocol/Analysis
boundaries.  The mixed-dominance/best-response theorem, Nash and dominant
survival, hostile separation, and executable certificate depend only on
`propext`, `Classical.choice`, and `Quot.sound`.  Exact coverage returned
`VERIFIED=1`, and the warning-clean default build completed all 3,531 jobs.
