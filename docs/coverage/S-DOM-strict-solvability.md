# S-DOM: strict dominance and dominant-strategy solvability

Title: Strict dominance, best response, and unique Nash
Family ID: S-DOM
Pinned roots: `GameTheory/Concepts/Dominance/DominanceNash.lean`; `GameTheory/Concepts/Dominance/DominanceSolvable.lean`; `GameTheory/Concepts/Dominance/DominanceSolvability.lean`; `GameTheory/Concepts/Dominance/StrictDominance.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `188d6f6`
Canonical destination: `GameTheory.Core.Response`
Domain contract / decision: D4, D5; post-architecture S-DOM BFS gate
Owner: Wave 1 / static response
Status: complete; all 15 declarations adapted with no deferred rows
Last verified: 2026-08-09

The successor states strict dominance over the canonical `GameForm`,
preference, and `Profile.update` surface.  Reflexivity is requested only when a
strictly dominant strategy is weakened to an ordinary dominant strategy or
used to construct Nash; uniqueness itself needs no global preference class.
The proof-only dominant-profile selector stores no finiteness and does not
pretend to be executable search.  Prisoner's Dilemma is the non-singleton
fixture: defection strictly dominates cooperation for both players, and the
generic theorem supplies existence and uniqueness of Nash without enumeration.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Dominance/DominanceNash.lean` | `not_in_nash_of_not_best_response` | theorem | adapt | `not_in_nash_of_not_isBestResponse` | focused Core build | Uses canonical `IsBestResponse` and `IsNash`. |
| same | `StrictlyDominates.not_nash` | theorem | adapt | `StrictlyDominates.not_isNash` | focused Core build | Generic preferences replace kernel-game utilities. |
| same | `IsStrictDominant.unique_best_response` | theorem | adapt | `IsStrictDominant.eq_of_isBestResponse` | focused Core build | Strictness contradicts the reverse best-response comparison directly. |
| `GameTheory/Concepts/Dominance/StrictDominance.lean` | `IsStrictDominant.toDominant` | theorem | adapt | `IsStrictDominant.toDominant` | focused Core build | Preference reflexivity is explicit at the weakening operation. |
| same | `strictly_dominant_is_nash` | theorem | adapt | `isNash_of_forall_isStrictDominant` | focused Core build | One canonical Nash predicate. |
| same | `strictly_dominant_unique_nash` | theorem | adapt | `IsNash.eq_of_forall_isStrictDominant` | focused Core build | Uniqueness is independent of the selector. |
| `GameTheory/Concepts/Dominance/DominanceSolvability.lean` | `IsDominantStrategySolvable` | def | adapt | `IsDominantStrategySolvable` | focused Core build | Strong one-round solvability remains distinct from iterated elimination. |
| same | `IsDominantStrategySolvable.dominantProfile` | def | adapt | `IsDominantStrategySolvable.dominantProfile` | focused Core build | Classical proof selector, not an executable algorithm. |
| same | `IsDominantStrategySolvable.isNash` | theorem | adapt | `IsDominantStrategySolvable.isNash` | focused Core build | Reflexivity appears only on existence. |
| same | `IsDominantStrategySolvable.nash_unique` | theorem | adapt | `IsDominantStrategySolvable.nash_eq_dominantProfile` | focused Core build | Any Nash profile uses each unique best response. |
| same | `IsDominantStrategySolvable.exists_unique_nash` | theorem | adapt | `IsDominantStrategySolvable.existsUniqueNash` | focused Core and hostile example build | Packages the generic existence/uniqueness result. |
| `GameTheory/Concepts/Dominance/DominanceSolvable.lean` | `StrictlyDominates.not_best_response` | theorem | adapt | `StrictlyDominates.not_isBestResponse` | existing `Core.Response` theorem | Pure strict domination rules out best response. |
| same | `WeaklyDominatesReflexive.best_response_of_best_response` | theorem | adapt | `WeaklyDominates.isBestResponse_of_isBestResponse` | focused Core build | Preference transitivity is explicit rather than baked into an EU-only relation. |
| same | `nash_never_strictly_dominated` | theorem | adapt | `IsNash.not_strictlyDominates` | existing `Core.Response` theorem | Nash survives canonical pure iterated dominance. |
| same | `IsDominant.isBestResponse` | theorem | adapt | `IsDominant.isBestResponse` | existing `Core.Response` theorem | Exact canonical owner. |

Attribution: the predecessor supplied the strict-dominance/unique-equilibrium
theorem family.  The successor generalizes it from a utility-specialized
kernel game to the canonical preference-parametric static form and keeps
assumptions local.

Remaining S-DOM work is not hidden by this ledger: mixed-strategy domination
and Bernheim--Pearce rationalizability are now closed by
[`S-DOM-rationalizability.md`](S-DOM-rationalizability.md).
IESDS-to-correlated-equilibrium support, the undominated
existence/counterexample family, and transform laws remain separate bounded BFS
batches.

The unique-best-response theorem, generic existence/uniqueness theorem, and
Prisoner's Dilemma flagship depend only on `propext`, `Classical.choice`, and
`Quot.sound`.  Source checks find no raw `Function.update`, source transport,
placeholder, custom axiom, or build-output command.

Validation:

```text
lake build GameTheory.Core.Response GameTheory.Examples.Classic
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected -SkipReachability
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
lake build
git diff --check
```
