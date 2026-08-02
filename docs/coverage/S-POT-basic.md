# S-POT: basic potential games

Title: Exact and ordinal potentials, finite improvement, and team games
Family ID: S-POT
Pinned roots: `GameTheory/Concepts/Potential/PotentialGame.lean`,
`PotentialFIP.lean`, `PotentialWellFounded.lean`, and `PotentialTeam.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `a829d9d`
Canonical destination: `GameTheory.Core.Potential`, with shared primitives in
`GameTheory.Core.Utility` and `GameTheory.Core.Response`, and the zero-sum/team
consequence in `GameTheory.Core.ZeroSum`
Domain contract / decision: D4-D5, D8-D10
Owner: Wave 2 / static theory
Status: complete; 22/22 declarations reviewed
Last verified: 2026-08-02

This bounded ledger covers the complete basic potential-game suite at the four
pinned roots. All results use the canonical `GameForm`, `Profile.update`,
`expectedUtility`, and ordinary `IsNash`; shared response and utility concepts
live below Potential, while the zero-sum/team intersection lives with zero-sum
theory. No `KernelGame`, `IsNashPure`, better-response scheduler, or
compatibility predicate is retained.

| Pinned path | Declaration | Kind | Disposition | Successor declaration | Evidence | Notes |
|---|---|---|---|---|---|---|
| `Concepts/Potential/PotentialGame.lean` | `IsExactPotential.toOrdinal` | theorem | adapt | `GameTheory.IsExactPotential.isOrdinalPotential` | focused Core build | Exact real differences preserve strict-improvement signs. |
| same | `IsOrdinalPotential.nash_of_maximizer` | theorem | adapt | `GameTheory.IsOrdinalPotential.isNash_of_maximal` | focused Core build | The canonical outcome is ordinary expected-utility `IsNash`. |
| same | `IsExactPotential.nash_of_maximizer` | theorem | adapt | `GameTheory.IsExactPotential.isNash_of_maximal` | focused Core build | Exact specialization of the ordinal theorem. |
| same | `IsOrdinalPotential.isNash_iff_local_maximizer` | theorem | adapt | `GameTheory.IsOrdinalPotential.isNash_iff_local_maximal` | focused Core build | Uses the existing profile-update operation; only spelling changes. |
| `Concepts/Potential/PotentialFIP.lean` | `IsExactPotential.eu_diff_eq_potential_diff` | theorem | adapt | `GameTheory.IsExactPotential.expectedUtility_diff_eq_potential_diff` | focused Core build | Named exact-difference equality over finite outcome laws. |
| same | `IsExactPotential.improving_deviation_increases_potential` | theorem | adapt | `GameTheory.IsExactPotential.improving_deviation_increases_potential` | focused Core build | Direct canonical expected-utility statement. |
| same | `IsExactPotential.no_improving_at_maximizer` | theorem | adapt | `GameTheory.IsExactPotential.no_improving_at_maximal` | focused Core build | No strict gain at a global potential maximum. |
| same | `IsExactPotential.strictNash_of_strict_maximizer` | theorem | adapt | `GameTheory.IsExactPotential.isStrictNash_of_strict_maximal`; `GameTheory.IsStrictNash` | focused Core build | Potential consumes the strict refinement owned by Core.Response. |
| same | `IsExactPotential.isNash_iff_local_maximizer` | theorem | adapt | `GameTheory.IsExactPotential.isNash_iff_local_maximal` | focused Core build | Derived through ordinal potential, with no parallel Nash definition. |
| same | `IsExactPotential.nash_exists` | theorem | adapt | `GameTheory.IsExactPotential.exists_isNash` | focused Core build | Existing finite maximization theorem already supplied this result. |
| `Concepts/Potential/PotentialWellFounded.lean` | `IsExactPotential.improvingStep_increases_potential` | theorem | adapt | `GameTheory.IsExactPotential.improvingStep_increases_potential` | focused Core build | Improvement edge is tied to canonical profile updates. |
| same | `IsExactPotential.no_infinite_improving_path` | theorem | adapt | `GameTheory.IsExactPotential.no_infinite_improving_path` | focused Core build | Uses finite profile space and injectivity of a strictly increasing potential sequence. |
| same | `WeaklyAcyclic` | definition | adapt | `GameTheory.WeaklyAcyclic`; `GameTheory.ImprovingStep` | focused Core build | Potential owns the convergence property while Core.Response owns the canonical edge relation. |
| same | `IsOrdinalPotential.improvingStep_increases_potential` | theorem | adapt | `GameTheory.IsOrdinalPotential.improvingStep_increases_potential` | focused Core build | Ordinal forward implication. |
| same | `IsOrdinalPotential.improvingStep_filter_card_lt` | theorem | adapt | `GameTheory.IsOrdinalPotential.improvingStep_filter_card_lt` | focused Core build | Finite higher-potential rank strictly drops. |
| same | `weaklyAcyclic_of_wellFounded` | theorem | adapt | `GameTheory.weaklyAcyclic_of_wellFounded` | focused Core build | General well-founded induction; needs neither finiteness nor potential. |
| same | `IsOrdinalPotential.improvement_wellFounded` | theorem | adapt | `GameTheory.IsOrdinalPotential.improvement_wellFounded` | focused Core build | Finite rank proves well-founded strict improvement. |
| same | `IsOrdinalPotential.weaklyAcyclic` | theorem | adapt | `GameTheory.IsOrdinalPotential.weaklyAcyclic` | focused Core build | Combines rank well-foundedness with the generic theorem. |
| same | `IsExactPotential.weaklyAcyclic` | theorem | adapt | `GameTheory.IsExactPotential.weaklyAcyclic` | focused Core build | Exact specialization. |
| `Concepts/Potential/PotentialTeam.lean` | `IsTeamGame.isExactPotential` | theorem | adapt | `GameTheory.IsTeamGame.isExactPotential`; `GameTheory.IsTeamGame.expectedUtility_eq` | focused Core build | Core.Utility owns team equality; Potential consumes it to build the exact potential. |
| same | `IsTeamGame.nash_iff_local_potential_max` | theorem | adapt | `GameTheory.IsTeamGame.isNash_iff_local_potential_maximal` | focused Core build | An anchor player's expected utility is the potential. |
| same | `IsZeroSum.teamGame_utility_zero` | theorem | adapt | `GameTheory.IsZeroSum.teamGame_utility_zero` | focused Core build | The cross-family consequence lives in Core.ZeroSum; it combines the existing zero-sum and utility-owned team definitions. |

Disposition count: 22 adapt; 0 subsumed; 0 retired; 0 deferred.

Attribution: the pinned files supply the potential-difference proof pattern,
the finite higher-potential cardinal rank, well-founded-induction route to weak
acyclicity, and the team/zero-sum degeneracy argument.  The successor recovers
the mathematics over the greenfield semantic APIs, omitting only obsolete
`KernelGame` transport and wrapper vocabulary.

Validation:

```text
lake build GameTheory.Core.Potential
git diff --check
```

The focused build completed in 1,721 jobs.  The integration owner should run
the project-level source/reachability and coverage audits after combining this
bounded ledger with the other Wave 2 batches.
