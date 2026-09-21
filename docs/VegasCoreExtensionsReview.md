# VegasCore extension admission review

The implementation is tracked by EXP-120 and
[D60](decisions/D60-noninvertible-strategic-transfer.md). The original admission
review below is retained as the proposal assessed by that experiment.

Reviewed 2026-09-21 against GameTheory `3dd93bf05286e5c6996fdf3e991d96a386156d4d`
and VegasCore `9d601771fcee6e170a53009016bc195b81b3eb2a`. VegasCore's nested
GameTheory checkout has the same commit as this workspace.

All five modules contain useful library material. Their imports already depend
only on GameTheory, Mathlib transitively, and each other. Independence from
VegasCore is therefore established at the source dependency level. Admission
requires API integration, rather than extracting runtime-specific definitions.
This is a review, not a port or a change to delivery status.

| Proposal | Recommendation | Intended owner |
|---|---|---|
| `Math/Probability/FinDist.lean` | Port all nine lemmas, largely as written; fix one false documentation claim and a few API details. | Existing `GameTheory.Math.Probability.FinDist` |
| `Math/SelectiveStopping.lean` | Port, splitting general probability lemmas from the binary decision family and generalizing the fiber helper. | `FinDist`, `Bounds`, and a focused `Math.Probability.SelectiveStopping` leaf |
| `Core/MixtureSimulation.lean` | Admit the transfer results; evaluate the small record under D8 before freezing it. | Focused Core transfer leaf |
| `Core/MixtureSimulationComposition.lean` | Port with the mixture API; retain the support-compatibility condition. | Same transfer family |
| `Core/UtilitySimulation.lean` | Port after replacing the duplicate equilibrium definition and extracting profile-local transfer theorems. | Canonical Core deviation/approximation API and a focused transfer leaf |

**Corrections that should precede a verbatim port**

1. The [finite-coupling comment](../../VegasCore/GameTheoryExtensions/Math/Probability/FinDist.lean)
   at lines 170–176 is false as written. Infinitely many prescribed marginals
   can have a finite-support coupling: draw one Boolean coin and assign its
   result to every natural-number-indexed site. Every marginal is the coin,
   while the assignment law has at most two support points. A Lean proof of
   the marginal identity passed in the review harness. Say instead that the
   finite-site construction guarantees finite support for arbitrary supplied
   site laws; infinite families require additional conditions. The theorem
   `runDependent_bind_apply` itself is correct.
2. [UtilitySimulation](../../VegasCore/GameTheoryExtensions/Core/UtilitySimulation.lean)
   defines `IsεGroupNash` directly at lines 50–58. Its singleton and all-coalition
   equivalences are correct, but a second logical equilibrium definition
   conflicts with D5. Recast it as a transparent specialization of
   `IsEquilibrium`, using constant coalition deviations and the coalition lift
   of `euPreferenceWithin`. Restrict to allowed nonempty coalitions. Currently,
   putting the empty coalition in `groups` makes the equilibrium predicate
   impossible, even though the simulation's bound for that coalition is vacuous.
3. The bundled strategic certificates require a D8 admission decision.
   [D8](decisions/D8-minimal-transformations.md) currently admits concrete
   transformations and theorem hypotheses, and requires independent consumers
   and a theorem unavailable from the existing operations before adding a
   structure. These proposals have substantive evidence for reopening that
   question; they should not be rejected merely because they use records.
   They also should not silently establish a general certificate hierarchy.

**1. Finite-distribution extensions**

Source: [Math/Probability/FinDist.lean](../../VegasCore/GameTheoryExtensions/Math/Probability/FinDist.lean).
These fill gaps around existing operations; they introduce no new probability
representation or game assumptions.

| Declaration | Disposition |
|---|---|
| `bindOnSupport_congr_measure` | Port the equality-transport convenience. Rename the suffix to refer to a law or equality: its input is a `FinDist`, not a measure. Keep the proof-witness transport inside this probability API. |
| `bindOnSupport_map` | Port essentially unchanged. Its noninjective pushforward case is valuable, and the total continuation used internally adds no public off-support assumption. |
| `bindOnSupport_bindOnSupport` | Port unchanged. It already delegates to Mathlib's `PMF.bindOnSupport_bindOnSupport`; this is the missing finite-support wrapper. |
| `bind_bindOnSupport_assoc` | Port as the total-first-branch specialization of the preceding law. Distinguish it from the existing `bind_bindOnSupport`, whose final continuation is total. |
| `probOf_congr` | Port unchanged beside `probOf` and its indicator laws. Support-local event equality is the right premise. |
| `ext_of_prob_on_support` | Port. Normalization makes agreement on just one law's support sufficient; the proof correctly rules out extra mass in the other law. |
| `prob_bind_of_unique_branch` | Port unchanged beside `prob_bind`. The selected branch need not have positive mass, and uniqueness is required only on realized branches. |
| `probOf_eq_expect_of_weighting` | Port the identity. Prefer the existing set/indicator conventions so a proof-only caller need not supply `DecidablePred`. Retain control of reference mass outside the event; weakening the hypothesis to the first law's support alone would be unsound. |
| `runDependent_bind_apply` | Port beside `runDependent_factor_of_mem`, with the corrected infinite-family comment. It is a useful continuation-facing form of the marginal law. |

Concrete consumers include
[message-policy composition](../../VegasCore/Interaction/MessageApplicationPolicyLaws.lean)
for dependent binds and
[purification](../../VegasCore/Vegas/Source/Purification.lean)
for the one-site marginal. The latter uses the marginal twice without needing
to expose the other sampled sites.

Mathlib's PMF associativity should remain the implementation source. Its
integral-average existence results are also available, but importing the
measure/integral layer into this finite-law core would be unnecessary. No
matching public GameTheory declarations were found for these nine statements.

**2. Selective stopping**

Source: [Math/SelectiveStopping.lean](../../VegasCore/GameTheoryExtensions/Math/SelectiveStopping.lean).
The mathematical content belongs in GameTheory's reusable probability layer.
It concerns one informed binary decision with random continuations; it is not
a stopping-time or optional-stopping theorem.

| Declaration family | Disposition |
|---|---|
| `exists_expect_le_support` | Move to `FinDist` beside the expectation/support inequalities. This is general finite-law mathematics, and utility transfer should not import stopping theory to obtain it. |
| `expect_le_add_event_gap` | Move to the existing `Bounds` module. State the primary version with `event : Set State` and `probOf`, consistent with that module. Keep a Boolean specialization only where useful. Preserve signed gaps: the proof does not require nonnegativity. |
| `selective_stopping_bound`, `_le`, `_lt` | Port essentially unchanged in a focused probability leaf. The support-local premise, including that stopping must be possible at the state, is appropriately weak. Keep strict positivity assumptions on the strict corollary only. |
| `stopping_information_fiber_bound` | Extract a general finite partition/fiber expectation identity or inequality, then derive this event-specific bound. The proof currently repeats almost the same fiber summation for source and target. Use existing finite-sum fiber machinery or one shared helper. Retain unnormalized expectations and zero-mass fibers. |
| `selective_stopping_optimal` | Port with its fully informed scope explicit. The chosen policy reads the entire state; admissibility under a coarser information model does not follow. No general finite-action optimization framework is needed for this port. |
| `selective_stopping_le_iff` | Port unchanged. Necessity quantifies over every state law and every stopping policy, which permits the point-mass test. Do not describe it as necessity at an arbitrary fixed law. |

The fiber theorem is valid, but its hypothesis compares values on
`stopped ∩ information-fiber`. It does not establish that the stopping decision
depends only on the stated information. To derive its premise from a comparison
on whole information fibers, an information-locality/factorization argument
is needed. Keep that distinction in the documentation.

The [existing tests](../../VegasCore/GameTheoryExtensionsTests/SelectiveStopping.lean)
cover a zero-mass information value, an informative fiber comparison despite
failed pointwise dominance, and a sharp event-gap bound.
[Disclosure](../../VegasCore/Vegas/Source/Disclosure.lean) is an actual consumer
of the binary stopping bound. Admission should additionally retain a small
control where unconditional quit/continue expectations agree but selecting
when to quit improves utility; this prevents accidentally weakening the
decision-point premise.

**3. Finite-mixture strategic transfer**

Source: [Core/MixtureSimulation.lean](../../VegasCore/GameTheoryExtensions/Core/MixtureSimulation.lean).
This is a real extension beyond the existing profile-equivalence theorem:
a target strategy can realize a lottery over source deviations even when no
single source deviation has that outcome law. The supplied three-strategy
[test](../../VegasCore/GameTheoryExtensionsTests/MixtureSimulation.lean)
proves exactly that separation.

Retain the common observation, the coordinatewise strategy translation, exact
honest laws, and finite mixtures of legal unilateral source deviations. The
results support arbitrary utilities on that common observation and preserve
the same epsilon. `guarantee` also has an independent use: it transfers a lower
bound on an observable, even when that observable is not the deviator's utility.

Recommended integration:

- Factor coordinatewise profile mapping and its update/override laws into
  `Core.Signature`; both simulation files currently reprove the update law.
  This operation needs neither a play law nor utilities.
- Keep `expect_compile`, `guarantee`, reobservation, restricted-deviation
  transfer, and total-deviation Nash transfer. Use a canonical restricted
  deviation scheme for any named restricted-equilibrium predicate.
- Separate obligations by direction. Honest-law preservation already reflects
  unrestricted target Nash to source Nash. `compiled_considered` is needed for
  reflection from the restricted target comparison; the mixture field is
  needed for preservation to target deviations. The existing record bundles
  all three, so theorem-level APIs should expose the weaker premises too.
- Evaluate a narrow reusable record against those direct theorems under D8.
  Source purification, scheduling/service edges, and their compositions are
  meaningful external evidence. A native mixed-extension or MAID consumer
  would make the library-side reuse concrete without importing VegasCore.

The certificate covers unilateral deviations at compiled profiles. It does
not imply arbitrary preference, coalition, CE/CCE, or off-image dominance
transfer. In particular, the mixture witness can depend on the opponents'
whole fixed profile; that is not automatically an information-local deviation
for a correlated recommendation law.

**4. Composition of mixture transfers**

Source: [Core/MixtureSimulationComposition.lean](../../VegasCore/GameTheoryExtensions/Core/MixtureSimulationComposition.lean).
Port this with the accepted mixture API. Flattening the two finite mixtures
with `bind` is the correct construction, and arbitrary fallback choices are
confined to unsupported branches.

`transOn` correctly requires a right-hand representation whose middle
alternatives all satisfy the left-hand deviation predicate. Two restricted
certificates alone do not imply this condition. `trans` is the useful corollary
when all middle strategies are considered. Both should retain these meanings.

One useful weakening: `transOn.compatible` currently quantifies over every
middle profile, but the proof uses it only at `left.compileProfile profile`.
State the minimal theorem over source profiles, with that compiled middle
profile substituted. This admits certificates valid only on the reachable
compiler image without changing the proof idea.

The existing composition test exercises `trans` with a total left predicate.
Add a restricted positive example and a failed-support-coverage control for
`transOn`; its distinctive hypothesis is not exercised by that test.
The external
[pending compositions](../../VegasCore/Vegas/Game/PendingCompositions.lean)
and [service composition](../../VegasCore/Vegas/Game/EventMessageStrategic.lean)
show that composition is used beyond the small test fixture.

**5. Utility-bound strategic transfer**

Source: [Core/UtilitySimulation.lean](../../VegasCore/GameTheoryExtensions/Core/UtilitySimulation.lean).
Retain the mathematical transfer results, but integrate the semantics and
dependencies before promoting the file.

The essential preservation premise is that each target coalition deviation
has one source replacement bounding every member simultaneously. Preserve the
quantifier order `exists alternative, forall member`; choosing a different
source replacement for each member would not prove strong-Nash transfer.
The [communication counterexample](../../VegasCore/GameTheoryExtensionsTests/CoalitionSimulation.lean)
is especially valuable: a unilateral certificate exists, every source profile
is strong Nash, and its compilation is not strong Nash.

Recommended changes and retained results:

- Replace the direct `IsεGroupNash` definition as described above. Retain the
  singleton and nonempty-coalition characterizations through the canonical
  predicates.
- Make profile-local deviation bounds the primary transfer theorem. The
  existing `isεGroupNash_compileProfile_iff_of_utility_bounds` already has this
  useful shape. A uniform record can be a convenience only after the D8
  comparison; requiring uniform bounds in every use would exclude safe
  reductions certified at one profile.
- Use [MAID's `CoversFullDeviationsAt`](../GameTheory/Languages/MAID/ObservationPruning.lean)
  as the second semantic consumer. It expresses the same unilateral coverage
  idea at a fixed reduced policy. Its nested-pruning coverage theorem also
  composes the same inequalities. Extract the common theorem rather than
  installing parallel semantics beside it.
- Retain honest-utility-only reflection, same-epsilon preservation/reflection,
  best-response transfer, and the carefully scoped dominant-strategy corollary.
  The latter gives best responses against compiled opponents; it does not
  assert dominance against every target opponent profile.
- Retain `ofUnilateral`, `congrUtilities`, composition, and the unmatched-value
  obstruction results in the accepted API form. Generalizing utilities to an
  arbitrary ordered scalar is unnecessary for the current consumers.
- Move `MixtureSimulationOn.toUtilitySimulation` to a bridge importing both
  transfer families. The utility-bound theory itself need not import mixture
  simulation. Move `exists_expect_le_support` down to remove its unrelated
  stopping import.

The finite-mixture-to-utility bridge is correctly unilateral. For utilities
with component payoff vectors `(1, 0)` and `(0, 1)`, their fair mixture gives
`(1/2, 1/2)`, but neither component bounds both players. Keep the coalition
separation test with any refactoring.

**Suggested delivery order and validation**

1. Admit the finite-law lemmas and corrected documentation, then the general
   expectation/event bounds and the focused stopping family. These reuse
   established probability architecture.
2. Extract profile mapping laws and profile-local utility-transfer theorems
   over the canonical equilibrium definitions; connect the latter to MAID.
3. Compare the narrow mixture/utility records with direct theorem APIs in a
   logged D8 experiment, using the existing noninvertible and coalition
   witnesses and actual composed consumers. Include the restricted-composition
   control before freezing that API. Record proof size and elaboration cost;
   the current build check is not that architectural comparison.
4. Update the owning delivery rows when admitted code and its consumers land.
   This review does not change existing family statuses.

Validation performed:

- `lake build GameTheoryExtensions GameTheoryExtensionsTests` in VegasCore:
  passed, 1,738 jobs, with warnings treated as errors.
- Re-elaborated all five extension files and all four test files in an ignored
  combined-source harness against this workspace's GameTheory imports and
  Lean options. The bodies were unchanged; internal extension imports were
  replaced by their source bodies in dependency order. Command:
  `lake env lean '-DwarningAsError=true' '-DrelaxedAutoImplicit=false' '-Dlinter.checkUnivs=false' '-DmaxSynthPendingDepth=3' .lake/reviews/VegasCoreExtensionsReview.lean`.
  Passed without diagnostics, including the infinite-site finite-coupling
  counterexample. This complements, rather than replaces, the separate-module
  Lake build.
- Searched the extension sources for placeholders, custom axioms, direct
  `Function.update` calls, explicit casts, and runtime imports. No prohibited code was
  found. Searched current GameTheory and the pinned Mathlib sources for overlap.
- No Lean library source, dependency configuration, or delivery status changed.
