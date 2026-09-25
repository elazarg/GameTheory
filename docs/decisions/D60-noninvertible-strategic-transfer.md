# D60: mixtures and utility coverage for noninvertible strategic transfer

- **Status:** adopted with narrowed, opt-in utility certificates
- **Date:** 2026-09-21
- **Experiments:** EXP-120; general PMF boundary EXP-131 / D62

## Question and competing designs

Can a compiler add strategic choices while preserving incentives at compiled
profiles? D8's profile-equivalence theorem does not cover a target deviation
whose observed law is a genuine mixture of source deviations, or a target
deviation bounded only in the supplied utilities.

The competition compares direct theorem hypotheses and bespoke composition
with two narrow records over the canonical `GameForm`. A universal morphism or
adequacy hierarchy remains outside the candidate set for admission.

The transfer theorems remain available without records. In particular,
`GameForm.isεNash_of_deviation_bounds` needs only honest utility equality at the
two supplied profiles and unilateral coverage at that source profile. MAID
pruning now uses its exact-Nash specialization and exposes the same-epsilon
approximate consequence. Uniform coverage is not imposed on that consumer.
These direct theorems live in `Core.UtilityTransfer`, included by `Core`.
`Core.UtilitySimulation` and `Core.MixtureUtilitySimulation` are stable explicit
imports for reused uniform bounds and composition. The cold utility cost below
refuted their initial admission into the default root.

## Candidate API and boundaries

- `GameForm.MixtureSimulationOn` records a coordinatewise strategy map, honest
  common-observation laws, coverage of compiled strategies by the selected
  target deviations, and PMF-mixture representation of those deviations.
  The direct reflection theorem needs only honest laws. Direct preservation
  needs only the supplied profile's honest law and deviation mixtures.
- `GameForm.UtilitySimulation` records honest utility equality and one source
  replacement bounding all members of each covered coalition simultaneously.
  Utilities are fixed parameters. The record is not a claim about other utility
  interpretations, arbitrary preferences, or nonmembers' welfare.
- `IsεGroupNash` is `IsEquilibrium` for a selected subfamily of the existing
  constant-coalition scheme and the coalition lift of `euPreferenceWithin`.
  Empty coalitions are excluded by the deviator subtype. No second equilibrium
  engine is introduced.
- `Profile.map`, its update and override laws, and `DeviationScheme.comap`
  own their lower-layer operations. Utility transfer does not import mixture
  transfer or stopping theory. The implication from mixture laws to unilateral
  utility coverage lives in `Core.MixtureUtilitySimulation`.
- Restricted composition requires a middle mixture supported on deviations
  covered by the left edge. This is checked only at compiled source profiles.
  Total left coverage supplies the convenient unrestricted composition.

Expected-utility equality alone is still a theorem derived from exact laws,
not an `EUMorphism` structure. The utility record's additional content is
deviation coverage, which can hold when law equality fails. Neither record
asserts CE/CCE transfer: profile-dependent witnesses need not be local to a
player's correlated recommendation. Dominant source strategies give best
responses against compiled opponents, without claiming off-image dominance.

## Representative evidence

`Tests.MixtureSimulation` has a target action with a fair Boolean law and only
deterministic source actions. Neither source action has that target law. It
also constructs a composition through a genuinely restricted left edge and
proves that two individually valid edges can have no total composite when
support coverage is absent.

`Core.MixedSimulation` is an independent native consumer: the canonical mixed
extension uses the deviator's mixed strategy itself as the source mixture.
Its pure-embedding theorem preserves and reflects the same real epsilon,
without finite strategy-carrier assumptions.

`Tests.UtilitySimulation` transfers a nonzero epsilon through two layers and
transfers best responses while a mixed target deviation is strictly worse.
`Tests.CoalitionSimulation` supplies both a positive joint-replacement witness
and the communication counterexample: source strong Nash and exact unilateral
coverage do not imply target strong Nash. It also checks that an empty selected
coalition cannot make equilibrium impossible.

`Languages.MAID.ObservationPruning` supplies the separate profile-local consumer
of the direct utility theorem. Its existing safe and value-of-information
failure controls continue through the shared Core theorem.

D62 uses ordinary PMFs for these laws. EXP-131 shows that preservation through
an arbitrary mixture requires integration of each actual target deviation;
integration of all source deviations separately does not imply it. Honest
expected-utility transport also preserves definedness.

General event and fiber inequalities live in `Math.Probability.Bounds`;
`Math.Probability.SelectiveStopping` proves the informed binary-decision
consequences. The infinite-site shared-coin counterexample refutes the source
comment claiming that infinitely many prescribed marginals always preclude a
finite-support coupling. Unconditional quit/continue equality is separately
shown insufficient for informed stopping.

## Measurements and kill conditions

The committed comparison sources are
`Experimental/PostArchitecture/MixtureSimulationComparison.lean` and
`Tests/UtilityTransferComparison.lean`. They retain both alternatives and their
identical conclusions.

The reserved kill conditions were to reject or narrow a single-consumer
abstraction, declaration and
construction above twice the direct baseline, more than 25 percent elaboration
overhead, duplicate equilibrium semantics, lost coalition quantifiers or
support restrictions, a forbidden dependency, or public equality transport.
Record shared infrastructure costs separately from each client construction;
a single short call cannot by itself amortize a new composition API.

| Comparison | Direct | Bundled | Observation |
|---|---:|---:|---|
| Native mixed transfer, nonblank declaration/construction/client lines | 18 | 16 record + 12 client = 28 | 1.56 times the baseline; common native laws excluded equally |
| Native mixed transfer, median whole-process seconds, three alternating runs | 8.7866 | 8.7883 | Bundled run also elaborates a fresh record declaration; both include imports and common laws |
| Reused utility composition, nonblank client lines | 30 | 19 | Two consumers: equilibrium equivalence and unilateral bound |
| Utility record, profile helper, composition, and both clients | 30 | 19 + 4 + 16 + 19 = 58 | 1.93 times the baseline; this is the selected construction slice, not the size of the entire API |
| Utility clients, median command elaboration milliseconds, five runs | 29.572 | 20.284 | Includes the composed-certificate construction in the bundled client |
| Utility infrastructure, median command elaboration milliseconds, three runs | — | 71.802 | Record, profile helper, and composition; paid once when compiling their library module |

Two failures narrow the outcome. Charging the utility infrastructure to just
one equilibrium consumer gives 50 lines against 18, above the two-times
budget. Charging its measured elaboration to the two-client comparison gives
about 92.086 ms against 29.572 ms, above the 25-percent budget. These are not
evidence for making a record the default way to perform one transfer. The
successful client-only measurement does not erase the initial cost, and the
import-inclusive mixture timings do not establish faster proof elaboration.

Consequently, direct utility theorems have their own leaf and remain in the
default root; the uniform record and its bridge require explicit imports.
`Tests.UtilityTransferBoundary` checks both direct-theorem availability and
certificate absence from `Core`. This is a narrowed admission for callers
reusing uniform bounds, whose composition and two distinct consumers are
checked. No existing isolated transfer is made to construct the record.

Timing commands use `lake env lean` with the package options
`-DwarningAsError=true -DrelaxedAutoImplicit=false -Dlinter.checkUnivs=false
-DmaxSynthPendingDepth=3`. For utility command timings, add
`-DElab.async=false -Dtrace.profiler=true -Dtrace.Elab.command=true
-Dtrace.profiler.threshold=1000000`, run the comparison or infrastructure
module, and sum the relevant top-level command blocks. All runs were serialized.
The local raw logs are `.lake/utility-comparison-profile-{1..5}.log`,
`.lake/utility-infrastructure-profile-{1..3}.log`, and
`.lake/reviews/EXP120MixtureTimings.json`; EXP-120 preserves their results.

## Consequence for D8

Admit finite-mixture simulation and its checked support-compatible composition.
Admit uniform utility certificates as explicit library leaves for reused
bounds, with the direct theorem layer owning isolated transfers. The latter
scope is narrower than the initial default-root proposal because its cold
construction costs failed the budget. Concrete relabelings and direct bridges
remain the defaults. No category instance, universal certificate level, new
runner, new probability representation, or compatibility surface follows.
