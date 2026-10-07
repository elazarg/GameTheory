# Optional complexity integration

The `GameTheoryComplexity` companion package lives in `extensions/complexity`.
It owns `GameTheoryComplexity` import modules, declares its API under
`GameTheory.Complexity`, and depends on GameTheory and selected
ComplexityLib modules. The main package has no dependency on this companion or
ComplexityLib. See the companion README for local and consumer commands.

## Delivered interfaces

- `GameTheoryComplexity.RandomTape`: the PMF of a verdict on uniformly drawn
  finite fair random tapes, its counting formula, and impossibility of exact
  acceptance probability `1/3` for any fixed tape length.
- `GameTheoryComplexity.Backend.Complexitylib`: equality of that PMF acceptance probability
  with ComplexityLib's machine counting semantics; one fixed machine with a
  named all-path polynomial clock; canonical Boolean sample serialization with
  unary security parameter; polynomial encoded-input and execution bounds; and
  specialization through the existing `SampleTest` interface.
- `GameTheoryComplexity.Backend.Serializer`: a deterministic polynomial-time
  machine witness for the canonical Boolean serializer, including tuple
  decoding, exact output correctness, and a runtime bound in the unary security
  parameter. `exists_uniform_booleanSerializer` supplies one machine for all
  sample degrees, parameters and sample tuples; each fixed sample degree has
  a polynomial runtime bound valid at every parameter, including zero.
- `GameTheoryComplexity.RandomTapeComposition` and `Backend.ClockPadding`:
  exact invariance of full verdict laws under unused fair bits and clock
  extension after all paths halt.
- `GameTheoryComplexity.Backend.Composition`: one probabilistic polynomial-time
  machine for deterministic FP preprocessing followed by a clocked randomized
  test, preserving its full acceptance law on every input.
- `GameTheoryComplexity.Backend.CompiledSampleTest`: one fixed machine implementing
  each canonical Boolean test, with a polynomial security clock uniform over
  all sample tuples, exact law agreement, and immediate rejection covered.
- `GameTheoryComplexity.Backend.Negligible`: equivalence of ComplexityLib's explicit
  inverse-power threshold predicate with the canonical Mathlib-based predicate.
- `GameTheoryComplexity.SampleTest`: a small client facade exposing the Boolean
  test class, its polynomial sample-count property, and indistinguishability
  implications using only canonical GameTheory types in declaration signatures.
- `GameTheory.Math.Probability.UniformProjection`: bijective transport, independent
  product factorization, and uniform prefix/suffix projections over any finite
  nonempty alphabet. The random-tape composition proofs reuse these base results.
- `GameTheory.Math.Probability.HybridIndistinguishability`: a finite telescoping
  bound and indistinguishable endpoints whenever the sum of adjacent advantages
  is negligible, without a polynomial stage-count assumption. Polynomially many
  uniformly negligible changes are a corollary.
- `GameTheory.Core.PseudoNashHybrid`: construction of the existing
  `SecureImplementation` certificate from honest and deviation utility hybrids.

The adjacent hybrid modules belong to the base library and import no machine
dependency. The machine and predicate bridges belong exclusively to the
companion package.

## Payoff-constrained Nash hardness

`GameTheory.Core.ConstrainedNash` defines `HasNashWithPayoffAtLeast` as canonical
mixed Nash, integrable utilities, and the requested expected-payoff thresholds.
`Core.BimatrixGame` supplies the general-sum two-player interpretation of the
existing matrix game form. Neither needs ComplexityLib.

`satisfiable_iff_exists_nash_threshold` in `Core.SatisfiabilityGameReduction` proves
that a Boolean clause incidence table with a nonzero number of variables is
satisfiable exactly when its symmetric two-player game has a mixed Nash
equilibrium giving each player payoff at least one. Actions are signed literals,
variable checks, clause checks and a fallback. A satisfying assignment gives
uniform literal play. Conversely, total payoff is at most two; meeting both
thresholds forces compatible literal support. Variable and clause deviations
then recover a consistent satisfying assignment. The contradictory fixture
still has the zero-payoff fallback equilibrium, so the theorem concerns the
payoff constraint rather than ordinary equilibrium existence.
The construction follows the literal/clause gadget of Conitzer and Sandholm's
[Complexity Results about Nash Equilibria](https://arxiv.org/abs/cs/0205074).
`satisfiable_iff_hasNash_threshold` presents the same characterization through
the generic utility-game predicate, without exposing matrix-profile bookkeeping.

The companion's `Backend.SATReduction` connects encoded SAT to
`GameTheory.Finite.BimatrixTable.unitPayoffLanguage`. This language decodes an
actual integer payoff table and asks for canonical mixed Nash with both payoffs
at least one. It does not decode a formula and generate a hidden game. The row
payoff matrix is explicit; the column matrix is its transpose.

For a source word of length `L`, the reduction pads both variable and clause
counts to `L + 1` and uses `q = 4L + 5` actions. The output has a unary dimension
header and `q²` row-major entries. Each entry consists of positive and negative
tallies, each padded to `q + 2` bits. Its exact length is
`q + 1 + 2q²(q + 2)`. Empty formulas are accepted, padded clauses are tautological,
and malformed SAT encodings produce unsatisfiable gadgets.

`SATTableMachine` implements the literal-incidence scanner with fixed-arity
unary registers and bounded recursion. `SATSyntaxMachine` reuses the upstream
syntax validator. `SATTablePayoff` computes the payoff cases and writes every
cell through the bounded row-major emitter in `SATTableEmission`. Its Cobham
certificate supplies an actual fixed deterministic polynomial-time machine;
the cubic output bound is a separate fact. `SATTablePayoffCorrectness` identifies
its complete output with the semantic serializer, and `SATReductionSemantic`
proves membership equivalence using exact decoding and bijective action renaming.
`sat_reduces_unitPayoffLanguage` transfers the certified SAT reduction;
`unitPayoffLanguage_NPHard` applies upstream Cook–Levin NP-hardness.

Import this backend leaf explicitly for hardness. The random-sample facade and
umbrella keep their smaller dependency closure. Changing the machine library
requires replacing the machine certificate and complexity-class transfer; the
base game, decoder and satisfiability characterization remain canonical.

This slice establishes NP-hardness. NP membership requires bounded rational
equilibrium witnesses and a certified verifier. PPAD requires End-of-Line search
semantics and solution-preserving reductions; exact Nash search, approximate Nash
search and FIXP have different output conventions. They remain separate delivery
seams.

Normal clients import the facade and continue using canonical `SampleTest`,
`IndistinguishableBy`, and `SecureImplementation`. Clients constructing concrete
machines import the backend explicitly. Swapping the machine library requires
changing backend implementations and proofs rather than these facade signatures;
no equivalence between arbitrary machine models is assumed. This is a module
boundary, not a universal computation interface or a backend registry.

## Exact limits

Machine bounds use encoded input length. The Boolean interface fixes sample
count to a power of `κ + 1`, serializes `κ` in unary, and proves an explicit
execution bound in `κ`. An arbitrary encoder with short outputs could hide an
oracle; no such encoder is admitted as efficient preprocessing. The serializer
certificate starts from a standard encoded pair containing the unary parameter
and the sample bitstring. Its deterministic machine computes
exactly the input consumed by `booleanMachineTest`, with polynomial cost
including pair decoding. General efficient postprocessing and general reference
mean tests remain separate obligations. The composition certificate now supplies
one probabilistic polynomial-time machine for serialization and testing together.
Its global clock is polynomial in raw input length; its clock on canonical tuples
is polynomial in the unary security parameter and independent of the samples.
Unused prefix bits and padding after halting preserve the full verdict law.
The initial encoded tuple remains the explicit machine input convention; this
certificate does not construct a sampler or encode a binary security parameter.

Finite fair random tapes give dyadic probabilities. Arbitrary rational laws
require approximation or another sampling model. Arbitrary real utilities need
efficient encodings and samplers before computational-security interpretation.
Restricting distinguishers does not restrict game strategies or deviations.
The canonical ideal-to-real theorem still requires `ContainsMeanTests` and a
simulation certificate; neither is supplied automatically by this package.

For hybrids, a separate negligible bound for every fixed index is insufficient.
`HybridIndistinguishabilityTest.movingJump` moves a perfectly visible jump to
index `κ`: every fixed adjacent pair is eventually identical, while the
polynomial-length chain has distinguishable endpoints. The accepted certificate
can bound the summed adjacent error directly, or use one eventual bound for
every active index when the number of stages is polynomial. An exponentially
long chain with only one nonzero change exercises the more general theorem.

## Source selection

The original public upstream ComplexityLib baseline is
`257ad90ec5f547894cc20f27bd828839b1bf7bbf`. Expanding its imports to Cook–Levin
exposed one Lean 4.34.1 proof failure. The package now pins the public fork
`elazarg/complexitylib@c5f2acf1a35d5b00db04cd1bd337a8ce57d66a40`, containing only
the two-line function-extensionality proof repair, and explicitly selects
Mathlib `v4.34.1`; EXP-159 records the refuted unchanged-closure hypothesis and
the repaired closure's validation. VI-NP-verification supplied useful compatibility evidence,
but its dependency branch is private and is not a portable dependency source.
Only the imported upstream closure is certified by this package's checks.

The `openai/math` randomized mean-payoff solution is a reference for finite
random-tape counting and machine compilation. Its machine model is different
and its result is quasipolynomial. Matroid prophet inequalities are potential
allocation theorem recovery, without an asserted efficient implementation.
Neither is imported or copied here. Comparator challenge statements must be
distinguished from their actual solution modules before any future recovery.

## Validation

Integration measurements are recorded in EXP-158 and EXP-159 in `ExperimentLog.md` and the
optional-package decision record. The companion CI builds only its own root and
lint target, checks dependency isolation, and audits the transitive axioms of
every extension-owned declaration, including private and generated declarations.
The base CI remains independent of the companion dependency resolution.

The combined serialization and composition slice builds the companion library,
fixtures, lint driver and axiom audit with 3,111 jobs on Lean/Mathlib 4.34.1. All
134 extension declarations pass the transitive axiom audit. The fair-coin consumer
has exact acceptance probability `1/2` even with a nonmonotone source clock, and a
zero-step source test exercises immediate rejection. Selected FP and machine
composition dependencies compile unchanged, without importing the full Cobham
characterization.

## Proof-mining and implementation review

The review moved general finite-uniform projection mathematics into the base
library and generalized hybrid composition to negligible total error. Neither
result depends on a machine backend. Clock proofs now share monotone halting
preservation and upstream clock monotonicity; serializer composition proofs use
ordinary function composition, and an exact encoded-length formula replaces
repeated encoding arithmetic. Existing client theorem statements are preserved.

The software review found that import modifiers and quoted module identifiers
could bypass the dependency scanner. The corrected scanner handles both and
requires every public companion module to appear in the lint driver. The axiom
audit follows declaration origin rather than namespace spelling. Nineteen
mutation regressions pass. The small facade avoids importing serializer and
composition proofs; the umbrella explicitly includes the full delivered surface.

The input-sensitive consumer uses one compiled machine for both Boolean payloads
and proves that its complete verdict law is the corresponding point mass. This
checks serialization observably, alongside the existing fair-coin and halted-start
controls. The base library and lint driver build in 4,342 jobs; the exponential
hybrid fixture, both linters, and the expected-value architecture audit pass.
The companion CI also resolves the published base pin without a local path
override and builds the facade and composed implementation against that pin.

The earlier random-sample released-mode check was blocked by GitHub HTTPS
timeouts. The SAT slice now passes a local released consumer check: Lake resolves
`GameTheory` as a git dependency at published commit
`3132599983a6baf0d67fa2e41e0da1c8e7521405`, without the local-path override, and
builds the facade, composed implementation and SAT hardness endpoint in 3,229
jobs. A command-scoped Git URL rewrite supplies the published objects from the
local repository; this checks git-mode package resolution and compilation,
while direct HTTPS retrieval is left to hosted CI. Lean 4.34.1 is confirmed and
`lake exe cache get` succeeds with 8,908 already-decompressed files.

The full SAT integration passes 4,355 base jobs and 3,241 companion jobs,
including fixtures, lint drivers and axiom audit. Both linters pass. All 462
extension-owned declarations have only standard transitive axioms, including
their Cook–Levin dependencies. The architecture audit, dependency isolation and
19 optional-boundary mutation regressions pass. Fixtures distinguish satisfiable
and contradictory formulas, empty formulas and empty clauses, malformed source
words, literal conflicts and the zero-payoff fallback equilibrium.

Proof mining moved generic payoff-constrained Nash and action-renaming results
into the base package and replaced duplicated backend expectation transport with
the base characterization. Numeric action evaluation has a proved equivalence
to canonical payoffs. Reviews checked that syntax validation suppresses malformed
scanner output, that table agreement uses only emitted indices, and that the
scanner's packed-state width bound is distinct from its polynomial runtime
certificate. No broader machine interface or second equilibrium semantics is
introduced.

## NP-completeness and bounded rational witnesses

`Backend.NashNPComplete.unitPayoffLanguage_NPComplete` combines the existing
whole-table SAT reduction with NP membership of the same explicit symmetric
integer-table language. The condition is a mixed Nash equilibrium with both
expected payoffs at least one. The target remains the canonical PMF game
predicate, including the total decoder's interpretation of malformed inputs.

The base package owns integer numerator certificates and their correctness.
Each player supplies natural weights with a positive common denominator. The
weights sum to that denominator; every pure action has payoff at most the
claimed utility numerator, and positively weighted actions attain it. The two
utility numerators meet the payoff-one thresholds. Generic PMF normalization
and exact weighted expectations live in `Math.Probability.Numerator`.

Completeness fixes the original equilibrium supports and solves two integer
linear systems with nonnegative variables. Each system has `2q + 2` variables
and `3q + 2` equations: normalization, best-response slacks, support tightness,
forbidden weights and the payoff threshold. Generic support elimination selects
independent columns; the Gram matrix and Cramer determinants supply bounded
integer numerators and a positive denominator. This replaces an unbounded real
equilibrium witness by an exact rational certificate without changing Nash
semantics.

For input length `L`, every certificate field fits
`W(L) = 14L² + 36L + 23` bits. The certificate has exactly `(2q + 4)W(L)` bits,
so every accepted witness has cubic length. The shared little-endian parser and
encoder have an exact roundtrip theorem. The verifier scans each payoff's
positive and negative tally bits and adds the corresponding binary weight;
carry addition and unsigned comparison have actual machine certificates. Its
loops depend on field widths and table dimensions, with no loop over a binary
field's numeric value. `binaryCertificateVerifier_eq_true_iff` proves exact
agreement with the base certificate constraints.

`Backend.NashNP` also validates canonical pair encodings and certifies one
deterministic polynomial-time machine for the full paired verifier. Its
polynomially balanced FNP witness relation characterizes the canonical target,
and the upstream guess-and-verify construction gives NP membership. The
membership leaf does not import the SAT reduction; only the NP-completeness
leaf combines them. Ordinary game and certificate clients need no ComplexityLib.

PPAD is the next search interface, not a consequence of this decision theorem.
The selected upstream version provides FNP and TFNP but no End-of-Line or PPAD
API. The next dependency gate is encoded End-of-Line totality with polynomial
verification, followed by solution-preserving polynomial search reductions.

The expanded base library and lint driver pass 4,364 jobs; the companion library,
fixtures, lint driver and axiom audit pass 3,294 jobs. All 759 extension-owned
declarations have only standard transitive axioms. Both linters, architecture
checks, optional dependency isolation and all 19 boundary mutation regressions
pass. Tests exercise binary carry and padding, exact roundtrips, actual decoded
game acceptance, incorrect support payoffs, certificate length rejection, empty
dimensions and malformed paired inputs. No unsafe evaluator or placeholder is
used to certify the new fixture results.

The released-mode consumer resolves `GameTheory` as a public git dependency at
`15b05259fabcc79f5b8b33630fd223a9a799e0f3`, with no local-path override, and builds
the facade, composed sample test and NP-completeness endpoint in 3,281 jobs.
The same command-scoped local Git object mirror supplies the published objects;
the manifest retains the public URL and exact revision. Lean 4.34.1 and the
successful Mathlib cache hook are confirmed. Hosted CI checks direct HTTPS
resolution and now includes the NP-completeness endpoint in its release smoke.
