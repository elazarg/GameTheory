# Optional complexity integration

The `GameTheoryComplexity` companion package lives in `extensions/complexity`.
It owns `GameTheoryComplexity` import modules, declares its API under
`GameTheory.Complexity`, and depends on GameTheory and selected
ComplexityLib modules. The main package has no dependency on this companion or
ComplexityLib. See the companion README for local and consumer commands.

The native source port is complete. Full upstream-matching library/fixture
validation passes 7,838 jobs; final lint/axiom-driver rebuilding passes 7,840
jobs. Public lint, the transitive axiom driver, all 251 authored cached-diagnostic
checks and 44 audit regressions pass. These checks use isolated 4.36-RC source
copies; tracked Lean/Mathlib remain stable 4.35.

A separate stable 4.35 selected-closure probe passes
`lake --iofail build GameTheoryComplexity.BimatrixNash` in 3,694 jobs
(`stable-probe-native-nash-build.log`). This verifies the Nash facade's imported
closure and does not validate the full stable optional package or its audit.

The stable merge gate is blocked by unmodified upstream
`Complexity.Probability.PMF.Bind`, which uses unavailable `tsum_sigma`,
`tsum_le_tsum` and `tsum_add` APIs. Actual stable local update/version/cache
checks pass, including 9,031 already-decompressed cache files, but the full
local audit fails during its build; later audit stages did not complete.
Actual published-base resolution verifies the sole GameTheory git dependency
at `c7cd6bed7498b9a16edb22262e9522ceff90648c` and Lean 4.35.0. Its pivot client
passes 3,125 jobs; the targeted probability check fails in a 3,049-job target
with the same missing APIs. The full published optional audit remains unrun
and blocked; no published cache gate is claimed. Local transcripts are under
`.codex/scratch/cslib-port/`: `stable-local-update.log`,
`stable-local-cache.log`, `stable-local-full-audit.log`,
`stable-published-update.log`, `stable-published-pivot-client.log` and
`stable-published-probability-gate.log`.

Final Lean and Mathlib 4.36 release endpoints return 404 as of 2026-11-09.
Normal final-release maintenance must precede full local-path and published-base
audits and a fresh published pivot-client check. Neither tracked RC toolchains
nor dependency-source patches are used to bypass this gate.

## Delivered interfaces

- `GameTheoryComplexity.RandomTape`: the PMF of a verdict on uniformly drawn
  finite fair random tapes, its counting formula, and impossibility of exact
  acceptance probability `1/3` for any fixed tape length.
- `GameTheoryComplexity.Backend.Complexitylib`: native
  `Cslib.Probability.IsPPTOn encBits encBool` certificates for Boolean programs,
  canonical unary-parameter sample serialization, and specialization through the
  existing `SampleTest` interface. `exists_program_randomTapeLaw` gives one
  efficient deterministic saved-coin evaluator whose uniform finite-tape law is
  exactly the program's PMF law. Every certified Boolean program therefore
  satisfies the same exact-third impossibility as the canonical random tapes.
- `GameTheoryComplexity.Backend.Serializer`: the canonical Boolean serializer
  on a native framed pair of raw words. `serializeBoolean_polyTime` supplies its
  actual deterministic polynomial-time machine certificate, including pair
  decoding, normalization of the first word to unary, and writing the delimiter
  and payload. `booleanTuple_encode_length` gives
  `2*κ + 1 + (κ+1)^sampleDegree`; its parameter-polynomial bound includes zero.
- `GameTheoryComplexity.RandomTapeComposition`: exact invariance of full verdict
  laws when unused independent fair bits are discarded.
- `GameTheoryComplexity.Backend.CompiledSampleTest`: native preprocessing
  closure and the native intrinsic-halting compiler give one fixed finite machine
  implementing serialization and testing. Its parameter-polynomial clock is
  uniform over all sample tuples, with exact agreement of the complete encoded
  verdict law and halting on every supported execution. The same machine has a
  raw-word polynomial clock that halts on every word; the program-law guarantee
  applies to encoded pairs. Native halting-padding
  lemmas preserve that law when the security bound enlarges the clock.
- `GameTheoryComplexity.Backend.Negligible`: the native nonnegative predicate on
  `fun κ => ‖advantage κ‖₊` is equivalent to GameTheory's canonical signed
  real-valued superpolynomial-decay predicate.
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

## Native End-of-Line classification

`GameTheoryComplexity.PPAD` proves native
`SearchComplete @Cslib.Complexity.PPAD encBits` for both concrete endpoint search
and the asymmetric raw pointer relation. It defines no local PPAD class or
reduction record. Native membership includes the independent Boolean verifier
and witness bounds; hardness covers arbitrary encoded source types.

Uniform native circuit generation is connected to the concrete byte evaluator by
an actual polynomial-time serializer. The zero-width cube and malformed circuit
semantics are explicit. Native origin masking is realized by filtering inactive
pointers. Every target answer decodes to a native answer; invalid source promises
return the native zero witness. Exact word codecs stay separate from native
framed machine arguments. EXP-172 and D77 record the design evidence; the delivery
ledger records the completed source port and blocked final stable consumer gate.

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

`SATTableMachine` implements the literal-incidence scan with typed native
word loops. `SATSyntaxMachine` certifies a five-Boolean-state validator for the
public byte format. `SATTablePayoff` computes each payoff case and writes every
cell through the bounded row-major emitter in `SATTableEmission`. Native
`ComputableInPolyTime` certificates charge the complete materialized output;
the cubic output bound is a separate fact. `SATTablePayoffCorrectness` identifies
the complete output with the semantic serializer on every raw source word, and
`SATReductionSemantic` proves membership equivalence against canonical Nash
semantics using exact decoding and bijective action renaming.

Native SAT uses binary variable labels. `satWordOfCNF` first applies native CNF
compaction, whose certificate produces unary labels, then serializes the
concrete SAT word. This avoids expanding an arbitrary binary label into an
exponentially long unary word. Native `CNF.satisfiable_compact` proves exact
satisfiability preservation. `sat_reduces_unitPayoffLanguage` composes native
`PolyTimeReducible` certificates through the concrete SAT-word language, and
`unitPayoffLanguage_NPHard` transfers native Cook–Levin hardness. A decider for
the payoff language yields `P inputEncoding = NP inputEncoding` for every
native instance encoding.

The matching-toolchain focused SAT hardness build passes 6,654 jobs, and its
transitive audit accepts 887 authored declarations with standard axioms only.
The complete source port includes native NP membership and later search
classifications. Full matching-toolchain gates pass; the final stable consumer
merge gate is blocked as recorded above.

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
`IndistinguishableBy`, and `SecureImplementation`. Backend clients supply a
program `List Bool → Cslib.ProbComp Bool` and an explicit native
`IsPPTOn encBits encBool` certificate. The backend uses the native computation
APIs directly; the facade's declaration signatures retain canonical GameTheory
types. The module boundary introduces no universal computation interface or
backend registry.

## Exact limits

Machine bounds use encoded input length. The Boolean interface fixes sample
count to a power of `κ + 1`, serializes `κ` in unary, and proves an explicit
parameter-polynomial length bound. An arbitrary encoder with short outputs could
hide an oracle; it requires its own deterministic computation certificate.

The serializer starts from the native encoding
`encPair encBits encBits` of a raw-word pair. At a canonical input the first
word is `List.replicate κ true` and the second is the sample bitstring.
`serializeBoolean_polyTime` computes exactly the input consumed by
`booleanProgramTest`, charging pair decoding and the complete output.
The native pair has length `2*κ + 1 + (κ+1)^sampleDegree`, bounded by
`4*(κ+1)^(sampleDegree+1)` for every parameter and prescribed sample tuple.

Native `IsPPTOn` identifies a program law with a fixed finite machine stopped at
a strict polynomial budget; that initial certificate alone need not assert that
the control state has halted. `exists_composed_booleanMachine` uses native
preprocessing closure and the intrinsic-halting compiler to supply one actual
halting machine for serialization and testing. The same machine halts on every
raw word within one polynomial in that word's length, including words outside
the pair encoding's image. Its exact program-law guarantee applies to encoded
pairs. Its security bound is polynomial in the
unary security parameter and independent of the sample values. Enlarging the
clock after halting preserves the complete configuration and verdict laws.
Saved-coin replay also permits arbitrary extra independent tape padding.

The explicit machine input remains the encoded pair. This certificate constructs
neither a sampler for arbitrary input laws nor a binary security-parameter
encoding. Reference utility mean tests and arbitrary efficient encodings require
their own implementation certificates.

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

`Backend.NashNP` certifies `nashCertificateVerdict`, a native typed Boolean
verifier of the complete table input and candidate certificate. The native
framed-pair encoding charges both arguments. Its polynomially balanced
`FNP encBits` relation characterizes the canonical target, and native domains
of FNP relations give `NP encBits` membership. The
membership leaf does not import the SAT reduction; only the NP-completeness
leaf combines them. Ordinary game and certificate clients need no ComplexityLib.

PPAD search completeness uses a separate search relation and reduction family.
The current decision proof combines native `NP encBits` membership and native
Cook–Levin hardness under `NPComplete encBits`; it defines no local complexity
class or paired-language compatibility interface.

The matching-toolchain NP/Cramer checkpoint passes 6,768 jobs, and its public
Nash and program controls pass 6,802 jobs. The expanded transitive audit accepts
2,402 authored declarations with standard axioms. Controls cover binary carry,
padding, exact codecs, actual decoded-game acceptance, incorrect support payoffs,
extra/missing certificate bits and empty dimensions. Full matching-toolchain
companion gates now pass; the final stable consumer merge gate is blocked as
recorded above.

## Succinct End-of-Line and search reductions

`GameTheory.Math.EndOfLine` defines a directed edge only when the successor and
predecessor pointers agree and its endpoints differ. `IsEndpoint` means exactly
one such incident edge. The finite theorem `exists_endpoint_ne_origin` obtains
another endpoint from a known source by matching the cardinalities of vertices
with incoming and outgoing edges. It permits disconnected cycles, self-loops
and inconsistent pointers; no global inverse assumption is needed. This generic
finite graph theorem has no ComplexityLib dependency.

The optional `Backend.EndOfLineProblem` serializes a unary width ruler and two
vectors of tagged Boolean circuit codes. Each vector has linear serialization
overhead. Its total evaluator returns exactly one output per vertex bit, using
zero for an invalid scalar code. Missing codes also produce zero. The existing
total pairing projections determine the meaning of malformed vector framing.
The ruler's length determines the width; its bit values have no semantic role.

A valid source has `P(0)=0`, `S(0)≠0`, and `P(S(0))=0`. Accepted witnesses then
have exactly that width, differ from zero, and satisfy the generic endpoint
predicate. Invalid source promises accept precisely the empty witness. This
convention makes the relation total on every input word. It uses consistent-edge
endpoints, rather than the broader familiar raw pointer-inconsistency witness
condition; the uniform normalization below proves their search equivalence.

`Backend.CircuitVectorMachine` proves actual FP evaluation through the verified
scalar circuit machine, bounded code selection and a bitwise output compiler.
`Backend.EndOfLineVerifier` checks the origin and immediate candidate neighbors,
validates the witness width and canonical paired verifier input, and certifies
a single deterministic polynomial-time machine. No computation enumerates the
`2^n` vertices. Balance bounds every accepted witness by the input length;
`endOfLineRelation_mem_TFNP` combines that bound, the verifier and finite totality.

The current backend uses native `Cslib.Complexity.SearchReducible` with explicit
instance encodings, polynomial-time instance maps and original-instance answer
decoders. It preserves **every** valid target answer and the source/target domain
obligation. Identity and composition have native machine certificates.
Composition gives each decoder its own instance. TFNP transport also requires
independent source FNP membership: other accepted witnesses need not be bounded
or efficiently checked. The earlier local `Backend.SearchReduction` record is
retired; the native `Tests.SearchReduction` controls remain.

This establishes the filtered-edge search foundation. The next section supplies
the standard raw convention and PPAD class. Uniform normalization then connects
the encodings. Brouwer/Sperner reductions, Nash search completeness and
approximation conventions remain further obligations.

The earlier backend checkpoint passed 4,366 base jobs and 3,827 companion jobs. All
937 owned declarations have only standard transitive axioms. Both linters,
architecture checks and 19 optional-boundary regression cases pass. The
released-mode consumer builds the facade, composed machine, NP-completeness and
End-of-Line endpoints and fixtures in 3,814 jobs against public base commit
`81ab22b375b12a8f869484deb982ac9b5c845803`, without a local-path override.
Dependency-mode switches use `lake -R update` to re-elaborate cached
configuration; CI asserts both local-path and released-git manifest modes.

## Standard End-of-Line and PPAD

`GameTheoryComplexity.PPAD` uses the standard raw condition
`P (S x) ≠ x ∨ (x ≠ origin ∧ S (P x) ≠ x)` under the weak source
promises `P origin = origin` and `S origin ≠ origin`. An outgoing
inconsistency may return the origin. Invalid promises accept exactly `[]`;
valid inputs require exact-width witnesses and canonical paired verification.
The relation has a genuine polynomial-time verifier, balance and totality,
including the broken-initial-link case, so it belongs to TFNP.

Native `Cslib.Complexity.PPAD` membership includes independent source FNP
evidence and encoded search reductions. `endOfLineRelation_PPADComplete` and
`rawEndOfLineRelation_PPADComplete` prove native `SearchComplete @PPAD encBits`
for arbitrary encoded source types through actual circuit maps and every-answer
decoders. TFNP containment and transport retain the independent FNP requirement.

The certified raw-to-endpoint reduction keeps the instance and decodes every
filtered-edge solution. With a genuine source it keeps the endpoint. When only
the initial link is broken it maps the target fallback to the origin; invalid
weak promises retain the empty fallback. Native `ComputableInPolyTime`
certificates cover its instance map and original-instance answer decoder.

Generic normalization replaces inconsistent pointers by self-loops, preserving
edges and endpoints. Its pointer-word evaluators have native
`ComputableInPolyTime` certificates. `nativeEndOfLine_searchReducible` and
`nativeEndOfLine_raw_searchReducible` supply both native circuit-family
reductions, preserving every answer, including width zero and failed source
promises. EXP-161/D69 and EXP-163/D71 record the earlier convention and
normalization evidence; EXP-172/D77 records the native class decision.

Validation: the base build and lint pass 4,368 jobs. The optional library,
lint scope and transitive axiom audit pass 3,835 jobs; all 1,024 owned declarations
use only standard axioms. Optional lint, isolation and 19 boundary regression
cases pass. Fixtures cover broken initial links, asymmetric origin handling,
isolated malformed pointers, exact widths, canonical pairs and actual decoder
behavior. Released-mode validation resolves public base commit
`790fbe3f8d0b745b1c111dd3cea508dd399a335f` and passes 3,821 jobs.

## Certified serialized prefix restriction

Import `GameTheoryComplexity.Backend.CircuitPrefixCompiler` to hardwire a seed
into a raw scalar circuit code. `restrictCircuitCode ruler seed code` uses the
ruler's length as the live input width. For positive live width and an input of
that width, `restrictCircuitCode_eval` proves exact `evalCode` agreement with the
original code evaluated on `seed ++ input`, for every source code. This includes
malformed syntax and invalid topology. Empty circuits and zero live width return
empty code; the evaluation theorem requires positive live width.

The compiler first validates exact raw syntax. It emits seed constants and
live-input copies, then shifts every original wire reference uniformly. This
preserves sharing, while the upstream shift theorem preserves evaluation
failures. The full compiler and validator have actual FP certificates. The
private bounded scanner's intermediate states are polynomially bounded; no
runtime claim is inferred from output size alone.

The local companion/lint/axiom build passes 3,843 jobs and audits all 1,194 owned
declarations with standard axioms only. Lint, structural architecture, optional
isolation and all 19 boundary regression controls pass. Fixtures cover a shared
diamond's entire two-input truth table, a forward reference, empty syntax,
empty-output guarding, zero live width, malformed fields, garbage and incorrect
input width. EXP-162 and D70 record the validated layout.

This closes prefix restriction as a component. The following integration supplies
the reverse End-of-Line reduction. Nash search completeness remains open.

Released-git smoke passes 3,829 jobs against public base `790fbe3f`; its
compiler fixture runs alongside the existing facade, composed machine, NP and
PPAD endpoints. Local-path mode is restored after the check.

## Uniform normalized End-of-Line instances

This is the historical pre-native implementation checkpoint. Its prefix
specialization route is superseded by `Backend.NativeCircuitFamilies` and
`EndOfLineCircuitGeneration.exists_activeEndOfLineInstance`.

`Backend.UniformCircuitSpecialization.exists_prefixCircuitGenerator` starts
with a genuine FP one-bit computation. The upstream unconditional uniform
containment theorem supplies an FL circuit-code generator; FL is contained in
FP. Generating the full-input circuit, removing its family tag, compiling a
fixed prefix, and restoring the tag are all polynomial-time word operations.
The resulting generator preserves exact scalar evaluation at positive live width.

`Backend.EndOfLineScalarQueries` queries a normalized pointer bit from a paired
instance, unary output index and live vertex. The compiler fixes the instance
and index as the circuit's prefix. `Backend.CircuitVectorEmission` emits one
such circuit for each coordinate, in ascending order. Cobham bounded recursion
certifies the serializer's runtime; a polynomial bound on each scalar producer
bounds every intermediate accumulator. It never enumerates vertices.

`Backend.EndOfLineCircuitGeneration.exists_normalizedEndOfLineInstance` combines
the two vectors and a unary width ruler. On a genuine source its pointers agree
with normalized evaluation at every exact-width vertex. A genuine source has
positive width, so it meets the prefix compiler's requirement. Invalid source
promises, including width zero, map directly to the empty invalid instance.

`Backend.NormalizedEndOfLineReduction` certifies the reverse search reduction
with an FP instance map and identity FPn answer decoder. Consistent pointers make
every raw target witness precisely an original non-origin endpoint. Invalid
inputs preserve the empty fallback. Together with the existing forward
reduction, `endOfLineRelation_PPADComplete` classifies filtered endpoint search
as complete for the standard raw End-of-Line definition of PPAD.

This closes an encoding equivalence, not a concrete Sperner, Brouwer or Nash
search reduction. Those results remain separate delivery obligations.

Validation: the full companion/lint/axiom build passes 4,102 jobs, with all 1,257
owned declarations using only standard transitive axioms. Lint, structural
architecture, dependency isolation and all 19 boundary controls pass. New
controls check ascending coordinate order, empty output vectors, scalar output
indices and normalized isolated vertices. Released-git smoke passes 4,089 jobs
against base `790fbe3f`, including the public PPAD classification and new fixtures.
Local-path mode is restored. EXP-163 and D71 record the integration evidence.

## Concrete square-grid Sperner totality

The base mathematical leaf `GameTheory.Math.GridSperner` proves the
two-dimensional square-grid Sperner theorem. Each square is split along its
rising diagonal. Its color function has values in `Fin 3`; the left boundary
forbids color one, the bottom forbids color two, and the top and right forbid
color zero. These are the general boundary exclusions, rather than a requirement
that each boundary have a fixed color.

`SpernerTriangle` counts oriented zero/one transitions. A triangle has nonzero
flux exactly when its colors are pairwise distinct. `GridFlux` cancels shared
edges using Mathlib's existing telescoping identities. The diagonal cancels
inside each square, and the entire grid leaves only its boundary. The bottom
count telescopes to one; the remaining sides contribute zero. Thus
`sum_gridFlux_eq_one` gives exact signed count one and
`exists_grid_trichromatic` returns bounded square coordinates and a trichromatic
lower or upper half. The argument supports multiple boundary transitions.
The standard geometric setting and its directed-path interpretation are
described in [the MIT Sperner lecture notes](https://www.mit.edu/~6.7980/brouwer.html).

`standardGridColor` enforces a canonical boundary by inspecting only the given
coordinates, preserving every strict interior value. It establishes the
boundary condition at every positive size without enumerating vertices. All
these definitions and proofs are independent of ComplexityLib and topology.

The theorem/control/lint-scope build passes 4,068 jobs, and base lint passes.
A transitive audit checks all 37 declarations owned by these modules and their
fixtures, allowing only `propext`, `Classical.choice` and `Quot.sound`.
Controls distinguish
both triangular halves, arbitrary interiors, repeated boundary transitions,
missing boundary assumptions and size zero. Structural checks and optional
dependency isolation pass. This establishes mathematical totality; binary cell
encoding, local predecessor/successor machines and a polynomial-time every-answer
reduction are still required for succinct Sperner PPAD membership. No such
classification or Brouwer/Nash reduction follows from this existence proof alone.

## Local directed Sperner graph

`GameTheory.Math.SpernerDoors` selects an incoming side with zero/one flux `+1`
and an outgoing side with flux `-1`. Each sign occurs on at most one side.
Exactly one sign is present precisely when the triangle is trichromatic.
`SpernerGridGeometry` represents a triangle by two natural coordinates and its
half-square bit. Crossing a numbered side computes the adjacent triangle and
its reversed side, or reports an exterior edge. The proofs certify coordinate
bounds, reciprocal crossing, distinct neighbors and opposite edge orientation.

The graph uses `standardGridColor` to enforce its boundary locally. The only
exterior zero/one door is the first lower triangle's incoming bottom side.
`SpernerGridGraph.gridPointer` connects that entrance to one added source node,
returns a self-loop for an absent door, and isolates out-of-range coordinates.
For every selected door, the opposite pointer returns to the original node.
This links local door presence to the canonical `Math.EndOfLine` edge predicates.

`grid_endpoint_iff` identifies valid triangle endpoints exactly with
trichromatic cells. `grid_endpoint_decodes` establishes that every endpoint
other than the added source is valid and trichromatic, independently of its
component. `grid_source` proves the source promises at positive size, including
size one when the entrance triangle itself can be the answer.
`exists_grid_endpoint` obtains a bounded endpoint from the established grid
Sperner theorem. The local functions inspect three corners and one neighbor;
they do not traverse a path or enumerate the grid.

The graph/control/lint-scope build passes 4,072 jobs, and base lint passes.
Controls execute a closed
six-triangle cycle disconnected from the source, both endpoint orientations,
size-one source and sink behavior, invalid-coordinate isolation and zero-size
source failure. Independent semantic and proof-simplification reviews found no
gaps; structural checks and optional dependency isolation pass. A transitive
axiom audit checks all 89 declarations owned by the four new mathematical
modules and their fixtures, allowing only standard axioms.

This supplies the semantic local graph for canonical boundary colors. It is
not a padding reduction from arbitrary boundary colorings. Succinct binary cell
encoding, actual FP pointer machines, polynomial-time circuit emission and the
word answer decoder remain the next obligations before claiming Sperner PPAD
membership. The base mathematical modules have no ComplexityLib dependency.


## Binary Sperner graph and FP primitives

`Backend.SpernerGridCodec` uses a `2*b+2`-bit word: a source/triangle tag,
an orientation bit and two little-endian `b`-bit coordinates. The unique
source is all zero. Every triangle-tagged word denotes a valid triangle in
a grid of side `2^b`; unused source-tagged words and incorrect lengths are
rejected. Encoding and decoding are exact inverses on their valid domains.
At `b=0` the grid has side one, with distinct source and triangle codes.

`Backend.SpernerGridWords.wordGridPointer` transports the established local
graph to words and isolates rejected codes. Its proofs establish unconditional
length preservation, source promises, endpoint correspondence and bounded
endpoint existence. `word_grid_endpoint_decodes` covers every non-source word
endpoint, including components disconnected from the source.

`Backend.SpernerGridCodecMachine` supplies actual FP certificates for source
word production, field extraction, orientation reading and exact acceptance.
`Backend.SpernerBinarySteps` supplies actual FP certificates for ripple-carry
increment and borrow decrement. Their recursion is over the input bits, with
fixed output length, never over the coordinate's numeric value. Arithmetic
correctness requires no overflow for increment and a positive value for
decrement; execution wraps at the fixed width.

The optional package's released base pin advances to
`a58d028f7fe4161782169c7f8c32dd793426b29c`, which publishes the prerequisite
Sperner mathematics. Clients of the base library still need no ComplexityLib.

The native pointer certificates enforce canonical boundary colors before
incrementing corner coordinates: a boundary corner can equal `2^b`, outside a
`b`-bit field. Uniform native circuit generation and every-answer
`SearchReducible` proofs complete the subsequent Sperner classification.


Validation: the full companion, lint scope and axiom driver build pass 4,114
jobs, auditing 1,356 owned declarations with standard axioms only. Optional
lint, structural checks, dependency isolation and all 19 isolation controls
pass. The released-git smoke builds the facade, Nash NP-completeness, PPAD,
normalized End-of-Line and binary Sperner controls in 4,093 jobs against the
new pin; local-path mode is restored. Read-only proof/software review found
no gaps and identified the boundary-overflow requirement for the next slice.


## Uniform polynomial-time Sperner pointer

`Backend.SpernerCornerMachine` appends a high zero bit before incrementing
corner coordinates. Thus a right or top boundary coordinate `2^b` remains
distinct from zero. Canonical colors give the bottom edge priority, then the
right/top edges, then the left edge, and query the interior only otherwise.
Interior queries receive two little-endian `(b+1)`-bit coordinates. Arbitrary
query outputs are normalized to two color flags with color one taking priority.

`Backend.SpernerCrossMachine` checks coordinate zero/max before taking an
exterior edge or applying the fixed-width increment/decrement. Its word
crossings agree with the geometric `across` operation on every valid triangle.
`Backend.SpernerDoorMachine` checks three oriented zero/one edges in the same
order as the mathematical door selector. Its FP certificate combines constant
controls rather than enumerating vertices.

`Backend.SpernerPointerMachine.gridPointerMachine_polyTime` composes these
operations into a native `ComputableInPolyTime` certificate. Its generic producer
form charges the ruler and vertex producers together with the joint certificate
for the captured color query. `spernerPointer_polyTime` specializes this to a
serialized color circuit vector and charges the complete instance and vertex
producers. The implementation agrees with `wordGridPointer` on all words,
preserving lengths and rejected-word isolation. Source promises and every-endpoint
trichromaticity therefore hold for the concrete serialized-circuit pointer itself.

The native pointer feeds the certified End-of-Line circuit-instance map and
every-answer decoder used by the completed succinct Sperner classification.


Validation: the full optional library, lint scope and axiom driver pass 4,119
jobs, auditing 1,468 owned declarations with standard axioms only. Optional
lint, structural checks, dependency isolation and all 19 isolation regressions
pass. Released-pin smoke passes 4,098 jobs against the published base pin,
including the new pointer fixtures, then local-path mode is restored. Controls
cover all zero-coordinate-width words, boundary carry and query order, color
normalization, source paths, upper endpoints, malformed codes, a disconnected
six-triangle cycle and actual uniform FP certification. Independent semantic,
software and proof-simplification reviews found no gaps.


## Succinct Sperner PPAD membership

`Backend.SpernerProblem.spernerRelation` asks for a triangle word whose three
canonical vertex colors are distinct. Decoding enforces coordinates inside the
power-of-two grid; witnesses have exactly `2*b+2` bits and linear balance in
the serialized input. Boundary enforcement makes every circuit input a total
coloring problem, including malformed codes under the established total circuit
evaluation convention. This is not a promise problem for arbitrary boundary
colorings.

`Backend.SpernerVerifier` supplies an independent actual FP verifier, its
single deterministic machine certificate and FNP membership. It checks exact
node acceptance, the triangle tag and pairwise distinct canonical corner
colors. Its outer pair guard accepts precisely the encoded pair language;
malformed verifier inputs do not become witnesses through permissive decoding.

`Backend.PointerCircuitGeneration` extracts the shared uniform compiler from
normalized End-of-Line generation. It specializes each scalar pointer query
and emits both circuit vectors with actual FP certificates and exact
positive-width agreement. Existing normalized End-of-Line generation now uses
this same implementation, preserving its invalid-source fallback.

`Backend.SpernerReduction.exists_spernerEndOfLineInstance` applies the compiler
to the certified Sperner pointer. The node width is always positive, including
zero coordinate bits, and the emitted instance has the proved source promises.
Every target endpoint yields the same trichromatic triangle word, independently
of its graph component. The decoder is the native polynomial-time second projection.
No path traversal, grid enumeration or selected-solution assumption is used.

`GameTheoryComplexity.Sperner.spernerRelation_mem_PPAD` combines that reduction
with the independent FNP certificate and the established End-of-Line PPAD
membership. TFNP membership and totality follow. A reverse reduction proving
Sperner hardness remains open, as do arbitrary-boundary padding and downstream
Brouwer/Nash search completeness.


Validation: the full optional library, lint scope and axiom driver pass 4,125
jobs, auditing all 1,511 owned declarations using only standard axioms. Optional
lint, architecture checks, dependency isolation and all 19 boundary regressions
pass. Released-pin smoke passes 4,104 jobs, including existing normalized
End-of-Line controls and the new Sperner classifier/verifier fixtures; local
path mode is restored. Controls cover zero/nonzero coordinate widths, both
triangle orientations, source exclusion, malformed node and verifier encodings,
malformed color circuits, semantic verifier agreement, and the actual FP
instance mapper's exact width. Independent semantic/software/proof-simplification
reviews found no gaps or unsupported completeness claims.


## Planar crossing switch for Sperner hardness

The [Chen–Deng construction](https://eccc.weizmann.ac.il/report/2006/037/download)
uses crossing switches that preserve directed leaves while changing path
connections. `Math.GridCrossing` implements all four orientations with two
bends, reciprocal edges and preserved port roles. `Math.GridCrossingGeometry`
embeds the nine nodes injectively in a three-by-three grid; every nontrivial
pointer step is an axis-aligned unit edge.

`Math.GridCrossingAttachment` compares switched and original strand
connections in an arbitrary exterior graph. It proves equivalence of valid
incoming-edge presence, outgoing-edge presence and endpoint status for every
node. Exterior pointers may be inconsistent, and attachments may be absent
or aliased. Used bends have two consistent edges; unused bends and the center
remain isolated. A fixture closes the original strands into two cycles and
shows that switching joins them into one cycle without introducing endpoints.

This was a proved local routing prerequisite at its historical checkpoint. Global succinct routing, original
endpoint decoding, wire colors, a canonical boundary/source hook and actual
FP/FPn reduction certificates remain before Sperner hardness. The mathematical
modules have no ComplexityLib dependency. The source paper's triangular region,
diagonal orientation and boundary convention require explicit translation;
its coloring cannot be imported unchanged into the current square-grid problem.


Validation: gadget fixtures and the full base lint scope build pass 4,076 jobs.
Base lint, structural checks, dependency isolation and all 19 boundary controls
pass. A transitive axiom audit checks all 137 declarations owned by the three
new mathematical modules and their two fixture modules, accepting only standard
axioms. Independent review found no semantic gaps; cycle fixtures explicitly
check both original four-step returns and the switched eight-step return.

## Directed wire routes and crossing ownership

`Math.GridWire` routes an edge from vertex `(0, 6*i)` east to column
`3*(n*i+j)`, vertically to row `6*j+3`, west to the boundary, then down to
vertex `(0, 6*j)`. The local predecessor and successor are executable and
work in either vertical direction. For a non-loop edge they are reciprocal
on every nontrivial step, leave off-wire points isolated and have exactly the
two original vertices as endpoints.

`Math.GridWireLanes` proves that bounded vertex pairs have distinct columns
below `3*n*n`, spaced at least three grid units apart. Incoming and outgoing
rows are separated, and the route visits no unrelated original vertex.
`Math.GridWireCrossings` uses reciprocal End-of-Line pointers to rule out
shared source or target lanes between distinct active edges. Every intersection
is either a common original vertex or a strict horizontal/vertical crossing.
Crossings have three-step clearance from bends, disjoint three-by-three switch
boxes and no third active wire inside a box. Neighboring boxes may have directly
adjacent ports; the proofs do not assume an extra empty row between them.

These were the geometric prerequisites at the historical routing checkpoint, with no
ComplexityLib dependency. The next slice must assemble globally consistent
switched pointers, prove preservation and decoding of every original endpoint,
and implement bounded local queries. Wire coloring, the canonical square-grid
boundary/source hook and actual FP/FPn reduction certificates still follow
before Sperner hardness. No completeness result is claimed by this slice.

Validation: the wire controls and full base lint scope build pass 4,078 jobs.
Base lint, structural architecture checks, dependency isolation and all 19
boundary regressions pass. A transitive audit accepts all 173 declarations
owned by the three new mathematical modules and their fixture module using
only standard axioms. Independent semantic, software and proof-simplification
reviews found no gaps. Controls exercise ascending and descending routes,
endpoint and off-wire behavior, both crossing directions, adjacent switch
ports, disjoint boxes and overlapping lanes when edge uniqueness is absent.

## Global routed grid pointers

`Math.GridRoutedGraph` now supplies actual predecessor and successor functions
on natural-number grid coordinates. Every nontrivial step is reciprocal and
axis-aligned with unit length. Background points are self-loops. For original
pointers preserving the bounded vertex set, every original vertex retains its
endpoint status and every grid endpoint decodes to an original endpoint, even
on components disconnected from the known source. The decoder simply reads
the endpoint's row divided by six. A known original source remains a known
grid source.

The construction first uses `Math.GridWireGraph` to distinguish the two wire
occurrences at each crossing. `Math.EndOfLineTailSwitch` proves that an
involution exchanging internal continuations preserves incident-edge roles
and endpoints; `Math.GridWireSwitch` verifies its hypotheses for every crossing
simultaneously. It excludes old edges between exchanged occurrences, preventing
new self-loops. No comparison-graph isomorphism or general graph framework is
needed.

`Math.GridCrossingPlacement` embeds and decodes each switch box.
`Math.GridCrossingLocator` identifies its nearest spacing-three center and
extracts the two possible owners from the row and column, using original
pointer queries. `Math.GridWireImage` moves just the crossing centers to their
assigned bends; `Math.GridWireRealization` proves coordinate injectivity on
live labels and excludes collisions with original vertices.
`Math.GridWireDecoder` validates at most six locally derived candidates and
proves an exact inverse on the live image. Removed centers and unused bends
are rejected. `Math.GridWireImageSteps` connects this coordinate map to the
local switch, including directly adjacent ports of neighboring boxes.

At this historical checkpoint, the modules had no ComplexityLib dependency. The six-candidate bound proves
locality; it is not an actual FP machine certificate. Coordinate word layouts,
certified FP arithmetic and queries, routed-wire colors, canonical square-grid
boundary/source translation and the FP/FPn hardness reduction remain open.
The current result does not yet prove Sperner PPAD-hardness.

Validation: the global routing controls, prior individual-wire controls and
full base lint scope build pass 4,089 jobs. Base lint, structural architecture
checks, dependency isolation and all 19 boundary regressions pass. A transitive
audit accepts all 365 declarations owned by the ten new mathematical modules,
the updated crossing module and the new fixture module using only standard
axioms. Independent semantic, software and proof-simplification reviews found
no gaps. Controls execute adjacent switches in both pointer directions,
ascending and descending crossing routes, displaced-center decoding, removed
centers and unused bends, malformed reciprocity, zero-size and background
inputs, and exact all-point endpoint sets including a disconnected cycle.

## Succinct square-grid Sperner completeness

`GameTheoryComplexity.Sperner.spernerRelation_PPADComplete` proves completeness
for standard PPAD of the existing canonical succinct grid relation. Membership
uses the previously certified directed triangle graph. The reverse reduction
has native `ComputableInPolyTime` color queries and circuit-instance generation,
plus an every-answer `SearchReducible` proof.

The dependency-free construction expands routed vertices into size-six color
tiles. A boundary entrance replaces the known source witness; inactive two-color
padding prevents extra answers when a power-of-two square cuts partial tiles.
Every remaining trichromatic triangle decodes to a bounded original endpoint
other than zero by row division by 36, regardless of its connected component.
The square uses `2*b+8` coordinate bits for `b`-bit original vertices. Fixed-width
normalization connects natural routing labels to the original circuit relation;
invalid source promises retain its required empty-witness fallback.

`Backend.GridSpernerColorMachine` supplies exact all-word query semantics and
actual seeded uniform FP evidence. `SpernerCircuitGeneration` reuses the shared
pointer compiler to serialize color circuits. `SpernerRoutingDecoderMachine`
composes two certified divisions by six, canonical label padding and the source
flag. `EndOfLineSpernerReduction` joins these certificates into the concrete
search reduction. The backend remains an opt-in package; the mathematical
coloring imports no complexity dependency. Brouwer and Nash search reductions,
approximation conventions and FIXP remain separate obligations.


## Continuous approximate Brouwer search

`GameTheoryComplexity.Brouwer.brouwerRelation_PPADComplete` proves the
continuous rational-point classification following the earlier simplicial
barycenter result. An instance consists of the existing width ruler and color
circuit, with canonical boundary correction. Its grid side is `n = 2^b`.
An answer encodes two numerators of `b+3` bits each, bounded by `6n`, denoting
`p = (X/(6n), Y/(6n))`. Acceptance means exactly
`|F(p).x - p.x| ≤ 1/(6n)` and `|F(p).y - p.y| ≤ 1/(6n)` for the actual real map.
No triangle or barycenter certificate accompanies the point.

The mathematical layer defines the map as a finite sum of continuous vertex
hat functions, then proves agreement with affine interpolation on both halves
of every square. Boundary colors make the vertex images stay in the square;
convex interpolation and normalization give a continuous unit-square self-map,
including seams and the closed top/right edges. The sixth-grid geometry
reconstructs any represented point and proves that its exact rational local
displacement is the real map residual multiplied by `n`.

The two search reductions retain the instance unchanged. To solve Sperner
using a Brouwer answer, binary division by six and boundary clamping locate
the containing triangle; the small residual forces its three colors to be
distinct. Conversely, every trichromatic triangle yields its rational
barycenter, which has zero displacement. Both answer maps have native
`ComputableInPolyTime` certificates under the complete instance/answer
encoding; both `Cslib.Complexity.SearchReducible` proofs preserve every target answer. The existing Sperner
PPAD-completeness theorem therefore supplies both directions of classification.

Membership also has an independent verifier. It checks the exact answer length
and numerator bounds, computes the triangle and two local offsets, evaluates
three corner color circuits, and checks the exact weighted residual. The latter
uses a fixed table over seven possible offsets in each coordinate and three
colors at each corner (1,323 cases), independent of the grid size. Binary
arithmetic and joint circuit evaluation have composed native machine certificates.
The typed Boolean verdict and linear witness balance prove `FNP encBits`
membership; `SearchComplete @PPAD encBits` and native TFNP use the same relation.
Residual lookup compares exact words, retaining rejection of noncanonical fields.
Totality holds for every serialized input under canonical boundary correction.

The smallest-grid controls accept `(4/6, 1/6)`, whose residual is
`(-1/6, 1/6)`, and the exact fixed barycenter `(4/6, 2/6)`. They reject
`(5/6, 1/6)` even though it lies in a trichromatic cell, malformed words,
out-of-square numerators and the far corner. Binary location handles diagonal
equality and the closed far edge. Kernel-checked verifier correctness and exact
rational arithmetic validate these controls without additional axioms.

This classifies the stated succinct color-induced map family and finite output
precision. It does not classify arbitrary piecewise affine input languages,
unrestricted rational denominators, distance to an exact fixed point, or FIXP.
Ordinary clients still require no complexity dependency; the public theorem
lives in the optional companion package.

Final shared-toolchain validation commands for the continuous slice
(companion Lake commands run
from `extensions/complexity`; the others run from the repository root):

```text
lake build GameTheory GameTheory.LintAll
lake lint
lake env lean .codex/scratch/BrouwerAxiomAudit.lean
lake -KgameTheoryPath=../.. build GameTheoryComplexity GameTheoryComplexity.LintAll GameTheoryComplexity.AxiomAudit
lake -KgameTheoryPath=../.. lint
python scripts/audit.py --source-only
python -m unittest discover -s scripts/tests
```

The native matching-toolchain checkpoint passes 5,328 jobs, including public
continuous and simplicial Brouwer leaves, coordinate-circuit generators and the
rational-point controls. Its transitive audit checks 2,801 authored declarations
using only `propext`, `Classical.choice` and `Quot.sound`. Source isolation and
coverage pass. Full matching-toolchain optional build/lint/axiom gates now pass;
the final stable consumer merge gate is blocked as recorded above.

Before the native API migration, the full continuous slice passed 4,198 companion
jobs in local and published-base-pin configurations at `b2a5e098`; that historical
run does not validate the current dependency selection.

## General rectangular binary Nash certificates

`Backend.GeneralBimatrixFNP.generalBimatrixRelation_mem_FNP` proves native
`FNP encBits` membership for exact mixed Nash certificates of independent signed
integer payoff matrices. The input has unary row, column and coefficient-width
headers and two row-major matrices with positive and negative binary fields.
The answer contains two denominators, two signed utility numerators and both
probability-numerator vectors. For input length `L`, each unsigned field has
width `(2*L+2)*(8*L+6)+1`; total witness length is cubic in `L`.

The actual verifier checks exact lengths, positive denominators, simplex
equations, every pure deviation inequality and equality on positive support.
Signed comparisons combine positive and negative scores with both utility
fields. Native machine composition charges every width, scan, arithmetic
operation and complete input/witness encoding. `generalBimatrixAccepts` returns
a Boolean under `encPair encBits encBits`; the unused outer-pair verifier
adapter is retired. Malformed game instances accept precisely the empty answer.
Short and simultaneously positive/negative fields retain their total decoding.

Accepted valid answers yield canonical PMF mixed Nash equilibria. A supplied
canonical equilibrium yields an exactly serialized bounded certificate.
`Backend.GeneralBimatrixTotality` additionally uses finite complementary-path
existence to prove native `TFNP encBits` membership for every input, without an
Analysis import. Native node, pointer, endpoint and every-answer PPAD reductions and the public
Nash completeness facade now pass the full matching-toolchain library, lint,
axiom and authored-diagnostic gates. The final stable consumer merge gate is
blocked as recorded above; verification and totality do not supply a polynomial-time solver.

The matching-toolchain verifier, totality, determinant and dictionary checkpoint
passes 6,756 jobs. Its expanded transitive audit checks 2,943 authored declarations
using only `propext`, `Classical.choice` and `Quot.sound`. Signed, singular,
zero-width, malformed-length and support controls compile. Source isolation and
coverage pass, along with all 44 script regressions. Full matching-toolchain
optional build/lint/axiom gates now pass; the final stable consumer merge gate
is blocked as recorded above.
The earlier 4,218-job full companion run at base `e4b2d039` predates the native
API migration and does not validate the current dependency selection.

## Complementary decoding prerequisite

The base now supplies the mathematical contract needed by the general Nash
PPAD reduction. `Math.LinearComplementarity` is independently reusable ordered
field mathematics. `Finite.BimatrixComplementarity` uses off-diagonal negative
payoff blocks and unit affine constants. A represented nonzero complementary
point has positive mass in both coordinate blocks and normalizes into the
existing exact Nash certificate. Row coordinates use scale `Dx`, column
coordinates use `Dy`; the cleared row utility is `Dy` and the column utility
is `Dx`. Keeping these independent handles rectangular games and unequal
scales.

Payoff-shift invariance handles signed tables. Adding `2^h+1` to a coefficient
of magnitude at most `2^h` gives a positive coefficient strictly below `2^(h+2)`.
The correctness module undoes independent shifts in the decoded certificate
and yields canonical PMF mixed Nash for the original game. Positive-payoff
certificates also map back to nonzero complementary points. Degenerate and
tied supports need no exceptional premise; the artificial zero solution is
explicitly excluded from decoding.

These base modules import no complexity package and no analytic existence
theorem. The companion's FNP classification is unchanged. The local symbolic
pivot mathematics below supplies the next prerequisite. Canonical complementary
nodes, oriented pointers and actual polynomial instance/answer machines remain
necessary to prove PPAD membership and serialized totality. These are local
mathematical results, not a completed path-following algorithm.

Validation passes the full 4,433-job base/lint-scope build, base lint, both
structural audits and a transitive standard-axiom check for all 88 new
declarations. The mathematical controls include direct exact rational
complementarity with unequal scales, fully degenerate games and the strict
positive-shift bit bound at `h = 0`.

## Symbolic dictionary pivots

The base supplies four independent Math leaves: `FiniteLexicographic`,
`PerturbedDictionary`, `DictionaryPivot` and `LexicographicPivot`. Finite
coefficient vectors use Mathlib's lexicographic order. Inverse-basis rows encode
the constant followed by independent perturbation coefficients; eligible
scaled rows are distinct. A minimum-ratio pivot is therefore unique and
preserves strict symbolic feasibility. Matrix column replacement has an exact
determinant and inverse-coordinate formula, and the same ratio rule selects
the restored old column on reversal.

`Finite.BimatrixPivotSource` instantiates these proofs at the identity slack
basis for positive-payoff nonempty rectangular games. Its successor is
invertible and strictly feasible. The degenerate 1×2 control resolves equal
ordinary ratios and preserves a row with zero constant term. All these are
mathematical proofs; no new executable basis solver or companion dependency
is introduced. Canonical almost complementary nodes, global pointer laws,
secondary-ray exclusion, perturbation decoding and polynomial machine costs
remain required for PPAD membership.

Validation: the full base/lint/control build passes 4,443 jobs. Base lint,
architecture and optional-dependency isolation pass; the transitive audit
checks all 94 new declarations using only standard Lean axioms. The companion
source and dependency pin are unchanged in this slice.

## Canonical complementary bases

`FiniteBasisExchange`, `DictionaryReindex`, `ComplementaryLabels` and
`CanonicalDictionary` are independent Math leaves. A basis is a finite set,
not a freely ordered list; Mathlib's sorted enumeration gives one matrix per
set. Sorting an exchange permutes only inverse-system solution coordinates,
leaving perturbation coefficients attached to their original equations.
Feasibility and reverse selection survive this permutation. Complementary-label
counting and coverage-preserving exchange are independent of matrix semantics.

`Finite.BimatrixBasis` combines these proofs. Its basis certificate contains the
size, nonzero determinant and strict symbolic feasibility. Its path node adds
coverage of nonbasic binding labels except the fixed dropped label. A pivot
requires an entering variable outside the basis, a symbolic leaving row, and a
dropped or duplicated nonbasic label. The successor satisfies the same node
invariants. The all-slack source is unique by its set of variables, avoiding
extra nodes created by reordered source columns.

The following slice supplies ray exclusion and rational terminal extraction.
Graph orientation and global inverse pointer laws remain open. The
noncomputable mathematical certificates do not supply binary node serialization
or polynomial machine costs.

Validation: full base and lint-scope build, 4,453 jobs; base lint and both
structural audits pass. The transitive standard-axiom audit checks all 145 new
declarations. Independent review confirms label orientation, sorted-coordinate
transport and the explicitly local scope of the certificates.

## Ray-free pivots and terminal extraction

`Math.NonnegativeDictionary` gives the positive-direction theorem, and
`Finite.BimatrixBasisExit` shows that every variable has a positive column entry
when both game dimensions are nonzero and payoffs are strictly positive. Every
certified basis therefore has a unique leaving row for every entering port.
The theorem rules out secondary rays in this nonnegative-column representation.
The dimension and payoff assumptions are on the operation, not basis data.

`Finite.BimatrixPivot` supplies a deterministic noncomputable port pivot. Its
opposite port enters the old leaving variable; a second pivot restores the full
port. No fixed point is possible because the entering variable was nonbasic.
This gives an unoriented edge involution, with path orientation still open.

`Math.BasisCoordinates` extends inverse coordinates by zero outside the basis
and proves ambient equations and nonnegative constant values.
`Finite.BimatrixBasisSolution` extracts the original rational complementary
solution from complementary labels. Its payoff block is zero if and only if the
basis is the all-slack source, including degenerate constant coordinates.
The explicit 1×2 terminal control has a basic slack coordinate zero while its
symbolic coefficient vector remains strictly positive.

These modules add no complexity backend dependency. Global oriented pointers,
endpoint label classification, natural numerator/common-denominator encoding,
polynomial bit bounds and actual End-of-Line machines remain outstanding.

Validation: the full base/lint-scope build passes 4,463 jobs, lint and both
structural audits pass, and 119 declarations in the updated proof scope pass
transitive standard-axiom auditing. The companion source and base pin are
unchanged. Proof review confirms reverse-row choice and the unoriented scope
of the port operation.

## Oriented bimatrix End-of-Line paths

Four game-free Math leaves finish the graph prerequisites. `ComplementaryPorts`
classifies the one terminal or two internal ports and proves closure under
pivot exchange. `FacetOrientation` proves the signed-minor kernel identity and
exact negative-pivot-factor relation. `ComplementaryPortOrder` proves twin port
index equality and payoff parity reversal. `OrientedInvolutionPath` composes
colored edge and node involutions into actual successor/predecessor pointers,
with inverse laws and an exact End-of-Line endpoint predicate. Its controls
include a source-to-sink path alongside an unrelated cycle.

`Finite.BimatrixPath` gives finite certified path ports, a restricted pivot
involution, internal switching and a unique artificial source port.
`BimatrixPathOrientation` supplies an actual determinant-based rational color:
facet orientation reverses across a positive pivot, complementary-label payoff
parity reverses between internal twins, and source calibration is positive.
`BimatrixPathEndOfLine` defines the directed pointers, proves their internal
inverse laws, characterizes endpoints as complementary bases and proves the
source pointer conditions. Every other endpoint decodes to a nonzero rational
complementary solution; the finite graph theorem yields existence for nonempty
positive-payoff integer games without importing Analysis.

This closed the mathematical oriented graph and endpoint proof at its historical checkpoint, including
degeneracy and ray exclusion. Natural numerator/common-denominator endpoint
encoding, polynomial bit bounds and actual serialized FP/FPn maps remain.
The pointer definitions are noncomputable; no new PPAD classification or
serialized totality is asserted, and the optional companion is unchanged.

Validation: full base/lint-scope build, 4,477 jobs; base lint and both structural
audits pass. All 184 declarations in the new path scope pass transitive
standard-axiom auditing. Seven control modules and independent semantic review
check the facet orientation, source uniqueness, endpoint decoding, degeneracy
and unrelated cycles.

## Exact rational endpoint certificates

`Math.FiniteRationalEncoding` is an independently reusable Mathlib-only module.
It computes the product of the reduced denominators and clears every
nonnegative coordinate to a natural numerator. The common denominator is
positive even for an empty vector. Exact decoding preserves the supplied vector;
uniform reduced-fraction bounds give explicit bounds on the cleared fields,
including binary exponent bounds linear in the number of coordinates.

`Finite.BimatrixPathCertificate` applies this encoding to a nonzero
complementary endpoint, normalizes its masses and undoes independent payoff
shifts. Finite graph totality therefore yields exact Nash certificates for
nonempty signed integer games without importing Analysis. Composing with the
existing support-system theorem gives polynomial-width certificate existence.
The support-system witness may differ from the original endpoint: no bound on
all path nodes, polynomial-time endpoint traversal or PPAD reduction follows.
Controls preserve a degenerate rectangular endpoint with unequal column masses
and negative unshifted utilities, and check empty vectors and negative encoding
boundaries.

Validation: full base/lint-scope build, 4,481 jobs; lint and architecture audit
pass. All 29 new encoding/certificate/control declarations pass transitive
standard-axiom auditing.

## Total general bimatrix Nash search

`Backend.GeneralBimatrixTotality` proves that the existing binary relation has
an answer for every input. Valid nonempty games use finite-path certificate
existence, the support-system bit bound and the existing exact certificate codec.
Malformed instances retain precisely the empty answer. The relation, verifier
and field widths are unchanged. Combining totality with the already certified
FNP verifier proves membership in ComplexityLib's actual `TFNP` class.

The public `BimatrixNash` module exports `bimatrixNashRelation_mem_TFNP` and
`exists_bimatrixNashCertificate`. No Analysis dependency is added, and base
clients still need no optional dependency. The mathematical endpoint proof is
sufficient for totality; PPAD membership additionally needs polynomial-time
serialized graph pointers and every-answer reduction maps. This totality proof
does not provide an efficient Nash solver.

Validation: the full companion/lint/axiom build passes 4,248 jobs against both
the local checkout and published base pin `7f6fe6535a9af20d58300fb3bcfac8ce7478ee16`.
All 2,620 owned extension declarations pass transitive standard-axiom auditing.
Both linters, architecture/isolation audits, all 19 optional-boundary regression
tests and the architecture regression fixture pass. Released-pin CI explicitly
builds the new totality control module.

## Uniform binary bounds along bimatrix paths

`Math.IntegerDeterminantBound` owns the previously proved integer determinant
estimate. `RationalQuotientBounds` controls numerator and denominator reduction,
and `IntegerBasisBounds` gives exact Cramer quotients and binary field width
`d*(d+h)+1` for integer matrices and right-hand sides bounded by `2^h`.
These modules import only Mathlib and reusable mathematics.

`Finite.BimatrixBasisBounds` applies this bound to all certified bases, not just
the source or a selected equilibrium: constants, symbolic perturbation
coefficients, entering directions and payoff coordinates all satisfy it.
Integer columns are exact encodings of the existing canonical rational columns.
The result requires no positivity of payoffs and is independent of path length.

`BimatrixEndpointBounds` bounds the same endpoint's natural encoding after
normalization and payoff unshifting. With coordinate width `W` and shift width
`s`, fields fit `W*(m+n+1)+(m+n)+s+2`. Width checking does not imply validity;
controls include a negative coordinate whose truncated encoding is bounded but
invalid. Other controls cover negative determinants and reduced fractions,
empty matrices, singular-premise rejection and a degenerate rectangular pivot.

At this historical checkpoint, the direct product-denominator bound was polynomial but could exceed the existing
serialized field width. Sharing the Cramer denominator is the next compression
step. Binary graph codecs, efficient exact linear algebra and actual FP/FPn
pointer and every-answer maps remain before PPAD membership. No runtime bound
is inferred from the determinant expansion.

Validation: full base/lint-scope build, 4,490 jobs; lint and both structural
audits pass. All 58 declarations in the new bound/control scope pass transitive
standard-axiom auditing. Independent semantic review passes. The companion
source and released base pin are unchanged.

## Compact common-denominator endpoint certificates

`Math.IntegerCramerEncoding` clears an integer system's nonnegative solution
with one absolute determinant denominator and sign-adjusted Cramer numerators.
Decoding recovers every coordinate exactly; all fields retain the generic
quadratic bit bound. A negative-determinant control uses denominator `7`, compared
with `49` for the product of reduced denominators.

`Finite.BimatrixCramerCertificate` preserves the supplied basis point, normalizes
its payoff masses and undoes payoff shifts. Every complementary non-source basis
of a shifted signed game supplies a valid certificate within the existing
`bimatrixCertificateWidth`; no support-system witness is reselected. Shared
`BimatrixComplementaryCertificateBounds` controls mass sums and signed utilities,
and the earlier arbitrary-rational-vector bound now reuses it.

The signed one-action control has determinant `-24`, denominator `24`, payoff
weights `6/4` and original utility numerators `-12/-30`. Source certificates are
rejected. This closed the direct endpoint field-size gap at its historical checkpoint. Efficient exact linear
algebra, binary graph encodings and actual FP/FPn maps remain before PPAD.

Validation: full base/lint-scope build, 4,496 jobs; lint and architecture audit
pass. All 73 declarations in the compact-encoding/shared-bound/control scope
pass transitive standard-axiom auditing.

## Binary emission of supplied bimatrix endpoints

`Backend.GeneralBimatrixEndpoint.generalBimatrixEndpointWord` uses the common
Cramer denominator to serialize the supplied complementary non-source shifted
basis. Its acceptance theorem round-trips the same certificate through the
existing codec and proves the unchanged exact Nash relation for the original
input. It does not select a replacement equilibrium. Signed rectangular controls
exercise this contract; malformed inputs retain precisely their empty answer.

The public `BimatrixNash` module imports this leaf. Endpoint emission has no
polynomial-time certificate yet; efficient exact linear algebra and serialized
graph pointers remain before the Nash PPAD reduction.

Validation: full companion/lint/axiom build, 4,258 jobs against both the local
checkout and published base pin `6bb618ca511f7f2edf3d105f0b20d7882870fa96`.
The transitive audit checks all 2,624 owned extension declarations using only
standard Lean axioms. Both companion lint configurations, architecture and
optional-isolation checks pass, as do all 19 optional-boundary regressions and
the architecture regression fixture. Independent semantic review passes.
Released-pin CI includes the endpoint control module.

## Materialized determinant computation

`Math.TabulatedBirdDeterminant` executes Bird's division-free recurrence with
each stage stored in a row-major array. This prevents nested scalar functions
from repeatedly evaluating earlier stages. Its determinant identity reuses
Mathlib's correctness theorem. The implementation has no pivot search, division,
classical choice or finite-instance synthesis.

`Math.BirdIterationBounds` proves stage-entry magnitude at most `(2*n*B)^t*B`
for input magnitude `B`, and polynomial binary width `(n+1)*(h+n+2)+1` through
`n` stages for coefficients bounded by `2^h`. `IntegerCramerComputation` connects
the stored arrays to those bounds and proves exact agreement of the computed
Cramer fields with the canonical encoding. The existing bimatrix endpoint
certificate producer uses these fields without a client API change.

At this historical checkpoint, the slice supplied executable determinant arithmetic and bounded its stored integer
entries. It does not yet supply a binary FP/FPn certificate. Machine-certified
matrix loops, ratio selection, graph codecs and pointers remain before Nash PPAD
membership. These generic leaves import only reusable mathematics.

Validation: full base/lint build, 4,500 jobs; lint and architecture/isolation
audits pass. All 92 declarations in the computation and changed endpoint/control
scope pass transitive standard-axiom auditing. Independent semantic review
passes. Kernel-checked controls include signed, singular and empty matrices,
zero leading pivots, several stages and a dense six-dimensional matrix.

The companion passes its full 4,263-job library/lint/axiom build against both
the local checkout and published base pin
`14183a4c203cfbc18c4ec99234ebdf53ab2f92aa`. Both companion lint runs pass;
all 2,624 owned declarations pass transitive standard-axiom auditing.
The isolation audit passes after the pin update. The existing endpoint acceptance
proof and controls build against the new computation without binary API changes.

## Executable symbolic ratio selection and pivot exchange

`Math.FiniteLexicographicCompare` gives a computable coefficient scan with a
proof of agreement with Mathlib's lexicographic relation.
`IntegerRatioSelection` compares eligible rows by integer cross-products,
excluding zero and negative directions. A selected row satisfies the existing
rational `IsLeavingRow`; `none` exactly characterizes the absence of a positive
direction. Ordinary and exact ties have distinct controls.

Signed Cramer numerators and `IntegerDictionaryComputation` materialize the
canonical symbolic coefficients and entering direction over one positive
determinant scale. Canceling this scale proves the computed scan correct for
the original rational dictionary. Each signed magnitude field fits
`d*(d+h)+1` bits, and comparison cross-products fit twice that width.

`Finite.BimatrixComputedPivot` computes both the leaving row and the actual
exchange. Nonempty positive-payoff games obtain precisely the canonical
mathematical pivot. A fully degenerate rectangular source selects the last
eligible row using a perturbation coefficient; its computed forward and reverse
exchanges restore the port data. The library contains formal controls; compiled
evaluation lives in ignored scratch, as required by the architecture audit.

At this historical checkpoint, these operations used integers and explicit finite scans. Rational inverses and
noncomputable function orders occur only in proofs. Actual FP/FPn certificates
for the binary matrix loops, scans, exchange and graph codecs remain before the
Nash PPAD reduction.

Validation: full base/lint build, 4,506 jobs; lint and architecture/isolation
audits pass. All 92 declarations in the scan/dictionary/pivot and changed signed
computation/control scope pass transitive standard-axiom auditing. Independent
semantic review passes. The compiled round-trip control runs with
`lake env lean .codex/scratch/BimatrixCompiledRoundtrip.lean`.

The full companion/lint/axiom and computed-pivot consumer build passes 4,268 jobs
in both local and published-base configurations, using pin
`9c0a2c223ec8eab2591c6c5ce6f509f7cccabae9`. Both companion lint runs pass;
all 2,624 owned extension declarations pass transitive standard-axiom auditing.
The isolation audit, 19 optional-boundary regressions and the architecture
regression fixture pass. Released-pin CI includes the new pivot consumer.

## Signed binary arithmetic machines

The optional generic leaves `Backend.BinaryWordSubtraction`,
`BinarySignedArithmetic`, `BinarySignedAddition` and
`BinarySignedCrossComparison` have native `ComputableInPolyTime` certificates.
Subtraction scans the longer operand with one borrow bit and saturates on
underflow. Signed words use a sign header followed by an arbitrary little-endian
magnitude. Addition compares magnitudes for opposite signs; multiplication
combines magnitude multiplication and exclusive-or signs. Negation flips the
header, and comparison treats negative zero as zero.

Exact decoding and linear output bounds hold without a canonical-padding
assumption, including empty and sign-only words. Four-field cross comparison
computes `x*dy < y*dx`; positive decoded denominators give exact rational ratio
order. These modules depend on generic word machinery and Mathlib, not game
semantics. The existing Nash certificate codec and relation are unchanged, and
base clients continue to need no ComplexityLib dependency.

Full companion/lint/axiom and pivot-consumer builds pass 4,273 jobs in both local
and published-base configurations at `9c0a2c22`; the audit checks 2,732 owned
declarations. Companion lint in both configurations, architecture/isolation audits,
19 optional-boundary regressions and the architecture fixture pass. Kernel controls and independent
review cover sign, padding, borrow, cancellation and ratio orientation.

Native packed-table traversal and minimum-row selection are supplied by
`binarySignedTable_polyTime` and `binarySignedRowSelect_polyTime`. The node,
pivot and every-answer Nash reduction clients are delivered below.

## Packed binary lexicographic ratio comparison

`Backend.BinaryIndexedLexicographic` implements a uniform indexed scan with a
two-bit state: prefix equality and strict order. Native composition and a
charged finite traversal give `ComputableInPolyTime` certificates. Exact
correctness detects a strict coordinate with every earlier coordinate equal.
The clock uses its length, with no numeric-value loop or requirement that its
bits are true.

`BinarySignedRowComparison` takes six words: coefficient-count ruler,
field-width ruler, two packed signed rows and their signed denominators. Field
extraction uses certified length multiplication, dropping and taking; scalar
comparison reuses signed cross-products. `binarySignedRowLT_compare` proves
exact agreement with the existing `IntegerRatioSelection.compare` on the
decoded data. Positive denominators give strict rational lexicographic order.
Zero-width and missing fields decode as zero; padding and negative zero keep
the signed arithmetic semantics. These are computation primitives, without a
claim that a packed word is a valid path node or feasible dictionary.

Full companion/lint/axiom and pivot-consumer builds pass 4,276 jobs against local
and published base `9c0a2c22`; the transitive audit checks 2,777 declarations.
Both companion lint runs, architecture/isolation checks, 19 optional-boundary
regressions and the architecture fixture pass. Kernel controls cover first
differences, later perturbations, scaled signed ties and malformed field sizes.
Independent semantic review passes. The generic scan is game-free; only the
row correctness bridge imports the existing generic mathematical comparator.

These primitives now feed the complete Nash reduction described below.

## Exact bimatrix Nash PPAD membership

Import `GameTheoryComplexity.BimatrixNash` and use
`bimatrixNashRelation_mem_PPAD`. It classifies the existing
`generalBimatrixRelation`: independently signed, rectangular integer payoff
matrices with binary magnitudes and unary dimension/field-width headers. Valid
answers decode to ordinary mixed Nash equilibria of the original payoff tables;
malformed instances retain precisely the empty answer. There is no
nondegeneracy assumption.

The reduction reconstructs each queried complementary-path dictionary. Packed
signed arithmetic computes division-free Bird determinants, Cramer
coefficients, entering directions and the full lexicographic minimum ratio.
The independent perturbation coefficients resolve degeneracy without changing
the output game's equilibrium semantics. Fixed-width arithmetic is justified
by bounds on every intermediate product and prefix sum, rather than only on
the final determinant. All loops have native `ComputableInPolyTime` certificates.

The node codec records a sorted basis membership mask and a one-hot entering
variable, relative to the distinguished source. Its arithmetic and syntax
checks accept exactly genuine feasible ports. Invalid words have identity
pointers. Integer determinant and label parity determine orientation;
computing the source score with the same routine calibrates its sign. The
certified pivot and internal switch agree with the existing mathematical
involutions, and the uniform circuit compiler emits their predecessor and
successor circuits in FP.

`Backend.GeneralBimatrixReduction` now proves native
`SearchReducible encBits encBits` to raw End-of-Line. Every target answer, including answers on components disconnected
from the known source, decodes to a complementary non-source basis. The native
polynomial-time answer machine computes that basis's Cramer certificate, normalizes the two
players' masses and undoes the positive payoff shift. It preserves the supplied
endpoint and uses no path enumeration or reachability assumption. On malformed
instances its explicit validity guard emits the designated empty answer.

Generic minimum scans, sorted finite-set ranks, determinant-stage bounds and
oriented-involution witness lemmas remain in dedicated base `Math` modules,
without game or machine-library dependencies. The base codec and path theorems
also require no ComplexityLib. Only the optional companion contains machine
certificates and PPAD classification. Membership does not assert a
polynomial-time equilibrium solver or Nash PPAD-hardness.

Validation: full base build passes 4,515 jobs; companion library/lint/axiom
scope passes 4,332 jobs. Both linters pass. The companion audit checks all 3,779
owned declarations, and the base slice audit checks 209 declarations, using only
standard axioms. Isolation, 19 optional-boundary regressions and the architecture
fixture pass. The full companion/lint/axiom scope and lint also pass against
published base pin `83c8e503`, auditing the same 3,779 declarations.
