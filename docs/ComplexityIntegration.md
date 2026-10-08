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

PPAD search completeness is separate from this decision theorem. The selected
upstream provides FNP and TFNP; the following slice supplies the missing
End-of-Line totality and solution-preserving search-reduction interface.

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

`Backend.SearchReduction` contains only an FP instance map, an FPn decoder taking
the original instance and target solution, and preservation of **every** valid
target solution. Identity and composition have genuine machine certificates.
Composition gives each decoder its own instance. A reduction transports totality
backward, but TFNP membership also requires independent FNP membership of the
source: its other accepted witnesses need not be bounded or efficiently checked.

This establishes the filtered-edge search foundation. The next section supplies
the standard raw convention and PPAD class. Uniform normalization then connects
the encodings. Brouwer/Sperner reductions, Nash search completeness and
approximation conventions remain further obligations.

The base build passes 4,366 jobs and the full companion build 3,827 jobs. All
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

PPAD membership consists of independent source FNP evidence and a certified
search reduction to this raw relation. This gives containment in TFNP and
closure under reductions with source FNP supplied. Raw End-of-Line is complete
by definition of the class; this is the reference problem, not a Nash
completeness theorem.

The certified raw-to-endpoint reduction keeps the instance and decodes every
filtered-edge solution. With a genuine source it keeps the endpoint. When only
the initial link is broken it maps the target fallback to the origin; invalid
weak promises retain the empty fallback. Its instance map is FP and its
original-instance decoder is FPn. Thus filtered-edge search is PPAD-hard.

Generic normalization replaces inconsistent pointers by self-loops, preserving
edges and endpoints. Its pointer-word evaluators are FP-certified. The normalized
circuit-instance compiler described below closes the reverse reduction and
proves filtered endpoint PPAD membership and completeness. EXP-161 and D69
record the original compilation obligation; EXP-163 and D71 discharge it.

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

The semantic word pointer has no composed FP certificate yet. That next
certificate must enforce canonical boundary colors before incrementing corner
coordinates: a boundary corner can equal `2^b`, outside a `b`-bit field.
Uniform circuit-instance generation and an FPn every-answer decoder then
complete the remaining reduction obligations. This slice does not establish
succinct Sperner PPAD membership.


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

`Backend.SpernerPointerMachine.gridPointerMachineUniformFn_mem_FP` composes
these operations into one actual polynomial-time computation. Its certificate
is uniform in the ruler, color-query seed and vertex. In particular,
`spernerPointer_pair_mem_FP` accepts a serialized color circuit vector as part
of its input; it does not assume one fixed coloring. The implementation agrees
with `wordGridPointer` on all words, preserving lengths and rejected-word
isolation. Source promises and every-endpoint trichromaticity therefore hold
for the concrete serialized-circuit pointer itself.

This closes the composed FP pointer obligation. Uniform generation of an
End-of-Line circuit instance and the FPn every-answer word decoder remain
before succinct Sperner PPAD membership. PPAD-hardness of Sperner is a further
separate reduction obligation.


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
of its graph component. The decoder is the actual FPn second projection.
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

This is a proved local routing prerequisite. Global succinct routing, original
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

These are the geometric prerequisites for the global route, with no
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

The modules have no ComplexityLib dependency. The six-candidate bound proves
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
now has actual uniform FP color queries and circuit-instance generation, plus
an FPn every-answer decoder.

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
barycenter, which has zero displacement. Both answer maps have actual FPn
certificates and preserve every target answer. The existing Sperner
PPAD-completeness theorem therefore supplies both directions of classification.

Membership also has an independent verifier. It checks the exact answer length
and numerator bounds, computes the triangle and two local offsets, evaluates
three corner color circuits, and checks the exact weighted residual. The latter
uses a fixed table over seven possible offsets in each coordinate and three
colors at each corner (1,323 cases), independent of the grid size. Binary
arithmetic and circuit evaluation have composed FP certificates, yielding an
actual polynomial-time machine, linear witness balance and FNP membership.
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

Validation commands for the continuous slice (companion Lake commands run
from `extensions/complexity`; the others run from the repository root):

```text
lake build GameTheory GameTheory.LintAll
lake lint
lake env lean .codex/scratch/BrouwerAxiomAudit.lean
lake -KgameTheoryPath=../.. build GameTheoryComplexity GameTheoryComplexity.LintAll GameTheoryComplexity.AxiomAudit
lake -KgameTheoryPath=../.. lint
pwsh -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -File scripts/complexity-audit.ps1
python -m unittest discover -s scripts/tests
```

The base build passes 4,416 jobs; its Brouwer axiom audit checks 119 owned
mathematical declarations. The companion build passes 4,198 jobs and audits
2,351 owned extension declarations transitively. Both linters and both
structural audits pass, as do all 30 boundary regressions. Only `propext`,
`Classical.choice` and `Quot.sound` are admitted by the axiom audits.

Published-pin validation also passes the full 4,198-job companion/lint/axiom
build against base commit `b2a5e0982ce6755197bde4e86ed4a295a37fa30c`.
`lake -R update GameTheory` resolves that git pin and completes the Mathlib
cache hook; `lake env lean --version` confirms Lean 4.34.1. The build then uses
`lake build GameTheoryComplexity GameTheoryComplexity.LintAll
GameTheoryComplexity.AxiomAudit` without a local-path override.

## General rectangular binary Nash certificates

`GameTheoryComplexity.BimatrixNash` supplies FNP membership for exact mixed Nash
certificates of independent signed integer payoff matrices. Unlike the earlier
payoff-constrained symmetric decision language, this relation has no utility
threshold. The input has unary row, column and coefficient-width headers and
two row-major matrices whose entries use positive and negative binary fields.
The answer contains two denominators, two signed utility numerators and both
probability-numerator vectors. For input length `L`, each unsigned field has
width `(2*L+2)*(8*L+6)+1`; the total answer length is cubic in `L`.

The verifier checks exact lengths, positive denominators, simplex equations,
every pure deviation inequality and equality on positive support. Signed
comparisons work directly on positive and negative sums. Generic bit-recursive
multiplication avoids iterating over payoff magnitudes. Cobham composition
certifies the whole paired-input machine, including outer-pair validation.
Malformed game instances accept precisely the empty answer; malformed outer
pairs are rejected. Decoding and verifier correctness are total, including
short words and noncanonical simultaneous positive/negative fields.

Accepted valid answers yield the base's ordinary PMF mixed Nash equilibria.
Conversely, a supplied canonical equilibrium yields an exactly serialized
bounded certificate. The mathematical existence theorem for every nonempty
integer game remains inside `GameTheory.Analysis`; the companion imports no
analytic existence result. Consequently this slice establishes FNP, while
unconditional serialized totality, TFNP and PPAD membership remain the next
reduction. Ordinary game clients acquire no new dependency.

`Backend.BinaryWordMultiplication` and `Backend.PairedVerifier` have no game
imports. The latter is shared with the older constrained Nash verifier, so
canonical pairing has one implementation and correctness proof.

Validation passes the full 4,218-job companion/lint/axiom build against both
the local checkout and published base commit
`e4b2d03957c70e27217d01e35d7076e9ada763be`. The final audit checks 2,615
extension declarations transitively, admitting only `propext`,
`Classical.choice` and `Quot.sound`. Companion lint, architecture and
optional-dependency audits, and all 30 boundary regression tests pass.
`lake -R update GameTheory`, `lake env lean --version` and `lake exe cache get`
confirm the published pin, Lean 4.34.1 and successful cache resolution.

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

This closes the mathematical oriented graph and endpoint proof, including
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
