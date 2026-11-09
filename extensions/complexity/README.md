# GameTheoryComplexity

This separate Lake package connects the CSLib-based ComplexityLib's certified
computation APIs to GameTheory probability and sample-test semantics. The base
GameTheory package does not depend on this package, ComplexityLib, or CSLib.
Clients needing only ordinary game theory do not resolve or download these
dependencies.

The random-sample integration uses native `Cslib.Probability.IsPPTOn`
certificates for programs `List Bool → Cslib.ProbComp Bool`. Each certificate
identifies the full program law with one finite fair-coin machine and a strict
polynomial clock in encoded input length. `booleanProgramTest program degree`
runs the program on the canonical unary parameter, delimiter and Boolean
samples. The public `booleanMachineTests` class requires the native certificate
and retains GameTheory's existing sample-test and indistinguishability
semantics.

`exists_program_randomTapeLaw` gives one deterministic polynomial-time
saved-coin evaluator with exactly the program's PMF law on a uniformly drawn
finite tape. This recovers the finite counting interpretation and rules out
exact acceptance probability `1/3` for every certified Boolean program.
The serializer's `ComputableInPolyTime` certificate charges native framed-pair
decoding and the complete output. A canonical pair at parameter `κ` and sample
degree `s` has encoded length `2*κ + 1 + (κ+1)^s`, bounded by
`4*(κ+1)^(s+1)`, including parameter zero.

Native preprocessing closure composes serialization and testing. The native
halting compiler produces one finite machine whose complete encoded verdict law
agrees exactly with the sample test and whose parameter-polynomial clock is
independent of the observed samples. The same machine has one raw-word polynomial
clock and halts on every raw input, including malformed outer encodings; the
program-law guarantee applies to encoded pairs. The negligible-advantage bridge
applies the native nonnegative predicate to `fun κ => ‖advantage κ‖₊`, preserving the
canonical two-sided real predicate.

Arbitrary real-valued utility samplers, game deviations and cryptographic
primitives still need their own efficient encodings and implementation
certificates. A bound on an encoder's output length does not certify its runtime.

The payoff-constrained Nash slice certifies SAT reduction to explicit symmetric
integer payoff tables and proves native `NPComplete encBits` for mixed Nash
existence with both payoffs at least one. The writer has an actual fixed polynomial-time machine
certificate and exact agreement with the table decoder. Base game semantics,
the satisfiability characterization and serialization remain dependency-free.
Membership uses bounded rational witnesses and a native typed Boolean verifier
with exact correctness for the same total decoder and canonical Nash predicate. Import
`GameTheoryComplexity.Backend.NashNPComplete` for the headline theorem,
`Backend.NashNP` for membership alone, or `Backend.SATReduction` for hardness
alone. General Nash search and fixed-point results use separate relations and
imports described below; FIXP results remain separate work.

Import `GameTheoryComplexity.BimatrixNash` for general rectangular games with
two independently signed integer payoff matrices. The binary certificate
verifier has an actual polynomial-time machine and proves FNP membership.
Unary dimension and coefficient-width headers bound the scans; payoff and
certificate magnitudes are binary. Accepted certificates give ordinary PMF
mixed Nash equilibria, and equilibrium existence is equivalent to existence
of an exactly serialized bounded certificate. Malformed instances accept only the empty
answer, and malformed outer pairs are rejected. Bit-recursive multiplication
and canonical paired-verifier composition are separate game-free modules.
Serialized totality, TFNP and general Nash PPAD membership are proved through
finite complementary paths and actual polynomial-time pointer and answer
machines. Analytic existence remains confined to the base `Analysis` root.

Import `GameTheoryComplexity.Backend.EndOfLineVerifier` for the total
circuit-encoded endpoint relation and its native Boolean verifier. The generic
finite endpoint theorem lives in the dependency-free base mathematics.
`Cslib.Complexity.SearchReducible` supplies efficient instance maps and decoders
that preserve every target answer; source FNP verification remains independent.

Import `GameTheoryComplexity.PPAD` for native `PPAD encBits` membership and
`SearchComplete @PPAD encBits` theorems for both concrete endpoint and asymmetric
raw End-of-Line. Completeness covers arbitrary encoded instance types. Raw
End-of-Line is proved complete for the upstream class. Broken initial links,
source masking, disconnected inconsistent pointers and invalid-source fallbacks
have explicit semantic proofs.

`Backend.NativeCircuitFamilies` specializes native uniform circuit generation.
`Backend.CircuitCompiler` certifies concrete scalar serialization and exact
optional evaluation; `Backend.CircuitVectorEmission` emits uniformly efficient
word-valued circuit vectors, including width zero. `Backend.PointerCircuitGeneration`
realizes any efficient width-preserving pointer pair on its prescribed cube.
`Backend.EndOfLineCircuitGeneration` realizes native active-edge filtering, and
`Backend.NativeEndOfLineReduction` decodes every raw or endpoint answer back to
the native family.

`Backend.GridRoutingWords` encodes the endpoint-preserving planar routed graph
using two coordinate fields, totaling `4*b+6` bits for `2^b` original vertices.
Reciprocal pointers, known sources and every-endpoint recovery are proved;
malformed words remain isolated. `Backend.GridRoutingCodecMachine` certifies
acceptance and field extraction in FP, and `Backend.GridRoutingDivision` supplies
actual bitwise FP division by 3 and 6 and remainder modulo 3.
`Backend.GridRoutingEndpointMachine` gives a uniform FP decoder returning the
canonical original vertex label.
`Backend.GridRoutingGeometryMachine`, `GridRoutingGuards`, `GridRoutingQueries`,
`GridRoutingCrossingMachine` and `GridRoutingWireMachine` supply certified local
components for that pointer: exact route geometry, rectangle rejection,
guarded seeded original queries, proper-crossing validation and both individual
wire steps. Oversized candidate labels retain their value and remain isolated.
`Backend.GridRoutingDecoderMachine` certifies the six-candidate mathematical
decoder, using an explicit found flag to distinguish failure from vertex zero.
`Backend.GridRoutingNodeStepMachine` certifies guarded vertex/interior steps.
`Backend.GridRoutingPointerMachine` composes these with crossing switches and
coordinate encoding into complete uniform FP predecessor/successor machines.
Their agreement with the mathematical word pointers holds on every input word,
including malformed and background inputs.

Import `GameTheoryComplexity.Sperner` for native
`SearchComplete @Cslib.Complexity.PPAD encBits` of the canonical succinct
square-grid relation. Its independent FNP verifier and both every-answer
reductions use native polynomial-time certificates. The reverse map compiles
exact routed color queries; binary division recovers every non-source endpoint,
including components disconnected from the known source. Invalid source
promises retain their prescribed empty answer.

## Use as a dependency

In a downstream `lakefile.lean`, select a published commit containing this
extension (the placeholder below must be replaced with that commit):

```lean
require GameTheoryComplexity from git
  "https://github.com/elazarg/GameTheory" @ "<extension-commit>" / "extensions/complexity"
```

Import only the modules needed by the client:

```lean
import GameTheoryComplexity.SampleTest
-- The umbrella contains the random-sample integration surface.
-- Import this leaf separately for payoff-constrained Nash NP-completeness:
import GameTheoryComplexity.Backend.NashNPComplete
```

The default dependency configuration fetches the base GameTheory commit
`c7cd6bed7498b9a16edb22262e9522ceff90648c`; it does not assume a sibling checkout.
The migration selects CSLib-based Complexitylib v0.2.0 at
`cslib-community/complexitylib@054834a4a4e6ac3ec50ed770bacea7fc42eccc7d`
and CSLib `254e30e6d4299c51323aaeaf5f51a4763b375d4a`. Tracked toolchains stay
on stable Lean/Mathlib 4.35 until final 4.36 is published; the larger native
probability closure needs that shared upgrade. Matching upstream-toolchain
snapshots validate the port meanwhile. Full companion and released-base
consumer validation remain open. Native computation, sampling, concrete
End-of-Line, Sperner and Brouwer classification, and payoff-language NP-completeness
have compiled evidence; the general Nash and circuit-to-game ports remain in progress.

Validation covers the dependency closure of selected imports. Third-party
diagnostics are allowed; first-party diagnostics and transitive nonstandard
axioms remain audit failures. The original integration is recorded in EXP-159;
the native computation decision and validation are recorded in EXP-172/D77.

Import modules use the disjoint prefix `GameTheoryComplexity` because the base
package owns every `GameTheory.*` module through its default Lake globs.
Declarations keep the public namespace `GameTheory.Complexity`. Ordinary clients
use the small `SampleTest` facade. Backend clients supply a native program and
its certificate through `GameTheoryComplexity.Backend.Complexitylib`:

```lean
open Cslib Cslib.Probability Turing.MultiTapeTM
open GameTheory.Complexity.Backend

example (program : List Bool → ProbComp Bool)
    (efficient : IsPPTOn encBits encBool program) (degree : ℕ) :
    booleanProgramTest program degree ∈ GameTheory.Complexity.booleanMachineTests :=
  ⟨program, efficient, degree, rfl⟩
```

The canonical framed-pair serializer and its deterministic certificate live in
`Backend.Serializer`. `Backend.CompiledSampleTest` specializes native
preprocessing closure and intrinsic halting to the canonical sample input.
`Backend.Negligible` relates the native nonnegative norm bound to signed
GameTheory advantages. These modules use the native computation APIs directly;
they introduce no general machine-interface framework or backend registry.

## Work in this repository

Run these commands from `extensions/complexity`. Quote the configuration option
in PowerShell so `../..` is passed to Lake intact:

```text
lake -R '-KgameTheoryPath=../..' update
lake '-KgameTheoryPath=../..' env lean --version
lake '-KgameTheoryPath=../..' exe cache get
python ../../scripts/audit.py --complexity
```

The extension's generated manifest is ignored because local development replaces
the released base pin with a path. Run `lake -R update` after switching between
local and released modes. Source dependencies remain explicitly pinned; never
edit either package's manifest by hand.

The audit rejects warnings and info in every extension module's stored build
diagnostics, including cached results. Dependency warnings also fail; upstream
proof suggestions are allowed. CI runs the same audit against both the local
checkout and the released base pin.

The extension has its own CI workflow. Its default build targets only its own
library and fixtures, together with their imported dependencies. It never builds
the broad ComplexityLib umbrella target. The boundary audit checks that base
modules cannot import the optional surface and that resolved Mathlib revisions
are identical. The axiom audit checks every extension declaration's transitive
axioms, rejecting placeholders and all axioms except `propext`,
`Classical.choice`, and `Quot.sound`.


Import `GameTheoryComplexity.Backend.SpernerGridWords` for binary encoding of
the local Sperner graph, source promises and every-endpoint decoding. Import
`Backend.SpernerGridCodecMachine` and `Backend.SpernerBinarySteps` for actual
native `ComputableInPolyTime` certificates for codec fields, exact acceptance
and fixed-width arithmetic.
Import `Backend.SpernerPointerMachine` for the composed pointer, its actual
uniform native certificate, source promises and endpoint decoding. Import
`GameTheoryComplexity.Sperner` for succinct Sperner PPAD-completeness, TFNP
totality and the independently verified trichromatic-triangle relation.
`Backend.SpernerReduction` and `Backend.EndOfLineSpernerReduction` supply both
native polynomial-time circuit-instance maps and every-answer decoders.

`Backend.SpernerCoordinateColor` supplies two native generators for checked raw
coordinate-color circuits. `Backend.BimatrixCoordinateColor` uses their bounded
output wires in the relocated game program. `Backend.BimatrixProgramEmission`
certifies source/output/action queries jointly and preserves the original suffix
rulers, including their bits.

Import `GameTheoryComplexity.Brouwer` for continuous approximate fixed-point
search PPAD-completeness. A serialized color circuit specifies a piecewise
affine continuous self-map of the real unit square. With grid side `n = 2^b`,
an answer is any bounded point `(X/(6n), Y/(6n))` whose actual coordinate
residuals are at most `1/(6n)`; answers need not be triangle barycenters.
`Backend.BrouwerVerifier` provides native `FNP encBits` membership and a typed
Boolean polynomial-time verifier. `Backend.BrouwerReduction` supplies both native
`SearchReducible` proofs to and from succinct Sperner, preserving every target
answer. The public classifier has type `SearchComplete @PPAD encBits`. The map continuity, square
preservation and exact rational residual semantics are base mathematics and
require no ComplexityLib. The theorem concerns this circuit-induced map
family and output precision, rather than arbitrary continuous-map encodings,
distance to an exact fixed point or FIXP.

The native circuit-to-game foundations are `Backend.BrouwerNashProgram`,
`Backend.BrouwerNashRewardMachine`, `Backend.BrouwerNashHeaders` and
`Backend.BrouwerNashCoefficientQuery`. They preserve checked native gate tuples,
exact source/code/header bytes, reward bounds and affine coefficient semantics.
The remaining coefficient/kind queries and aggregate reduction are still being ported.

The native general verifier and totality leaves are
`Backend.GeneralBimatrixFNP` and `Backend.GeneralBimatrixTotality`. They prove
`FNP encBits` and `TFNP encBits` for the canonical signed rectangular relation
using the actual typed Boolean verifier and finite complementary-path existence.
The node/pointer and full public Nash classifier port remains in progress.

Import `GameTheoryComplexity.BimatrixNash` for exact signed rectangular Nash
search PPAD-completeness (`bimatrixNashRelation_PPADComplete`). The existing binary relation
has an actual FP instance map to End-of-Line and an FPn decoder preserving
every target answer. Full lexicographic perturbations handle degenerate games;
malformed inputs retain the empty answer. The decoder computes the supplied
endpoint's certificate and undoes payoff shifts. Hardness uses an actual FP
Brouwer-to-game instance map and FPn decoder. The canonical sampled program's
coefficient/kind machines agree at every output, and its emitted reward proves
that every accepted Nash certificate yields an accepted Brouwer answer.
`bimatrixNashRelation_PPADHard` and the existing membership theorem classify the
same binary relation. Ordinary base clients continue to require no ComplexityLib.
