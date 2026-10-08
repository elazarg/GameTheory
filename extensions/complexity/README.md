# GameTheoryComplexity

This separate Lake package connects selected ComplexityLib machine definitions
to GameTheory probability and sample-test semantics. The base GameTheory package
does not depend on this package, ComplexityLib, or CSLib. Clients needing only
ordinary game theory do not resolve or download these dependencies.

The first integration provides finite fair-coin random tapes, their exact
counting interpretation, canonically encoded Boolean sample tests with certified
polynomial input length and machine execution, and equivalence
between the two libraries' negligibility predicates. It does not establish
efficient sampling of arbitrary real-valued utilities, efficient game deviations,
cryptographic primitives, or complexity bounds for arbitrary Lean definitions.
The canonical serializer also has a deterministic polynomial-time machine
certificate, with exact output correctness and tuple decoding included in the
cost. Its encoded input length and runtime are polynomial in the unary security
parameter. A composed probabilistic machine implements serialization plus
testing with exactly the same verdict law, one fixed machine, and a polynomial
clock independent of the samples. FP preprocessing is certified rather than
inferred from output length. A user-supplied encoder is never
classified as efficient merely because its result has polynomial length.

The payoff-constrained Nash slice certifies SAT reduction to explicit symmetric
integer payoff tables and proves NP-completeness of mixed Nash existence with both
payoffs at least one. The writer has an actual fixed polynomial-time machine
certificate and exact agreement with the table decoder. Base game semantics,
the satisfiability characterization and serialization remain dependency-free.
Membership uses bounded rational witnesses and a polynomial-time binary verifier
for the same total decoder and canonical Nash predicate. Import
`GameTheoryComplexity.Backend.NashNPComplete` for the headline theorem,
`Backend.NashNP` for membership alone, or `Backend.SATReduction` for hardness
alone. PPAD/FIXP search results remain separate work.

Import `GameTheoryComplexity.Backend.EndOfLineVerifier` for a total circuit-encoded
End-of-Line
endpoint relation in TFNP and its actual polynomial-time verifier.
`Backend.SearchReduction` provides certified instance maps and decoders preserving
every target solution. The generic finite endpoint theorem lives independently in
the base `GameTheory.Math.EndOfLine` module. This slice uses mutually consistent
edges. Import `GameTheoryComplexity.PPAD` for the standard asymmetric raw
End-of-Line relation, PPAD membership and closure, and a certified reduction
showing consistent-edge endpoint search is PPAD-complete. Raw End-of-Line is complete
by definition of the class. Uniformly generated normalized circuit instances
give the reverse reduction with an actual FP instance map and every-answer decoder;
Nash PPAD-completeness remains separate work.

`Backend.CircuitPrefixCompiler` provides an actual polynomial-time serialized
prefix restriction component. It preserves exact optional evaluation on all
source codes at positive live width, rejects malformed syntax and guards empty
outputs. `Backend.UniformCircuitSpecialization` joins this compiler to actual
uniform generation; `Backend.CircuitVectorEmission` serializes the output coordinates
in polynomial time. `Backend.EndOfLineCircuitGeneration` specializes normalized
pointer computations and preserves the invalid-source fallback.

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
including malformed and background inputs. Wire coloring, canonical
boundary/source translation and Sperner hardness remain open.

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
`a58d028f7fe4161782169c7f8c32dd793426b29c`; it does not assume a sibling checkout.
All packages must share Lean/Mathlib 4.34.1. ComplexityLib is pinned to the public
fork `elazarg/complexitylib@c5f2acf1a35d5b00db04cd1bd337a8ce57d66a40`, and CSLib to
`94ea80f41a5678fce997a004f0d8d12dbe47cc4b`. Their declared upstream toolchains are
newer, so compatibility claims cover only the dependency closure of this
extension's selected imports. They do not cover upstream umbrella modules,
unrelated theorem families, or CSLib interoperability.
The fork adds only a two-line Cook–Levin proof repair to upstream
`257ad90ec5f547894cc20f27bd828839b1bf7bbf`; definitions and theorem statements
are unchanged. See EXP-159 in the repository's experiment log.

Import modules use the disjoint prefix `GameTheoryComplexity` because the base
package owns every `GameTheory.*` module through its default Lake globs.
Declarations keep the public namespace `GameTheory.Complexity`. Ordinary clients
use the small `SampleTest` facade; machine-specific builders live under
`GameTheoryComplexity.Backend.Complexitylib`, and the negligibility equivalence
under `GameTheoryComplexity.Backend.Negligible`. The serializer machine
certificate lives in `GameTheoryComplexity.Backend.Serializer`. Composition and
its canonical sample-test specialization live in `Backend.Composition` and
`Backend.CompiledSampleTest`, respectively. This separates backend details
without introducing a general machine-interface framework. Swapping a backend
still requires proofs that its implementation satisfies the facade contract.

## Work in this repository

Run these commands from `extensions/complexity`. Quote the configuration option
in PowerShell so `../..` is passed to Lake intact:

```text
lake -R '-KgameTheoryPath=../..' update
lake '-KgameTheoryPath=../..' env lean --version
lake '-KgameTheoryPath=../..' exe cache get
lake '-KgameTheoryPath=../..' build
lake '-KgameTheoryPath=../..' build GameTheoryComplexity.LintAll
lake '-KgameTheoryPath=../..' lint
lake '-KgameTheoryPath=../..' build GameTheoryComplexity.AxiomAudit
../../scripts/complexity-audit.ps1
```

The extension's generated manifest is ignored because local development replaces
the released base pin with a path. Run `lake -R update` after switching between
local and released modes. Source dependencies remain explicitly pinned; never
edit either package's manifest by hand.

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
FP certificates for codec fields, exact acceptance and fixed-width arithmetic.
Import `Backend.SpernerPointerMachine` for the composed pointer, its actual
uniform FP certificate, source promises and endpoint decoding. Import `GameTheoryComplexity.Sperner` for succinct Sperner PPAD membership,
TFNP totality and the independently verified trichromatic-triangle relation.
`Backend.SpernerReduction` supplies actual FP circuit-instance emission and
FPn every-answer decoding. Sperner hardness remains a separate obligation.
