# Complexity and computational results roadmap

This is the active dependency order after continuous approximate Brouwer
PPAD-completeness. The delivery ledger records compiled results; this document
records targets and acceptance gates. Ordinary game clients must continue to
need neither ComplexityLib nor CSLib.

## Starting point

Delivered: NP-completeness of payoff-constrained symmetric mixed Nash existence;
standard End-of-Line, succinct Sperner and continuous approximate Brouwer
PPAD-completeness; actual FP/FPn reductions and independent polynomial verifiers.
The base has bimatrix support identities, potential-game termination,
multiplicative-weights regret bounds, zero-sum regret-to-Nash transfer and
Gale–Shapley stability.

The earlier machine-certified Nash certificates concern one square payoff
matrix, its transpose, and payoff-one constraints. General rectangular
certificates now have mathematical correctness and bounded-witness completeness;
their serialized machine verifier is now delivered. Real learning and
matching constructions are not automatically executable finite-bit algorithms.

## 1. Generic prerequisites and general bimatrix witnesses

**First slice, delivered.** The dedicated `Math.FiniteLinearBinaryBound` and
`Math.BoundedLinearCertificate` modules extend small rational solutions of
integer linear systems with bounds polynomial in coefficient **bit width**.
The earlier bound polynomial in coefficient magnitude suffices for the
restricted SAT game family but is inadequate for arbitrary binary payoffs.
The new modules have no game or machine imports and are independently portable.

Their first consumer is one canonical rectangular bimatrix certificate with two independent
integer payoff matrices, natural probability numerators, positive denominators
and signed utility numerators, without payoff thresholds. Exact executable
checking is proved sound against ordinary PMF mixed Nash, and every real Nash
witness admits bounded rational certificates. A fixed-support linear system
splits signed payoff variables into two nonnegative coordinates so the generic
rational-witness theorem applies without a payoff-normalization policy.

Controls cover a rectangular asymmetric game, negative payoffs, a mixed
equilibrium, and rejected simplex or best-response certificates. This slice
claims bounded witnesses and exact verification, not polynomial runtime, TFNP
or PPAD membership of serialized general Nash search.

**Serialized verifier slice, delivered.** Explicit two-matrix binary input/output
codecs have a precise malformed-input convention and an independent actual FP
verifier. The proofs establish witness balance, FNP membership and encoding
completeness from a supplied canonical equilibrium. Unary dimensions and coefficient-width
headers bound scan clocks by input length; payoff magnitudes remain binary.
Malformed instances accept precisely the empty answer. Widths depend on input
bit length, not payoff magnitude. Generic bit-recursive multiplication and
canonical paired-verifier machinery live in dedicated game-free companion
modules, with correctness and actual polynomial-time certificates.

Finite complementary paths now give nonempty-game existence without Analysis.
The endpoint decoder and bounded support-system witnesses supply total serialized
answers. The optional companion combines this theorem with its existing actual
polynomial verifier to establish TFNP for the same relation. The actual pointer
machines and reduction completing PPAD membership are described in section 2.

## 2. Bimatrix Nash PPAD membership

**Delivered and validated.** The public optional theorem
`GameTheory.Complexity.bimatrixNashRelation_mem_PPAD` classifies exact Nash
certificate search for independently signed rectangular integer payoff tables.
It combines the existing FNP verifier with an actual FP instance map to standard
raw End-of-Line and an actual FPn answer map. There is no nondegeneracy premise,
assumed polynomial-time pivot operation, or bound on path length in the theorem.
Full library, lint, axiom and released-pin validation of this final integration
has passed; the delivery ledger records the released consumer pin.

The relation retains its exact existing certificate codec and malformed-input
fallback. Ordinary game clients continue to import the base library without
ComplexityLib or CSLib. Finite-path totality and TFNP remain independently proved
without an Analysis import. Nash PPAD hardness and completeness are the next
separate reduction in section 3.

The mathematical and executable prerequisites below explain the construction.
Earlier validation records describe their individual delivery slices.

**Complementary decoding, delivered.** The game-free
`Math.LinearComplementarity` module defines affine slack and exact nonnegative
complementarity over ordered fields. `Finite.BimatrixComplementarity` specializes
it to the off-diagonal negative payoff blocks with unit constants. Independently
scaled rational coordinates use row numerators divided by `Dx` and column
numerators divided by `Dy`. Every nonzero solution has positive mass in both
blocks; normalizing these masses yields the existing Nash certificate, with row
utility numerator `Dy` and column utility numerator `Dx`. The converse holds for
positive-payoff certificates. No nondegeneracy or nonempty-dimension premise is
hidden in the decoding theorem.

`Finite.BimatrixCertificateShift` proves exact constant-shift invariance and
inverse-shift decoding. If coefficient magnitudes are at most `2^h`, adding
`2^h+1` makes them positive with magnitude strictly below `2^(h+2)`, ready for an `h+2`-bit field.
`BimatrixComplementarityCorrectness` therefore recovers canonical PMF mixed Nash
for the original signed tables from any represented nonzero complementary
solution. Controls include fully tied mixed equilibria, the artificial zero
solution, a rejected single nonzero block, and an independent rational check
with unequal scales `Dx=5`, `Dy=7`.

**Delivered local pivot mathematics:**

Four game-free Math leaves use finite coefficient vectors with Mathlib `Lex`.
`PerturbedDictionary` represents each row by its inverse-basis constant and
independent perturbation coefficients, and proves eligible ratios distinct.
`DictionaryPivot` proves the determinant and inverse-coordinate formulas for
actual basis-column replacement and its reversal. `LexicographicPivot` proves
unique minimum-ratio selection, strict symbolic feasibility of the updated
basis, and selection of the old column on reversal. These are ordered-field
proofs, not an executable rational solver.

`Finite.BimatrixPivotSource` supplies the first game consumer: positive-payoff,
nonempty rectangular games have a unique pivot from the identity slack basis,
with an invertible, strictly feasible successor. A fully degenerate 1×2 control
has entering direction `[0,1,1]`, equal ordinary ratios, and successor constants
`[1,0,1]`; the zero constant row remains symbolically positive. A generic reverse
control has two eligible reverse rows and selects the original leaving row.

**Delivered canonical basis nodes:**

`Math.FiniteBasisExchange` represents a basis by a finite set and uses Mathlib's
increasing enumeration, with a proved permutation relating a sorted exchange
to raw column replacement. `DictionaryReindex` transports inverse coordinates,
perturbation coefficients, feasibility and leaving rows while keeping
perturbation powers attached to the equations. `CanonicalDictionary` therefore
proves feasible canonical exchange and reverse selection after sorting.

`ComplementaryLabels` proves the cardinality dichotomy for binding labels:
exactly one variable of every label, or a missing designated label and exactly
one duplicate. Removing a dropped-label variable or one of a duplicated pair
preserves the remaining coverage. These predicates apply to nonbasic variables.

`Finite.BimatrixBasis` provides basis certificates for cardinality, invertibility
and strict symbolic feasibility, and path-node certificates for coverage except
a fixed dropped label. Exchanges require a nonbasic entering variable and a
valid leaving row; the dropped/duplicated label condition preserves the node
certificate. The all-slack source is canonical and unique by its variable set.
A degenerate rectangular game constructs a certified successor. A separate
control forces sorting to move a column and proves the reverse exchange restores
the original set; a noninvolutive three-cycle checks permutation orientation.

The full base/lint-scope build passes 4,453 jobs. Base lint and both structural
audits pass; all 144 new declarations pass a transitive standard-axiom audit.
Independent review confirms nonbasic exchange direction, permutation orientation,
cardinality and certificate scope. The optional companion is unchanged.

**Delivered exits, reversible ports and rational terminal extraction:**

`Math.NonnegativeDictionary` proves a nonnegative invertible basis has a positive
inverse direction whenever the entering column has a positive coordinate.
`Finite.BimatrixBasisExit` applies this to every slack and payoff variable of a
positive-payoff game with both player dimensions nonzero. Thus every nonbasic
port of every certified basis has a unique symbolic leaving row; secondary rays
of this representation are excluded without a hypothetical bounded solver.

`Finite.BimatrixPivot` chooses that row and defines the opposite port by entering
the old leaving variable in the sorted successor. Pivoting twice restores both
the basis and entering variable; the pivot has no fixed points. This is an
unoriented edge involution. The determinant coloring below supplies oriented
path pointers.

`Math.BasisCoordinates` lifts inverse coordinates to the full variable universe,
sets nonbasic coordinates to zero, proves the ambient equations and derives
nonnegative constant coordinates from symbolic feasibility.
`Finite.BimatrixBasisSolution` extracts a rational complementary solution from
any complementary basis and proves its payoff point is zero exactly at the
all-slack source. The terminal control includes a degenerate 1×2 basis with
constant coordinates `[1,0,1]`: a basic slack has zero constant and a strictly
positive symbolic coefficient vector. Controls also cover nonpositive entering
columns, negative basis entries, a nonbasic variable ignored by coordinate
lifting, the exact source pivot, and reversal of the full port.

Validation: full base/lint-scope build, 4,463 jobs; lint and both structural
audits pass. All 119 declarations in the updated proof scope pass transitive
standard-axiom auditing. Independent review confirms sorted reverse-row choice,
uniqueness-based selection and the explicitly unoriented scope of the port pivot.

**Delivered oriented End-of-Line paths:**

`Math.ComplementaryPorts` classifies the permitted nonbasic entering variables:
a complementary node has one port at the dropped label, and an internal node
has two at its unique duplicate. Switching pairs the internal ports and fixes
exactly the complementary terminals; pivot exchange preserves port validity.
`Finite.BimatrixPath` specializes these invariants, proves the restricted pivot
involution and a unique artificial source port, and gives a finite carrier by
injecting ports into their finite variable set and entering label.

`Math.FacetOrientation` proves that signed maximal minors form a kernel vector.
It derives an exact canonical facet identity: the opposite pivot facet is the
original facet times the negative pivot direction. `ComplementaryPortOrder`
proves twin inserted variables have the same canonical index, while the parity
of payoff variables outside the dropped label reverses. These two facts give
`Finite.BimatrixPathOrientation` a nonzero rational score that reverses across
both types of internal edges. Calibration against the source score makes the
source's direction bit true without an assumed coloring.

`Math.OrientedInvolutionPath` builds actual successor/predecessor functions
from the two colored involutions and proves their inverse laws and exact
endpoint characterization using the existing End-of-Line owner. The generic
control includes an unrelated cycle beside a source-to-sink path.
`Finite.BimatrixPathEndOfLine` instantiates these pointers with the determinant
color. Endpoints are exactly complementary bases; the source has a consistent
nontrivial outgoing edge and no incoming edge. Every other endpoint supplies a
nonzero rational complementary solution. Finiteness therefore yields such a
solution for every positive-payoff integer bimatrix game with both dimensions
nonzero, with no analytic existence import.

These modules provide mathematical pointer and endpoint proofs, including ray
exclusion and degenerate games. Their pointers are noncomputable definitions.
The binary machines below implement exactly these pointers and certify the
serialized complexity classification independently of the mathematical graph.

Validation: the full base/lint-scope build passes 4,477 jobs; lint and both
structural audits pass. All 184 declarations in the new path scope pass the
transitive standard-axiom audit. Seven control modules cover port classification,
canonical facet signs, source uniqueness, degenerate terminals and unrelated
cycles. Independent semantic review confirms the orientation and endpoint proof.

**Delivered endpoint encoding:** `Math.FiniteRationalEncoding` computes a positive
product denominator and natural numerators for any finite nonnegative rational
vector, proves exact decoding, and bounds the fields from reduced-fraction bounds.
For `k` coordinates with numerator magnitudes and denominators at most `2^h`,
the common denominator is at most `2^(h*k)` and numerators at most `2^(h*(k+1))`.
Empty vectors and zero coordinates are covered; negative coordinates deliberately
require a different signed representation. This module imports only Mathlib.

`Finite.BimatrixPathCertificate` clears every coordinate of a supplied endpoint
and undoes independent payoff shifts, preserving that endpoint's normalized
equilibrium. Finite-path existence now gives exact certificates for arbitrary
signed nonempty integer games. The existing support-system bound then supplies
polynomial-width certificates without analytic existence. This last certificate
may use a different rational witness; it does not establish a bound on each
original path node or endpoint. A degenerate signed rectangular control retains
unequal column weights and negative utility numerators.

Validation: full base/lint-scope build, 4,481 jobs; lint and architecture audit
pass. All 29 new encoding/certificate/control declarations pass transitive
standard-axiom auditing. The generic rational encoding uses only Mathlib; the
generic signed-minor, complementary-port and involution graph lemmas likewise
remain separate from the game-specific instantiation for future upstreaming.

The companion integration is delivered in `Backend.GeneralBimatrixTotality`:
every binary input has an accepted answer, and the unchanged machine-certified
verifier gives TFNP membership. Signed rectangular and malformed controls pass.
The full companion/lint/axiom build passes 4,248 jobs in both local and published
base-pin configurations (`7f6fe653`); optional lint passes and all 2,620 owned
extension declarations pass transitive standard-axiom auditing. Architecture and
isolation audits and all 19 optional-boundary tests plus the architecture
regression fixture pass. The class result is public in `BimatrixNash`.

**Delivered basis and endpoint bit bounds:** `Math.IntegerDeterminantBound`
owns the existing permutation-expansion estimate, extracted unchanged from
`SmallRationalWitness`. `RationalQuotientBounds` shows fraction reduction cannot
increase either field of a nonzero-denominator integer quotient.
`IntegerBasisBounds` proves Cramer's identity and bounds determinants, inverse
entries and inverse-system solutions by width `d*(d+h)+1`, for dimension `d`
and entry/right-hand-side magnitudes at most `2^h`. These are Mathlib-only leaves.

`Finite.BimatrixBasisBounds` proves the same reduced-fraction bounds for every
certified basis's ambient coordinates, symbolic dictionary coefficients and
entering directions. No path-length or positive-payoff assumption is needed.
Its integer representation is obtained from the existing rational columns and
proved exactly equal after coercion, rather than introducing another column
semantics. `BimatrixEndpointBounds` bounds the directly decoded, unshifted
certificate, retaining the supplied endpoint. Given coordinate width `W` and
shift magnitudes at most `2^s`, its fields fit width
`W*(m+n+1)+(m+n)+s+2`. This closes polynomial coordinate and direct endpoint
size; it does not prove polynomial-time arithmetic or graph encoding.

The arbitrary-vector product-denominator bound can exceed the existing serialized
field width. The basis-specific shared-denominator decoder below resolves that
size gap. Bounds on determinants do not make the permutation-expansion computation
polynomial-time: certified efficient integer linear algebra is also required.

Validation: full base/lint-scope build, 4,490 jobs; lint and both structural
audits pass. All 58 declarations in the new bound/control scope pass transitive
standard-axiom auditing; independent semantic review passes. The optional
companion is unchanged.

**Delivered shared Cramer certificates:** `Math.IntegerCramerEncoding` uses
the absolute integer basis determinant as one positive denominator. Multiplying
each Cramer numerator by the determinant sign and taking its natural value
recovers every nonnegative solution coordinate exactly. Denominator and numerator
fields retain width `d*(d+h)+1`; no product of reduced coordinate denominators is
needed. Signed determinant, singular/empty and nonnegativity controls compile.

`Finite.BimatrixCramerCertificate` lifts these weights to the existing variable
universe, preserving the full supplied basis point. Complementary non-source
bases yield valid normalized certificates after independent payoff unshifting.
The compact fields fit the existing `bimatrixCertificateWidth m n h`, even after
the positive shift `2^h+1`. This bound applies to every supplied endpoint and
does not select a different equilibrium. `BimatrixComplementaryCertificateBounds`
owns the shared mass and utility estimate; the arbitrary-vector endpoint bound
now reuses it. A signed one-action terminal has determinant `-24`, common
denominator `24`, weights `6/4` and original utility numerators `-12/-30`.

Validation: full base/lint-scope build, 4,496 jobs; lint and architecture audit
pass. All 73 declarations in the compact-encoding/shared-bound/control scope
pass transitive standard-axiom auditing.

**Delivered binary endpoint emission:** The optional
`Backend.GeneralBimatrixEndpoint` now serializes each supplied
complementary non-source shifted basis with the existing certificate codec.
`generalBimatrixEndpointWord_accept` proves the unchanged binary relation accepts
that exact endpoint's certificate. Signed rectangular and malformed-input
controls compile. This module is the mathematical emission map. The dictionary
and emission machines below discharge its determinant-runtime obligation while
preserving the same supplied endpoint.

Validation: full companion/lint/axiom build, 4,258 jobs in both local and
published-base configurations (`6bb618ca`), auditing 2,624 owned declarations.
Both linters, architecture/isolation audits, 19 optional-boundary regressions
and the architecture regression fixture pass. Independent semantic review passes.

**Delivered materialized determinant computation:**
`Math.TabulatedBirdDeterminant` stores every division-free Bird stage as a
row-major array, avoiding repeated evaluation of earlier function-valued stages.
It reuses Mathlib's determinant correctness theorem. Each stage has `n*n`
stored entries and each entry reads two finite tails of the previous stage;
no Gaussian pivot search or exact division is needed.

`Math.BirdIterationBounds` bounds the existing mathematical recurrence by
`(2*n*B)^t*B` for input magnitude `B`. For `t ≤ n` and `B = 2^h`, every entry
fits width `(n+1)*(h+n+2)+1`. `IntegerCramerComputation` transfers these bounds
to the actual stored arrays and proves computed determinants, scales and
numerators equal the canonical encoding. The existing bimatrix certificate
producer now uses this computation, with its API and decoding contract unchanged.
All three generic modules are independent of game and machine imports.

Controls cover zero leading pivots, signed and singular matrices, dimension
zero, multiple stored stages and a dense six-dimensional matrix. A scratch
evaluation of the dense twenty-dimensional `I+J` matrix returns `21`.
Full base/lint build: 4,500 jobs; lint and architecture/isolation audits pass.
All 92 declarations in the new computation and changed certificate/control scope
pass transitive standard-axiom auditing; independent semantic review passes.

Companion integration: full 4,263-job library/lint/axiom builds against both local
checkout and published base pin `14183a4c`, auditing 2,624 owned declarations.
Both companion lint runs and the isolation audit pass; endpoint acceptance and
its controls compile unchanged against the new determinant computation.

**Delivered executable symbolic ratio selection:**
`Math.FiniteLexicographicCompare` scans coefficients from left to right with the
scalar's computable order, avoiding Mathlib's noncomputable function order.
`IntegerRatioSelection` filters positive directions and compares integer
cross-products. It returns `none` exactly when every direction is nonpositive;
every selected row satisfies the existing rational `IsLeavingRow` predicate.
Exact ties retain the earliest row; symbolic perturbations break ordinary ties.

`IntegerCramerComputation` now exposes signed fields, preserving negative
direction and perturbation coefficients. `IntegerDictionaryComputation`
materializes all coefficients and direction fields over the same positive
determinant denominator. Exact division recovers the canonical dictionary;
canceling that common scale transfers integer selection to its ratio theorem.
Magnitude fields retain width `d*(d+h)+1`, and comparison cross-products fit
twice that width. No new mathematical leaving-row predicate is introduced.

`Finite.BimatrixComputedPivot` computes the leaving row and exchanges the actual
port. For nonempty positive-payoff games, both outputs agree with the canonical
symbolic pivot. Controls cover negative determinants/directions, empty scans,
ineligible rows, late symbolic differences, exact ties and a degenerate `1×2`
source. Its selected row is kernel checked; formal and scratch compiled checks
confirm pivot followed by reverse pivot restores the port data.

Validation: full base/lint build, 4,506 jobs; lint and architecture/isolation
audits pass. All 92 declarations in the scan/dictionary/pivot and changed signed
computation/control scope pass transitive standard-axiom auditing. Independent
semantic review passes. Compiled round-trip validation runs from ignored
`.codex/scratch/BimatrixCompiledRoundtrip.lean`.

Companion integration and the computed-pivot consumer pass 4,268 build jobs
against both the local checkout and published base pin `9c0a2c22`. Both companion
lint runs pass; the transitive audit checks 2,624 owned extension declarations.
The isolation audit, all 19 optional-boundary regressions and the architecture
regression fixture pass. Released-pin CI now builds the pivot control module.

**Delivered signed binary machines:** The optional, game-free
`Backend.BinaryWordSubtraction` implements saturating subtraction with a
bit-length-bounded borrow scan. `BinarySignedArithmetic` supplies sign-header
multiplication, negation and strict comparison; `BinarySignedAddition` supplies
addition and subtraction by comparing magnitudes when signs differ. Every
operation has exact decoding, a linear output-length bound and actual Cobham
and FPn certificates. Arbitrary padding, empty words and negative zero are
accepted. This internal arithmetic representation does not change the Nash codec.

`BinarySignedCrossComparison` composes multiplication and comparison on four
signed fields. With positive decoded denominators, its singleton Boolean output
is equivalent to strict rational ratio order. All four leaves depend only on
generic word machines and Mathlib, making them candidates for upstreaming.

Validation: full companion/lint/axiom and pivot-consumer builds pass 4,273 jobs
against both local and published base configurations (`9c0a2c22`); 2,732 owned
declarations pass the transitive standard-axiom audit. Companion lint in both configurations,
architecture/isolation audits, 19 optional-boundary regressions and the
architecture fixture pass. Kernel controls cover borrow cascades, underflow,
opposite signs, carries, cancellation, padding, negative zero and scaled ratios;
independent semantic and proof review passes.

**Delivered full binary lexicographic comparison:**
`Backend.BinaryIndexedLexicographic` composes any two certified indexed strict
and equality flags into an actual Cobham/FPn scan. A constant two-bit state
records prefix equality and strict order. Its correctness theorem detects the
first strict witness with an equal earlier prefix; arbitrary clock bits work
because producers use the clock's length.

`BinarySignedRowComparison` extracts fixed-width signed fields from two packed
rows and compares their denominator cross-products. Its actual uniform machine
agrees exactly with `Math.IntegerRatioSelection.compare` on all decoded rows.
Positive decoded denominators recover strict rational lexicographic ratio
order. Empty scans, zero-width fields, truncation, padding and negative zero
retain total decoding semantics. The generic scan has no game dependencies;
the row bridge reuses the existing generic mathematical comparator.

Full companion/lint/axiom and pivot-consumer builds pass 4,276 jobs in local and
published-base configurations (`9c0a2c22`), with 2,777 owned declarations audited.
Lint in both configurations, architecture/isolation audits, 19 optional-boundary
regressions and the architecture fixture pass. Kernel controls cover late
perturbations, opposite early/late differences, scaled signed ties, arbitrary
ruler bits and malformed/truncated fields. Independent semantic review passes.

**Implemented canonical binary nodes and generic scan prerequisites:**

`Math.FiniteMinimumScan` certifies finite prefix minimum selection, and
`FiniteSetRank` identifies membership-prefix counts with Mathlib's increasing
finite-set enumeration. They support the existing lexicographic ratio selector
without introducing another leaving-row predicate. The generic leaves remain
independent of game and complexity-machine imports.

`Finite.BimatrixPathBinaryCodec` encodes a port with `4*k` bits, where
`k = m+n`: `2*k` basis-membership bits and `2*k` entering-variable one-hot bits.
A fixed source mask makes the all-slack source word all false. Encoding is
injective; canonical decoding checks length, basis cardinality, the unique
nonbasic entering variable, complementary-label coverage, nonzero determinant,
and strict lexicographic dictionary feasibility. The decoder checks symbolic
coefficients, so a zero constant coordinate in a degenerate game is permitted
only when its perturbation vector is strictly positive. Invalid words are
isolated by identity pointers and cannot become raw End-of-Line witnesses.
The representation stores neither all bases nor an inverse-matrix witness.

`Finite.BimatrixComputedOrientation` evaluates the determinant score and
source calibration using integers and proves equality with the canonical path
color. `Math.OrientedInvolutionPathWitness` proves that raw pointer inconsistency
is exactly a switching terminal away from the calibrated source. In particular,
the outgoing-inconsistency branch cannot falsely identify the source even though
that branch has no explicit origin-exclusion clause. `Finite.BimatrixPathWitness`
then supplies complementary and non-source basis certificates for every witness.
These arguments apply to every graph component, including components unrelated
to the source; internal cycles have no such witnesses.

**Implemented polynomial dictionary, pivot and endpoint machines:**

The companion's generic signed fixed-width arithmetic, sum/table scans,
subset tally/ordinal/parity machines, minimum-row scan and materialized Bird
machines all carry actual Cobham/FPn certificates. `BinaryDictionaryCorrectness`
connects computed determinants, sign-adjusted Cramer coefficients and entering
directions to the existing integer dictionary. Feasibility tests use the same
computed symbolic rows. `BirdIterationBounds.workWidth` covers stored stages,
comparison products and accumulation prefixes; scan clocks count represented
rows, columns and bits, rather than coefficient magnitudes.

`Backend.GeneralBimatrixMatrixWord` assembles the canonically ordered integer
matrix from membership ordinals. Its exact matrix theorem applies to any
cardinality-correct candidate set, including singular or infeasible sets, so
node validation does not assume the property it checks. The dictionary controller
uses this matrix to compute the determinant, all `k*(k+1)` symbolic coefficients,
entering direction and selected leaving row. The node-operation and pointer
machines implement sorted exchange and internal switching, with exact agreement
with the canonical typed pivot and source-calibrated predecessor/successor.
No general-position or ordinary positive-coordinate assumption replaces strict
symbolic feasibility.

`Backend.GeneralBimatrixEndpointMachine` emits the supplied basis's payoff
weights, their row/column masses, and utilities after undoing the positive shift.
`GeneralBimatrixEndpointCapacity` proves the controller's working width suffices
for every intermediate and the existing certificate field width suffices for
its output. Clients supply no additional capacity proofs. The output is exactly
`generalBimatrixEndpointWord` for the same basis; neither a support search nor
selection of a different Nash witness occurs. `GeneralBimatrixPathEndpoint`
therefore proves every non-source raw path witness emits an answer accepted by
the unchanged Nash relation.

**Implemented actual End-of-Line reduction:**

`Backend.PointerCircuitGeneration` uniformly compiles polynomial pointer
machines into serialized circuits. `GeneralBimatrixCircuitMachine` specializes
it to both bimatrix pointers and proves circuit agreement at every vertex of
the explicit node width, including invalid encodings. The all-false vertex is
the canonical source, with a predecessor loop and a consistent nontrivial
successor. The instance mapper itself belongs to FP; circuit existence alone
is not used as a runtime certificate.

`Backend.GeneralBimatrixReduction` supplies the actual FPn answer machine and
`SearchReduction generalBimatrixRelation rawEndOfLineRelation`. Every accepted
End-of-Line answer decodes through the exact word transport to a genuine typed
path witness, then emits that endpoint's certificate. This proof imposes no
reachability-from-source restriction. Invalid Nash instances return exactly
`[]`; invalid vertex encodings are isolated and cannot supply false endpoints.
The public `BimatrixNash` theorem composes this reduction with the existing FNP
verifier to prove unconditional PPAD membership of the original serialized
signed rectangular Nash relation.

Validation scope: the generic/base helpers, dictionary and pointer semantics,
endpoint equality/capacity/acceptance, and final reduction have passed
warning-free narrow builds or standalone combined checks. Controls include tied
ordinary ratios, zero basic constants with positive perturbations, singular
candidate selections, negative determinants and utilities, signed rectangular
games, source rejection, malformed inputs and arbitrary ruler bits. The final
full base build passes 4,515 jobs; companion/lint/axiom scope passes 4,332 jobs.
Both linters, isolation and boundary regressions pass; standard-axiom audits cover
3,779 companion declarations and 209 base-slice declarations. The full companion/lint/axiom scope and lint also pass in published-base mode
at pin `83c8e503`, with the same 3,779-declaration audit.
Membership does not assert a polynomial bound on following the complementary
path or a polynomial-time Nash solver. PPAD hardness remains separate.

## 3. Bimatrix Nash PPAD hardness and completeness

Reduce the classified fixed-point problem to a finite game. Introduce generalized
circuits only if they shorten the actual reduction and have a concrete game
consumer. Fix gate semantics, fan-out and precision before gadget recovery;
verify every-answer soundness, accumulated error and ambiguous comparators.
The current two-dimensional Brouwer family does not automatically classify
another continuous-map language or generalized circuits.

**Paired-action gate slice, delivered.** `Finite.BimatrixBlockGame` proves
that matching payoffs with `H > kD` force every block into support and keep
both players' block masses within `D/H` of `1/k`. Individual actions may have
zero weight. `BimatrixAffineGate` implements exact saturated affine equations
against the actual block capacity; rescaling to unit capacity costs at most
`kD/H`. `BimatrixComparatorGate` selects the upper or lower endpoint for a
strictly positive or negative signal. All statements apply to every accepted
canonical certificate, without selecting an equilibrium or graph component.

The supporting generic Math leaves prove support-to-clamp implications,
matching-mass uniformity, clipped-feedback residual bounds, exact binary cell
extraction with quantitative trajectory errors, four-corner interpolation and
polynomially coarse displacement Lipschitz bounds. Binary extraction handles
the right endpoint as the last cell with residual one. Four-corner formulas
include cell edges and the diagonal and reuse the existing Brouwer map.

Controls validate concrete negative, interior and saturated affine targets,
both comparator signs, nonuniform block masses with zero action weights, and
unsupported blocks when the matching-payoff hypothesis fails. Full base and
lint-scope validation passes 4,538 jobs; lint passes and all 331 selected
new/changed declarations depend only on standard axioms.

**Composed gates and robust sampling.** `Finite.BimatrixGateProgram` now
implements both gate types in one game, preserving repeated input coefficients
and adding explicit output feedback for comparators. `BimatrixBooleanGate`
implements AND, OR and NOT with integer coefficients and normalized error
bounds. `Math.GridJitter` bounds near-boundary samples by one per coordinate,
and `Math.RobustAverage`/`RobustFeedback` combine exceptional-sample counts with
projected-feedback errors. A kernel-accepted mixed-gate game has unequal row
block masses and zero individual-action weights. Architecture/isolation audits
and all 30 Python regressions pass.

**Remaining reduction obligations.** Connect the actual circuit translation
to robust jittered color evaluation and feedback soundness, then provide
actual polynomial instance serialization and an every-answer binary decoder.
These gates alone do not establish Nash hardness or PPAD completeness.

Certify actual polynomial serialization, then prove every target Nash answer
decodes to a source answer. Combine membership and hardness on the same relation.
Restricted-game corollaries (graphical, polymatrix, sparse or win/lose) follow
only when their own reductions justify their scope.

## 4. Positive algorithms on established semantics

Independent deliveries after their shared APIs settle:

- **Potential/congestion improvement search:** executable finite deviations,
  strict potential progress, correctness and finite step bounds. Integer-range
  bounds are pseudo-polynomial unless their binary encoding is controlled.
  Then define PLS and prove membership for a concrete succinct congestion
  representation; PLS-hardness is a separate reduction project.
- **Zero-sum approximation and approximate CCE:** rational learning updates,
  rounding errors, explicit horizon and bit-cost bounds connected to existing
  regret theorems. External regret gives CCE; CE needs internal or swap regret.
- **Exact correlated equilibrium:** rational linear feasibility and certificate
  correctness first; exact solver next; an actual polynomial-time LP algorithm
  last. Polynomially many constraints do not constitute a runtime certificate.
  Start with explicit payoff tables before succinct games.
- **Deferred acceptance:** ranked finite inputs, executable proposals and
  agreement with stable-matching semantics. Bound proposals by the number of
  possible pairs and separately bound total work. Proposer optimality and
  strategyproofness follow as semantic theorem deliveries.

## 5. Later domains

Scarf and balanced-core search need the balancedness converse and a finite
certificate language. Fisher/Arrow–Debreu results need a market model, utility
representation and precise approximation; linear and Leontief cases must not
be conflated. Exact Nash with three or more players and FIXP need algebraic
circuits and real output semantics rather than rational-witness FNP machinery.

## Module and validation policy

Generic mathematics lives in dedicated Math leaves. Executable rational
algorithms live in Finite; real correctness uses separate modules and canonical
Core predicates. Machine classes and certificates live in the optional
companion, with reusable game-free modules separated from game reductions.
Introduce no universal backend abstraction or duplicate game semantics.
Upstream readiness means minimal imports, generic statements, no placeholders
and independent consumers; submission is separate work.

Compile hostile controls, update lint scopes, run relevant targets and lint,
and audit transitive axioms. Import or package changes require the full affected
build. Update the owning ledger row with its evidence in the same commit.
Use .codex/scratch for probes and release-test companion pins when new base
APIs are used. Ordinary recovery needs no architecture experiment entry.

## Validation of the first slice

The full base and lint-scope build passes 4,426 jobs. Base lint passes, and the
transitive audit checks all 143 new declarations using only propext,
Classical.choice and Quot.sound. Architecture and optional-dependency isolation
audits pass, as do all 30 boundary regressions. Independent review confirms
signed splitting, support preservation and polynomial binary widths.
The analytic existence corollary supplies a bounded certificate for every
nonempty integer bimatrix game while keeping fixed-point imports in Analysis.

Commands from the repository root:

    lake build GameTheory GameTheory.LintAll
    lake lint
    lake env lean .codex/scratch/BimatrixWitnessAxiomAudit.lean
    pwsh -File scripts/phase2-audit.ps1 -VerifyExpected
    pwsh -File scripts/complexity-audit.ps1
    python -m unittest discover -s scripts/tests

The sole added representation owner is the Nash-to-linear-system bridge which
extracts native atom weights. Raw probability representation tokens remain
forbidden in the linear systems, certificates, algorithms and all other
non-owner modules.

## Validation of serialized verification

The full companion/lint/axiom build passes 4,218 jobs against the local checkout
and published base pin `e4b2d03957c70e27217d01e35d7076e9ada763be`.
The final transitive audit checks 2,615 extension declarations using only the
three standard Lean axioms. Companion lint and both structural audits pass;
all 30 boundary regressions pass. Controls cover signed rectangular games with
either column occupied, rejected utilities and dominated support, overlapping
sign fields, malformed inputs and outer pairs, and binary multiplication.

From `extensions/complexity`, release validation uses:

    lake -R update GameTheory
    lake env lean --version
    lake exe cache get
    lake build GameTheoryComplexity GameTheoryComplexity.LintAll GameTheoryComplexity.AxiomAudit
    lake lint

The local-checkout build selects `-KgameTheoryPath=../..`. The next active
delivery is PPAD hardness for the same now-total relation, whose membership
proof and machine-certified reduction are complete.

## Primary proof references

- [Lemke–Howson: complementary paths for bimatrix games](https://epubs.siam.org/doi/10.1137/0112033).
- [von Stengel: equilibrium computation and degeneracy](https://www.sciencedirect.com/science/article/pii/S1574000502030084).
- [Chen–Deng–Teng: bimatrix Nash](https://arxiv.org/abs/0704.1678).
- [Fabrikant–Papadimitriou–Talwar: congestion complexity](https://alex.fabrikant.us/papers/fpt04.pdf).
- [Papadimitriou–Roughgarden: correlated equilibrium](https://timroughgarden.org/papers/cor.pdf).
- [Generalized-circuit tolerance semantics](https://arxiv.org/abs/1907.12854).
- [Etessami–Yannakakis: Nash and FIXP](https://www.research.ed.ac.uk/en/publications/on-the-complexity-of-nash-equilibria-and-other-fixed-points-exten/).
