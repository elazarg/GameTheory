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

The public upstream ComplexityLib baseline is
`257ad90ec5f547894cc20f27bd828839b1bf7bbf`; the package explicitly selects
Mathlib `v4.34.1`. VI-NP-verification supplied useful compatibility evidence,
but its dependency branch is private and is not a portable dependency source.
Only the imported upstream closure is certified by this package's checks.

The `openai/math` randomized mean-payoff solution is a reference for finite
random-tape counting and machine compilation. Its machine model is different
and its result is quasipolynomial. Matroid prophet inequalities are potential
allocation theorem recovery, without an asserted efficient implementation.
Neither is imported or copied here. Comparator challenge statements must be
distinguished from their actual solution modules before any future recovery.

## Validation

Integration measurements are recorded in EXP-158 in `ExperimentLog.md` and the
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

The local released-mode update was attempted but GitHub HTTPS fetches failed
with connection timeouts. The published base commit is confirmed through the
GitHub API; local builds use the same committed sources through the path override.
The new hosted released-pin consumer check remains the validation for git-mode
resolution; it is not counted as a local pass. Restoring the local path resolved
the dependency configuration, but the automatic cache fetch stalled and was
cancelled. Lean 4.34.1 was confirmed and the complete companion build passed
again using existing compiled dependencies.
