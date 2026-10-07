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
- `GameTheoryComplexity.Backend.Negligible`: equivalence of ComplexityLib's explicit
  inverse-power threshold predicate with the canonical Mathlib-based predicate.
- `GameTheoryComplexity.SampleTest`: a small client facade exposing the Boolean
  test class, its polynomial sample-count property, and indistinguishability
  implications using only canonical GameTheory types in declaration signatures.
- `GameTheory.Math.Probability.HybridIndistinguishability`: a uniform adjacent
  advantage certificate, finite telescoping bound, and indistinguishable
  endpoints after polynomially many uniformly negligible changes.
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
certificate starts from a standard encoded pair containing the unary parameter and the sample bitstring. Its deterministic machine computes
exactly the input consumed by `booleanMachineTest`, with polynomial cost
including pair decoding. General efficient postprocessing and general reference
mean tests remain separate obligations. Serialization and test execution have
separate machine certificates; this slice does not build one composed NTM.

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
uses one eventual bound for every active index at each security parameter.

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
lint target, checks dependency isolation, and audits selected theorem axioms.
The base CI remains independent of the companion dependency resolution.

The serializer follow-up builds the companion library, fixtures, lint driver and
axiom audit together with 3,099 jobs on Lean/Mathlib 4.34.1. All 76 extension
declarations pass the transitive axiom audit. Its primitive FP dependency closure
compiles unchanged, without importing the full Cobham characterization.
