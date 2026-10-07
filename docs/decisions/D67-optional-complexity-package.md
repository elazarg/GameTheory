# D67: optional certified computation package

Status: adopted for the narrowed Boolean sample-test and packaging interface.

Experiment: [EXP-158](../ExperimentLog.md).

## Question and competing designs

Concrete machine certificates should specialize the existing sample-test and
probability interfaces while ordinary GameTheory clients retain their dependency
set. An unconditional root Lake dependency with selective Lean imports isolates
the import graph but still resolves and downloads the extra package. A separate
companion Lake package isolates both dependency resolution and the import graph.

## Chosen boundary

`extensions/complexity` owns the `GameTheoryComplexity` import modules, with
declarations under `GameTheory.Complexity`. Its dependency
direction is companion to base and companion to ComplexityLib; the base never
requires or imports the companion. Namespace ownership is independent of package
ownership. The source directory is outside the base library's default submodule
globs, so a base build does not schedule companion modules.

The initial shared `GameTheory.Complexity` import prefix failed: Lake assigned
these imports to the base package's broad `GameTheory` glob and searched the
base source directory for companion files. A disjoint import prefix resolves
ownership without changing the base configuration. The public declaration
namespace remains canonical. EXP-158 preserves this refuted packaging hypothesis.

The client facade exposes canonical sample-test types and properties; upstream
machine types appear only in explicit backend leaves. There is no generic
machine class, registry, or cross-model equivalence assumption. Backend-specific
construction clients accept that dependency; game/security clients use the
facade and existing semantics.

Consumers fetch a published repository revision with the companion's git
subdirectory. The companion uses a pinned public base revision by default, with
an explicit local-path configuration for in-repository development. It shares
the base Lean/Mathlib version. Separate packaging does not support mixing Lean
versions or incompatible Mathlib revisions within one consumer environment.

## Representative evidence and kill conditions

The finite-random-tape PMF acceptance formula is compared directly with the
upstream machine's acceptance count. A two-step fair-coin machine provides a
positive consumer; impossibility of exact `1/3` acceptance by every fixed-length
fair tape rejects treating all rational samplers as exact bounded machines.

Canonical Boolean inputs encode the security parameter in unary and use a
fixed polynomial sample count. The input length and selected all-path execution
clock are polynomial in that parameter. An arbitrary short-output encoder could
hide an oracle, so no arbitrary-encoder class is designated efficient.

The design is killed by any required base toolchain/dependency change, optional
dependencies in the base manifest, companion imports in the base graph, a
parallel probability/indistinguishability semantics, or a test interface claiming
parameter-polynomial execution without controlling encoded input length.
The boundary audit checks base imports/configuration/manifest and matching
resolved Mathlib revisions; the companion has independent build, lint and
transitive axiom checks. EXP-158 records exact commands and outcomes.

## Result and limitations

The public API is deliberately limited to canonically encoded Boolean samples,
certified machine execution, and the probability/predicate bridges. It does not
characterize all PPT tests. The follow-up serializer slice supplies a
deterministic machine witness for the exact canonical input, with polynomial
runtime in the unary security parameter including tuple decoding; EXP-158
records the original narrower validation separately.
Efficient encodings, efficient reference utility samplers, postprocessing
closure, and efficient strategy/compilation/simulation certificates remain
separate obligations. A class of efficient distinguishers does not restrict
game deviations. No commitment primitive or full computational-equilibrium
instantiation follows from this boundary.

Uniform hybrid composition remains dependency-free, reusing the existing
negligible-advantage semantics and producing canonical `SecureImplementation`
certificates. A moving-jump counterexample rejects fixed-index negligible gaps
as a substitute for a uniform bound over the active indices.
