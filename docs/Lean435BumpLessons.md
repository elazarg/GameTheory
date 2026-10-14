# Lean 4.35 / Mathlib v4.35.0: bump lessons for clients

GameTheory and its optional complexity package now use released Lean and Mathlib
4.35.0. The base package version is 4.35.0; the optional package retains its
independent product version, 0.1.0.

## Dependency pins

| Component | Pin |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.35.0` |
| Mathlib requirement | `v4.35.0` |
| Resolved Mathlib commit | `56a005855ea17e0b0958f73ec801ae140b0a1679` |
| fixed-point-theorems | `f06449c5fb1ca49f14ea2b5331ddf71bd2dcd232` |
| Complexitylib, selected imports only | `257ad90ec5f547894cc20f27bd828839b1bf7bbf` |
| CSLib, selected imports only | `94ea80f41a5678fce997a004f0d8d12dbe47cc4b` |

The [fixed-point repair](https://github.com/elazarg/fixed-point-theorems-lean4/commit/f06449c5fb1ca49f14ea2b5331ddf71bd2dcd232)
is published. It supplies explicit arguments in the cubical Sperner proof and
the affine-space import no longer supplied transitively to Kakutani. Its strict
standalone build passed 3,189 jobs, and all six theorem endpoints use only the
standard axioms.

The complexity extension uses the original upstream Complexitylib repository.
The previous fork added a Cook–Levin proof tail that now fails with “No goals to
be solved”: `congr 1` already closes that goal. Its public upstream parent works
unchanged. Upstream warning cleanup is unnecessary; only selected imports must
compile, and only axioms transitively used by authored declarations are audited.
No full Complexitylib or CSLib umbrella compatibility is claimed.

Keep the explicit Mathlib requirement last in each Lake configuration. Its
released transitive pins must override older inherited manifests; otherwise
Mathlib's cache rejects the dependency combination. Use Lake to regenerate
manifests rather than editing them or dependency sources by hand. After updating:

```text
lake update
lake env lean --version
lake exe cache get
```

The package option `allowNonModules := true` preserves the existing legacy
module visibility while importing Mathlib modules. This bump does not convert
GameTheory's source tree to Lean's module system.

## Finite uniform probability

Mathlib removed its finite uniform PMF constructors. The deprecated
`PMF.uniformOfFintype` name now suggests a measure constructor with a different
carrier, so replacing it mechanically changes the semantics.

[`FiniteUniform.lean`](../GameTheory/Math/Probability/FiniteUniform.lean) defines
`GameTheory.Math.Probability.uniformLaw` directly using `PMF.ofFintype`, with
inverse-cardinality atoms, full support, and event mass equal to the fraction of
carrier points in the event. It needs no measurable structure. All finite uniform
laws in the base and optional package use this construction.

For `PMF.map_apply` followed by a finite filtered sum, ensure the predicate's
decidability agrees with the classical decider in the mapped PMF. The proof in
[`Uniform.lean`](../GameTheory/Math/Probability/Uniform.lean) selects it explicitly;
a direct rewrite can fail even when the predicates are propositionally equal.

## Parser and proof diagnostics

- Rename the new reserved identifier `recall` in binders and references.
- Rename `hidden` when used as a match-pattern variable; otherwise the parser
  recognizes a deprecated builtin. Ordinary compiled uses need no blanket rename.
- Replace `Mathlib.Data.Prod.Lex` imports with `Mathlib.Order.Prod.Lex.Basic`.
- Remove tactics after a preceding tactic has closed the goal. For branches
  whose remaining goals vary, sequential `all_goals` blocks avoid ineffective
  `<;>` chains without weakening the proof or disabling linters.
- For the three concrete routing tests exceeding elaborator recursion depth,
  `decide +kernel` checks the computations directly in the kernel. It adds no
  evaluation axiom and needs no raised global recursion limit.

## Validation

```text
python scripts/audit.py
python scripts/audit.py --complexity
python -B -m unittest discover -s scripts/tests
```

The base audit passed all 4,643 build jobs, environment lint, source boundaries,
coverage, diagnostic traces, and transitive axiom checks. The optional audit
against the local base checkout passed all 4,458 jobs, lint, diagnostic traces,
and transitive axiom checks using unchanged upstream Complexitylib sources.
All 41 tooling regression tests passed, including rejection of authored warnings
while permitting third-party warnings. Raw build logs and probes remain local.

The extension's default base Git pin is
`b0a92aefcdca842e8a14e64829bbc54c0040d0d2`, containing the migration and citation
metadata. The optional audit also passed all 4,458 jobs, lint, diagnostic traces,
and axiom checks against that Git checkout without a local-path override.
The separate `lake --iofail build GameTheory.Tests.BimatrixComputedPivot` consumer
check passed 3,125 jobs. This used a temporary local Git transport for the committed
base revision before publishing GameTheory; dependency pins resolve publicly.
The development manifest was restored to the local checkout afterward.
