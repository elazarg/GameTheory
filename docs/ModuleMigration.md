# Mechanical module-system migration

The base and optional complexity packages use Lean 4.35's module system and
set `requiresModuleSystem := true`. All 1,145 authored Lean files were converted,
including the lint and axiom drivers, fixtures, and experiments. Lake configuration
files retain Lake's own syntax.

Library files start with `module`, keep their existing imports as `public import`,
and use `@[expose] public section` after the imports. This preserves the existing
public declarations, reexports, and unfolding behavior. Definition and proof
bodies are unchanged; visibility reduction is a separate future task.

The packages enable `backward.privateInPublic` and suppress its transition warning.
Existing exposed definitions can therefore still reference private helpers without
moving, renaming, or inlining them. A few declarations use scoped
`backward.proofsInPublic` to preserve elaboration of inferred witnesses in data
definitions. These options preserve legacy behavior during the mechanical port.

Explicit imports replace dependencies previously available only through private
Mathlib imports. Existing executable `#guard` checks have corresponding meta
imports. The FOSG fixtures and Bird determinant consumers selectively use
`import all` for private instances or unexposed implementation bodies.

Internal lint and axiom drivers use `import all` for authored modules so unused
private declarations remain auditable. Lean elaborator helpers in axiom drivers
are meta imports. Regression tests check wrapped public imports and demonstrate
that the axiom driver detects an unused private declaration with an untrusted
transitive axiom.

Validation uses the unchanged full workflows:

```text
python scripts/audit.py
python scripts/audit.py --complexity
python -B -m unittest discover -s scripts/tests
```

The optional package is checked against both the local base checkout and its
default committed Git pin. An exact source comparison against the pre-migration
commit verifies every declaration and proof body after removing only the added
section marker and scoped compatibility-option wrappers. Scratch comparisons,
probes, and build logs remain in ignored local storage.

The base audit passed all 4,643 build jobs, lint, and transitive axiom checks.
All 43 tooling regression tests passed. The exact comparison preserved every
declaration and proof body; compatibility wrappers are scoped to nine declarations.
The optional audit against the local base passed all 4,458 jobs, lint, diagnostic
trace checks, and transitive axiom checks. Across both packages, 41 explicit import
edges were added to preserve the existing proofs and executable checks.

The optional package's default base pin is
`c7cd6bed7498b9a16edb22262e9522ceff90648c`. Its full audit also passed all
4,458 jobs, lint, diagnostic traces, and axiom checks in default Git mode.
The separate `lake --dir extensions/complexity --iofail build
GameTheory.Tests.BimatrixComputedPivot` consumer passed all 3,125 jobs. A temporary
local Git transport supplied the committed base before publication; the ordinary
local-path development manifest was restored afterward.
