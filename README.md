# GameTheory

Greenfield Lean 4 game-theory library built on Mathlib.

The architecture spike in [`docs/GameTheory2Design.md`](docs/GameTheory2Design.md)
has passed Phase 0 (architecture evidence), Phase 1 (core competition), and
Phase 2 (incentive vertical slice). Phase 3, the sequential slice, has not
started.

```text
GameTheory/Probability   finite-support probability laws (FinDist)
GameTheory/Core          signatures, profiles, forms, preferences, utility,
                         deviation schemes, equilibrium, response concepts
GameTheory/Finite        executable rational frontend and its correctness layer
GameTheory/Examples      reader-facing examples with #eval and #guard tests
GameTheory/Tests         architecture and locality tests
GameTheory/Experimental  architecture spikes, never re-exported
```

The ignored `reference/GameTheory-v1/` directory is an exact source snapshot of
the previous library at commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
It is evidence for design experiments, not a dependency or migration source.

## Environment

- Lean: `v4.32.0`
- Mathlib: `v4.32.0`
- Lake package, public library, and public Lean namespace: `GameTheory`

Use `lake update` to resolve dependencies and `lake exe cache get` to fetch
Mathlib build artifacts.

## Checks

```text
lake build
pwsh -NoProfile -File scripts/phase0-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
```

`lake build` compiles every module, including examples, tests, and experiments.
The phase audits re-check the measurements each gate was decided on.
