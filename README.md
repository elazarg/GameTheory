# GameTheory

Greenfield Lean 4 game-theory library built on Mathlib.

This repository currently contains only the project environment and design
documents. The `GameTheory/` source tree and `GameTheory.lean` public root are
intentionally absent until the architecture spikes in
[`docs/GameTheory2Design.md`](docs/GameTheory2Design.md) begin.

The ignored `reference/GameTheory-v1/` directory is an exact source snapshot of
the previous library at commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
It is evidence for design experiments, not a dependency or migration source.

## Environment

- Lean: `v4.32.0`
- Mathlib: `v4.32.0`
- Lake package and future public library: `GameTheory`
- Public Lean namespace: `GameTheory`

Use `lake update` to resolve dependencies and `lake exe cache get` to fetch
Mathlib build artifacts. There is no library code to build yet.
