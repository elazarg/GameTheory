# GameTheory (Lean 4)

Finite, discrete game-theory foundations in Lean 4, centered on a common semantic core (`KernelGame`) and multiple concrete representations (`NFG`, `EFG`, `MAID`).

## Scope

In scope:
- Finite players/actions/states with discrete probability (`PMF`).
- Strategic semantic core: `KernelGame`.
- Representations: normal form (`NFG`), extensive form (`EFG`), and typed MAID.
- Preference-parameterized solution concepts over outcome distributions.
- Utility-distribution API (`udist`, `udistPlayer`).
- Bridge theorems across representations.
- Kuhn equivalence corollaries at utility-distribution level.

Out of scope:
- Continuous/infinite probability spaces.
- Subgame perfect, sequential, correlated equilibrium.
- Client-specific product APIs.

## Current API Surface

The library exposes:
1. `KernelGame.udist` and `KernelGame.udistPlayer` (+ point-mass collapse lemmas).
2. Preference-parameterized concepts:
   - `KernelGame.IsNashFor`
   - `KernelGame.IsDominantFor`
   - `KernelGame.dominant_is_nash_for`
3. EU specialization:
   - `KernelGame.euPref`
   - `IsNash_iff_IsNashFor_eu`
   - `IsDominant_iff_IsDominantFor_eu`
4. Utility-distribution bridge corollaries:
   - `NFGGame.toKernelGame_udist`
   - `toStrategicKernelGame_udist` (EFG)
   - `maidToEFG_udist` (MAID)
5. Kuhn utility-distribution corollaries:
   - `kuhn_behavioral_to_mixed_udist`
   - `kuhn_mixed_to_behavioral_udist`
6. Example coverage in:
   - `NFGExamples.lean`
   - `EFGExamples.lean`
   - `MAIDExamples.lean`

Build:
- `lake build` is the project build command.

## MVP Surface Decision

`InfoArena` is currently experimental and excluded from the top-level library surface because its evaluator is intentionally unfinished.

## Module Map

- `GameTheory/Probability.lean` - kernels and expectation utilities
- `GameTheory/KernelGame.lean` - semantic core, `eu`, `udist`
- `GameTheory/SolutionConcepts.lean` - Nash/dominance and preference-parameterized variants
- `GameTheory/NFG*.lean` - normal-form games and examples/bridges
- `GameTheory/EFG*.lean` - extensive-form games, Kuhn results, examples/bridges
- `GameTheory/MAID*.lean` - typed MAID semantics, EFG bridge, examples
- `ROADMAP.md` - MVP roadmap and acceptance gates
