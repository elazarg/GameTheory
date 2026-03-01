# GameTheory (Lean 4)

Formalized finite game theory in Lean 4, centered on a single stochastic game model.

This library proves core results for finite, discrete games:
- normal-form games (NFG),
- extensive-form games (EFG, including perfect-recall/Kuhn results),
- MAIDs (multi-agent influence diagrams),
all unified through `KernelGame`.

## Major Theorems Proved

- **Mixed Nash existence (finite games)**: `KernelGame.mixed_nash_exists`
- **Von Neumann minimax (finite 2-player zero-sum)**: `KernelGame.von_neumann_minimax`
- **Zermelo / backward induction (finite perfect-information EFG)**: `EFG.zermelo`
- **Kuhn equivalence under perfect recall**:
  `EFG.kuhn_behavioral_to_mixed`, `EFG.kuhn_mixed_to_behavioral`
- **Nash characterization by best responses**:
  `KernelGame.isNash_iff_bestResponse`
- **Strict dominance gives unique Nash**:
  `KernelGame.strictly_dominant_unique_nash`
- **Pure Nash induces correlated equilibrium**:
  `KernelGame.nash_pure_isCorrelatedEq`
- **Coarse correlated equilibrium existence (finite games)**:
  `KernelGame.coarseCorrelatedEq_exists`

Scope is intentionally discrete:
- probabilities are `PMF` (finite/discrete distributions),
- expected utility is over finite supports,
- no continuous strategy spaces or measure-theoretic probability.

## What This Library Is

The core object is:
- `KernelGame ι`: per-player strategy types, stochastic outcome kernel, and utility map.

Once a model is expressed as `KernelGame`, the same definitions/theorems apply:
- equilibrium (`IsNash`, `IsStrictNash`, `IsBestResponse`),
- dominance (`IsDominant`, `WeaklyDominates`, `StrictlyDominates`),
- correlated equilibrium (`IsCorrelatedEq`, `IsCoarseCorrelatedEq`),
- structural game classes (`IsZeroSum`, `IsConstantSum`, `IsTeamGame`, potential-game notions).

## Key Definitions (Fast Orientation)

From `GameTheory/SolutionConcepts.lean`, `GameTheory/GameProperties.lean`, `GameTheory/KernelGame.lean`:
- `KernelGame ι`
- `Profile G`
- `KernelGame.eu` / expected utility
- `KernelGame.udist` / utility-distribution semantics
- `KernelGame.IsNash`
- `KernelGame.IsBestResponse`
- `KernelGame.IsDominant`, `KernelGame.IsStrictDominant`
- `KernelGame.WeaklyDominates`, `KernelGame.StrictlyDominates`
- `KernelGame.IsCorrelatedEq`, `KernelGame.IsCoarseCorrelatedEq`
- `KernelGame.IsZeroSum`, `KernelGame.IsConstantSum`, `KernelGame.IsTeamGame`
- `KernelGame.IsExactPotential`, `KernelGame.IsOrdinalPotential`

From `GameTheory/Probability.lean`:
- `Kernel α β` (stochastic kernels via `PMF`)
- `expect`
- basic kernel composition/pushforward lemmas used across the library.

## Landmark Theorems (Exact Names)

### Nash and Core Characterizations
- `KernelGame.isNash_iff_bestResponse`
- `KernelGame.dominant_is_nash`
- `KernelGame.strictly_dominant_unique_nash`
- `KernelGame.IsStrictNash.isNash`
- `ofEU_nash_affine`

### Existence and Fixed-Point Pipeline
- `KernelGame.mixed_nash_exists` (Nash existence in finite mixed strategies)
- `KernelGame.mixed_nash_exists_of_nashMapOnMixedSimplex_fixed_point`
- `KernelGame.continuous_nashMapOnMixedSimplex`
- `brouwer_mixedSimplex` (via `ProductSimplexBrouwer`)

### Minimax
- `KernelGame.isSaddlePoint_iff_isNash`
- `KernelGame.von_neumann_minimax`

### Correlated Equilibrium
- `KernelGame.IsCorrelatedEq.toCoarseCorrelatedEq`
- `KernelGame.nash_pure_isCorrelatedEq`
- `KernelGame.nash_pure_isCoarseCorrelatedEq`
- `KernelGame.mixed_nash_isCoarseCorrelatedEq`
- `KernelGame.coarseCorrelatedEq_exists`

### EFG / Kuhn
- `EFG.zermelo`
- `EFG.kuhn_behavioral_to_mixed`
- `EFG.kuhn_mixed_to_behavioral`
- with utility-distribution corollaries:
  `EFG.kuhn_behavioral_to_mixed_udist`,
  `EFG.kuhn_mixed_to_behavioral_udist`.

## Architecture and Module Map

Entry point:
- `GameTheory.lean` (imports the full library surface)

Core:
- `GameTheory/Probability.lean`
- `GameTheory/PMFProduct.lean`
- `GameTheory/KernelGame.lean`
- `GameTheory/SolutionConcepts.lean`

Major theorem families:
- Nash/existence: `BestResponse.lean`, `NashExistence.lean`, `NashExistenceMixed.lean`
- dominance: `StrictDominance.lean`, `DominanceRelations.lean`, `DominanceNash.lean`
- correlated equilibrium: `CorrelatedEqProperties.lean`, `NashCorrelatedEq.lean`, `CorrelatedNashMixed.lean`
- zero/constant-sum + minimax: `ZeroSum*.lean`, `ConstantSum*.lean`, `Minimax*.lean`
- potential/team/welfare/pareto/IR:
  `Potential*.lean`, `TeamGame*.lean`, `WelfareTheorems.lean`,
  `ParetoOptimal.lean`, `IndividualRationality.lean`

Representations and bridges:
- NFG: `NFG.lean`, `NFG_EFG.lean`
- EFG: `EFG.lean`, `EFGKuhn.lean`, `EFGKuhnFull.lean`, `EFG_NFG.lean`
- MAID: `MAID.lean`, `MAID_EFG.lean`

Examples:
- `NFGExamples.lean`
- `EFGExamples.lean`
- `MAIDExamples.lean`

## Representation Interoperability

The design goal is semantic reuse:
- each concrete representation has a translation to `KernelGame`,
- generic theorems are proved once and apply after translation,
- bridge theorems preserve outcome/utility-distribution semantics where appropriate.

Important bridge functions include:
- `NFGGame.toKernelGame`
- `EFGGame.toKernelGame`
- `MAID.toKernelGame`

## Build and Toolchain

Toolchain and dependencies:
- Lean: `leanprover/lean4:v4.27.0` (`lean-toolchain`)
- Mathlib: `v4.27.0` (`lakefile.toml`)
- local dependency: `fixed-point-theorems-lean4` (`FixedPointTheorems`)

Build:

```bash
lake build
```

Targeted build:

```bash
lake build GameTheory
```

## Current Status

- The exported `GameTheory/*.lean` library surface builds successfully.
- Current tree includes 48 imported `GameTheory.*` modules from `GameTheory.lean`.
- Theorem/lemma/def declarations in `GameTheory/*.lean`: 423 (quick source count).

## Minimal Usage

Import the full library:

```lean
import GameTheory
```

Or import specific components:

```lean
import GameTheory.NashExistenceMixed
import GameTheory.MinimaxTheorem
import GameTheory.EFGKuhnFull
```

## Future Work (Textbook Theorems Within Scope)

- **Aumann correlated-equilibrium existence (finite games)**:
  for every finite game, `∃ μ, IsCorrelatedEq μ`.
- **One-shot deviation principle (finite extensive-form, perfect recall)**:
  characterize sequential rationality / SPE via one-step deviations.
- **Sequential equilibrium existence (finite extensive-form games)**:
  Kreps-Wilson style existence with explicit belief consistency.
- **Perfect Bayesian equilibrium existence (finite extensive-form games)**:
  after fixing a concrete Bayes-consistency notion in this library.
- **Shapley theorem for discounted stochastic games (finite state/action)**:
  existence of stationary equilibrium/value in finite discounted stochastic games.

## Non-Goals

- Infinite/continuous games
- Measure-theoretic probability foundations
- Algorithmic equilibrium computation tooling

This repository is focused on formal theorem development for finite game theory.
