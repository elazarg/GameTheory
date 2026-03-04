# GameTheory (Lean 4)

Formalized finite game theory in Lean 4, centered on a single stochastic game model.

This library proves core results for finite, discrete games:
- normal-form games (NFG),
- extensive-form games (EFG, including perfect-recall/Kuhn results),
- MAIDs (multi-agent influence diagrams),
all unified through `KernelGame`, with first-class deviation operators for
incentive-style concepts (Nash/CE/CCE/regret).

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
- **Correlated equilibrium existence (finite games)**:
  `KernelGame.correlatedEq_exists`
- **One-shot deviation principle (finite perfect-information EFG)**:
  `EFG.oneShotDeviation_iff_spe`

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

## Game Forms

Unified semantic form:
- `KernelGame ι`
- `Profile G`
- `KernelGame.eu` / expected utility
- `KernelGame.udist` / utility-distribution semantics

Concrete forms represented in the library and bridged to `KernelGame`:
- normal-form games (NFG)
- extensive-form games (EFG)
- MAIDs

## Core Concepts

Deviation and incentives:
- `KernelGame.Deviation`
- `KernelGame.unilateralDeviation`, `KernelGame.constantDeviation`
- `KernelGame.unilateralDeviationDistribution`, `KernelGame.constantDeviationDistribution`

Equilibrium and dominance:
- `KernelGame.IsNash`
- `KernelGame.IsBestResponse`
- `KernelGame.IsDominant`, `KernelGame.IsStrictDominant`
- `KernelGame.WeaklyDominates`, `KernelGame.StrictlyDominates`
- `KernelGame.IsCorrelatedEq`, `KernelGame.IsCoarseCorrelatedEq`

Structural classes:
- `KernelGame.IsZeroSum`, `KernelGame.IsConstantSum`, `KernelGame.IsTeamGame`
- `KernelGame.IsExactPotential`, `KernelGame.IsOrdinalPotential`

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
- `KernelGame.mixed_nash_isCorrelatedEq`
- `KernelGame.correlatedEq_exists`
- `KernelGame.coarseCorrelatedEq_exists` (corollary via `toCoarseCorrelatedEq`)

### EFG / Kuhn
- `EFG.zermelo`
- `EFG.kuhn_behavioral_to_mixed`
- `EFG.kuhn_mixed_to_behavioral`
- with utility-distribution corollaries:
  `EFG.kuhn_behavioral_to_mixed_udist`,
  `EFG.kuhn_mixed_to_behavioral_udist`.

### One-Shot Deviation Principle
- `EFG.spe_hasNoOneShotDeviation` (SPE implies no profitable OSD)
- `EFG.hasNoOneShotDeviation_spe` (converse for perfect-info games)
- `EFG.oneShotDeviation_iff_spe` (the equivalence)

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

## Minimal Usage

Import the full library:

```lean
import GameTheory
```

Or import specific components:

```lean
import GameTheory.Concepts.NashExistenceMixed
import GameTheory.NFG.MinimaxTheorem
import GameTheory.EFG.Kuhn
```

## Future Work (Textbook Theorems Within Scope)

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
