# GameTheory (Lean 4)

Formalized finite game theory in Lean 4, centered on a single stochastic game model.

This project develops a reusable finite-game-theory foundation across multiple
representations, with one semantic target model used to share definitions and
proofs. The emphasis is not on isolated model-specific developments, but on
proving core concepts once and transporting them cleanly.

## Major Theorems Proved

The library includes formal proofs of standard finite-game results, including:
- existence of mixed Nash equilibria in finite games,
- finite two-player zero-sum minimax,
- backward induction/Zermelo-style existence in finite perfect-information trees,
- Kuhn-style mixed/behavioral equivalence under perfect recall assumptions,
- correlated and coarse correlated equilibrium existence and relations,
- one-shot deviation principle formulations for sequential settings.

Scope is intentionally discrete:
- probabilities are `PMF` (finite/discrete distributions),
- expected utility is over finite supports,
- no continuous strategy spaces or measure-theoretic probability.

## What This Library Is

At the center is a stochastic strategic-form object (`KernelGame`) that
packages strategy spaces, outcome uncertainty, and utility. Normal-form,
extensive-form, MAID-style, and protocol-style developments are connected to
this shared form through translation/bridge constructions.

Because of this design, notions such as equilibrium, dominance, and incentive
constraints are defined semantically rather than representation-by-representation.
The recent deviation-first refactor makes deviation operators explicit in that
semantic layer, which keeps correlated-equilibrium and regret developments
uniform and easier to generalize.

## Forms and Semantics

The library treats game forms as different presentations of the same underlying
mathematical object:
- normal-form descriptions of simultaneous strategic choice,
- extensive/protocol descriptions of sequentially unfolding choices and information,
- graph-structured decision models (MAID-like).

All of these are interpreted into one expected-utility semantics over finite
probability distributions. This is the key abstraction boundary in the codebase.

## Concepts and Proof Style

Most proofs are structured around a small set of semantic ideas:
- no-profitable-deviation conditions (best response, Nash, correlated notions),
- order/comparison arguments on expected utility,
- decomposition lemmas for finite products and pushforwards,
- bridge lemmas that move statements across equivalent representations.

This leads to a “prove once, reuse across forms” workflow: representation-specific
work is mostly in the bridges, while concept proofs live in the shared layer.

## Representation Interoperability

The design goal is semantic reuse:
- each concrete representation has a translation to `KernelGame`,
- generic theorems are proved once and apply after translation,
- bridge theorems preserve outcome/utility-distribution semantics where appropriate.

In practice, this means model-specific developments can focus on modeling and
structural assumptions, while solution concepts and many existence/characterization
results come from the shared semantic layer.

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
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Concepts.NashExistenceMixed
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
