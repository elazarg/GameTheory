# Game Theory in Lean4

[![CI](https://github.com/elazarg/GameTheory/actions/workflows/ci.yml/badge.svg)](https://github.com/elazarg/GameTheory/actions/workflows/ci.yml)

A Lean 4 library for finite and discrete game theory, built on Mathlib. Static
and sequential games share one semantic core: a single deviation API carries
Nash, correlated, Bayesian, and refinement results; the language encodings
compile into that core; and the executable algorithms are tied to their
specifications by correctness theorems.

## Getting started

GameTheory follows Mathlib releases. The Lean toolchain it builds with is in
[`lean-toolchain`](lean-toolchain), and the Mathlib revision is in
[`lakefile.lean`](lakefile.lean). Use the same toolchain in your project, and
match any Mathlib requirement you declare yourself to GameTheory's.

Add the library to your `lakefile.lean`. Pin it to a release tag or a commit.
Release tags are named after the Lean version they build with.

```lean
require "elazarg" / "GameTheory" @ git "<tag-or-commit>"
```

Then fetch the dependencies and the prebuilt Mathlib cache, and build:

```text
lake update
lake exe cache get
lake build
```

Lake also fetches the other dependencies, including the fixed-point theorem
library used by `GameTheory.Analysis`.

`import GameTheory` gives the static, sequential, epistemic, evolutionary, and
executable foundations. Everything else is an explicit import, which keeps each
family's assumptions out of the basic one:

| Goal | Import |
|---|---|
| Pure and mixed games, preferences, Nash, CE/CCE, Bayesian games, welfare, learning foundations | `GameTheory.Core` |
| Protocol execution, histories, information, assessment, SPE, backward induction | `GameTheory.Protocol` |
| Finite pure-Nash enumeration and checked rational algorithms | `GameTheory.Finite.Algorithm`, `GameTheory.Finite.Correctness` |
| Mixed-Nash existence, minimax, refinements, approachability, convergence | `GameTheory.Analysis` |
| Discrete probability, DAGs, online learning, discounted sums, reusable geometry | `GameTheory.Math` |
| Repeated games, public monitoring, PPE, self-generation, uniform equilibrium | `GameTheory.Repeated` |
| Stochastic games, public policies, restart calculus, uniform payoffs | `GameTheory.Stochastic` |
| Auctions, Groves mechanisms, information design, implementation, fair division | `GameTheory.Mechanism` |
| Bargaining, matching, coalitional games, voting-power indices | `GameTheory.Cooperative` |
| NFG, EFG, FOSG, MAID, Bayesian, intrinsic, and multi-round encodings | `GameTheory.Languages.*` |

`GameTheory.Math` is its own Lake target and stands alone, without any game
definitions:

```lean
import GameTheory.Math.Probability.Bounds

open GameTheory.Math.Probability

#check eventMass_toReal_le_expect_div
```

## Examples

The examples are executable documentation. The classic finite games connect a
table frontend to the semantic equilibrium predicates:

```lean
import GameTheory.Examples.Classic

open GameTheory GameTheory.Examples

#check prisonersDilemma_bothDefect_isNash
#check matchingPennies_noPureNash
```

Good entry points:

- [`Examples/Classic.lean`](GameTheory/Examples/Classic.lean) — Prisoner's
  Dilemma, Matching Pennies, Battle of the Sexes, and a potential game;
- [`Examples/NFG.lean`](GameTheory/Examples/NFG.lean) — a countably infinite
  action carrier, handled without enumeration;
- [`Examples/StochasticUniform.lean`](GameTheory/Examples/StochasticUniform.lean)
  — a nonconstant finite stochastic payoff and its uniform bound;
- [`Tests/StochasticContinuation.lean`](GameTheory/Tests/StochasticContinuation.lean)
  — chronological histories, continuation, and restart;
- [`Tests/Bayesian.lean`](GameTheory/Tests/Bayesian.lean) — direct Bayesian and
  protocol-form Nash agreeing.

The [capability matrix](docs/CapabilityMatrix.md) indexes the public workflows
with their exact imports and compiled consumers.

## Organization

`GameTheory.Math` owns the reusable mathematics, including products,
conditioning, and guarded expectation for ordinary Mathlib `PMF` laws.
`GameTheory.Core` owns static forms, utility,
deviations, preferences, and solution concepts. `GameTheory.Protocol` owns the
single execution and behavioral-policy semantics the sequential languages share.
`GameTheory.Analysis` owns analytic existence and convergence arguments and is
the only root allowed to import the external fixed-point library. Architecture
audits check these project dependency boundaries.

Assumptions sit on the theorem or operation that needs them: finite support,
finite player/action carriers, and payoff integrability are requested locally.
Executable modules use explicit enumerations and computable scalars;
correctness modules connect them to the real-valued semantics.

## Scope

Discrete semantics uses `PMF` on arbitrary carriers; each law may have countably
infinite support. Real expected utility requires integrability of the actual
compared laws. An undefined alternative fails its equilibrium comparison,
rather than disappearing from the deviation quantifier. Finite support and
bounded payoffs are sufficient ways to discharge these requirements.

Ordinary measures represent infinite policy products and arbitrary independent
per-player policy laws, with exact finite-prefix behavioral correspondences.
General measurable games and infinite-play outcome laws are outside the core;
focused experiments with infinite-play laws live under
`GameTheory.Experimental`.

The [delivery ledger](docs/DeliveryLedger.md) lists theorem families that are
partial or planned.

## Development

```text
lake build      # library, examples, tests, and experiments, warnings as errors
lake lint       # Batteries environment linters over the public library
pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
```

Before tagging a release, set the package `version` in `lakefile.lean` to the
tag's version number (without the `v` prefix).

Architecture and contribution rules live in
[`docs/GameTheory2Design.md`](docs/GameTheory2Design.md) and
[`AGENTS.md`](AGENTS.md). The predecessor library is at tag `v1-final`, with its
workflows mapped in the [v1 capability map](docs/V1CapabilityMap.md).

Licensed under the [Apache License 2.0](LICENSE).
