# GameTheory

[![CI](https://github.com/elazarg/GameTheory/actions/workflows/ci.yml/badge.svg)](https://github.com/elazarg/GameTheory/actions/workflows/ci.yml)

A Lean 4 library for finite and discrete game theory, built on Mathlib. Static
and sequential games share one semantic core: a single deviation API carries
Nash, correlated, Bayesian, and refinement results; the language encodings
compile into that core; and the executable algorithms are tied to their
specifications by correctness theorems.

## Getting started

The library tracks Mathlib and is currently on Lean `v4.33.1`. Add it to your
`lakefile.lean`:

```lean
require "elazarg" / "GameTheory" @ git "v4.33.1"
```

Releases carry the toolchain they build against, so a downstream project moves
GameTheory and Mathlib together by changing one version string.

```text
lake update
lake build
```

`import GameTheory` gives the static, sequential, epistemic, evolutionary, and
executable foundations. Everything else is an explicit import, which keeps each
family's assumptions out of the basic one:

| Goal | Import |
|---|---|
| Pure and mixed games, preferences, Nash, CE/CCE, Bayesian games, welfare, learning foundations | `GameTheory.Core` |
| Protocol execution, histories, information, assessment, SPE, backward induction | `GameTheory.Protocol` |
| Finite pure-Nash enumeration and checked rational algorithms | `GameTheory.Finite.Algorithm`, `GameTheory.Finite.Correctness` |
| Mixed-Nash existence, minimax, refinements, approachability, convergence | `GameTheory.Analysis` |
| Finite probability, DAGs, online learning, discounted sums, reusable geometry | `GameTheory.Math` |
| Repeated games, public monitoring, PPE, self-generation, uniform equilibrium | `GameTheory.Repeated` |
| Finite stochastic games, public policies, restart calculus, uniform payoffs | `GameTheory.Stochastic` |
| Auctions, Groves mechanisms, information design, implementation, fair division | `GameTheory.Mechanism` |
| Bargaining, matching, coalitional games, voting-power indices | `GameTheory.Cooperative` |
| NFG, EFG, FOSG, MAID, Bayesian, intrinsic, and multi-round encodings | `GameTheory.Languages.*` |

`GameTheory.Math` is its own Lake target and stands alone, without any game
definitions:

```lean
import GameTheory.Math.Probability.Bounds

open GameTheory.Math.Probability

#check FinDist.probOf_le_expect_div
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

`GameTheory.Math` owns the reusable mathematics, including the canonical
finite-support law `FinDist`. `GameTheory.Core` owns static forms, utility,
deviations, preferences, and solution concepts. `GameTheory.Protocol` owns the
single execution and behavioral-policy semantics the sequential languages share.
`GameTheory.Analysis` is the one root that may reach fixed points, topology, and
the other analytic existence arguments; the architecture audits check that
boundary on every build.

Assumptions sit on the theorem or operation that needs them: finite support
belongs to a probability law, and finiteness of players or actions is requested
separately. Executable modules use explicit enumerations and computable scalars;
correctness modules connect them to the real-valued semantics.

## Scope

Probability is finite-support throughout, including laws on infinite carriers.
This is the one boundary worth knowing before you build on the library: results
needing a general measure over infinite play paths — measurable games, monitored
public randomization — live in focused experiments under
`GameTheory.Experimental`, not in the public roots.

Partial and queued theorem families are tracked in the
[delivery ledger](docs/DeliveryLedger.md).

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
