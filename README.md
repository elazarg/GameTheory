# GameTheory

[![CI](https://github.com/elazarg/GameTheory/actions/workflows/ci.yml/badge.svg)](https://github.com/elazarg/GameTheory/actions/workflows/ci.yml)

GameTheory is a Lean 4 library for finite and discrete game theory, built on
Mathlib. It provides shared semantics for static and sequential games together
with checked theorem families in equilibrium, learning, repeated and stochastic
games, mechanisms, social choice, epistemics, evolutionary stability,
cooperative games, matching, and congestion games.

The library favors useful mathematical interfaces over source compatibility:
one deviation API supports Nash, correlated, Bayesian, and refinement results;
language encodings compile into those shared semantics; executable algorithms
are connected to proof-level specifications by correctness theorems.

## Start here

Add the repository to a Lake project:

```lean
require GameTheory from git
  "https://github.com/elazarg/GameTheory.git" @ "main"
```

For reproducible work, replace `main` with a commit hash. Then run:

```text
lake update
lake build
```

The project pins Lean and Mathlib at `v4.32.2`.

For the stable static, sequential, epistemic, evolutionary, and executable
foundations:

```lean
import GameTheory
```

Specialized theorem families are explicit imports:

| Goal | Import |
|---|---|
| Pure and mixed games, preferences, Nash, CE/CCE, Bayesian games, welfare, learning foundations | `GameTheory.Core` |
| Protocol execution, histories, information, assessment, SPE, backward induction | `GameTheory.Protocol` |
| Finite pure-Nash enumeration and checked rational algorithms | `GameTheory` or the focused `GameTheory.Finite.Algorithm` / `GameTheory.Finite.Correctness` modules |
| Mixed-Nash existence, minimax, refinements, approachability, convergence | `GameTheory.Analysis` |
| Finite probability, DAGs, online learning, discounted sums, reusable geometry | `GameTheory.Math` |
| Repeated games, public monitoring, PPE, self-generation, uniform equilibrium | `GameTheory.Repeated` |
| Finite stochastic games, public policies, restart calculus, uniform payoffs | `GameTheory.Stochastic` |
| Auctions, Groves mechanisms, information design, implementation, fair division | `GameTheory.Mechanism` |
| Bargaining, matching, coalitional games, voting-power indices | `GameTheory.Cooperative` |
| NFG, EFG, FOSG, MAID, Bayesian, intrinsic, and multi-round encodings | the relevant `GameTheory.Languages.*` root |

`GameTheory.Math` is also a separate Lake target. It can be imported and built
without importing game definitions:

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

Useful entry points include:

- [`GameTheory/Examples/Classic.lean`](GameTheory/Examples/Classic.lean) for
  Prisoner's Dilemma, Matching Pennies, Battle of the Sexes, and a potential
  game;
- [`GameTheory/Examples/NFG.lean`](GameTheory/Examples/NFG.lean) for a
  countably infinite action carrier without executable enumeration;
- [`GameTheory/Examples/StochasticUniform.lean`](GameTheory/Examples/StochasticUniform.lean)
  for a nonconstant finite stochastic payoff and uniform bound;
- [`GameTheory/Tests/StochasticContinuation.lean`](GameTheory/Tests/StochasticContinuation.lean)
  for chronological histories and continuation/restart; and
- [`GameTheory/Tests/Bayesian.lean`](GameTheory/Tests/Bayesian.lean) for direct
  Bayesian and protocol-form Nash correspondence.

The [capability matrix](docs/CapabilityMatrix.md) indexes public workflows,
their exact imports, compiled consumers, and limitations. Readers coming from
the predecessor should use the [v1 capability map](docs/V1CapabilityMap.md),
which redirects mathematical workflows rather than preserving old declaration
names. The final predecessor revision remains available at tag `v1-final`.

## Mathematical organization

- `GameTheory.Math` owns reusable mathematics, including the canonical
  finite-support law `GameTheory.Math.Probability.FinDist`.
- `GameTheory.Core` owns static forms, utility, deviations, preferences, and
  solution concepts.
- `GameTheory.Protocol` owns the single execution and behavioral-policy
  semantics used by sequential languages.
- `GameTheory.Analysis` is an opt-in boundary for fixed points, topology, and
  other analytic existence arguments.
- Domain and language roots remain opt-in so their specialized assumptions do
  not enlarge the basic import.

Assumptions are placed on the theorem or operation that needs them. Finite
support belongs to a probability law; finiteness of players or actions is
requested separately. Executable modules use explicit finite enumerations and
computable scalars, while correctness modules connect them to real-valued
semantics.

## Scope

Current probability semantics use finite-support laws, including laws on
infinite carriers. The library does not model a general measure on infinite
play paths, and it does not claim general uniform-equilibrium existence for
stochastic games. Measurable games, monitored public randomization, and other
research-frontier surfaces are explored only through focused experiments.

Known partial or queued theorem families are recorded in the
[delivery ledger](docs/DeliveryLedger.md); a nearby module name is not treated
as evidence that an entire literature has been formalized.

## Development

The default build compiles all library modules, examples, tests, and recorded
experiments with warnings as errors:

```text
lake build
pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
```

The architecture and contribution rules are documented in
[`docs/GameTheory2Design.md`](docs/GameTheory2Design.md) and [`AGENTS.md`](AGENTS.md).
The project is licensed under the [MIT License](LICENSE).
