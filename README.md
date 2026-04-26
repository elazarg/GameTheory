# GameTheory (Lean 4)

A formalization of finite game theory in Lean 4 / Mathlib, covering normal-form
games, extensive-form games, multi-agent influence diagrams (MAIDs),
factored-observation stochastic games (FOSGs), and their interconnections.

The library is organized around a single semantic target — `KernelGame` — that
packages strategy spaces, stochastic outcomes, and utility. Solution concepts
like Nash equilibrium, dominance, and correlated equilibrium are defined once on
this shared abstraction, then inherited by every concrete representation through
compilation and bridging.

## Theorems

Formal proofs of standard results in finite game theory:

- **Nash existence** — every finite game has a mixed Nash equilibrium
  (via Brouwer fixed point on product simplices)
- **Minimax** — von Neumann's minimax theorem for finite two-player zero-sum games
- **Kuhn's theorem** — equivalence of mixed and behavioral strategies under
  perfect recall, proved at a semantic model layer and instantiated for four
  game representations:
  - **EFG** — behavioral ↔ mixed for extensive-form games with information sets
  - **MAID** — behavioral policy ↔ product mixed strategy for multi-agent
    influence diagrams under DAG perfect recall
  - **Sequential** — behavioral ↔ mixed for protocol-based sequential games
  - **FOSG** — behavioral ↔ mixed for factored-observation stochastic games,
    via the bridge to `ObsModelCore` and natively in terms of FOSG histories
- **Zermelo / backward induction** — finite perfect-information games have
  pure subgame-perfect equilibria
- **One-shot deviation principle** — SPE characterization via single-step
  deviations
- **Correlated equilibrium existence** — every finite game has a correlated
  equilibrium
- **MAID → EFG perfect recall preservation** — a MAID with perfect recall
  produces an EFG tree with perfect recall, using DAG topological ordering

## Core abstractions

| Abstraction | Role |
|---|---|
| `GameForm` | Utility-free game: strategies, outcomes, stochastic kernel. Solution concept templates (`IsNashFor`, `WeaklyDominatesFor`, …) live here. |
| `KernelGame` | `GameForm` + utility function. All EU-based solution concepts (`IsNash`, `IsDominant`, …) are defined here. |
| `ObsModel` | Observation-indexed actions over a `DSMachine`. Canonical model for Kuhn's theorem. |
| `InfoModel` | State-based sequential game model with observations, actions, and signals. ODP and other sequential theorems are stated at this level. |

`Payoff ι` is just `ι → ℝ`. Probabilities are `PMF` (discrete distributions).
There are no continuous strategy spaces or measure-theoretic foundations.

## Solution concepts

The `Concepts/` directory defines ~40 interrelated notions, including:

- Nash equilibrium, strict Nash, approximate (ε-)Nash
- Dominant strategies, strict/weak dominance, iterated elimination
- Correlated and coarse correlated equilibrium
- Best response, best-response dynamics
- Security strategies (maximin), minimax guarantees, saddle points
- Potential games (exact, ordinal, weighted), finite improvement property
- Rationalizability, dominance solvability
- Evolutionary stable strategies (ESS)
- Price of anarchy, individual rationality, social welfare
- Zero-sum, constant-sum, symmetric, and team game properties

Key relationships are proved: dominant strategies are Nash, Nash EU dominates
the security level, ESS implies Nash, Nash equilibria are correlated equilibria,
potential game maximizers are Nash.

## Representations and bridges

The library treats game representations as *languages* with a uniform pipeline:
`Syntax → SOS → Compile → KernelGame`.

| Language | What it models |
|---|---|
| **NFG** | Simultaneous strategic choice (normal form) |
| **EFG** | Sequential play with information sets (extensive form) |
| **MAID** | Graph-structured decisions with chance, decision, and utility nodes |
| **Sequential** | Protocol-based sequential games, repeated games, stochastic games |
| **FOSG** | Factored-observation stochastic games: state-based, simultaneous moves, factored private/public observations, optional participation per player |
| **Intrinsic** | Witsenhausen's intrinsic model — information as equivalence relations on a product configuration space |

Bridges connect representations: MAID → EFG (topological unrolling, preserving
perfect recall and evaluation semantics), EFG ↔ NFG (strategic form extraction
and simultaneous-game embedding), FOSG → augmented-EFG (bounded-horizon
presentation with two-way distributional transport — a respectful EFG profile
maps back to a legal FOSG profile via `efgToFOSGProfile`, and outcome kernels /
expected utilities agree in both directions), NFG → FOSG (one-shot embedding),
and all languages compile to `KernelGame`.

## Kuhn's theorem — proof architecture

Kuhn's equivalence theorem (behavioral ↔ mixed strategies) is proved at the
`ObsModel` level — a multi-player observation model over a deterministic
stochastic machine (`DSMachine`). This is the canonical abstraction: players
observe state through per-player observation functions, and actions are
indexed by observations.

The proof decomposes into two independent directions:

- **B→M** (`BehavioralToMixed.lean`): constructs a joint distribution over
  pure profiles by taking products of per-step marginals. An involution/swap
  argument establishes scalar independence. **No recall conditions needed.**

- **M→B** (`CorrelatedRealization.lean`): starts with a correlated mediator
  realization (always exists), then decentralizes under progressively weaker
  recall conditions. The weakest sufficient condition is
  `TracePlayerStepRecall` (weaker than classical perfect recall).

Each concrete language compiles to `ObsModel` and applies the generic
theorems:

- **EFG**: Both directions proved for the outcome distribution and
  expected utility.
- **MAID**: Both directions proved for the native frontier evaluation
  semantics under DAG perfect recall (Koller & Milch).
- **Sequential**: Both directions proved for the native sequential
  evaluation semantics.
- **FOSG**: Both directions proved natively in terms of FOSG histories,
  legal behavioral profiles, terminal weights, and run distributions, plus
  re-exposed through the `ObsModelCore` bridge.

The Intrinsic form (`Languages/Intrinsic/`) formalizes Witsenhausen's intrinsic
model following Heymann, De Lara, and Chancelier (2020), where information is
represented as equivalence relations on a product configuration space rather
than as tree-based information sets. Key results:

- **Proposition 12**: product-mixed → behavioral (unconditional)
- **Proposition 13**: behavioral → product-mixed via product PMF over
  information classes, with the marginal identity proved using an equivalence
  `PureStrategy ≃ (InfoClass → Decision)`
- **Theorem 16 (Kuhn's equivalence)**: for any mixed strategy there exists a
  product-mixed strategy with matching behavioral marginals

## Auctions and mechanism design

- First-price, second-price (Vickrey), all-pay, and VCG auctions
- Quasi-linear utility decomposition (allocation + payment)
- Bayesian games with type spaces
- Incentive compatibility (dominant-strategy and Bayesian)
- Revelation principle
- Social choice and aggregation

## Mathematical infrastructure

The `Math/` directory provides supporting libraries for discrete probability
(`PMF` products, marginals, conditioning), directed acyclic graphs (acyclicity,
topological orders), function/finset update lemmas, and local-to-global
optimization.

## Build

Requires Lean 4 (v4.27.0) and Mathlib (v4.27.0). Also depends on
[`fixed-point-theorems-lean4`](https://github.com/ldct/fixed-point-theorems-lean4)
for Brouwer/Kakutani.

```bash
lake build          # full build
lake build GameTheory  # library only
```

## Non-goals

- Infinite or continuous strategy spaces
- Measure-theoretic probability
- Algorithmic equilibrium computation
