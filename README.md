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
- **Folk theorem (discounted, approximate)** — every strictly
  individually-rational feasible payoff vector of the mixed extension is
  approachable by Nash equilibrium payoffs of the infinite discounted repeated
  game as δ → 1, via an explicit trigger-strategy construction with finite
  cycle approximation and minmax punishment
- **MAID → EFG perfect recall preservation** — a MAID with perfect recall
  produces an EFG tree with perfect recall, using DAG topological ordering
- **Aumann's agreement theorem** — agents with a common prior who share an
  information-partition cell have equal posteriors ("agreeing to disagree" is
  impossible), with the full-agreement version on common self-evident events
  and an S5 knowledge operator (`Concepts/CommonKnowledge.lean`)

## Core abstractions

| Abstraction | Role |
|---|---|
| `GameForm` | Utility-free game: strategies, outcomes, stochastic kernel. Protocol-level constructions live in `Core/`; preference-parametric solution concepts over game forms live in `Concepts/GameFormSolutionConcepts.lean`. |
| `KernelGame` | `GameForm` + utility function. EU-based solution concepts (`IsNash`, `IsDominant`, …) live in `Concepts/SolutionConcepts.lean`. |
| `ObsModel` | Observation-indexed actions over a `DSMachine`. Canonical model for Kuhn's theorem. |
| `InfoModel` | State-based sequential game model with observations, actions, and signals. ODP and other sequential theorems are stated at this level. |

`Payoff ι` is just `ι → ℝ`. Probabilities are `PMF` (discrete distributions).
There are no continuous strategy spaces or measure-theoretic foundations.

## Solution concepts

The `Concepts/` directory defines ~40 interrelated notions, including:

- Nash equilibrium, strict Nash, approximate (ε-)Nash
- Dominant strategies, strict/weak dominance, iterated elimination
- Correlated and coarse correlated equilibrium, and the value of correlation
  (the welfare gap from the best pure Nash to the best correlated / coarse
  correlated equilibrium)
- Observable cheap-talk extensions and babbling-equilibrium transport
- Best response, best-response dynamics
- Mixed-extension gain tests, including uniform mixed balance ⇒ Nash and
  binary-labeled matching-pennies-style exact mixed equilibrium characterizations
- Security strategies (maximin), minimax guarantees, saddle points
- Potential games (exact, ordinal, weighted), finite improvement property
- Rationalizability, dominance solvability
- Evolutionary stable strategies (ESS)
- Price of anarchy — including smoothness and the robust PoA bound that extends
  from Nash to coarse correlated equilibria — individual rationality, social
  welfare
- Zero-sum, constant-sum, symmetric, and team game properties

Key relationships are proved: dominant strategies are Nash, Nash EU dominates
the security level, ESS implies Nash, Nash equilibria are correlated equilibria,
potential game maximizers are Nash.

The library keeps `Core/` dependency-light: it contains semantic structures and
protocol/distribution constructions. `Concepts/` contains preference-dependent
and EU-dependent predicates and transport theorems.

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

The NFG layer also includes canonical worked examples. For Matching Pennies it
now records both the absence of pure Nash equilibria and the exact fair mixed
Nash characterization.

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
- **Kuhn outcome-equivalence reduction**: the Intrinsic API proves full
  outcome-law equivalence from the player-local event-mass realization
  condition; the old behavioral-marginal statement is not exposed as Kuhn's
  theorem.

## Auctions and mechanism design

- First-price, second-price (Vickrey), all-pay, and VCG auctions
- Quasi-linear utility decomposition (allocation + payment)
- Bayesian games with type spaces
- Incentive compatibility (dominant-strategy and Bayesian)
- Revelation principle
- Dominant-strategy implementability: weak monotonicity is necessary for
  truthfulness, and affine maximizers — with VCG as the canonical case — are
  sufficient
- Hidden-action principal–agent contracts (moral hazard, linear contracts,
  the first-best benchmark)
- Finite information design / Bayesian persuasion (signal structures, Bayes
  plausibility, sender/receiver persuasion primitives), and feasible posteriors
  via the canonical splitting coupling (single- and multi-receiver)
- Social choice and aggregation, including one direction of **Arrow's
  impossibility theorem** (a dictatorial social welfare function satisfies
  Pareto and independence of irrelevant alternatives)

## Cooperative game theory

A parallel `Cooperative/` branch formalizes the cooperative tradition, whose
primitives are coalition value functions, feasible payoff sets, and preference
rankings rather than per-player strategies. It does **not** go through
`KernelGame` — apart from the player-index type and `ℝ` it shares no
load-bearing abstractions with the non-cooperative core, and lives in the same
package only for packaging convenience.

- **Coalitional (TU) games** — the **Shapley value** and its uniqueness via
  unanimity-game decomposition (efficiency, symmetry, dummy, additivity), the
  Banzhaf index and the Shapley–Shubik power index on simple games, convex
  (supermodular) games with the monotone-marginals characterization, the
  core (with nonemptiness for convex games), and the cost of stability
- **Bargaining** — the Nash bargaining solution for two-player problems
  (Pareto optimality, symmetry, affine invariance), the egalitarian (Kalai)
  solution, and the Kalai–Smorodinsky solution
- **Stable matching** — two-sided matching markets, blocking pairs, and
  **Gale–Shapley existence** of a stable matching via deferred acceptance

Note: "cooperative" here refers to the *formalism* (coalition-value functions,
axiomatic solutions), not to strategic games with aligned interests — those
(`IsTeamGame`, symmetric games) live in the non-cooperative `Concepts/` layer.

## Mathematical infrastructure

The `Math/` directory provides supporting libraries for discrete probability
(`PMF` products, marginals, conditioning), directed acyclic graphs (acyclicity,
topological orders), function/finset update lemmas, and local-to-global
optimization.

## Build

Requires Lean 4 (`v4.30.0`) and Mathlib (`v4.30.0`). Also depends on
[`fixed-point-theorems-lean4`](https://github.com/ldct/fixed-point-theorems-lean4)
for Brouwer/Kakutani.

```bash
lake exe cache get
lake build GameTheory Math Semantics
lake env lean scripts/AxiomAudit.lean
```

## Non-goals

- Continuous strategy spaces with non-discrete distributions
- Measure-theoretic probability
- Algorithmic equilibrium computation

## Countable-support PMFs

Strategy and outcome types can be countably infinite. `pmfPi` is defined
for any per-coordinate PMF family over a finite player index, and
`KernelGame.mixedExtension` inherits that generality. Expected-utility
lemmas (`expect_bind`, `expect_pushforward`, `expect_mono_of_pointwise`)
have bounded/countable siblings in `Math.Probability`; the pushforward API
also has an image-bounded variant for utility-distribution morphisms.
Concept-layer theorems such as `mixedExtension_eu`,
`weighted_gain_sum_zero`, `isNash_iff_gains_nonpos`, the mixed-Nash support
lemma, CE/CCE transport from mixed Nash, correlated-EU identities, OSD,
Zermelo, and EU morphism wrappers no longer need finite outcome carriers
when a bounded-utility hypothesis is supplied. Finite outcomes remain as
convenient wrappers that derive boundedness automatically.

Remaining finite assumptions are intentional proof boundaries:

- `mixed_nash_exists_of_bounded`, `correlatedEq_exists_of_bounded`, and
  `coarseCorrelatedEq_exists_of_bounded` remove finite outcomes but still
  require finite nonempty strategy spaces because the current proof is
  Brouwer-on-product-simplices. Removing that would require a different
  compactness/fixed-point theorem and continuity hypotheses for
  infinite-dimensional mixed spaces.
- Security levels now have sup/inf definitions (`worstCaseEUInf`,
  `securityLevelSup`) without finite profile/strategy enumerations. Existence
  of an attaining security strategy still requires finite/compact attainment
  hypotheses.
- `zermelo_of_bounded` and `oneShotDeviation_iff_spe_of_bounded` remove finite
  outcomes. They still rely on the finite game-tree/action structure for
  backward induction and local action maximization.
- Kuhn wrappers keep finiteness where they enumerate pure strategies,
  histories, or reachable information/action carriers. Removing those would
  require countable/integrable versions of the reweighting and pure-strategy
  product arguments.
- The CE/CCE theorem “mixed Nash induces CE/CCE” is now finite-strategy-free;
  the product-deviation identity is proved directly for arbitrary coordinate
  carriers over a finite player index.
- Von Neumann minimax and zero-sum interchangeability have bounded-utility
  variants without finite outcomes, but still depend on mixed Nash existence,
  hence on finite nonempty pure strategy spaces in the current development.

See `Languages/NFG/CountableExample.lean` for a smoke test exercising
`NFGGame` over `ℕ`-valued actions.
