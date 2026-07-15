# GameTheory (Lean 4)

`GameTheory` is a Lean 4/mathlib library for finite and discrete game theory.
It formalizes strategic-form games, sequential games, mechanism design,
auctions, social choice, fair division, cooperative games, and the mathematical
infrastructure needed to connect them.

The main organizing idea is a common semantic target, `KernelGame`: strategy
spaces for each player, a stochastic outcome kernel, and utilities on outcomes.
Concrete representations such as normal-form games, extensive-form games,
multi-agent influence diagrams, multi-round games, factored-observation
stochastic games, and intrinsic-form games compile into this target. Solution
concepts are then stated once on the semantic core and reused across languages.

## Highlights

The library contains mechanized versions of several standard finite-game
theory results.

**Equilibrium and zero-sum games**

- Mixed Nash equilibrium existence for finite games, via Brouwer on product
  simplices.
- Correlated and coarse-correlated equilibrium existence.
- Von Neumann minimax for finite two-player zero-sum games.
- Security levels, saddle-point vocabulary, zero-sum and constant-sum structure.

**Sequential games**

- Zermelo/backward induction for finite perfect-information extensive games.
- The one-shot deviation principle for subgame-perfect equilibrium.
- Kuhn's behavioral/mixed equivalence, proved on an observation-model layer and
  instantiated for several concrete game representations.
- Perfect-recall preservation results for language bridges such as MAID to EFG.

**Learning and repeated games**

- Multiplicative weights with an explicit finite-horizon regret bound.
- No-regret play implies approximate coarse correlated equilibrium.
- Blackwell approachability and regret matching.
- Fictitious-play convergence facts, including the exact-potential-game route.
- An approximate discounted folk theorem for observable mixed-action repeated
  games.

**Mechanism design, auctions, and social choice**

- Bayesian games, finite information-design primitives, and a finite revelation
  principle.
- Dominant-strategy implementability: weak monotonicity, affine maximizers, and
  VCG as the canonical case.
- Single-parameter Myerson payments: monotonicity, envelope payments, DSIC, and
  uniqueness for zero-normalized continuous-slice payments.
- Vickrey, reserve Vickrey, first-price, all-pay, VCG, and knapsack auctions.
- Arrow, Gibbard-Satterthwaite, May's theorem, Condorcet, median voter, and
  Sen's liberal paradox.

**Fair division**

- Indivisible-goods EF, EF1, EFX, proportionality, and maximin-share
  definitions and existence results.
- EF1 allocations via envy-cycle and round-robin rules.
- Two-agent EFX for indivisible goods.
- Divisible cake-cutting on `[0,1]`: cut-and-choose, Dubins-Spanier
  proportionality, and Stromquist envy-free existence via KKM.

**Cooperative game theory and matching**

- TU coalitional games, the Shapley value, and Shapley uniqueness through the
  unanimity-game basis.
- Banzhaf and Shapley-Shubik power indices, convex games, core facts, cost of
  stability, and the easy direction of Bondareva-Shapley.
- Nash, egalitarian, and Kalai-Smorodinsky bargaining solutions.
- Gale-Shapley stable matching via deferred acceptance, proposer optimality,
  receiver pessimality, rural-hospitals invariants, and the lattice of stable
  matchings.

**Expected utility and mathematical support**

- A finite von Neumann-Morgenstern expected-utility representation theorem.
- Discrete probability support for `PMF`, products, conditioning, couplings, and
  bounded expected utility.
- Finite combinatorics, DAGs, finite-carrier transport, KKM covers, unit
  interval measure/cut lemmas, online learning, and fixed-point support.

## Architecture

The non-cooperative part of the library is organized as:

```text
Languages  ──compile──▶  KernelGame / GameForm  ──theorems──▶  solution concepts
```

`GameForm` is the utility-free protocol layer. `KernelGame` adds utilities and
expected-utility solution concepts. Preference-parametric versions of the
solution concepts live on `GameForm`; expected-utility specializations live on
`KernelGame`.

The dependency is directional: `GameTheory.Basic → GameForm → KernelGame →
Concepts`. Utility-independent constructors originate on `GameForm`; a
`KernelGame` version is a utility-preserving lift of that constructor. For
example, mixed extension is defined by `GameForm.mixedExtension`, while
`KernelGame.mixedExtension` reattaches the original utility. The repository
audit rejects imports from `GameTheory/Core` into downstream layers and keeps
the raw `GameForm` module independent of `KernelGame`.

The language layer treats concrete presentations as syntax plus semantics:

| Layer | Presentation |
|---|---|
| NFG | Simultaneous strategic choice |
| EFG | Extensive-form games with information sets |
| MAID | Graph-structured decisions and utilities |
| MultiRound | Protocol-based sequential and repeated games |
| FOSG | Factored-observation stochastic games |
| Intrinsic | Witsenhausen-style intrinsic information structures |

The cooperative branch is intentionally separate. Coalitional games, bargaining,
and matching do not compile to `KernelGame`; their primitives are coalition
values, feasible payoff sets, and preference rankings rather than strategic
profiles.

## Scope

The library is finite/discrete by design.

- Probability is represented by mathlib's `PMF`.
- Major existence theorems typically assume finite player and strategy/action
  carriers.
- Many expected-utility lemmas also have bounded-utility versions that do not
  require finite outcome types.
- Continuous strategy spaces, measure-theoretic mixed strategies, and
  continuous auction models are outside the current scope.
- Existence theorems using Brouwer or classical choice are generally
  `noncomputable`; this is a theorem library, not an equilibrium solver.

## Build

Requires Lean 4 (`v4.31.0`) and Mathlib (`v4.31.0`). The project also depends on
the pinned [`fixed-point-theorems-lean4`](https://github.com/elazarg/fixed-point-theorems-lean4)
fork for Brouwer/Kakutani-style fixed-point support.

```bash
git submodule update --init
lake exe cache get
lake build
python scripts/check_lean_placeholders.py
python scripts/audit_repository.py
```

## Repository Map

```text
GameTheory/Core/          semantic structures, morphisms, simulations
GameTheory/Concepts/      solution concepts, welfare, learning, knowledge
GameTheory/Languages/     NFG, EFG, MAID, MultiRound, FOSG, Intrinsic
GameTheory/Theorems/      high-level theorem packages
GameTheory/Mechanism/     mechanisms; Bayesian, SocialChoice, FairDivision, Contracts
GameTheory/Auctions/      auction formats and truthfulness results
GameTheory/Cooperative/   coalitional games, bargaining, matching
Math/                     project-local mathematical infrastructure
Semantics/                generic transition-system and trace infrastructure
latex/                    paper and definitional supplement
```

## Relation to EconCSLib

Several theorem packages are ports from
[`EconCSLib`](https://github.com/gametheoryinlean/EconCSLib), reworked against
this library's APIs and sometimes generalized or moved under `Math/` when the
result is not game-theoretic. Important examples include KKM covers, reserve
Vickrey auctions, zero-sum matrix games, the stable-matching lattice,
single-parameter Myerson payments, finite VNM representation, fair division, and
knapsack auctions.

## Paper

The `latex/` directory contains the paper source and definitional supplement.
The paper gives the narrative and proof architecture; the supplement is the
declaration-level map of the main definitions and theorems.
