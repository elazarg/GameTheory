# GameTheory (Lean 4)

A Lean 4 formalization of finite discrete game theory, built on Mathlib. The library covers normal-form games, extensive-form games, and multi-agent influence diagrams (MAIDs), unified through a common semantic core (`KernelGame`). All probability is discrete (`PMF`); continuous/infinite spaces are out of scope.

## Overview

The central abstraction is `KernelGame ι`: a game with per-player strategy types, a stochastic outcome kernel, and a utility function. Solution concepts — Nash equilibrium, dominance, correlated equilibrium — are defined once on `KernelGame`. Concrete representations (NFG, EFG, MAID) bridge to `KernelGame` via `toKernelGame` conversions, inheriting all solution-concept theorems automatically.

The library includes 200+ formally verified theorems covering Nash equilibrium characterizations, dominance relations, zero-sum and constant-sum results, potential games, team games, Pareto efficiency, welfare theorems, correlated equilibrium, minimax, and Kuhn's theorem. All proofs are machine-checked with 0 `sorry`.

## Main Definitions

### Core Abstraction (`KernelGame.lean`, `SolutionConcepts.lean`)
- `KernelGame ι` — a game with per-player strategy types, stochastic outcome kernel, and utility
- `Profile G` — strategy profile (∀ i, G.Strategy i)
- `eu G σ i` — expected utility of player i under profile σ

### Solution Concepts (`SolutionConcepts.lean`)
- `IsNash G σ` — σ is a Nash equilibrium: ∀ i s', eu(σ, i) ≥ eu(σ[i↦s'], i)
- `IsDominant G i s` — s is a dominant strategy for player i
- `IsStrictNash G σ` — strict Nash: all deviations strictly decrease EU
- `IsBestResponse G i σ s` — s is a best response for i against σ
- `IsStrictDominant G i s` — s is a strict dominant strategy
- `WeaklyDominates G i s t` — s weakly dominates t
- `StrictlyDominates G i s t` — s strictly dominates t
- `IsCorrelatedEq G μ` — μ is a correlated equilibrium
- `IsCoarseCorrelatedEq G μ` — μ is a coarse correlated equilibrium

### Game Properties (`GameProperties.lean`)
- `IsZeroSum G` — zero-sum: ∀ ω, Σ_i u(ω, i) = 0
- `IsConstantSum G c` — constant-sum: ∀ ω, Σ_i u(ω, i) = c
- `IsTeamGame G` — identical interest: ∀ ω i j, u(ω, i) = u(ω, j)
- `IsExactPotential G Φ` — Φ is an exact potential function
- `IsOrdinalPotential G Φ` — Φ is an ordinal potential function
- `ParetoDominates G σ τ` — σ Pareto-dominates τ
- `IsParetoEfficient G σ` — σ is Pareto-efficient
- `IsIndividuallyRational G r σ` — σ satisfies reservation utilities r
- `socialWelfare G σ` — Σ_i eu(σ, i)

### Minimax (`Minimax.lean`)
- `Guarantees G i s v` — strategy s guarantees player i at least v
- `IsSaddlePoint G σ` — σ is a saddle point (2-player)

### Preference-Parameterized Variants (`SolutionConcepts.lean`)
- `IsNashFor G pref σ` — Nash w.r.t. arbitrary preference on outcome distributions
- `IsDominantFor G pref i s` — dominant w.r.t. preference
- `euPref G` — the standard EU preference (recovers `IsNash` from `IsNashFor`)

## Main Theorems

### Nash Equilibrium
- Nash ↔ all players play best responses (`isNash_iff_bestResponse`)
- Dominant-strategy profile is Nash (`dominant_is_nash`)
- Strictly dominant profile is the unique Nash (`strictly_dominant_unique_nash`)
- Strict Nash ⟹ Nash (`IsStrictNash.isNash`)
- Affine utility transformation preserves Nash (`ofEU_nash_affine`)
- Nash exists when all players have dominant strategies (`nash_of_all_have_dominant`)
- Nash exists in finite exact potential games (`exact_potential_nash_exists`)
- Saddle point ↔ Nash in 2-player games (`isSaddlePoint_iff_isNash`)

### Dominance
- Weak dominance: reflexive, transitive (`WeaklyDominates.refl`, `.trans`)
- Strict dominance: transitive, implies weak (`StrictlyDominates.trans`, `.toWeaklyDominates`)
- Strictly dominated ⟹ never a best response (`StrictlyDominates.not_nash`)
- Strictly dominant ⟹ unique best response (`IsStrictDominant.unique_best_response`)

### Correlated Equilibrium
- CE ⟹ CCE (`IsCorrelatedEq.toCoarseCorrelatedEq`)
- Pure Nash ⟹ CE (`nash_pure_isCorrelatedEq`)
- Pure Nash ⟹ CCE (`nash_pure_isCoarseCorrelatedEq`)
- Identity deviation is trivial (`deviateDistribution_id`)

### Zero-Sum and Constant-Sum Games
- Social welfare = c in constant-sum games (`IsConstantSum.socialWelfare_eq`)
- eu(σ, 0) = c − eu(σ, 1) in 2-player constant-sum (`IsConstantSum.eu_determined`)
- eu(σ, 0) = −eu(σ, 1) in 2-player zero-sum (`IsZeroSum.eu_neg`)
- Opponent's Nash deviation helps you in constant-sum (`IsConstantSum.nash_opponent_deviation_helps`)
- Nash strategy guarantees Nash payoff in constant-sum (`IsConstantSum.nash_guarantees_0`)

### Potential Games
- Exact potential ⟹ ordinal potential (`IsExactPotential.toOrdinal`)
- Potential maximizer is Nash (`IsExactPotential.nash_of_maximizer`)
- Improving deviation increases potential (`IsExactPotential.improving_deviation_increases_potential`)
- Team game is exact potential game (`IsTeamGame.isExactPotential`)

### Team Games
- All players have equal EU (`IsTeamGame.eu_eq`)
- Nash deviation doesn't improve any player (`IsTeamGame.nash_no_unilateral_pareto_improvement`)
- Zero-sum + team ⟹ all utilities zero (`IsZeroSum.teamGame_utility_zero`)

### Pareto Efficiency and Welfare
- Pareto dominance: irreflexive, asymmetric, transitive (`ParetoDominates.irrefl`, `.asymm`, `.trans`)
- Pareto-dominated ⟹ not efficient (`ParetoDominates.not_paretoEfficient`)
- IR monotone in reservation utility, preserved by Pareto improvement (`IsIndividuallyRational.mono`, `.of_pareto_dominates`)
- Team game social welfare = n · eu (`IsTeamGame.socialWelfare_eq`)

### Kuhn's Theorem (EFG)
- Behavioral → mixed equivalence under perfect recall
- Mixed → behavioral equivalence under perfect recall

## Game Representations

| Representation | File | Bridge to KernelGame |
|---|---|---|
| Normal form (NFG) | `NFG.lean` | `NFGGame.toKernelGame` |
| Extensive form (EFG) | `EFG.lean` | `GameTree.toKernel` |
| MAID | `MAID.lean` | `MAID.toKernelGame` |

Cross-representation bridges: NFG↔EFG (`NFG_EFG.lean`, `EFG_NFG.lean`), MAID→EFG (`MAID_EFG.lean`).

## Examples

- **Prisoner's Dilemma** with Nash equilibrium proof (`NFGExamples.lean`)
- **Matching Pennies** with no-pure-Nash proof (`NFGExamples.lean`)
- **Sequential games** with expected utility computation (`EFGExamples.lean`)
- **MAID examples** with evaluation equivalence (`MAIDExamples.lean`)

## Experimental

- `AbstractFolk.lean` — Folk theorem infrastructure (IR region properties). Contains one `sorry` placeholder for the full folk theorem statement.

## Building

```bash
lake build GameTheory   # ~1750 jobs, 0 errors
```

Requires Lean 4 + Mathlib v4.27.0.
