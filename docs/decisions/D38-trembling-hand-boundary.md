# D38: perturbations stay in Core; perfection crosses into Analysis

- **Status:** adopted and promoted
- **Date:** 2026-08-09
- **Experiment ID:** EXP-071

## Decision / question

Whether normal-form trembling-hand refinement belongs entirely in stable Core,
entirely behind the analytic boundary, or should split topology-free
perturbation semantics from limit-based perfection.

## Competing designs

1. Put perturbations, restricted equilibrium, convergence, and perfection in
   Core.
2. Put the entire refinement surface in Analysis.
3. Put real lower bounds and restricted deviations in Core, reuse canonical
   `IsEquilibrium` there, and put pointwise convergence and perfection in a
   one-way Analysis leaf.

Design 3 is adopted. A perturbation is only a coordinatewise real lower bound
on canonical finite-law mass. A perturbed unilateral deviation is an ordinary
constant unilateral replacement carrying a lower-bound certificate. Neither
construction needs topology. Limits of profiles and perturbations do, so they
belong in `GameTheory.Analysis.TremblingHand`.

## Representative hostile slice

The general theorem takes a full-support mixed Nash profile and proves it is
trembling-hand perfect. At stage `n`, the lower bound on each action is its
target mass scaled by `1 / (n + 2)`; the approximating equilibrium is the
target profile itself. Positivity comes from full support, feasibility from the
weight being at most one, optimality from the original Nash certificate, and
the perturbation converges pointwise to zero.

Fair Matching Pennies is the concrete witness. Both actions have positive
mass, the existing canonical mixed-Nash proof supplies the equilibrium, and a
separate checked theorem says the game has no pure Nash equilibrium. The slice
therefore cannot pass through a point mass or singleton shortcut.

## Measurements

| Measure | EXP-071 result |
|---|---|
| Core owner | `GameForm.Perturbation`, respect/positivity, constrained deviations, and `IsPerturbedEq` |
| Analysis owner | pointwise profile convergence, vanishing perturbations, and `IsTremblingHandPerfect` |
| canonical reuse | perturbed equilibrium is `IsEquilibrium` for `DeviationScheme.perturbedMixed`; its hom maps into `unilateralConstant` |
| stored capabilities | none; finiteness and decidable equality occur only where the deviation scheme needs finite players |
| representation | real `FinDist.prob` only; no PMF, ENNReal, or second probability carrier |
| hostile distinction | fair Matching Pennies is fully mixed and perfect while admitting no pure Nash profile |
| bounded accounting | all 26 pinned declarations classified; 20 adapted/subsumed and six alternative-limit rows deferred |
| boundary correction | an Analysis-importing fixture under `Tests` was rejected and moved under `Analysis`; no source-check exemption was added |
| source checks | zero forbidden imports, raw `Function.update`, representation leaks, source transports, placeholders, custom axioms, or build-output commands |
| trust sample | the characterization, general perfection theorem, and hostile witness use only `propext`, `Classical.choice`, and `Quot.sound` |
| reachability | Core inputs reached 3/3 and analytic names rejected 2/2; Analysis inputs reached 5/5 and unrelated boundaries rejected 4/4 |
| release validation | Phase 2 and exact coverage return `VERIFIED=1`; warning-clean default build completes 3,517 jobs |

## Kill condition

Reject the split if Core needs topology; the refinement requires a parallel
Nash predicate; PMF/ENNReal representation escapes `FinDist`; the proof needs
raw updates or user-visible transports; full-support Nash cannot furnish a
positive vanishing certificate; or the hostile fixture does not exercise
genuine mixing.

No kill condition fired. The source audit instead caught and corrected the
fixture's directory-level boundary violation, which is evidence that the
one-way rule is enforced rather than descriptive.

## Consequences for the public API

Topology-free consumers import `GameTheory.Core.TremblingHand`. Limit-based
consumers import `GameTheory.Analysis.TremblingHand`. Expected-utility
perfection is a transparent `UtilityGame` specialization; new refinement
theorems continue to use canonical `IsNash`, `IsEquilibrium`, `Profile.update`,
and `FinDist`.

The predecessor's fully-mixed-equilibrium and vanishing-approximate-Nash limit
predicates remain a bounded S-MIX BFS gate because they express distinct
notions. Sequential-assessment recovery remains in the existing
Analysis/Protocol owner and is not folded into this normal-form leaf.
