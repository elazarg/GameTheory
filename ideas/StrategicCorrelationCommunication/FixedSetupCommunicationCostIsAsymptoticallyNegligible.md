# Fixed setup communication cost is asymptotically negligible

## Lifecycle card

| Field | Value |
|---|---|
| Lifecycle | `ACTIVE` |
| Status | `PROVED (M+L), accounting only` |
| Priority | `P2` |
| Provenance | Elementary Cesaro bound and the finite public-coin selection-phase accounting library |
| Audited | 2026-08-03 |
| Consumer | Communication-cost objections to uniform-equilibrium and endogenous-public-randomness constructions |
| Formalization destination | Generic prefix-charge results already live in `PublicCoinSelectionPhase`; optional bounded-payoff symmetric-difference corollary |
| Formalization status | One-sided prefix charge and deviation accounting are landed; this file records the standard two-path bounded-payoff corollary |
| Reactivation / exit | Exit after compiler proposals cite the prefix theorem and isolate irreversible/incentive costs; reactivate for accuracy-dependent or repeated communication phases |

## Claim ledger

| ID | Claim | Status |
|---|---|---|
| FIX-COST-1 | If two bounded-payoff plays differ in at most a fixed `L` stages, their `N`-stage average payoff difference is at most `2ML/N`. | `PROVED, elementary` |
| FIX-COST-2 | A fixed finite prefix charge vanishes in the Cesaro limit. | `PROVED (M+L)` |
| FIX-COST-3 | Therefore a fixed number of communication bits or stages is, by itself, an asymptotic payoff obstruction. | `REFUTED as a standalone claim` |
| FIX-COST-4 | Vanishing average charge makes the communication phase strategically or physically harmless. | `FALSE inference` |

## Intuition

A bounded prefix occupies a vanishing fraction of a long horizon. Its direct payoff charge therefore disappears under Cesaro averaging. The difficult question is whether those early actions permanently alter the state, information, deviation incentives, or continuation—not how many bits they encode.

## Mathematical statement

Suppose stage payoffs satisfy `|g_t|,|g'_t| <= M` and the two payoff streams differ on at most `L` dates. Then

\[
\left|
\frac1N\sum_{t=1}^N g_t
-
\frac1N\sum_{t=1}^N g'_t
\right|
\le
\frac1N\sum_{t:g_t\ne g'_t}|g_t-g'_t|
\le
\frac{2ML}{N}.
\]

For fixed `M` and `L`, this converges to zero as `N` tends to infinity. More generally, if a finite selection phase incurs total charge at most `C`, its direct contribution to the `N`-stage average is at most `C/N`.

Uniform-equilibrium quantifiers do not change this basic accounting: for each requested error `epsilon`, a compiler may use a finite setup length `L(epsilon)`, after which the horizon threshold can be chosen large enough that `2 M L(epsilon)/N <= epsilon`, provided the phase is otherwise safe. What fails is a bound with positive asymptotic invocation density or uncontrolled horizon-dependent setup length.

## Evidence

- [`PublicCoinSelectionPhase.lean`](../../GameTheory/Concepts/Stochastic/PublicCoinSelectionPhase.lean) proves exact prefix-cost and Cesaro average bounds, including lower, upper, and unilateral-deviation charge variants.
- [`FinitePublicCoinStoppedExpectation.lean`](../../GameTheory/Concepts/Stochastic/FinitePublicCoinStoppedExpectation.lean) supplies the stopped-selection expectation interface used by the phase accounting.
- [`OneStepDeviationSafePublicCoinSelector.lean`](../../GameTheory/Concepts/Stochastic/OneStepDeviationSafePublicCoinSelector.lean) shows how a finite action-independent selector can feed an adaptive certificate once its strategic hypotheses hold.

The elementary `2ML/N` estimate is the symmetric bounded-stream version of the same prefix principle. No claim of a complete compiler is made.

## What the bound does not buy

Average-payoff smallness controls the direct numerical charge only. A one-stage action can have a permanent effect even when its immediate payoff contribution is `O(1/N)`:

- it can move the game into an absorbing or otherwise irreversible state;
- it can reveal private information and destroy an obedience inequality;
- a deviator can bias the sampled continuation;
- the intended continuation may start from the wrong state or public memory;
- failed or repeated sampling can occur at positive density;
- the required `L(epsilon)` may interact with other error bounds or lack a uniform tail guarantee.

Thus the relevant obstruction is not “communication takes `k` stages” but the absence of a payoff-safe, transition-safe, deviation-safe, and information-compatible splice.

## Falsifiers

FIX-COST-1 would fail only without bounded payoffs, without a bound on the number/total magnitude of changed stages, or under a payoff criterion where a finite prefix is not Cesaro-negligible.

The intended application is falsified if the setup changes later payoffs or states: then the streams do not differ on only `L` dates, so the theorem's hypothesis is absent. Likewise, if a phase is invoked linearly often, its total charge can be `Theta(N)` rather than `O(1)`.

## Exit condition

Treat fixed finite setup cost as closed accounting. Future work should quantify the actual obstruction: irreversibility, disclosure, deviation bias, failed recovery, positive-density use, or accuracy-dependent error propagation. Do not promote ordinary bit complexity alone as a uniform-equilibrium barrier.
