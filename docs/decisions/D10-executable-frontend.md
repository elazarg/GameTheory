# D10: a separate executable rational finite-game frontend

- **Status:** accepted
- **Date:** 2026-07-26
- **Experiment IDs:** EXP-007

**Decision:** Keep a `TableGame` frontend over finite carriers and exact
rational payoffs, in its own dependency root, and prove every boolean procedure
correct against the semantic predicates of `GameTheory.Core`.

## Layering

```text
GameTheory.Core.Signature      shared signatures and profile operations, no probability
GameTheory.Finite.Algorithm    data, enumeration, boolean procedures, ℚ only
GameTheory.Finite.Correctness  imports Core and real-valued semantics
```

Splitting `GameSignature`/`Profile` out of the probability layer is what lets
the executable frontend use `Profile.update` instead of its own copy of
`Function.update`, so RFC 7.1's "no `Function.update` outside the profile
implementation" holds across both layers.

## Procedures and their correctness theorems

| Procedure | Correctness theorem |
|---|---|
| `isNash` | `isNash_eq_true_iff` |
| `enumerateNash` | `mem_enumerateNash_iff` |
| `weaklyDominates` | `weaklyDominates_eq_true_iff` |
| `strictlyDominates` | `strictlyDominates_eq_true_iff` |
| `isDominant`, `isDominantProfile` | `isDominantProfile_eq_true_iff` |
| `paretoDominates`, `isParetoEfficient` | `paretoDominates_eq_true_iff`, `isParetoEfficient_eq_true_iff` |
| `eliminateRound`, `survivors` | `mem_survivors_iff` |
| `expectedPayoff`, `verifyMixedNash` | `expectedUtility_toMixed`, `verifyMixedNash_eq_true_iff` |

`verifyMixedNash_eq_true_iff` is the D2 kill test "NFG mixed extension using the
final signature API". It needs `isNash_mixed_iff` — a randomized deviation in
the mixed extension is a mixture of pure ones — and `FinDist.ofWeights` to
compile a rational weight vector into the semantic law. No second mixed-game
API appears.

## Dependency budget, measured

Authored-import checks cannot see Mathlib's transitive closure, so the audit
elaborates probe files instead and requires the named constant to be unknown:

| Root | Must not reach | Result |
|---|---|---|
| `GameTheory.Finite.Algorithm` | `Real.instAdd` | unreachable |
| `GameTheory.Finite.Algorithm` | `PMF` | unreachable |
| `GameTheory.Finite.Algorithm` | `MeasureTheory.Measure` | unreachable |
| `GameTheory.Finite.Algorithm` | `stdSimplex` | unreachable |
| `GameTheory.Core` | `stdSimplex` | unreachable |
| `GameTheory.Core` | `Polynomial` | unreachable |

The algorithm module contains no `open Classical`, `classical`,
`noncomputable`, or `Fintype.ofFinite`.

## Executable examples

Prisoner's Dilemma, Matching Pennies, Battle of the Sexes, and a three-player
unanimity game, each with `#guard` regression tests and `#eval` output, in
`GameTheory/Examples/Classic.lean`.

## Unexpected cost

Kernel `decide` cannot evaluate rational arithmetic. `Rat.add` and `Rat.blt` do
not reduce, so `decide` fails on `(0 : ℚ) ≤ 1/2`. Consequences:

- pure-Nash, dominance, and Pareto facts still `decide`, because they only
  compare payoff literals;
- mixed-profile checks are *run* by compiled evaluation (`#guard`, `#eval`) and
  *proved* by `norm_num` after expanding the profile enumeration explicitly
  (`pennyProfiles`, `sum_pennies`);
- `native_decide` would remove the obstacle but adds a compiler-trust axiom, so
  it is excluded and used nowhere.

This is a toolchain fact, not evidence against the rational representation: the
representation is exactly what makes the executable answers exact.

## Kill condition

Change the concrete representation if evaluation requires classical choice,
opaque real arithmetic, or large proof terms at runtime. None of these
occurred; the frontend evaluates by compiled code with no classical reasoning.

## Result

Accept. An equilibrium *solver* remains out of scope; exact finite mixed
equilibria need not have rational coordinates, so the frontend verifies a
supplied rational profile rather than searching for one.
