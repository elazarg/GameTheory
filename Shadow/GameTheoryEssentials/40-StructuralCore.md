# Structural Core (Name-Later Style)

This note intentionally avoids intuitive labels.
Start from structure, keep names provisional, add intuition only after stable decomposition.

## S0. Primitive Signatures

Assume only:

1. `I` : finite index type.
2. `X` : global assignment space (`I -> Xi` form, but not fixed as a def).
3. `Ω` : observable space.
4. `Σ` : latent exogenous signal space (optional).
5. `S` : state space.
6. `K` : step-kernel constructor (from local read + state to `PMF S`).
7. `Eval` : finite list composition of kernels.
8. `Obs` : read map extracting coordinate queries used at a step.

No semantic interpretation required.

## S1. Structural Constraints (Axioms/Interfaces)

Use numbered constraints, not named concepts.

- `A1` (Finite Product): product PMFs over `I` are available.
- `A2` (Update Algebra): `Function.update` laws + fold transport.
- `A3` (Read Separation): step-0 reads are disjoint from tail reads.
- `A4` (Read Determinacy): current read class determines required branch class.
- `A5` (Reachability Congruence): equal local kernels on reachable reads imply equal `Eval`.
- `A6` (Tail Closure): `A3/A4/A5` transport to suffixes.
- `A7` (Disintegration): bind decomposes over read fibers.
- `A8` (Independent Refactor): partitioned dependency permits fresh-resample swap.
- `A9` (Region Envelope): feasible set intersected with coordinate floors preserves
  closed/compact/convex properties under stated ambient assumptions.

## S2. Major Theorem Schemas

### T1 (Factorization Equivalence)

Given `A1,A2,A3,A6,A8`, prove:

`Eval(local-factorized source) = Eval(global-factorized source)`.

This is induction on step list + one local refactor.

### T2 (Existential Local Reconstruction)

Given `A1,A2,A4,A5,A6,A7`, prove:

`∃ local source, Eval(local source) = Eval(given global source)`.

This is induction + branch disintegrate/recombine.

### T3 (Packaging)

Any concrete format theorem should be:

`FormatAssumptions -> (A1..Ak)` + `T1/T2`.

No heavy proof content in T3.

## S3. Design Rule

Before introducing any new named definition:

1. Try expressing the needed step as one of `A1..A8`.
2. If not possible, add one new constraint slot `A9` in this document first.
3. Only then consider adding a definition in code.

## S4. Cross-Field Correspondence (Only after structure fixed)

- `A8`: conditional-independence swap / Fubini-style bind refactor.
- `A7`: disintegration / mixture decomposition.
- `A5`: contextual equivalence on reachable support.
- `A2`: store-update algebra / frame-style invariance.

Treat these as mnemonic aliases, not primary formulation.
