# Geometry Layer (AbstractFolk-Style, Non-Domain First)

Goal:

- incorporate a region-based abstraction (`F`, lower-bound vector `V`, intersection region `IR`) as a reusable layer,
- keep it independent of specific game encodings and story terms.

## G-Region primitives

Assume:

1. finite index set `I`,
2. ambient vector space `R^I` (concretely `Fin n -> R` in Lean),
3. feasible set `F : Set X`,
4. floor vector `V : X`,
5. region `IR(F,V) := {x | x ∈ F ∧ V ≤ x (coordinatewise)}`.

This is exactly a geometry/filter layer; no strategy/history object is needed.

## Core facts (already aligned with mathlib style)

1. coordinate lower halfspaces are closed,
2. finite/all-coordinate lower set is closed,
3. `F` closed implies `IR(F,V)` closed,
4. `F` compact implies `IR(F,V)` compact,
5. `F` convex implies `IR(F,V)` convex.

These are pure topology/convexity facts and can be developed without `GameTheory` imports.

## Where this plugs into theorem families

- F4 (existence): bridge from equilibrium payoff statements to fixed-point/compactness assumptions.
- F7 (welfare/minimax/value): separates objective geometry from strategic construction.
- F6 (mechanism): separates feasible-transfer inequalities from format-specific truthfulness predicates.

## Structural mapping

Introduce a provisional additional global block:

- `B11` feasible-region geometry:
  closedness/compactness/convexity transport for intersections with coordinate halfspaces.

`B11` is complementary to:

- `B8` (continuity/convex transfer through maps),
- `B9` (inequality rearrangement).

## Extraction rule

When a theorem mixes geometric and strategic content:

1. isolate the geometric statement as a standalone `B11` lemma over sets/functions,
2. keep strategic assumptions only in the adapter theorem that instantiates `F` and `V`,
3. avoid new wrapper definitions unless they remove repeated quantifier noise.
