# Abstract Vocabulary (De-Gamified)

Purpose: remove intuitive game language and keep only structural semantics.

## Core Objects

1. `Coord`:
   index set for random coordinates.

2. `Assignment`:
   total map `Coord -> Value`.

3. `Observable`:
   function extracting an index-dependent read from state/context.

4. `Step Kernel`:
   stochastic transition from current state to next state.

5. `Process`:
   finite list composition of step kernels.

6. `Factorization`:
   way to realize random samples:
   - local per-observable sampling
   - global pre-sampled assignment

## Structural Properties

1. `Ignorant j F`:
   updating coordinate `j` does not change `F`.

2. `Separation`:
   current-step observables do not collide with future-step observables.

3. `Determinacy`:
   current observable value uniquely determines relevant history class.

4. `Reachable Congruence`:
   if two local laws agree on reachable observables, process outcomes agree.

## Target Theorem Schemas

1. Factorization Equivalence (easy direction):
   local factorization == global factorization under separation.

2. Realizability (hard direction):
   every global factorization admits equivalent local factorization under determinacy.
