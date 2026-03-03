# Restriction and Transport

Goal:

- package theorem transfer across representation maps.

GameTheory-side patterns:

- “compiled model” equivalence,
- lifting predicates/results through map adapters.

Math-side target:

- abstract transfer schema:
  - eval preserved,
  - predicate preserved,
  - theorem transported.

Equivalent names:

- `Transport` (chosen):
  - structure: push a proved property through a map preserving required structure.
  - equivalent names: refinement transfer, compilation-preservation, model morphism lift.
- `Representation map` (chosen):
  - structure: interpretation-changing map preserving selected equations/predicates.
  - equivalent names: encoding, compilation map, abstraction/concretization link.

External-field fit:

- compiler correctness, model transformation, API refinement.

Candidate artifacts:

- compositional transfer combinators,
- map-chain transport lemmas,
- bidirectional transport under invertible maps.
