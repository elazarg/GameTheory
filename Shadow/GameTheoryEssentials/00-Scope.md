# Scope (Game-Theory Modules Only)

This analysis intentionally excludes probability-only abstraction files.

Excluded from scope:

- `GameTheory/PMFProduct.lean`
- `GameTheory/Probability.lean`

Included:

- game-form and extensive-form modules
- protocol/sequential modules
- equilibrium/concept modules
- mechanism/auction/social-choice modules
- conversion/bridge modules (EFG↔NFG↔MAID↔Protocol)

Primary goal:

Extract minimal, definition-free theorem shapes and assumptions from game-theory proofs,
keeping format-specific assumptions in thin adapters.

