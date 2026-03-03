# Systematic Analysis Workflow (Non-Final)

This workflow is intentionally iterative and backtrack-friendly.

## Operating Rules

1. Nothing is final.
2. Prefer prose over formalization.
3. Add at most one-shot independent lemmas.
4. Avoid framework-specific objects unless in explicit adapter notes.
5. Keep theorem statements in dependency-layer form.

## Dependency Layers

- `L0` Function/List Algebra
- `L1` Finite PMF Algebra
- `L2` Sequential Composition / Trace Semantics
- `L3` Format Adapters (keep thin and last)

## Analysis Loop

1. Pick one large theorem.
2. Write abstract goal shape.
3. List direct dependencies (current code).
4. Re-express each dependency by lowest layer possible.
5. Mark assumptions:
   - essential
   - likely removable
   - framework artifact
6. Extract at most one small lemma candidate.
7. Record what failed / what remains unclear.

## Backtracking Policy

When a decomposition fails:

1. Mark the failing edge in dependency graph.
2. Add one diagnostic question:
   - missing algebraic lemma?
   - missing semantic interface?
   - hidden definitional equality dependency?
3. Re-route through a different local statement instead of extending hierarchy.

