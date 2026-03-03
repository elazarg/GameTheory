# Audit: `EFGKuhnFull.lean` (Structure-First)

Scope: major theorems near the mixed→behavioral pipeline.

Reference constraints: `A1..A8` from `40-StructuralCore.md`.

## Module-level observation

- This file is mostly an instance of `T2` (existential local reconstruction) plus packaging.
- Many local lemmas are adapter-heavy to the concrete EFG encoding.
- Reusable core patterns are concentrated in:
  - conditional decomposition,
  - invariance of marginals under filtered conditioning,
  - subtree evaluation induction.

## Theorem audit

## `muCond_disintegration` (line ~971)

- Role: direct instance of `A7` (disintegrate bind by observable fiber).
- Structural layer: `L1`.
- Essential assumptions:
  - finite support/discrete PMF setting (`A1`-side finite sums),
  - observable projection map.
- Likely accidental assumptions:
  - concrete `FlatProfile` coordinate encoding.
- Extraction candidate:
  - one generic theorem schema `disintegrate_bind_by_coordinate`.

## `mixedToBehavioral_context_eq` (line ~988)

- Role: branchwise context identity used by main induction.
- Structural layer: `L2` + adapter.
- Uses:
  - `A4` (determinacy through perfect-recall path identity),
  - `A5` (reachable-congruence style replacement),
  - `A6` (tail/path transport).
- Essential assumptions:
  - determinacy of filtered path representation.
- Likely accidental:
  - concrete `DecPath`, `GoodPath` witness encoding.
- Extraction candidate:
  - generic lemma: if two branch contexts induce same reachable read class, local kernel terms are equal.

## `eval_subtree_decision_step` (line ~1068)

- Role: one-step inductive transition at decision node.
- Structural layer: `L2`.
- Uses:
  - `A2` (update algebra on local map),
  - `A4/A5` (context determines branch + congruence).
- Essential assumptions:
  - read determinacy at this step.
- Likely accidental:
  - explicit player/infoset indexed wrappers in statement.
- Extraction candidate:
  - `decision_step_rewrite` schema over abstract step constructor.

## `eval_subtree_correct` (line ~1200)

- Role: main structural induction proving conditioned-evaluation equivalence on subtrees.
- Structural layer: `L2`.
- Uses:
  - `A6` tail closure,
  - `A7` disintegration facts,
  - branchwise step lemma above.
- Essential assumptions:
  - finite branching, deterministic read-to-subtree relation.
- Likely accidental:
  - explicit subtree/reachability witness transport details.
- Extraction candidate:
  - generic theorem `subprocess_eval_correct_by_path_induction`.

## `rhs_eq_flat_bind` (line ~1257)

- Role: representation-bridge equality.
- Structural layer: `L3` adapter.
- Uses:
  - representation equivalence + map/bind normalization.
- Essential assumptions:
  - translation correctness only.
- Accidental:
  - none major; this is appropriately adapter-level.

## `mixed_to_behavioral_nplayer` (line ~1283)

- Role: end-to-end existential result in flat representation.
- Structural layer: `T2` composition.
- Uses:
  - `eval_subtree_correct` + algebraic bridge lemmas.
- Essential assumptions:
  - `A1,A4,A5,A6,A7` (via previously proved chain).
- Likely accidental:
  - explicit player-index wrappers in theorem surface.

## `kuhn_mixed_to_behavioral` / `_udist` (lines ~1297, ~1327)

- Role: thin packaging to public theorem/API.
- Structural layer: `L3`.
- Status:
  - good as adapters; heavy proof should stay below.

## Immediate reusable extractions from this module

1. Generic disintegration-use lemma for branchwise recombination (`A7`-centric).
2. Reachable-context congruence lemma (generalizes `mixedToBehavioral_context_eq`) (`A5`).
3. Path-filter determinacy transport lemma (generalizes `FilterPlayer_path_eq_history`) (`A4/A6`).

