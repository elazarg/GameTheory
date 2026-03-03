# Audit: `EFGKuhn.lean` (Structure-First)

Scope: behavioral↔mixed equivalence at base EFG level.

Reference constraints: `A1..A8` from `40-StructuralCore.md`.

## Module-level observation

- Easy direction is a near-direct `T1` instance:
  - local factorization + non-repetition/separation + induction.
- Hard-direction content appears in specialized helper chain but still centers on:
  - context conditioning,
  - reachable agreement,
  - subtree-local reconstruction.

## Theorem audit

## `PerfectRecall_implies_NoInfoSetRepeat` (line ~107)

- Role: adapter from strong structural recall to separation/non-repeat condition.
- Structural layer: `L3` adapter (feeds `A3`).
- Essential assumptions:
  - recall condition with path/history equality consequences.
- Extraction candidate:
  - abstract adapter form: determinacy/recall ⇒ read-separation.

## `evalDist_pure_eq_of_agree` (line ~139)

- Role: canonical reachable-agreement congruence.
- Structural layer: `A5` prototype.
- Essential assumptions:
  - extensional dependence of evaluation on visited reads only.
- Likely accidental:
  - concrete `DecisionNodeIn` witness machinery in statement.
- Extraction candidate:
  - generic “evaluation depends only on reachable coordinates”.

## `behavioral_to_mixed` (line ~164)

- Role: main easy-direction theorem.
- Structural layer: `T1`.
- Uses:
  - product factorization at decision step,
  - separation-to-invariance argument,
  - induction over tree structure.
- Essential assumptions:
  - finite product support (`A1`),
  - separation/non-repeat (`A3`),
  - update algebra (`A2`),
  - structural induction carrier (`A6`-like closure).
- Likely accidental:
  - explicit profile flattening details in theorem surface.

## `evalDist_eq_of_behavioral_agree` (line ~897)

- Role: behavioral-version reachable-agreement congruence.
- Structural layer: `A5`.
- Essential assumptions:
  - same as `evalDist_pure_eq_of_agree` but at kernel profile level.

## `mixed_to_behavioral_flat` (line ~945)

- Role: hard-direction reconstruction in restricted setting.
- Structural layer: `T2` fragment.
- Uses:
  - branch/local reconstruction lemmas (`mixedToBehavioralFlat_*`),
  - determinacy assumptions encoded as single-actor subcondition.
- Essential assumptions:
  - determinacy for branch-local representation,
  - finite conditioning machinery.
- Likely accidental:
  - specific restriction `hsp` shape could be abstracted as `A4`.

## `kuhn_behavioral_to_mixed` / `_udist` (lines ~1047, ~1057)

- Role: public packaging of easy direction.
- Structural layer: adapter.
- Status:
  - good thin wrappers.

## Immediate reusable extractions from this module

1. One generic reachable-agreement lemma subsuming both `evalDist_*_agree` variants.
2. Adapter lemma family: recall-like property ⇒ separation condition needed by `T1`.
3. Abstract decision-step factorization lemma independent of EFG naming.

