# Zermelo-Style Decomposition (Abstract)

Status: exploratory, not final.

## Z0. Large Theorem Shape

For a finite well-founded decision process with ordered terminal outcomes:

1. a recursive selector map exists (backward recursion),
2. it is optimal at each subprocess,
3. resulting value is determined by alternating extremization.

No game wording required.

## Z1. Core Structural Model

- Well-founded transition graph over trace-prefixes.
- At each nonterminal node: finite action set.
- Terminal evaluator to an ordered codomain.

## Z2. Proof Skeleton

1. Define recursive value functional (`L0`/well-founded recursion).
2. Prove local optimality step:
   - maximizing/minimizing chooser attains extremum on finite set.
3. Lift local optimality to global by recursion induction.
4. Prove determinacy / forced-bound formulation equivalent to value recursion.

## Z3. Assumption Audit

- essential:
  - well-foundedness/finite horizon
  - finite branching
  - ordered outcome codomain
- likely removable:
  - explicit tree datatype if traces already prefix-closed
- framework artifact:
  - player decomposition labels

## Z4. One-Shot Lemma Candidates

1. finite argmax/argmin attainment wrappers,
2. prefix-trace recursion equivalence to explicit tree recursion,
3. local-step optimality implies recursive optimality (single induction carrier).

## Z5. Backtracking Log

- Open.
- If recursion proof gets stuck, record:
  - missing monotonicity lemma?
  - missing finite attainment helper?
  - wrong induction carrier (tree node vs trace)?
