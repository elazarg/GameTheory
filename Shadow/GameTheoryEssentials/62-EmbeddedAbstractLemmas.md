# Embedded Abstract Concepts and Lemma Candidates

This file captures non-game-theoretic mathematical structure recurring across
the game-theory codebase.

## E1. Update-locality to global invariance

### Structural form

Pointwise invariance under coordinate updates implies invariance under finite
update compositions.

### Seen in

- trace/protocol proofs (`F3`)
- dominance/potential update arguments (`F5`)

### Candidate lemma shape

`(∀ j∈K, update-invariant j) -> fold-updates-invariant K`

### Other fields

- non-interference / frame rules

---

## E2. Evaluation congruence on reachable support

### Structural form

If two local maps agree on all coordinates/observables reachable in a process,
their global evaluations are equal.

### Seen in

- Kuhn-family proofs (`F3`)
- representation bridges (`F2`)

### Candidate lemma shape

`reachableAgree -> Eval f = Eval g`

### Other fields

- contextual equivalence restricted to reachable states

---

## E3. Disintegration-recombination of bind

### Structural form

Decompose bind by observable fibers, solve branchwise, recombine.

### Seen in

- mixed→behavioral constructions (`F3`)
- branchwise mechanism conditioning (`F6`)

### Candidate lemma shape

`bind μ k = bind (pushforward μ obs) (fiberConditional μ obs ▷ k)`

### Other fields

- law of total probability / disintegration

---

## E4. Independent-source refactor

### Structural form

Swapping “same source reused in continuation” with “fresh source” under
dependency partition assumptions.

### Seen in

- behavioral↔mixed equivalence (`F3`)
- correlated/mixed transformations (`F4`)

### Candidate lemma shape

`dependencyPartition -> sameSampleEqFreshSample`

### Other fields

- conditional independence factorization

---

## E5. Tail transport of structural constraints

### Structural form

A structural property on a full step list/tree transports to suffix/subtree.

### Seen in

- all inductive process proofs (`F3`, `F5`, `F7`)

### Candidate lemma shape

`P whole -> P tail`

### Other fields

- suffix-closed invariants

---

## E6. Translation-preservation skeleton

### Structural form

A representation map preserves evaluation and target predicates.

### Seen in

- bridge modules (`F2`)
- public packaging wrappers (`F3`, `F4`, `F7`)

### Candidate lemma shape

`translateEvalEq + predicateTransport -> theoremTransport`

### Other fields

- semantics-preserving compilation

---

## E7. Fixed-point transfer skeleton

### Structural form

Fixed-point identity of a normalized map implies inequality constraints that
characterize equilibrium-like predicates.

### Seen in

- mixed Nash existence (`F4`)

### Candidate lemma shape

`isFixedPt T x -> constraints x -> targetPredicate x`

### Other fields

- KKT-like algebraic transfer patterns (finite/discrete setting)

---

## E8. Well-founded extremization recursion

### Structural form

Local extremum selection + recursive decomposition yields global value/determinacy.

### Seen in

- minimax / zermelo / value files (`F7`, `F3`)

### Candidate lemma shape

`wfRec + finiteBranch + localExtremum -> globalOptimalValue`

### Other fields

- dynamic programming / Bellman recursion

