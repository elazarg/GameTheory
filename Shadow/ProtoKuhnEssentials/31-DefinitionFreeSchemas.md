# Definition-Free Lemma Schemas

These are reusable statement patterns using only existing primitives
(`Function.update`, `PMF.bind`, `pushforward`, finite sums/products).

## S1. Update-Fold Invariance

### Schema

If for all `j ∈ l`, `F (Function.update s j a) = F s`, then:

`F (l.foldl (fun s j => Function.update s j (vals j)) base) = F base`.

### Cross-field names

- program logics: frame/footprint stability under writes
- compiler analyses: non-interference of dead stores
- dynamical systems (discrete): inert coordinates

### Typical role

Bridge from pointwise invariance assumptions to finite batch rewrites.

---

## S2. Pushforward Composition Normal Form

### Schema

`pushforward (pushforward μ f) g = pushforward μ (g ∘ f)`.

### Cross-field names

- probability: compositional LOTUS
- category theory: functoriality of distribution mapping

### Typical role

Normalize nested maps/binds before larger algebraic transformations.

---

## S3. Coordinate-Wise Mapping of Product Law

### Schema

For coordinate-wise maps `g i`, pushforward of product = product of pushforwards.

### Cross-field names

- measure theory: image of product measure under product map
- probabilistic programming: map over independent random variables

### Typical role

Local-to-global transport of coordinate transformations.

---

## S4. Partitioned Independence Refactor

### Schema

Given a coordinate partition `(J, Jᶜ)`, if one kernel is invariant under edits in `Jᶜ`
and another is invariant under edits in `J`, then same-sample and fresh-sample binds are equal.

### Cross-field names

- statistics: conditional independence factorization
- causal inference: nuisance-variable irrelevance (informal)
- MCMC/MC methods: independent block resampling

### Typical role

Main swap step in local-vs-global randomization equivalence proofs.

---

## S5. Disintegrate Then Recombine

### Schema

Decompose:

`μ.bind g`

into observable-first mixture:

`(pushforward μ obs).bindOnSupport (fun b => (μ filtered on obs=b).bind g)`.

### Cross-field names

- probability: law of total probability (distribution-valued)
- measure theory: disintegration formula
- Bayesian inference: mixture of conditionals/posteriors

### Typical role

Core step in existential constructions (hard-direction proofs).

---

## S6. Reachable-Agreement Congruence

### Schema

If two local kernels agree on all observables reachable by a process,
their composed outcome distributions are equal.

### Cross-field names

- semantics: contextual equivalence on reachable states
- model checking: equivalence up to unreachable parts

### Typical role

Allows replacing branchwise witnesses by a single global witness.

---

## S7. Tail Transport

### Schema

A structural property on a full step list implies corresponding property on tail lists.

### Cross-field names

- inductive invariants under suffix restriction

### Typical role

Induction hygiene: avoids re-proving the same index plumbing repeatedly.

---

## Minimal-Assumption Checklist (per schema)

For each concrete instantiation, explicitly annotate:

1. finite types actually required?
2. decidable equality actually required?
3. support-nonempty requirement actually required?
4. framework-specific assumptions accidentally included?

