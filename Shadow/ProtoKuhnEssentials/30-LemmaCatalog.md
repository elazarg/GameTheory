# Lemma Catalog (Essence + Cross-Field Names)

This is a non-final decomposition list.  
Each entry: statement shape, minimal assumptions, known aliases in other fields, and why it matters.

## L0-1. `curry_update`

### Shape

Updating a pair-indexed function and then currying equals currying and nested update.

### Minimal assumptions

- `DecidableEq` on index types used by `Function.update`.

### Known names elsewhere

- PL / semantics: *store update commutation* (for product locations).
- Lens-style algebra: *update fusion law*.
- Category-ish language: naturality of reindexing under product decomposition.

### Why useful

Removes proof noise where goals differ only by `update` placement.

---

## L0-2. Pointwise update-invariance fold (definition-free schema)

### Shape

If for every `j ∈ K` we have:

`∀ s a, F (Function.update s j a) = F s`,

then any finite sequence of updates along `K` leaves `F` unchanged.

### Minimal assumptions

- `DecidableEq` for updates.
- finite index set representation only where folding is used.

### Known names elsewhere

- Analysis / measure: *cylinder measurability dependence on complement coordinates*.
- Probabilistic graphical models (informal): coordinate-wise *irrelevance*.
- Program logics: *frame property* flavor (changes outside footprint do not matter).

### Why useful

It is the deterministic core behind “independence by irrelevance” PMF lemmas,
without introducing any new named predicate.

---

## L1-1. `pushforward_comp'`

### Shape

Pushforward along `f` then `g` equals pushforward along `g ∘ f`.

### Minimal assumptions

- None beyond PMF definitions.

### Known names elsewhere

- Probability: *law of the unconscious statistician* in compositional form.
- Category theory: functoriality of distribution pushforward.

### Why useful

Canonical normal form; prevents ad-hoc bind/map rewrites.

---

## L1-2. Product pushforward under coordinate maps

### Shape

Pushforward of product measure through coordinate-wise map equals product of pushforwards.

### Minimal assumptions

- Finite coordinate index and finite coordinate domains.

### Known names elsewhere

- Probability: *independence preserved under coordinate-wise measurable maps*.
- Measure theory: product-measure mapping theorem (discrete finite case).

### Why useful

Turns local coordinate transformations into pointwise factor rewrites.

---

## L1-3. Independence refactor via ignorance (`bind_partition_indep`-style)

### Shape

If one kernel depends only on coordinate block `J` and another depends on complement,
“same sample” and “fresh independent sample” are equivalent.

### Minimal assumptions

- Finite product PMF support assumptions.
- Ignorance hypotheses for partition sides.

### Known names elsewhere

- Probability: *conditional independence factorization*.
- Causal inference language (informal): variation in nuisance coordinates is irrelevant.
- Monte Carlo: valid resampling of independent blocks.

### Why useful

This is usually the technical hinge in easy-direction factorization proofs.

---

## L1-4. Bind disintegration (`pmf_bind_disintegrate`-style)

### Shape

A bind can be decomposed by first pushing forward via observable, then binding conditionals on fibers.

### Minimal assumptions

- Finite support for explicit filter normalization (in discrete PMF setting).

### Known names elsewhere

- Probability: *law of total probability* (distribution-valued form).
- Measure theory: *disintegration formula*.
- Bayesian inference: *mixture over posterior conditionals*.

### Why useful

Main bridge for constructive existence proofs (hard direction).

---

## L2-1. Tail transport of structural conditions

### Shape

A structural property on full process list induces corresponding property on tail/subprocess.

### Minimal assumptions

- Property must be suffix-stable by definition/proof.

### Known names elsewhere

- Operational semantics: *invariant under suffix restriction*.
- Temporal logic flavor: *future-closed invariants* (informal).

### Why useful

Needed in any induction over process lists.

---

## L2-2. Reachable-congruence of local kernels

### Shape

If two local kernels agree on observables reachable in a process, final outcome distributions agree.

### Minimal assumptions

- A notion of reachable observable support.
- Extensionality of step semantics in local-kernel argument.

### Known names elsewhere

- Semantics: *contextual equivalence on reachable states*.
- Model checking style: *bisimulation up to unreachable states* (informal analogy).

### Why useful

Allows replacement of branchwise constructions by a single global construction.

---

## L2-3. Separation implies ignorance of continuation

### Shape

If current-step observables do not collide with future-step observables, future evaluation ignores current-step coordinate edits.

### Minimal assumptions

- Separation predicate on observable names/indices.
- Functional update model for local kernels.

### Known names elsewhere

- Dataflow/compilers: *non-interference*.
- Program analysis: *disjoint footprint implies frame stability*.

### Why useful

It turns structural separation into probabilistic factorization preconditions.
