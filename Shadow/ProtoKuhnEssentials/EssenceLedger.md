# Essence Ledger (Framework-Agnostic)

This is a theorem-architecture note, not an implementation file.
It intentionally avoids any framework-specific object model.

## Method

For each major theorem, isolate:

1. **Goal Shape**: compositional form of the theorem.
2. **Minimal Assumptions**: weakest plausible assumptions.
3. **Dependency Layers**:
   - `L0`: pure function/list algebra
   - `L1`: probability algebra on finite products
   - `L2`: sequential composition semantics (round lists)
   - `L3`: format-specific adapters
4. **Extraction Targets**: reusable, domain-agnostic lemmas.

---

## A. Single-Step Sampling Equivalence

### Goal shape

Local randomized evaluation at queried coordinates equals:
draw full pure map first, then evaluate deterministically.

### Minimal assumptions

- finite coordinate domain
- finite action/value domain for product PMF
- no recall/history assumptions

### Core dependencies

- `L1`: pushforward composition, coordinate-wise pushforward of product PMFs
- `L0`: function normalization (compose/curry forms)

### Extraction targets

- `pushforward_coordwise_product`
- `local_sampling_bind_normal_form`

---

## B. Independence Refactor (Same Draw vs Fresh Draw)

### Goal shape

Replace continuation using the same random draw with one using an independent
fresh draw, provided continuation ignores a designated coordinate set.

### Minimal assumptions

- product PMF over finite coordinates
- an `Ignores`-style condition for designated coordinates

### Core dependencies

- `L1`: product-bind independence lemma (`bind_indep` form)
- `L0`: update algebra (`curry_update`, pointwise update lemmas)

### Extraction targets

- `bind_indep_under_ignores`
- `update_transport_through_curry`

---

## C. Easy Direction (Behavioral to Mixed Equivalence)

### Goal shape

Induction over step list:
local equivalence + independence refactor + induction hypothesis on tail.

### Minimal assumptions

- local non-repetition/separation condition between current step views and future-step views
- finiteness assumptions needed by product PMF lemmas

### Core dependencies

- `L2`: recursive decomposition of list evaluation
- `L1`: results from A and B
- `L0`: tail index arithmetic helpers

### Extraction targets

- `list_eval_equiv_under_view_separation`

---

## D. Hard Direction (Mixed to Behavioral Existence)

### Goal shape

Constructive existence by induction:
disintegrate on current-step observable branch, apply tail existence per branch,
recombine.

### Minimal assumptions

- branch determinacy condition (observable determines relevant history)
- finite domains for explicit conditioning/filter PMFs
- tail-closure of branch determinacy

### Core dependencies

- `L1`: disintegration identity for bind, conditioning/filter normalization
- `L2`: evaluation congruence under behavioral profile agreement on reachable views
- `L0`: selector helper for branch-indexed witnesses

### Extraction targets

- `disintegrate_then_recombine`
- `tail_determinacy_transport`
- `reachable_view_congruence`

---

## E. Final Packaging Theorem

### Goal shape

One-line adapter from concrete format assumptions to generic list theorem(s).

### Minimal assumptions

- only what is required to instantiate C and D.

### Design rule

Keep this theorem as thin as possible; all heavy proofs belong to `L0-L2`.

---

## Currently Implemented Small Generic Lemmas

- `curry_update` (function algebra)
- `pushforward_comp'` (PMF bind/pushforward algebra)

These live in `CoreSmallLemmas.lean` and avoid format-specific definitions.
