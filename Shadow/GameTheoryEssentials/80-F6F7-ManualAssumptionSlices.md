# Manual Assumption Slices (F6/F7, Structure-First)

This note records essentials for representative larger theorems, with
non-domain phrasing first and theorem names second.

## 1) Representation transfer over deviation inequalities

Concrete theorem:

- `MechanismDesign.isIC_implies_truthful_bayesNash`

Essential shape:

1. there is a pointwise inequality kernel `K(x, dev(x)) <= K(x, x)` for each sample point `x`,
2. expectation is monotone under pointwise inequality with nonnegative weights,
3. the deviation representation can be rewritten by an extensional update identity.

Block view:

- primary `B5` (representation transfer),
- secondary `B9` (sum/inequality transport), `B0` (update extensionality).

Cross-field name:

- refinement-preserving optimization inequality.

## 2) Communication-form equivalence principle

Concrete theorem:

- `RevelationPrinciple.revelation_principle`

Essential shape:

1. two optimization problems are related by a map from direct deviations to induced deviations,
2. objective values are equal after rewriting by this map,
3. an inequality known in source formulation is transported to target formulation.

Block view:

- primary `B5`,
- secondary `B0` (update algebra).

Cross-field name:

- normal-form reduction / compile-and-preserve no-improvement.

## 3) Locality lemma feeding an incentive theorem

Concrete theorem:

- `VickreyAuction.maxOtherBid_update_self`

Essential shape:

1. an aggregator over a finite set excludes one coordinate,
2. updating excluded coordinate leaves all aggregated terms unchanged,
3. aggregator value is invariant by congruence.

Block view:

- primary `B0`, secondary `B2`.

Cross-field name:

- frame/locality for finite supremum aggregators.

## 4) Extremal sandwich (minimax core)

Concrete theorem:

- `MinimaxTheorem.von_neumann_minimax`

Essential shape:

1. existence of a fixed point/witness `σ`,
2. lower bound on objective under one coordinate updates,
3. upper bound on objective under the other coordinate updates,
4. choose `v` as witness value and package both bounds.

Block view:

- primary `B7`, secondary `B6`, `B9`.

Cross-field name:

- saddle-value witness via dual bounds.

## 5) Interchangeability as two-sided rewrite + squeeze

Concrete theorem:

- `MinimaxTheorem.IsZeroSum.nash_interchangeable`

Essential shape:

1. prove equality of two mixed update expressions (`update_comm`-style normalization),
2. obtain one lower and one upper bound for the same normalized term,
3. squeeze to equality of objective value,
4. transfer equality into no-improvement inequalities for both coordinates.

Block view:

- primary `B7`, secondary `B0`, `B9`.

Cross-field name:

- commutation-normalized saddle transfer.

## One-shot extraction candidates from these slices

1. `expect_mono_of_pointwise` style lemma with minimal assumptions over finite-support weights.
2. generic `exclude_index_aggregator_update_invariant` for `Finset.sup'`/`Finset.sum`.
3. `dual_bound_witness_packaging` lemma: lower+upper envelopes around a witness imply value statement.
