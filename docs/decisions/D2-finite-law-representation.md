# D2: finite-law representation

- **Status:** adopted for the v1 finite core; Phase 2 kill tests passed
- **Date:** 2026-07-22, amended 2026-07-26
- **Evidence:** EXP-003, EXP-004, EXP-006, EXP-007
- **Decision:** Represent the future `FinDist α` by a `PMF α` paired with a
  proof that its support is finite. Hide that representation behind the public
  API; do not expose the experimental candidate name.

## Competition and hostile slice

Candidate A is `{ μ : PMF α // μ.support.Finite }`. Candidate B stores
`weight : α →₀ ℝ≥0` and a mass-one proof. Both implement pure, map, bind,
product, map identity/composition, monad laws, unconditional real expectation
and expectation-bind, support, finite-simplex round trips, and a genuine
two-point law over the infinite carrier `Nat`. Candidate A also implements the
dependent finite product directly and proves pure-vertex, general product,
expectation, and affine-mixture preservation at the simplex boundary.
Candidate B's dependent product is explicitly routed through Candidate A's PMF
implementation in `D2/Interop.lean`; it is measured negative interoperability
evidence, not an independent Finsupp dependent-product implementation.

Candidate A adapts proof ideas from the pinned v1
`Math/FiniteProbabilityMassFunction.lean`,
`Math/PMFProduct/Basic.lean`, and
`Math/ProbabilityMassFunction/Simplex.lean` at `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
The snapshot is not imported.

## Measurements

Run:

```text
pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected -Time
lake build GameTheory.Experimental.Phase1.D1.Stress GameTheory.Experimental.Phase1.D2.Interop
```

| Metric | PMF subtype | Normalized Finsupp | Finsupp interop/product boundary |
|---|---:|---:|---:|
| Nonblank lines | 345 | 221 | 101 |
| Expectation-bind declaration lines | 52 | 19 | — |
| Simplex-equivalence declaration lines | 14 | 12 | — |
| Transport tokens | 3 | 4 | 3 |
| `toReal` tokens | 24 | 0 | 3 |
| `ENNReal` tokens | 41 | 1 | 3 |
| Classical/noncomputable tokens | 5 | 8 | 4 |
| Whole-file warm elaboration, observed review run | 15.368 s | 15.959 s | 15.118 s |

The PMF candidate pays visibly for `ENNReal.toReal` and finite-support Fubini.
The Finsupp candidate has the cleaner expectation and simplex surface, but it
must develop fresh nested-sum algebra and then recover PMF interoperability.
Its tested dependent product uses the PMF boundary, making the usable measured
surface 322 nonblank lines rather than 221. Timings are close enough to treat
their differences as noise, not a decision criterion.

The qualitative tradeoff matters more than the counters: PMF makes basic real
expectation and affine proofs noticeably heavier, while Finsupp feels native
for those proofs but becomes an island at dependent products and the existing
probability ecosystem. The measurements expose those costs; they do not by
themselves choose the representation.

## Result and boundaries

Neither candidate dominates every metric. D2 specifies the PMF subtype as the
fallback in exactly that case, and the pinned ecosystem supplies substantial
additional PMF bind, conditioning, independence, and update evidence. Candidate
A therefore wins.

The finite-carrier Analysis bridge is one equivalence to `stdSimplex ℝ α`;
there is no second mixed-game or equilibrium API. Finite support remains a law
capability, not a `Fintype` assumption on its carrier. Countable-support and
measurable/path-space laws remain separate layers under D3 and D11.

The representation must be reopened if any remaining hostile slice shows that
the hidden PMF subtype cannot support the required public API without leaking
`ENNReal`/`toReal` plumbing or duplicating semantics. The remaining kill tests
are: NFG mixed extension using the final signature API; EFG chance and
behavioral products; CE/CCE joint-law constraints; the Phase 4 Nash-existence
route through compact convex simplices; and fuller same-signature reuse across
those modules. Affine simplex preservation, previously missing, is now covered
by `Law.mix`, `expect_mix`, and `simplexEquiv_mix_apply`.

## Phase 2 amendment (EXP-006, EXP-007)

Two of the named kill tests ran and passed.

*NFG mixed extension through the final signature API.* `GameForm.mixed`,
`pi_update_mixed`, `mixed_play_update`, `isNash_mixed_iff` and the executable
`verifyMixedNash_eq_true_iff` are all stated and proved without a second
mixed-game API and without exposing the representation. Mixed Nash is
`IsNash F.mixed`, not a predicate of its own.

*CE/CCE joint-law constraints.* Both are `IsEquilibrium` at an arbitrary
`FinDist (Profile sig)` with different schemes; `IsCorrelatedEq.isCoarseCorrelatedEq`
is one application of a scheme morphism.

Representation leakage was measured at the public surface. `FinDist` exposes
`prob : FinDist α → α → ℝ` and `expect`, and no Core, Finite, Examples, or Tests
module mentions `ENNReal` or `toReal`; those tokens occur only inside
`GameTheory/Probability/FinDist.lean`. The single source-level transport token
in Phase 2 source is one `change` in `FinDist.mix`.

The measured cost is a *dependency* one, not an API one. Mathlib's
`ProbabilityMassFunction.Basic` imports `MeasureTheory.Measure.Dirac` and
`Topology.Instances.ENNReal.Lemmas`, so `MeasureTheory.Measure` and
`ContinuousMap` are reachable from `GameTheory.Core` even though Core's authored
imports name neither. Narrowing `FinDist`'s import from
`ProbabilityMassFunction.Constructions` to `.Monad` — which required defining
`FinDist.map` from `bind` and `pure` rather than reusing `PMF.map` — removed
`stdSimplex` and `Polynomial` from that closure and is checked by the Phase 2
audit. The remaining measure-theoretic closure is inherent to Mathlib's `PMF`
and cannot be removed while D2 stands.

RFC 9.1.5 ("importing Core pulls topology") cannot be read as a statement about
Mathlib's transitive closure, since any `ℝ`-valued expectation reaches
topological instances. It is enforced here as an authored-import rule plus the
reachability probes above, and this reading is recorded rather than assumed.
