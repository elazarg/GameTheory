# D2: finite-law representation

- **Status:** adopted for the v1 finite core
- **Date:** 2026-07-22
- **Evidence:** EXP-003, EXP-004
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
