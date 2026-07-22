# D2: finite-law representation

- **Status:** adopted for the v1 finite core
- **Date:** 2026-07-22
- **Evidence:** EXP-003
- **Decision:** Represent the future `FinDist α` by a `PMF α` paired with a
  proof that its support is finite. Hide that representation behind the public
  API; do not expose the experimental candidate name.

## Competition and hostile slice

Candidate A is `{ μ : PMF α // μ.support.Finite }`. Candidate B stores
`weight : α →₀ ℝ≥0` and a mass-one proof. Both implement pure, map, bind,
product, monad laws, unconditional real expectation and expectation-bind,
support, finite-simplex round trips, pure/product/expectation checks, and a
law over the infinite carrier `Nat`. Candidate A also implements the dependent
finite product directly. Candidate B's required dependent product is exercised
through its explicit PMF interoperability boundary in `D2/Interop.lean`.

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
| Nonblank lines | 266 | 212 | 85 |
| Expectation-bind declaration lines | 51 | 19 | — |
| Simplex-equivalence declaration lines | 13 | 12 | — |
| `toReal` tokens | 15 | 0 | 3 |
| `ENNReal` tokens | 18 | 1 | 3 |
| Classical/noncomputable tokens | 5 | 8 | 2 |
| Whole-file warm elaboration | 14.050 s | 13.572 s | 13.626 s |

The PMF candidate pays visibly for `ENNReal.toReal` and finite-support Fubini.
The Finsupp candidate has the cleaner expectation and simplex surface, but it
must develop fresh nested-sum algebra and then recover PMF interoperability.
Its tested dependent product uses the PMF boundary, making the usable measured
surface 297 nonblank lines rather than 212. Timings are close enough to treat
their differences as noise, not a decision criterion.

## Result and boundaries

Neither candidate dominates every metric. D2 specifies the PMF subtype as the
fallback in exactly that case, and the pinned ecosystem supplies substantial
additional PMF bind, conditioning, independence, and update evidence. Candidate
A therefore wins.

The finite-carrier Analysis bridge is one equivalence to `stdSimplex ℝ α`;
there is no second mixed-game or equilibrium API. Finite support remains a law
capability, not a `Fintype` assumption on its carrier. Countable-support and
measurable/path-space laws remain separate layers under D3 and D11.
