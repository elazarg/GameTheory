# T-CE: correlated-equilibrium existence

Title: Correlated- and coarse-correlated-equilibrium existence
Family ID: T-CE
Pinned root: `GameTheory/Theorems/CorrelatedEqExistence.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `21c49fd`
Canonical destination: `GameTheory.Analysis.Correlated`; `GameTheory.Core.Mixed`
Domain contract / decision: D2, D5, and the accepted Analysis boundary
Owner: post-architecture breadth wave
Status: complete; 6 declarations reviewed
Last verified: 2026-08-02

The pinned existence proofs factor through mixed-Nash existence.  The
successor keeps exactly that mathematical factorization while removing the
obsolete `KernelGame`, countably-supported `PMF`, `Fintype.ofFinite`, and
bounded-versus-finite-outcome duplication.  Canonical finite laws have finite
support, so the stronger successor results need neither a utility bound nor a
finite outcome carrier.

| Pinned path | Declaration | Kind | Disposition | Successor declaration | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Theorems/CorrelatedEqExistence.lean` | `correlatedEq_exists_of_bounded` | theorem | subsumed | `GameTheory.exists_isCorrelatedEq` | focused Analysis build; hostile Matching Pennies consumer | The successor needs no bound and permits an arbitrary outcome type. |
| same | `correlatedEq_exists` | theorem | adapt | `GameTheory.exists_isCorrelatedEq` | focused build; axiom audit | Canonical `GameForm`, `FinDist`, and expected-utility preference. |
| same | `mixed_nash_isCoarseCorrelatedEq_of_bounded` | theorem | subsumed | `GameTheory.IsNash.isCoarseCorrelatedEq_pi` | focused Core/Analysis build | The topology-free bridge is preference-parametric and needs no bound. |
| same | `mixed_nash_isCoarseCorrelatedEq` | theorem | adapt | `GameTheory.IsNash.isCoarseCorrelatedEq_pi` | focused build; axiom audit | Derived from Nash-to-CE and CE-to-CCE on the canonical product law. |
| same | `coarseCorrelatedEq_exists_of_bounded` | theorem | subsumed | `GameTheory.exists_isCoarseCorrelatedEq` | focused Analysis build | The successor needs no bound and permits an arbitrary outcome type. |
| same | `coarseCorrelatedEq_exists` | theorem | adapt | `GameTheory.exists_isCoarseCorrelatedEq` | focused build; hostile Matching Pennies consumer | Direct corollary of canonical mixed-Nash existence. |

Disposition count: 3 adapt, 3 subsumed.

Attribution: theorem statements and the mixed-Nash factorization are recovered
from the pinned correlated-equilibrium existence file.  The successor reuses
the canonical bridges proved independently in `Core.Mixed` and
`Core.Equilibrium`; it does not reproduce v1's probability or game semantics.

Validation:

```text
lake build GameTheory.Analysis.Correlated GameTheory.Analysis.Examples
lake env lean AxiomAudit.lean  # temporary local module with `#print axioms`
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
rg -n "KernelGame|PMF|Function\.update|sorry|admit|axiom|Fintype\.ofFinite|open Classical" GameTheory/Analysis/Correlated.lean GameTheory/Core/Mixed.lean
git diff --check
```
