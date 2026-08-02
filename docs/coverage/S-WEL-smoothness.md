# S-WEL: smoothness and robust welfare bounds

Title: Generic smoothness and robust welfare bounds
Family ID: S-WEL
Pinned root: `GameTheory/Concepts/Welfare/Smoothness.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `9e35ab1`
Canonical destination: `GameTheory.Core.Welfare`; future finite-law correlation layer
Domain contract / decision: EXP-052/D24; aggregate expected utility is a Core operation
Owner: post-architecture welfare and congestion wave
Status: in progress; 4/4 declarations reviewed, 2 deferred to the finite-law CCE gate
Last verified: 2026-08-02

The pure smoothness definition and its Nash consequence belong at the lowest
sufficient Core layer: aggregate canonical expected utility and canonical
profile updates.  The predecessor's robust results require a single missing
bridge, named here the **canonical `FinDist` expected-social-welfare/CCE gate**:
a finite-law expected-social-welfare operation together with the compatible
coarse-correlated-equilibrium inequality.  Neither an obsolete `PMF` surface
nor a parallel correlated-utility aggregate is recreated in advance of that
gate.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Welfare/Smoothness.lean` | `IsSmooth` | def | adapt | `GameTheory.UtilityGame.IsSmooth` | current `GameTheory/Core/Welfare.lean`; focused welfare build | Same unilateral-deviation inequality over canonical `Profile.update` and expected utility. |
| same | `IsSmooth.nash_bound` | theorem | adapt | `GameTheory.UtilityGame.IsSmooth.nash_bound` | current welfare source; focused welfare build | Same division-free pure Nash welfare inequality. |
| same | `IsSmooth.epsilonCoarseCorrelated_bound` | theorem | deferred | canonical `FinDist` expected-social-welfare/CCE gate | source comparison; S-WEL gate | Reopen with a named finite-law welfare expectation and epsilon-CCE aggregate inequality; do not retain `PMF` or finite-outcome boilerplate. |
| same | `IsSmooth.coarseCorrelated_bound` | theorem | deferred | canonical `FinDist` expected-social-welfare/CCE gate | source comparison; S-WEL gate | Exact robust bound follows the epsilon result only after the same canonical finite-law bridge exists. |

Disposition count: 2 adapt, 2 deferred.

Attribution: the smoothness inequality and Nash squeeze are recovered from the
pinned file.  The successor adapts them to `UtilityGame`, `Profile.update`, and
the canonical expected-utility API.  The robust results are deliberately not
claimed before their finite-distribution welfare semantics has one reusable
consumer-facing home.

Validation:

```text
lake build GameTheory.Core.Welfare
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
git diff --check
```
