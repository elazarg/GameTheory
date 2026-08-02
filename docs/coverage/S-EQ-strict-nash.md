# S-EQ: strict Nash seed

Title: Strict expected-utility Nash
Family ID: S-EQ
Pinned root: `GameTheory/Concepts/Equilibrium/SolutionConcepts.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `a829d9d`
Canonical destination: `GameTheory.Core.Response`
Domain contract / decision: D4-D5
Owner: Wave 2 / equilibrium recovery
Status: in progress; 1 bounded declaration reviewed
Last verified: 2026-08-02

This deliberately partial ledger claims only the strict expected-utility Nash
predicate recovered by the potential-game slice. It does not claim the nearby
legacy `KernelGame`, `...For`, payoff-set, or correlated-equilibrium wrappers.

| Pinned path | Declaration | Kind | Disposition | Successor declaration | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Concepts/Equilibrium/SolutionConcepts.lean` | `IsStrictNash` | def | adapt | `GameTheory.IsStrictNash` | focused Core.Response build | Expected-utility strict Nash is stated directly on canonical `GameForm`, utility, and `Profile.update`; no `KernelGame` wrapper. |

Disposition count: 1 adapt.

Attribution: the pinned declaration supplies the genuine-deviation strict
inequality. The successor places it with response concepts, below potential
games, and preserves the same mathematics without the old semantic bundle.

Validation:

```text
lake build GameTheory.Core.Response
```
