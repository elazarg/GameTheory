# GameTheory

Greenfield Lean 4 game-theory library built on Mathlib.

The foundational architecture spike in
[`docs/GameTheory2Design.md`](docs/GameTheory2Design.md) has passed Phases 0-3.
The scoped Phase 4 static harvest is complete, and Phase 5's named queue is
complete while its method remains a standing design-stress protocol. The active
coverage and expansion schedule is
[`docs/PostArchitectureDeliveryPlan.md`](docs/PostArchitectureDeliveryPlan.md);
its honest pinned-v1 baseline is
[`docs/V1CoverageLedger.md`](docs/V1CoverageLedger.md).

```text
GameTheory/Probability   finite-support probability laws (FinDist)
GameTheory/Core          signatures, profiles, forms, preferences, utility,
                         deviations, equilibrium and response concepts, static
                         game theory, and foundational social/coalitional theory
GameTheory/Protocol      execution, histories, information, assessment,
                         randomization, well-founded subgame perfection, and
                         static-form compilation
GameTheory/Finite        executable rational frontend and its correctness layer
GameTheory/Analysis      stable, opt-in fixed-point, minimax, and existence theory
  /Protocol              analytic behavioral-assessment consistency bridge
  /Repeated              analytic repeated-game bridge and discounted folk theorem
GameTheory/Repeated      stable public histories, discounting, cycles, and triggers
GameTheory/Languages     scoped language encodings with recorded limitations
  /EFG                   transparent extensive-form specialization; finite
                         capabilities are supplied explicitly
GameTheory/Examples      reader-facing examples with #eval and #guard tests
GameTheory/Tests         architecture and locality tests
GameTheory/Experimental  architecture spikes, never re-exported
GameTheoryMath           independently reusable, game-free mathematics
```

The root `GameTheory` import re-exports Core, Protocol, and Finite. Analysis is
stable but deliberately opt-in so its fixed-point and topology dependencies
cannot leak across the audited boundary. Repeated is also opt-in: its stable
root remains analysis-light, while `GameTheory.Analysis.Repeated` is the
one-way bridge for feasible-payoff geometry and the discounted folk theorem.
`GameTheory.Analysis.Protocol` is the separate one-way bridge for pointwise
Kreps-Wilson consistency over stable behavioral assessments; its EFG adapter
supplies finite history instances and canonical continuation contexts without
moving solution concepts into stable syntax.
`GameTheoryMath` is a separate Lake target and cannot import game semantics.
Languages and Experimental also stay outside the root for the separate reasons
recorded in their modules. Examples and Tests compile in the default library
target but are not public-root imports.

The ignored `reference/GameTheory-v1/` directory is an exact source snapshot of
the previous library at commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
It is evidence for design experiments, not a dependency or migration source.

## Environment

- Lean: `v4.32.0`
- Mathlib: `v4.32.0`
- Lake package, public library, and public Lean namespace: `GameTheory`

Use `lake update` to resolve dependencies and `lake exe cache get` to fetch
Mathlib build artifacts.

## Checks

```text
lake build
pwsh -NoProfile -File scripts/phase0-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
```

`lake build` compiles every module, including examples, tests, and experiments.
The phase audits re-check the architecture constraints. Later Phase 4/5 probes
were folded into the historically named Phase 2/3 scripts; the delivery plan
requires a consolidated coverage audit before any v1-accounted claim.
