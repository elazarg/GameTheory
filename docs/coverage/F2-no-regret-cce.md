# F2: no-regret time averages are approximate CCE

Title: Finite no-regret learning to coarse correlated equilibrium
Family ID: F2
Pinned roots: `GameTheory/Concepts/Learning/NoRegretToCCE.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `7fb2b57`
Canonical destination: `GameTheory.Core.Learning`
Domain contract / decision: D4, D5, D10; post-architecture gate W1-C
Owner: Wave 1 / learning
Status: complete for the frozen F2 theorem; broader learning remains D-LEARN
Last verified: 2026-07-30

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `Concepts/Learning/NoRegretToCCE.lean` | `expect_uniformOfFintype_fin` | theorem | adapt | `Probability.FinDist.expect_uniformFin` | focused and full builds; axiom audit | The finite-support probability API owns its uniform `Fin` law; no `PMF` representation escapes into learning. |
| same | `externalRegret_eq_expect` | theorem | adapt | `UtilityGame.externalRegret_eq_expect_gain` | focused build; source audit | Uses `Profile.update`, the accepted play law, and ordinary expected utility. |
| same | `timeAverage` | definition | adapt | `UtilityGame.timeAverage` | focused and full builds | A uniform finite-support mixture of round laws. |
| same | `externalRegret_timeAverage` | theorem | adapt | `UtilityGame.externalRegret_timeAverage` | focused build; axiom audit | Regret remains affine in the status-quo law. |
| same | `timeAverage_isεCCE_of_regret_le` | theorem | adapt | `UtilityGame.timeAverage_isεCoarseCorrelatedEq_of_regret_le` | two-round hostile trace; axiom audit | The successor spells out “coarse correlated” and targets the canonical utility-game CCE semantics. |

The predecessor imported the much larger correlation/regret hierarchy, but the
frozen result uses only constant unilateral deviations and finite averaging.
Those dependencies are recovered at their lowest sufficient layer here; swap
regret, conditional regret, regret algorithms, and limit convergence remain in
the broader S-CORR and D-LEARN inventories.

Attribution: the predecessor's affine-regret calculation and uniform-time
mixture are retained. The successor replaces `KernelGame`, `PMF`, and direct
`Function.update` with the accepted `UtilityGame`, `FinDist`, and
`Profile.update` APIs.

Validation:

```text
lake build GameTheory.Core.Learning GameTheory.Tests.Learning
lake build
pwsh -NoProfile -File scripts/phase0-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
```

The two-player hostile trace has cumulative external regret at most one over
two rounds, and player zero's second-round regret is exactly one. Its time
average is therefore a `1 / 2`-CCE, while a separate theorem proves that it is
not an exact CCE. The focused trust audit for the uniform expectation,
regret-average theorem, flagship, and both trace conclusions reports only
`propext`, `Classical.choice`, and `Quot.sound`.
