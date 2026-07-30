# F8: public-monitoring signal-prefix law

Title: Finite public-signal history generation and bind-first recursion
Family ID: F8
Pinned roots: the public-signal-history cluster in
`GameTheory/Concepts/Repeated/Monitoring.lean`:
`PublicMonitoring`, `SignalHistory`, `MonitoredStrategy`, `MonitoredProfile`,
`afterSignal`, and `signalHistoryDist` through
`signalHistoryDist_succ_eq_bind_first`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `43e94df`
Canonical destination: `GameTheory.Repeated.Monitoring`
Domain contract / decision: D2, D5, D6, D11; post-architecture gate W1-D
Owner: Wave 1 / repeated monitoring
Status: complete for the frozen F8 law; broader monitoring remains D-REPEAT
Last verified: 2026-07-30

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `Concepts/Repeated/Monitoring.lean` | `KernelGame.PublicMonitoring` | structure | adapt | `UtilityGame.PublicMonitoring` | focused and full builds; boundary audits | Signal kernels consume the accepted stage profile and return a `FinDist`; no universal game hub or infinite-path law. |
| same | `PublicMonitoring.SignalHistory` | abbreviation | adapt | `UtilityGame.PublicMonitoring.SignalHistory` | focused build | A length-indexed public prefix remains `Fin t → Signal`. |
| same | `PublicMonitoring.MonitoredStrategy` | abbreviation | adapt | `UtilityGame.PublicMonitoring.MonitoredStrategy` | focused build; noisy probe | Strategies see only public signal histories. |
| same | `PublicMonitoring.MonitoredProfile` | abbreviation | adapt | `UtilityGame.PublicMonitoring.MonitoredProfile` | focused build; noisy probe | Uses the canonical player-indexed profile shape. |
| same | `PublicMonitoring.afterSignal` | definition | adapt | `UtilityGame.PublicMonitoring.afterSignal` | focused build; branch-dependent probe | Cast-free continuation through `Fin.cons`. |
| same | `PublicMonitoring.afterSignal_apply` | theorem | adapt | `UtilityGame.PublicMonitoring.afterSignal_apply` | focused build | Transparent application rule. |
| same | `PublicMonitoring.signalHistoryDist` | definition | adapt | `UtilityGame.PublicMonitoring.signalHistoryLaw` | focused and full builds | Finite recursion only; every horizon has a `FinDist`. |
| same | `PublicMonitoring.signalHistoryDist_zero` | theorem | adapt | `UtilityGame.PublicMonitoring.signalHistoryLaw_zero` | focused build | Empty history is a point mass. |
| same | `PublicMonitoring.signalHistoryDist_succ` | theorem | adapt | `UtilityGame.PublicMonitoring.signalHistoryLaw_succ` | focused build | Append-oriented recursion. |
| same | `PublicMonitoring.signalHistoryDist_succ_eq_bind_first` | theorem | adapt | `UtilityGame.PublicMonitoring.signalHistoryLaw_succ_eq_bind_first` | noisy two-period probe; axiom audit | First sample the current public signal, then generate the continuation prefix. |

The pinned file continues into garblings, expected stage utility, average and
discounted payoffs, equilibrium, rank conditions, and self-generation. Those
declarations are not silently credited to F8; they remain in D-REPEAT and
S-CORR inventories. F8 is exactly the finite signal-prefix substrate frozen by
the RFC.

Attribution: the predecessor's two equivalent decompositions—append the newest
signal, or bind the first signal and recurse on the continuation—are retained.
The successor replaces `KernelGame` and `PMF` with the accepted `UtilityGame`
and `FinDist` layers.

Validation:

```text
lake build GameTheory.Repeated.Monitoring GameTheory.Tests.Monitoring
lake build
pwsh -NoProfile -File scripts/phase0-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected
pwsh -NoProfile -File scripts/phase3-audit.ps1 -VerifyExpected
```

The two-period probe begins with a fair public coin. After `false`, the
continuation signal law remains fair; after `true`, it becomes a point mass.
The first signal is proved unequal to either point mass, and the bind-first
theorem is specialized to this branch-dependent process.

The first Phase 2 run found two source-level transport tokens in the new proof:
a `change` tactic and a proof-term rewrite. Both were eliminated without
changing the statement. The final audit reports
`TRANSPORT_REPEATED_SOURCE=0`. The focused axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.
