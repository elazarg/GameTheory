# M-BAYES: finite information design

Title: Finite-support public signaling and Bayesian persuasion
Family ID: M-BAYES
Pinned roots: `GameTheory/Mechanism/Bayesian/InformationDesign.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `60ae515`
Canonical destination: `GameTheory.SignalStructure` and
`GameTheory.PersuasionProblem`, opt-in through `GameTheory.Mechanism`
Domain contract / decision: D2, D4, D9; validated M-BAYES split
Owner: Post-architecture Wave 2 / mature Bayesian-mechanism recovery
Status: complete for the pinned information-design file; 21/21 declarations reviewed
Last verified: 2026-08-08

The predecessor used an unbounded-support `PMF` even though every intended
workflow was finite.  The successor uses the canonical `FinDist`, keeps state,
message, and action carriers arbitrary in semantic data, and requests
finiteness only for finite sums and optimizer existence.  Bayes plausibility is
the marginal equality itself rather than a second predicate duplicating
`BayesianGame.IsBayesPlausible`.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Mechanism/Bayesian/InformationDesign.lean` | `SignalStructure` | structure | adapt | `GameTheory.SignalStructure` | focused build; stochastic hostile signal | The kernel returns the canonical finite-support law and stores no carrier finiteness. |
| same | `SignalStructure.joint` | def | adapt | `SignalStructure.joint` | marginal and point-mass laws | Prior followed by the public-signal kernel. |
| same | `SignalStructure.messageMarginal` | def | adapt | `SignalStructure.messageMarginal` | bind characterization | The pushforward remains a finite-support law. |
| same | `SignalStructure.HasPriorMarginal` | def | retired | marginal equality `(S.joint prior).map Prod.fst = prior` | no-duplicate-semantics rule | A second name for the same map equality added no capability and collided conceptually with canonical Bayesian plausibility. |
| same | `SignalStructure.joint_hasPriorMarginal` | theorem | adapt | `SignalStructure.map_fst_joint` | focused build; hostile prior witness | Every kernel-induced joint law preserves its prior. |
| same | `SignalStructure.uninformative` | def | adapt | `SignalStructure.uninformative` | focused build | Unit public signal. |
| same | `SignalStructure.fullInformation` | def | adapt | `SignalStructure.fullInformation` | sender-value comparison | The signal reports the realized state. |
| same | `SignalStructure.uninformative_kernel` | theorem | port | `SignalStructure.uninformative_kernel` | focused build | Transparent constructor law. |
| same | `SignalStructure.fullInformation_kernel` | theorem | port | `SignalStructure.fullInformation_kernel` | focused build | Transparent constructor law. |
| same | `SignalStructure.joint_apply` | theorem | adapt | `SignalStructure.prob_joint` | two positive hostile joint masses | Real masses replace exposed `ENNReal` PMF application. |
| same | `SignalStructure.messageMarginal_apply` | theorem | adapt | `SignalStructure.prob_messageMarginal` | focused build | Requires only a finite state carrier, not a finite message carrier. |
| same | `PersuasionProblem` | structure | adapt | `GameTheory.PersuasionProblem` | focused build; partial/full comparison | Stores no finite instances. |
| same | `PersuasionProblem.receiverScore` | def | adapt | `PersuasionProblem.receiverScore` | four strict-score calculations | Defined by finite-support expectation, including zero-probability messages. |
| same | `PersuasionProblem.senderScore` | def | adapt | `PersuasionProblem.senderScore` | score-sum theorem | Defined at arbitrary carriers. |
| same | `PersuasionProblem.IsReceiverOptimal` | def | port | `PersuasionProblem.IsReceiverOptimal` | strict receiver incentives | Uses the predecessor's weak-maximizer semantics. |
| same | `PersuasionProblem.DecisionRule` | abbrev | port | `PersuasionProblem.DecisionRule` | focused build | A message-contingent receiver action. |
| same | `PersuasionProblem.IsPersuasive` | def | port | `PersuasionProblem.IsPersuasive` | hostile partial-revelation rule | Checks every message, including off-path messages. |
| same | `PersuasionProblem.senderEU` | def | adapt | `PersuasionProblem.senderEU` | `3/4` versus `1/2` witness | Uses unconditional real expectation from `FinDist`. |
| same | `PersuasionProblem.senderEU_eq_sum` | theorem | adapt | `PersuasionProblem.senderEU_eq_sum` | focused build | Finiteness is theorem-local. |
| same | `PersuasionProblem.senderEU_eq_sum_senderScore` | theorem | adapt | `PersuasionProblem.senderEU_eq_sum_senderScore` | focused build | Interchanges the two finite sums. |
| same | `PersuasionProblem.IsOptimalPersuasive` | def | port | `PersuasionProblem.IsOptimalPersuasive` | optimizer existence theorem | The successor additionally proves existence on finite message/action spaces whenever a persuasive rule exists. |

## Validation

```text
lake build GameTheory.Mechanism.InformationDesign GameTheory.Tests.InformationDesign GameTheory.Mechanism
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected -SkipReachability
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
```

The hostile binary problem has a fair state prior.  In the false state its
signal is genuinely random; in the true state it deterministically reports
`true`.  The receiver strictly follows either message, both false-state joint
events have probability `1/4`, and partial revelation raises sender utility
from `1/2` under full information to `3/4`.  The generic finite optimizer
theorem is then specialized to this persuasive rule.  This closes the pinned
information-design file without claiming the broader M-BAYES family complete.
