# M-CONTRACT: finite hidden-action contracts

Title: Finite hidden-action principal-agent contracts
Family ID: M-CONTRACT
Pinned roots: `GameTheory/Mechanism/Contracts/Basic.lean`
Pinned commit: `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`
Successor baseline: `0b77ebd`
Canonical destination: `GameTheory.Mechanism.PrincipalAgent`, opt-in through `GameTheory.Mechanism`
Domain contract / decision: D32; EXP-065
Owner: Post-architecture Wave 4 / mature coordinated-domain recovery
Status: complete; 23/23 declarations reviewed
Last verified: 2026-08-03

The successor retains the pinned hidden-action mathematics without pretending
that the principal and agent make simultaneous strategic choices.  Every
action carries its own `FinDist` outcome law, so outcome finiteness is no
longer a global assumption.  Participation is parameterized by a real outside
option; the pinned zero-normalized claims are transparent corollaries.

| Pinned path | Declaration | Kind | Disposition | Successor declaration or gate | Evidence | Notes |
|---|---|---|---|---|---|---|
| `GameTheory/Mechanism/Contracts/Basic.lean` | `PrincipalAgent` | structure | adapt | `GameTheory.Mechanism.PrincipalAgent` | focused public-leaf build | Uses action-indexed `FinDist`; no stored carrier capabilities. |
| same | `agentUtility` | def | adapt | `PrincipalAgent.agentUtility`; `expectedPayment` | focused build | Expected transfer less effort cost; expected transfer is also named independently. |
| same | `principalUtility` | def | adapt | `PrincipalAgent.principalUtility` | focused build | Expected reward net of outcome-contingent transfer. |
| same | `expectedReward` | def | adapt | `PrincipalAgent.expectedReward` | focused build | Unconditional finite-support expectation on an arbitrary outcome carrier. |
| same | `linearPayment` | def | adapt | `PrincipalAgent.linearPayment` | focused build | Same realized-reward commission. |
| same | `LimitedLiability` | def | adapt | `PrincipalAgent.IsLimitedLiability` | focused build | Environment-independent predicate; no dummy environment argument. |
| same | `IsIncentivized` | def | adapt | `PrincipalAgent.IsIncentivized` | focused build | The agent's weak maximizer predicate, not a duplicate Nash surface. |
| same | `IsIR` | def | adapt | `PrincipalAgent.Participates` | hostile nonzero-option witness | Strengthened from a hard-coded zero floor to an explicit outside option. |
| same | `principalUtility_add_agentUtility` | theorem | adapt | same spelling | stochastic hostile witness | Transfer cancellation gives exact social surplus for non-point-mass laws. |
| same | `agentUtility_ge` | theorem | adapt | same spelling | focused build | Limited liability bounds utility below by negative cost without outcome finiteness. |
| same | `linearPayment_limitedLiability` | theorem | adapt | same spelling | focused build | Reward and commission nonnegativity remain theorem-local. |
| same | `agentUtility_linearPayment` | theorem | adapt | same spelling | focused build | Uses `FinDist.expect_smul`. |
| same | `exists_incentivized` | theorem | adapt | same spelling | generic theorem and Bool specialization | `[Finite Action] [Nonempty Action]` occur only on classical existence. |
| same | `socialSurplus` | def | adapt | `PrincipalAgent.socialSurplus` | focused build | Expected reward less effort cost. |
| same | `agentUtility_linearPayment_one` | theorem | adapt | same spelling | focused build | Full commission makes the agent residual claimant. |
| same | `principalUtility_linearPayment` | theorem | adapt | same spelling | focused build | Principal retains the complementary expected-reward share. |
| same | `principalUtility_linearPayment_one` | theorem | adapt | same spelling | focused build | Full commission leaves principal utility zero. |
| same | `isIncentivized_linearPayment_one_iff` | theorem | adapt | same spelling | focused build | Characterizes agent optimality as surplus maximization, without claiming participation. |
| same | `agentUtility_mono` | theorem | adapt | same spelling | focused build | Pointwise-larger transfer raises utility for a fixed action. |
| same | `isIR_of_isIncentivized` | theorem | adapt | `participates_of_offersParticipation_of_isIncentivized`; zero-cost/limited-liability corollary | hostile fallback and negative control | The genuine premise is an offered acceptable action; LL plus optimality alone is refuted. |
| same | `principalUtility_le_socialSurplus_of_isIR` | theorem | adapt | `principalUtility_le_socialSurplus_sub_outsideOption`; zero-option corollary | focused build | Strengthened to subtract the explicit rent floor. |
| same | `principalUtility_eq_socialSurplus_iff` | theorem | adapt | same spelling; explicit-option strengthening | focused build | Zero-rent equality is retained as the normalized corollary. |
| same | `principalUtility_le_firstBest` | theorem | adapt | same spelling; `principalUtility_le_firstBest_zero` | focused build | The primary theorem subtracts the explicit outside option; the pinned statement is the zero corollary. |

## Validation

```text
lake build GameTheory.Mechanism.PrincipalAgent GameTheory.Tests.PrincipalAgent GameTheory.Mechanism
pwsh -NoProfile -File scripts/phase2-audit.ps1 -VerifyExpected -SkipReachability
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
```

The promoted leaf imports only `GameTheory.Probability.FinDist`; Mechanism
remains opt-in.  The hostile Boolean fixture uses both a fair law and a point
mass, changes the strictly preferred action when the contract changes,
accepts outside utility `1/4`, rejects `3/4`, and preserves the negative
limited-liability control from EXP-065.  Source scans reject raw updates,
transports, stored-finiteness workarounds, placeholders, and custom axioms.
