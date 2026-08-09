# GameTheory

Greenfield Lean 4 game-theory library built on Mathlib.

The foundational architecture spike in
[`docs/GameTheory2Design.md`](docs/GameTheory2Design.md) has passed Phases 0-3.
The scoped Phase 4 static harvest is complete, and Phase 5's named queue is
complete while its method remains a standing design-stress protocol. The active
coverage and expansion schedule is
[`docs/PostArchitectureDeliveryPlan.md`](docs/PostArchitectureDeliveryPlan.md);
its honest pinned-v1 baseline is
[`docs/V1CoverageLedger.md`](docs/V1CoverageLedger.md). User-facing parity is
tracked separately in
[`docs/V1CapabilityMatrix.md`](docs/V1CapabilityMatrix.md): exact declaration
accounting is regression evidence, while release usefulness is judged by
mature workflows and cannot be bought with unrelated beyond-v1 breadth.

```text
GameTheory/Probability   finite-support probability laws (FinDist)
GameTheory/Core          signatures, profiles, forms, preferences, utility,
                         deviations, equilibrium and response concepts, static
                         game theory, strict-dominance solvability, approximate
                         Nash, mixed and pure rationalizability, Bayesian
                         recommendation/obedience,
                         finite no-regret learning, concrete reindexing and
                         relabeling laws, utility-scale invariance, profile
                         individual rationality, social
                         welfare, robust CCE smoothness, zero-sum matrix
                         security, May's majority
                         characterization, and foundational social/coalitional
                         theory
GameTheory/Protocol      execution, histories, information, assessment,
                         randomization, well-founded subgame perfection, and
                         static-form compilation
GameTheory/Epistemic     finite information partitions, posteriors, exact and
                         approximate common knowledge, and agreement
GameTheory/Evolutionary  static ESS/NSS and the canonical symmetric-Nash bridge
GameTheory/Finite        executable rational frontend and its correctness layer
GameTheory/Analysis      stable, opt-in fixed-point, minimax and matrix values,
                         existence, trembling-hand refinement,
                         approachability, and learning-convergence theory
  /Protocol              analytic behavioral-assessment consistency bridge
  /Repeated              analytic repeated-game bridge and discounted folk theorem
  /Stochastic            normalized Shapley values and stationary statewise saddles
GameTheory/Repeated      stable public histories, finite public monitoring,
                         finite-average uniform equilibrium, discounting,
                         cycles, and triggers
GameTheory/Stochastic    opt-in finite-support stochastic games, perfect-public
                         Protocol play, finite-horizon payoff, and uniformity
GameTheory/Congestion    opt-in load calculus, Rosenthal potential, pure and
                         coarse-correlated affine PoA, and canonical
                         Pigou/Braess examples
GameTheory/Cooperative   opt-in bargaining, ordinal matching, and voting power,
                         including Nash-product affine invariance, finite
                         deferred-acceptance stability, balanced perfect
                         matchings, and Banzhaf/Shapley--Shubik indices
GameTheory/Mechanism     opt-in coordinated mechanisms, finite auctions,
                         combinatorial allocations, finite round-robin EF1,
                         two-agent EFX existence, all-pay arithmetic, and
                         exact/VCG and checked half-approximate finite knapsack
GameTheory/Languages     scoped language encodings and truthful Bayesian
                         mechanism compilation with recorded limitations
  /NFG                   deterministic normal-form syntax compiling directly
                         to the canonical static form, with no second Nash API
  /FOSG                  transparent Protocol execution/information
                         specialization with simultaneous actions; Values and
                         Kuhn are intentional explicit opt-in leaves, not
                         syntax-root imports
  /Bridges/NFGFOSG       exact one-shot source-to-target outcome and utility
                         laws through the actual Protocol history runner
  /EFG                   transparent extensive-form specialization; finite
                         capabilities are supplied explicitly; strategic
                         extraction exposes exact pure/mixed Nash iff laws and
                         both Kuhn directions preserve canonical history laws;
                         well-founded one-shot/SPE is a transparent specialization
  /MAID                  typed acyclic influence diagrams with site-local
                         policies, order-free frontier evaluation, explicit
                         EFG compilation, order independence, and exact
                         source-owner behavioral Nash transfer
  /Intrinsic             capability-light closed-loop configurations,
                         information-local pure rules, solvability, and
                         configuration-dependent causality before compilation;
                         Solution is an intentional explicit opt-in leaf, not
                         a syntax-root import
  /MultiRound            finite imperfect-monitoring games with remembered own
                         actions, canonical perfect recall, and direct
                         Protocol/FOSG compilation
GameTheory/Examples      reader-facing examples with silent #guard checks
GameTheory/Tests         architecture and locality tests
GameTheory/Experimental  architecture spikes, never re-exported
GameTheoryMath           independently reusable, game-free mathematics,
                         including online-learning and approachability engines
```

The root `GameTheory` import re-exports Core, Protocol, Epistemic,
Evolutionary, and Finite. Epistemic is deliberately independent of Protocol:
Protocol information is history-local, whereas epistemic cells partition a
state space. Evolutionary keeps ESS/NSS static and imports Core only in its
one-way Nash bridge; population dynamics remain reserved for a future opt-in
Analysis root. Analysis is stable but deliberately opt-in so its fixed-point
and topology dependencies cannot leak across the audited boundary. Repeated is
also opt-in: its stable root remains analysis-light, while
`GameTheory.Analysis.Repeated` is the one-way bridge for feasible-payoff
geometry and the discounted folk theorem.
`GameTheory.Analysis.Protocol` is the separate one-way bridge for pointwise
Kreps-Wilson consistency over stable behavioral assessments; its EFG adapter
supplies finite history instances and canonical continuation contexts without
moving solution concepts into stable syntax.
`GameTheoryMath` is a separate Lake target and cannot import game semantics.
The supported finite stochastic-game domain is also opt-in. Its native object
stores only state, actions, finite-support transitions, and stage utility; a
named perfect-monitoring bridge reuses Protocol's sole behavioral runner, and
each finite horizon reuses canonical approximate Nash. The one-way
`GameTheory.Analysis.Stochastic` bridge proves the normalized two-player
zero-sum Shapley contraction, unique discounted value, and stationary
statewise saddle selectors. Neither root contains an infinite-path law or a
general uniform-equilibrium existence claim.
Congestion, Cooperative, and coordinated Mechanism domains are stable but
opt-in, so their specialized APIs do not enlarge the main root. Languages and Experimental also
stay outside the root for the separate reasons recorded in their modules.
The intrinsic language is likewise opt-in: its native product and closed-loop
semantics precede any temporal compiler, while mixed strategies, utility,
perfect recall, and Kuhn equivalence remain separately gated.
Per D28 and D31, `GameTheory.Languages.FOSG.Values`,
`GameTheory.Languages.FOSG.Kuhn`, and
`GameTheory.Languages.Intrinsic.Solution` are intentional explicit opt-in
leaves. They are therefore not imported by their language syntax roots.
Examples and Tests compile in the default library target but are not
public-root imports.

The ignored `reference/GameTheory-v1/` directory is an exact source snapshot of
the previous library at commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
It is evidence for design experiments, not a dependency or migration source.

## Environment

- Lean: `v4.32.2`
- Mathlib: `v4.32.2`
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
pwsh -NoProfile -File scripts/coverage-audit.ps1 -VerifyExpected
```

`lake build` compiles every module, including examples, tests, and experiments.
The phase audits re-check the architecture constraints. Later Phase 4/5 probes
were folded into the historically named Phase 2/3 scripts. The coverage audit
owns the separate pinned-v1 accounting gate: it checks exclusive file
ownership, a current generated declaration index, and exact reviewed ledger
rows before any `v1-accounted` claim.

Hosted CI runs the full build, the self-contained Phase 1-3 audits, and the
tracked-index structural coverage checks on a clean checkout. Phase 0 and the
coverage audit's source-ownership and index-freshness checks additionally
require the exact ignored `reference/GameTheory-v1/` snapshot; they remain
explicit local release gates until that pinned evidence is provisioned in CI.
