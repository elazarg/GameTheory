# Formalization status

Two halves: what **this repository** has formalized of the known literature,
and what the **external** proof-assistant world has. Both were checked by
direct inspection (this repo, and the mathlib checkout under
`.lake/packages/mathlib/`) rather than taken from documentation.

---

## Part I — this repository

Inspected 2026-08-02; the fixed-public credibility checkpoints are commits
`24b5bf7`, `8090347`, `97178e6`, `cbf1ab4`, `83b1826`, `68149dd`,
`4f12352`, and `fcf3ff4`. Theorem names and line numbers below were
checked directly in the tree.

**Credibility addendum, 2026-08-02.**
`PublicResponseCredibilityCriterion.lean` and
`ReachablePublicResponseCredibilityCriterion.lean` are committed,
build-checked, and imported by `GameTheory.lean`. They prove the supplied
finite-public-architecture implication from (T0)/(Ti)/(N)/(P) to uniform
enforcement ledgers, including rebasing and an `O(1/N)` modulus; the second
module gives the support-pruned sound direction at a declared entry. The
split-domain semantic converse is landed at `4f12352`, and the exact all-start
semantic iff finite gain/bias wrapper at `fcf3ff4`. These results do not prove
the separate `(RC)`/fifth-obstruction rejection exhaustion, bounded-template
synthesis, architecture existence, or private-memory/unrestricted coverage.
The FTV actual-data
adapter is landed at `8090347`: it checks the concrete payoff table and
ten-node architecture and compiles the four sufficient conditions to the
operational consumers. Q97's sharp modulus, necessity, phase-minimality, and
rigidity remain unformalized. The two Q95 cap-separator regressions are landed
at `97178e6`. The split-domain arbitrary-start prescribed telescope and
owner-arena cap are landed at `cbf1ab4`; the shared-modulus explicit-domain
verifier and its prescribed-entry ledger adapter are landed at `83b1826`.
The Q96 two-player/two-node uncovered-class regression is landed at `68149dd`:
the four nearest target/occupation tests pass, yet an escaped prescribed class
outside player one's arena has exact linear positive delivery error and no
global prescribed Poisson bias. This formalizes the counterexample, not its
minimality among all smaller encodings and not the corrected occupation-
rejection exhaustion.

**Sorin stopping addendum, 2026-08-02.** Review 05 reconstructs the source
proof giving asymptotic live `(Bottom, Right)` occupation at most `14ε` for a
fixed uniform `ε`-Nash profile. Commit `f3afee1` formalizes player 2's
stationary `2/3` one-sided guarantee. The later chain through `c1161dc` and
`6b0fc81` now lands both security adapters, cone resets, live-tail accounting,
occupation vanishing, and unconditional exclusion of the discounted endpoint.
The converse realization of the whole uniform segment remains open.

**Integration addendum, 2026-08-02.** Commit `43d410b` lands the canonical
genuine analytic endpoint Bellman-row compiler. It does not supply transition
monitoring, legal public responses, or recursive closers. Commit `1f097d2`
umbrella-imports the global nonexistence interface and corrects the README and
variable-stopping roadmap. Commit `914c765` lands the Vrieze
single-controller no-trap kernel and `d9f212e` the rank-decreasing policy
compiler. The fixed-kernel reachability-to-zero-occupation/transience step and
mean-ergodic projection inequality remain open.

**Question-corpus addendum, Q97--Q100 (2026-08-02).** These are internal status
rows, not literature-verification seals:

| Item | Current mathematical status | Repo marker | Lean boundary |
|---|---|---|---|
| Q97, minimal cyclic FTV credibility | Exact answer internally checked: minimum period three and rigidity of the named three-phase realization; approximate supportwise stability separated from weighted-regret instability | `T+A+C` for the concrete sufficient architecture and finite cyclic minimum/rigidity | Actual game, ten-node architecture, criterion checks, ledger, punishment and adaptive consumers landed; `408bf3b` lands the table-expanded finite minimum/normalized rigidity; sharp modulus and semantic necessity remain absent |
| Q98, computable public-node bounds | Answered **source-conditionally**: r.e.-completeness/no total bound, conditional on the finite-state SSMG reduction recorded below and on the internal bridge | `T` | Fixed-`K` ETR encoding, terminal bridge, graph trimming/all-node completion, halting gate, and exact-target compensation are not formalized |
| Q99, supplied private-controller verification | External finite-POMDP theory settles the common asymptotic value and finite-memory approximation. An audited internal PFA embedding makes \(L>c\) \(\Sigma^0_1\)-complete, \(L\le c\) \(\Pi^0_1\)-complete, \(L\ge c\) and \(L=c\) \(\Pi^0_2\)-complete, and \(L<c\) \(\Sigma^0_2\)-complete; finite strict-rejection certificates exist and complete enumerable cap-acceptance certificates do not. The appended repaired-historywise \(\Pi^0_1\) and effective-clock \(\Pi^0_3\) theorems are candidate results pending Reviews 01--02; exact attainment, stationary distinctions, tight complexity, decidable islands, restricted memory bounds, and the automatic-clock exact boundary remain open or omitted | `T` for the core; review-pending for appended extensions | No private-controller semantics, product filter, PFA embedding, finite-POMDP value theorem, arithmetic-hierarchy classification, historywise/clocked theorem, or certificate result in Lean |
| Q100, endogenous autonomous correlation | Solan--Vieille externally settle uniform correlated existence for every finite player number; Q100 asks for a device-to-ordinary-strategy compiler or obstruction and distinguishes private temporal recommendations from public coins | external theorem plus internal target separator | `a6a66b5` lands the sharp static product separator, `9f8aece` its pure-root lift, `afe018c` the arbitrary mixed-root/update bridge, and `a9cb4ca` target-specific exclusion of `(5/7,5/7)`; retargeting and every universal compiler/noncompiler claim remain open |

The Q98 source boundary is load-bearing. Ummels's thesis Theorem 4.13 states
undecidability of `PureFinNE`, `PureFinSPE`, `FinNE`, and `FinSPE` for
14-player SSMGs, but labels its proof a **sketch**. The peer-reviewed
Ummels--Wojtczak LMCS theorem supplies the 14-player `FinNE`/`PureFinNE`
statement, also by a proof sketch; the `FinSPE` strengthening is recorded in
the thesis. Our conversion from that source game to Q98's terminal-reward
gain--bias language, including physical-state trimming and all-node
completion, is internal and not Lean-formalized. A citation to the source does
not certify those conversion steps.

The Q99 source boundary is equally explicit. Rosenberg--Solan--Vieille and
Chatterjee--Saona--Ziliotto are external theorems about finite POMDP values and
finite-memory approximation. Rote and Chadha--Sistla--Viswanathan supply the
PFA threshold facts. The timing-preserving PFA-to-private-controller embedding,
the equality between PFA value and unilateral best-response value, the
two-player small bound, the arithmetic-hierarchy transfer, and the
delivery/credibility gadgets are repository derivations. None has been
formalized in Lean, and the citations do not certify those bridge steps.

### The conjecture itself

`GameTheory/Concepts/Stochastic/Uniform.lean:207` —
`StochasticGame.exists_uniformDeviationCapConstructor`, whose body is the
repository's **only** intentional `sorry` (line 211, enforced by
`scripts/check_lean_placeholders.py`). Verified: `rg sorry` over `GameTheory/`
and `Math/` returns exactly one code occurrence; the other four hits are the
word appearing in docstrings.

The two waists:

- **Construction waist** — `HasUniformDeviationCapConstructor`
  (`Uniform.lean:169`), proved exactly equivalent to the semantic
  uniform-equilibrium-payoff property by `hasUniformDeviationCapConstructor_iff`
  (`Uniform.lean:181`).
- **Verification waist** — the adaptive certificates in
  `AdaptiveCertificate.lean`.

### Classical results that ARE formalized here

| Literature result | Lean declaration | File:line |
|---|---|---|
| Shapley 1953, discounted zero-sum value + exact discounted Nash | `shapleyBehaviorProfile_isDiscountedNash` | `ZeroSum.lean:607` |
| Fink 1964, discounted stationary equilibria, `n` players | `exists_isDiscountedStationaryBellmanEq` | `Fink.lean:1238` |
| Blackwell–Ferguson 1968, **the Big Match**, uniform value | `exists_uniformEquilibriumPayoff_live` | `BigMatchUniform.lean:1913` |
| Sorin 1986 absorbing game, discount-constant behavioral Nash at `(1/2, 2/3)` | `SorinAbsorbingGame.isDiscountedNash` | `SorinAbsorbingGame.lean` |
| Mertens–Neyman 1981 — **conditional** reduction to two named hypotheses | `uniformValue_of_rowColumnTrackingCertificates` | `MertensNeymanCriterion.lean:1619` |
| Sorin 1986 separation direction and discounted-endpoint exclusion | `uniformEquilibriumPayoff_weighted_eq_two`; `discountedEndpoint_not_isUniformEquilibriumPayoff` | `SorinOccupationVanishing.lean` (umbrella-imported, `c1161dc`) |

Special cases of the conjecture proved here (these are *our* results, not
transcriptions of published theorems):

| Class | Declaration | File:line |
|---|---|---|
| Absorbing initial state | `exists_uniformEquilibriumPayoff_of_isAbsorbingState` | `Absorbing.lean:135` |
| Single-state games | `exists_uniformEquilibriumPayoff_of_subsingleton_state` | `Absorbing.lean:225` |
| Action-independent transitions | `exists_uniformEquilibriumPayoff_of_isActionIndependent` | `TransitionIndependent.lean:227` |
| All children absorbing after one step | `exists_uniformEquilibriumPayoff_of_absorbingChildren` | `OneStepAbsorbingChildUniform.lean:96` |
| Zero-sum single-controller (modulo one named LP hypothesis) | `exists_uniformEquilibriumPayoff_of_singleController` | `SingleController.lean:451` |

### Classical results NOT formalized here

The load-bearing absences recorded by this audit are:

- **Mertens–Neyman unconditional.** Only the conditional criterion exists.
- **Bewley–Kohlberg.** The whole semi-algebraic/Puiseux apparatus was built
  (`Math/CurveSelection/`, 45 files; `Math/AlgebraicSelection.lean`;
  `Math/PolynomialSignCell.lean`; `BellmanVariety.lean`;
  `DiscountedShapleyAlgebraic.lean`) but the theorem — bounded variation of
  `λ ↦ v_λ`, convergence of `v_λ`, `lim vₙ = lim v_λ` — is not stated.
- **Kohlberg 1974**, zero-sum absorbing games with a live state.
- **Vieille 2000 I/II**, the two-player non-zero-sum existence theorem.
- **Sorin's converse inclusion.** The target-free stopping estimate,
  separation hyperplane, and endpoint exclusion are formalized. The converse
  construction of every point with `1/2 ≤ w₁ ≤ 2/3` is not.
- **Flesch–Thuijsman–Vrieze stationary-impossibility/approximate boundary.**
  The game, ten-node period-three adapter, exact sufficient-condition checks,
  cyclic packet rigidity, exact finite-horizon delivery constants and
  `22/(7T)` modulus, and the all-start semantic credibility bridge are
  formalized. The remaining source-aligned target is the published exclusion
  of sufficiently accurate stationary equilibria and any stronger weighted-
  regret counterfamily actually supported by the source.
- **Ummels finite-state equilibrium undecidability.** Neither the 14-player
  SSMG reduction nor its `FinNE`/`FinSPE` variants are formalized here. Q98
  tracks a source-conditional use of the result; it is not a Lean
  transcription of the external theorem.

### Negative results formalized here

These have no direct counterpart in the literature — they are falsifiers
generated by this program and kept permanently:

`BigMatchNoMarkov.lean` (uniform witnesses must be history-dependent),
`BigMatchFinkEndpoint.lean`, `BigMatchDeficitIndexNoGo.lean` (the linear
running-deficit index is not a universal Mertens–Neyman constructor),
`DiscountBiasNoGo.lean`, `FinkTangentCounterexample.lean`,
`FinkSelectionCounterexample.lean`, `PureExternalityCycle.lean`.

Note that `BigMatchNoMarkov` independently reproduces, in a checked form, the
Markov-insufficiency content that Thuijsman's *Big Match and the Paris Match*
records as Lemmas 1–2 (stationary `max min = 0 < 1/2 = min max`; Markov
`sup inf = 0`).

### Supporting infrastructure built here

`Math/Probability/` (57 files) — couplings, stitched martingales, hitting-time
potentials, closed classes, occupation flows, optional target transport,
sublinear ledgers. `Math/CurveSelection/` (45 files) — Puiseux and
curve-selection machinery. `Math/MeanErgodic.lean`, `Math/ShapleyOperator.lean`,
`Math/SchauderFixedPoint.lean`, `Math/FixedPoint/{KKM,Scarf}.lean`,
`Math/Minimax/` (Loomis, Shapley–Snow).

---

## Part II — mathlib and the external landscape

### What mathlib 4 has today

Checked against the vendored checkout at `.lake/packages/mathlib/Mathlib/`.

| Prerequisite | In mathlib? | Where |
|---|---|---|
| Martingale / submartingale convergence | **yes** | `Probability/Martingale/Convergence.lean` |
| Optional stopping / optional sampling | **yes** | `Probability/Martingale/OptionalStopping.lean`, `OptionalSampling.lean` |
| Upcrossing estimates | **yes** | `Probability/Martingale/Upcrossing.lean` |
| Markov kernels, composition, disintegration | **yes** | `Probability/Kernel/` (`Defs`, `Composition/`, `Disintegration/`, `Invariance.lean`) |
| Ionescu–Tulcea (infinite-horizon path measure) | **yes** | `Probability/Kernel/IonescuTulcea/` |
| Mean ergodic theorem (von Neumann) | **yes** | `Analysis/InnerProductSpace/MeanErgodic.lean` |
| Birkhoff sums / ergodic averages | **yes** | `Dynamics/BirkhoffSum/`, `Dynamics/Ergodic/` |
| **Brouwer fixed point** | **no** | — |
| **Kakutani fixed point** | **no** | — (`MeasureTheory/Integral/RieszMarkovKakutani/` is the *Riesz–Markov–Kakutani representation theorem*, an unrelated result — do not be misled by the name) |
| **Nash equilibrium existence** | **no** | — |
| **Semialgebraic sets / Tarski–Seidenberg** | **no** | — |
| **Puiseux series** | **no** | — |

The bottom five rows are the reason this repository carries so much homegrown
mathematics. Brouwer is supplied by an **external package**, not mathlib: the
root `lakefile.lean:41` has
`require FixedPointTheorems from "fixed-point-theorems-lean4"` (harfe's Lean 4
Brouwer/Kakutani via a cubical Sperner route after Kuhn 1960). Nash existence
is built here in `GameTheory/Concepts/Existence/`
(`NashExistence.lean`, `NashExistenceMixed.lean`, `ProductSimplexBrouwer.lean`).

**Consequence for anyone planning a Bewley–Kohlberg formalization:**
Tarski–Seidenberg quantifier elimination for real closed fields is absent from
mathlib and is plausibly the single hardest missing prerequisite. That is
exactly why `Math/CurveSelection/` exists — it routes around the missing
general theory with bespoke curve-selection arguments rather than proving
quantifier elimination.

### External proof-assistant work

**Headline: no close counterpart was found in the audited sources.** No formalization of stochastic games in the
Shapley 1953 sense — nor of the Shapley operator for games, Fink/Takahashi
discounted stationary equilibria, the uniform value, Mertens–Neyman, Vieille's
theorem, the Big Match, repeated games, or folk theorems — was found in **any**
proof assistant, in a sweep dated 2026-08-02.

⚠ Read the strength of that negative carefully; it is **asymmetric**. It is
well-evidenced for the Isabelle/AFP probability and AI shelves and for one Coq
artifact. It is **merely unrefuted** for Lean 4, mathlib4, Coq/Rocq at large,
Agda, HOL4, PVS and Mizar: the two research claims that would have covered the
Lean side and the AFP games-and-economics shelf were both voted down **0–3**,
and no replacement evidence was gathered. Anyone needing a hard field-wide
negative must run those sweeps. (The Lean-side facts in the table above are
**not** from that research — they come from direct inspection of the vendored
mathlib checkout in this repository, which is stronger evidence.)

**What does exist — and why none of it is close:**

`[primary]` **Isabelle AFP, *Markov Models*** — Johannes Hölzl & Tobias Nipkow,
submitted 2012-01-03. Theories include `Markov_Decision_Process`,
`MDP_Reachability_Problem`, `MDP_RP`, `MDP_RP_Certification`, plus DTMCs,
CTMCs, PCTL, pGCL, Crowds, ZeroConf, Gossip. The MDP theory stays at the
**semantic** level — coinductive configuration type `cfg`, schedulers, `K_cfg`,
`cfg_on`, `memoryless_on`, trace space, `E_sup`/`P_sup`/`E_inf`/`P_inf`,
`Finite_Markov_Decision_Process` — and targets reachability. A verifier
downloaded the actual 814-line `Markov_Decision_Process.thy` from the AFP git
mirror and grepped case-insensitively for
`discount|reward|average|optimal|value_iter|policy_iter|game|nash|player`:
**zero matches**.

`[primary]` **Isabelle AFP, *Markov Decision Processes with Rewards*** and
***Verified Algorithms for Solving Markov Decision Processes*** — Maximilian
Schäffeler & Mohammad Abdulaziz (TU Munich), both 2021-12-16. Expected total
**discounted** reward, the Bellman operator iteration, the optimality
equations, existence of an optimal stationary deterministic policy; then
executable value iteration, policy iteration, Gauss–Seidel VI, modified PI.

⚠ **Strictly single-agent and strictly discounted.** Scope is Puterman ch. 5–6
("Infinite-Horizon Foundations", "Discounted"), **not** ch. 8–10 (average
reward, multichain, sensitive discount optimality). The entry's
`Bounded_Functions`/`Blinfun_Util` theories exist precisely because the
discounted Bellman operator is a contraction — machinery that does **not**
transfer to the average-reward criterion. Actively maintained (rebuilt
2026-02-06 against Isabelle2025-2), so this is current, not stale.

`[primary]` **Le Roux, Martin-Dorel & Smaus**, *An Existence Theorem of Nash
Equilibrium in Coq and Isabelle*, GandALF'17, EPTCS **256**, 46–60,
DOI [`10.4204/EPTCS.256.4`](https://doi.org/10.4204/EPTCS.256.4),
arXiv:1709.02096. Theorem 9 ("finitary equilibrium transfer"): for a two-player
normal-form game with finite outcome set and both preferences strict partial
orders, determinacy of the derived win/lose games gives a Nash equilibrium.
Two live artifacts: **Coq ~1300 lines** (SSReflect/MathComp, verified
axiom-free) and **Isabelle/HOL ~1100 lines of Isar**, both at
`irit.fr/~Erik.Martin-Dorel/equi-thm/` (HTTP 200 confirmed 2026-08-02).

⚠ **No probabilities anywhere.** Outcomes are elements of an arbitrary set
under an arbitrary binary relation: no mixed strategies, no state transitions,
no discounting, no expected payoffs, no time. The paper's covered game classes
are exclusively deterministic (finite/infinite extensive-form, Muller, parity)
and its future-work list contains nothing stochastic.

### What this means for this repository

**This repository is distinctive within the audited subset.** The sweep found
no close proof-assistant counterpart to its stochastic-game/uniform-value
development. That is not a certified field-wide uniqueness theorem: the Lean,
Rocq/Coq, Agda, HOL4, PVS, and Mizar searches were incomplete. In particular,
no Big Match counterpart was found in the checked sources; do not strengthen
that observation to “none exists anywhere” without a broader reproducible
sweep.

The nearest external stepping stone toward a uniform-value formalization would
be **average-reward / gain-bias / Blackwell optimality for MDPs** (Puterman
ch. 8–10). The Isabelle side demonstrably stops at the discounted criterion,
and nothing was checked in Coq, Lean, PVS or HOL4. That is a well-scoped,
genuinely reachable target that nobody appears to have taken.
