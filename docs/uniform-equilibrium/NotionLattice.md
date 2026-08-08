# The notion lattice

**Curated at commit `6523070`, 2026-08-04; disambiguation note added
2026-08-05** (this file's `K0`/`K1` cluster IDs are unrelated to any
question's `K`-numbering used elsewhere — see `PIPELINE.md`). Tracks pipeline
row `LEAN-F0-5`.
This file is the artifact that row asks for: every ordered pair of
payoff/equilibrium notions in its declared universe is LANDED with a named
theorem, OPEN with a tracked row, FALSE with a counterexample or reason, or
N/A with a reason. No blank cells, and "standard" is not an answer.

**Scope, stated honestly.** This is a complete inventory *relative to an
explicitly declared universe of notions* — the ones enumerated in §1, found
by reading `GameTheory/Concepts/Stochastic/UniformEquilibrium/README.md`, `Uniform.lean`,
`GameTheory/Languages/MultiRound/StochasticGame.lean`, the quitting-specific
files, and the modules they import or are imported by. It does **not**
establish that this universe is exhaustive, nor does it certify the global
consistency of the repository's definitions. A notion absent from §1 is
either genuinely absent from the tree (verified by grep, see §5) or missed by
this pass; §1 is a floor, not a ceiling.

**Why a registry, not a matrix.** "Uniform" is a horizon quantifier, not a
payoff functional; `IsUniformEquilibriumPayoff` is already a payoff-level
predicate, so it cannot be a matrix column alongside functionals like
`finiteAveragePayoff`. `IsεAsymptoticNash` is parameterized by an *arbitrary*
payoff functional `u`, so no fixed matrix cell can hold it — each
instantiation of `u` is a different edge. §1 records nodes with five
independent fields (payoff functional, strategy class, quantifier order,
approximation regime, game scope); §2 records directed edges between nodes.
The small per-cluster tables in §2 are views generated from that edge list,
not the primary structure.

Every Lean name below was verified to exist by `grep` at the cited
file:line. No theorem name is stated without that check.

## 1. Registry of nodes

Columns: payoff functional the notion is stated against; strategy class
quantified over; quantifier order (per-horizon / uniform-in-horizon /
asymptotic / stationary-fixed-point); approximation regime (exact / ε /
vanishing-ε family); game scope (general finite `StochasticGame`, a
restricted class, or quitting-only).

### Cluster 0 — ground floor, one-shot kernel games

| ID | Lean name | File:line | Payoff functional | Strategy class | Quantifier order | Approximation | Game scope |
|---|---|---|---|---|---|---|---|
| K0 | `KernelGame.IsNash` | `Concepts/Equilibrium/SolutionConcepts.lean:68` | one-shot `eu` | pure/mixed strategy of a `KernelGame` | none (single shot) | exact | any `KernelGame` |
| K1 | `KernelGame.IsεNash` | `Concepts/Equilibrium/ApproximateNash.lean:43` | one-shot `eu` | as K0 | none | ε | any `KernelGame` |

(`K0`/`K1` here are this registry's own cluster-node IDs, unrelated to any
question's `K`-numbering — e.g. `PIPELINE.md`'s Q148/Q159 `K1`–`K4` labels,
which name different objects entirely.)

Not stochastic-game notions themselves, but the base every stage-level and
horizon-level notion below reduces to (`isεHorizonNash_iff_horizonGame`,
`stageKernelGame`, `stageGame`).

### Cluster 1 — stagewise and Markov

| ID | Lean name | File:line | Payoff functional | Strategy class | Quantifier order | Approximation | Game scope |
|---|---|---|---|---|---|---|---|
| M1 | `StochasticGame.IsMarkovNash` | `Languages/MultiRound/StochasticGame.lean:74` | raw `stagePayoff` at one state | pure `MarkovProfile` (state → action, no randomization) | none — single-state, single-stage deviation | exact | any `StochasticGame` |
| M2 | `StochasticGame.IsMixedStageNash` | `Concepts/Stochastic/Core/StageGame.lean:100` | `mixedStageEU` at one state | mixed Markov (`State → ∀ i, PMF (Act i)`) | none — single-state, single-stage deviation | exact | any `StochasticGame` |
| M3 | `StochasticGame.IsεLegalMarkovNash` | `Concepts/Stochastic/Transform/ActionLegality/Normalization.lean:121` | raw `stagePayoff`, deviations restricted to `Legal` | pure `MarkovProfile`, legal actions only | none | ε | state-dependent legal action sets |
| M4 | `StochasticGame.IsεNormalizedMarkovNash` | `Concepts/Stochastic/Transform/ActionLegality/Normalization.lean:131` | `normStagePayoff` (illegal actions padded) | pure `MarkovProfile` | none | ε | as M3, padded presentation |

**M1 is misnamed relative to the literature and its own docstring says so.**
"Markov Nash equilibrium" in the stochastic-game literature means a
*Markov-perfect* equilibrium: stationary, no profitable deviation once
continuation values (transitions, discounting or long-run averaging) are
accounted for. `M1` checks none of that — it compares only
`G.stagePayoff s (fun i => σ i s) who` against one-stage deviations at one
state, exactly the field `stagePayoff` and nothing downstream of it; the
transition kernel and every other state are invisible to the predicate. Its
own docstring: *"This is a stage-game Nash condition, not the full
discounted-payoff Nash."* The honest name is **stagewise pure Nash**, and it
is recorded as such in every edge description below. **The repository has no
continuation-aware, Markov-perfect equilibrium notion at all** — no
`IsMarkovPerfectNash`, no fixed-point-in-value-function predicate outside the
discounted Bellman machinery of Cluster 2, which is stated for a *fixed*
discount factor and never packaged as a genuine `β → 1` or average-reward
Markov-perfect notion. That absence is itself one of this document's
findings, not just a gap in M1's name.

`M1` has **zero importers** anywhere in `GameTheory/` outside its own
declaration file (`grep -rln IsMarkovNash GameTheory/` returns only
`Languages/MultiRound/StochasticGame.lean`). It is not merely disconnected
from the uniform-equilibrium tower; nothing in the tree uses it at all.

### Cluster 2 — discounted

| ID | Lean name | File:line | Payoff functional | Strategy class | Quantifier order | Approximation | Game scope |
|---|---|---|---|---|---|---|---|
| D1 | `StochasticGame.IsDiscountedεNash` | `Concepts/Stochastic/Equilibrium/Discounted.lean:974` | `discountedPayoff β` | full `BehaviorProfile` | fixed `β`, single-shot deviation test | ε | any `StochasticGame` |
| D2 | `StochasticGame.IsDiscountedStationaryBellmanEq` | `Concepts/Stochastic/Equilibrium/Discounted/Fink.lean:1007` | `discountedAuxEU β` (Bellman value `V`) | stationary mixed `StationaryMixedProfile` | fixed `β`, Bellman fixed point | exact | any `StochasticGame` (Fink 1964) |

### Cluster 3 — finite-horizon and uniform (behavior strategies)

| ID | Lean name | File:line | Payoff functional | Strategy class | Quantifier order | Approximation | Game scope |
|---|---|---|---|---|---|---|---|
| U1 | `StochasticGame.IsεHorizonNash` | `Concepts/Stochastic/Equilibrium/Uniform.lean:77` | `finiteAveragePayoff` at fixed `T` | full `BehaviorProfile` | per-horizon (one `T`) | ε | any `StochasticGame` |
| U2 | `StochasticGame.IsUniformεEquilibrium` | `Concepts/Stochastic/Equilibrium/Uniform.lean:85` | `finiteAveragePayoff` | full `BehaviorProfile` | uniform-in-horizon (`∃T₀∀T≥T₀`) | ε | any `StochasticGame` |
| U3 | `StochasticGame.IsUniformEquilibriumPayoff` | `Concepts/Stochastic/Equilibrium/Uniform.lean:94` | `finiteAveragePayoff`, target `v : Payoff ι` | full `BehaviorProfile`, may depend on ε | uniform-in-horizon, ∀ε∃σ | vanishing-ε family | any `StochasticGame` — **the central notion** (Solan–Vieille Def. 2.1 / Mertens–Neyman) |
| U4 | `StochasticGame.HasUniformDeviationCapConstructor` | `Concepts/Stochastic/Equilibrium/Uniform.lean:172` | `finiteAveragePayoff`, target `v` | full `BehaviorProfile` | as U3, split into on-path + deviation-cap clauses | vanishing-ε family | any `StochasticGame` |
| U5 | `StochasticGame.IsUniformScheduledMarkovEquilibriumPayoff` | `Concepts/Stochastic/UniformEquilibrium/VanishingDiscount/Fink/MarkovEndpoint.lean:27` | `finiteAveragePayoff`, target `v` | **scheduled-Markov** (`ℕ → StationaryMixedProfile`) only | as U3 | vanishing-ε family | any `StochasticGame` |
| U6 | `StochasticGame.IsεAsymptoticNash` | `Concepts/Stochastic/Equilibrium/Asymptotic.lean:40` | **arbitrary** `u : BehaviorProfile → ι → ℝ` | full `BehaviorProfile` | asymptotic (whatever `u` encodes) | ε | any `StochasticGame`; a family of nodes, one per `u` |

U6 is not one node but a schema: every instantiation of `u` (limiting
functional) is a distinct payoff notion. Two instantiations matter below:
`u = quittingTerminalPayoff reward` (Cluster 7) and the never-built
liminf-average functional (Cluster 4).

### Cluster 4 — liminf/limsup-average (no Lean `Prop` exists for either)

**There is no Lean node here for either aggregation** — no
`IsLiminfAverageEquilibrium` and no `IsLimsupAverageEquilibrium` `Prop`
anywhere in the tree (`grep -rn "def.*LiminfAverage\|LiminfAverageEquilibrium\|
def.*LimsupAverage\|LimsupAverageEquilibrium" GameTheory/` returns no
matches). The infinite-play measure itself **is** built —
`StochasticGame.infinitePlayMeasure`
(`Concepts/Stochastic/Core/Probability/InfinitePlayMeasure.lean:160`), by the Ionescu-Tulcea
theorem from the game's transition kernel and a fixed behavior profile — and
`LiminfAverageBridge.lean` uses it directly, with no representation
hypothesis, via `StochasticGame.pathwiseAveragePayoff`
(`LiminfAverageBridge.lean:415`) and
`StochasticGame.integral_pathwiseAveragePayoff`
(`LiminfAverageBridge.lean:462`). `LiminfAverageBridge.lean` states four
bridge theorems from U3 to the literature's liminf- and limsup-average
games — one deviation-direction and one on-path-direction theorem for each
aggregation — every one unconditional in its pathwise realization. Exactly
one of the two directions is unconditional in its *mathematics* for each
aggregation (Fatou for liminf-deviation and limsup-on-path; nothing for
liminf-on-path and limsup-deviation without an extra a.s.-convergence
hypothesis). Recorded as edges in §2.4, not as nodes.

### Cluster 5 — monitored / realized-action repeated games

Base type is `KernelGame`/`PublicMonitoring`, not `StochasticGame` — connected
to Cluster 3 only through the one-state adapter `realizedActionStochasticGame`.

| ID | Lean name | File:line | Payoff functional | Strategy class | Quantifier order | Approximation | Game scope |
|---|---|---|---|---|---|---|---|
| R1 | `KernelGame.IsεFiniteRepeatedNash` | `Concepts/Repeated/Uniform.lean:47` | `finiteAveragePayoff` (repeated) | `RepeatedProfile` | per-horizon | ε | any `KernelGame` |
| R2 | `KernelGame.IsUniformεEquilibrium` | `Concepts/Repeated/Uniform.lean:55` | as R1 | `RepeatedProfile` | uniform-in-horizon | ε | any `KernelGame` |
| R3 | `KernelGame.IsUniformEquilibrium` | `Concepts/Repeated/Uniform.lean:61` | as R1, plus `HasLongRunAveragePayoff` | `RepeatedProfile`, one fixed profile | fixed profile, ∀ε | exact convergence + ε-family | any `KernelGame` |
| P1 | `PublicMonitoring.IsUniformEquilibrium` | `Concepts/Repeated/Monitoring.lean:636` | monitored `finiteAveragePayoff` | `MonitoredProfile`, one fixed profile | as R3 | as R3 | monitored `KernelGame` |
| P2 | `PublicMonitoring.IsUniformEquilibriumPayoff` | `Concepts/Stochastic/Transform/Repeated/RealizedActionRepeatedAdapter.lean:86` | monitored `finiteAveragePayoff`, target `v` | `MonitoredProfile`, may depend on ε | as U3 | vanishing-ε family | monitored `KernelGame` |

### Cluster 6 — zero-sum discounted / Mertens–Neyman

| ID | Lean name | File:line | Payoff functional | Strategy class | Quantifier order | Approximation | Game scope |
|---|---|---|---|---|---|---|---|
| Z1 | `StochasticGame.IsZeroSum` | `Concepts/Stochastic/ZeroSum/Basic.lean:329` | game-class predicate, not an equilibrium notion | — | — | — | two-player, `Payoff (Fin 2)` |
| Z2 | `discountedShapleyValue` / `shapleyBehaviorProfile` + `shapleyBehaviorProfile_isDiscountedNash` | `Concepts/Stochastic/ZeroSum/Basic.lean:607` | `discountedPayoff β` | `stationaryBehaviorProfile` of the Shapley optimal pair | fixed `β` | exact (ε=0) | zero-sum two-player |
| Z3 | `StochasticGame.IsRowTrackingCertificate` / `SecuresCol` | `Concepts/Stochastic/UniformEquilibrium/SpecialCases/ZeroSum/MertensNeyman/Criterion.lean:909` | finite-horizon securing guarantee | history-adaptive strategy | uniform-in-horizon | ε | zero-sum two-player |

### Cluster 7 — quitting-specific

Quitting games are ordinary `StochasticGame`s with `Act = Bool`
(quit/continue) and a specific `stagePayoff`/`transition` built by
`quittingGame`; every general notion above applies to them unchanged. The
notions below exist **only** for quitting games — no general-game analogue
is defined anywhere in the tree.

| ID | Lean name | File:line | Payoff functional | Strategy class | Quantifier order | Approximation | Game scope |
|---|---|---|---|---|---|---|---|
| Q1 | `IsεQuittingRootNash` | `Concepts/Stochastic/UniformEquilibrium/Quitting/Root/FirstBranch.lean:197` | `quittingRootExpectedPayoff` (root mixture + free continuation vector) | one-shot `ι → PMF Bool` at the root | none | ε | quitting only |
| Q2 | `IsεQuittingRootEndpointNash` | `Concepts/Stochastic/UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean:119` | as Q1, tested at the two pure endpoints | as Q1 | none | ε | quitting only |
| Q3 | `HasUniformDeviationUpperApproximation` | `Concepts/Stochastic/UniformEquilibrium/Quitting/Terminal/ToUniformDeviationApproximation.lean:44` | any limiting functional `u` vs. `finiteAveragePayoff` | full `BehaviorProfile` | uniform-in-horizon, one-sided | ε | stated generally; used only for quitting |
| Q4 | `quittingTerminalPayoff` | `Concepts/Stochastic/Models/Quitting/Asymptotic.lean:201` | expected absorption-weighted terminal reward | full `BehaviorProfile` | — (a payoff functional, not an equilibrium notion) | exact | quitting only |
| Q5 | `IsQuittingZeroSolo` | `Concepts/Stochastic/UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean:57` | reward-table admissibility class, not an equilibrium notion | — | — | — | quitting only |
| Q6 | `HasAdmissibleAbsorbingQuittingCycle` | `Concepts/Stochastic/UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean:156` | as Q5 | — | — | — | quitting only |

`IsUniformEquilibriumPayoff` (U3) itself applies verbatim to quitting games
(instantiated at `quittingGame reward`); it is not a separate node, but every
edge into U3 in §2.6 is stated for `G = quittingGame reward`.

## 2. Directed edges

Each edge is `source → target : VERDICT`, evidence, and the hypothesis
gap if the edge is conditional. Only edges between comparable nodes (same or
transportable payoff functional, compatible strategy classes) are listed;
pairs with no shared payoff functional and no known transport (e.g. Q1 vs.
D1) are omitted rather than padded with N/A, per the registry-not-matrix
design — the two clusters share nothing to compare.

### 2.1 Ground floor ↔ stagewise (Clusters 0–1)

| Edge | Verdict | Evidence |
|---|---|---|
| M1 → (K0 of `stageKernelGame s`) | **LANDED** | `isMarkovNash_iff_all_stage_nash` (`Languages/MultiRound/StochasticGame.lean:87`) — full iff, per state. |
| M2 (viewed at a Dirac/pure profile) → M1 | **N/A** | Different carrier types (`State → ∀i, PMF(Act i)` vs. `State → ∀i, Act i`); no coercion or specialization theorem exists. Not fabricated as OPEN because no meaningful statement is even stated in-tree at either type. |
| M1 → M2 (pure stage-Nash, viewed as degenerate mixed, is stage-Nash against mixed deviations) | **OPEN** | Mathematically the standard "pure Nash ⇒ Nash against mixed deviations in a one-shot game" fact, but no Lean theorem connects M1 and M2 (M1 has zero importers, confirmed §1). No pipeline row found. |
| M1 → U1/U2/U3 (stagewise pure Nash ⇒ any uniform notion) | **OPEN** | Tracked by `LEAN-F0-1` (`PIPELINE.md:69`), whose acceptance text names this exact gap: *"the transfer is proved against a locally-defined Markov epsilon-Nash notion, not against the behaviour-strategy notion `IsUniformEquilibriumPayoff` actually uses."* This is the task's orientation instance #1. |
| M2 → U1, **restricted to `IsActionIndependent` games** | **LANDED (restricted)** | `isεHorizonNash_markovBehaviorProfile` (`Concepts/Stochastic/Classes/TransitionIndependent.lean:148`), for every `ε ≥ 0` and every horizon. Requires the extra game-class hypothesis `∀ s a, G.transition s a = κ s` (transitions independent of actions); **not** proved for general transitions. |
| M2 → U1, general transitions | **OPEN** | No theorem and no pipeline row; expected false by any reader who knows why Bellman equations exist (a stage-optimal action can lead to a permanently worse continuation), but no in-tree counterexample witnesses it either, so it is recorded OPEN rather than FALSE per the no-fabrication rule. |
| M2 (action-independent) → U3 | **LANDED (restricted)** | `exists_uniformEquilibriumPayoff_of_isActionIndependent` (`TransitionIndependent.lean:213`). |
| M4 → M3 | **LANDED** | `isεLegalMarkovNash_of_normalized` (`Transform/ActionLegality/Normalization.lean:144`) — a legal, normalized-Nash Markov profile is Nash for the legality-constrained game. |
| M3 → M4 | **OPEN** | Module docstring, `Transform/ActionLegality/Normalization.lean:24`: *"The converse direction is not addressed here."* Tracked under `LEAN-F0-1`. |
| M3/M4 → U1/U3 | **OPEN** | Same `LEAN-F0-1` row: the padding-reduction transfer stops at the Markov level and is never lifted to the behavior-strategy notions. |

### 2.2 Discounted ↔ Uniform (Clusters 2–3)

| Edge | Verdict | Evidence |
|---|---|---|
| D2 → D1 (a Bellman equilibrium's stationary play is an exact discounted Nash) | **LANDED** | `IsDiscountedStationaryBellmanEq.isDiscountedεNash` (`Fink.lean:1301`), in full generality — any `StochasticGame`, any player count, `ε = 0` exactly, no zero-sum assumption. Two hypotheses are explicit and were implicit before: `β < 1` **strictly** (Fink's own existence theorem assumes only `β ≤ 1`, so it must be specialized), and a uniform stage-payoff bound `|stagePayoff s a who| ≤ U`; both are needed for series summability. Only `.onProfile_bellman_eq` and `.deviation_bellman_ge` were reusable; the deviation side additionally required a general dual that **did not exist** — an upper bound on `discountedPayoff` from a Bellman upper inequality — now `discountedPayoff_le_of_bellman_ge` (`Discounted.lean:381`), mirroring `le_discountedPayoff_of_bellman_le`. That the zero-sum file obtains the same step via antisymmetry (`ZeroSum/Basic.lean:607`) confirms the general dual was genuinely absent. |
| Z2 (D1 specialized to zero-sum + Shapley profile) | **LANDED** | `shapleyBehaviorProfile_isDiscountedNash` (`ZeroSum/Basic.lean:607`), exact (`ε = 0`). |
| D2-family (a family of certificates, one per accuracy, with state-uniformly convergent values) → U3 | **LANDED, conditional on the certificate family's convergence** | `isUniformEquilibriumPayoff_of_fink_certificates` (`Fink.lean:1353`). The premise is an explicit hypothesis package (`hcert`), not derived from a single D2 instance — Fink's theorem alone does not discharge it. |
| D1 (single fixed β) → U3 | **OPEN** | This is exactly the residual `isUniformEquilibriumPayoff_of_fink_certificates` isolates as "the remaining substantive issue after Fink's theorem" (its own docstring). The natural discharge mechanisms are shown obstructed, not proved impossible in general: `UniformEquilibrium/VanishingDiscount/Fink/TangentCounterexample.lean` and `UniformEquilibrium/VanishingDiscount/Fink/SelectionCounterexample.lean` show the supported-harmonic-adjustment selection route fails, and `DiscountBiasNoGo.lean` shows unscaled tail variation cannot control the scaled discount-bias drift. None of these is a counterexample game refuting D1 → U3 itself; they refute specific *mechanisms* for discharging `hcert`. Recorded OPEN, not FALSE. |
| Z3-pair (`IsRowTrackingCertificate` + `SecuresCol`) → U3, zero-sum | **LANDED, conditional on both certificates** | `uniformValue_of_rowColumnTrackingCertificates` (`UniformEquilibrium/SpecialCases/ZeroSum/MertensNeyman/Criterion.lean`, assembly layer, `:60-68` docstring). The certificates themselves are supplied by two conditional constructors (`trackingCertificate_of_discountBiasControl`, `trackingCertificate_of_runningDeficit`), **not** proved to exist for every zero-sum game. |
| "linear running-deficit index" mechanism → Z3's `IsRowTrackingCertificate` | **FALSE** | `UniformEquilibrium/Examples/BigMatch/DeficitIndexNoGo.lean` (README: *"the linear running-deficit index is not a universal Mertens–Neyman constructor"*) — refutes that specific constructor, not Z3 → U3 itself. |

### 2.3 Within Cluster 3 (the uniform ladder)

| Edge | Verdict | Evidence |
|---|---|---|
| U3 ↔ U4 | **LANDED** | `hasUniformDeviationCapConstructor_iff` (`Uniform.lean:184`), full iff both directions. |
| U2 unfolds to `∀T≥T₀, U1` | **N/A** | Definitional — U2 *is* a quantifier wrapped around U1 (`Uniform.lean:85-87`), not an independent implication needing a bridge theorem. |
| U3 ⇒ `∀ε>0 ∃σ, U2` | **LANDED** | `exists_isUniformεEquilibrium` (`UniformExistenceConjecture.lean:129`), derived from U3 by dropping the payoff-proximity clause already present in U3's own definition. |
| U3 → U6 (arbitrary pointwise-convergent `u`) | **LANDED, conditional on `hlim`** | `exists_isεAsymptoticNash_of_isUniformEquilibriumPayoff` (`Asymptotic.lean:71`). `hlim : ∀ τ who, Tendsto (finiteAveragePayoff · τ who) atTop (𝓝 (u τ who))` is a genuine extra hypothesis about `u`, supplied per instantiation. |
| ¬∃(U6 witness) → ¬∃U3 | **LANDED** | `not_exists_uniformEquilibriumPayoff_of_no_asymptoticNash` (`Asymptotic.lean:87`) — the contrapositive, used by counterexample arguments. |
| U3 → U5 (scheduled-Markov witness exists) | **FALSE** | Big Match: `exists_uniformEquilibriumPayoff_live` (`UniformEquilibrium/Examples/BigMatch/Uniform.lean:1894`) gives U3 at `v = (1/2, -1/2)` from `.live`; `not_isUniformScheduledMarkovEquilibriumPayoff_half` (`UniformEquilibrium/Examples/BigMatch/NoMarkov.lean:58`) refutes U5 at the same state and the same value `1/2`. Same game, same target, U3 holds and U5 fails. |
| U5 → U3 | **LANDED** | `IsUniformScheduledMarkovEquilibriumPayoff.isUniformEquilibriumPayoff` (`UniformEquilibrium/VanishingDiscount/Fink/MarkovEndpoint.lean:39`) — forgetting the scheduled-Markov form of the witness. |
| U1 ↔ K1 of `horizonGame` | **LANDED** | `isεHorizonNash_iff_horizonGame` (`Uniform.lean:123`) — full iff; "per horizon, a stochastic game *is* a kernel game." |

### 2.4 Liminf/limsup-average (Cluster 4) — mirrored, not doubled

The task's orientation instance #2. `LiminfAverageBridge.lean`'s own docstring
separates these explicitly; they must not be merged. The infinite-play
measure is landed (`infinitePlayMeasure`, `InfinitePlayMeasure.lean:160`), so
every edge below is unconditional in its pathwise *realization* — no
representation hypothesis remains anywhere in this cluster. What remains
conditional is a genuine mathematical fact about a.s. convergence, and it is
conditional for exactly one direction of each aggregation, mirrored: liminf's
deviation direction is free and its on-path direction costs `hconv`; limsup's
on-path direction is free and its *deviation* direction costs `hconv`. This
is the exact opposite pairing, not two free directions for either notion.

| Edge | Verdict | Evidence |
|---|---|---|
| U3 (deviation direction) → liminf-average cap on one fixed deviation | **LANDED, unconditional** | `deviation_liminf_le_of_isUniformEquilibriumPayoff` (`LiminfAverageBridge.lean:481`), real Fatou (`integral_liminf_le_of_bounded_of_eventually_le`, `LiminfAverageBridge.lean:209`). No representation hypothesis: `infinitePlayMeasure` supplies the pathwise realization directly. |
| U3 (on-path direction), **unconditional** — pinned expectations alone ⇒ `E[liminf A_T] ≥ v_i - ε` | **FALSE** | Module docstring (`LiminfAverageBridge.lean` §"Two directions, two different stories") records the standard moving-bump/typewriter-sequence construction: a uniformly bounded sequence of expectations converging to `L` can have `liminf_T A_T ω = 0` almost everywhere pathwise. This is the documented *reason*, not a separately Lean-formalized counterexample game — recorded as FALSE-by-reason per the task's own rule ("FALSE — with the counterexample **or the reason**"), not overclaimed as machine-checked. |
| U3 (on-path direction), **conditional on `hconv` (a.s. convergence of `A_T`)** → liminf-average payoff of `σ` itself | **LANDED, conditional on `hconv` — a genuine extra mathematical hypothesis, not infrastructure** | `onPath_le_liminf_integral_of_isUniformEquilibriumPayoff` (`LiminfAverageBridge.lean:513`), via `le_integral_liminf_of_bounded_of_tendsto_ae_of_eventually_le` (`LiminfAverageBridge.lean:348`, dominated convergence). Tracked by `LEAN-F0-3` (`PIPELINE.md:930`). |
| U3 (on-path direction) → limsup-average payoff of `σ` itself | **LANDED, unconditional** | `onPath_le_limsup_integral_of_isUniformEquilibriumPayoff` (`LiminfAverageBridge.lean:544`), reverse Fatou (`le_integral_limsup_of_bounded_of_eventually_le`, `LiminfAverageBridge.lean:316`) — the dual of the liminf-deviation lemma under `A ↦ -A` (`liminf_neg_eq_neg_limsup`, `LiminfAverageBridge.lean:194`). This is the direction the deviation-direction reasoning does **not** give: it is on-path, not deviation. |
| U3 (deviation direction), **unconditional** — pinned expectations alone ⇒ `E[limsup A_T] ≤ v_i + 2ε` on a deviation | **FALSE** | Dual of the liminf on-path counterexample under `A ↦ -A`: a constant sequence of expectations `1/2` with `limsup_T A_T ω = 1` and `liminf_T A_T ω = 0` at every `ω` satisfies "eventually `E[A_T] ≤ 1/2`" while `E[limsup_T A_T] = 1 > 1/2`. Documented reason (`LiminfAverageBridge.lean` §"The limsup dual, and the asymmetry it makes explicit"), not a separately Lean-formalized counterexample game — FALSE-by-reason, not machine-checked. |
| U3 (deviation direction), **conditional on `hconv` (a.s. convergence of the deviation profile's own `A_T`)** → limsup-average cap on one fixed deviation | **LANDED, conditional on `hconv`** | `deviation_limsup_le_of_isUniformEquilibriumPayoff` (`LiminfAverageBridge.lean:576`), via `integral_limsup_le_of_bounded_of_tendsto_ae_of_eventually_le` (`LiminfAverageBridge.lean:380`, dominated convergence dualized). Same hypothesis shape as the liminf on-path edge, applied to the deviation profile instead of `σ`. No pipeline row yet. |

**`hconv` is not discharged by anything currently in the tree, for either
aggregation.** It is a missing mathematical property of the specific process
(`pathwiseAveragePayoff`), not missing infrastructure: `IsUniformEquilibriumPayoff`
pins expectations and nothing more, and pinned expectations do not force a.s.
convergence (the moving-bump family above, and its dual, are the reason). No
Lean theorem in the tree discharges `hconv` for any profile, and this
document does not claim one does.

### 2.5 Repeated/monitored (Cluster 5) ↔ Uniform (Cluster 3)

| Edge | Verdict | Evidence |
|---|---|---|
| R1 ↔ U1, via `realizedActionStochasticGame` | **LANDED** | `isεFiniteRepeatedNash_iff_isεHorizonNash` (`RealizedActionRepeatedAdapter.lean:467`). |
| R2 ↔ U2, via the adapter | **LANDED** | `isUniformεEquilibrium_iff` (`RealizedActionRepeatedAdapter.lean:493`). |
| P2 ↔ U3, via the adapter | **LANDED** | `isUniformEquilibriumPayoff_iff` (`RealizedActionRepeatedAdapter.lean:539`). |
| R3 → payoff-level notion, plain `KernelGame` (no monitoring) | **N/A** | No `KernelGame.IsUniformEquilibriumPayoff` is defined — only the monitored generalization P2 exists (in namespace `KernelGame.PublicMonitoring`). There is nothing to compare R3 against at the unmonitored level. |
| P1 → P2, given `HasLongRunAveragePayoff` | **LANDED, conditional** | `IsUniformEquilibrium.isUniformEquilibriumPayoff_of_hasLongRunAveragePayoff` (`RealizedActionRepeatedAdapter.lean:93`). |
| P1 → ∃target, P2 | **LANDED** | `IsUniformEquilibrium.exists_isUniformEquilibriumPayoff` (`RealizedActionRepeatedAdapter.lean:124`). |
| P2 → P1 | **OPEN** | Module docstring, `RealizedActionRepeatedAdapter.lean:84`: *"The converse would require a coherent selection/compactness theorem and is not asserted."* No pipeline row found yet. |

### 2.6 Quitting-specific (Cluster 7) ↔ general (Clusters 3, 0)

| Edge | Verdict | Evidence |
|---|---|---|
| Q1 ↔ Q2 | **LANDED** | `isεQuittingRootEndpointNash_iff_isεQuittingRootNash` (`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean:130-233`), full iff. |
| Q1 (root Bellman-layer, one-shot `PMF Bool`) → exact full-behavior-strategy terminal Nash | **LANDED** | `quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue` (`UniformEquilibrium/Quitting/Cycles/BehaviorPureTimeExtremality.lean:224`) — exact, "legitimate because before absorption a quitting game has exactly one public history" (audit, `2026-08-04-ModelFaithfulness.md:63`). |
| `∀ε>0, U6 instantiated at u = quittingTerminalPayoff` ↔ `∃v, U3` for `quittingGame reward` | **LANDED** | `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean:167`) — full iff. This is the sharp contrast with §2.4: the general liminf-average bridge is one-directional and needs an unbuilt measure; the quitting-specific terminal bridge is a full iff with **no** measure needed, because `quittingTerminalPayoff` is a finite absorption-weighted sum, not a liminf, and its Cesàro-limit identity is itself proved (`tendsto_finiteAveragePayoff_quittingGame`, audit §1). |
| Q3 (`HasUniformDeviationUpperApproximation`, deviation direction only) + Q1/Q2 → U3, quitting | **LANDED** | `quittingGame_hasUniformDeviationUpperApproximation` (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformization.lean:75-198`) — "the quitting-specific content of Solan–Vieille Prop. 2.13," one-sided (deviation-cap direction only; audit §5). |
| Q5 ∨ Q6 (zero-solo or admissible-cycle) → ∃v, U3 for that reward table | **LANDED (conditional on the disjunction, per table)** | `exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle` (`UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`, `HEADLINE`). |
| "every reward table satisfies Q5 ∨ Q6" (the disjunction is exhaustive) | **FALSE** | `not_forall_isQuittingZeroSolo_or_hasAdmissibleAbsorbingQuittingCycle` (`UniformEquilibrium/Quitting/Boundary/Repair/DisjunctionCounterexample.lean:676`) — proves the disjunction is not exhaustive, so the theorem above can never be upgraded to unconditional existence for quitting games (audit, weakness #1). |
| M1 (stagewise pure Nash) instantiated at `quittingGame reward` → any of Q1–Q4, U3-for-quitting | **N/A** | Verified zero occurrences: `grep -n quittingGame Languages/MultiRound/StochasticGame.lean` and `rg -n IsMarkovNash GameTheory/Concepts/Stochastic -g '*.lean'` both return nothing. M1 is never instantiated at `quittingGame` anywhere in the tree; the boundary notion simply is not connected to anything, general or quitting-specific. |
| `quittingGame_exists_uniformEquilibriumPayoff` (the open conjecture, quitting case) | **OPEN — the module's own intentional `sorry`** | `UniformEquilibrium/Quitting/Conjecture/Basic.lean:148`. Not a relation between two notions but the existence statement itself; listed for completeness since it is the terminus every quitting edge above points toward. |

## 3. General/quitting boundary, stated explicitly

Notions that exist **only** for quitting games, with no general-game
counterpart anywhere in the tree: Q1 (`IsεQuittingRootNash`), Q2
(`IsεQuittingRootEndpointNash`), Q4 (`quittingTerminalPayoff`), Q5
(`IsQuittingZeroSolo`), Q6 (`HasAdmissibleAbsorbingQuittingCycle`), and the
~130-file `Quitting*` combinatorial machinery feeding Q5/Q6. Q3
(`HasUniformDeviationUpperApproximation`) is stated at general-game
generality (any `u`, any `StochasticGame`) but is used nowhere outside the
quitting bridge chain — a general-purpose tool with a quitting-only import
graph, not a quitting-only definition.

Conversely, every *general* notion (M1–M4, D1–D2, U1–U6, R1–R3, P1–P2)
applies to `quittingGame reward` without modification, since it is an
ordinary `StochasticGame` with `Act = Bool`. The audit's finding stands:
**nothing in the tree instantiates M1 (stagewise pure Nash) at a quitting
game**, and no theorem connects the quitting-specific Bellman-layer notions
(Q1/Q2) to the general Markov-level notions (M1/M2) at all — only to the
full behavior-strategy notions (U3, U6), skipping the Markov layer entirely.

## 4. Implications assumed in prose without a theorem behind them

The highest-value output of this exercise, per the brief. Two were found,
both already self-flagged in their own module docstrings rather than
silently assumed — which is the honest state of the program, but each is
still a real gap with no landed theorem and (for the second) no pipeline row:

1. **D2 → D1** (§2.2) — now `LANDED`, and the first pass of this document got
   its evidence wrong. The claim that `.finiteAveragePayoff_ge/_le` and
   `.deviation_finiteAveragePayoff_le` carry this content piecewise across
   37+ files is **false**: those lemmas bound `finiteAveragePayoff`, the
   undiscounted Cesàro average, not `discountedPayoff`, which is what
   `IsDiscountedεNash` uses. They feed the separate D2-family → U3 bridge,
   already recorded elsewhere in §2.2. So the edge was genuinely unproved, but
   for a different reason than stated, and the pervasive downstream use was of
   a different implication.

   The lesson generalizes past this cell: a registry that records *which
   lemmas discharge an edge* can be wrong about the lemmas while right that
   the edge is open. Cited witnesses must be checked against the notion each
   one actually mentions, not against the notion the edge is about.
2. **P2 → P1** (§2.5): explicitly flagged in the module docstring
   (`RealizedActionRepeatedAdapter.lean:84`) as needing "a coherent
   selection/compactness theorem" that is "not asserted" — correctly not
   claimed as landed, but also not yet given a pipeline row.

Both are added here rather than to `PIPELINE.md` directly, since queue
placement is a project-control decision for the maintainer, not this audit.

## 5. What was checked and found absent

`grep -rn "IsMarkovNash" GameTheory/` — one declaration file only, zero
importers. `grep -rn "def IsLiminfAverage\|LiminfAverageEquilibrium"
GameTheory/` — no matches; confirmed no such `Prop` exists (§1, Cluster 4).
`grep -rn "def.*StochasticGame" GameTheory/` — exactly one `structure
StochasticGame`, in `Languages/MultiRound/StochasticGame.lean`;
`Concepts/Stochastic/Core/Basic.lean` reopens its namespace rather than defining a
second, unrelated structure of the same name — so every notion in Clusters
1–7 quantifies over the *same* underlying game object, which is why the
gaps recorded above are gaps in missing theorems, not gaps in incompatible
definitions.
