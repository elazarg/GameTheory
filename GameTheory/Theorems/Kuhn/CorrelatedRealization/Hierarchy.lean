/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Languages.Kuhn.ObsModel
import GameTheory.Languages.Kuhn.MixedToBehavioralCore
import GameTheory.Theorems.Kuhn.CorrelatedRealization.ObsLocality

set_option autoImplicit false

namespace ObsModel

open Math.ProbabilityMassFunction Math.ParameterizedChain Math.TraceRun

attribute [local instance] Fintype.ofFinite

variable {ι σ : Type} {Obs : ι → Type} {Act : (i : ι) → Obs i → Type}
variable {O : ObsModel ι σ Obs Act}


/-! ## Semantic vs syntactic conditions

The Kuhn M→B proof uses two kinds of conditions:

**Syntactic conditions** — structural properties of the game model `M` and info structure `I`,
independent of dynamics `D`:
- `PerStepActionRecall O` (PSAR): joint action determined by joint obs transition
- `PlayerStepRecall O i`: player i's action determined by own obs transition
- `PerStepPlayerRecall O` (PSPR = ∀ i, PlayerStepRecall O i)
- `ReachablePlayerStepRecall O i`: PlayerStepRecall restricted to step-reachable states
- `PerfectRecall I`: full history reconstruction from observations

**Semantic conditions** — properties of the execution semantics, depending on dynamics `D`:
- `ObsLocalFeasibility D i`: whether a continuation πᵢ is feasible at a reachable trace
  depends only on player i's observation
- `StepActionDeterminism D`: at any reachable transition, the joint action that
  caused the transition is uniquely determined

The key relationships:

```
Syntactic → Semantic (always holds):
  PSAR + PlayerStepRecall O i  →  ObsLocalFeasibility D i  (for all D)
  PSAR                         →  StepActionDeterminism D   (for all D)

Semantic ↛ Syntactic (converse fails):
  ObsLocalFeasibility may hold for specific D without PlayerStepRecall
  (e.g., dynamics that make certain transitions impossible)
```
-/

section SemanticConditions

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

noncomputable local instance semanticToCoreInfoStateFintype
    [∀ i, Fintype (O.InfoState i)] (i : ι) :
    Fintype (O.toCore.InfoState i) := by
  simpa [ObsModel.toCore, ObsModelCore.InfoState] using
    ((inferInstance : ∀ i, Fintype (O.InfoState i)) i)

noncomputable local instance semanticToCoreInfoStateFintypeFamily
    [∀ i, Fintype (O.InfoState i)] :
    ∀ i, Fintype (O.toCore.InfoState i) :=
  fun i => semanticToCoreInfoStateFintype (O := O) i

/-- Semantic locality on `ObsModel`, viewed as the corresponding core condition on
`O.toCore`. This is the semantic content of what `PlayerStepRecall O i` provides
in the Kuhn proof. Unlike `PlayerStepRecall`, this condition depends on the
dynamics. -/
abbrev ObsLocalFeasibility (i : ι) : Prop :=
  ObsModelCore.ObsLocalFeasibility O.toCore i

/-- Full semantic locality on `ObsModel`, viewed as the corresponding core
condition on `O.toCore`. Unlike `ObsLocalFeasibility`, this has no
`Subsingleton` guard on the current action type. -/
abbrev ObsLocalFeasibilityFull (i : ι) : Prop :=
  ObsModelCore.ObsLocalFeasibilityFull O.toCore i

/-- Minimal semantic locality on `ObsModel`, viewed as the corresponding core
posterior-local condition on `O.toCore`. -/
abbrev ActionPosteriorLocal (O : ObsModel ι σ Obs Act)
    [∀ i, Fintype (O.InfoState i)] (i : ι) : Prop :=
  ObsModelCore.ActionPosteriorLocal O.toCore i

/-- **Semantic condition**: At any reachable transition `(s, a, t)`, the joint action `a`
is uniquely determined by the source-target pair `(s, t)`.

This is the semantic content of what `PerStepActionRecall` provides: at reachable
transitions with the same obs-equivalence classes, the action must be the same.
Since `StepActionDeterminism` applies to the *same* states (reflexive obs-equivalence),
it is strictly weaker than PSAR. -/
abbrev StepActionDeterminism (O : ObsModel ι σ Obs Act) : Prop :=
  ObsModelCore.StepActionDeterminism O.toCore

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] in
/-- PSAR implies step action determinism.
PSAR with reflexive obs-equivalence (same source, same target) gives action uniqueness. -/
theorem PerStepActionRecall.toStepActionDeterminism
    (hPSAR : PerStepActionRecall O) :
    O.StepActionDeterminism :=
  ObsModelCore.PerStepActionRecall.toStepActionDeterminism (O := O.toCore) hPSAR

open Classical in
/-- **Syntactic → Semantic**: PSAR + `PlayerStepRecall O i` implies `ObsLocalFeasibility D i`
for any dynamics `D`.

This is exactly `pureRun_update_obs_local_player`, restated as an implication between
named conditions. -/
theorem obsLocalFeasibility_of_playerStepRecall
    (hPSAR : PerStepActionRecall O) (i : ι) (hPSR_i : PlayerStepRecall O i)
    : O.ObsLocalFeasibility i := by
  intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ _ πᵢ
  have hn : n₁ = n₂ := by
    have hlen : ss₁.length = ss₂.length := O.projectStates_eq_length i hobs
    have hrun₁ := pureRun_length (O.pureStep) O.init n₁ π₀ ss₁ h₁
    have hrun₂ := pureRun_length (O.pureStep) O.init n₂ π₀' ss₂ h₂
    omega
  subst hn
  exact pureRun_update_obs_local_player hPSAR i hPSR_i n₁ hobs h₁ h₂ πᵢ

/-- Under `PerStepPlayerRecall` (= ∀ i, PlayerStepRecall O i), obs-local feasibility
holds for every player and any dynamics. -/
theorem obsLocalFeasibility_of_pspr
    (hPSPR : PerStepPlayerRecall O) (i : ι) :
    O.ObsLocalFeasibility i :=
  obsLocalFeasibility_of_playerStepRecall
    hPSPR.toAction i (perStepPlayerRecall_iff_forall.mp hPSPR i)

/-- Per-player step action equality at reachable states: like
`pureStep_component_eq_of_playerRecall` but using the weaker
`ReachablePlayerStepRecall` with explicit step-reachability witnesses. -/
theorem pureStep_component_eq_of_reachablePlayerRecall
    (i : ι) (hRPSR_i : O.ReachablePlayerStepRecall i)
    {π π' : PureProfile O} {ss ss' : List σ} {t t' : σ}
    (hobs_i : O.projectStates i ss = O.projectStates i ss')
    (hobst_i : O.obsEq i t t')
    (h1 : O.pureStep π ss t ≠ 0) (h2 : O.pureStep π' ss' t' ≠ 0)
    (hreach_s : O.StepReachable (O.lastState ss))
    (hreach_s' : O.StepReachable (O.lastState ss')) :
    π i (O.projectStates i ss) = hobs_i ▸ π' i (O.projectStates i ss') := by
  rw [pureStep_eq] at h1 h2
  have hpspr := hRPSR_i.action_eq h1 h2
    (O.obsEq_of_projectStates_getLast i hobs_i) hobst_i hreach_s hreach_s'
  apply eq_of_heq
  exact ((rec_heq_of_heq _ HEq.rfl).symm).trans
    (((rec_heq_of_heq _ HEq.rfl).symm).trans
      ((heq_of_eq hpspr).trans (rec_heq_of_heq _ HEq.rfl))) |>.trans
    (rec_heq_of_heq
      (C := fun v => Act i (O.currentObs i v))
      (x := π' i (O.projectStates i ss'))
      (y := π' i (O.projectStates i ss'))
      hobs_i.symm HEq.rfl).symm

open Classical in
/-- **Weakest syntactic → semantic**: PSAR + `ReachablePlayerStepRecall O i`
implies `ObsLocalFeasibility D i`. This uses the weakest syntactic condition
that the Kuhn proof actually needs.

The key insight: `pureRun_update_obs_local_player` only invokes
`PlayerStepRecall` at states reached via `pureRun` with nonzero probability,
which are exactly the step-reachable states. -/
theorem obsLocalFeasibility_of_reachablePlayerStepRecall
    (hPSAR : PerStepActionRecall O) (i : ι)
    (hRPSR_i : O.ReachablePlayerStepRecall i)
    : O.ObsLocalFeasibility i := by
  intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ _ πᵢ
  have hn : n₁ = n₂ := by
    have hlen : ss₁.length = ss₂.length := O.projectStates_eq_length i hobs
    have hrun₁ := pureRun_length (O.pureStep) O.init n₁ π₀ ss₁ h₁
    have hrun₂ := pureRun_length (O.pureStep) O.init n₂ π₀' ss₂ h₂
    omega
  subst hn
  exact pureRun_update_obs_local_of hPSAR n₁ i hobs h₁ h₂
    (fun m p₁ p₂ _ _ hobs_p hobst hp₁ hp₂ ht₁ ht₂ =>
      pureStep_component_eq_of_reachablePlayerRecall i hRPSR_i
        hobs_p hobst ht₁ ht₂
        (pureRun_nonzero_last_stepReachable m _ p₁ hp₁)
        (pureRun_nonzero_last_stepReachable m _ p₂ hp₂)) πᵢ

/-- Step-level action equality under `TracePlayerStepRecall`:
at pureStep-supported transitions from traces with equal obs-projections,
the player-i action components agree. -/
theorem pureStep_component_eq_of_tracePlayerRecall
    (i : ι) (hTPSR : O.TracePlayerStepRecall i)
    {π π' : PureProfile O} {ss ss' : List σ} {t t' : σ}
    (hproj : O.projectStates i ss = O.projectStates i ss')
    (hobst : O.obsEq i t t')
    (h1 : O.pureStep π ss t ≠ 0) (h2 : O.pureStep π' ss' t' ≠ 0)
    (hreach : Nonempty (O.ReachActionTrace ss))
    (hreach' : Nonempty (O.ReachActionTrace ss')) :
    π i (O.projectStates i ss) = hproj ▸ π' i (O.projectStates i ss') := by
  rw [pureStep_eq] at h1 h2
  have rat_ne : ∀ {l : List σ}, Nonempty (O.ReachActionTrace l) → l ≠ [] := by
    intro l ⟨r⟩; cases r with
    | init => exact List.cons_ne_nil _ _
    | snoc _ _ _ _ => exact List.concat_ne_nil _ _
  have hlast_eq : ∀ {l : List σ}, l ≠ [] → l.getLast? = some (O.lastState l) := by
    intro l hl; cases hg : l.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp hg) hl
    | some s => simp [ObsModel.lastState, ObsModelCore.lastState, hg]
  have hpspr := hTPSR.action_eq hreach hreach'
    (hlast_eq (rat_ne hreach)) (hlast_eq (rat_ne hreach')) hproj h1 h2 hobst
    (O.obsEq_of_projectStates_getLast i hproj)
  apply eq_of_heq
  exact ((rec_heq_of_heq _ HEq.rfl).symm).trans
    (((rec_heq_of_heq _ HEq.rfl).symm).trans
      ((heq_of_eq hpspr).trans (rec_heq_of_heq _ HEq.rfl))) |>.trans
    (rec_heq_of_heq
      (C := fun v => Act i (O.currentObs i v))
      (x := π' i (O.projectStates i ss'))
      (y := π' i (O.projectStates i ss'))
      hproj.symm HEq.rfl).symm

open Classical in
/-- **Tightest syntactic → semantic**: PSAR + `TracePlayerStepRecall O i`
implies `ObsLocalFeasibility D i`.

This is strictly tighter than `obsLocalFeasibility_of_reachablePlayerStepRecall`
because `TracePlayerStepRecall` only requires action agreement at states
reached via traces with equal full player information states, not at all
obs-equivalent reachable states. The proof's induction naturally maintains
the stronger `projectStates i p₁ = projectStates i p₂` invariant. -/
theorem obsLocalFeasibility_of_tracePlayerStepRecall
    (hPSAR : PerStepActionRecall O) (i : ι)
    (hTPSR : O.TracePlayerStepRecall i)
    : O.ObsLocalFeasibility i := by
  intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ _ πᵢ
  have hn : n₁ = n₂ := by
    have hlen : ss₁.length = ss₂.length := O.projectStates_eq_length i hobs
    have hrun₁ := pureRun_length (O.pureStep) O.init n₁ π₀ ss₁ h₁
    have hrun₂ := pureRun_length (O.pureStep) O.init n₂ π₀' ss₂ h₂
    omega
  subst hn
  exact pureRun_update_obs_local_of hPSAR n₁ i hobs h₁ h₂
    (fun m p₁ p₂ _ _ hobs_p hobst hp₁ hp₂ ht₁ ht₂ =>
      pureStep_component_eq_of_tracePlayerRecall i hTPSR
        hobs_p hobst ht₁ ht₂
        (pureRun_nonzero_to_reachActionTrace m _ p₁ hp₁)
        (pureRun_nonzero_to_reachActionTrace m _ p₂ hp₂)) πᵢ

end SemanticConditions

/-! ### Trace-level obs-locality

The following theorems establish obs-locality under `TracePlayerStepRecall`,
the weakest syntactic condition in the hierarchy. They are placed after
`SemanticConditions` because they depend on `pureStep_component_eq_of_tracePlayerRecall`
and `pureRun_nonzero_to_reachActionTrace` from that section. -/

open Classical in
/-- Under PSAR + `TracePlayerStepRecall O i`, updating player `i`'s strategy
preserves feasibility across obs-equivalent traces. -/
theorem pureRun_update_obs_local_trace
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (hPSAR : PerStepActionRecall O) (i : ι)
    (hTPSR : O.TracePlayerStepRecall i)
    (n : Nat)
    {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List σ}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (O.pureStep) O.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (O.pureStep) O.init n π₀' ss₂ ≠ 0)
    (πᵢ : O.LocalStrategy i) :
    pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
    pureRun (O.pureStep) O.init n (Function.update π₀' i πᵢ) ss₂ ≠ 0 :=
  pureRun_update_obs_local_of hPSAR n i hobs_i h₁ h₂
    (fun m p₁ p₂ _ _ hobs_p hobst hp₁ hp₂ ht₁ ht₂ =>
      pureStep_component_eq_of_tracePlayerRecall i hTPSR
        hobs_p hobst ht₁ ht₂
        (pureRun_nonzero_to_reachActionTrace m _ p₁ hp₁)
        (pureRun_nonzero_to_reachActionTrace m _ p₂ hp₂)) πᵢ

open Classical in
/-- Under PSAR + `TracePlayerStepRecall O i`, `reweightPMF` is obs-local for player `i`. -/
theorem reweightPMF_update_obs_local_trace
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    [∀ i, Fintype (O.InfoState i)]
    (hPSAR : PerStepActionRecall O) (i : ι)
    (hTPSR : O.TracePlayerStepRecall i)
    (n : Nat)
    (b_i : PMF (O.LocalStrategy i))
    {π₀ π₀' : PureProfile O} {ss₁ ss₂ : List σ}
    (hobs_i : O.projectStates i ss₁ = O.projectStates i ss₂)
    (h₁ : pureRun (O.pureStep) O.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (O.pureStep) O.init n π₀' ss₂ ≠ 0) :
    reweightPMF b_i
      (fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀ i πᵢ) ss₁) =
    reweightPMF b_i
      (fun πᵢ => pureRun (O.pureStep) O.init n (Function.update π₀' i πᵢ) ss₂) :=
  reweightPMF_update_obs_local_of hPSAR n n i b_i h₁ h₂
    fun πᵢ => pureRun_update_obs_local_trace hPSAR i hTPSR n hobs_i h₁ h₂ πᵢ

/-- Trace-level recall implies full obs-local feasibility for the semantic core.

This is the packaging lemma needed by the core mixed-to-behavioral theorem
whose support-factorization route requires locality even at subsingleton action
states. The actual induction is `pureRun_update_obs_local_trace`; this theorem
only reconciles the core `ObsLocalFeasibilityFull` shape. -/
theorem obsLocalFeasibilityFull_of_tracePlayerStepRecall
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (hPSAR : PerStepActionRecall O) (i : ι)
    (hTPSR : O.TracePlayerStepRecall i) :
    O.ObsLocalFeasibilityFull i := by
  intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ πᵢ
  have hn : n₁ = n₂ := by
    have hlen : ss₁.length = ss₂.length := O.projectStates_eq_length i hobs
    have hrun₁ := pureRun_length (O.pureStep) O.init n₁ π₀ ss₁ h₁
    have hrun₂ := pureRun_length (O.pureStep) O.init n₂ π₀' ss₂ h₂
    omega
  subst hn
  exact pureRun_update_obs_local_trace hPSAR i hTPSR n₁ hobs h₁ h₂ πᵢ

/-- Semantic locality hypotheses on `ObsModel` are exactly the corresponding core
locality hypotheses on `O.toCore`. -/
theorem obsLocalFeasibility_toCore
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (hLocal : ∀ i, O.ObsLocalFeasibility i) :
    ∀ i, ObsModelCore.ObsLocalFeasibility O.toCore i := by
  intro i
  simpa [ObsModel.ObsLocalFeasibility] using hLocal i

/-- Full semantic locality hypotheses on `ObsModel` are exactly the
corresponding full core locality hypotheses on `O.toCore`. -/
theorem obsLocalFeasibilityFull_toCore
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    (hLocal : ∀ i, O.ObsLocalFeasibilityFull i) :
    ∀ i, ObsModelCore.ObsLocalFeasibilityFull O.toCore i := by
  intro i
  simpa [ObsModel.ObsLocalFeasibilityFull] using hLocal i

/-- Stronger feasibility-locality hypotheses imply the minimal posterior-local
core hypotheses. -/
theorem actionPosteriorLocal_toCore
    [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
    [∀ i, Fintype (O.InfoState i)]
    (hDet : ObsModelCore.StepMassInvariant O.toCore)
    (hLocal : ∀ i, O.ObsLocalFeasibility i) :
    ∀ i, O.ActionPosteriorLocal i := by
  letI : ∀ j, Fintype (O.toCore.InfoState j) := by
    intro j
    simpa [ObsModel.toCore, ObsModelCore.InfoState] using
      ((inferInstance : ∀ j, Fintype (O.InfoState j)) j)
  change ∀ i, ObsModelCore.ActionPosteriorLocal O.toCore i
  intro i
  exact ObsModelCore.actionPosteriorLocal_of_obsLocalFeasibility
    (O := O.toCore) hDet i (obsLocalFeasibility_toCore hLocal i)

/-! ## Kuhn theorem hierarchy

The results in this file form a hierarchy of increasingly specific realization
theorems:

### Level 0: Correlated realization (no recall needed)
`correlated_realization`: For any `ν : PMF (PureProfile O)`, there exists a
state-trace mediator producing the same outcome distribution. No structural
assumptions on the game.

### Level 1: Observation-level correlated realization (PSAR)
`obs_correlated_realization`: Under `PerStepActionRecall`, the state-trace
mediator factors through observations, giving a `BehavioralProfileCorr O`
(correlated behavioral profile).

### Level 2: Product preservation (PSAR)
`conditioning_preserves_product`: Under PSAR, if the ex ante
distribution is a product (`pmfPi μ`), conditioning on reaching any
trace gives a product at the strategy level. The reach weight is
cross-multiplicatively equivalent to a per-player product weight
(`pureRun_cross_mul_product`), and product weights on product
distributions factor (`reweightPMF_pmfPi`).

`mediator_product_of_product`: The action-level corollary — product
ν gives product mediator output at each reachable trace.

### Level 3: Per-player obs-locality (PSAR + PlayerStepRecall i)
`reweightPMF_update_obs_local_player`: Under PSAR + `PlayerStepRecall O i`,
the i-th factor of the product mediator depends only on player i's
information state. This is the per-player content — each player's decentralization
needs only their own recall condition.

### Level 4: Full decentralization
`kuhn_mixed_to_behavioral_semantic`: Main theorem, stated over the
minimal semantic posterior-locality condition `ActionPosteriorLocal`.

`kuhn_mixed_to_behavioral_trace`: Syntactic corollary under the weakest
currently proved recall condition (PSAR + per-player trace step recall).

`kuhn_mixed_to_behavioral_pspr`: PSPR corollary (via PlayerStepRecall → TracePlayerStepRecall).
`kuhn_mixed_to_behavioral_decomposed`: Per-player corollary.

### Weakening the per-player condition

`ReachablePlayerStepRecall O i`: `PlayerStepRecall O i` restricted to
step-reachable source states.

`TracePlayerStepRecall O i`: Even tighter — requires action agreement
only at reachable states reached via traces with equal **full**
player information states (`projectStates i ss = projectStates i ss'`),
not merely obs-equivalent endpoints (`obsEq i s s'`).

Syntactic implication chain:
```
  PSPR = ∀ i, PlayerStepRecall O i
               ↓ (drop reachability req)
         ∀ i, ReachablePlayerStepRecall O i
               ↓ (strengthen hyp: obsEq → full trace eq)
         ∀ i, TracePlayerStepRecall O i
               ↑ (PerfectRecall → Reachable → Trace)
         PerfectRecall = ObsRecall ∧ ActionRecall
```

Neither PSPR nor PerfectRecall implies the other:
- PSPR constrains ALL transitions; PerfectRecall only reachable traces
- PerfectRecall reconstructs full history; PSPR is one-step

### Semantic conditions

`ObsLocalFeasibility D i`: stronger feasibility-style locality.

`ActionPosteriorLocal D i`: the posterior law of player `i`'s local action,
after conditioning on reaching the trace, depends only on player `i`'s
information state. This is the actual condition used by the theorem.

`StepActionDeterminism D`: at any transition, the action is determined
by the source-target pair. Semantic content of PSAR (reflexive case).

Full syntactic → semantic implication graph:
```
  PlayerStepRecall O i → ReachablePlayerStepRecall O i
    → TracePlayerStepRecall O i → (+ PSAR) ObsLocalFeasibility D i

  PerfectRecall → ReachablePlayerStepRecall O i (via ActionRecall)
  PSAR → StepActionDeterminism D
```

The semantic conditions depend on D; syntactic ones do not. The converse
(semantic → syntactic) does not hold: dynamics-specific feasibility can
make obs-locality hold without the syntactic action-uniqueness property. -/

section Hierarchy

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.InfoState i)]

open Math.PMFProduct

noncomputable local instance hierarchyToCoreInfoStateFintype (i : ι) :
    Fintype (O.toCore.InfoState i) := by
  simpa [ObsModel.toCore, ObsModelCore.InfoState] using
    ((inferInstance : ∀ i, Fintype (O.InfoState i)) i)

noncomputable local instance hierarchyToCoreInfoStateFintypeFamily :
    ∀ i, Fintype (O.toCore.InfoState i) :=
  fun i => hierarchyToCoreInfoStateFintype (O := O) i

open Classical in
/-- **Core Kuhn M→B theorem**: under step-action determinism and the semantic
locality condition `ObsLocalFeasibility`, every product distribution over pure
profiles is realized by an independent behavioral profile with the same trace
distribution.

This is the correct abstraction boundary for the mixed-to-behavioral direction:
the theorem only assumes the semantic locality actually used by the proof.
Syntactic recall principles such as `TracePlayerStepRecall` are handled later
as sufficient conditions implying `ObsLocalFeasibility`. -/
theorem kuhn_mixed_to_behavioral_semantic [∀ i o, Nonempty (Act i o)]
    (hPSAR : PerStepActionRecall O)
    (hLocal : ∀ i, ObsModel.ActionPosteriorLocal O i)
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (k : Nat) :
  ∃ β : BehavioralProfile O,
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k) := by
  have hDet : ObsModelCore.StepActionDeterminism O.toCore := hPSAR.toStepActionDeterminism
  change ∃ β : BehavioralProfile O,
    O.toCore.runDist k β = (pmfPi μ).bind (O.toCore.runDistPure k)
  exact ObsModelCore.kuhn_mixed_to_behavioral_semantic (O := O.toCore)
    hDet.toMassInvariant hDet.toSupportFactorization
    (fun i => by simpa [ObsModel.ActionPosteriorLocal] using hLocal i) μ k

omit [∀ i, Fintype (O.InfoState i)] in
/-- **Kuhn M→B under the weakest current syntactic condition**:
`PSAR + ∀ i, TracePlayerStepRecall O i`.

This is now a corollary of the semantic theorem
`kuhn_mixed_to_behavioral_semantic`, using the derived implication
`TracePlayerStepRecall -> ObsLocalFeasibility -> ActionPosteriorLocal`. -/
theorem kuhn_mixed_to_behavioral_trace
    [∀ i, Finite (O.InfoState i)] [∀ i o, Nonempty (Act i o)]
    (hPSAR : PerStepActionRecall O)
    (hTPSR : ∀ i, O.TracePlayerStepRecall i)
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (k : Nat) :
    ∃ β : BehavioralProfile O,
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k) := by
  let hMass : ObsModelCore.StepMassInvariant O.toCore :=
    (hPSAR.toStepActionDeterminism).toMassInvariant
  letI : ∀ j, Fintype (O.toCore.InfoState j) := by
    intro j
    simpa [ObsModel.toCore, ObsModelCore.InfoState] using
      Fintype.ofFinite (O.InfoState j)
  change ∃ β : BehavioralProfile O,
    O.toCore.runDist k β = (pmfPi μ).bind (O.toCore.runDistPure k)
  exact ObsModelCore.kuhn_mixed_to_behavioral_of_obsLocal
    (O := O.toCore) hMass
    (obsLocalFeasibilityFull_toCore
      (O := O)
      (fun i => obsLocalFeasibilityFull_of_tracePlayerStepRecall
        hPSAR i (hTPSR i)))
    μ k

omit [∀ i, Fintype (O.InfoState i)] in
/-- **Generalized Kuhn (M→B) under PSPR**: For any product distribution over
pure profiles, there exists an independent behavioral profile producing the
same trace distribution.

Corollary of `kuhn_mixed_to_behavioral_semantic` via
`PerStepPlayerRecall -> ObsLocalFeasibility -> ActionPosteriorLocal`. -/
theorem kuhn_mixed_to_behavioral_pspr
    [∀ i, Finite (O.InfoState i)] [∀ i o, Nonempty (Act i o)]
    (hPSPR : PerStepPlayerRecall O) (μ : ∀ i, PMF (O.LocalStrategy i))
    (k : Nat) :
    ∃ β : BehavioralProfile O,
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k) := by
  let hDet : ObsModelCore.StepMassInvariant O.toCore :=
    (hPSPR.toAction.toStepActionDeterminism).toMassInvariant
  letI : ∀ j, Fintype (O.toCore.InfoState j) := by
    intro j
    simpa [ObsModel.toCore, ObsModelCore.InfoState] using
      Fintype.ofFinite (O.InfoState j)
  exact kuhn_mixed_to_behavioral_semantic hPSPR.toAction
    (fun i => by
      simpa [ObsModel.ActionPosteriorLocal] using
        ObsModelCore.actionPosteriorLocal_of_obsLocalFeasibility
          (O := O.toCore) hDet i
          ((obsLocalFeasibility_of_pspr hPSPR i : O.ObsLocalFeasibility i)))
    μ k

omit [∀ i, Fintype (O.InfoState i)] in
/-- **Per-player Kuhn M→B**: each player individually needs `PlayerStepRecall`.
Logically equivalent to `kuhn_mixed_to_behavioral_pspr` since
`PSPR ↔ ∀ i, PlayerStepRecall O i` (and PSPR → PSAR).

The conceptual value is that it shows the proof decomposes cleanly per player:
the global PSAR handles the reach structure (derived from the per-player
conditions), while each player's factor obs-locality uses only their own
`PlayerStepRecall`. See `reweightPMF_update_obs_local_player` for the
corresponding local conditioning lemma. -/
theorem kuhn_mixed_to_behavioral_decomposed
    [∀ i, Finite (O.InfoState i)] [∀ i o, Nonempty (Act i o)]
    (hPSR : ∀ i, PlayerStepRecall O i)
    (μ : ∀ i, PMF (O.LocalStrategy i))
    (k : Nat) :
    ∃ β : BehavioralProfile O,
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k) :=
  kuhn_mixed_to_behavioral_pspr
    (perStepPlayerRecall_iff_forall.mpr hPSR) μ k

end Hierarchy

end ObsModel
