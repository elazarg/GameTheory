import GameTheory.Languages.Sequential.SOS
import GameTheory.Theorems.Kuhn.MixedToBehavioralCore
import Mathlib.Data.List.TakeDrop

/-!
# Linearized Compilation of Sequential Protocols to ObsModelCore

Compiles a sequential protocol to an `ObsModelCore` where each step involves
**at most one player** making a nontrivial action choice. This is achieved by
splitting each simultaneous action phase into `n` sequential per-player
sub-phases.

The key advantage over the standard `compileObsCoreModel` (which processes all
players simultaneously): `StepSupportFactorization` holds trivially, enabling
Kuhn's theorem without any special recall conditions.

## Design

The state type `LinConfig G` extends `Config G` with a `playerTurn` variant that
tracks which player is currently choosing their action. At each `playerTurn`
sub-step, only the acting player has a nontrivial observation (their view) and
action type (`Option A`). All other players see `none` and have trivial action
type `PUnit`.

## Main definitions

- `LinConfig G` — extended configuration with per-player action sub-phases
- `LinAct V A` — observation-dependent action type (nontrivial only when active)
- `linConfigStepPMF` — per-player step function
- `compileObsCoreModelLin` — linearized ObsModelCore compilation
-/

namespace GameTheory.Sequential

open GameTheory

variable {n : Nat} {S V A Sig : Type}

-- ============================================================================
-- Linearized configuration
-- ============================================================================

/-- Extended configuration for the linearized model. The `playerTurn` variant
decomposes the simultaneous action phase into per-player sub-phases.

- `signal k s` — waiting for signal at round `k`, state `s`
- `playerTurn k s sig p accActs` — player `p` is choosing; players `< p` have
  already committed their actions in `accActs`
- `applyTransition k s sig accActs` — all players have acted; apply transition
- `terminal s` — game over

The `applyTransition` phase separates the transition application from the last
player's action storage. This ensures every player's step is injective in their
action (the action is stored as a field of the successor state), which is needed
for `ObsLocalFeasibility` and hence Kuhn's M→B theorem. -/
inductive LinConfig (G : Protocol n S V A Sig) where
  | signal (round : Nat) (state : S)
  | playerTurn (round : Nat) (state : S) (sig : Fin n → Sig)
      (currentPlayer : Fin n) (accActs : Fin n → Option A)
  | applyTransition (round : Nat) (state : S) (sig : Fin n → Sig)
      (accActs : Fin n → Option A)
  | terminal (state : S)

/-- Initial configuration for the linearized model. -/
def linInitialConfig (G : Protocol n S V A Sig) : LinConfig G :=
  if G.rounds[0]? = none then .terminal G.init else .signal 0 G.init

-- ============================================================================
-- Observations and actions
-- ============================================================================

/-- Round-indexed observation type. Includes the round number to distinguish
the same view at different rounds, which is essential for `ObsLocalFeasibility`
(ensures OLF only compares traces at the same round, where FullRecall applies). -/
abbrev RoundView (G : Protocol n S V A Sig) := Fin G.rounds.length × V

/-- Player-local observation in the linearized model.
Only the currently acting player has a nontrivial observation, which includes
the round number. -/
def linObserve (G : Protocol n S V A Sig) [DecidableEq (Fin n)]
    (i : Fin n) : LinConfig G → Option (RoundView G)
  | .signal _ _ => none
  | .terminal _ => none
  | .applyTransition _ _ _ _ => none
  | .playerTurn k s sig p _ =>
      if i = p then
        if hk : k < G.rounds.length then
          some (⟨k, hk⟩, G.rounds[k].view i s (sig i))
        else none
      else none

/-- Observation-dependent action type: nontrivial (`Option A`) when the player
is active (sees `some (k, v)`), trivial (`PUnit`) when inactive (sees `none`). -/
def LinAct (RV A : Type) : Option RV → Type
  | some _ => Option A
  | none => PUnit

instance linActFintype {O : Type} [Fintype A] : (o : Option O) → Fintype (LinAct O A o)
  | some _ => inferInstanceAs (Fintype (Option A))
  | none => inferInstanceAs (Fintype PUnit)

instance linActNonempty {O : Type} [Nonempty A] : (o : Option O) → Nonempty (LinAct O A o)
  | some _ => inferInstanceAs (Nonempty (Option A))
  | none => ⟨PUnit.unit⟩

-- ============================================================================
-- Linearized step function
-- ============================================================================

/-- Advance to the next sub-phase after player `p` acts. If `p` is the last
player, move to `applyTransition` (which fires the transition in a separate
action-free step). -/
private noncomputable def advancePlayerTurn (G : Protocol n S V A Sig)
    (k : Nat) (s : S) (sig : Fin n → Sig) (p : Fin n) (accActs : Fin n → Option A)
    (_r : Round n S V A Sig) : PMF (LinConfig G) :=
  if h : p.val + 1 < n then
    PMF.pure (.playerTurn k s sig ⟨p.val + 1, h⟩ accActs)
  else
    PMF.pure (.applyTransition k s sig accActs)

/-- Extract the effective `Option A` action for the acting player from a
dependent action tuple at a `playerTurn` configuration. The `cast` resolves
the dependent type to `Option A`. -/
private def extractPlayerAction [DecidableEq (Fin n)] (G : Protocol n S V A Sig)
    (k : Nat) (s : S) (sig : Fin n → Sig) (p : Fin n) (accActs : Fin n → Option A)
    (acts : (i : Fin n) → LinAct (RoundView G) A (linObserve G i (.playerTurn k s sig p accActs)))
    : Option A :=
  if hk : k < G.rounds.length then
      have hobs : linObserve G p (.playerTurn k s sig p accActs) =
          some (⟨k, hk⟩, G.rounds[k].view p s (sig p)) := by
        simp [linObserve, hk]
      cast (congrArg (LinAct (RoundView G) A) hobs) (acts p)
  else
      -- linObserve G p ... = none in this case, so acts p : PUnit → use none
      none

/-- Per-player step function for the linearized model.

- **Signal phase**: sample signal, start player 0's turn with default actions.
- **Player turn**: read the acting player's action, store it, advance to next
  player or to `applyTransition`.
- **Apply transition**: fire the round's transition, advance to next round or terminal.
- **Terminal**: absorbing. -/
noncomputable def linConfigStepPMF [DecidableEq (Fin n)] (G : Protocol n S V A Sig)
    (cfg : LinConfig G)
    (acts : (i : Fin n) → LinAct (RoundView G) A (linObserve G i cfg)) :
    PMF (LinConfig G) :=
  match cfg with
  | .signal k s =>
      match G.rounds[k]? with
      | some r =>
          if hn : 0 < n then
            (r.signal s).map fun sig =>
              .playerTurn k s sig ⟨0, hn⟩ (fun _ => none)
          else
            -- n = 0: no players, go directly to applyTransition
            (r.signal s).map fun sig =>
              .applyTransition k s sig (fun _ => none)
      | none => PMF.pure (.signal k s)
  | .playerTurn k s sig p accActs =>
      match G.rounds[k]? with
      | some r =>
          let accActs' := Function.update accActs p
              (extractPlayerAction G k s sig p accActs acts)
          advancePlayerTurn G k s sig p accActs' r
      | none => PMF.pure (.playerTurn k s sig p accActs)
  | .applyTransition k s _sig accActs =>
      match G.rounds[k]? with
      | some r =>
          let next := r.transition s accActs
          match G.rounds[k + 1]? with
          | some _ => PMF.pure (.signal (k + 1) next)
          | none => PMF.pure (.terminal next)
      | none => PMF.pure (.terminal s)
  | .terminal s => PMF.pure (.terminal s)

-- ============================================================================
-- Compilation to ObsModelCore
-- ============================================================================

/-- Compile a sequential protocol into an `ObsModelCore` with per-player
action sub-phases. At each step, at most one player has a nontrivial action.

- **States**: `LinConfig G` (extended configurations with per-player turns)
- **Players**: `Fin n`
- **Observations**: `Option (RoundView G)` (nontrivial only for the acting player)
- **Actions**: `LinAct (RoundView G) A` (nontrivial only when active)
- **InfoState**: identity — observation = info state -/
noncomputable def compileObsCoreModelLin [DecidableEq (Fin n)]
    (G : Protocol n S V A Sig) :
    ObsModelCore (Fin n) (LinConfig G)
      (fun _ => Option (RoundView G))
      (fun _ => LinAct (RoundView G) A) where
  infoState := fun _ => {
    Carrier := Option (RoundView G)
    start := id
    push := fun _ o => o
    current := id
    current_start := fun _ => rfl
    current_push := fun _ _ => rfl
  }
  observe := linObserve G
  machine := {
    init := linInitialConfig G
    step := linConfigStepPMF G
  }

/-- Abbreviation for the linearized compiled model. -/
noncomputable abbrev compiledLinObs [DecidableEq (Fin n)]
    (G : Protocol n S V A Sig) :=
  compileObsCoreModelLin G

-- ============================================================================
-- Fintype instances for the compiled model
-- ============================================================================

noncomputable instance compiledLinObs_infoState_fintype [DecidableEq (Fin n)]
    [Fintype V] (G : Protocol n S V A Sig) (i : Fin n) :
    Fintype ((compiledLinObs G).InfoState i) :=
  inferInstanceAs (Fintype (Option (Fin G.rounds.length × V)))

noncomputable instance compiledLinObs_infoState_decidableEq [DecidableEq (Fin n)]
    [DecidableEq V] (G : Protocol n S V A Sig) (i : Fin n) :
    DecidableEq ((compiledLinObs G).InfoState i) :=
  inferInstanceAs (DecidableEq (Option (Fin G.rounds.length × V)))

noncomputable instance compiledLinObs_localStrategy_fintype [DecidableEq (Fin n)]
    [DecidableEq V] [Fintype V] [Fintype A] (G : Protocol n S V A Sig) (i : Fin n) :
    Fintype ((compiledLinObs G).LocalStrategy i) :=
  Pi.instFintype

-- ============================================================================
-- Structural properties
-- ============================================================================

section Properties

variable [DecidableEq (Fin n)] [Fintype (Fin n)]
variable [Fintype A] [Nonempty A]

omit [Fintype (Fin n)] [Fintype A] [Nonempty A] in
/-- At every playerTurn state, only the acting player has a nontrivial
observation — all others see `none`. -/
theorem linObserve_ne_acting {G : Protocol n S V A Sig}
    {k : Nat} {s : S} {sig : Fin n → Sig} {p : Fin n}
    {accActs : Fin n → Option A} {i : Fin n} (hi : i ≠ p) :
    linObserve G i (.playerTurn k s sig p accActs) = none := by
  simp [linObserve, hi]

private theorem pure_ne_zero_iff' {α : Type*} (a b : α) :
    (PMF.pure a) b ≠ 0 ↔ b = a := by
  rw [ne_eq, PMF.pure_apply]
  constructor
  · intro h; by_contra hne; exact h (if_neg hne)
  · intro h; subst h; simp

omit [DecidableEq (Fin n)] [Fintype (Fin n)] [Fintype A] [Nonempty A] in
private theorem advancePlayerTurn_mass_invariant (G : Protocol n S V A Sig)
    (k : Nat) (s : S) (sig : Fin n → Sig) (p : Fin n)
    (accActs₁ accActs₂ : Fin n → Option A) (r : Round n S V A Sig)
    (t : LinConfig G)
    (h₁ : (advancePlayerTurn G k s sig p accActs₁ r) t ≠ 0)
    (h₂ : (advancePlayerTurn G k s sig p accActs₂ r) t ≠ 0) :
    (advancePlayerTurn G k s sig p accActs₁ r) t =
    (advancePlayerTurn G k s sig p accActs₂ r) t := by
  unfold advancePlayerTurn at h₁ h₂ ⊢
  split
  · simp_all [PMF.pure_apply]
  · simp_all [PMF.pure_apply]

omit [DecidableEq (Fin n)] [Fintype (Fin n)] [Fintype A] [Nonempty A] in
/-- If two `accActs` both give nonzero probability at the same target through
`advancePlayerTurn`, then the `accActs` must be equal (since the step is `PMF.pure`). -/
private theorem advancePlayerTurn_accActs_eq (G : Protocol n S V A Sig)
    (k : Nat) (s : S) (sig : Fin n → Sig) (p : Fin n)
    (accActs₁ accActs₂ : Fin n → Option A) (r : Round n S V A Sig)
    (t : LinConfig G)
    (h₁ : (advancePlayerTurn G k s sig p accActs₁ r) t ≠ 0)
    (h₂ : (advancePlayerTurn G k s sig p accActs₂ r) t ≠ 0) :
    accActs₁ = accActs₂ := by
  unfold advancePlayerTurn at h₁ h₂
  split at h₁
  · rename_i h_pos
    simp only [dif_pos h_pos] at h₂
    rw [pure_ne_zero_iff'] at h₁ h₂
    have := h₁.symm.trans h₂
    exact (LinConfig.playerTurn.injEq .. ▸ this).2.2.2.2
  · rename_i h_neg
    simp only [dif_neg h_neg] at h₂
    rw [pure_ne_zero_iff'] at h₁ h₂
    have := h₁.symm.trans h₂
    exact (LinConfig.applyTransition.injEq .. ▸ this).2.2.2

omit [DecidableEq (Fin n)] [Fintype (Fin n)] [Fintype A] [Nonempty A] in
/-- `linConfigStepPMF` is mass-invariant: if two action vectors both assign
nonzero probability to the same successor, the step probabilities are equal.

- **Signal**: step ignores actions (samples from signal distribution)
- **PlayerTurn**: `advancePlayerTurn` is `PMF.pure`; equal at `t` by purity
- **Terminal**: absorbing, action-independent -/
private theorem linConfigStepPMF_mass_invariant (G : Protocol n S V A Sig)
    [DecidableEq (Fin n)]
    (cfg : LinConfig G)
    (acts₁ acts₂ : (i : Fin n) → LinAct (RoundView G) A (linObserve G i cfg))
    (t : LinConfig G)
    (h₁ : (linConfigStepPMF G cfg acts₁) t ≠ 0)
    (h₂ : (linConfigStepPMF G cfg acts₂) t ≠ 0) :
    (linConfigStepPMF G cfg acts₁) t = (linConfigStepPMF G cfg acts₂) t := by
  match cfg with
  | .signal _ _ => simp only [linConfigStepPMF] at h₁ h₂ ⊢
  | .playerTurn k s sig p accActs =>
    simp only [linConfigStepPMF] at h₁ h₂ ⊢
    revert h₁ h₂
    match G.rounds[k]? with
    | some r => intro h₁ h₂; exact advancePlayerTurn_mass_invariant G k s sig p _ _ r t h₁ h₂
    | none => intro _ _; rfl
  | .applyTransition _ _ _ _ => simp only [linConfigStepPMF] at h₁ h₂ ⊢
  | .terminal _ => simp only [linConfigStepPMF] at h₁ h₂ ⊢

omit [Nonempty A] in
/-- The linearized model satisfies `StepMassInvariant`.
Signal phases ignore actions entirely. PlayerTurn phases are deterministic
(the step is `PMF.pure` of a single successor). Terminal is absorbing. -/
theorem stepMassInvariant_compiledLin (G : Protocol n S V A Sig) :
    ObsModelCore.StepMassInvariant (compiledLinObs G) := by
  intro ss t π₁ π₂ h₁ h₂
  have eq₁ := ObsModelCore.pureStep_eq π₁ ss
  have eq₂ := ObsModelCore.pureStep_eq π₂ ss
  rw [eq₁] at h₁ ⊢; rw [eq₂] at h₂ ⊢
  change linConfigStepPMF G _ _ t = linConfigStepPMF G _ _ t
  exact linConfigStepPMF_mass_invariant G _ _ _ t h₁ h₂

omit [DecidableEq (Fin n)] [Fintype (Fin n)] [Fintype A] [Nonempty A] in
private theorem extractPlayerAction_congr [DecidableEq (Fin n)]
    (G : Protocol n S V A Sig)
    (k : Nat) (s : S) (sig : Fin n → Sig) (p : Fin n) (accActs : Fin n → Option A)
    (acts₁ acts₂ : (i : Fin n) →
      LinAct (RoundView G) A (linObserve G i (.playerTurn k s sig p accActs)))
    (hp : acts₁ p = acts₂ p) :
    extractPlayerAction G k s sig p accActs acts₁ =
    extractPlayerAction G k s sig p accActs acts₂ := by
  simp only [extractPlayerAction]
  split
  · simp [hp]
  · rfl

omit [DecidableEq (Fin n)] [Fintype (Fin n)] [Fintype A] [Nonempty A] in
private theorem linConfigStepPMF_playerTurn_congr [DecidableEq (Fin n)]
    (G : Protocol n S V A Sig)
    (k : Nat) (s : S) (sig : Fin n → Sig) (p : Fin n) (accActs : Fin n → Option A)
    (acts₁ acts₂ : (i : Fin n) →
      LinAct (RoundView G) A (linObserve G i (.playerTurn k s sig p accActs)))
    (hp : acts₁ p = acts₂ p) :
    linConfigStepPMF G (.playerTurn k s sig p accActs) acts₁ =
    linConfigStepPMF G (.playerTurn k s sig p accActs) acts₂ := by
  simp only [linConfigStepPMF]
  match G.rounds[k]? with
  | some r =>
    dsimp only
    congr 2
    exact extractPlayerAction_congr G k s sig p accActs acts₁ acts₂ hp
  | none => rfl

omit [DecidableEq (Fin n)] [Fintype (Fin n)] [Fintype A] [Nonempty A] in
private theorem linAct_eq_punit_of_ne [DecidableEq (Fin n)]
    {G : Protocol n S V A Sig}
    {k : Nat} {s : S} {sig : Fin n → Sig} {p : Fin n} {accActs : Fin n → Option A}
    {i : Fin n} (hi : i ≠ p)
    (a₁ a₂ : LinAct (RoundView G) A (linObserve G i (.playerTurn k s sig p accActs))) :
    a₁ = a₂ := by
  have hobs : linObserve G i (.playerTurn k s sig p accActs) = none := by
    simp [linObserve, hi]
  have hsub : Subsingleton
      (LinAct (RoundView G) A
        (linObserve G i (.playerTurn k s sig p accActs))) := by
    rw [hobs]; exact ⟨fun a b => PUnit.ext a b⟩
  exact hsub.elim a₁ a₂

/-- For identity info states (current = id), the cast in `pureStep_eq`
is trivial: evaluating a dependent function after transport equals
evaluating at the transported index. -/
private theorem cast_dep_apply {α : Type} {P : α → Type}
    (f : ∀ x, P x) {a b : α} (h : a = b) :
    h ▸ f a = f b := by cases h; rfl

omit [Nonempty A] in
/-- Closed form of pure one-step execution in the linearized compilation.
Eliminates all dependent-type casts from `pureStep_eq`. -/
theorem pureStep_compiledLin_eq (G : Protocol n S V A Sig)
    (π : (compiledLinObs G).PureProfile) (ss : List (LinConfig G)) :
    (compiledLinObs G).pureStep π ss =
      linConfigStepPMF G ((compiledLinObs G).lastState ss)
        (fun i => π i (linObserve G i ((compiledLinObs G).lastState ss))) := by
  rw [ObsModelCore.pureStep_eq]
  congr 1
  funext i
  exact cast_dep_apply (π i) ((compiledLinObs G).currentObs_projectStates i ss)

omit [Nonempty A] in
/-- Two profiles producing the same observation-dependent actions at a given
configuration have equal pure steps. Takes the last state as a parameter
to avoid matching issues with `lastState ss`. -/
private theorem pureStep_congr_compiledLin (G : Protocol n S V A Sig)
    (π₁ π₂ : (compiledLinObs G).PureProfile) (ss : List (LinConfig G))
    (cfg : LinConfig G) (hlast : (compiledLinObs G).lastState ss = cfg)
    (h : ∀ i, π₁ i (linObserve G i cfg) = π₂ i (linObserve G i cfg)) :
    (compiledLinObs G).pureStep π₁ ss = (compiledLinObs G).pureStep π₂ ss := by
  rw [pureStep_compiledLin_eq, pureStep_compiledLin_eq, hlast]
  exact congrArg (linConfigStepPMF G cfg) (funext h)

omit [Nonempty A] in
/-- The linearized model satisfies `StepSupportFactorization`.
At each step, at most one player has a nontrivial action (the acting player
at a `playerTurn` phase). Changing any other player's strategy does not
affect the step, so the per-player update condition holds trivially. -/
theorem stepSupportFactorization_compiledLin (G : Protocol n S V A Sig) :
    ObsModelCore.StepSupportFactorization (compiledLinObs G) := by
  intro ss t π₀ π h₀
  constructor
  · -- Forward: pureStep π reaches t → all single-player updates reach t
    intro hπ i
    cases hlast : (compiledLinObs G).lastState ss with
    | signal k s =>
        -- All observations are none at signal → all actions are PUnit → profiles agree
        suffices heq : (compiledLinObs G).pureStep (Function.update π₀ i (π i)) ss =
            (compiledLinObs G).pureStep π₀ ss from heq ▸ h₀
        exact pureStep_congr_compiledLin G _ _ ss _ hlast
          (fun j => PUnit.ext _ _)
    | terminal s =>
        suffices heq : (compiledLinObs G).pureStep (Function.update π₀ i (π i)) ss =
            (compiledLinObs G).pureStep π₀ ss from heq ▸ h₀
        exact pureStep_congr_compiledLin G _ _ ss _ hlast
          (fun j => PUnit.ext _ _)
    | applyTransition k s sig accActs =>
        suffices heq : (compiledLinObs G).pureStep (Function.update π₀ i (π i)) ss =
            (compiledLinObs G).pureStep π₀ ss from heq ▸ h₀
        exact pureStep_congr_compiledLin G _ _ ss _ hlast
          (fun j => PUnit.ext _ _)
    | playerTurn k s sig p accActs =>
        by_cases hip : i = p
        · -- i = p: update at acting player, step matches π's step
          subst hip
          suffices heq : (compiledLinObs G).pureStep (Function.update π₀ i (π i)) ss =
              (compiledLinObs G).pureStep π ss from heq ▸ hπ
          exact pureStep_congr_compiledLin G _ _ ss _ hlast (fun j => by
            by_cases hji : j = i
            · subst hji; exact congrFun (Function.update_self j (π j) π₀) _
            · exact linAct_eq_punit_of_ne (accActs := accActs) hji _ _)
        · -- i ≠ p: update at non-acting player, step matches π₀'s step
          suffices heq : (compiledLinObs G).pureStep (Function.update π₀ i (π i)) ss =
              (compiledLinObs G).pureStep π₀ ss from heq ▸ h₀
          exact pureStep_congr_compiledLin G _ _ ss _ hlast (fun j => by
            by_cases hji : j = i
            · subst hji; exact linAct_eq_punit_of_ne (accActs := accActs) hip _ _
            · simp only [Function.update, dif_neg hji])
  · -- Backward: all single-player updates reach t → pureStep π reaches t
    intro hall
    cases hlast : (compiledLinObs G).lastState ss with
    | signal k s =>
        suffices heq : (compiledLinObs G).pureStep π ss =
            (compiledLinObs G).pureStep π₀ ss from heq ▸ h₀
        exact pureStep_congr_compiledLin G _ _ ss _ hlast
          (fun j => PUnit.ext _ _)
    | terminal s =>
        suffices heq : (compiledLinObs G).pureStep π ss =
            (compiledLinObs G).pureStep π₀ ss from heq ▸ h₀
        exact pureStep_congr_compiledLin G _ _ ss _ hlast
          (fun j => PUnit.ext _ _)
    | applyTransition k s sig accActs =>
        suffices heq : (compiledLinObs G).pureStep π ss =
            (compiledLinObs G).pureStep π₀ ss from heq ▸ h₀
        exact pureStep_congr_compiledLin G _ _ ss _ hlast
          (fun j => PUnit.ext _ _)
    | playerTurn k s sig p accActs =>
        have hp := hall p
        suffices heq : (compiledLinObs G).pureStep π ss =
            (compiledLinObs G).pureStep (Function.update π₀ p (π p)) ss from heq ▸ hp
        exact pureStep_congr_compiledLin G _ _ ss _ hlast (fun j => by
          by_cases hjp : j = p
          · subst hjp; exact (congrFun (Function.update_self j (π j) π₀) _).symm
          · exact (linAct_eq_punit_of_ne (accActs := accActs) hjp _ _).symm)

-- ============================================================================
-- OLF (Obs-Local Feasibility) helpers
-- ============================================================================

omit [DecidableEq (Fin n)] [Fintype (Fin n)] [Fintype A] [Nonempty A] in
/-- Index into `l.concat a` at position `j < l.length` equals `l[j]`. -/
private theorem getElem_concat_left {α : Type*} (l : List α) (a : α)
    (j : Nat) (hj : j < l.length) {h : j < (l.concat a).length} :
    (l.concat a)[j] = l[j] := by
  simp [List.getElem_append_left hj]

omit [Nonempty A] in
open Math.ParameterizedChain in
/-- Under the linearized model, if `πᵢ` agrees with `(π i)` at every intermediate
observation along the trace, then `pureRun` under the player-i update equals the
original `pureRun`. -/
theorem pureRun_update_eq_of_obs_agree (G : Protocol n S V A Sig)
    (π : (compiledLinObs G).PureProfile) (i : Fin n)
    (πᵢ : (compiledLinObs G).LocalStrategy i)
    (k : Nat) (ss : List (LinConfig G))
    (hss : pureRun ((compiledLinObs G).pureStep) (compiledLinObs G).init k π ss ≠ 0)
    (h : ∀ j (hj : j + 1 < ss.length),
        πᵢ (linObserve G i ss[j]) = (π i) (linObserve G i ss[j])) :
    pureRun ((compiledLinObs G).pureStep) (compiledLinObs G).init k
      (Function.update π i πᵢ) ss =
    pureRun ((compiledLinObs G).pureStep) (compiledLinObs G).init k π ss := by
  induction k generalizing ss with
  | zero => rfl
  | succ m ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨pre, t, rfl⟩
    · exact absurd (pureRun_succ_nil _ _ m _) hss
    · -- Convert concat→append for pureRun only
      have hconcat : pre.concat t = pre ++ [t] := List.concat_eq_append
      rw [hconcat] at hss ⊢
      simp only [pureRun_succ_append] at hss ⊢
      have hpre : pureRun _ _ m π pre ≠ 0 := left_ne_zero_of_mul hss
      have hlen : pre.length = m + 1 := pureRun_length _ _ m _ pre hpre
      -- Helper: extract from h at index j < pre.length (converting concat indexing)
      have h' : ∀ j (hj : j < pre.length),
          πᵢ (linObserve G i pre[j]) = (π i) (linObserve G i pre[j]) := by
        intro j hj
        have hjlt : j + 1 < (pre.concat t).length := by simp; omega
        have hobs := h j hjlt
        rw [getElem_concat_left pre t j hj] at hobs
        exact hobs
      -- IH for prefix
      have hpre_eq : pureRun _ _ m (Function.update π i πᵢ) pre =
          pureRun _ _ m π pre := ih pre hpre (fun j hj => h' j (by omega))
      -- Step agreement at lastState pre
      have hstep_eq : (compiledLinObs G).pureStep (Function.update π i πᵢ) pre =
          (compiledLinObs G).pureStep π pre :=
        pureStep_congr_compiledLin G _ _ pre _ rfl (fun j => by
          by_cases hji : j = i
          · subst hji
            have hobs := h' (pre.length - 1) (by omega)
            have hlast : (compiledLinObs G).lastState pre = pre[pre.length - 1] := by
              simp [ObsModelCore.lastState, List.getLast?_eq_getElem?,
                List.getElem?_eq_getElem (by omega : pre.length - 1 < pre.length),
                Option.getD_some]
            rw [Function.update_self, hlast]
            exact hobs
          · simp [Function.update, dif_neg hji])
      rw [hpre_eq, hstep_eq]

omit [DecidableEq (Fin n)] [Fintype (Fin n)] [Fintype A] [Nonempty A] in
private theorem lastState_take_eq_getElem
    [DecidableEq (Fin n)] {G : Protocol n S V A Sig}
    (ss : List (LinConfig G)) (j : Nat) (hj : j + 1 < ss.length) :
    (compiledLinObs G).lastState (ss.take (j + 1)) = ss[j] := by
  simp [ObsModelCore.lastState, List.getLast?_eq_getElem?,
    List.length_take_of_le (by omega : j + 1 ≤ ss.length),
    show j + 1 - 1 = j from by omega, Option.getD_some]

open Math.ParameterizedChain in
omit [Nonempty A] in
/-- Converse: if `pureRun` is nonzero under both the original profile and a
player-i update, then `πᵢ` must agree with `(π i)` at all observations along
the trace. At non-i steps this is trivial (PUnit). At i-steps, the step is
deterministic and injective in the action, so both hitting the same target forces
the actions to agree. -/
theorem pureRun_update_nonzero_agree (G : Protocol n S V A Sig)
    (π : (compiledLinObs G).PureProfile) (i : Fin n)
    (πᵢ : (compiledLinObs G).LocalStrategy i)
    (k : Nat) (ss : List (LinConfig G))
    (hss : pureRun ((compiledLinObs G).pureStep) (compiledLinObs G).init k π ss ≠ 0)
    (hupd : pureRun ((compiledLinObs G).pureStep) (compiledLinObs G).init k
      (Function.update π i πᵢ) ss ≠ 0)
    (j : Nat) (hj : j + 1 < ss.length) :
    πᵢ (linObserve G i ss[j]) = (π i) (linObserve G i ss[j]) := by
  -- Extract per-step nonzero for both profiles
  have hstep_π := pureRun_step_nonzero _ _ k π ss hss j hj
  have hstep_upd := pureRun_step_nonzero _ _ k (Function.update π i πᵢ) ss hupd j hj
  -- Rewrite pureStep to linConfigStepPMF form
  rw [pureStep_compiledLin_eq] at hstep_π hstep_upd
  -- cfg = lastState(ss.take(j+1)) = ss[j]
  have hcfg_eq : (compiledLinObs G).lastState (ss.take (j + 1)) = ss[j] :=
    lastState_take_eq_getElem ss j hj
  -- Suffices to show the claim at cfg = ss[j]
  suffices ∀ (cfg : LinConfig G),
      (compiledLinObs G).lastState (ss.take (j + 1)) = cfg →
      (linConfigStepPMF G cfg
        (fun p => (Function.update π i πᵢ) p (linObserve G p cfg))) ss[j + 1] ≠ 0 →
      (linConfigStepPMF G cfg
        (fun p => π p (linObserve G p cfg))) ss[j + 1] ≠ 0 →
      πᵢ (linObserve G i cfg) = (π i) (linObserve G i cfg) by
    rw [← hcfg_eq]; exact this _ rfl (hcfg_eq ▸ hstep_upd) (hcfg_eq ▸ hstep_π)
  intro cfg _ h_upd h_orig
  match cfg with
  | .signal k' s =>
    have : linObserve G i (.signal k' s) = none := by simp [linObserve]
    rw [this]; exact PUnit.ext _ _
  | .terminal s =>
    have : linObserve G i (.terminal s) = none := by simp [linObserve]
    rw [this]; exact PUnit.ext _ _
  | .applyTransition k' s sig' aa =>
    have : linObserve G i (.applyTransition k' s sig' aa) = none := by simp [linObserve]
    rw [this]; exact PUnit.ext _ _
  | .playerTurn k' s sig p accActs =>
    by_cases hip : i = p
    · subst hip
      -- Active player = i: step is deterministic (PMF.pure via advancePlayerTurn).
      -- Both nonzero at same target → same accActs' → same extractPlayerAction → acts agree.
      by_cases hk : k' < G.rounds.length
      · -- Valid round: unfold linConfigStepPMF to advancePlayerTurn
        have hr : G.rounds[k']? = some G.rounds[k'] := List.getElem?_eq_getElem hk
        simp only [linConfigStepPMF, hr] at h_upd h_orig
        -- advancePlayerTurn nonzero at same target → updated accActs agree
        have haa := advancePlayerTurn_accActs_eq G k' s sig i _ _
          G.rounds[k'] ss[j + 1] h_upd h_orig
        -- Function.update accActs i epa₁ = Function.update accActs i epa₂ → epa₁ = epa₂
        have hepa := congrFun haa i
        simp only [Function.update_self] at hepa
        -- hepa : extractPlayerAction ... acts₁ = extractPlayerAction ... acts₂
        -- extractPlayerAction with hk is cast ... (acts i), cast injective via HEq
        unfold extractPlayerAction at hepa
        simp only [hk, dite_true, Function.update_self] at hepa
        -- hepa : cast ⋯ (πᵢ obs) = cast ⋯ ((π i) obs)
        exact eq_of_heq ((cast_heq _ _).symm.trans ((heq_of_eq hepa).trans (cast_heq _ _)))
      · -- Invalid round: obs = none, PUnit
        have : linObserve G i (.playerTurn k' s sig i accActs) = none := by
          simp [linObserve, hk]
        rw [this]; exact PUnit.ext _ _
    · -- Non-active player: observation is none, PUnit
      have : linObserve G i (.playerTurn k' s sig p accActs) = none :=
        linObserve_ne_acting hip
      rw [this]; exact PUnit.ext _ _

end Properties

-- ============================================================================
-- Profile lift / descend
-- ============================================================================

section Profiles

variable {G : Protocol n S V A Sig} [DecidableEq (Fin n)]

/-- Lift a protocol-level pure strategy to a compiled local strategy.
At `some (k, v)` (active), uses the strategy's action on `v`; at `none`
(inactive), uses the unique `PUnit` action. -/
def liftLocalStrategy (σ : PureStrategy V A) :
    (compiledLinObs G).LocalStrategy (i := i) :=
  fun obs =>
    match obs with
    | some (_, v) => (σ v : LinAct (RoundView G) A (some (_, v)))
    | none => (PUnit.unit : LinAct (RoundView G) A none)

/-- Lift a protocol-level pure profile to a compiled pure profile. -/
def liftPureProfile (σ : PureProfile n V A) :
    (compiledLinObs G).PureProfile :=
  fun i => liftLocalStrategy (i := i) (σ i)

/-- Descend a compiled local strategy to a protocol-level pure strategy.
Extracts the action at `some (k₀, v)` observations where `k₀` is a chosen
round index. Requires `G.rounds` to be nonempty. -/
noncomputable def descendLocalStrategy [Nonempty (Fin G.rounds.length)]
    (π : (compiledLinObs G).LocalStrategy (i := i)) :
    PureStrategy V A :=
  fun v => π (some (Classical.arbitrary _, v))

/-- Descend a compiled pure profile to a protocol-level pure profile. -/
noncomputable def descendPureProfile [Nonempty (Fin G.rounds.length)]
    (π : (compiledLinObs G).PureProfile) :
    PureProfile n V A :=
  fun i => descendLocalStrategy (π i)

/-- Lift then descend is the identity on pure strategies. -/
@[simp]
theorem descendLocalStrategy_liftLocalStrategy [Nonempty (Fin G.rounds.length)]
    (σ : PureStrategy V A) :
    descendLocalStrategy (G := G) (i := i) (liftLocalStrategy σ) = σ := by
  ext v; simp [descendLocalStrategy, liftLocalStrategy]

/-- Lift then descend is the identity on pure profiles. -/
@[simp]
theorem descendPureProfile_liftPureProfile [Nonempty (Fin G.rounds.length)]
    (σ : PureProfile n V A) :
    descendPureProfile (G := G) (liftPureProfile σ) = σ := by
  ext i v; simp [descendPureProfile, liftPureProfile, descendLocalStrategy, liftLocalStrategy]


-- ============================================================================
-- Behavioral profile bridges
-- ============================================================================

/-- Lift a native behavioral strategy to a compiled behavioral local strategy.
At `none` (inactive), returns `PMF.pure PUnit.unit`.
At `some (k, v)` (active), returns `σ v : PMF (Option A)`. -/
noncomputable def liftBehavioralStrategy [Fintype (Option A)]
    (σ : BehavioralStrategy V A) :
    (obs : Option (RoundView G)) → PMF (LinAct (RoundView G) A obs)
  | none => PMF.pure PUnit.unit
  | some (_, v) => σ v

/-- Lift a native behavioral profile to a compiled behavioral profile. -/
noncomputable def liftBehavioralProfile [Fintype (Option A)]
    (σ : BehavioralProfile n V A) :
    ObsModelCore.BehavioralProfile (compiledLinObs G) :=
  fun i => liftBehavioralStrategy (G := G) (σ i)

/-- Descend a compiled behavioral profile to a native behavioral profile.
Extracts the action distribution at `some (k₀, v)` observations. -/
noncomputable def descendBehavioralProfile [Nonempty (Fin G.rounds.length)]
    (β : ObsModelCore.BehavioralProfile (compiledLinObs G)) :
    BehavioralProfile n V A :=
  fun i v => β i (some (Classical.arbitrary _, v))

/-- Lift then descend is the identity on behavioral profiles. -/
@[simp]
theorem descendBehavioralProfile_liftBehavioralProfile
    [Fintype (Option A)] [Nonempty (Fin G.rounds.length)]
    (σ : BehavioralProfile n V A) :
    descendBehavioralProfile (G := G) (liftBehavioralProfile σ) = σ := by
  ext i v; simp [descendBehavioralProfile, liftBehavioralProfile, liftBehavioralStrategy]

open Classical in
/-- The unique round for a view under `ViewDeterminesRound`. -/
noncomputable def viewRound [Nonempty (Fin G.rounds.length)]
    (_hVRD : G.ViewDeterminesRound) (i : Fin n) (v : V) :
    Fin G.rounds.length :=
  if h : ∃ (k : Fin G.rounds.length) (s : S) (sig : Sig),
    G.rounds[k].view i s sig = v
  then h.choose
  else Classical.arbitrary _

omit [DecidableEq (Fin n)] in
theorem viewRound_eq [Nonempty (Fin G.rounds.length)] (hVRD : G.ViewDeterminesRound)
    (k : Fin G.rounds.length) (s : S) (sig_i : Sig) (i : Fin n)
    (hv : G.rounds[k].view i s sig_i = v) :
    viewRound hVRD i v = k := by
  classical
  unfold viewRound
  have hex : ∃ (k' : Fin G.rounds.length) (s' : S) (sig' : Sig),
    G.rounds[k'].view i s' sig' = v := ⟨k, s, sig_i, hv⟩
  rw [dif_pos hex]
  obtain ⟨s', sig', hv'⟩ := hex.choose_spec
  exact hVRD i _ _ _ _ _ _ (hv'.trans hv.symm)

/-- Smart descent using `viewRound` — uses the unique reachable round for each view
instead of `Classical.arbitrary`. -/
noncomputable def descendBehavioralProfileVRD [Nonempty (Fin G.rounds.length)]
    (hVRD : G.ViewDeterminesRound)
    (β : ObsModelCore.BehavioralProfile (compiledLinObs G)) :
    BehavioralProfile n V A :=
  fun i v => β i (some (viewRound hVRD i v, v))

/-- Lift then descend is the identity under `ViewDeterminesRound`. -/
@[simp]
theorem descendBehavioralProfileVRD_liftBehavioralProfile
    [Fintype (Option A)] [Nonempty (Fin G.rounds.length)]
    (hVRD : G.ViewDeterminesRound)
    (σ : BehavioralProfile n V A) :
    descendBehavioralProfileVRD hVRD (liftBehavioralProfile σ) = σ := by
  ext i v; simp [descendBehavioralProfileVRD, liftBehavioralProfile, liftBehavioralStrategy]

-- ============================================================================
-- Mixed profile lift
-- ============================================================================

/-- Lift native per-player mixed strategies to compiled local strategy distributions. -/
noncomputable def liftMixedProfile
    (μ : (i : Fin n) → PMF (PureStrategy V A)) :
    (i : Fin n) → PMF ((compiledLinObs G).LocalStrategy i) :=
  fun i => (μ i).map (liftLocalStrategy (G := G) (i := i))

/-- The joint product of lifted mixed profiles equals the pushforward of the native
joint product through `liftPureProfile`. -/
theorem liftMixedProfile_joint [DecidableEq V] [Fintype V] [Fintype A]
    [Fintype (Fin n)]
    [∀ i, Fintype ((compiledLinObs G).LocalStrategy i)]
    (μ : (i : Fin n) → PMF (PureStrategy V A)) :
    Math.PMFProduct.pmfPi (liftMixedProfile (G := G) μ) =
      Math.ProbabilityMassFunction.pushforward
        (Math.PMFProduct.pmfPi μ) (liftPureProfile (G := G)) := by
  exact (Math.PMFProduct.pmfPi_push_coordwise μ
    (fun (i : Fin n) => liftLocalStrategy (G := G) (i := i))).symm

end Profiles

-- ============================================================================
-- Adequacy: linearized execution matches protocol evaluation
-- ============================================================================

section Adequacy

variable {G : Protocol n S V A Sig} [DecidableEq (Fin n)] [Fintype (Fin n)]

-- [Fintype (Fin n)] is needed for runDistPure_eq_eval to unify with
-- downstream callers that have [Fintype (Fin n)] section variables.
-- Many intermediate lemmas don't use it directly.
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-- The final state of a `LinConfig`. For `terminal s`, this is `s`.
For non-terminal configurations, this is the current state carried
by the configuration (evaluation not yet complete). -/
def LinConfig.state : LinConfig G → S
  | .signal _ s => s
  | .playerTurn _ s _ _ _ => s
  | .applyTransition _ s _ _ => s
  | .terminal s => s

/-- Resolve players `pVal, pVal+1, ..., n-1` at round `k`, accumulating actions,
then transition and continue from round `k+1`.

This is the "semantic backbone" for adequacy: it evaluates the protocol by
resolving one player at a time, matching the linearized model's step structure. -/
noncomputable def evalLinearized (G : Protocol n S V A Sig)
    (σ : PureProfile n V A)
    (rounds : List (Round n S V A Sig))
    (s : S) : PMF S :=
  match rounds with
  | [] => PMF.pure s
  | r :: rest =>
    (r.signal s).bind fun sig =>
      let acts : Fin n → Option A := fun i => σ i (r.view i s (sig i))
      let next := r.transition s acts
      evalLinearized G σ rest next

omit [DecidableEq (Fin n)] in
private theorem pmf_foldl_bind
    (f : Round n S V A Sig → PureProfile n V A → S → PMF S)
    (σ : PureProfile n V A) (μ : PMF S) (rest : List (Round n S V A Sig)) :
    rest.foldl (fun dist r => dist.bind (f r σ)) μ =
      μ.bind (fun s => rest.foldl (fun dist r => dist.bind (f r σ)) (PMF.pure s)) := by
  induction rest generalizing μ with
  | nil => simp
  | cons r' rest' ih =>
    simp only [List.foldl_cons]
    rw [ih, PMF.bind_bind]
    congr 1
    ext s
    rw [PMF.pure_bind, ih]

omit [DecidableEq (Fin n)] in
private theorem evalRounds_cons (r : Round n S V A Sig)
    (rest : List (Round n S V A Sig)) (σ : PureProfile n V A) (s : S) :
    evalRounds (r :: rest) σ s = (r.eval σ s).bind (evalRounds rest σ) := by
  simp only [evalRounds, List.foldl_cons]
  rw [PMF.pure_bind]
  exact pmf_foldl_bind Round.eval σ (r.eval σ s) rest

omit [DecidableEq (Fin n)] in
set_option linter.unusedFintypeInType false in
private theorem pmf_foldl_bind_mixed [Fintype (Option A)]
    (f : Round n S V A Sig → BehavioralProfile n V A → S → PMF S)
    (σ : BehavioralProfile n V A) (μ : PMF S) (rest : List (Round n S V A Sig)) :
    rest.foldl (fun dist r => dist.bind (f r σ)) μ =
      μ.bind (fun s => rest.foldl (fun dist r => dist.bind (f r σ)) (PMF.pure s)) := by
  induction rest generalizing μ with
  | nil => simp
  | cons r' rest' ih =>
    simp only [List.foldl_cons]
    rw [ih, PMF.bind_bind]
    congr 1
    ext s
    rw [PMF.pure_bind, ih]

omit [DecidableEq (Fin n)] in
set_option linter.unusedFintypeInType false in
private theorem evalRoundsMixed_cons [Fintype (Option A)] (r : Round n S V A Sig)
    (rest : List (Round n S V A Sig)) (σ : BehavioralProfile n V A) (s : S) :
    evalRoundsMixed (r :: rest) σ s = (r.evalMixed σ s).bind (evalRoundsMixed rest σ) := by
  simp only [evalRoundsMixed, List.foldl_cons]
  rw [PMF.pure_bind]
  exact pmf_foldl_bind_mixed Round.evalMixed σ (r.evalMixed σ s) rest

omit [DecidableEq (Fin n)] in
private theorem evalLinearized_eq_evalRounds (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) (rounds : List (Round n S V A Sig)) (s : S) :
    evalLinearized G σ rounds s = evalRounds rounds σ s := by
  induction rounds generalizing s with
  | nil => simp [evalLinearized, evalRounds]
  | cons r rest ih =>
    rw [evalRounds_cons]
    simp only [evalLinearized, Round.eval, PMF.map]
    conv_rhs => rw [PMF.bind_bind]
    congr 1
    ext sig
    simp only [Function.comp, PMF.pure_bind]
    exact congrFun (congrArg DFunLike.coe (ih _)) _

omit [DecidableEq (Fin n)] in
theorem evalLinearized_eq_eval (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) :
    evalLinearized G σ G.rounds G.init = G.eval σ :=
  evalLinearized_eq_evalRounds G σ G.rounds G.init

/-- Resolve players `pVal, pVal+1, ..., n-1` with pure strategies, accumulating
their actions. Returns the fully populated action vector. -/
def resolveActions (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) (r : Round n S V A Sig)
    (s : S) (sig : Fin n → Sig) (pVal : Nat) (accActs : Fin n → Option A) :
    Fin n → Option A :=
  if hp : pVal < n then
    let p : Fin n := ⟨pVal, hp⟩
    resolveActions G σ r s sig (pVal + 1)
      (Function.update accActs p (σ p (r.view p s (sig p))))
  else
    accActs
  termination_by (n - pVal)

/-- After resolving players from `pVal` onward, the accumulated actions for
players `< pVal` are unchanged and players `≥ pVal` get their strategy values. -/
private theorem resolveActions_spec (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) (r : Round n S V A Sig)
    (s : S) (sig : Fin n → Sig) (pVal : Nat) (accActs : Fin n → Option A)
    (h_below : ∀ i : Fin n, i.val < pVal → accActs i = σ i (r.view i s (sig i))) :
    resolveActions G σ r s sig pVal accActs =
      fun i => σ i (r.view i s (sig i)) := by
  unfold resolveActions
  split
  case isTrue hp =>
    apply resolveActions_spec
    intro i hi
    by_cases hpi : i = ⟨pVal, hp⟩
    · subst hpi; simp [Function.update_self]
    · rw [Function.update_of_ne hpi]
      exact h_below i (Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) (by
        intro heq; exact hpi (Fin.ext heq)))
  case isFalse hp =>
    funext i
    exact h_below i (by omega)
  termination_by (n - pVal)

/-- After resolving all players from 0, the accumulated actions equal the
simultaneous action vector. -/
theorem resolveActions_eq (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) (r : Round n S V A Sig)
    (s : S) (sig : Fin n → Sig) :
    resolveActions G σ r s sig 0 (fun _ => none) =
      fun i => σ i (r.view i s (sig i)) :=
  resolveActions_spec G σ r s sig 0 _ (fun i hi => absurd hi (by omega))

/-- Evaluate from a `LinConfig` using a pure profile. Non-recursive: dispatches
to `evalLinearized` on the remaining rounds.

- **Signal k s**: evaluate rounds from k onward
- **PlayerTurn k s sig p accActs**: resolve remaining players, then evaluate from k+1
- **Terminal s**: point mass on s -/
noncomputable def evalFromCfg (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) : LinConfig G → PMF S
  | .terminal s => PMF.pure s
  | .signal k s => evalLinearized G σ (G.rounds.drop k) s
  | .playerTurn k s sig p accActs =>
    match G.rounds[k]? with
    | some r =>
      let fullActs := resolveActions G σ r s sig p.val accActs
      let next := r.transition s fullActs
      evalLinearized G σ (G.rounds.drop (k + 1)) next
    | none => PMF.pure s
  | .applyTransition k s _sig accActs =>
    match G.rounds[k]? with
    | some r =>
      let next := r.transition s accActs
      evalLinearized G σ (G.rounds.drop (k + 1)) next
    | none => PMF.pure s

/-- `evalFromCfg` at the initial configuration equals `Protocol.eval`. -/
theorem evalFromCfg_init (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) :
    evalFromCfg G σ (linInitialConfig G) = G.eval σ := by
  simp only [linInitialConfig]
  split <;> simp only [evalFromCfg]
  · -- G.rounds[0]? = none → rounds is empty → terminal case
    rename_i h
    have hnil : G.rounds = [] := by
      match hr : G.rounds with
      | [] => rfl
      | _ :: _ => simp [hr] at h
    simp [Protocol.eval, evalRounds, hnil]
  · -- G.rounds[0]? ≠ none → signal case
    rw [List.drop_zero]
    exact evalLinearized_eq_eval G σ

/-- `extractPlayerAction` with `liftPureProfile` gives the protocol-level action. -/
private theorem extractPlayerAction_lift (σ : PureProfile n V A)
    (k : Nat) (s : S) (sig : Fin n → Sig) (p : Fin n)
    (accActs : Fin n → Option A) (r : Round n S V A Sig)
    (hr : G.rounds[k]? = some r) :
    extractPlayerAction G k s sig p accActs
      (fun i => (liftPureProfile (G := G) σ) i
        (linObserve G i (.playerTurn k s sig p accActs))) =
    σ p (r.view p s (sig p)) := by
  unfold extractPlayerAction
  have hk : k < G.rounds.length := by
    by_contra h; push_neg at h; simp [List.getElem?_eq_none (by omega)] at hr
  split
  case isTrue hk' =>
    have hobs : linObserve G p (.playerTurn k s sig p accActs) =
        some (⟨k, hk'⟩, G.rounds[k].view p s (sig p)) := by simp [linObserve, hk']
    have hr' : G.rounds[k] = r := by
      have := List.getElem?_eq_getElem hk' ▸ hr; exact Option.some.inj this
    change cast _ _ = _
    rw [cast_eq_iff_heq]
    simp only [liftPureProfile, liftLocalStrategy]
    rw [hobs, hr']
  case isFalse hk' =>
    exact absurd hk hk'

/-- One step of the linearized model composed with `evalFromCfg` telescopes:
performing one step and then evaluating from the resulting configuration gives
the same result as evaluating from the current configuration. -/
private theorem stepPMF_bind_evalFromCfg
    (σ : PureProfile n V A) (cfg : LinConfig G) :
    (linConfigStepPMF G cfg
      (fun i => (liftPureProfile (G := G) σ) i (linObserve G i cfg))).bind
        (evalFromCfg G σ) =
    evalFromCfg G σ cfg := by
  cases cfg with
  | terminal s =>
    -- Step at terminal is PMF.pure (.terminal s), identity
    simp [linConfigStepPMF, evalFromCfg, PMF.pure_bind]
  | signal k s =>
    -- Step samples signal and creates playerTurn (or transitions if n=0)
    simp only [linConfigStepPMF]
    split
    case h_1 r hr =>
      split
      case isTrue hn =>
        -- n > 0: signal → playerTurn 0
        -- LHS: (r.signal s).map (fun sig => .playerTurn k s sig ⟨0, hn⟩ (fun _ => none))
        --        .bind (evalFromCfg G σ)
        -- = (r.signal s).bind (fun sig => evalFromCfg G σ (.playerTurn ...))
        rw [PMF.bind_map]
        -- Unfold evalFromCfg at the playerTurn
        simp only [Function.comp_def, evalFromCfg, hr]
        -- RHS: evalLinearized G σ (G.rounds.drop k) s
        -- Since G.rounds[k]? = some r, drop k = r :: drop (k+1)
        have hk : k < G.rounds.length := by
          by_contra h; push_neg at h
          simp [List.getElem?_eq_none (by omega)] at hr
        have hdrop : G.rounds.drop k = r :: G.rounds.drop (k + 1) := by
          rw [← List.cons_getElem_drop_succ (h := hk)]
          congr 1; exact (List.getElem_of_getElem? hr).choose_spec
        rw [hdrop, evalLinearized]
        congr 1; ext sig; simp only []
        rw [resolveActions_eq]
      case isFalse hn =>
        have h0 : n = 0 := by omega
        subst h0
        have hempty : ∀ (f g : Fin 0 → Option A), f = g :=
          fun f g => funext fun i => absurd i.pos hn
        have hk : k < G.rounds.length := by
          by_contra h; push_neg at h; simp [List.getElem?_eq_none (by omega)] at hr
        have hdrop : G.rounds.drop k = r :: G.rounds.drop (k + 1) := by
          rw [← List.cons_getElem_drop_succ (h := hk)]
          congr 1; exact (List.getElem_of_getElem? hr).choose_spec
        -- LHS: (r.signal s).map (.applyTransition k s · (fun _ => none)).bind (evalFromCfg G σ)
        rw [PMF.bind_map]
        -- Unfold evalFromCfg at .applyTransition
        simp only [Function.comp_def, evalFromCfg, hr]
        -- RHS: evalLinearized G σ (G.rounds.drop k) s
        rw [hdrop, evalLinearized]
        -- Both sides: (r.signal s).bind (fun sig => ...)
        congr 1; funext sig
        -- Equate the transition arguments using hempty
        exact congrArg (evalLinearized G σ (G.rounds.drop (k + 1)))
          (congrArg (r.transition s) (hempty _ _))
    case h_2 hr =>
      -- G.rounds[k]? = none: step is identity
      simp [PMF.pure_bind]
  | playerTurn k s sig p accActs =>
    -- Step resolves player p; evalFromCfg resolves p onward
    simp only [linConfigStepPMF]
    split
    case h_1 r hr =>
      simp only [advancePlayerTurn]
      rw [extractPlayerAction_lift σ k s sig p accActs r hr]
      split
      case isTrue hp1 =>
        -- p.val + 1 < n: advance to next player
        simp only [PMF.pure_bind, evalFromCfg, hr]
        congr 1
        -- resolveActions from p with updated accActs = resolveActions from p with original
        conv_rhs => rw [show p.val = p.val from rfl]; unfold resolveActions; rw [dif_pos p.isLt]
      case isFalse hp1 =>
        -- p is last player: advance → applyTransition
        have hresolve : resolveActions G σ r s sig p.val accActs =
            Function.update accActs p (σ p (r.view p s (sig p))) := by
          unfold resolveActions; rw [dif_pos p.isLt]
          have : ⟨p.val, p.isLt⟩ = p := Fin.ext rfl
          rw [this]; unfold resolveActions; rw [dif_neg hp1]
        -- LHS: PMF.pure (.applyTransition k s sig updatedActs).bind (evalFromCfg G σ)
        simp only [PMF.pure_bind, evalFromCfg, hr, hresolve]
    case h_2 hr =>
      simp [PMF.pure_bind, evalFromCfg, hr]
  | applyTransition k s sig accActs =>
    -- Step applies transition; evalFromCfg does the same thing
    simp only [linConfigStepPMF]
    split
    case h_1 r hr =>
      -- G.rounds[k]? = some r: transition fires
      split
      case h_1 _ hr2 =>
        -- G.rounds[k+1]? = some _: next round exists → signal (k+1)
        simp only [PMF.pure_bind]
        show evalFromCfg G σ (.signal (k + 1) (r.transition s accActs)) =
          evalFromCfg G σ (.applyTransition k s sig accActs)
        simp only [evalFromCfg, hr]
      case h_2 _ hr2 =>
        -- G.rounds[k+1]? = none: terminal
        simp only [PMF.pure_bind]
        show evalFromCfg G σ (.terminal (r.transition s accActs)) =
          evalFromCfg G σ (.applyTransition k s sig accActs)
        simp only [evalFromCfg, hr]
        have hdrop2 : G.rounds.drop (k + 1) = [] :=
          List.drop_eq_nil_of_le (by
            by_contra h; push_neg at h
            rw [List.getElem?_eq_getElem h] at hr2; exact absurd hr2 (by simp))
        rw [hdrop2, evalLinearized]
    case h_2 hr =>
      simp [PMF.pure_bind, evalFromCfg, hr]

/-- **Telescoping**: running the linearized model for `k` steps and composing
with `evalFromCfg` on the last state equals `evalFromCfg` at the initial config,
which is `Protocol.eval`.

Proof idea: by induction on `k`, using `stepPMF_bind_evalFromCfg` at each step
to show that one step composed with `evalFromCfg` telescopes back to `evalFromCfg`
on the previous last state. The base case is `evalFromCfg_init`. -/
private theorem lastState_snoc (ss : List (LinConfig G)) (t : LinConfig G) :
    (compiledLinObs G).lastState (ss ++ [t]) = t := by
  simp [ObsModelCore.lastState, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil t [])]

theorem runDistPure_bind_evalFromCfg [Fintype A]
    (σ : PureProfile n V A) (k : Nat) :
    ((compiledLinObs G).runDistPure k (liftPureProfile σ)).bind
        (fun ss => evalFromCfg G σ ((compiledLinObs G).lastState ss)) =
      G.eval σ := by
  induction k with
  | zero =>
    change (PMF.pure [(compiledLinObs G).init]).bind _ = _
    simp only [PMF.pure_bind, ObsModelCore.lastState, List.getLast?_singleton, Option.getD_some]
    exact evalFromCfg_init G σ
  | succ k ih =>
    change ((ObsModelCore.runDistPure (compiledLinObs G) k (liftPureProfile σ)).bind
      (fun ss => Math.ProbabilityMassFunction.pushforward
        ((compiledLinObs G).pureStep (liftPureProfile σ) ss)
        (fun t => ss ++ [t]))).bind
      (fun ss => evalFromCfg G σ ((compiledLinObs G).lastState ss)) = _
    simp only [PMF.bind_bind, Math.ProbabilityMassFunction.pushforward, PMF.pure_bind,
      lastState_snoc]
    simp_rw [pureStep_compiledLin_eq, stepPMF_bind_evalFromCfg]
    exact ih

/-- A `LinConfig` is "done" when `evalFromCfg` reduces to `PMF.pure ∘ state`:
terminal configs, and non-terminal configs past all rounds. -/
def LinConfig.isDone (G : Protocol n S V A Sig) : LinConfig G → Prop
  | .terminal _ => True
  | .signal k _ => G.rounds[k]? = none
  | .playerTurn k _ _ _ _ => G.rounds[k]? = none
  | .applyTransition k _ _ _ => G.rounds[k]? = none

/-- Combined round+player phase measure. Increases by ≥1 at each non-done step.
Terminal configs get maximum phase so that monotonicity holds universally. -/
def LinConfig.phase (G : Protocol n S V A Sig) : LinConfig G → Nat
  | .signal k _ => k * (n + 2)
  | .playerTurn k _ _ p _ => k * (n + 2) + p.val + 1
  | .applyTransition k _ _ _ => k * (n + 2) + n + 1
  | .terminal _ => G.rounds.length * (n + 2)

private theorem evalFromCfg_of_isDone (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) (cfg : LinConfig G)
    (hd : cfg.isDone G) :
    evalFromCfg G σ cfg = PMF.pure cfg.state := by
  cases cfg with
  | terminal s => rfl
  | signal k s =>
    change evalLinearized G σ (G.rounds.drop k) s = PMF.pure s
    have hdr : G.rounds.drop k = [] := by
      apply List.drop_eq_nil_of_le
      by_contra h; push_neg at h
      have : G.rounds[k]? = some G.rounds[k] := List.getElem?_eq_getElem h
      simp [LinConfig.isDone, this] at hd
    rw [hdr, evalLinearized]
  | playerTurn k s sig p accActs =>
    change (match G.rounds[k]? with | some r => _ | none => PMF.pure s) = PMF.pure s
    have hd' : G.rounds[k]? = none := hd
    rw [hd']
  | applyTransition k s sig accActs =>
    change (match G.rounds[k]? with | some r => _ | none => PMF.pure s) = PMF.pure s
    have hd' : G.rounds[k]? = none := hd
    rw [hd']

omit [DecidableEq (Fin n)] in
private theorem isDone_of_phase_ge (G : Protocol n S V A Sig)
    (cfg : LinConfig G) (h : cfg.phase G ≥ G.rounds.length * (n + 2)) :
    cfg.isDone G := by
  cases cfg with
  | terminal _ => trivial
  | signal k s =>
    simp only [LinConfig.phase] at h
    have hk : k ≥ G.rounds.length := Nat.le_of_mul_le_mul_right h (by omega)
    simp only [LinConfig.isDone]
    exact List.getElem?_eq_none (by omega)
  | playerTurn k s sig p accActs =>
    simp only [LinConfig.phase] at h
    have hk : k ≥ G.rounds.length := by
      by_contra hlt; push_neg at hlt
      have : k * (n + 2) + p.val + 1 ≤ k * (n + 2) + n + 1 := by omega
      have : k * (n + 2) + n + 1 < G.rounds.length * (n + 2) := by nlinarith
      omega
    simp only [LinConfig.isDone]
    exact List.getElem?_eq_none (by omega)
  | applyTransition k s sig accActs =>
    simp only [LinConfig.phase] at h
    have hk : k ≥ G.rounds.length := by
      by_contra hlt; push_neg at hlt
      have : k * (n + 2) + n + 1 < G.rounds.length * (n + 2) := by nlinarith
      omega
    simp only [LinConfig.isDone]
    exact List.getElem?_eq_none (by omega)

omit [DecidableEq (Fin n)] in
private theorem phase_init_le (G : Protocol n S V A Sig) :
    (linInitialConfig G).phase G ≤ G.rounds.length * (n + 2) := by
  simp only [linInitialConfig]
  split <;> simp [LinConfig.phase]

/-- At done configs, any successor is also done and has the same state. -/
private theorem isDone_step_of_isDone (G : Protocol n S V A Sig)
    (cfg : LinConfig G)
    (acts : (i : Fin n) → LinAct (RoundView G) A (linObserve G i cfg))
    (hd : cfg.isDone G) (t : LinConfig G)
    (ht : t ∈ (linConfigStepPMF G cfg acts).support) :
    t.isDone G ∧ t.state = cfg.state := by
  rw [PMF.mem_support_iff] at ht
  cases cfg with
  | terminal s =>
    have ht' := (pure_ne_zero_iff' _ t).mp (by rwa [linConfigStepPMF] at ht)
    subst ht'; exact ⟨trivial, rfl⟩
  | signal k s =>
    simp only [linConfigStepPMF] at ht; split at ht
    · rename_i r hr; exact absurd hr (by change G.rounds[k]? = none at hd; simp [hd])
    · rw [pure_ne_zero_iff'] at ht; subst ht; exact ⟨hd, rfl⟩
  | playerTurn k s sig p accActs =>
    simp only [linConfigStepPMF] at ht; split at ht
    · rename_i r hr; exact absurd hr (by change G.rounds[k]? = none at hd; simp [hd])
    · rw [pure_ne_zero_iff'] at ht; subst ht; exact ⟨hd, rfl⟩
  | applyTransition k s sig accActs =>
    simp only [linConfigStepPMF] at ht; split at ht
    · rename_i r hr; exact absurd hr (by change G.rounds[k]? = none at hd; simp [hd])
    · rw [pure_ne_zero_iff'] at ht; subst ht; exact ⟨trivial, rfl⟩

/-- At non-done configs, every successor has phase exactly `cfg.phase + 1`. -/
private theorem phase_step_progress (G : Protocol n S V A Sig)
    (cfg : LinConfig G)
    (acts : (i : Fin n) → LinAct (RoundView G) A (linObserve G i cfg))
    (hnd : ¬ cfg.isDone G) (t : LinConfig G)
    (ht : t ∈ (linConfigStepPMF G cfg acts).support) :
    t.phase G = cfg.phase G + 1 := by
  rw [PMF.mem_support_iff] at ht
  cases cfg with
  | terminal s => exact absurd trivial hnd
  | signal k s =>
    simp only [linConfigStepPMF] at ht
    -- Split on match G.rounds[k]?
    split at ht
    · -- some r branch: split on if 0 < n
      rename_i r hr
      have hk : k < G.rounds.length := by
        by_contra h; push_neg at h; simp [List.getElem?_eq_none (by omega)] at hr
      split at ht
      · -- 0 < n: (r.signal s).map (fun sig => .playerTurn k s sig ⟨0, _⟩ _)
        rename_i hn
        obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ t).mp
          ((PMF.mem_support_iff _ t).mpr ht)
        simp [LinConfig.phase]
      · -- ¬(0 < n): map to .applyTransition
        rename_i hn
        have h0 : n = 0 := by omega
        obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ t).mp
          ((PMF.mem_support_iff _ t).mpr ht)
        simp only [LinConfig.phase]; subst h0; omega
    · -- none branch: contradicts ¬isDone
      exact absurd (by assumption : G.rounds[k]? = none) hnd
  | playerTurn k s sig p accActs =>
    simp only [linConfigStepPMF] at ht
    split at ht
    · -- some r branch
      rename_i r hr
      have hk : k < G.rounds.length := by
        by_contra h; push_neg at h; simp [List.getElem?_eq_none (by omega)] at hr
      simp only [advancePlayerTurn] at ht
      have hpn : p.val < n := p.isLt
      split at ht
      · rename_i hp1
        obtain rfl := (pure_ne_zero_iff' _ t).mp ht
        simp only [LinConfig.phase]; omega
      · rename_i hp1
        obtain rfl := (pure_ne_zero_iff' _ t).mp ht
        simp only [LinConfig.phase]
        nlinarith [show p.val + 1 = n by omega]
    · -- none branch: contradicts ¬isDone
      exact absurd (by assumption : G.rounds[k]? = none) hnd
  | applyTransition k s sig accActs =>
    simp only [linConfigStepPMF] at ht
    split at ht
    · -- some r branch: transition fires
      rename_i r hr
      have hk : k < G.rounds.length := by
        by_contra h; push_neg at h; simp [List.getElem?_eq_none (by omega)] at hr
      split at ht
      · -- G.rounds[k+1]? = some _: signal (k+1)
        obtain rfl := (pure_ne_zero_iff' _ t).mp ht
        simp only [LinConfig.phase]; nlinarith
      · -- G.rounds[k+1]? = none: terminal
        rename_i hknone
        have hklen : G.rounds.length = k + 1 := by
          have hge : G.rounds.length ≤ k + 1 := by
            simp only [List.getElem?_eq_none_iff] at hknone; exact hknone
          omega
        obtain rfl := (pure_ne_zero_iff' _ t).mp ht
        simp only [LinConfig.phase]; nlinarith
    · -- none branch: contradicts ¬isDone
      exact absurd (by assumption : G.rounds[k]? = none) hnd

private theorem PMF.bind_congr_support {α β : Type*} (p : PMF α) (f g : α → PMF β)
    (h : ∀ x ∈ p.support, f x = g x) : p.bind f = p.bind g := by
  ext b; simp only [PMF.bind_apply]
  congr 1; ext a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [PMF.mem_support_iff, not_not] at ha; simp [ha]

/-- After `k ≥ rounds.length * (n+1)` steps, all reachable last states are done. -/
private theorem isDone_of_reachable [Fintype A]
    (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) (k : Nat) (ss : List (LinConfig G))
    (hss : ss ∈ ((compiledLinObs G).runDistPure k (liftPureProfile σ)).support) :
    ((compiledLinObs G).lastState ss).isDone G ∨
    ((compiledLinObs G).lastState ss).phase G ≥ k := by
  rw [PMF.mem_support_iff] at hss
  induction k generalizing ss with
  | zero => right; omega
  | succ k ih =>
    -- Unfold runDistPure (k+1) using support membership
    change _ at hss
    rw [show (compiledLinObs G).runDistPure (k + 1) (liftPureProfile σ) =
      ((compiledLinObs G).runDistPure k (liftPureProfile σ)).bind
        (fun ss' => Math.ProbabilityMassFunction.pushforward
          ((compiledLinObs G).pureStep (liftPureProfile σ) ss')
          (fun t => ss' ++ [t])) from rfl] at hss
    have hsupp := (PMF.mem_support_iff _ _).mpr hss
    rw [PMF.mem_support_bind_iff] at hsupp
    obtain ⟨ss', hss'_supp, ht_supp⟩ := hsupp
    -- pushforward: ss = ss' ++ [t] for some t in pureStep support
    rw [show Math.ProbabilityMassFunction.pushforward
        ((compiledLinObs G).pureStep (liftPureProfile σ) ss')
        (fun t => ss' ++ [t]) =
      ((compiledLinObs G).pureStep (liftPureProfile σ) ss').map
        (fun t => ss' ++ [t]) from rfl] at ht_supp
    rw [PMF.mem_support_map_iff] at ht_supp
    obtain ⟨t, ht_in_step, rfl⟩ := ht_supp
    rw [lastState_snoc]
    -- IH on ss'
    have ih_ss' := ih ss' ((PMF.mem_support_iff _ _).mp hss'_supp)
    -- t is in support of pureStep at ss'
    rw [pureStep_compiledLin_eq] at ht_in_step
    set cfg := (compiledLinObs G).lastState ss' with cfg_def
    set acts := (fun i => (liftPureProfile (G := G) σ) i (linObserve G i cfg))
    -- Case split on whether cfg is done
    by_cases hd : cfg.isDone G
    · -- cfg is done: successor is also done
      left
      exact (isDone_step_of_isDone G cfg acts hd t ht_in_step).1
    · -- Not done: phase increases
      right
      have hprog := phase_step_progress G cfg acts hd t ht_in_step
      rcases ih_ss' with hd' | hph
      · exact absurd hd' hd
      · omega

/-- **Adequacy (pure profiles)**: running the linearized compiled model with
`liftPureProfile σ` for enough steps, and extracting the terminal state, gives
the same distribution as `Protocol.eval G σ`. -/
theorem runDistPure_eq_eval (G : Protocol n S V A Sig) [Fintype A]
    (σ : PureProfile n V A) (k : Nat) (hk : k ≥ G.rounds.length * (n + 2)) :
    ((compiledLinObs G).runDistPure k (liftPureProfile σ)).bind
        (fun ss => PMF.pure ((compiledLinObs G).lastState ss).state) =
      G.eval σ := by
  have htele := runDistPure_bind_evalFromCfg (G := G) σ k
  rw [← htele]
  exact PMF.bind_congr_support _ _ _ fun ss hss => by
    have hdr := isDone_of_reachable G σ k ss hss
    rcases hdr with hd | hph
    · exact (evalFromCfg_of_isDone G σ _ hd).symm
    · exact (evalFromCfg_of_isDone G σ _ (isDone_of_phase_ge G _ (by omega))).symm

end Adequacy

-- ============================================================================
-- Behavioral adequacy: linearized execution matches Protocol.evalMixed
-- ============================================================================

section BehavioralAdequacy

variable {G : Protocol n S V A Sig} [DecidableEq (Fin n)] [Fintype (Option A)]

/-- Resolve players `pVal, pVal+1, ..., n-1` by sampling from behavioral
strategies, accumulating actions into `accActs`. -/
noncomputable def resolveActionsMixed
    (σ : BehavioralProfile n V A) (r : Round n S V A Sig)
    (s : S) (sig : Fin n → Sig) (pVal : Nat) (accActs : Fin n → Option A) :
    PMF (Fin n → Option A) :=
  if hp : pVal < n then
    let p : Fin n := ⟨pVal, hp⟩
    (σ p (r.view p s (sig p))).bind fun a =>
      resolveActionsMixed σ r s sig (pVal + 1) (Function.update accActs p a)
  else
    PMF.pure accActs
  termination_by (n - pVal)

private theorem resolveActionsMixed_gen [Fintype (Fin n)]
    (σ : BehavioralProfile n V A) (r : Round n S V A Sig)
    (s : S) (sig : Fin n → Sig) (pVal : Nat) (accActs : Fin n → Option A) :
    resolveActionsMixed σ r s sig pVal accActs =
      Math.PMFProduct.pmfPi (fun i : Fin n =>
        if i.val < pVal then PMF.pure (accActs i)
        else σ i (r.view i s (sig i))) := by
  suffices h : ∀ m, m = n - pVal → resolveActionsMixed σ r s sig pVal accActs =
      Math.PMFProduct.pmfPi (fun i : Fin n =>
        if i.val < pVal then PMF.pure (accActs i)
        else σ i (r.view i s (sig i))) from h _ rfl
  intro m
  induction m generalizing pVal accActs with
  | zero =>
    intro hm
    have hp : ¬ pVal < n := by omega
    rw [resolveActionsMixed, dif_neg hp]
    have : ∀ (i : Fin n), i.val < pVal := fun i => by omega
    simp only [this, ite_true]
    exact (Math.PMFProduct.pmfPi_pure accActs).symm
  | succ m ih =>
    intro hm
    have hp : pVal < n := by omega
    rw [resolveActionsMixed, dif_pos hp]
    let q : Fin n := ⟨pVal, hp⟩
    -- Apply IH to each branch of the bind
    change (σ q (r.view q s (sig q))).bind (fun a =>
      resolveActionsMixed σ r s sig (pVal + 1) (Function.update accActs q a)) = _
    have hbind : ∀ a, resolveActionsMixed σ r s sig (pVal + 1) (Function.update accActs q a) =
        Math.PMFProduct.pmfPi (fun i : Fin n =>
          if i.val < pVal + 1 then PMF.pure (Function.update accActs q a i)
          else σ i (r.view i s (sig i))) := fun a => ih (pVal + 1) _ (by omega)
    simp_rw [hbind]
    -- Define the family for the RHS
    let σ' := fun i : Fin n => if i.val < pVal then PMF.pure (accActs i)
        else σ i (r.view i s (sig i))
    -- Show the families agree
    suffices hfam : ∀ a,
        Math.PMFProduct.pmfPi (fun i : Fin n =>
          if i.val < pVal + 1 then PMF.pure (Function.update accActs q a i)
          else σ i (r.view i s (sig i))) =
        Math.PMFProduct.pmfPi (Function.update σ' q (PMF.pure a)) by
      simp_rw [hfam]
      have hσ'q : σ' q = σ q (r.view q s (sig q)) := by
        change (if pVal < pVal then _ else _) = _
        simp
      rw [show Math.PMFProduct.pmfPi σ' =
          Math.PMFProduct.pmfPi (Function.update σ' q (σ q (r.view q s (sig q)))) from by
        rw [Function.update_eq_self_iff.mpr hσ'q.symm]]
      rw [Math.PMFProduct.pmfPi_update_bind]
    intro a; congr 1; funext i
    by_cases hi : i = q
    · subst hi
      simp only [Function.update_self, σ']
      -- goal: (if ↑q < pVal + 1 then PMF.pure a else ...) = PMF.pure a
      have : (q : Fin n).val < pVal + 1 := show pVal < pVal + 1 from by omega
      rw [if_pos this]
    · simp only [Function.update_of_ne hi, σ']
      -- goal: (if ↑i < pVal + 1 then ... else ...) = (if ↑i < pVal then ... else ...)
      have hne : i.val ≠ pVal := fun h => hi (Fin.ext h)
      congr 1; ext; constructor <;> intro h <;> omega

/-- Resolving from player 0 with default actions equals the joint behavioral
sampling `pmfPi (fun i => σ i (r.view i s (sig i)))`. -/
theorem resolveActionsMixed_eq_pmfPi [Fintype (Fin n)]
    (σ : BehavioralProfile n V A) (r : Round n S V A Sig)
    (s : S) (sig : Fin n → Sig) :
    resolveActionsMixed σ r s sig 0 (fun _ => none) =
      Math.PMFProduct.pmfPi (fun i => σ i (r.view i s (sig i))) :=
  resolveActionsMixed_gen σ r s sig 0 _

/-- Evaluate from a `LinConfig` using behavioral strategies. Like `evalFromCfg`
but samples actions from behavioral distributions rather than applying pure
strategies deterministically. -/
noncomputable def evalFromCfgMixed
    (G : Protocol n S V A Sig) (σ : BehavioralProfile n V A) : LinConfig G → PMF S
  | .terminal s => PMF.pure s
  | .signal k s => evalRoundsMixed (G.rounds.drop k) σ s
  | .playerTurn k s sig p accActs =>
      match G.rounds[k]? with
      | some r =>
        (resolveActionsMixed σ r s sig p.val accActs).bind fun fullActs =>
          let next := r.transition s fullActs
          evalRoundsMixed (G.rounds.drop (k + 1)) σ next
      | none => PMF.pure s
  | .applyTransition k s _sig accActs =>
      match G.rounds[k]? with
      | some r =>
        let next := r.transition s accActs
        evalRoundsMixed (G.rounds.drop (k + 1)) σ next
      | none => PMF.pure s

/-- `evalFromCfgMixed` at the initial configuration equals `Protocol.evalMixed`. -/
theorem evalFromCfgMixed_init (G : Protocol n S V A Sig)
    (σ : BehavioralProfile n V A) :
    evalFromCfgMixed G σ (linInitialConfig G) = G.evalMixed σ := by
  simp only [linInitialConfig]
  split <;> simp only [evalFromCfgMixed]
  · -- G.rounds[0]? = none → rounds is empty
    rename_i h
    have hnil : G.rounds = [] := by
      match hr : G.rounds with
      | [] => rfl
      | _ :: _ => simp [hr] at h
    simp [Protocol.evalMixed, evalRoundsMixed, hnil]
  · -- G.rounds[0]? ≠ none → signal case
    rw [List.drop_zero]
    rfl

/-- At done configs, `evalFromCfgMixed` reduces to `PMF.pure cfg.state`. -/
private theorem evalFromCfgMixed_of_isDone (G : Protocol n S V A Sig)
    (σ : BehavioralProfile n V A) (cfg : LinConfig G)
    (hd : cfg.isDone G) :
    evalFromCfgMixed G σ cfg = PMF.pure cfg.state := by
  cases cfg with
  | terminal s => rfl
  | signal k s =>
    change evalRoundsMixed (G.rounds.drop k) σ s = PMF.pure s
    have hdr : G.rounds.drop k = [] := by
      apply List.drop_eq_nil_of_le
      by_contra h; push_neg at h
      have : G.rounds[k]? = some G.rounds[k] := List.getElem?_eq_getElem h
      simp [LinConfig.isDone, this] at hd
    rw [hdr]; rfl
  | playerTurn k s sig p accActs =>
    change (match G.rounds[k]? with | some r => _ | none => PMF.pure s) = PMF.pure s
    have hd' : G.rounds[k]? = none := hd
    rw [hd']
  | applyTransition k s sig accActs =>
    change (match G.rounds[k]? with | some r => _ | none => PMF.pure s) = PMF.pure s
    have hd' : G.rounds[k]? = none := hd
    rw [hd']

variable [Fintype (Fin n)] [Fintype A]

omit [Fintype (Option A)] in
/-- Any config reachable via `stepDist` is in the support of `linConfigStepPMF`
for some action choice. -/
private theorem stepDist_support_subset_step_support
    {β : ObsModelCore.BehavioralProfile (compiledLinObs G)}
    {ss : List (LinConfig G)} {t : LinConfig G}
    (ht : t ∈ ((compiledLinObs G).stepDist β ss).support) :
    ∃ acts, t ∈ (linConfigStepPMF G ((compiledLinObs G).lastState ss) acts).support := by
  simp only [ObsModelCore.stepDist, PMF.mem_support_bind_iff] at ht
  obtain ⟨a, _, ht'⟩ := ht
  exact ⟨(compiledLinObs G).castJointAction ss a, ht'⟩

omit [Fintype (Option A)] in
/-- For large enough k, all configs reachable by `runDist k β` are done. -/
private theorem isDone_of_reachable_behavioral
    {β : ObsModelCore.BehavioralProfile (compiledLinObs G)}
    (k : Nat) (ss : List (LinConfig G))
    (hss : ((compiledLinObs G).runDist k β) ss ≠ 0) :
    ((compiledLinObs G).lastState ss).isDone G ∨
    ((compiledLinObs G).lastState ss).phase G ≥ k := by
  induction k generalizing ss with
  | zero => right; omega
  | succ k ih =>
    change _ at hss
    rw [show (compiledLinObs G).runDist (k + 1) β =
      ((compiledLinObs G).runDist k β).bind
        (fun ss' => Math.ProbabilityMassFunction.pushforward
          ((compiledLinObs G).stepDist β ss')
          (fun t => ss' ++ [t])) from rfl] at hss
    have hsupp := (PMF.mem_support_iff _ _).mpr hss
    rw [PMF.mem_support_bind_iff] at hsupp
    obtain ⟨ss', hss'_supp, ht_supp⟩ := hsupp
    rw [show Math.ProbabilityMassFunction.pushforward
        ((compiledLinObs G).stepDist β ss')
        (fun t => ss' ++ [t]) =
      ((compiledLinObs G).stepDist β ss').map
        (fun t => ss' ++ [t]) from rfl] at ht_supp
    rw [PMF.mem_support_map_iff] at ht_supp
    obtain ⟨t, ht_in_step, rfl⟩ := ht_supp
    rw [lastState_snoc]
    have ih_ss' := ih ss' ((PMF.mem_support_iff _ _).mp hss'_supp)
    obtain ⟨acts', ht_acts⟩ := stepDist_support_subset_step_support ht_in_step
    by_cases hd : ((compiledLinObs G).lastState ss').isDone G
    · left; exact (isDone_step_of_isDone G _ acts' hd t ht_acts).1
    · right
      have hprog := phase_step_progress G _ acts' hd t ht_acts
      rcases ih_ss' with hd' | hph
      · exact absurd hd' hd
      · omega

private theorem stepDist_liftBehavioral_bind_evalFromCfgMixed
    (σ : BehavioralProfile n V A) (ss : List (LinConfig G)) :
    ((compiledLinObs G).stepDist (liftBehavioralProfile σ) ss).bind
        (evalFromCfgMixed G σ) =
      evalFromCfgMixed G σ ((compiledLinObs G).lastState ss) := by
  -- Unfold stepDist and merge binds.
  simp only [ObsModelCore.stepDist, ObsModelCore.jointActionDist]
  rw [PMF.bind_bind]
  -- Relate projectStates to linObserve at lastState (identity info states).
  have hps : ∀ i, (compiledLinObs G).projectStates i ss =
      linObserve G i ((compiledLinObs G).lastState ss) := fun i => by
    have h := ObsModelCore.currentObs_projectStates (compiledLinObs G) i ss
    simp only [ObsModelCore.currentObs, compileObsCoreModelLin] at h; exact h
  -- suffices: prove the result by cases on the config type of lastState ss.
  -- We use a helper that takes cfg explicitly, avoiding castJointAction issues.
  suffices helper : ∀ (cfg : LinConfig G)
      (obs : Fin n → Option (RoundView G))
      (hobs : ∀ i, obs i = linObserve G i cfg),
      ((Math.PMFProduct.pmfPi (fun i =>
          liftBehavioralStrategy (G := G) (σ i) (obs i))).bind
        (fun a => (linConfigStepPMF G cfg
          (fun i => cast (congrArg (LinAct (RoundView G) A) (hobs i)) (a i))).bind
          (evalFromCfgMixed G σ))) =
      evalFromCfgMixed G σ cfg by
    convert helper ((compiledLinObs G).lastState ss)
      (fun i => (compiledLinObs G).projectStates i ss) hps using 2
    rename_i a
    funext j; congr 1; congr 1
    funext i
    -- Both sides transport j i along propositionally equal proofs.
    -- castJointAction uses currentObs_projectStates, the other uses hps.
    simp only [ObsModelCore.castJointAction, compileObsCoreModelLin]
    simp [eqRec_eq_cast]
  -- Now prove the helper by cases on cfg.
  intro cfg obs hobs
  cases cfg with
  | terminal s =>
    -- All obs are none, step is PMF.pure (terminal s)
    have hall : ∀ i, obs i = none := fun i => by simp [hobs, linObserve]
    simp only [linConfigStepPMF, PMF.pure_bind, evalFromCfgMixed]
    simp [PMF.bind_const]
  | signal k s =>
    -- All obs are none for signal configs
    have hall : ∀ i, obs i = none := fun i => by simp [hobs, linObserve]
    -- linConfigStepPMF at signal doesn't use the action tuple.
    -- Show the function is constant, then use PMF.bind_const.
    have default_a : (i : Fin n) → LinAct (RoundView G) A (obs i) :=
      fun i => (hall i).symm ▸ PUnit.unit
    have hconst : ∀ (a : (i : Fin n) → LinAct (RoundView G) A (obs i)),
        (linConfigStepPMF G (.signal k s)
          (fun i => cast (congrArg _ (hobs i)) (a i))).bind
          (evalFromCfgMixed G σ) =
        (linConfigStepPMF G (.signal k s)
          (fun i => cast (congrArg _ (hobs i)) (default_a i))).bind
          (evalFromCfgMixed G σ) := by
      intro a; congr 1
    simp_rw [hconst]; rw [PMF.bind_const]
    -- Now: step(any_acts).bind(eval) = eval(signal k s)
    simp only [linConfigStepPMF]
    split
    case h_1 r hr =>
      have hk : k < G.rounds.length := by
        by_contra h; push_neg at h; simp [List.getElem?_eq_none (by omega)] at hr
      have hdrop : G.rounds.drop k = r :: G.rounds.drop (k + 1) := by
        rw [← List.cons_getElem_drop_succ (h := hk)]
        congr 1; exact (List.getElem_of_getElem? hr).choose_spec
      split
      case isTrue hn =>
        rw [PMF.bind_map]
        simp only [Function.comp_def, evalFromCfgMixed, hr, hdrop, evalRoundsMixed_cons,
          Round.evalMixed, PMF.bind_bind]
        congr 1; funext sig'
        conv_rhs => rw [PMF.bind_map]; simp only [Function.comp_def]
        rw [resolveActionsMixed_eq_pmfPi]; convert rfl using 3
      case isFalse hn =>
        rw [PMF.bind_map]
        simp only [Function.comp_def, evalFromCfgMixed, hr, hdrop, evalRoundsMixed_cons,
          Round.evalMixed, PMF.bind_bind]
        congr 1; funext sig'
        have hn0 : n = 0 := by omega
        subst hn0
        have : ∀ f : Fin 0 → Option A, r.transition s f = r.transition s (fun _ => none) := by
          intro f; congr 1; funext i; exact Fin.elim0 i
        simp_rw [this]
        have hmc : (fun acts : Fin 0 → Option A => r.transition s fun x => none) =
            Function.const _ (r.transition s fun x => none) := funext fun _ => rfl
        rw [hmc, PMF.map_const, PMF.pure_bind]
    case h_2 hr =>
      simp [PMF.pure_bind, evalFromCfgMixed]
  | playerTurn k s sig p accActs =>
    simp only [linConfigStepPMF]
    split
    case h_2 hr =>
      -- G.rounds[k]? = none: step is pure, all obs are none
      have hlen : G.rounds.length ≤ k := by
        by_contra h; push_neg at h; rw [List.getElem?_eq_getElem h] at hr; exact absurd hr (by simp)
      have hall : ∀ i, obs i = none := fun i => by
        rw [hobs]; simp [linObserve, show ¬(k < G.rounds.length) from by omega]
      simp only [PMF.pure_bind, evalFromCfgMixed, hr]
      simp only [PMF.bind_const]
    case h_1 r hr =>
      have hk : k < G.rounds.length := by
        by_contra h; push_neg at h; simp [List.getElem?_eq_none (by omega)] at hr
      -- Observations: player p sees some, others see none
      have hobs_p : obs p = some (⟨k, hk⟩, r.view p s (sig p)) := by
        rw [hobs]; simp [linObserve, hk, (List.getElem_of_getElem? hr).choose_spec]
      have hobs_ne : ∀ i, i ≠ p → obs i = none := fun i hi => by
        rw [hobs]; simp [linObserve, hi]
      -- Unfold advancePlayerTurn and evalFromCfgMixed on the RHS
      simp only [advancePlayerTurn, evalFromCfgMixed, hr]
      -- Unfold resolveActionsMixed one step
      rw [resolveActionsMixed, dif_pos p.isLt]
      simp only [PMF.bind_bind]
      -- The continuation only depends on extractPlayerAction, which only uses a p.
      -- We'll show extractPlayerAction gives cast(a p) = the Option A value of a p.
      -- Then factor the pmfPi to extract player p's marginal.
      -- Step 1: Simplify the bind. Push pure_bind inside the if.
      have hbind_eq :
          ∀ a : (i : Fin n) → LinAct (RoundView G) A (obs i),
          ((if h : ↑p + 1 < n then
              PMF.pure (LinConfig.playerTurn k s sig ⟨↑p + 1, h⟩
                (Function.update accActs p
                  (extractPlayerAction G k s sig p accActs
                    fun i => cast (congrArg _ (hobs i)) (a i))))
            else
              PMF.pure (LinConfig.applyTransition k s sig
                (Function.update accActs p
                  (extractPlayerAction G k s sig p accActs
                    fun i => cast (congrArg _ (hobs i)) (a i))))).bind
            (evalFromCfgMixed G σ)) =
          (resolveActionsMixed σ r s sig (↑p + 1)
            (Function.update accActs p
              (extractPlayerAction G k s sig p accActs
                fun i => cast (congrArg _ (hobs i)) (a i)))).bind
            fun fullActs =>
              evalRoundsMixed (G.rounds.drop (k + 1)) σ
                (r.transition s fullActs) := by
        intro a
        split
        case isTrue hp1 =>
          rw [PMF.pure_bind]
          simp only [evalFromCfgMixed, hr]
        case isFalse hp1 =>
          rw [PMF.pure_bind]
          simp only [evalFromCfgMixed, hr]
          rw [resolveActionsMixed, dif_neg (by omega)]
          simp [PMF.pure_bind]
      simp_rw [hbind_eq]
      -- Step 2: extractPlayerAction with cast gives cast(a p).
      -- extractPlayerAction uses cast based on linObserve.
      -- Net effect: extractPlayerAction = a p (modulo cast).
      have hextract :
          ∀ a : (i : Fin n) → LinAct (RoundView G) A (obs i),
          extractPlayerAction G k s sig p accActs
            (fun i => cast (congrArg _ (hobs i)) (a i)) =
          cast (congrArg _ hobs_p) (a p) := by
        intro a
        unfold extractPlayerAction
        rw [dif_pos hk]
        -- Both sides cast (a p) to Option A through propositionally equal proofs
        simp only [cast_cast]
      simp_rw [hextract]
      -- Goal: pmfPi(lift).bind(fun a => g(cast(a p))) = (σ p view).bind(fun ap => g ap)
      -- The cast transports LinAct(obs p) → LinAct(some(k_fin, view)) = Option A.
      -- We prove the two sides are equal using pmfPi_bind_eval after
      -- eliminating the cast via congrArg on the continuation.
      -- First, show the cast is identity by changing it to an Eq.rec and using
      -- proof that the two types are equal via hobs_p.
      -- pmfPi_bind_eval says: pmfPi(σ).bind(fun s => f(s j)) = (σ j).bind f
      -- Our continuation is: fun a => g(cast ⋯ (a p))
      -- = fun a => (fun ap => g(cast ⋯ ap)) (a p)
      -- = fun a => f(a p) where f = fun ap => g(cast ⋯ ap)
      -- So pmfPi_bind_eval gives:
      -- (liftBehavioralStrategy (σ p) (obs p)).bind(fun ap => g(cast ⋯ ap))
      -- We need this to equal (σ p view).bind g.
      -- Key: cast ⋯ is a function LinAct(obs p) → Option A, and
      -- liftBehavioralStrategy (σ p) (obs p) : PMF (LinAct(obs p)).
      -- We use the fact that for any h : α = β,
      -- (cast (show PMF α = PMF β from congrArg PMF h) d).bind f = d.bind (f ∘ cast h)
      -- And liftBehavioralStrategy (σ p) (obs p) = cast ⋯ (σ p view).
      -- Then: (cast ⋯ (σ p view)).bind(f ∘ cast ⋯) = (σ p view).bind f.
      -- Actually, let's use a simpler approach.
      -- Directly show: ∀ (h : obs p = some(k, v)),
      -- Factor the pmfPi to extract player p's marginal via pmfPi_bind_eval.
      have heval := Math.PMFProduct.pmfPi_bind_eval
        (fun i => liftBehavioralStrategy (G := G) (σ i) (obs i)) p
        (fun (ap : LinAct (RoundView G) A (obs p)) =>
          (resolveActionsMixed σ r s sig (↑p + 1)
            (Function.update accActs p (cast (congrArg (LinAct (RoundView G) A) hobs_p) ap))).bind
            fun fullActs => evalRoundsMixed (G.rounds.drop (k + 1)) σ (r.transition s fullActs))
      rw [heval]; clear heval
      -- Goal: (liftBehav(σ p)(obs p)).bind(fun ap => g(cast ap)) = (σ p view).bind g
      -- Generalize obs p to a free variable so we can subst.
      set op := obs p with hop_def
      rw [hobs_p] at hop_def
      -- Now op = some(⟨k,hk⟩, r.view p s (sig p)) and we have hobs_p : op = some(...)
      -- But op appears in the types. We need to rewrite using hobs_p.
      -- Use a general lemma: for h : α = β, cast h applied to bind gives the same.
      have key : ∀ (o : Option (RoundView G))
          (h : o = some (⟨k, hk⟩, r.view p s (sig p)))
          (g' : Option A → PMF S),
          (liftBehavioralStrategy (G := G) (σ p) o).bind
            (fun ap => g' (cast (congrArg (LinAct (RoundView G) A) h) ap)) =
          (σ p (r.view p s (sig p))).bind g' := by
        intro o h g'; subst h; simp [liftBehavioralStrategy, cast_eq]
      convert key op hobs_p _ using 2
      ext ap; congr 2
  | applyTransition k s sig accActs =>
    -- All obs are none, step doesn't depend on actions
    have hall : ∀ i, obs i = none := fun i => by simp [hobs, linObserve]
    have default_a : (i : Fin n) → LinAct (RoundView G) A (obs i) :=
      fun i => (hall i).symm ▸ PUnit.unit
    have hconst : ∀ (a : (i : Fin n) → LinAct (RoundView G) A (obs i)),
        (linConfigStepPMF G (.applyTransition k s sig accActs)
          (fun i => cast (congrArg (LinAct (RoundView G) A) (hobs i)) (a i))).bind
          (evalFromCfgMixed G σ) =
        (linConfigStepPMF G (.applyTransition k s sig accActs)
          (fun i => cast (congrArg (LinAct (RoundView G) A) (hobs i)) (default_a i))).bind
          (evalFromCfgMixed G σ) := by
      intro a; congr 1
    simp_rw [hconst]; rw [PMF.bind_const]
    simp only [linConfigStepPMF]
    split
    case h_1 r hr =>
      split
      case h_1 _ hr2 =>
        simp only [PMF.pure_bind, evalFromCfgMixed, hr]
      case h_2 _ hr2 =>
        simp only [PMF.pure_bind, evalFromCfgMixed, hr]
        have hdrop2 : G.rounds.drop (k + 1) = [] :=
          List.drop_eq_nil_of_le (by
            by_contra h; push_neg at h
            rw [List.getElem?_eq_getElem h] at hr2; exact absurd hr2 (by simp))
        rw [hdrop2, evalRoundsMixed]; simp
    case h_2 hr =>
      simp [PMF.pure_bind, evalFromCfgMixed, hr]

/-- **Behavioral adequacy (telescoping)**: running the linearized model for `k`
steps under `liftBehavioralProfile σ` and composing with `evalFromCfgMixed`
equals `evalFromCfgMixed` at the initial configuration.

Uses `runDist_bind_interp` with the one-step simulation. -/
theorem runDist_liftBehavioral_bind_evalFromCfgMixed
    (σ : BehavioralProfile n V A) (k : Nat) :
    ((compiledLinObs G).runDist k (liftBehavioralProfile σ)).bind
        (fun ss => evalFromCfgMixed G σ ((compiledLinObs G).lastState ss)) =
      G.evalMixed σ := by
  have hstep := stepDist_liftBehavioral_bind_evalFromCfgMixed (G := G) σ
  have := ObsModelCore.runDist_bind_interp (compiledLinObs G)
    (evalFromCfgMixed G σ) (liftBehavioralProfile σ) hstep k
  rw [this]
  exact evalFromCfgMixed_init G σ

/-- **Behavioral adequacy (state extraction)**: running the linearized model
for enough steps and extracting the terminal state gives `Protocol.evalMixed`.

For large enough `k`, all reachable configs are done, so `evalFromCfgMixed`
reduces to `PMF.pure ∘ state`. -/
theorem runDist_liftBehavioral_extractState_eq_evalMixed
    (σ : BehavioralProfile n V A) (k : Nat) (hk : k ≥ G.rounds.length * (n + 2)) :
    ((compiledLinObs G).runDist k (liftBehavioralProfile σ)).bind
        (fun ss => PMF.pure ((compiledLinObs G).lastState ss).state) =
      G.evalMixed σ := by
  rw [← runDist_liftBehavioral_bind_evalFromCfgMixed (G := G) σ k]
  apply PMF.bind_congr_support
  intro ss hss
  have hdr := isDone_of_reachable_behavioral (G := G) k ss hss
  rcases hdr with hd | hph
  · exact (evalFromCfgMixed_of_isDone G σ _ hd).symm
  · exact (evalFromCfgMixed_of_isDone G σ _
      (isDone_of_phase_ge G _ (by omega))).symm

end BehavioralAdequacy


-- ============================================================================
-- ObsLocalFeasibility from FullRecall
-- ============================================================================

section OLFBridge

open Math.ParameterizedChain

variable [DecidableEq (Fin n)] [Fintype (Fin n)]
variable [Fintype A] [Nonempty A]
variable (G : Protocol n S V A Sig)

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- `linObserve G i cfg = some obs` implies cfg is a playerTurn for player i
at a valid round, and extracts the state, signals, and accumulated actions. -/
theorem linObserve_some_playerTurn (cfg : LinConfig G) (i : Fin n)
    (obs : RoundView G)
    (h : linObserve G i cfg = some obs) :
    ∃ (s : S) (sig : Fin n → Sig) (accActs : Fin n → Option A),
      cfg = .playerTurn obs.1.val s sig i accActs ∧
      (G.rounds[obs.1.val]'(obs.1.isLt)).view i s (sig i) = obs.2 := by
  cases cfg with
  | signal _ _ => simp [linObserve] at h
  | terminal _ => simp [linObserve] at h
  | applyTransition _ _ _ _ => simp [linObserve] at h
  | playerTurn k s sig p accActs =>
    simp only [linObserve] at h
    split at h
    · rename_i hip
      split at h
      · rename_i hk
        simp only [Option.some.injEq] at h
        subst hip
        have hk_eq : k = obs.1.val := by
          have := congrArg (fun x => x.1.val) h; simp at this; omega
        have hv_eq : G.rounds[k].view i s (sig i) = obs.2 := congrArg Prod.snd h
        subst hk_eq
        exact ⟨s, sig, accActs, rfl, hv_eq⟩
      · simp at h
    · simp at h

set_option linter.unusedFintypeInType false in
/-- `linObserve G i cfg = some obs` implies `cfg` is not done. -/
private theorem not_isDone_of_linObserve_some
    (cfg : LinConfig G) (i : Fin n) (obs : RoundView G)
    (h : linObserve G i cfg = some obs) : ¬ cfg.isDone G := by
  obtain ⟨s, sig, accActs, hcfg, _⟩ := linObserve_some_playerTurn G cfg i obs h
  subst hcfg
  change ¬ (G.rounds[obs.1.val]? = none)
  rw [show G.rounds[obs.1.val]? = some G.rounds[obs.1.val] from
    List.getElem?_eq_getElem obs.1.isLt]
  exact Option.some_ne_none _

set_option linter.unusedFintypeInType false in
/-- Phase of a config where `linObserve G i cfg = some (⟨r, hr⟩, v)`. -/
private theorem phase_of_linObserve_some
    (cfg : LinConfig G) (i : Fin n) (r : Fin G.rounds.length) (v : V)
    (h : linObserve G i cfg = some (r, v)) :
    cfg.phase G = r.val * (n + 2) + i.val + 1 := by
  obtain ⟨s, sig, accActs, hcfg, _⟩ := linObserve_some_playerTurn G cfg i ⟨r, v⟩ h
  rw [hcfg]; simp [LinConfig.phase]

set_option linter.unusedSectionVars false in
/-- On a nonzero trace, if `ss[b]` is not done, then `ss[a]` is not done for `a ≤ b`. -/
private theorem not_isDone_of_later_not_isDone
    (pi : (compiledLinObs G).PureProfile)
    (k : Nat) (ss : List (LinConfig G))
    (hss : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init k pi ss ≠ 0)
    (a b : Nat) (ha : a < ss.length) (hb : b < ss.length) (hab : a ≤ b)
    (hnd : ¬ (ss[b]'hb).isDone G) : ¬ (ss[a]'ha).isDone G := by
  intro hd; apply hnd
  suffices h : ∀ c, a ≤ c → (hc : c < ss.length) → (ss[c]'hc).isDone G from h b hab hb
  intro c hac
  induction c with
  | zero =>
    intro hc
    have ha0 : a = 0 := by omega
    subst ha0; exact hd
  | succ c ih =>
    intro hc
    by_cases hac' : a ≤ c
    · have hc' : c < ss.length := by omega
      have ihc := ih hac' hc'
      have hstep := pureRun_step_nonzero _ _ k pi ss hss c (show c + 1 < ss.length by omega)
      rw [pureStep_compiledLin_eq] at hstep
      have hcfg := lastState_take_eq_getElem ss c (show c + 1 < ss.length by omega)
      rw [hcfg] at hstep
      exact (isDone_step_of_isDone G _ _ ihc _ (PMF.mem_support_iff _ _ |>.mpr hstep)).1
    · have ha0 : a = c + 1 := by omega
      subst ha0; exact hd

/-- On a nonzero trace, if `ss[b]` is not done and `a < b`, then
`phase(ss[a]) < phase(ss[b])`. -/
private theorem phase_strict_mono_of_not_done
    (pi : (compiledLinObs G).PureProfile)
    (k : Nat) (ss : List (LinConfig G))
    (hss : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init k pi ss ≠ 0)
    (a b : Nat) (ha : a < ss.length) (hb : b < ss.length) (hab : a < b)
    (hnd : ¬ (ss[b]'hb).isDone G) :
    (ss[a]'ha).phase G < (ss[b]'hb).phase G := by
  induction b with
  | zero => omega
  | succ b' ih =>
    have hb'lt : b' < ss.length := by omega
    have hstep := pureRun_step_nonzero _ _ k pi ss hss b' (show b' + 1 < ss.length by omega)
    rw [pureStep_compiledLin_eq] at hstep
    have hcfg := lastState_take_eq_getElem ss b' (show b' + 1 < ss.length by omega)
    rw [hcfg] at hstep
    have hnd' : ¬ (ss[b']'hb'lt).isDone G :=
      not_isDone_of_later_not_isDone G pi k ss hss b' (b' + 1) hb'lt hb (by omega) hnd
    have hprog := phase_step_progress G _ _ hnd' _ (PMF.mem_support_iff _ _ |>.mpr hstep)
    by_cases hab' : a < b'
    · exact lt_of_lt_of_le (ih hb'lt hab' hnd') (by omega)
    · have hab'eq : a = b' := by omega
      subst hab'eq; omega

/-- The first element of a nonzero `pureRun` trace is the initial state. -/
private theorem pureRun_head_eq_init
    {T P : Type} (step : P → List T → PMF T) (s₀ : T)
    (m : Nat) (π : P) (ss : List T)
    (h : pureRun step s₀ m π ss ≠ 0)
    (h0 : 0 < ss.length) :
    ss[0] = s₀ := by
  induction m generalizing ss with
  | zero =>
    have hss : ss = [s₀] := by
      by_contra hne; exact h (by simp [pureRun, PMF.pure_apply, hne])
    subst hss; rfl
  | succ m ih =>
    have hne : ss ≠ [] := by intro he; subst he; simp at h0
    have hsplit := (List.dropLast_append_getLast hne).symm
    have h_pre : pureRun step s₀ m π ss.dropLast ≠ 0 := by
      rw [hsplit] at h; rw [pureRun_succ_append] at h; exact left_ne_zero_of_mul h
    have hlen_pre : 0 < ss.dropLast.length := by
      have := pureRun_length step s₀ m π ss.dropLast h_pre; omega
    have hih := ih ss.dropLast h_pre hlen_pre
    -- ss[0] = ss.dropLast[0] since dropLast is a prefix
    have h_eq : ss[0] = ss.dropLast[0]'hlen_pre := by
      rcases ss with _ | ⟨hd, tl⟩
      · exact absurd rfl hne
      · cases tl with
        | nil => simp at hlen_pre
        | cons h t => rfl
    rw [h_eq, hih]

set_option linter.unusedSectionVars false in
/-- On a nonzero trace where `ss[last]` is not done, `phase(ss[j]) = j` for all j. -/
private theorem phase_eq_index
    (pi : (compiledLinObs G).PureProfile)
    (k : Nat) (ss : List (LinConfig G))
    (hss : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init k pi ss ≠ 0)
    (hlast_nd : ¬ (ss[ss.length - 1]'(by
      have := pureRun_length _ _ k pi ss hss; omega)).isDone G)
    (j : Nat) (hj : j < ss.length) :
    (ss[j]'hj).phase G = j := by
  induction j with
  | zero =>
    have hlen : 0 < ss.length := by omega
    have h0 := pureRun_head_eq_init _ _ k pi ss hss hlen
    conv_lhs => rw [show ss[0]'hj = ss[0]'hlen from rfl, h0]
    -- linInitialConfig G phase
    simp only [compiledLinObs, compileObsCoreModelLin, linInitialConfig]
    split
    · -- rounds empty: terminal phase = G.rounds.length * (n+2) = 0
      rename_i hempty
      simp only [LinConfig.phase]
      have : G.rounds.length = 0 := by
        by_contra hne; push_neg at hne
        have : G.rounds[0]? ≠ none := by
          rw [ne_eq, List.getElem?_eq_none_iff]; omega
        exact this hempty
      simp [this]
    · simp [LinConfig.phase]
  | succ j ih =>
    have hjlt : j < ss.length := by omega
    have hnd_j : ¬ (ss[j]'hjlt).isDone G :=
      not_isDone_of_later_not_isDone G pi k ss hss j (ss.length - 1) hjlt
        (by have := pureRun_length _ _ k pi ss hss; omega) (by omega) hlast_nd
    have hstep := pureRun_step_nonzero _ _ k pi ss hss j (show j + 1 < ss.length by omega)
    rw [pureStep_compiledLin_eq] at hstep
    have hcfg := lastState_take_eq_getElem ss j (show j + 1 < ss.length by omega)
    rw [hcfg] at hstep
    have hprog := phase_step_progress G _ _ hnd_j _ (PMF.mem_support_iff _ _ |>.mpr hstep)
    rw [hprog, ih hjlt]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- A config with phase `r*(n+2) + i.val + 1` (where `r < G.rounds.length` and `i < n`)
is a `playerTurn` for player `i` at round `r`, so `linObserve G i` returns `some`. -/
private theorem linObserve_of_phase_eq
    (cfg : LinConfig G) (p : Fin n)
    (r : Nat) (hr : r < G.rounds.length)
    (hphase : cfg.phase G = r * (n + 2) + p.val + 1) :
    ∃ (v : V), linObserve G p cfg = some (⟨r, hr⟩, v) := by
  cases cfg with
  | signal k s =>
    simp only [LinConfig.phase] at hphase
    -- k*(n+2) = r*(n+2) + p.val + 1, impossible since p.val+1 < n+2
    exfalso
    rcases le_or_gt r k with hrk | hrk
    · have heq : (k - r) * (n + 2) = p.val + 1 := by
        rw [Nat.sub_mul]; omega
      rcases Nat.eq_zero_or_pos (k - r) with h0 | h0
      · simp [h0] at heq
      · have := Nat.le_mul_of_pos_left (n + 2) h0; omega
    · have : k * (n + 2) < r * (n + 2) :=
        (Nat.mul_lt_mul_right (by omega : 0 < n + 2)).mpr hrk
      omega
  | playerTurn k s sig q accActs =>
    simp only [LinConfig.phase] at hphase
    -- k*(n+2) + q.val + 1 = r*(n+2) + p.val + 1 → k = r, q = p
    have hk : k = r := by
      rcases le_or_gt r k with hrk | hrk
      · rcases le_or_gt k r with hkr | hkr
        · omega
        · have : (k - r) * (n + 2) = p.val - q.val := by rw [Nat.sub_mul]; omega
          rcases Nat.eq_zero_or_pos (k - r) with h0 | h0
          · omega
          · have := Nat.le_mul_of_pos_left (n + 2) h0; omega
      · have : (r - k) * (n + 2) = q.val - p.val := by rw [Nat.sub_mul]; omega
        rcases Nat.eq_zero_or_pos (r - k) with h0 | h0
        · omega
        · have := Nat.le_mul_of_pos_left (n + 2) h0; omega
    subst hk
    have hp : q = p := Fin.ext (by omega)
    subst hp
    simp only [linObserve]
    split
    · exact ⟨G.rounds[k].view q s (sig q), rfl⟩
    · rename_i habs
      exfalso
      have : G.rounds[k]? ≠ none := by rw [ne_eq, List.getElem?_eq_none_iff]; omega
      simp at habs
  | applyTransition k s sig accActs =>
    simp only [LinConfig.phase] at hphase
    -- k*(n+2) + n + 1 = r*(n+2) + p.val + 1, same sub_mul technique
    exfalso
    rcases le_or_gt k r with hkr | hkr
    · have heq : (r - k) * (n + 2) = n - p.val := by rw [Nat.sub_mul]; omega
      rcases Nat.eq_zero_or_pos (r - k) with h0 | h0
      · simp [h0] at heq; omega
      · have := Nat.le_mul_of_pos_left (n + 2) h0; omega
    · have heq : (k - r) * (n + 2) = p.val - n := by rw [Nat.sub_mul]; omega
      rcases Nat.eq_zero_or_pos (k - r) with h0 | h0
      · omega
      · have := Nat.le_mul_of_pos_left (n + 2) h0; omega
  | terminal s =>
    simp only [LinConfig.phase] at hphase
    -- G.rounds.length*(n+2) = r*(n+2) + p.val + 1, same technique as signal
    exfalso
    rcases le_or_gt r G.rounds.length with hrk | hrk
    · have heq : (G.rounds.length - r) * (n + 2) = p.val + 1 := by rw [Nat.sub_mul]; omega
      rcases Nat.eq_zero_or_pos (G.rounds.length - r) with h0 | h0
      · simp [h0] at heq
      · have := Nat.le_mul_of_pos_left (n + 2) h0; omega
    · have : G.rounds.length * (n + 2) < r * (n + 2) :=
        (Nat.mul_lt_mul_right (by omega : 0 < n + 2)).mpr hrk
      omega

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- On a nonzero trace, if `linObserve G i ss[last] = some (kLast, vLast)`,
then for every r < kLast, there exists an internal position j (j+1 < ss.length)
with `linObserve G i ss[j] = some (r, v)` for some v. -/
private theorem earlier_i_step_exists
    (pi : (compiledLinObs G).PureProfile)
    (k : Nat) (ss : List (LinConfig G))
    (hss : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init k pi ss ≠ 0)
    (i : Fin n) (kLast : Fin G.rounds.length) (vLast : V)
    (hobsLast : linObserve G i (ss[ss.length - 1]'(by
      have := pureRun_length _ _ k pi ss hss; omega)) = some (kLast, vLast))
    (r : Nat) (hr : r < kLast.val) :
    ∃ (j : Nat) (hj : j + 1 < ss.length)
      (hr' : r < G.rounds.length) (v : V),
      linObserve G i (ss[j]'(by omega)) = some (⟨r, hr'⟩, v) := by
  have hlen := pureRun_length _ _ k pi ss hss
  have hlast_nd : ¬ (ss[ss.length - 1]'(by omega)).isDone G :=
    not_isDone_of_linObserve_some G _ i _ hobsLast
  have hr' : r < G.rounds.length := lt_trans hr kLast.isLt
  set target := r * (n + 2) + i.val + 1
  have hp_last := phase_of_linObserve_some G _ i kLast vLast hobsLast
  -- phase(ss[last]) = kLast.val * (n+2) + i.val + 1 = ss.length - 1
  have hlast_phase := phase_eq_index G pi k ss hss hlast_nd (ss.length - 1) (by omega)
  -- target < ss.length - 1
  have htarget_lt_last : target < ss.length - 1 := by
    rw [← hlast_phase, hp_last]
    change r * (n + 2) + i.val + 1 < kLast.val * (n + 2) + i.val + 1
    have : r * (n + 2) < kLast.val * (n + 2) :=
      (Nat.mul_lt_mul_right (by omega : 0 < n + 2)).mpr hr
    omega
  have htarget_lt : target < ss.length := by omega
  have hphase_target := phase_eq_index G pi k ss hss hlast_nd target htarget_lt
  obtain ⟨v, hobs⟩ := linObserve_of_phase_eq G (ss[target]'htarget_lt) i r hr' hphase_target
  exact ⟨target, by omega, hr', v, hobs⟩

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- Two positions in a nonzero trace with the same `linObserve G i` returning
`some` at the same round must be at the same position and have the same view. -/
private theorem unique_i_step_position
    (pi : (compiledLinObs G).PureProfile)
    (k : Nat) (ss : List (LinConfig G))
    (hss : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init k pi ss ≠ 0)
    (i : Fin n) (kLast : Fin G.rounds.length) (vLast : V)
    (_hobsLast : linObserve G i (ss[ss.length - 1]'(by
      have := pureRun_length _ _ k pi ss hss; omega)) = some (kLast, vLast))
    (j1 j2 : Nat) (hj1 : j1 + 1 < ss.length) (hj2 : j2 + 1 < ss.length)
    (r : Fin G.rounds.length) (v1 v2 : V)
    (hobs1 : linObserve G i (ss[j1]'(by omega)) = some (r, v1))
    (hobs2 : linObserve G i (ss[j2]'(by omega)) = some (r, v2)) :
    j1 = j2 ∧ v1 = v2 := by
  have hp1 := phase_of_linObserve_some G _ i r v1 hobs1
  have hp2 := phase_of_linObserve_some G _ i r v2 hobs2
  have hj_eq : j1 = j2 := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hnd2 : ¬ (ss[j2]'(by omega)).isDone G :=
        not_isDone_of_linObserve_some G _ i _ hobs2
      have := phase_strict_mono_of_not_done G pi k ss hss
        j1 j2 (by omega) (by omega) hlt hnd2
      omega
    · have hnd1 : ¬ (ss[j1]'(by omega)).isDone G :=
        not_isDone_of_linObserve_some G _ i _ hobs1
      have := phase_strict_mono_of_not_done G pi k ss hss
        j2 j1 (by omega) (by omega) hlt hnd1
      omega
  subst hj_eq
  have heq : (r, v1) = (r, v2) := Option.some_injective _ (hobs1.symm.trans hobs2)
  exact ⟨rfl, (Prod.mk.inj heq).2⟩

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- Show r < kLast from phase arithmetic on a trace. -/
private theorem round_lt_of_earlier_step
    (pi : (compiledLinObs G).PureProfile)
    (k : Nat) (ss : List (LinConfig G))
    (hss : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init k pi ss ≠ 0)
    (i : Fin n) (kLast : Fin G.rounds.length) (vLast : V)
    (hobsLast : linObserve G i (ss[ss.length - 1]'(by
      have := pureRun_length _ _ k pi ss hss; omega)) = some (kLast, vLast))
    (j : Nat) (hj : j + 1 < ss.length) (r : Fin G.rounds.length) (v : V)
    (hobs : linObserve G i (ss[j]'(by omega)) = some (r, v)) :
    r.val < kLast.val := by
  have hlast : ss.length - 1 < ss.length := by
    have := pureRun_length _ _ k pi ss hss; omega
  have hndLast : ¬ (ss[ss.length - 1]'hlast).isDone G :=
    not_isDone_of_linObserve_some G _ i _ hobsLast
  have hlt : j < ss.length - 1 := by omega
  have hphase_lt := phase_strict_mono_of_not_done G pi k ss hss
    j (ss.length - 1) (by omega) hlast hlt hndLast
  have hp_j := phase_of_linObserve_some G _ i r v hobs
  have hp_last := phase_of_linObserve_some G _ i kLast vLast hobsLast
  rw [hp_j, hp_last] at hphase_lt
  by_contra h; push_neg at h
  exact Nat.not_lt.mpr (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ h) _) _) hphase_lt

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- **FullRecall bridge**: On nonzero traces with same last i-observation,
for each round r < kLast, the view at round r matches between the two traces
and the profile actions at that view agree. -/
private theorem fullRecall_view_action_match
    (hFR : G.FullRecall)
    (pi0 pi0' : (compiledLinObs G).PureProfile)
    (n1 n2 : Nat) (ss1 ss2 : List (LinConfig G))
    (h1 : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init n1 pi0 ss1 ≠ 0)
    (h2 : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init n2 pi0' ss2 ≠ 0)
    (i : Fin n) (kLast : Fin G.rounds.length) (vLast : V)
    (hobs1 : linObserve G i (ss1[ss1.length - 1]'(by
      have := pureRun_length _ _ n1 pi0 ss1 h1; omega)) = some (kLast, vLast))
    (hobs2 : linObserve G i (ss2[ss2.length - 1]'(by
      have := pureRun_length _ _ n2 pi0' ss2 h2; omega)) = some (kLast, vLast))
    (r : Nat) (hr : r < kLast.val) :
    ∃ (hr' : r < G.rounds.length)
      (j1 : Nat) (hj1 : j1 + 1 < ss1.length) (v : V),
      linObserve G i (ss1[j1]'(by omega)) = some (⟨r, hr'⟩, v) ∧
      ∃ (j2 : Nat) (hj2 : j2 + 1 < ss2.length),
        linObserve G i (ss2[j2]'(by omega)) = some (⟨r, hr'⟩, v) ∧
        ∀ (o : Option (RoundView G)),
          o = some (⟨r, hr'⟩, v) →
          (pi0 i) o = (pi0' i) o := by
  obtain ⟨j1, hj1, hr', v1, hobs_j1⟩ :=
    earlier_i_step_exists G pi0 n1 ss1 h1 i kLast vLast hobs1 r hr
  obtain ⟨j2, hj2, _, v2, hobs_j2⟩ :=
    earlier_i_step_exists G pi0' n2 ss2 h2 i kLast vLast hobs2 r hr
  obtain ⟨s1, sig1, acc1, hcfg1, hview1⟩ :=
    linObserve_some_playerTurn G _ i ⟨⟨r, hr'⟩, v1⟩ hobs_j1
  obtain ⟨s2, sig2, acc2, hcfg2, hview2⟩ :=
    linObserve_some_playerTurn G _ i ⟨⟨r, _⟩, v2⟩ hobs_j2
  obtain ⟨sL1, sigL1, accL1, hcfgL1, hviewL1⟩ :=
    linObserve_some_playerTurn G _ i ⟨kLast, vLast⟩ hobs1
  obtain ⟨sL2, sigL2, accL2, hcfgL2, hviewL2⟩ :=
    linObserve_some_playerTurn G _ i ⟨kLast, vLast⟩ hobs2
  -- Build ExecRecords with correct actions for player i
  let act1 : Option A := (pi0 i) (some (⟨r, hr'⟩, v1))
  let act2 : Option A := (pi0' i) (some (⟨r, hr'⟩, v2))
  let recs1 : Fin (kLast.val + 1) → ExecRecord n S A Sig := fun m =>
    if hm : m.val = kLast.val then
      ⟨⟨sL1, sigL1⟩, fun _ => none⟩
    else if hm : m.val = r then
      ⟨⟨s1, sig1⟩, Function.update (fun _ => none) i act1⟩
    else ⟨⟨s1, sig1⟩, fun _ => none⟩
  let recs2 : Fin (kLast.val + 1) → ExecRecord n S A Sig := fun m =>
    if hm : m.val = kLast.val then
      ⟨⟨sL2, sigL2⟩, fun _ => none⟩
    else if hm : m.val = r then
      ⟨⟨s2, sig2⟩, Function.update (fun _ => none) i act2⟩
    else ⟨⟨s2, sig2⟩, fun _ => none⟩
  -- Views at round kLast match
  have hview_kLast : G.rounds[kLast.val].playerView i
        (recs1 ⟨kLast.val, Nat.lt_succ_self _⟩).toRound =
      G.rounds[kLast.val].playerView i
        (recs2 ⟨kLast.val, Nat.lt_succ_self _⟩).toRound := by
    simp only [recs1, recs2, ↓reduceDIte]
    simp only [ExecRecord.toRound, Round.playerView]
    rw [hviewL1, hviewL2]
  -- Apply FullRecall
  have hfr := hFR i kLast.val kLast.isLt recs1 recs2 hview_kLast r hr
  obtain ⟨hview_match, haction_match⟩ := hfr
  have hr_ne : ¬(r = kLast.val) := by omega
  simp only [recs1, recs2, hr_ne, ↓reduceDIte] at hview_match haction_match
  simp only [ExecRecord.toRound, Round.playerView] at hview_match
  change G.rounds[r].view i s1 (sig1 i) = v1 at hview1
  change G.rounds[r].view i s2 (sig2 i) = v2 at hview2
  have hv_eq : v1 = v2 := by rw [← hview1, ← hview2]; exact hview_match
  subst hv_eq
  simp only [Function.update_self] at haction_match
  refine ⟨hr', j1, hj1, v1, hobs_j1, j2, hj2, ?_, ?_⟩
  · convert hobs_j2 using 2
  · intro o ho; subst ho; exact haction_match

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- projectStates for the compiled model equals the last observation. -/
theorem projectStates_eq_lastObs
    (i : Fin n) (ss : List (LinConfig G)) (hne : ss ≠ []) :
    (compiledLinObs G).projectStates i ss =
      linObserve G i (ss[ss.length - 1]'(by
        rcases ss with _ | ⟨_, _⟩ <;> simp_all)) := by
  have h := ObsModelCore.currentObs_projectStates (compiledLinObs G) i ss
  change id ((compiledLinObs G).projectStates i ss) =
    (compiledLinObs G).observe i ((compiledLinObs G).lastState ss) at h
  rw [id_eq] at h; rw [h]
  simp only [ObsModelCore.lastState]
  rcases ss with _ | ⟨hd, tl⟩
  · exact absurd rfl hne
  · have hne' : hd :: tl ≠ [] := by simp
    rw [List.getLast?_eq_getLast_of_ne_nil hne', Option.getD_some,
      List.getLast_eq_getElem]
    rfl

set_option linter.unusedSectionVars false in
/-- **ObsLocalFeasibility for the linearized model under FullRecall**:
if two traces have the same `projectStates` for player i, then updating
player i's strategy preserves reachability equivalently. -/
theorem obsLocalFeasibility_of_fullRecall
    (hFR : G.FullRecall) (i : Fin n) :
    ObsModelCore.ObsLocalFeasibility (compiledLinObs G) i := by
  intro n1 n2 pi0 pi0' ss1 ss2 hproj h1 h2 hns pii
  have hlen1 := pureRun_length _ _ n1 pi0 ss1 h1
  have hlen2 := pureRun_length _ _ n2 pi0' ss2 h2
  have hne1 : ss1 ≠ [] := by intro h; subst h; simp at hlen1
  have hne2 : ss2 ≠ [] := by intro h; subst h; simp at hlen2
  have hproj1 := projectStates_eq_lastObs G i ss1 hne1
  have hproj2 := projectStates_eq_lastObs G i ss2 hne2
  have hproj' : linObserve G i (ss1[ss1.length - 1]'(by omega)) =
      linObserve G i (ss2[ss2.length - 1]'(by omega)) := by
    rw [← hproj1, ← hproj2]; exact hproj
  match hobs_last1 : linObserve G i (ss1[ss1.length - 1]'(by omega)) with
  | none =>
    exfalso; apply hns
    have : (compiledLinObs G).currentObs i ((compiledLinObs G).projectStates i ss1) =
        (compiledLinObs G).projectStates i ss1 := rfl
    rw [this, hproj1, hobs_last1]
    exact inferInstanceAs (Subsingleton PUnit)
  | some ⟨kLast, vLast⟩ =>
    have hobs_last2 : linObserve G i (ss2[ss2.length - 1]'(by omega)) =
        some (kLast, vLast) := by rwa [← hproj']
    suffices key : ∀ (nA nB : Nat) (piA piB : (compiledLinObs G).PureProfile)
        (ssA ssB : List (LinConfig G))
        (hA : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init nA piA ssA ≠ 0)
        (hB : pureRun (compiledLinObs G).pureStep (compiledLinObs G).init nB piB ssB ≠ 0)
        (hobsA : linObserve G i (ssA[ssA.length - 1]'(by
          have := pureRun_length _ _ nA piA ssA hA; omega)) = some (kLast, vLast))
        (hobsB : linObserve G i (ssB[ssB.length - 1]'(by
          have := pureRun_length _ _ nB piB ssB hB; omega)) = some (kLast, vLast))
        (hagree : ∀ j (hj : j + 1 < ssA.length),
          pii (linObserve G i (ssA[j]'(by omega))) =
            (piA i) (linObserve G i (ssA[j]'(by omega))))
        (j : Nat) (hj : j + 1 < ssB.length),
        pii (linObserve G i (ssB[j]'(by omega))) =
          (piB i) (linObserve G i (ssB[j]'(by omega))) by
      constructor
      · intro hup1
        have hagree1 : ∀ j (hj : j + 1 < ss1.length),
            pii (linObserve G i (ss1[j]'(by omega))) =
              (pi0 i) (linObserve G i (ss1[j]'(by omega))) :=
          fun j hj => pureRun_update_nonzero_agree G pi0 i pii n1 ss1 h1 hup1 j hj
        rw [pureRun_update_eq_of_obs_agree G pi0' i pii n2 ss2 h2
          (fun j hj => key n1 n2 pi0 pi0' ss1 ss2 h1 h2
            hobs_last1 hobs_last2 hagree1 j hj)]
        exact h2
      · intro hup2
        have hagree2 : ∀ j (hj : j + 1 < ss2.length),
            pii (linObserve G i (ss2[j]'(by omega))) =
              (pi0' i) (linObserve G i (ss2[j]'(by omega))) :=
          fun j hj => pureRun_update_nonzero_agree G pi0' i pii n2 ss2 h2 hup2 j hj
        rw [pureRun_update_eq_of_obs_agree G pi0 i pii n1 ss1 h1
          (fun j hj => key n2 n1 pi0' pi0 ss2 ss1 h2 h1
            hobs_last2 hobs_last1 hagree2 j hj)]
        exact h1
    -- Prove the key lemma
    intro nA nB piA piB ssA ssB hA hB hobsA hobsB hagree j hj
    match hobs : linObserve G i (ssB[j]'(by omega)) with
    | none => exact PUnit.ext _ _
    | some ⟨⟨r, hr⟩, v⟩ =>
      have hr_lt : r < kLast.val :=
        round_lt_of_earlier_step G piB nB ssB hB i kLast vLast hobsB j hj ⟨r, hr⟩ v hobs
      obtain ⟨hr', jA, hjA, v_match, hobsA_j, jB, hjB, hobsB_j, hact_eq⟩ :=
        fullRecall_view_action_match G hFR piA piB nA nB ssA ssB hA hB i kLast vLast
          hobsA hobsB r hr_lt
      have ⟨hjBeq, hveq⟩ := unique_i_step_position G piB nB ssB hB i kLast vLast hobsB
        jB j hjB hj ⟨r, hr'⟩ v_match v hobsB_j
        (by convert hobs using 2)
      subst hjBeq; subst hveq
      have hfin_eq : (⟨r, hr⟩ : Fin G.rounds.length) = ⟨r, hr'⟩ := Fin.ext rfl
      have h1' := hagree jA hjA
      rw [hobsA_j] at h1'
      have h2' := hact_eq (some (⟨r, hr'⟩, v_match)) rfl
      rw [show (some (⟨r, hr⟩, v_match) : Option (RoundView G)) =
        some (⟨r, hr'⟩, v_match) from by rw [hfin_eq]]
      rw [h1', h2']

/-- The linearized compiled model satisfies `NoNontrivialInfoStateRepeat`
unconditionally: along any reachable trace, no observation `some (k, v)`
appears at two distinct positions. This follows from the strict monotonicity
of the phase function along non-done traces. -/
theorem noNontrivialInfoStateRepeat_compiledLin :
    (compiledLinObs G).NoNontrivialInfoStateRepeat := by
  intro i π k ss hss j₁ j₂ hlt hj₂ hproj
  rw [ObsModelCore.runDistPure_eq_pureRun] at hss
  have hlen := pureRun_length _ _ k π ss hss
  -- For identity info state, projectStates (take) = linObserve at last element
  have hne₁ : ss.take (j₁ + 1) ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
  have hne₂ : ss.take (j₂ + 1) ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
  have hobs_eq₁ := projectStates_eq_lastObs G i (ss.take (j₁ + 1)) hne₁
  have hobs_eq₂ := projectStates_eq_lastObs G i (ss.take (j₂ + 1)) hne₂
  -- Simplify: last element of take (j+1) ss is ss[j]
  have htake_last₁ : (ss.take (j₁ + 1))[(ss.take (j₁ + 1)).length - 1]'(by
      simp; omega) = ss[j₁]'(by omega) := by
    have : (ss.take (j₁ + 1)).length - 1 = j₁ := by simp; omega
    simp only [this]; exact List.getElem_take
  have htake_last₂ : (ss.take (j₂ + 1))[(ss.take (j₂ + 1)).length - 1]'(by
      simp; omega) = ss[j₂]'(by omega) := by
    have : (ss.take (j₂ + 1)).length - 1 = j₂ := by simp; omega
    simp only [this]; exact List.getElem_take
  rw [htake_last₁] at hobs_eq₁
  rw [htake_last₂] at hobs_eq₂
  -- Now: projectStates i (take (j+1) ss) = linObserve G i ss[j]
  -- hproj gives equal projectStates → equal observations
  have hobseq : linObserve G i (ss[j₁]'(by omega)) =
      linObserve G i (ss[j₂]'(by omega)) := by
    rw [← hobs_eq₁, ← hobs_eq₂]; exact hproj
  -- The goal is about Act at currentObs (projectStates (take (j₂+1) ss))
  -- For identity: currentObs = id, so this is projectStates = linObserve at j₂
  -- For identity info state: currentObs = id, so goal reduces to
  -- Subsingleton (LinAct _ A (projectStates i (take (j₂+1) ss)))
  -- which equals linObserve G i ss[j₂] by hobs_eq₂
  change Subsingleton (LinAct (RoundView G) A
    ((compiledLinObs G).projectStates i (ss.take (j₂ + 1))))
  rw [hobs_eq₂]
  cases hobs₂ : linObserve G i (ss[j₂]'(by omega)) with
  | none => exact inferInstanceAs (Subsingleton PUnit)
  | some rv =>
    obtain ⟨r, v⟩ := rv
    rw [hobs₂] at hobseq
    have hp₁ := phase_of_linObserve_some G _ i r v hobseq
    have hp₂ := phase_of_linObserve_some G _ i r v hobs₂
    have hnd₂ := not_isDone_of_linObserve_some G _ i _ hobs₂
    have hphase_lt := phase_strict_mono_of_not_done G π k ss hss
      j₁ j₂ (by omega) (by omega) hlt hnd₂
    omega

end OLFBridge

-- ============================================================================
-- VRD agreement: lift ∘ descendVRD agrees with β at reachable observations
-- ============================================================================

section VRDAgreement

variable {G : Protocol n S V A Sig} [DecidableEq (Fin n)] [Fintype (Fin n)]
variable [Fintype A] [Nonempty A] [Nonempty (Fin G.rounds.length)]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- Under `ViewDeterminesRound`, the lifted VRD-descended profile agrees with `β` at all
info states visited during `runDist`. This provides the hypothesis for `runDist_congr`. -/
theorem liftBehavioralProfile_descendVRD_agree
    (hVRD : G.ViewDeterminesRound)
    (β : ObsModelCore.BehavioralProfile (compiledLinObs G))
    (m : Nat) (i : Fin n) (ss : List (LinConfig G))
    (_hss : ((compiledLinObs G).runDist m β) ss ≠ 0) :
    β i ((compiledLinObs G).projectStates i ss) =
      (liftBehavioralProfile (G := G) (descendBehavioralProfileVRD hVRD β)) i
        ((compiledLinObs G).projectStates i ss) := by
  -- For identity info states, projectStates i ss = observe i (lastState ss)
  set obs := (compiledLinObs G).projectStates i ss
  -- The key insight: projectStates is linObserve at the last state
  have hps : obs = linObserve G i ((compiledLinObs G).lastState ss) := by
    have h := ObsModelCore.currentObs_projectStates (compiledLinObs G) i ss
    simp only [ObsModelCore.currentObs, compileObsCoreModelLin] at h
    exact h
  cases hobs : obs with
  | none =>
    -- Both sides are PMF over PUnit (subsingleton action type at none)
    change β i none = liftBehavioralStrategy (descendBehavioralProfileVRD hVRD β i) none
    simp only [liftBehavioralStrategy]
    -- Goal: β i none = PMF.pure PUnit.unit
    ext ⟨⟩
    simp only [PMF.pure_apply, ite_true]
    have h : ∑' (a : PUnit), (β i none) a = 1 := (β i none).tsum_coe
    rwa [tsum_eq_single PUnit.unit
      (fun x hx => absurd (Subsingleton.elim x PUnit.unit) hx)] at h
  | some rv =>
    obtain ⟨k, v⟩ := rv
    -- linObserve at lastState = some (k, v)
    rw [hobs] at hps
    obtain ⟨s, sig, _, _, hview⟩ := linObserve_some_playerTurn G _ i (k, v) hps.symm
    -- viewRound hVRD i v = k by ViewDeterminesRound
    have hvr : viewRound hVRD i v = k :=
      viewRound_eq hVRD k s (sig i) i hview
    -- Both sides now reduce to β i (some (k, v))
    change β i (some (k, v)) =
      liftBehavioralStrategy (descendBehavioralProfileVRD hVRD β i) (some (k, v))
    simp only [liftBehavioralStrategy, descendBehavioralProfileVRD]
    rw [hvr]

end VRDAgreement

-- ============================================================================
-- Pure profile VRD descent (for B→M)
-- ============================================================================

section PureVRDDescent

variable [DecidableEq (Fin n)] [Fintype (Fin n)]
variable [Fintype A] [Nonempty A]
variable {G : Protocol n S V A Sig}

/-- Descend a compiled local strategy using `ViewDeterminesRound`: picks the
canonical round for each view via `viewRound`. -/
noncomputable def descendLocalStrategyVRD [Nonempty (Fin G.rounds.length)]
    (hVRD : G.ViewDeterminesRound)
    (π : (compiledLinObs G).LocalStrategy (i := i)) :
    PureStrategy V A :=
  fun v => π (some (viewRound hVRD i v, v))

/-- Descend a compiled pure profile using `ViewDeterminesRound`. -/
noncomputable def descendPureProfileVRD [Nonempty (Fin G.rounds.length)]
    (hVRD : G.ViewDeterminesRound)
    (π : (compiledLinObs G).PureProfile) :
    PureProfile n V A :=
  fun i => descendLocalStrategyVRD hVRD (π i)

/-- `liftPureProfile (descendPureProfileVRD hVRD π)` agrees with `π` at all
reachable info states under `pureToBehavioral`. -/
theorem liftPureProfile_descendVRD_agree
    [Nonempty (Fin G.rounds.length)]
    (hVRD : G.ViewDeterminesRound)
    (π : (compiledLinObs G).PureProfile)
    (m : Nat) (i : Fin n) (ss : List (LinConfig G))
    (_hss : ((compiledLinObs G).runDist m
      ((compiledLinObs G).pureToBehavioral π)) ss ≠ 0) :
    ((compiledLinObs G).pureToBehavioral π) i
      ((compiledLinObs G).projectStates i ss) =
    ((compiledLinObs G).pureToBehavioral
      (liftPureProfile (G := G) (descendPureProfileVRD hVRD π))) i
      ((compiledLinObs G).projectStates i ss) := by
  set obs := (compiledLinObs G).projectStates i ss
  cases hobs : obs with
  | none =>
    simp [ObsModelCore.pureToBehavioral]
    rfl
  | some rv =>
    obtain ⟨k, v⟩ := rv
    have hps : obs = linObserve G i ((compiledLinObs G).lastState ss) := by
      have h := ObsModelCore.currentObs_projectStates (compiledLinObs G) i ss
      simp only [ObsModelCore.currentObs, compileObsCoreModelLin] at h
      exact h
    rw [hobs] at hps
    obtain ⟨s, sig, _, _, hview⟩ := linObserve_some_playerTurn G _ i (k, v) hps.symm
    have hvr : viewRound hVRD i v = k := viewRound_eq hVRD k s (sig i) i hview
    simp only [ObsModelCore.pureToBehavioral]
    congr 1
    change π i (some (k, v)) =
      liftLocalStrategy (descendLocalStrategyVRD hVRD (π i)) (some (k, v))
    simp only [liftLocalStrategy, descendLocalStrategyVRD]; rw [hvr]

end PureVRDDescent

end GameTheory.Sequential
