import GameTheory.Languages.MultiRound.SOS
import GameTheory.Theorems.Kuhn.MixedToBehavioralCore
import Mathlib.Data.List.TakeDrop

/-!
# Linearized Compilation of MultiRound Protocols to ObsModelCore

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

namespace GameTheory.MultiRound

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
inductive LinConfig (G : MultiRoundGame n S V A Sig) where
  | signal (round : Nat) (state : S)
  | playerTurn (round : Nat) (state : S) (sig : Fin n → Sig)
      (currentPlayer : Fin n) (accActs : Fin n → Option A)
  | applyTransition (round : Nat) (state : S) (sig : Fin n → Sig)
      (accActs : Fin n → Option A)
  | terminal (state : S)

/-- Initial configuration for the linearized model. -/
def linInitialConfig (G : MultiRoundGame n S V A Sig) : LinConfig G :=
  if G.rounds[0]? = none then .terminal G.init else .signal 0 G.init

-- ============================================================================
-- Observations and actions
-- ============================================================================

/-- Round-indexed observation type. Includes the round number to distinguish
the same view at different rounds, which is essential for `ObsLocalFeasibility`
(ensures OLF only compares traces at the same round, where FullRecall applies). -/
abbrev RoundView (G : MultiRoundGame n S V A Sig) := Fin G.rounds.length × V

/-- Player-local observation in the linearized model.
Only the currently acting player has a nontrivial observation, which includes
the round number. -/
def linObserve (G : MultiRoundGame n S V A Sig) [DecidableEq (Fin n)]
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
noncomputable def advancePlayerTurn (G : MultiRoundGame n S V A Sig)
    (k : Nat) (s : S) (sig : Fin n → Sig) (p : Fin n) (accActs : Fin n → Option A)
    (_r : Round n S V A Sig) : PMF (LinConfig G) :=
  if h : p.val + 1 < n then
    PMF.pure (.playerTurn k s sig ⟨p.val + 1, h⟩ accActs)
  else
    PMF.pure (.applyTransition k s sig accActs)

/-- Extract the effective `Option A` action for the acting player from a
dependent action tuple at a `playerTurn` configuration. The `cast` resolves
the dependent type to `Option A`. -/
def extractPlayerAction [DecidableEq (Fin n)] (G : MultiRoundGame n S V A Sig)
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
noncomputable def linConfigStepPMF [DecidableEq (Fin n)] (G : MultiRoundGame n S V A Sig)
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
    (G : MultiRoundGame n S V A Sig) :
    ObsModelCore (Fin n) (LinConfig G)
      (fun _ => Option (RoundView G))
      (fun _ => LinAct (RoundView G) A) where
  infoState := fun _ => InfoStateCore.identity _
  observe := linObserve G
  machine := {
    init := linInitialConfig G
    step := linConfigStepPMF G
  }

/-- Abbreviation for the linearized compiled model. -/
noncomputable abbrev compiledLinObs [DecidableEq (Fin n)]
    (G : MultiRoundGame n S V A Sig) :=
  compileObsCoreModelLin G

-- ============================================================================
-- Fintype instances for the compiled model
-- ============================================================================

noncomputable instance compiledLinObs_infoState_fintype [DecidableEq (Fin n)]
    [Fintype V] (G : MultiRoundGame n S V A Sig) (i : Fin n) :
    Fintype ((compiledLinObs G).InfoState i) :=
  inferInstanceAs (Fintype (Option (Fin G.rounds.length × V)))

noncomputable instance compiledLinObs_infoState_decidableEq [DecidableEq (Fin n)]
    [DecidableEq V] (G : MultiRoundGame n S V A Sig) (i : Fin n) :
    DecidableEq ((compiledLinObs G).InfoState i) :=
  inferInstanceAs (DecidableEq (Option (Fin G.rounds.length × V)))

noncomputable instance compiledLinObs_localStrategy_fintype [DecidableEq (Fin n)]
    [DecidableEq V] [Fintype V] [Fintype A] (G : MultiRoundGame n S V A Sig) (i : Fin n) :
    Fintype ((compiledLinObs G).LocalStrategy i) :=
  Pi.instFintype

-- ============================================================================
-- Structural properties
-- ============================================================================

section Properties

/-- At every playerTurn state, only the acting player has a nontrivial
observation — all others see `none`. -/
theorem linObserve_ne_acting [DecidableEq (Fin n)] {G : MultiRoundGame n S V A Sig}
    {k : Nat} {s : S} {sig : Fin n → Sig} {p : Fin n}
    {accActs : Fin n → Option A} {i : Fin n} (hi : i ≠ p) :
    linObserve G i (.playerTurn k s sig p accActs) = none := by
  simp [linObserve, hi]

theorem pure_ne_zero_iff' {α : Type*} (a b : α) :
    (PMF.pure a) b ≠ 0 ↔ b = a := by
  rw [ne_eq, PMF.pure_apply]
  constructor
  · intro h; by_contra hne; exact h (if_neg hne)
  · intro h; subst h; simp

private theorem advancePlayerTurn_mass_invariant (G : MultiRoundGame n S V A Sig)
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

/-- If two `accActs` both give nonzero probability at the same target through
`advancePlayerTurn`, then the `accActs` must be equal (since the step is `PMF.pure`). -/
private theorem advancePlayerTurn_accActs_eq (G : MultiRoundGame n S V A Sig)
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

/-- `linConfigStepPMF` is mass-invariant: if two action vectors both assign
nonzero probability to the same successor, the step probabilities are equal.

- **Signal**: step ignores actions (samples from signal distribution)
- **PlayerTurn**: `advancePlayerTurn` is `PMF.pure`; equal at `t` by purity
- **Terminal**: absorbing, action-independent -/
private theorem linConfigStepPMF_mass_invariant (G : MultiRoundGame n S V A Sig)
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

/-- The linearized model satisfies `StepMassInvariant`.
Signal phases ignore actions entirely. PlayerTurn phases are deterministic
(the step is `PMF.pure` of a single successor). Terminal is absorbing. -/
theorem stepMassInvariant_compiledLin [DecidableEq (Fin n)] [Fintype (Fin n)] [Fintype A]
    (G : MultiRoundGame n S V A Sig) :
    ObsModelCore.StepMassInvariant (compiledLinObs G) := by
  intro ss t π₁ π₂ h₁ h₂
  have eq₁ := ObsModelCore.pureStep_eq π₁ ss
  have eq₂ := ObsModelCore.pureStep_eq π₂ ss
  rw [eq₁] at h₁ ⊢; rw [eq₂] at h₂ ⊢
  change linConfigStepPMF G _ _ t = linConfigStepPMF G _ _ t
  exact linConfigStepPMF_mass_invariant G _ _ _ t h₁ h₂

private theorem extractPlayerAction_congr
    (G : MultiRoundGame n S V A Sig)
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

private theorem linConfigStepPMF_playerTurn_congr
    (G : MultiRoundGame n S V A Sig)
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

private theorem linAct_eq_punit_of_ne [DecidableEq (Fin n)]
    {G : MultiRoundGame n S V A Sig}
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

/-- Closed form of pure one-step execution in the linearized compilation.
Eliminates all dependent-type casts from `pureStep_eq`. -/
theorem pureStep_compiledLin_eq [DecidableEq (Fin n)] [Fintype (Fin n)] [Fintype A]
    (G : MultiRoundGame n S V A Sig)
    (π : (compiledLinObs G).PureProfile) (ss : List (LinConfig G)) :
    (compiledLinObs G).pureStep π ss =
      linConfigStepPMF G ((compiledLinObs G).lastState ss)
        (fun i => π i (linObserve G i ((compiledLinObs G).lastState ss))) := by
  rw [ObsModelCore.pureStep_eq]
  congr 1
  funext i
  exact cast_dep_apply (π i) ((compiledLinObs G).currentObs_projectStates i ss)

/-- Two profiles producing the same observation-dependent actions at a given
configuration have equal pure steps. Takes the last state as a parameter
to avoid matching issues with `lastState ss`. -/
private theorem pureStep_congr_compiledLin [DecidableEq (Fin n)] [Fintype (Fin n)] [Fintype A]
    (G : MultiRoundGame n S V A Sig)
    (π₁ π₂ : (compiledLinObs G).PureProfile) (ss : List (LinConfig G))
    (cfg : LinConfig G) (hlast : (compiledLinObs G).lastState ss = cfg)
    (h : ∀ i, π₁ i (linObserve G i cfg) = π₂ i (linObserve G i cfg)) :
    (compiledLinObs G).pureStep π₁ ss = (compiledLinObs G).pureStep π₂ ss := by
  rw [pureStep_compiledLin_eq, pureStep_compiledLin_eq, hlast]
  exact congrArg (linConfigStepPMF G cfg) (funext h)

/-- The linearized model satisfies `StepSupportFactorization`.
At each step, at most one player has a nontrivial action (the acting player
at a `playerTurn` phase). Changing any other player's strategy does not
affect the step, so the per-player update condition holds trivially. -/
theorem stepSupportFactorization_compiledLin [DecidableEq (Fin n)] [Fintype (Fin n)] [Fintype A]
    (G : MultiRoundGame n S V A Sig) :
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

/-- Index into `l.concat a` at position `j < l.length` equals `l[j]`. -/
private theorem getElem_concat_left {α : Type*} (l : List α) (a : α)
    (j : Nat) (hj : j < l.length) {h : j < (l.concat a).length} :
    (l.concat a)[j] = l[j] := by
  simp [List.getElem_append_left hj]

open Math.ParameterizedChain in
/-- Under the linearized model, if `πᵢ` agrees with `(π i)` at every intermediate
observation along the trace, then `pureRun` under the player-i update equals the
original `pureRun`. -/
theorem pureRun_update_eq_of_obs_agree [DecidableEq (Fin n)] [Fintype (Fin n)] [Fintype A]
    (G : MultiRoundGame n S V A Sig)
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

theorem lastState_take_eq_getElem
    [DecidableEq (Fin n)] {G : MultiRoundGame n S V A Sig}
    (ss : List (LinConfig G)) (j : Nat) (hj : j + 1 < ss.length) :
    (compiledLinObs G).lastState (ss.take (j + 1)) = ss[j] := by
  simp [ObsModelCore.lastState, List.getLast?_eq_getElem?,
    List.length_take_of_le (by omega : j + 1 ≤ ss.length),
    show j + 1 - 1 = j from by omega, Option.getD_some]

open Math.ParameterizedChain in
/-- Converse: if `pureRun` is nonzero under both the original profile and a
player-i update, then `πᵢ` must agree with `(π i)` at all observations along
the trace. At non-i steps this is trivial (PUnit). At i-steps, the step is
deterministic and injective in the action, so both hitting the same target forces
the actions to agree. -/
theorem pureRun_update_nonzero_agree [DecidableEq (Fin n)] [Fintype (Fin n)] [Fintype A]
    (G : MultiRoundGame n S V A Sig)
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

section ViewRound

variable {G : MultiRoundGame n S V A Sig}

open Classical in
/-- The unique round for a view under `ViewDeterminesRound`. -/
noncomputable def viewRound [Nonempty (Fin G.rounds.length)]
    (_hVRD : G.ViewDeterminesRound) (i : Fin n) (v : V) :
    Fin G.rounds.length :=
  if h : ∃ (k : Fin G.rounds.length) (s : S) (sig : Sig),
    G.rounds[k].view i s sig = v
  then h.choose
  else Classical.arbitrary _

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

end ViewRound

section Profiles

variable {G : MultiRoundGame n S V A Sig} [DecidableEq (Fin n)]

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

end GameTheory.MultiRound
