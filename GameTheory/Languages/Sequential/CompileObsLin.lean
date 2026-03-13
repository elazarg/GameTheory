import GameTheory.Languages.Sequential.SOS
import GameTheory.Theorems.Kuhn.MixedToBehavioralCore

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
- `terminal s` — game over -/
inductive LinConfig (G : Protocol n S V A Sig) where
  | signal (round : Nat) (state : S)
  | playerTurn (round : Nat) (state : S) (sig : Fin n → Sig)
      (currentPlayer : Fin n) (accActs : Fin n → Option A)
  | terminal (state : S)

/-- Initial configuration for the linearized model. -/
def linInitialConfig (G : Protocol n S V A Sig) : LinConfig G :=
  if G.rounds[0]? = none then .terminal G.init else .signal 0 G.init

-- ============================================================================
-- Observations and actions
-- ============================================================================

/-- Player-local observation in the linearized model.
Only the currently acting player has a nontrivial observation. -/
def linObserve (G : Protocol n S V A Sig) [DecidableEq (Fin n)]
    (i : Fin n) : LinConfig G → Option V
  | .signal _ _ => none
  | .terminal _ => none
  | .playerTurn k s sig p _ =>
      if i = p then
        match G.rounds[k]? with
        | some r => some (r.view i s (sig i))
        | none => none
      else none

/-- Observation-dependent action type: nontrivial (`Option A`) when the player
is active (sees `some v`), trivial (`PUnit`) when inactive (sees `none`). -/
def LinAct (V A : Type) : Option V → Type
  | some _ => Option A
  | none => PUnit

instance linActFintype [Fintype A] : (o : Option V) → Fintype (LinAct V A o)
  | some _ => inferInstanceAs (Fintype (Option A))
  | none => inferInstanceAs (Fintype PUnit)

instance linActNonempty [Nonempty A] : (o : Option V) → Nonempty (LinAct V A o)
  | some _ => inferInstanceAs (Nonempty (Option A))
  | none => ⟨PUnit.unit⟩

-- ============================================================================
-- Linearized step function
-- ============================================================================

/-- Advance to the next sub-phase after player `p` acts. If `p` is the last
player, apply the transition and advance to the next round (or terminal). -/
private noncomputable def advancePlayerTurn (G : Protocol n S V A Sig)
    (k : Nat) (s : S) (sig : Fin n → Sig) (p : Fin n) (accActs : Fin n → Option A)
    (r : Round n S V A Sig) : PMF (LinConfig G) :=
  if h : p.val + 1 < n then
    PMF.pure (.playerTurn k s sig ⟨p.val + 1, h⟩ accActs)
  else
    let next := r.transition s accActs
    match G.rounds[k + 1]? with
    | some _ => PMF.pure (.signal (k + 1) next)
    | none => PMF.pure (.terminal next)

/-- Extract the effective `Option A` action for the acting player from a
dependent action tuple at a `playerTurn` configuration. The `cast` resolves
the dependent type `LinAct V A (linObserve G p cfg)` to `Option A`. -/
private def extractPlayerAction [DecidableEq (Fin n)] (G : Protocol n S V A Sig)
    (k : Nat) (s : S) (sig : Fin n → Sig) (p : Fin n) (accActs : Fin n → Option A)
    (acts : (i : Fin n) → LinAct V A (linObserve G i (.playerTurn k s sig p accActs)))
    : Option A :=
  match hr : G.rounds[k]? with
  | some r =>
      have hobs : linObserve G p (.playerTurn k s sig p accActs) =
          some (r.view p s (sig p)) := by simp [linObserve, hr]
      cast (congrArg (LinAct V A) hobs) (acts p)
  | none =>
      -- linObserve G p ... = none in this case, so acts p : PUnit → use none
      none

/-- Per-player step function for the linearized model.

- **Signal phase**: sample signal, start player 0's turn with default actions.
- **Player turn**: read the acting player's action, store it, advance to next
  player or apply transition.
- **Terminal**: absorbing. -/
noncomputable def linConfigStepPMF [DecidableEq (Fin n)] (G : Protocol n S V A Sig)
    (cfg : LinConfig G)
    (acts : (i : Fin n) → LinAct V A (linObserve G i cfg)) :
    PMF (LinConfig G) :=
  match cfg with
  | .signal k s =>
      match hr : G.rounds[k]? with
      | some r =>
          if hn : 0 < n then
            (r.signal s).map fun sig =>
              .playerTurn k s sig ⟨0, hn⟩ (fun _ => none)
          else
            -- n = 0: no players, apply transition with empty action vector
            (r.signal s).bind fun sig =>
              let next := r.transition s (fun i => absurd i.pos hn)
              match G.rounds[k + 1]? with
              | some _ => PMF.pure (.signal (k + 1) next)
              | none => PMF.pure (.terminal next)
      | none => PMF.pure (.signal k s)
  | .playerTurn k s sig p accActs =>
      match G.rounds[k]? with
      | some r =>
          let accActs' := Function.update accActs p
              (extractPlayerAction G k s sig p accActs acts)
          advancePlayerTurn G k s sig p accActs' r
      | none => PMF.pure (.playerTurn k s sig p accActs)
  | .terminal s => PMF.pure (.terminal s)

-- ============================================================================
-- Compilation to ObsModelCore
-- ============================================================================

/-- Compile a sequential protocol into an `ObsModelCore` with per-player
action sub-phases. At each step, at most one player has a nontrivial action.

- **States**: `LinConfig G` (extended configurations with per-player turns)
- **Players**: `Fin n`
- **Observations**: `Option V` (nontrivial only for the acting player)
- **Actions**: `LinAct V A` (nontrivial only when active)
- **InfoState**: identity — observation = info state -/
noncomputable def compileObsCoreModelLin [DecidableEq (Fin n)]
    (G : Protocol n S V A Sig) :
    ObsModelCore (Fin n) (LinConfig G)
      (fun _ => Option V)
      (fun _ => LinAct V A) where
  infoState := fun _ => {
    Carrier := Option V
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
  · split
    · simp_all [PMF.pure_apply]
    · simp_all [PMF.pure_apply]

omit [DecidableEq (Fin n)] [Fintype (Fin n)] [Fintype A] [Nonempty A] in
/-- `linConfigStepPMF` is mass-invariant: if two action vectors both assign
nonzero probability to the same successor, the step probabilities are equal.

- **Signal**: step ignores actions (samples from signal distribution)
- **PlayerTurn**: `advancePlayerTurn` is `PMF.pure`; equal at `t` by purity
- **Terminal**: absorbing, action-independent -/
private theorem linConfigStepPMF_mass_invariant (G : Protocol n S V A Sig)
    [DecidableEq (Fin n)]
    (cfg : LinConfig G)
    (acts₁ acts₂ : (i : Fin n) → LinAct V A (linObserve G i cfg))
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
    (acts₁ acts₂ : (i : Fin n) → LinAct V A (linObserve G i (.playerTurn k s sig p accActs)))
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
    (acts₁ acts₂ : (i : Fin n) → LinAct V A (linObserve G i (.playerTurn k s sig p accActs)))
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
    (a₁ a₂ : LinAct V A (linObserve G i (.playerTurn k s sig p accActs))) :
    a₁ = a₂ := by
  have hobs : linObserve G i (.playerTurn k s sig p accActs) = none := by
    simp [linObserve, hi]
  have hsub : Subsingleton (LinAct V A (linObserve G i (.playerTurn k s sig p accActs))) := by
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
    | playerTurn k s sig p accActs =>
        have hp := hall p
        suffices heq : (compiledLinObs G).pureStep π ss =
            (compiledLinObs G).pureStep (Function.update π₀ p (π p)) ss from heq ▸ hp
        exact pureStep_congr_compiledLin G _ _ ss _ hlast (fun j => by
          by_cases hjp : j = p
          · subst hjp; exact (congrFun (Function.update_self j (π j) π₀) _).symm
          · exact (linAct_eq_punit_of_ne (accActs := accActs) hjp _ _).symm)

end Properties

-- ============================================================================
-- Profile lift / descend
-- ============================================================================

section Profiles

variable {G : Protocol n S V A Sig} [DecidableEq (Fin n)]

/-- Lift a protocol-level pure strategy to a compiled local strategy.
At `some v` (active), uses the strategy's action; at `none` (inactive), uses
the unique `PUnit` action. -/
def liftLocalStrategy (σ : PureStrategy V A) :
    (compiledLinObs G).LocalStrategy (i := i) :=
  fun obs =>
    match obs with
    | some v => (σ v : LinAct V A (some v))
    | none => (PUnit.unit : LinAct V A none)

/-- Lift a protocol-level pure profile to a compiled pure profile. -/
def liftPureProfile (σ : PureProfile n V A) :
    (compiledLinObs G).PureProfile :=
  fun i => liftLocalStrategy (i := i) (σ i)

/-- Descend a compiled local strategy to a protocol-level pure strategy.
Extracts the action at `some v` observations. -/
def descendLocalStrategy (π : (compiledLinObs G).LocalStrategy (i := i)) :
    PureStrategy V A :=
  fun v => π (some v)

/-- Descend a compiled pure profile to a protocol-level pure profile. -/
def descendPureProfile (π : (compiledLinObs G).PureProfile) :
    PureProfile n V A :=
  fun i => descendLocalStrategy (π i)

/-- Lift then descend is the identity on pure strategies. -/
@[simp]
theorem descendLocalStrategy_liftLocalStrategy (σ : PureStrategy V A) :
    descendLocalStrategy (G := G) (i := i) (liftLocalStrategy σ) = σ := by
  ext v; simp [descendLocalStrategy, liftLocalStrategy]

/-- Descend then lift agrees with the original on all observations. -/
@[simp]
theorem liftLocalStrategy_descendLocalStrategy
    (π : (compiledLinObs G).LocalStrategy (i := i)) :
    liftLocalStrategy (G := G) (descendLocalStrategy π) = π := by
  funext obs
  match obs with
  | some v => simp [liftLocalStrategy, descendLocalStrategy]
  | none => exact PUnit.ext _ _

/-- Lift then descend is the identity on pure profiles. -/
@[simp]
theorem descendPureProfile_liftPureProfile (σ : PureProfile n V A) :
    descendPureProfile (G := G) (liftPureProfile σ) = σ := by
  ext i v; simp [descendPureProfile, liftPureProfile, descendLocalStrategy, liftLocalStrategy]

/-- Descend then lift is the identity on compiled pure profiles. -/
@[simp]
theorem liftPureProfile_descendPureProfile (π : (compiledLinObs G).PureProfile) :
    liftPureProfile (G := G) (descendPureProfile π) = π := by
  funext i obs
  simp only [liftPureProfile, descendPureProfile, liftLocalStrategy, descendLocalStrategy]
  match obs with
  | some _ => rfl
  | none => exact PUnit.ext _ _

end Profiles

-- ============================================================================
-- Adequacy: linearized execution matches protocol evaluation
-- ============================================================================

section Adequacy

variable {G : Protocol n S V A Sig} [DecidableEq (Fin n)]

/-- The final state of a `LinConfig`. For `terminal s`, this is `s`.
For non-terminal configurations, this is the current state carried
by the configuration (evaluation not yet complete). -/
def LinConfig.state : LinConfig G → S
  | .signal _ s => s
  | .playerTurn _ s _ _ _ => s
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

/-- **Adequacy (pure profiles)**: running the linearized compiled model with
`liftPureProfile σ` for enough steps, and extracting the terminal state, gives
the same distribution as `Protocol.eval G σ`.

The key argument is that the linearized model's step function resolves one player
at a time, and for pure memoryless strategies the order of resolution doesn't
matter — the final accumulated action vector is the same. So the linearized
execution matches `evalLinearized`, which equals `Protocol.eval`. -/
theorem runDistPure_eq_eval (G : Protocol n S V A Sig) [Fintype (Fin n)] [Fintype A]
    (σ : PureProfile n V A) (k : Nat) (hk : k ≥ G.rounds.length * (n + 1)) :
    ((compiledLinObs G).runDistPure k (liftPureProfile σ)).bind
        (fun ss => PMF.pure ((compiledLinObs G).lastState ss).state) =
      G.eval σ := by
  sorry

end Adequacy

end GameTheory.Sequential
