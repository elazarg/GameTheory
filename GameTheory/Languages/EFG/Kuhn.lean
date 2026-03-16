import Math.PMFProduct
import GameTheory.Languages.EFG.CompileObs
import GameTheory.Theorems.Kuhn

/-!
# Kuhn's Theorem for EFG — via ObsModelCore

Kuhn's theorem (behavioral ↔ mixed strategy equivalence) for extensive-form
games, derived as a corollary of the generic Kuhn development on
`ObsModelCore`.

## Architecture

The EFG game tree compiles to an `ObsModelCore` via `compileObsCoreModel` (in
`CompileObs.lean`). Kuhn's theorem is proved generically on `ObsModelCore`
(in `Theorems/Kuhn/`). This file:

1. Provides EFG-native definitions used downstream (`FlatProfile`,
   `productProfile`, `flatToBehavioral`, etc.)
2. Builds the EFG-specific `ObsModelCore` bridge
3. Transports the generic Kuhn result to tree-level `evalDist` statements

## Main results

- `kuhn_behavioral_to_mixed` : B→M at tree level
- `kuhn_mixed_to_behavioral` : M→B at tree level via `ObsModelCore`
-/

namespace EFG

open GameTheory Math.PMFProduct

variable {S : InfoStructure} {Outcome : Type}

-- ============================================================================
-- Type aliases and instances
-- ============================================================================

/-- Flat index over all infosets across all players. -/
abbrev FlatIdx (S : InfoStructure) := (p : Fin S.n) × S.Infoset p

/-- A flat profile assigns an action to every infoset of every player. -/
abbrev FlatProfile (S : InfoStructure) := (idx : FlatIdx S) → S.Act idx.2

-- ============================================================================
-- Product PMF and flat-to-behavioral conversion
-- ============================================================================

/-- Product PMF: independently sample each info set from a behavioral profile.
    Uses `pmfPi`: assigns weight `∏ idx, σ idx.1 idx.2 (s idx)` to profile `s`. -/
noncomputable def productProfile (σ : BehavioralProfile S) : PMF (FlatProfile S) :=
  pmfPi (fun idx => σ idx.1 idx.2)

@[simp] theorem productProfile_apply (σ : BehavioralProfile S) (s : FlatProfile S) :
    (productProfile σ) s = ∏ idx : FlatIdx S, σ idx.1 idx.2 (s idx) := by
  simp [productProfile]

/-- Evaluate a flat profile as a behavioral profile (point mass at each infoset). -/
noncomputable def flatToBehavioral (s : FlatProfile S) : BehavioralProfile S :=
  fun p I => PMF.pure (s ⟨p, I⟩)

/-- Equivalence between flat profiles and pure profiles. -/
def flatProfileEquivPureProfile : Equiv (FlatProfile S) (PureProfile S) where
  toFun := fun s p I => s ⟨p, I⟩
  invFun := fun pi idx => pi idx.1 idx.2
  left_inv := by intro s; funext idx; cases idx; rfl
  right_inv := by intro pi; funext p I; rfl

instance (p : S.Player) : DecidableEq (PureStrategy S p) :=
  show DecidableEq ((I : S.Infoset p) → S.Act I) from inferInstance

instance : DecidableEq (PureProfile S) :=
  show DecidableEq ((p : S.Player) → PureStrategy S p) from
    Fintype.decidablePiFintype

/-- Joint distribution over pure profiles from a mixed (per-player) profile. -/
noncomputable abbrev mixedProfileJoint (muP : MixedProfile S) : PMF (PureProfile S) :=
  pmfPi (A := fun p => PureStrategy S p) muP

-- ============================================================================
-- NoInfoSetRepeat
-- ============================================================================

/-- No info set appears both at a decision node and in its subtrees.
    This ensures the product PMF factorizes correctly at decision nodes.
    Follows from `PerfectRecall` (proved below). -/
def NoInfoSetRepeat : GameTree S Outcome → Prop
  | .terminal _ => True
  | .chance _k _μ _hk next => ∀ b, NoInfoSetRepeat (next b)
  | .decision (p := _p) I next =>
      (∀ a, ¬ DecisionNodeIn I (next a)) ∧ (∀ a, NoInfoSetRepeat (next a))

/-- Every `DecisionNodeIn` witness yields a `ReachBy` path. -/
theorem DecisionNodeIn_to_ReachBy {p : S.Player} {I : S.Infoset p} {t : GameTree S Outcome}
    (h : DecisionNodeIn I t) :
    ∃ (hist : List (HistoryStep S)) (next : S.Act I → GameTree S Outcome),
      ReachBy hist t (.decision I next) := by
  induction h with
  | root next => exact ⟨[], next, .here _⟩
  | in_chance k μ hk f b _ ih =>
    obtain ⟨hist, next, hr⟩ := ih
    exact ⟨.chance k b :: hist, next, .chance b hr⟩
  | in_decision I' f a _ ih =>
    obtain ⟨hist, next, hr⟩ := ih
    exact ⟨.action _ I' a :: hist, next, .action a hr⟩

/-- Perfect recall implies no info set repeats on paths. -/
theorem PerfectRecall_implies_NoInfoSetRepeat
    (t : GameTree S Outcome) (hpr : PerfectRecall t) : NoInfoSetRepeat t := by
  induction t with
  | terminal _ => trivial
  | chance _k _μ _hk next ih =>
    intro b
    apply ih b
    intro h₁ h₂ p I next₁ next₂ hr₁ hr₂
    have := hpr (.chance _ b :: h₁) (.chance _ b :: h₂) I next₁ next₂
      (.chance b hr₁) (.chance b hr₂)
    simpa [playerHistory] using this
  | decision I next ih =>
    refine ⟨fun a hmem => ?_, fun a => ?_⟩
    · obtain ⟨hist, next₂, hr₂⟩ := DecisionNodeIn_to_ReachBy hmem
      have key := hpr [] (.action _ I a :: hist) I next next₂
        (.here _) (.action a hr₂)
      simp [playerHistory] at key
    · apply ih a
      intro h₁ h₂ q J next₁ next₂ hr₁ hr₂
      have key := hpr (.action _ I a :: h₁) (.action _ I a :: h₂) J next₁ next₂
        (.action a hr₁) (.action a hr₂)
      simp only [playerHistory] at key
      split at key <;> simp_all

/-- The honest core compilation for an EFG tree. -/
noncomputable abbrev compiledCoreObs (t : GameTree S Outcome) :=
  GameTheory.EFG.compileObsCoreModel t

-- ============================================================================
-- ObsModelCore bridge for EFG
-- ============================================================================

section ObsModelCoreBridge

open GameTheory.EFG
open Math.PMFProduct

variable (t : GameTree S Outcome)

noncomputable instance compiledCoreInfoStateFintype (t : GameTree S Outcome) (i : S.Player) :
    Fintype ((compiledCoreObs t).InfoState i) := by
  dsimp [compiledCoreObs, compileObsCoreModel, ObsModelCore.InfoState, InfoStateCore.identity]
  infer_instance

@[simp] theorem projectStates_compiledCore
    (i : S.Player) (ss : List (GameTree S Outcome)) :
    (compiledCoreObs t).projectStates i ss =
      obsOfState i
        ((compiledCoreObs t).lastState ss) := by
  induction ss with
  | nil =>
      simp [ObsModelCore.projectStates, ObsModelCore.projectStatesFrom, ObsModelCore.lastState,
        compiledCoreObs, compileObsCoreModel, InfoStateCore.identity, obsOfState]
  | cons s ss ih =>
      cases ss with
      | nil =>
          simp [ObsModelCore.projectStates, ObsModelCore.projectStatesFrom, ObsModelCore.lastState,
            compiledCoreObs, compileObsCoreModel, InfoStateCore.identity, obsOfState]
      | cons t ts =>
          simpa [ObsModelCore.projectStates, ObsModelCore.projectStatesFrom, ObsModelCore.lastState,
            compiledCoreObs, compileObsCoreModel, InfoStateCore.identity, obsOfState] using ih

/-- Product mixed distribution over lifted core local strategies is the
pushforward of the native mixed-profile joint law along `liftPureProfileCore`. -/
theorem liftMixedProfileCore_joint
    (μ : MixedProfile S) :
    pmfPi (liftMixedProfileCore t μ) =
      Math.ProbabilityMassFunction.pushforward (mixedProfileJoint μ)
        (liftPureProfileCore t) := by
  classical
  rw [mixedProfileJoint]
  exact (Math.PMFProduct.pmfPi_push_coordwise μ
    (fun i => pureStrategyEquivCoreLocalStrategy t i)).symm

/-- Closed form of one compiled-core step at an explicit tree state. -/
private theorem compiledCore_step_eq
    (s : GameTree S Outcome)
    (a : (compiledCoreObs t).JointActionAt s) :
    (compiledCoreObs t).step s a =
      match s with
      | .terminal z => PMF.pure (.terminal z)
      | .chance _k μ _hk next => μ.map next
      | .decision (p := p) I next =>
          PMF.pure
            (next
              (cast
                (compiledAct_eq_of_some S p
                  (show obsOfState p (.decision I next) = some I by
                    simp [obsOfState]))
                (a p))) := by
  cases s with
  | terminal z => rfl
  | chance k μ hk next => rfl
  | decision I next => rfl

@[simp] private theorem obsOfState_decision_eq_some
    {p : S.Player} (I : S.Infoset p) (next : S.Act I → GameTree S Outcome) :
    obsOfState p (.decision I next) = some I := by
  simp [obsOfState]

private theorem compiledCore_step_of_decision
    {s : GameTree S Outcome}
    {p : S.Player} (I : S.Infoset p)
    (next : S.Act I → GameTree S Outcome)
    (hs : s = .decision I next)
    (a : (compiledCoreObs t).JointActionAt s) :
    (compiledCoreObs t).step s a =
      PMF.pure
        (next
          (cast
            (compiledAct_eq_of_some S p
              (obsOfState_decision_eq_some I next))
            (hs ▸ a p))) := by
  cases hs
  simp [ObsModelCore.step, compileObsCoreModel, InfoStateCore.identity, treeStepPMF, obsOfState]

private theorem compiledCore_step_of_terminal
    {s : GameTree S Outcome} {z : Outcome}
    (hs : s = .terminal z)
    (a : (compiledCoreObs t).JointActionAt s) :
    (compiledCoreObs t).step s a = PMF.pure (.terminal z) := by
  cases hs
  simp [compiledCore_step_eq]

private theorem compiledCore_step_of_chance
    {s : GameTree S Outcome}
    {k : Nat} {μ : PMF (Fin k)} {hk : 0 < k}
    (next : Fin k → GameTree S Outcome)
    (hs : s = .chance k μ hk next)
    (a : (compiledCoreObs t).JointActionAt s) :
    (compiledCoreObs t).step s a = μ.map next := by
  cases hs
  simp [compiledCore_step_eq]

/-- In the honest core compilation, projecting a pure profile action to the
current step just evaluates it at the current observation cell. -/
@[simp] theorem castProfileAction_compiledCore
    (π : ObsModelCore.PureProfile (compiledCoreObs t))
    (i : S.Player) (ss : List (GameTree S Outcome)) :
    (compiledCoreObs t).castProfileAction i ss
      (π i ((compiledCoreObs t).projectStates i ss)) =
        π i (obsOfState i
          ((compiledCoreObs t).lastState ss)) := by
  induction ss with
  | nil =>
      simp [ObsModelCore.castProfileAction, ObsModelCore.projectStates,
        ObsModelCore.projectStatesFrom, ObsModelCore.lastState,
        compileObsCoreModel, InfoStateCore.identity, obsOfState]
  | cons s ss ih =>
      cases ss with
      | nil =>
          simp [ObsModelCore.castProfileAction, ObsModelCore.projectStates,
            ObsModelCore.projectStatesFrom, ObsModelCore.lastState,
            compileObsCoreModel, InfoStateCore.identity, obsOfState]
      | cons t ts =>
          simpa [ObsModelCore.castProfileAction, ObsModelCore.projectStates,
            ObsModelCore.projectStatesFrom, ObsModelCore.lastState,
            compileObsCoreModel, InfoStateCore.identity, obsOfState] using ih

@[simp] theorem castJointAction_compiledCore
    (π : ObsModelCore.PureProfile (compiledCoreObs t))
    (ss : List (GameTree S Outcome)) :
    (compiledCoreObs t).castJointAction ss
      (fun i => π i ((compiledCoreObs t).projectStates i ss)) =
        (fun i =>
          π i (obsOfState i
            ((compiledCoreObs t).lastState ss))) := by
  funext i
  exact castProfileAction_compiledCore t π i ss

/-- Closed form of pure one-step execution in the honest core compilation. -/
theorem pureStep_compiledCore_eq
    (π : ObsModelCore.PureProfile (compiledCoreObs t))
    (ss : List (GameTree S Outcome)) :
    (compiledCoreObs t).pureStep π ss =
      match (compiledCoreObs t).lastState ss with
      | .terminal z => PMF.pure (.terminal z)
      | .chance _k μ _hk next => μ.map next
      | .decision (p := p) I next => PMF.pure (next (π p (some I))) := by
  let O := compiledCoreObs t
  rw [ObsModelCore.pureStep_eq]
  have hcast :
      (fun i =>
        O.currentObs_projectStates i ss ▸ π i (O.projectStates i ss)) =
        (fun i => O.castProfileAction i ss (π i (O.projectStates i ss))) := by
    rfl
  rw [hcast]
  have hact :
      (fun i => O.castProfileAction i ss (π i (O.projectStates i ss))) =
        (fun i => π i (obsOfState i (O.lastState ss))) := by
    funext i
    exact castProfileAction_compiledCore t π i ss
  rw [hact]
  have hstep :=
    compiledCore_step_eq t
      (O.lastState ss)
      (fun i => π i (obsOfState i (O.lastState ss)))
  cases hlast : O.lastState ss with
  | terminal z =>
      simp [compiledCore_step_eq, obsOfState]
  | chance k μ hk next =>
      simp [compiledCore_step_eq, obsOfState]
  | @decision p I next =>
      simp only [obsOfState, compiledCore_step_eq, dite_eq_ite]
      have hcast' :
          cast
            (compiledAct_eq_of_some S p
              (obsOfState_decision_eq_some I next))
            (π p (if p = p then some I else none)) =
          π p (some I) := by
        grind
      exact congrArg PMF.pure (congrArg next hcast')

/-- Closed form of behavioral one-step execution in the honest core compilation. -/
private theorem stepDist_compiledCore_eq_terminal
    (σ : BehavioralProfile S) (ss : List (GameTree S Outcome))
    {z : Outcome}
    (hs : (compiledCoreObs t).lastState ss = .terminal z) :
    (compiledCoreObs t).stepDist
      (liftBehavioralProfileCore t σ) ss =
      PMF.pure (.terminal z) := by
  dsimp [ObsModelCore.stepDist, ObsModelCore.jointActionDist]
  have hf :
      (fun a =>
        (compiledCoreObs t).step
          ((compiledCoreObs t).lastState ss)
          ((compiledCoreObs t).castJointAction ss a)) =
      (fun _ => PMF.pure (.terminal z)) := by
    funext a
    exact compiledCore_step_of_terminal t hs
      ((compiledCoreObs t).castJointAction ss a)
  rw [hf]
  simp

private theorem stepDist_compiledCore_eq_chance
    (σ : BehavioralProfile S) (ss : List (GameTree S Outcome))
    {k : Nat} {μ : PMF (Fin k)} {hk : 0 < k}
    (next : Fin k → GameTree S Outcome)
    (hs : (compiledCoreObs t).lastState ss = .chance k μ hk next) :
    (compiledCoreObs t).stepDist
      (liftBehavioralProfileCore t σ) ss =
      μ.map next := by
  dsimp [ObsModelCore.stepDist, ObsModelCore.jointActionDist]
  have hf :
      (fun a =>
        (compiledCoreObs t).step
          ((compiledCoreObs t).lastState ss)
          ((compiledCoreObs t).castJointAction ss a)) =
      (fun _ => μ.map next) := by
    funext a
    exact compiledCore_step_of_chance t next hs
      ((compiledCoreObs t).castJointAction ss a)
  rw [hf]
  simp

private theorem stepDist_compiledCore_eq_decision
    (σ : BehavioralProfile S) (ss : List (GameTree S Outcome))
    {p : S.Player} (I : S.Infoset p)
    (next : S.Act I → GameTree S Outcome)
    (hs : (compiledCoreObs t).lastState ss = .decision I next) :
    (compiledCoreObs t).stepDist
      (liftBehavioralProfileCore t σ) ss =
      (σ p I).bind (fun a => PMF.pure (next a)) := by
  let O := compiledCoreObs t
  dsimp [ObsModelCore.stepDist, ObsModelCore.jointActionDist]
  have hf :
      (fun a =>
        O.step (O.lastState ss) (O.castJointAction ss a)) =
      (fun a =>
        PMF.pure
          (next
            (cast
              (compiledAct_eq_of_some S p
                (show O.projectStates p ss = some I by
                  simp [O, hs, obsOfState]))
              (a p)))) := by
    funext a
    have hs' :=
      compiledCore_step_of_decision t I next hs
        (O.castJointAction ss a)
    grind [obsOfState, ObsModelCore.castJointAction, cast_cast]
  rw [hf]
  rw [Math.ProbabilityMassFunction.bind_pure_eq_pushforward]
  have hcomp :
      Math.ProbabilityMassFunction.pushforward
        (pmfPi (fun i =>
          liftBehavioralProfileCore t σ i
            (O.projectStates i ss)))
        (fun a =>
          next
            (cast
              (compiledAct_eq_of_some S p
                (show O.projectStates p ss = some I by simp [O, hs, obsOfState]))
              (a p))) =
      Math.ProbabilityMassFunction.pushforward
        (Math.ProbabilityMassFunction.pushforward
          (pmfPi (fun i =>
            liftBehavioralProfileCore t σ i
              (O.projectStates i ss)))
          (fun a =>
            cast
              (compiledAct_eq_of_some S p
                (show O.projectStates p ss = some I by simp [O, hs, obsOfState]))
              (a p)))
        next := by
    simpa [Function.comp] using
      (Math.ProbabilityMassFunction.pushforward_comp
        (pmfPi (fun i =>
          liftBehavioralProfileCore t σ i
            (O.projectStates i ss)))
        (fun a =>
          cast
            (compiledAct_eq_of_some S p
              (show O.projectStates p ss = some I by simp [O, hs, obsOfState]))
            (a p))
        next).symm
  rw [hcomp]
  have hpush :
      Math.ProbabilityMassFunction.pushforward
        (pmfPi (fun i =>
          liftBehavioralProfileCore t σ i
            (O.projectStates i ss)))
        (fun a =>
          cast
            (compiledAct_eq_of_some S p
              (show O.projectStates p ss = some I by simp [O, hs, obsOfState]))
            (a p)) =
      σ p I := by
    have hcomp' :
        Math.ProbabilityMassFunction.pushforward
          (pmfPi (fun i =>
            liftBehavioralProfileCore t σ i
              (O.projectStates i ss)))
          (fun a =>
            cast
              (compiledAct_eq_of_some S p
                (show O.projectStates p ss = some I by simp [O, hs, obsOfState]))
              (a p)) =
        Math.ProbabilityMassFunction.pushforward
          (Math.ProbabilityMassFunction.pushforward
            (pmfPi (fun i =>
              liftBehavioralProfileCore t σ i
                (O.projectStates i ss)))
            (fun a => a p))
          (fun x =>
            cast
              (compiledAct_eq_of_some S p
                (show O.projectStates p ss = some I by simp [O, hs, obsOfState]))
              x) := by
      simpa [Function.comp] using
        (Math.ProbabilityMassFunction.pushforward_comp
          (pmfPi (fun i =>
            liftBehavioralProfileCore t σ i
              (O.projectStates i ss)))
          (fun a => a p)
          (fun x =>
            cast
            (compiledAct_eq_of_some S p
              (show O.projectStates p ss = some I by simp [O, hs, obsOfState]))
              x)).symm
    rw [hcomp', Math.PMFProduct.pmfPi_push_coord]
    have hproj : O.projectStates p ss = some I := by
      simp [O, hs, obsOfState]
    have hlocal :
        ∀ v : Option (S.Infoset p),
          ∀ h : v = some I,
            Math.ProbabilityMassFunction.pushforward
              (liftBehavioralProfileCore t σ p v)
              (fun x => cast (compiledAct_eq_of_some S p h) x) =
            σ p I := by
      intro v h
      cases h
      simpa [liftBehavioralProfileCore] using
        (Math.ProbabilityMassFunction.pushforward_id (σ p I))
    exact hlocal _ hproj
  rw [hpush, Math.ProbabilityMassFunction.bind_pure_eq_pushforward]

theorem stepDist_compiledCore_eq
    (σ : BehavioralProfile S) (ss : List (GameTree S Outcome)) :
    (compiledCoreObs t).stepDist
      (liftBehavioralProfileCore t σ) ss =
      match (compiledCoreObs t).lastState ss with
      | .terminal z => PMF.pure (.terminal z)
      | .chance _k μ _hk next => μ.map next
      | .decision (p := p) I next => (σ p I).bind (fun a => PMF.pure (next a)) := by
  match hs : (compiledCoreObs t).lastState ss with
  | .terminal z =>
      exact stepDist_compiledCore_eq_terminal t σ ss hs
  | .chance k μ hk next =>
      exact stepDist_compiledCore_eq_chance t σ ss next hs
  | .decision (p := p) I next =>
      exact stepDist_compiledCore_eq_decision t σ ss I next hs

/-- The honest core EFG compilation has step-mass invariance. -/
theorem stepMassInvariant_compiledCore :
    ObsModelCore.StepMassInvariant
      (compiledCoreObs t) := by
  intro ss dst π₁ π₂ h₁ h₂
  cases hlast : (compiledCoreObs t).lastState ss with
  | terminal z =>
      simp [pureStep_compiledCore_eq, hlast] at h₁ h₂ ⊢
  | chance k μ hk next =>
      simp [pureStep_compiledCore_eq, hlast] at h₁ h₂ ⊢
  | @decision p I next =>
      have h₁' := h₁
      have h₂' := h₂
      simp only [pureStep_compiledCore_eq, hlast, PMF.pure_apply, ne_eq, ite_eq_right_iff,
        one_ne_zero, imp_false, not_not] at h₁' h₂' ⊢
      have hEq : next (π₁ p (some I)) = next (π₂ p (some I)) := h₁'.symm.trans h₂'
      cases h₁'
      simp [hEq]

/-- The honest core EFG compilation has one-step support factorization. -/
theorem stepSupportFactorization_compiledCore :
    ObsModelCore.StepSupportFactorization
      (compiledCoreObs t) := by
  intro ss dst π₀ π h₀
  cases hlast : (compiledCoreObs t).lastState ss with
  | terminal z =>
      have h₀' := h₀
      simp only [pureStep_compiledCore_eq, hlast, PMF.pure_apply, ne_eq, ite_eq_right_iff,
        one_ne_zero, imp_false, not_not] at h₀' ⊢
      constructor
      · intro hd i
        simpa using hd
      · intro hall
        simpa only using h₀'
  | chance k μ hk next =>
      have h₀' := h₀
      simp only [pureStep_compiledCore_eq, hlast, PMF.map_apply, tsum_fintype, ne_eq,
        Finset.sum_eq_zero_iff, Finset.mem_univ, ite_eq_right_iff,
        forall_const, not_forall] at h₀' ⊢
      constructor
      · intro hd i
        simpa using hd
      · intro hall
        simpa [h₀'] using h₀'
  | @decision p I next =>
      have h₀' := h₀
      simp only [pureStep_compiledCore_eq, hlast, PMF.pure_apply, ne_eq, ite_eq_right_iff,
        one_ne_zero, imp_false, not_not] at h₀' ⊢
      constructor
      · intro hd i
        by_cases hi : i = p
        · subst hi
          simpa [Function.update_self] using hd
        · have hpi : p ≠ i := by
            intro h
            exact hi h.symm
          simpa [Function.update_of_ne hpi] using h₀'
      · intro hall
        simpa [Function.update_self] using hall p

/-- One-step adequacy for the honest core compilation. -/
theorem stepDist_bind_evalDist_core
    (σ : BehavioralProfile S) (ss : List (GameTree S Outcome)) :
    ((compiledCoreObs t).stepDist
      (liftBehavioralProfileCore t σ) ss).bind
        (fun u => u.evalDist σ) =
      ((compiledCoreObs t).lastState ss).evalDist σ := by
  rw [stepDist_compiledCore_eq t σ ss]
  cases hlast : (compiledCoreObs t).lastState ss with
  | terminal z =>
      simp
  | chance k μ hk next =>
      simp [PMF.map, PMF.bind_bind]
  | decision I next =>
      simp [GameTree.evalDist]

/-- Bounded-run adequacy via generic `runDist_bind_interp`. -/
theorem runDist_bind_evalDist_core
    (σ : BehavioralProfile S) (k : Nat) :
    ((compiledCoreObs t).runDist k
      (liftBehavioralProfileCore t σ)).bind
        (fun ss => ((compiledCoreObs t).lastState ss).evalDist σ) =
      t.evalDist σ :=
  ObsModelCore.runDist_bind_interp
    (compiledCoreObs t) (fun u => u.evalDist σ)
    (liftBehavioralProfileCore t σ)
    (stepDist_bind_evalDist_core t σ) k

@[simp] theorem liftBehavioralProfileCore_pure_descend
    (π : ObsModelCore.PureProfile (compiledCoreObs t)) :
    liftBehavioralProfileCore t
      (pureToBehavioral (descendPureProfileCore t π)) =
      (compiledCoreObs t).pureToBehavioral π := by
  funext i v
  cases v <;> rfl

/-- Pure-profile adequacy for the honest core compilation. -/
theorem runDistPure_bind_evalDist_core
    (π : ObsModelCore.PureProfile (compiledCoreObs t))
    (k : Nat) :
    ((compiledCoreObs t).runDistPure k π).bind
        (fun ss =>
          ((compiledCoreObs t).lastState ss).evalDist
            (pureToBehavioral (descendPureProfileCore t π))) =
      t.evalDist (pureToBehavioral (descendPureProfileCore t π)) := by
  simpa [ObsModelCore.runDistPure, liftBehavioralProfileCore_pure_descend]
    using runDist_bind_evalDist_core t
      (pureToBehavioral (descendPureProfileCore t π)) k

private def HistoryCompatibleCore
    (π : ObsModelCore.PureProfile (compiledCoreObs t))
    (h : List (HistoryStep S)) : Prop :=
  ∀ ⦃p : S.Player⦄ ⦃I : S.Infoset p⦄ ⦃a : S.Act I⦄,
    HistoryStep.action p I a ∈ h → π p (some I) = a

private def HistorySupportStep :
    HistoryStep S → GameTree S Outcome → GameTree S Outcome → Prop
  | .chance k b, src, dst =>
      ∃ (μ : PMF (Fin k)) (hk : 0 < k) (next : Fin k → GameTree S Outcome),
        src = .chance k μ hk next ∧ μ b ≠ 0 ∧ dst = next b
  | .action _p I a, src, dst =>
      ∃ (next : S.Act I → GameTree S Outcome),
        src = .decision I next ∧ dst = next a

private inductive HistorySupportTrace (t : GameTree S Outcome) :
    List (GameTree S Outcome) → List (HistoryStep S) → Type
  | init : HistorySupportTrace t [t] []
  | stutter {ss : List (GameTree S Outcome)} {h : List (HistoryStep S)}
      {z : Outcome}
      (hw : HistorySupportTrace t ss h)
      (hterm : ((compiledCoreObs t).lastState ss) = .terminal z) :
      HistorySupportTrace t (ss ++ [.terminal z]) h
  | snoc {ss : List (GameTree S Outcome)} {h : List (HistoryStep S)}
      {u : GameTree S Outcome} {ℓ : HistoryStep S}
      (hw : HistorySupportTrace t ss h)
      (hstep : HistorySupportStep ℓ
        ((compiledCoreObs t).lastState ss) u) :
      HistorySupportTrace t (ss ++ [u]) (h ++ [ℓ])

private theorem historySupportTrace_nonempty
    {ss : List (GameTree S Outcome)} {h : List (HistoryStep S)}
    (hw : HistorySupportTrace t ss h) :
    ss ≠ [] := by
  induction hw with
  | init =>
      simp
  | @stutter ss h z hw _ ih =>
      intro hnil
      simp at hnil
  | @snoc ss h u ℓ hw _ ih =>
      intro hnil
      simp at hnil

private theorem historySupportTrace_length_pos
    {ss : List (GameTree S Outcome)} {h : List (HistoryStep S)}
    (hw : HistorySupportTrace t ss h) :
    0 < ss.length := by
  exact List.length_pos_iff_ne_nil.mpr
    (historySupportTrace_nonempty t hw)

private theorem reachBy_singleton_of_historySupportStep
    {src dst : GameTree S Outcome} {ℓ : HistoryStep S}
    (hstep : HistorySupportStep ℓ src dst) :
    ReachBy [ℓ] src dst := by
  cases ℓ with
  | chance k b =>
      rcases hstep with ⟨μ, hk, next, rfl, _, rfl⟩
      exact ReachBy.chance b (.here _)
  | action p I a =>
      rcases hstep with ⟨next, rfl, rfl⟩
      exact ReachBy.action a (.here _)

private theorem historySupportTrace_reachBy
    {ss : List (GameTree S Outcome)} {h : List (HistoryStep S)}
    (hw : HistorySupportTrace t ss h) :
    ReachBy h t ((compiledCoreObs t).lastState ss) := by
  induction hw with
  | init =>
      simp [compiledCoreObs, compileObsCoreModel, InfoStateCore.identity, ObsModelCore.lastState]
  | @stutter ss h z hw hterm ih =>
      have ih' : ReachBy h t (.terminal z) := by
        simpa [hterm] using ih
      have hlast :
          (compiledCoreObs t).lastState (ss ++ [.terminal z]) =
            .terminal z := by
        simp [ObsModelCore.lastState]
      exact hlast.symm ▸ ih'
  | @snoc ss h u ℓ hw hstep ih =>
      have htail : ReachBy [ℓ]
          ((compiledCoreObs t).lastState ss) u :=
        reachBy_singleton_of_historySupportStep hstep
      have hcat := ReachBy_append ih htail
      simpa [compiledCoreObs, compileObsCoreModel, InfoStateCore.identity,
        ObsModelCore.lastState] using hcat

private theorem playerHistory_mem_of_action_mem
    {i : S.Player} {I : S.Infoset i} {a : S.Act I} {h : List (HistoryStep S)}
    (hm : HistoryStep.action i I a ∈ h) :
    ⟨I, a⟩ ∈ playerHistory S i h := by
  induction h with
  | nil =>
      cases hm
  | cons step rest ih =>
      cases step with
      | chance k b =>
          simp only [List.mem_cons, reduceCtorEq, false_or, playerHistory] at hm ⊢
          exact ih hm
      | action p J act =>
          by_cases hp : p = i
          · subst hp
            simp only [List.mem_cons] at hm
            simp only [playerHistory, ↓reduceDIte, List.mem_cons, Sigma.mk.injEq]
            rcases hm with hm | hm
            · cases hm
              simp
            · exact Or.inr (ih hm)
          · simp only [List.mem_cons] at hm
            rcases hm with hm | hm
            · cases hm
              exact (hp rfl).elim
            · simpa [playerHistory, hp] using ih hm

private theorem action_mem_of_playerHistory_mem
    {i : S.Player} {tok : Σ I : S.Infoset i, S.Act I} {h : List (HistoryStep S)}
    (hm : tok ∈ playerHistory S i h) :
    HistoryStep.action i tok.1 tok.2 ∈ h := by
  induction h with
  | nil =>
      simp only [List.not_mem_nil, playerHistory] at hm
  | cons step rest ih =>
      cases step with
      | chance k b =>
          simp only [playerHistory, List.mem_cons, reduceCtorEq, false_or] at hm ⊢
          exact ih hm
      | action p J act =>
          by_cases hp : p = i
          · subst hp
            simp only [List.mem_cons] at ⊢
            simp only [playerHistory, ↓reduceDIte, List.mem_cons] at hm
            rcases hm with rfl | hm
            · exact Or.inl rfl
            · exact Or.inr (ih hm)
          · have hm' : tok ∈ playerHistory S i rest := by
              simpa [playerHistory, hp] using hm
            simpa [List.mem_cons] using Or.inr (ih hm')

private theorem playerHistory_agrees_of_historyCompatibleCore_update
    {i : S.Player}
    {π₀ : ObsModelCore.PureProfile (compiledCoreObs t)}
    {πᵢ : (compiledCoreObs t).LocalStrategy i}
    {h : List (HistoryStep S)}
    (hcomp : HistoryCompatibleCore t
      (Function.update π₀ i πᵢ) h) :
    ∀ tok ∈ playerHistory S i h, πᵢ (some tok.1) = tok.2 := by
  intro tok htok
  have hm : HistoryStep.action i tok.1 tok.2 ∈ h :=
    action_mem_of_playerHistory_mem htok
  simpa [HistoryCompatibleCore, Function.update_self] using hcomp hm

private theorem historyCompatibleCore_update_of_playerHistory
    {i : S.Player}
    {π₀ : ObsModelCore.PureProfile (compiledCoreObs t)}
    {πᵢ : (compiledCoreObs t).LocalStrategy i}
    {h : List (HistoryStep S)}
    (hbase : HistoryCompatibleCore t π₀ h)
    (hpi : ∀ tok ∈ playerHistory S i h, πᵢ (some tok.1) = tok.2) :
    HistoryCompatibleCore t
      (Function.update π₀ i πᵢ) h := by
  intro q J a hm
  by_cases hq : q = i
  · subst hq
    simpa [Function.update_self] using
      hpi ⟨J, a⟩ (playerHistory_mem_of_action_mem hm)
  · simpa [HistoryCompatibleCore, Function.update_of_ne hq] using hbase hm

private theorem pureRun_nonzero_to_historySupportTrace
    {n : Nat}
    {π : ObsModelCore.PureProfile (compiledCoreObs t)}
    {ss : List (GameTree S Outcome)}
    (h : Math.ParameterizedChain.pureRun
      ((compiledCoreObs t).pureStep)
      ((compiledCoreObs t).init) n π ss ≠ 0) :
    ∃ hist,
      Nonempty (HistorySupportTrace t ss hist) ∧
      HistoryCompatibleCore t π hist := by
  induction n generalizing ss with
  | zero =>
      simp only [Math.ParameterizedChain.pureRun, Nat.rec_zero, PMF.pure_apply, ne_eq,
        ite_eq_right_iff, one_ne_zero, imp_false, not_not] at h
      subst ss
      exact ⟨[], ⟨.init⟩, by
        intro p I a hm
        cases hm⟩
  | succ n ih =>
      rcases List.eq_nil_or_concat ss with rfl | ⟨pfx, u, rfl⟩
      · exact absurd (Math.ParameterizedChain.pureRun_succ_nil _ _ _ _) h
      · have hp :
            Math.ParameterizedChain.pureRun
              ((compiledCoreObs t).pureStep)
              ((compiledCoreObs t).init) n π pfx ≠ 0 := by
            rw [List.concat_eq_append, Math.ParameterizedChain.pureRun_succ_append] at h
            exact left_ne_zero_of_mul h
        have hu :
            ((compiledCoreObs t).pureStep π pfx) u ≠ 0 := by
            rw [List.concat_eq_append, Math.ParameterizedChain.pureRun_succ_append] at h
            exact right_ne_zero_of_mul h
        rcases ih hp with ⟨hist, ⟨hh⟩, hcompat⟩
        cases hlast : (compiledCoreObs t).lastState pfx with
        | terminal z =>
            have hu' : u = .terminal z := by
              simpa [pureStep_compiledCore_eq, hlast] using hu
            subst hu'
            refine ⟨hist, ?_, hcompat⟩
            exact ⟨by
              simpa [List.concat_eq_append] using (HistorySupportTrace.stutter hh hlast)⟩
        | chance k μ hk next =>
            have hmap : ∃ b, u = next b ∧ μ b ≠ 0 := by
              simpa [pureStep_compiledCore_eq, hlast, PMF.map] using hu
            rcases hmap with ⟨b, rfl, hb⟩
            refine ⟨hist ++ [HistoryStep.chance k b], ?_, ?_⟩
            · refine ⟨by
                simpa [List.concat_eq_append] using
                  (HistorySupportTrace.snoc hh
                    (show HistorySupportStep
                      (HistoryStep.chance k b)
                      ((compiledCoreObs t).lastState pfx)
                      (next b) from ⟨μ, hk, next, hlast, hb, rfl⟩))⟩
            · intro p I a hm
              simp only [List.mem_append, List.mem_singleton] at hm
              rcases hm with hm | hm
              · exact hcompat hm
              · cases hm
        | @decision p I next =>
            have hnext :
                u = next (π p (some I)) := by
              simpa [pureStep_compiledCore_eq, hlast] using hu
            subst u
            refine ⟨hist ++ [HistoryStep.action p I (π p (some I))], ?_, ?_⟩
            · refine ⟨by
                simpa [List.concat_eq_append] using
                  (HistorySupportTrace.snoc hh
                    (show HistorySupportStep
                      (HistoryStep.action p I (π p (some I)))
                      ((compiledCoreObs t).lastState pfx)
                      (next (π p (some I))) from ⟨next, hlast, rfl⟩))⟩
            · intro q J a hm
              simp only [List.mem_append, List.mem_singleton] at hm
              rcases hm with hm | hm
              · exact hcompat hm
              · cases hm
                rfl

private theorem historySupportTrace_pureRun_nonzero
    {π : ObsModelCore.PureProfile (compiledCoreObs t)}
    {ss : List (GameTree S Outcome)} {hist : List (HistoryStep S)}
    (hw : HistorySupportTrace t ss hist)
    (hcompat : HistoryCompatibleCore t π hist) :
    Math.ParameterizedChain.pureRun
      ((compiledCoreObs t).pureStep)
      ((compiledCoreObs t).init) (ss.length - 1) π ss ≠ 0 := by
  induction hw with
  | init =>
      simp [Math.ParameterizedChain.pureRun, compiledCoreObs,
        compileObsCoreModel, InfoStateCore.identity]
  | @stutter ss hist z hw hterm ih =>
      have hu :
          ((compiledCoreObs t).pureStep π ss)
            (.terminal z) ≠ 0 := by
        simp [pureStep_compiledCore_eq, hterm]
      have hlen : 0 < ss.length :=
        historySupportTrace_length_pos t hw
      have hslen : ss.length - 1 + 1 = ss.length := by
        omega
      have hmul :
          Math.ParameterizedChain.pureRun
            ((compiledCoreObs t).pureStep)
            ((compiledCoreObs t).init)
            ((ss.length - 1) + 1) π (ss ++ [.terminal z]) ≠ 0 := by
        rw [Math.ParameterizedChain.pureRun_succ_append]
        exact mul_ne_zero (ih hcompat) hu
      simpa [List.length_append, hslen] using hmul
  | @snoc ss hist u ℓ hw hstep ih =>
      have hcompat_prev :
          HistoryCompatibleCore t π hist := by
        intro p I a hm
        exact hcompat (by simp [hm])
      have hp := ih hcompat_prev
      have hu :
          ((compiledCoreObs t).pureStep π ss) u ≠ 0 := by
        cases ℓ with
        | chance k b =>
            rcases hstep with ⟨μ, hk, next, hsrc, hb, hdst⟩
            simpa [pureStep_compiledCore_eq, hsrc, hdst, PMF.map] using
              (show ∃ x, next b = next x ∧ μ x ≠ 0 from ⟨b, rfl, hb⟩)
        | action p I a =>
            rcases hstep with ⟨next, hsrc, hdst⟩
            have ha :
                π p (some I) = a := by
              apply hcompat
              simp
            simp [pureStep_compiledCore_eq, hsrc, hdst, ha]
      have hlen : 0 < ss.length :=
        historySupportTrace_length_pos t hw
      have hslen : ss.length - 1 + 1 = ss.length := by
        omega
      have hmul :
          Math.ParameterizedChain.pureRun
            ((compiledCoreObs t).pureStep)
            ((compiledCoreObs t).init)
            ((ss.length - 1) + 1) π (ss ++ [u]) ≠ 0 := by
        rw [Math.ParameterizedChain.pureRun_succ_append]
        exact mul_ne_zero hp hu
      simpa [List.length_append, hslen] using hmul

private theorem exists_decision_of_projectStates_eq_some
    {i : S.Player} {I : S.Infoset i} {ss : List (GameTree S Outcome)}
    (h : (compiledCoreObs t).projectStates i ss = some I) :
    ∃ next : S.Act I → GameTree S Outcome,
      (compiledCoreObs t).lastState ss = .decision I next := by
  cases hlast : (compiledCoreObs t).lastState ss with
  | terminal z =>
      simp [projectStates_compiledCore, hlast, obsOfState] at h
  | chance k μ hk next =>
      simp [projectStates_compiledCore, hlast, obsOfState] at h
  | @decision p J next =>
      by_cases hp : p = i
      · subst hp
        simp only [projectStates_compiledCore, obsOfState, hlast, ↓reduceDIte] at h
        cases h
        refine ⟨next, ?_⟩
        simp
      · simp [projectStates_compiledCore, hlast, obsOfState, hp] at h

private theorem infoState_some_of_not_subsingleton
    {i : S.Player} {ss : List (GameTree S Outcome)}
    (hsub : ¬ Subsingleton
      (CompiledAct S i
        ((compiledCoreObs t).currentObs i
          ((compiledCoreObs t).projectStates i ss)))) :
    ∃ I : S.Infoset i,
      (compiledCoreObs t).projectStates i ss = some I := by
  cases hlast : (compiledCoreObs t).lastState ss with
  | terminal z =>
      exfalso
      apply hsub
      simpa [projectStates_compiledCore, hlast, obsOfState, CompiledAct] using
        (inferInstance : Subsingleton PUnit)
  | chance k μ hk next =>
      exfalso
      apply hsub
      simpa [projectStates_compiledCore, hlast, obsOfState, CompiledAct] using
        (inferInstance : Subsingleton PUnit)
  | @decision p J next =>
      by_cases hp : p = i
      · subst hp
        refine ⟨J, ?_⟩
        simp [projectStates_compiledCore, hlast, obsOfState]
      · exfalso
        apply hsub
        simpa [projectStates_compiledCore, hlast, obsOfState, hp, CompiledAct] using
          (inferInstance : Subsingleton PUnit)

private theorem obsLocalFeasibility_compiledCore
    (hpr : PerfectRecall t) (i : S.Player) :
    ObsModelCore.ObsLocalFeasibility
      (compiledCoreObs t) i := by
  intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ hsub πᵢ
  obtain ⟨I, hI₁⟩ :=
    infoState_some_of_not_subsingleton t
      (i := i) (ss := ss₁) hsub
  have hI₂ :
      (compiledCoreObs t).projectStates i ss₂ = some I := by
    exact hobs.symm ▸ hI₁
  obtain ⟨next₁, hdec₁⟩ :=
    exists_decision_of_projectStates_eq_some t hI₁
  obtain ⟨next₂, hdec₂⟩ :=
    exists_decision_of_projectStates_eq_some t hI₂
  obtain ⟨hist₁, ⟨hsupp₁⟩, hcompat₁⟩ :=
    pureRun_nonzero_to_historySupportTrace t h₁
  obtain ⟨hist₂, ⟨hsupp₂⟩, hcompat₂⟩ :=
    pureRun_nonzero_to_historySupportTrace t h₂
  have hreach₁ : ReachBy hist₁ t (.decision I next₁) := by
    simpa [hdec₁] using
      (historySupportTrace_reachBy t hsupp₁)
  have hreach₂ : ReachBy hist₂ t (.decision I next₂) := by
    simpa [hdec₂] using
      (historySupportTrace_reachBy t hsupp₂)
  have hplayer :
      playerHistory S i hist₁ = playerHistory S i hist₂ := by
    exact hpr hist₁ hist₂ I next₁ next₂ hreach₁ hreach₂
  constructor
  · intro hupd₁
    obtain ⟨hist₁', ⟨hsupp₁'⟩, hcompat₁'⟩ :=
      pureRun_nonzero_to_historySupportTrace t hupd₁
    have hreach₁' : ReachBy hist₁' t (.decision I next₁) := by
      simpa [hdec₁] using
        (historySupportTrace_reachBy t hsupp₁')
    have hplayer₁' :
        playerHistory S i hist₁' = playerHistory S i hist₁ := by
      exact hpr hist₁' hist₁ I next₁ next₁ hreach₁' hreach₁
    have hagree₁ :
        ∀ tok ∈ playerHistory S i hist₁, πᵢ (some tok.1) = tok.2 := by
      intro tok htok
      have htok' : tok ∈ playerHistory S i hist₁' := by
        simpa [hplayer₁'] using htok
      exact playerHistory_agrees_of_historyCompatibleCore_update
        t hcompat₁' tok htok'
    have hagree₂ :
        ∀ tok ∈ playerHistory S i hist₂, πᵢ (some tok.1) = tok.2 := by
      intro tok htok
      have htok₁ : tok ∈ playerHistory S i hist₁ := by
        simpa [hplayer] using htok
      exact hagree₁ tok htok₁
    have hcompat₂' :=
      historyCompatibleCore_update_of_playerHistory
        t hcompat₂ hagree₂
    have hlen₂ : ss₂.length - 1 = n₂ := by
      have := Math.ParameterizedChain.pureRun_length
        ((compiledCoreObs t).pureStep)
        ((compiledCoreObs t).init) n₂ π₀' ss₂ h₂
      omega
    simpa [hlen₂] using
      historySupportTrace_pureRun_nonzero
        t hsupp₂ hcompat₂'
  · intro hupd₂
    obtain ⟨hist₂', ⟨hsupp₂'⟩, hcompat₂'⟩ :=
      pureRun_nonzero_to_historySupportTrace t hupd₂
    have hreach₂' : ReachBy hist₂' t (.decision I next₂) := by
      simpa [hdec₂] using
        (historySupportTrace_reachBy t hsupp₂')
    have hplayer₂' :
        playerHistory S i hist₂' = playerHistory S i hist₂ := by
      exact hpr hist₂' hist₂ I next₂ next₂ hreach₂' hreach₂
    have hagree₂ :
        ∀ tok ∈ playerHistory S i hist₂, πᵢ (some tok.1) = tok.2 := by
      intro tok htok
      have htok' : tok ∈ playerHistory S i hist₂' := by
        simpa [hplayer₂'] using htok
      exact playerHistory_agrees_of_historyCompatibleCore_update
        t hcompat₂' tok htok'
    have hagree₁ :
        ∀ tok ∈ playerHistory S i hist₁, πᵢ (some tok.1) = tok.2 := by
      intro tok htok
      have htok₂ : tok ∈ playerHistory S i hist₂ := by
        simpa [hplayer] using htok
      exact hagree₂ tok htok₂
    have hcompat₁' :=
      historyCompatibleCore_update_of_playerHistory
        t hcompat₁ hagree₁
    have hlen₁ : ss₁.length - 1 = n₁ := by
      have := Math.ParameterizedChain.pureRun_length
        ((compiledCoreObs t).pureStep)
        ((compiledCoreObs t).init) n₁ π₀ ss₁ h₁
      omega
    simpa [hlen₁] using
      historySupportTrace_pureRun_nonzero
        t hsupp₁ hcompat₁'

private noncomputable def treeHeight : GameTree S Outcome → Nat
  | .terminal _ => 0
  | .chance _k _μ _hk next => Nat.succ <| Finset.univ.sup fun b => treeHeight (next b)
  | .decision _ next => Nat.succ <| Finset.univ.sup fun a => treeHeight (next a)

private theorem treeHeight_pos_of_nonterminal
    {u : GameTree S Outcome} (hnterm : ∀ z, u ≠ .terminal z) :
    0 < treeHeight u := by
  cases u with
  | terminal z =>
      exact (hnterm z rfl).elim
  | chance k μ hk next =>
      simp [treeHeight]
  | decision I next =>
      simp [treeHeight]

private theorem historyStepStep_height_lt
    {src dst : GameTree S Outcome} {ℓ : HistoryStep S}
    (hstep : HistoryStepStep ℓ src dst) :
    treeHeight dst <
      treeHeight src := by
  cases ℓ with
  | chance k b =>
      rcases hstep with ⟨μ, hk, next, rfl, rfl⟩
      simp only [treeHeight, Nat.succ_eq_add_one, Order.lt_add_one_iff]
      exact Finset.le_sup
        (f := fun b : Fin k => treeHeight (next b))
        (by simp)
  | action p I a =>
      rcases hstep with ⟨next, rfl, rfl⟩
      simp only [treeHeight, Nat.succ_eq_add_one, Order.lt_add_one_iff]
      exact Finset.le_sup
        (f := fun a : S.Act I => treeHeight (next a))
        (by simp)

private theorem reachBy_length_add_height_le
    {src dst : GameTree S Outcome} {h : List (HistoryStep S)}
    (hr : ReachBy h src dst) :
    h.length + treeHeight dst ≤
      treeHeight src := by
  induction hr with
  | nil =>
      simp only [List.length_nil, zero_add, le_refl]
  | @cons ℓ rest src mid dst hstep hreach ih =>
      have hlt :
          treeHeight mid <
            treeHeight src :=
        historyStepStep_height_lt hstep
      have hle :
          rest.length + treeHeight dst + 1 ≤
            treeHeight src := by
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hlt)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hle

private theorem historySupportStep_source_nonterminal
    {src dst : GameTree S Outcome} {ℓ : HistoryStep S}
    (hstep : HistorySupportStep ℓ src dst) :
    ∀ z, src ≠ .terminal z := by
  intro z hz
  cases ℓ with
  | chance k b =>
      rcases hstep with ⟨μ, hk, next, hsrc, _hb, _hdst⟩
      simp [hz] at hsrc
  | action p I a =>
      rcases hstep with ⟨next, hsrc, _hdst⟩
      simp [hz] at hsrc

private theorem historySupportTrace_length_eq_of_nonterminal
    {ss : List (GameTree S Outcome)} {h : List (HistoryStep S)}
    (hw : HistorySupportTrace t ss h)
    (hnterm : ∀ z,
      (compiledCoreObs t).lastState ss ≠ .terminal z) :
    ss.length = h.length + 1 := by
  induction hw with
  | init =>
      simp
  | @stutter ss h z hw hterm ih =>
      exfalso
      exact hnterm z (by
        have :
            (compiledCoreObs t).lastState (ss ++ [.terminal z]) =
              .terminal z := by
          simp [ObsModelCore.lastState]
        exact this)
  | @snoc ss h u ℓ hw hstep ih =>
      have hsrc_nonterm :
          ∀ z,
            (compiledCoreObs t).lastState ss ≠ .terminal z :=
        historySupportStep_source_nonterminal hstep
      have hlen := ih hsrc_nonterm
      simp [List.length_append, hlen]

private theorem lastState_terminal_of_pureRun_height
    {π : ObsModelCore.PureProfile (compiledCoreObs t)}
    {ss : List (GameTree S Outcome)}
    (h :
      Math.ParameterizedChain.pureRun
        ((compiledCoreObs t).pureStep)
        ((compiledCoreObs t).init)
        (treeHeight t) π ss ≠ 0) :
    ∃ z,
      (compiledCoreObs t).lastState ss = .terminal z := by
  obtain ⟨hist, ⟨hsupp⟩, hcompat⟩ :=
    pureRun_nonzero_to_historySupportTrace t h
  by_contra hnot
  have hnterm :
      ∀ z, (compiledCoreObs t).lastState ss ≠ .terminal z := by
    intro z hz
    exact hnot ⟨z, hz⟩
  have hlenTrace := Math.ParameterizedChain.pureRun_length
    ((compiledCoreObs t).pureStep)
    ((compiledCoreObs t).init)
    (treeHeight t) π ss h
  have hlenHist :
      hist.length = treeHeight t := by
    have hlenSupport :=
      historySupportTrace_length_eq_of_nonterminal
        t hsupp hnterm
    omega
  have hreach :=
    historySupportTrace_reachBy t hsupp
  have hbound :=
    reachBy_length_add_height_le hreach
  have hpos :
      0 < treeHeight
        ((compiledCoreObs t).lastState ss) := by
    exact treeHeight_pos_of_nonterminal hnterm
  omega

-- ============================================================================
-- NoNontrivialInfoStateRepeat for the compiled core
-- ============================================================================

/-- `NoInfoSetRepeat` is hereditary along `ReachBy` paths in the game tree. -/
private theorem noInfoSetRepeat_of_reachBy
    {src dst : GameTree S Outcome} {h : List (HistoryStep S)}
    (hnr : NoInfoSetRepeat src) (hr : ReachBy h src dst) :
    NoInfoSetRepeat dst := by
  induction hr with
  | nil => exact hnr
  | @cons ℓ _ src mid _ hstep _ ih =>
    apply ih
    cases ℓ with
    | chance k b =>
      rcases hstep with ⟨μ, hk, next, rfl, rfl⟩; exact hnr b
    | action p I a =>
      rcases hstep with ⟨next, rfl, rfl⟩; exact hnr.2 a

/-- `DecisionNodeIn` lifts backwards along `ReachBy` paths in the game tree. -/
private theorem decisionNodeIn_of_reachBy
    {parent child : GameTree S Outcome} {h : List (HistoryStep S)}
    {p : S.Player} {I : S.Infoset p}
    (hr : ReachBy h parent child) (hd : DecisionNodeIn I child) :
    DecisionNodeIn I parent := by
  induction hr with
  | nil => exact hd
  | @cons ℓ _ src mid _ hstep _ ih =>
    cases ℓ with
    | chance k b =>
      rcases hstep with ⟨μ, hk, next, rfl, rfl⟩
      exact .in_chance k μ hk next b (ih hd)
    | action q I' a =>
      rcases hstep with ⟨next, rfl, rfl⟩
      exact .in_decision I' next a (ih hd)

/-- A nonzero compiled pureStep yields a `ReachBy` path (one step for
chance/decision nodes, zero steps for terminal stuttering). -/
private theorem reachBy_of_pureStep_nonzero
    {π : ObsModelCore.PureProfile (compiledCoreObs t)}
    {ss : List (GameTree S Outcome)} {u : GameTree S Outcome}
    (hstep : (compiledCoreObs t).pureStep π ss u ≠ 0) :
    ∃ hist, ReachBy hist ((compiledCoreObs t).lastState ss) u := by
  rw [pureStep_compiledCore_eq] at hstep
  split at hstep
  case h_1 z hlast =>
    simp only [ne_eq, PMF.pure_apply, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hstep
    exact ⟨[], by rw [hlast, hstep]; exact .here _⟩
  case h_2 k μ hk next hlast =>
    rw [ne_eq, PMF.map_apply, ENNReal.tsum_eq_zero, not_forall] at hstep
    obtain ⟨b, hb⟩ := hstep
    have hub : u = next b := by split_ifs at hb with h <;> [exact h; exact absurd rfl hb]
    exact ⟨[.chance k b], by rw [hlast, hub]; exact ReachBy.chance b (.here _)⟩
  case h_3 q I' next hlast =>
    simp only [ne_eq, PMF.pure_apply, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hstep
    exact ⟨[.action q I' (π q (some I'))], by
      rw [hlast, hstep]; exact ReachBy.action _ (.here _)⟩

/-- If `obsOfState i node = some I`, then `node` is a decision node for `I`. -/
private theorem decisionNodeIn_of_obsOfState_some
    {i : S.Player} {I : S.Infoset i} {node : GameTree S Outcome}
    (hobs : obsOfState i node = some I) :
    DecisionNodeIn I node := by
  match node with
  | .terminal _ | .chance .. => simp [obsOfState] at hobs
  | .decision (p := p) I' next =>
    have hp : p = i := by by_contra h; simp [obsOfState, h] at hobs
    subst hp
    have hI : I' = I := by simpa [obsOfState] using hobs
    subst hI; exact .root next

/-- `lastState` of a take-prefix equals the corresponding element. -/
private theorem lastState_take_eq
    (ss : List (GameTree S Outcome)) (j : Nat) (hj : j < ss.length) :
    (compiledCoreObs t).lastState (ss.take (j + 1)) = ss[j] := by
  simp only [ObsModelCore.lastState]
  have hlen : (ss.take (j + 1)).length = j + 1 :=
    List.length_take_of_le (by omega)
  rw [List.getLast?_eq_getElem?, hlen]
  simp only [show j + 1 - 1 = j from by omega, List.getElem?_take_of_succ,
    show ss[j]? = some ss[j] from List.getElem?_eq_getElem hj, Option.getD_some]

/-- On a nonzero trace, the first element is the tree root. -/
private theorem pureRun_getElem_zero
    {π : ObsModelCore.PureProfile (compiledCoreObs t)}
    {k : Nat} {ss : List (GameTree S Outcome)}
    (h : (compiledCoreObs t).runDistPure k π ss ≠ 0)
    (h0 : 0 < ss.length) :
    ss[0] = t := by
  rw [ObsModelCore.runDistPure_eq_pureRun] at h
  induction k generalizing ss with
  | zero =>
    have : ss = [(compiledCoreObs t).init] := by
      by_contra hne; exact h (by simp [Math.ParameterizedChain.pureRun, PMF.pure_apply, hne])
    simp [this, compiledCoreObs, compileObsCoreModel]
  | succ m ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨pre, last, hcat⟩
    · simp at h0
    · rw [List.concat_eq_append] at hcat; subst hcat
      have hpre := left_ne_zero_of_mul
        (Math.ParameterizedChain.pureRun_succ_append .. ▸ h)
      have hlen_pre : 0 < pre.length := by
        have := Math.ParameterizedChain.pureRun_length _ _ m π pre hpre; omega
      simp only [List.getElem_append_left hlen_pre]
      exact ih hpre hlen_pre

/-- `ReachBy` between positions on a nonzero compiled trace, using
`pureRun_step_nonzero` from `Math.ParameterizedChain`. -/
private theorem reachBy_trace_positions
    {π : ObsModelCore.PureProfile (compiledCoreObs t)}
    {k : Nat} {ss : List (GameTree S Outcome)}
    (hrun : (compiledCoreObs t).runDistPure k π ss ≠ 0)
    {j₁ j₂ : Nat} (hle : j₁ ≤ j₂) (hj₂ : j₂ < ss.length) :
    ∃ hist, ReachBy hist ss[j₁] ss[j₂] := by
  have hlen : ss.length = k + 1 :=
    Math.ParameterizedChain.pureRun_length _ _ _ _ _ hrun
  obtain ⟨d, rfl⟩ : ∃ d, j₂ = j₁ + d := ⟨j₂ - j₁, by omega⟩
  induction d with
  | zero => exact ⟨[], .here _⟩
  | succ d ih =>
    obtain ⟨hist₁, hr₁⟩ := ih (by omega) (by omega)
    have hstep_ne : (compiledCoreObs t).pureStep π
        (ss.take ((j₁ + d) + 1)) ss[j₁ + d + 1] ≠ 0 :=
      Math.ParameterizedChain.pureRun_step_nonzero _ _ k π ss
        (ObsModelCore.runDistPure_eq_pureRun (compiledCoreObs t) k π ▸ hrun) (j₁ + d) (by omega)
    obtain ⟨hist_step, hr_step⟩ := reachBy_of_pureStep_nonzero t hstep_ne
    rw [lastState_take_eq t ss (j₁ + d) (by omega)] at hr_step
    exact ⟨hist₁ ++ hist_step, ReachBy_append hr₁ hr_step⟩

/-- For the compiled core EFG model, `NoInfoSetRepeat` implies no non-trivial
info state repeats on reachable traces. -/
theorem noNontrivialInfoStateRepeat_compiledCore
    (hnr : NoInfoSetRepeat t) :
    (compiledCoreObs t).NoNontrivialInfoStateRepeat := by
  intro i π k ss hreach j₁ j₂ hjlt hjlen hEq
  simp only [projectStates_compiledCore] at hEq ⊢
  have hlen : ss.length = k + 1 :=
    Math.ParameterizedChain.pureRun_length _ _ _ _ _ hreach
  -- Rewrite lastState (ss.take (j + 1)) = ss[j] everywhere
  rw [lastState_take_eq t ss j₁ (by omega)] at hEq
  rw [lastState_take_eq t ss j₂ (by omega)] at hEq ⊢
  change Subsingleton (CompiledAct S i (obsOfState i ss[j₂]))
  match hobs : obsOfState i ss[j₂] with
  | none =>
    change Subsingleton PUnit; exact inferInstance
  | some I =>
    exfalso
    have hobs₁ : obsOfState i ss[j₁] = some I := by rw [hEq, hobs]
    -- Get ReachBy from root to j₁ and from j₁+1 to j₂
    have hroot : ss[0] = t := pureRun_getElem_zero t hreach (by omega)
    obtain ⟨hist_root, hr_root⟩ := reachBy_trace_positions t hreach
      (Nat.zero_le j₁) (by omega)
    rw [hroot] at hr_root
    -- NoInfoSetRepeat propagates from root to position j₁
    have hnr_j₁ := noInfoSetRepeat_of_reachBy hnr hr_root
    -- Get ReachBy from j₁+1 to j₂; lift DecisionNodeIn I back
    obtain ⟨hist_seg, hr_seg⟩ := reachBy_trace_positions t hreach
      (show j₁ + 1 ≤ j₂ by omega) (by omega)
    have hdec_child := decisionNodeIn_of_reachBy hr_seg
      (decisionNodeIn_of_obsOfState_some hobs)
    -- The step from j₁ to j₁+1 identifies the child
    have hstep_ne : (compiledCoreObs t).pureStep π
        (ss.take (j₁ + 1)) ss[j₁ + 1] ≠ 0 :=
      Math.ParameterizedChain.pureRun_step_nonzero _ _ k π ss
        (ObsModelCore.runDistPure_eq_pureRun (compiledCoreObs t) k π ▸ hreach) j₁ (by omega)
    rw [pureStep_compiledCore_eq, lastState_take_eq t ss j₁ (by omega)] at hstep_ne
    -- Case split on the node at j₁
    match hnode : ss[j₁], hnr_j₁, hobs₁, hstep_ne, hdec_child with
    | .decision (p := p) I' next, hnr_node, hobs_node, hstep, hdec =>
      have hp : p = i := by by_contra hne; simp [obsOfState, hne] at hobs_node
      subst hp
      have hI : I' = I := by simpa [obsOfState] using hobs_node
      subst hI
      simp only [PMF.pure_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
        not_not] at hstep
      rw [hstep] at hdec
      exact hnr_node.1 _ hdec
    | .terminal _, _, hobs_node, _, _ => simp [obsOfState] at hobs_node
    | .chance .., _, hobs_node, _, _ => simp [obsOfState] at hobs_node

end ObsModelCoreBridge

-- ============================================================================
-- B→M via the central ObsModelCore theorem
-- ============================================================================

/-- **Kuhn B→M for EFG via the central theorem.**
The `runDist` of the lifted behavioral profile equals the product mixed strategy
bound to `runDistPure`, provided the tree has no info-set repeats. -/
theorem kuhn_behavioral_to_mixed_runDist
    (σ : BehavioralProfile S) (t : GameTree S Outcome)
    (hnr : NoInfoSetRepeat t) (k : Nat) :
    let O := compiledCoreObs t
    O.runDist k (GameTheory.EFG.liftBehavioralProfileCore t σ) =
      (O.behavioralToMixedJoint (GameTheory.EFG.liftBehavioralProfileCore t σ)).bind
        (fun π => O.runDistPure k π) :=
  ObsModelCore.kuhn_behavioral_to_mixed
    (noNontrivialInfoStateRepeat_compiledCore t hnr)
    (GameTheory.EFG.liftBehavioralProfileCore t σ) k

/-- **Kuhn B→M for EFG at the `evalDist` level, via the central theorem.**
For any behavioral profile on a tree with no info-set repeats,
the `evalDist` equals the expected `evalDist` under the product mixed strategy. -/
theorem kuhn_behavioral_to_mixed_evalDist
    (σ : BehavioralProfile S) (t : GameTree S Outcome)
    (hnr : NoInfoSetRepeat t) :
    let O := compiledCoreObs t
    t.evalDist σ =
      (O.behavioralToMixedJoint
        (GameTheory.EFG.liftBehavioralProfileCore t σ)).bind
        (fun π => t.evalDist
          (pureToBehavioral
            (GameTheory.EFG.descendPureProfileCore t π))) := by
  let O := compiledCoreObs t
  let k := treeHeight t
  let β' := GameTheory.EFG.liftBehavioralProfileCore t σ
  have hrun := kuhn_behavioral_to_mixed_runDist σ t hnr k
  -- Apply adequacy to both sides
  have hleft :
      (O.runDist k β').bind (fun ss => (O.lastState ss).evalDist σ) =
        t.evalDist σ :=
    runDist_bind_evalDist_core t σ k
  have hper_pure :
      ∀ π, (O.runDistPure k π).bind (fun ss => (O.lastState ss).evalDist σ) =
        t.evalDist (pureToBehavioral (GameTheory.EFG.descendPureProfileCore t π)) := by
    intro π
    have hadq := runDistPure_bind_evalDist_core t π k
    -- Both sides agree on terminal states, and all reachable states are terminal
    calc
      (O.runDistPure k π).bind (fun ss => (O.lastState ss).evalDist σ)
        = (O.runDistPure k π).bind (fun ss =>
            (O.lastState ss).evalDist
              (pureToBehavioral (GameTheory.EFG.descendPureProfileCore t π))) := by
          refine Math.ProbabilityMassFunction.bind_congr_on_support
            (O.runDistPure k π) _ _ ?_
          intro ss hss
          have hss' :=
            lastState_terminal_of_pureRun_height t
              (by simpa [O, k, ObsModelCore.runDistPure_eq_pureRun] using hss)
          obtain ⟨z, hz⟩ := hss'
          simp [O, hz]
      _ = t.evalDist
            (pureToBehavioral (GameTheory.EFG.descendPureProfileCore t π)) := hadq
  have hright :
      ((O.behavioralToMixedJoint β').bind (O.runDistPure k)).bind
          (fun ss => (O.lastState ss).evalDist σ) =
        (O.behavioralToMixedJoint β').bind
          (fun π => t.evalDist
            (pureToBehavioral
              (GameTheory.EFG.descendPureProfileCore t π))) := by
    rw [PMF.bind_bind]
    refine Math.ProbabilityMassFunction.bind_congr_on_support
      (O.behavioralToMixedJoint β') _ _ ?_
    intro π _hπ
    exact hper_pure π
  calc
    t.evalDist σ =
      (O.runDist k β').bind (fun ss => (O.lastState ss).evalDist σ) :=
        hleft.symm
    _ = ((O.behavioralToMixedJoint β').bind (O.runDistPure k)).bind
        (fun ss => (O.lastState ss).evalDist σ) := by
      rw [hrun]
    _ = (O.behavioralToMixedJoint β').bind
        (fun π => t.evalDist
          (pureToBehavioral
            (GameTheory.EFG.descendPureProfileCore t π))) :=
      hright

-- ============================================================================
-- Tree-level Kuhn theorems (bridge from ObsModel to evalDist)
-- ============================================================================

/-- Kuhn's theorem (behavioral → mixed direction):
    For any behavioral profile σ and tree with no info-set repeats,
    there exists a distribution over flat profiles
    that induces the same outcome distribution.

Delegates to `kuhn_behavioral_to_mixed_evalDist` (the central ObsModel proof)
and transports the witness through `flatProfileEquivPureProfile`. -/
theorem kuhn_behavioral_to_mixed (σ : BehavioralProfile S) (t : GameTree S Outcome)
    (hnr : NoInfoSetRepeat t) :
    ∃ μ : PMF (FlatProfile S),
      μ.bind (fun s => t.evalDist (flatToBehavioral s)) = t.evalDist σ := by
  let O := compiledCoreObs t
  let β' := GameTheory.EFG.liftBehavioralProfileCore t σ
  have heval := kuhn_behavioral_to_mixed_evalDist σ t hnr
  let μ : PMF (FlatProfile S) :=
    (O.behavioralToMixedJoint β').map
      (fun π => flatProfileEquivPureProfile.symm
        (GameTheory.EFG.descendPureProfileCore t π))
  refine ⟨μ, ?_⟩
  simp only [μ, PMF.bind_map]
  have : (fun s => t.evalDist (flatToBehavioral s)) ∘
      (fun π => flatProfileEquivPureProfile.symm
        (GameTheory.EFG.descendPureProfileCore t π)) =
      fun π => t.evalDist (pureToBehavioral
        (GameTheory.EFG.descendPureProfileCore t π)) := by
    ext π; congr 1
  rw [this]
  exact heval.symm

/-- `kuhn_behavioral_to_mixed` under the original `PerfectRecall` assumption. -/
theorem kuhn_behavioral_to_mixed_pr (σ : BehavioralProfile S) (t : GameTree S Outcome)
    (hpr : PerfectRecall t) :
    ∃ μ : PMF (FlatProfile S),
      μ.bind (fun s => t.evalDist (flatToBehavioral s)) = t.evalDist σ :=
  kuhn_behavioral_to_mixed σ t (PerfectRecall_implies_NoInfoSetRepeat t hpr)

open GameTheory in
/-- Kuhn's theorem lifted to utility distributions (behavioral → mixed). -/
theorem kuhn_behavioral_to_mixed_udist (G : EFGGame)
    (σ : BehavioralProfile G.inf) (hpr : PerfectRecall G.tree) :
    ∃ μ : PMF (FlatProfile G.inf),
      μ.bind (fun s => G.toKernelGame.udist (flatToBehavioral s)) =
      G.toKernelGame.udist σ := by
  obtain ⟨μ, hμ⟩ := kuhn_behavioral_to_mixed_pr σ G.tree hpr
  exact ⟨μ, by
    simp only [KernelGame.udist, EFGGame.toKernelGame]
    rw [← hμ, PMF.bind_bind]⟩

private theorem kuhn_mixed_to_behavioral_core
    (t : GameTree S Outcome)
    (hpr : PerfectRecall t)
    (muP : MixedProfile S) :
    ∃ β : (compiledCoreObs t).BehavioralProfile,
      let O := compiledCoreObs t
      let k := treeHeight t
      let μ := GameTheory.EFG.liftMixedProfileCore t muP
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k) := by
  let O := compiledCoreObs t
  let k := treeHeight t
  let μ := GameTheory.EFG.liftMixedProfileCore t muP
  have hMass :
      ObsModelCore.StepMassInvariant O := by
    intro ss u π₁ π₂ h₁ h₂
    exact stepMassInvariant_compiledCore t π₁ π₂ h₁ h₂
  have hFactor :
      ObsModelCore.StepSupportFactorization O := by
    intro ss u π₀ π h₀
    exact stepSupportFactorization_compiledCore t π₀ π h₀
  obtain ⟨β, hβ⟩ :=
    ObsModelCore.kuhn_mixed_to_behavioral_semantic (O := O)
      hMass hFactor
      (fun i =>
        ObsModelCore.actionPosteriorLocal_of_obsLocalFeasibility (O := O)
          hMass i
          (by
            simpa [O] using
              obsLocalFeasibility_compiledCore t hpr i))
      μ k
  exact ⟨β, hβ⟩

private theorem compiledCore_runEq_to_evalDistEq
    (t : GameTree S Outcome)
    (muP : MixedProfile S)
    {β : (compiledCoreObs t).BehavioralProfile}
    (hβ :
      let O := compiledCoreObs t
      let k := treeHeight t
      let μ := GameTheory.EFG.liftMixedProfileCore t muP
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k)) :
    let σ := GameTheory.EFG.descendBehavioralProfileCore t β
    t.evalDist σ =
      (mixedProfileJoint muP).bind
        (fun pi => t.evalDist (pureToBehavioral pi)) := by
  let O := compiledCoreObs t
  let k := treeHeight t
  let μ := GameTheory.EFG.liftMixedProfileCore t muP
  let σ : BehavioralProfile S :=
    GameTheory.EFG.descendBehavioralProfileCore t β
  have hleft :
      (O.runDist k β).bind (fun ss => (O.lastState ss).evalDist σ) = t.evalDist σ := by
    simpa [O, k, σ, GameTheory.EFG.liftBehavioralProfileCore_descendBehavioralProfileCore] using
      runDist_bind_evalDist_core t σ k
  have hright :
      ((pmfPi μ).bind (O.runDistPure k)).bind
          (fun ss => (O.lastState ss).evalDist σ) =
        (mixedProfileJoint muP).bind
          (fun pi => t.evalDist (pureToBehavioral pi)) := by
    rw [PMF.bind_bind]
    calc
      (pmfPi μ).bind
          (fun π => (O.runDistPure k π).bind (fun ss => (O.lastState ss).evalDist σ))
        =
      (pmfPi μ).bind
          (fun π =>
            (O.runDistPure k π).bind
              (fun ss =>
                (O.lastState ss).evalDist
                  (pureToBehavioral
                    (GameTheory.EFG.descendPureProfileCore
                      t π)))) := by
            refine Math.ProbabilityMassFunction.bind_congr_on_support (pmfPi μ) _ _ ?_
            intro π _hπ
            refine Math.ProbabilityMassFunction.bind_congr_on_support (O.runDistPure k π) _ _ ?_
            intro ss hss
            have hss' :
                Math.ParameterizedChain.pureRun (O.pureStep) O.init k π ss ≠ 0 := by
              simpa [O, k, ObsModelCore.runDistPure_eq_pureRun] using hss
            obtain ⟨z, hz⟩ :=
              lastState_terminal_of_pureRun_height
                t
                (by simpa [O, k] using hss')
            simp [O, hz]
      _ =
        (pmfPi μ).bind
          (fun π =>
            t.evalDist
              (pureToBehavioral
                (GameTheory.EFG.descendPureProfileCore
                  t π))) := by
          refine Math.ProbabilityMassFunction.bind_congr_on_support (pmfPi μ) _ _ ?_
          intro π _hπ
          simpa [O, k] using
            runDistPure_bind_evalDist_core t π k
      _ =
        (Math.ProbabilityMassFunction.pushforward
          (mixedProfileJoint muP)
          (GameTheory.EFG.liftPureProfileCore t)).bind
            (fun π =>
              t.evalDist
                (pureToBehavioral
                  (GameTheory.EFG.descendPureProfileCore
                    t π))) := by
          rw [liftMixedProfileCore_joint t muP]
      _ =
        (mixedProfileJoint muP).bind
          (fun pi => t.evalDist (pureToBehavioral pi)) := by
          simp [Math.ProbabilityMassFunction.pushforward,
            GameTheory.EFG.descendPureProfileCore_liftPureProfileCore]
  calc
    t.evalDist σ =
      (O.runDist k β).bind (fun ss => (O.lastState ss).evalDist σ) := by
        symm
        exact hleft
    _ =
      ((pmfPi μ).bind (O.runDistPure k)).bind
        (fun ss => (O.lastState ss).evalDist σ) := by
          simpa [O, k, μ] using congrArg
            (fun d => d.bind (fun ss => (O.lastState ss).evalDist σ)) hβ
    _ =
      (mixedProfileJoint muP).bind
        (fun pi => t.evalDist (pureToBehavioral pi)) := hright

/-- **Kuhn's theorem (mixed → behavioral direction).**
    For any game tree with perfect recall and any mixed strategy profile,
    there exists a behavioral strategy profile that induces the same
    outcome distribution. -/
theorem kuhn_mixed_to_behavioral
    (t : GameTree S Outcome)
    (hpr : PerfectRecall t)
    (muP : MixedProfile S) :
    ∃ sigma : BehavioralProfile S,
      t.evalDist sigma =
      (mixedProfileJoint muP).bind
        (fun pi => t.evalDist
          (pureToBehavioral pi)) := by
  obtain ⟨β, hβ⟩ :=
    kuhn_mixed_to_behavioral_core t hpr muP
  let σ : BehavioralProfile S :=
    GameTheory.EFG.descendBehavioralProfileCore t β
  refine ⟨σ, ?_⟩
  simpa [σ] using
    compiledCore_runEq_to_evalDistEq t muP hβ

open GameTheory in
/-- Kuhn's theorem lifted to utility distributions (mixed → behavioral). -/
theorem kuhn_mixed_to_behavioral_udist (G : EFGGame)
    (hpr : PerfectRecall G.tree) (muP : MixedProfile G.inf) :
    ∃ σ : BehavioralProfile G.inf,
      G.toKernelGame.udist σ =
      (mixedProfileJoint (S := G.inf) muP).bind
        (fun pi => G.toKernelGame.udist (pureToBehavioral pi)) := by
  obtain ⟨σ, hσ⟩ := kuhn_mixed_to_behavioral G.tree hpr muP
  exact ⟨σ, by
    simp only [KernelGame.udist, EFGGame.toKernelGame]
    rw [hσ, PMF.bind_bind]⟩

end EFG
