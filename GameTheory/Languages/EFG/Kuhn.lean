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

instance : Fintype (FlatIdx S) :=
  Sigma.instFintype

instance : DecidableEq (FlatIdx S) :=
  Sigma.instDecidableEqSigma

instance : Fintype (FlatProfile S) :=
  Pi.instFintype

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
    Fintype ((compiledCoreObs (S := S) (Outcome := Outcome) t).InfoState i) := by
  dsimp [compiledCoreObs, compileObsCoreModel, ObsModelCore.InfoState]
  infer_instance

@[simp] theorem projectStates_compiledCore
    (i : S.Player) (ss : List (GameTree S Outcome)) :
    (compiledCoreObs (S := S) (Outcome := Outcome) t).projectStates i ss =
      obsOfState (S := S) (Outcome := Outcome) i
        ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss) := by
  induction ss with
  | nil =>
      simp [ObsModelCore.projectStates, ObsModelCore.projectStatesFrom, ObsModelCore.lastState,
        compiledCoreObs, compileObsCoreModel, obsOfState]
  | cons s ss ih =>
      cases ss with
      | nil =>
          simp [ObsModelCore.projectStates, ObsModelCore.projectStatesFrom, ObsModelCore.lastState,
            compiledCoreObs, compileObsCoreModel, obsOfState]
      | cons t ts =>
          simpa [ObsModelCore.projectStates, ObsModelCore.projectStatesFrom, ObsModelCore.lastState,
            compiledCoreObs, compileObsCoreModel, obsOfState] using ih

/-- Product mixed distribution over lifted core local strategies is the
pushforward of the native mixed-profile joint law along `liftPureProfileCore`. -/
theorem liftMixedProfileCore_joint
    (μ : MixedProfile S) :
    pmfPi (liftMixedProfileCore (S := S) (Outcome := Outcome) t μ) =
      Math.ProbabilityMassFunction.pushforward (mixedProfileJoint (S := S) μ)
        (liftPureProfileCore (S := S) (Outcome := Outcome) t) := by
  classical
  rw [mixedProfileJoint]
  exact (Math.PMFProduct.pmfPi_push_coordwise μ
    (fun i => pureStrategyEquivCoreLocalStrategy (S := S) (Outcome := Outcome) t i)).symm

/-- Closed form of one compiled-core step at an explicit tree state. -/
private theorem compiledCore_step_eq
    (s : GameTree S Outcome)
    (a : (compiledCoreObs (S := S) (Outcome := Outcome) t).JointActionAt s) :
    (compiledCoreObs (S := S) (Outcome := Outcome) t).step s a =
      match s with
      | .terminal z => PMF.pure (.terminal z)
      | .chance _k μ _hk next => μ.map next
      | .decision (p := p) I next =>
          PMF.pure
            (next
              (cast
                (compiledAct_eq_of_some S p
                  (show obsOfState (S := S) (Outcome := Outcome) p (.decision I next) = some I by
                    simp [obsOfState]))
                (a p))) := by
  cases s with
  | terminal z => rfl
  | chance k μ hk next => rfl
  | decision I next => rfl

@[simp] private theorem obsOfState_decision_eq_some
    {p : S.Player} (I : S.Infoset p) (next : S.Act I → GameTree S Outcome) :
    obsOfState (S := S) (Outcome := Outcome) p (.decision I next) = some I := by
  simp [obsOfState]

private theorem compiledCore_step_of_decision
    {s : GameTree S Outcome}
    {p : S.Player} (I : S.Infoset p)
    (next : S.Act I → GameTree S Outcome)
    (hs : s = .decision I next)
    (a : (compiledCoreObs (S := S) (Outcome := Outcome) t).JointActionAt s) :
    (compiledCoreObs (S := S) (Outcome := Outcome) t).step s a =
      PMF.pure
        (next
          (cast
            (compiledAct_eq_of_some S p
              (obsOfState_decision_eq_some (S := S) (Outcome := Outcome) I next))
            (hs ▸ a p))) := by
  cases hs
  simp [ObsModelCore.step, compileObsCoreModel, treeStepPMF, obsOfState]

private theorem compiledCore_step_of_terminal
    {s : GameTree S Outcome} {z : Outcome}
    (hs : s = .terminal z)
    (a : (compiledCoreObs (S := S) (Outcome := Outcome) t).JointActionAt s) :
    (compiledCoreObs (S := S) (Outcome := Outcome) t).step s a = PMF.pure (.terminal z) := by
  cases hs
  simp [compiledCore_step_eq]

private theorem compiledCore_step_of_chance
    {s : GameTree S Outcome}
    {k : Nat} {μ : PMF (Fin k)} {hk : 0 < k}
    (next : Fin k → GameTree S Outcome)
    (hs : s = .chance k μ hk next)
    (a : (compiledCoreObs (S := S) (Outcome := Outcome) t).JointActionAt s) :
    (compiledCoreObs (S := S) (Outcome := Outcome) t).step s a = μ.map next := by
  cases hs
  simp [compiledCore_step_eq]

/-- In the honest core compilation, projecting a pure profile action to the
current step just evaluates it at the current observation cell. -/
@[simp] theorem castProfileAction_compiledCore
    (π : ObsModelCore.PureProfile (compiledCoreObs (S := S) (Outcome := Outcome) t))
    (i : S.Player) (ss : List (GameTree S Outcome)) :
    (compiledCoreObs (S := S) (Outcome := Outcome) t).castProfileAction i ss
      (π i ((compiledCoreObs (S := S) (Outcome := Outcome) t).projectStates i ss)) =
        π i (obsOfState (S := S) (Outcome := Outcome) i
          ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss)) := by
  induction ss with
  | nil =>
      simp [ObsModelCore.castProfileAction, ObsModelCore.projectStates,
        ObsModelCore.projectStatesFrom, ObsModelCore.lastState,
        compileObsCoreModel, obsOfState]
  | cons s ss ih =>
      cases ss with
      | nil =>
          simp [ObsModelCore.castProfileAction, ObsModelCore.projectStates,
            ObsModelCore.projectStatesFrom, ObsModelCore.lastState,
            compileObsCoreModel, obsOfState]
      | cons t ts =>
          simpa [ObsModelCore.castProfileAction, ObsModelCore.projectStates,
            ObsModelCore.projectStatesFrom, ObsModelCore.lastState,
            compileObsCoreModel, obsOfState] using ih

@[simp] theorem castJointAction_compiledCore
    (π : ObsModelCore.PureProfile (compiledCoreObs (S := S) (Outcome := Outcome) t))
    (ss : List (GameTree S Outcome)) :
    (compiledCoreObs (S := S) (Outcome := Outcome) t).castJointAction ss
      (fun i => π i ((compiledCoreObs (S := S) (Outcome := Outcome) t).projectStates i ss)) =
        (fun i =>
          π i (obsOfState (S := S) (Outcome := Outcome) i
            ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss))) := by
  funext i
  exact castProfileAction_compiledCore (S := S) (Outcome := Outcome) (t := t) π i ss

/-- Closed form of pure one-step execution in the honest core compilation. -/
theorem pureStep_compiledCore_eq
    (π : ObsModelCore.PureProfile (compiledCoreObs (S := S) (Outcome := Outcome) t))
    (ss : List (GameTree S Outcome)) :
    (compiledCoreObs (S := S) (Outcome := Outcome) t).pureStep π ss =
      match (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss with
      | .terminal z => PMF.pure (.terminal z)
      | .chance _k μ _hk next => μ.map next
      | .decision (p := p) I next => PMF.pure (next (π p (some I))) := by
  let O := compiledCoreObs (S := S) (Outcome := Outcome) t
  rw [ObsModelCore.pureStep_eq]
  have hcast :
      (fun i =>
        O.currentObs_projectStates i ss ▸ π i (O.projectStates i ss)) =
        (fun i => O.castProfileAction i ss (π i (O.projectStates i ss))) := by
    rfl
  rw [hcast]
  have hact :
      (fun i => O.castProfileAction i ss (π i (O.projectStates i ss))) =
        (fun i => π i (obsOfState (S := S) (Outcome := Outcome) i (O.lastState ss))) := by
    funext i
    exact castProfileAction_compiledCore (S := S) (Outcome := Outcome) (t := t) π i ss
  rw [hact]
  have hstep :=
    compiledCore_step_eq (S := S) (Outcome := Outcome) (t := t)
      (O.lastState ss)
      (fun i => π i (obsOfState (S := S) (Outcome := Outcome) i (O.lastState ss)))
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
              (obsOfState_decision_eq_some (S := S) (Outcome := Outcome) I next))
            (π p (if p = p then some I else none)) =
          π p (some I) := by
        grind
      exact congrArg PMF.pure (congrArg next hcast')

/-- Closed form of behavioral one-step execution in the honest core compilation. -/
private theorem stepDist_compiledCore_eq_terminal
    (σ : BehavioralProfile S) (ss : List (GameTree S Outcome))
    {z : Outcome}
    (hs : (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss = .terminal z) :
    (compiledCoreObs (S := S) (Outcome := Outcome) t).stepDist
      (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ) ss =
      PMF.pure (.terminal z) := by
  dsimp [ObsModelCore.stepDist, ObsModelCore.jointActionDist]
  have hf :
      (fun a =>
        (compiledCoreObs (S := S) (Outcome := Outcome) t).step
          ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss)
          ((compiledCoreObs (S := S) (Outcome := Outcome) t).castJointAction ss a)) =
      (fun _ => PMF.pure (.terminal z)) := by
    funext a
    exact compiledCore_step_of_terminal (S := S) (Outcome := Outcome) (t := t) hs
      ((compiledCoreObs (S := S) (Outcome := Outcome) t).castJointAction ss a)
  rw [hf]
  simp

private theorem stepDist_compiledCore_eq_chance
    (σ : BehavioralProfile S) (ss : List (GameTree S Outcome))
    {k : Nat} {μ : PMF (Fin k)} {hk : 0 < k}
    (next : Fin k → GameTree S Outcome)
    (hs : (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss = .chance k μ hk next) :
    (compiledCoreObs (S := S) (Outcome := Outcome) t).stepDist
      (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ) ss =
      μ.map next := by
  dsimp [ObsModelCore.stepDist, ObsModelCore.jointActionDist]
  have hf :
      (fun a =>
        (compiledCoreObs (S := S) (Outcome := Outcome) t).step
          ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss)
          ((compiledCoreObs (S := S) (Outcome := Outcome) t).castJointAction ss a)) =
      (fun _ => μ.map next) := by
    funext a
    exact compiledCore_step_of_chance (S := S) (Outcome := Outcome) (t := t) next hs
      ((compiledCoreObs (S := S) (Outcome := Outcome) t).castJointAction ss a)
  rw [hf]
  simp

private theorem stepDist_compiledCore_eq_decision
    (σ : BehavioralProfile S) (ss : List (GameTree S Outcome))
    {p : S.Player} (I : S.Infoset p)
    (next : S.Act I → GameTree S Outcome)
    (hs : (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss = .decision I next) :
    (compiledCoreObs (S := S) (Outcome := Outcome) t).stepDist
      (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ) ss =
      (σ p I).bind (fun a => PMF.pure (next a)) := by
  let O := compiledCoreObs (S := S) (Outcome := Outcome) t
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
      compiledCore_step_of_decision (S := S) (Outcome := Outcome) (t := t) I next hs
        (O.castJointAction ss a)
    grind [obsOfState, ObsModelCore.castJointAction, cast_cast]
  rw [hf]
  rw [Math.ProbabilityMassFunction.bind_pure_eq_pushforward]
  have hcomp :
      Math.ProbabilityMassFunction.pushforward
        (pmfPi (fun i =>
          liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ i
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
            liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ i
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
          liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ i
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
          liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ i
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
            liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ i
              (O.projectStates i ss)))
          (fun a =>
            cast
              (compiledAct_eq_of_some S p
                (show O.projectStates p ss = some I by simp [O, hs, obsOfState]))
              (a p)) =
        Math.ProbabilityMassFunction.pushforward
          (Math.ProbabilityMassFunction.pushforward
            (pmfPi (fun i =>
              liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ i
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
            liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ i
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
              (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ p v)
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
    (compiledCoreObs (S := S) (Outcome := Outcome) t).stepDist
      (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ) ss =
      match (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss with
      | .terminal z => PMF.pure (.terminal z)
      | .chance _k μ _hk next => μ.map next
      | .decision (p := p) I next => (σ p I).bind (fun a => PMF.pure (next a)) := by
  match hs : (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss with
  | .terminal z =>
      exact stepDist_compiledCore_eq_terminal (S := S) (Outcome := Outcome) (t := t) σ ss hs
  | .chance k μ hk next =>
      exact stepDist_compiledCore_eq_chance (S := S) (Outcome := Outcome) (t := t) σ ss next hs
  | .decision (p := p) I next =>
      exact stepDist_compiledCore_eq_decision (S := S) (Outcome := Outcome) (t := t) σ ss I next hs

/-- The honest core EFG compilation has step-mass invariance. -/
theorem stepMassInvariant_compiledCore :
    ObsModelCore.StepMassInvariant
      (compiledCoreObs (S := S) (Outcome := Outcome) t) := by
  intro ss dst π₁ π₂ h₁ h₂
  cases hlast : (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss with
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
      (compiledCoreObs (S := S) (Outcome := Outcome) t) := by
  intro ss dst π₀ π h₀
  cases hlast : (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss with
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

private theorem bind_pushforward_lastState_evalDist
    (σ : BehavioralProfile S) (ss : List (GameTree S Outcome)) (d : PMF (GameTree S Outcome)) :
    (Math.ProbabilityMassFunction.pushforward d (fun u => ss ++ [u])).bind
      (fun ss' =>
        ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss').evalDist σ) =
      d.bind (fun u => u.evalDist σ) := by
  simp [Math.ProbabilityMassFunction.pushforward, PMF.bind_bind, ObsModelCore.lastState]

/-- One-step adequacy for the honest core compilation. -/
theorem stepDist_bind_evalDist_core
    (σ : BehavioralProfile S) (ss : List (GameTree S Outcome)) :
    ((compiledCoreObs (S := S) (Outcome := Outcome) t).stepDist
      (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ) ss).bind
        (fun u => u.evalDist σ) =
      ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss).evalDist σ := by
  rw [stepDist_compiledCore_eq (S := S) (Outcome := Outcome) t σ ss]
  cases hlast : (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss with
  | terminal z =>
      simp
  | chance k μ hk next =>
      simp [PMF.map, PMF.bind_bind]
  | decision I next =>
      simp [GameTree.evalDist]

/-- Bounded-run adequacy for behavioral profiles on the honest core compilation. -/
theorem runDist_bind_evalDist_core
    (σ : BehavioralProfile S) (k : Nat) :
    ((compiledCoreObs (S := S) (Outcome := Outcome) t).runDist k
      (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ)).bind
        (fun ss => ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss).evalDist σ) =
      t.evalDist σ := by
  induction k with
  | zero =>
      simp [compiledCoreObs, compileObsCoreModel, ObsModelCore.runDist, ObsModelCore.lastState]
  | succ k ih =>
      rw [ObsModelCore.runDist]
      calc
        (((compiledCoreObs (S := S) (Outcome := Outcome) t).runDist k
            (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ)).bind
            (fun ss =>
              Math.ProbabilityMassFunction.pushforward
                ((compiledCoreObs (S := S) (Outcome := Outcome) t).stepDist
                  (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ) ss)
                (fun u => ss ++ [u]))).bind
              (fun ss' =>
                ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss').evalDist σ)
            =
          ((compiledCoreObs (S := S) (Outcome := Outcome) t).runDist k
            (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ)).bind
            (fun ss =>
              (Math.ProbabilityMassFunction.pushforward
                ((compiledCoreObs (S := S) (Outcome := Outcome) t).stepDist
                  (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ) ss)
                (fun u => ss ++ [u])).bind
                  (fun ss' =>
                    ((compiledCoreObs (S := S)
                     (Outcome := Outcome) t).lastState ss').evalDist σ)) := by
              rw [PMF.bind_bind]
        _ =
          ((compiledCoreObs (S := S) (Outcome := Outcome) t).runDist k
            (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ)).bind
            (fun ss =>
              ((compiledCoreObs (S := S) (Outcome := Outcome) t).stepDist
                (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ) ss).bind
                  (fun u => u.evalDist σ)) := by
              refine Math.ProbabilityMassFunction.bind_congr_on_support
                ((compiledCoreObs (S := S) (Outcome := Outcome) t).runDist k
                  (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ))
                _ _ ?_
              intro ss _
              exact bind_pushforward_lastState_evalDist
                (S := S) (Outcome := Outcome) (t := t) σ ss
                ((compiledCoreObs (S := S) (Outcome := Outcome) t).stepDist
                  (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ) ss)
        _ =
          ((compiledCoreObs (S := S) (Outcome := Outcome) t).runDist k
            (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ)).bind
            (fun ss =>
              ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss).evalDist σ) := by
              refine Math.ProbabilityMassFunction.bind_congr_on_support
                ((compiledCoreObs (S := S) (Outcome := Outcome) t).runDist k
                  (liftBehavioralProfileCore (S := S) (Outcome := Outcome) t σ))
                _ _ ?_
              intro ss _
              exact stepDist_bind_evalDist_core (S := S) (Outcome := Outcome) (t := t) σ ss
        _ = t.evalDist σ := ih

@[simp] theorem liftBehavioralProfileCore_pure_descend
    (π : ObsModelCore.PureProfile (compiledCoreObs (S := S) (Outcome := Outcome) t)) :
    liftBehavioralProfileCore (S := S) (Outcome := Outcome) t
      (pureToBehavioral (descendPureProfileCore (S := S) (Outcome := Outcome) t π)) =
      (compiledCoreObs (S := S) (Outcome := Outcome) t).pureToBehavioral π := by
  funext i v
  cases v <;> rfl

/-- Pure-profile adequacy for the honest core compilation. -/
theorem runDistPure_bind_evalDist_core
    (π : ObsModelCore.PureProfile (compiledCoreObs (S := S) (Outcome := Outcome) t))
    (k : Nat) :
    ((compiledCoreObs (S := S) (Outcome := Outcome) t).runDistPure k π).bind
        (fun ss =>
          ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss).evalDist
            (pureToBehavioral (descendPureProfileCore (S := S) (Outcome := Outcome) t π))) =
      t.evalDist (pureToBehavioral (descendPureProfileCore (S := S) (Outcome := Outcome) t π)) := by
  simpa [ObsModelCore.runDistPure, liftBehavioralProfileCore_pure_descend]
    using runDist_bind_evalDist_core (S := S) (Outcome := Outcome) t
      (pureToBehavioral (descendPureProfileCore (S := S) (Outcome := Outcome) t π)) k

private def HistoryCompatibleCore
    (π : ObsModelCore.PureProfile (compiledCoreObs (S := S) (Outcome := Outcome) t))
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
      (hterm : ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss) = .terminal z) :
      HistorySupportTrace t (ss ++ [.terminal z]) h
  | snoc {ss : List (GameTree S Outcome)} {h : List (HistoryStep S)}
      {u : GameTree S Outcome} {ℓ : HistoryStep S}
      (hw : HistorySupportTrace t ss h)
      (hstep : HistorySupportStep (S := S) (Outcome := Outcome) ℓ
        ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss) u) :
      HistorySupportTrace t (ss ++ [u]) (h ++ [ℓ])

private theorem historySupportTrace_nonempty
    {ss : List (GameTree S Outcome)} {h : List (HistoryStep S)}
    (hw : HistorySupportTrace (S := S) (Outcome := Outcome) t ss h) :
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
    (hw : HistorySupportTrace (S := S) (Outcome := Outcome) t ss h) :
    0 < ss.length := by
  exact List.length_pos_iff_ne_nil.mpr
    (historySupportTrace_nonempty (S := S) (Outcome := Outcome) (t := t) hw)

private theorem reachBy_singleton_of_historySupportStep
    {src dst : GameTree S Outcome} {ℓ : HistoryStep S}
    (hstep : HistorySupportStep (S := S) (Outcome := Outcome) ℓ src dst) :
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
    (hw : HistorySupportTrace (S := S) (Outcome := Outcome) t ss h) :
    ReachBy h t ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss) := by
  induction hw with
  | init =>
      simp [compiledCoreObs, compileObsCoreModel, ObsModelCore.lastState]
  | @stutter ss h z hw hterm ih =>
      have ih' : ReachBy h t (.terminal z) := by
        simpa [hterm] using ih
      have hlast :
          (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState (ss ++ [.terminal z]) =
            .terminal z := by
        simp [ObsModelCore.lastState]
      exact hlast.symm ▸ ih'
  | @snoc ss h u ℓ hw hstep ih =>
      have htail : ReachBy [ℓ]
          ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss) u :=
        reachBy_singleton_of_historySupportStep (S := S) (Outcome := Outcome) hstep
      have hcat := ReachBy_append ih htail
      simpa [compiledCoreObs, compileObsCoreModel, ObsModelCore.lastState] using hcat

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
    {π₀ : ObsModelCore.PureProfile (compiledCoreObs (S := S) (Outcome := Outcome) t)}
    {πᵢ : (compiledCoreObs (S := S) (Outcome := Outcome) t).LocalStrategy i}
    {h : List (HistoryStep S)}
    (hcomp : HistoryCompatibleCore (S := S) (Outcome := Outcome) (t := t)
      (Function.update π₀ i πᵢ) h) :
    ∀ tok ∈ playerHistory S i h, πᵢ (some tok.1) = tok.2 := by
  intro tok htok
  have hm : HistoryStep.action i tok.1 tok.2 ∈ h :=
    action_mem_of_playerHistory_mem (S := S) htok
  simpa [HistoryCompatibleCore, Function.update_self] using hcomp hm

private theorem historyCompatibleCore_update_of_playerHistory
    {i : S.Player}
    {π₀ : ObsModelCore.PureProfile (compiledCoreObs (S := S) (Outcome := Outcome) t)}
    {πᵢ : (compiledCoreObs (S := S) (Outcome := Outcome) t).LocalStrategy i}
    {h : List (HistoryStep S)}
    (hbase : HistoryCompatibleCore (S := S) (Outcome := Outcome) (t := t) π₀ h)
    (hpi : ∀ tok ∈ playerHistory S i h, πᵢ (some tok.1) = tok.2) :
    HistoryCompatibleCore (S := S) (Outcome := Outcome) (t := t)
      (Function.update π₀ i πᵢ) h := by
  intro q J a hm
  by_cases hq : q = i
  · subst hq
    simpa [Function.update_self] using
      hpi ⟨J, a⟩ (playerHistory_mem_of_action_mem (S := S) hm)
  · simpa [HistoryCompatibleCore, Function.update_of_ne hq] using hbase hm

private theorem pureRun_nonzero_to_historySupportTrace
    {n : Nat}
    {π : ObsModelCore.PureProfile (compiledCoreObs (S := S) (Outcome := Outcome) t)}
    {ss : List (GameTree S Outcome)}
    (h : Math.ParameterizedChain.pureRun
      ((compiledCoreObs (S := S) (Outcome := Outcome) t).pureStep)
      ((compiledCoreObs (S := S) (Outcome := Outcome) t).init) n π ss ≠ 0) :
    ∃ hist,
      Nonempty (HistorySupportTrace (S := S) (Outcome := Outcome) t ss hist) ∧
      HistoryCompatibleCore (S := S) (Outcome := Outcome) (t := t) π hist := by
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
              ((compiledCoreObs (S := S) (Outcome := Outcome) t).pureStep)
              ((compiledCoreObs (S := S) (Outcome := Outcome) t).init) n π pfx ≠ 0 := by
            rw [List.concat_eq_append, Math.ParameterizedChain.pureRun_succ_append] at h
            exact left_ne_zero_of_mul h
        have hu :
            ((compiledCoreObs (S := S) (Outcome := Outcome) t).pureStep π pfx) u ≠ 0 := by
            rw [List.concat_eq_append, Math.ParameterizedChain.pureRun_succ_append] at h
            exact right_ne_zero_of_mul h
        rcases ih hp with ⟨hist, ⟨hh⟩, hcompat⟩
        cases hlast : (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState pfx with
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
                    (show HistorySupportStep (S := S) (Outcome := Outcome)
                      (HistoryStep.chance k b)
                      ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState pfx)
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
                    (show HistorySupportStep (S := S) (Outcome := Outcome)
                      (HistoryStep.action p I (π p (some I)))
                      ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState pfx)
                      (next (π p (some I))) from ⟨next, hlast, rfl⟩))⟩
            · intro q J a hm
              simp only [List.mem_append, List.mem_singleton] at hm
              rcases hm with hm | hm
              · exact hcompat hm
              · cases hm
                rfl

private theorem historySupportTrace_pureRun_nonzero
    {π : ObsModelCore.PureProfile (compiledCoreObs (S := S) (Outcome := Outcome) t)}
    {ss : List (GameTree S Outcome)} {hist : List (HistoryStep S)}
    (hw : HistorySupportTrace (S := S) (Outcome := Outcome) t ss hist)
    (hcompat : HistoryCompatibleCore (S := S) (Outcome := Outcome) (t := t) π hist) :
    Math.ParameterizedChain.pureRun
      ((compiledCoreObs (S := S) (Outcome := Outcome) t).pureStep)
      ((compiledCoreObs (S := S) (Outcome := Outcome) t).init) (ss.length - 1) π ss ≠ 0 := by
  induction hw with
  | init =>
      simp [Math.ParameterizedChain.pureRun, compiledCoreObs, compileObsCoreModel]
  | @stutter ss hist z hw hterm ih =>
      have hu :
          ((compiledCoreObs (S := S) (Outcome := Outcome) t).pureStep π ss)
            (.terminal z) ≠ 0 := by
        simp [pureStep_compiledCore_eq, hterm]
      have hlen : 0 < ss.length :=
        historySupportTrace_length_pos (S := S) (Outcome := Outcome) (t := t) hw
      have hslen : ss.length - 1 + 1 = ss.length := by
        omega
      have hmul :
          Math.ParameterizedChain.pureRun
            ((compiledCoreObs (S := S) (Outcome := Outcome) t).pureStep)
            ((compiledCoreObs (S := S) (Outcome := Outcome) t).init)
            ((ss.length - 1) + 1) π (ss ++ [.terminal z]) ≠ 0 := by
        rw [Math.ParameterizedChain.pureRun_succ_append]
        exact mul_ne_zero (ih hcompat) hu
      simpa [List.length_append, hslen] using hmul
  | @snoc ss hist u ℓ hw hstep ih =>
      have hcompat_prev :
          HistoryCompatibleCore (S := S) (Outcome := Outcome) (t := t) π hist := by
        intro p I a hm
        exact hcompat (by simp [hm])
      have hp := ih hcompat_prev
      have hu :
          ((compiledCoreObs (S := S) (Outcome := Outcome) t).pureStep π ss) u ≠ 0 := by
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
        historySupportTrace_length_pos (S := S) (Outcome := Outcome) (t := t) hw
      have hslen : ss.length - 1 + 1 = ss.length := by
        omega
      have hmul :
          Math.ParameterizedChain.pureRun
            ((compiledCoreObs (S := S) (Outcome := Outcome) t).pureStep)
            ((compiledCoreObs (S := S) (Outcome := Outcome) t).init)
            ((ss.length - 1) + 1) π (ss ++ [u]) ≠ 0 := by
        rw [Math.ParameterizedChain.pureRun_succ_append]
        exact mul_ne_zero hp hu
      simpa [List.length_append, hslen] using hmul

private theorem exists_decision_of_projectStates_eq_some
    {i : S.Player} {I : S.Infoset i} {ss : List (GameTree S Outcome)}
    (h : (compiledCoreObs (S := S) (Outcome := Outcome) t).projectStates i ss = some I) :
    ∃ next : S.Act I → GameTree S Outcome,
      (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss = .decision I next := by
  cases hlast : (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss with
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
        ((compiledCoreObs (S := S) (Outcome := Outcome) t).currentObs i
          ((compiledCoreObs (S := S) (Outcome := Outcome) t).projectStates i ss)))) :
    ∃ I : S.Infoset i,
      (compiledCoreObs (S := S) (Outcome := Outcome) t).projectStates i ss = some I := by
  cases hlast : (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss with
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
      (compiledCoreObs (S := S) (Outcome := Outcome) t) i := by
  intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ hsub πᵢ
  obtain ⟨I, hI₁⟩ :=
    infoState_some_of_not_subsingleton (S := S) (Outcome := Outcome) (t := t)
      (i := i) (ss := ss₁) hsub
  have hI₂ :
      (compiledCoreObs (S := S) (Outcome := Outcome) t).projectStates i ss₂ = some I := by
    exact hobs.symm ▸ hI₁
  obtain ⟨next₁, hdec₁⟩ :=
    exists_decision_of_projectStates_eq_some (S := S) (Outcome := Outcome) (t := t) hI₁
  obtain ⟨next₂, hdec₂⟩ :=
    exists_decision_of_projectStates_eq_some (S := S) (Outcome := Outcome) (t := t) hI₂
  obtain ⟨hist₁, ⟨hsupp₁⟩, hcompat₁⟩ :=
    pureRun_nonzero_to_historySupportTrace (S := S) (Outcome := Outcome) (t := t) h₁
  obtain ⟨hist₂, ⟨hsupp₂⟩, hcompat₂⟩ :=
    pureRun_nonzero_to_historySupportTrace (S := S) (Outcome := Outcome) (t := t) h₂
  have hreach₁ : ReachBy hist₁ t (.decision I next₁) := by
    simpa [hdec₁] using
      (historySupportTrace_reachBy (S := S) (Outcome := Outcome) (t := t) hsupp₁)
  have hreach₂ : ReachBy hist₂ t (.decision I next₂) := by
    simpa [hdec₂] using
      (historySupportTrace_reachBy (S := S) (Outcome := Outcome) (t := t) hsupp₂)
  have hplayer :
      playerHistory S i hist₁ = playerHistory S i hist₂ := by
    exact hpr hist₁ hist₂ I next₁ next₂ hreach₁ hreach₂
  constructor
  · intro hupd₁
    obtain ⟨hist₁', ⟨hsupp₁'⟩, hcompat₁'⟩ :=
      pureRun_nonzero_to_historySupportTrace (S := S) (Outcome := Outcome) (t := t) hupd₁
    have hreach₁' : ReachBy hist₁' t (.decision I next₁) := by
      simpa [hdec₁] using
        (historySupportTrace_reachBy (S := S) (Outcome := Outcome) (t := t) hsupp₁')
    have hplayer₁' :
        playerHistory S i hist₁' = playerHistory S i hist₁ := by
      exact hpr hist₁' hist₁ I next₁ next₁ hreach₁' hreach₁
    have hagree₁ :
        ∀ tok ∈ playerHistory S i hist₁, πᵢ (some tok.1) = tok.2 := by
      intro tok htok
      have htok' : tok ∈ playerHistory S i hist₁' := by
        simpa [hplayer₁'] using htok
      exact playerHistory_agrees_of_historyCompatibleCore_update
        (S := S) (Outcome := Outcome) (t := t) hcompat₁' tok htok'
    have hagree₂ :
        ∀ tok ∈ playerHistory S i hist₂, πᵢ (some tok.1) = tok.2 := by
      intro tok htok
      have htok₁ : tok ∈ playerHistory S i hist₁ := by
        simpa [hplayer] using htok
      exact hagree₁ tok htok₁
    have hcompat₂' :=
      historyCompatibleCore_update_of_playerHistory
        (S := S) (Outcome := Outcome) (t := t) hcompat₂ hagree₂
    have hlen₂ : ss₂.length - 1 = n₂ := by
      have := Math.ParameterizedChain.pureRun_length
        ((compiledCoreObs (S := S) (Outcome := Outcome) t).pureStep)
        ((compiledCoreObs (S := S) (Outcome := Outcome) t).init) n₂ π₀' ss₂ h₂
      omega
    simpa [hlen₂] using
      historySupportTrace_pureRun_nonzero
        (S := S) (Outcome := Outcome) (t := t) hsupp₂ hcompat₂'
  · intro hupd₂
    obtain ⟨hist₂', ⟨hsupp₂'⟩, hcompat₂'⟩ :=
      pureRun_nonzero_to_historySupportTrace (S := S) (Outcome := Outcome) (t := t) hupd₂
    have hreach₂' : ReachBy hist₂' t (.decision I next₂) := by
      simpa [hdec₂] using
        (historySupportTrace_reachBy (S := S) (Outcome := Outcome) (t := t) hsupp₂')
    have hplayer₂' :
        playerHistory S i hist₂' = playerHistory S i hist₂ := by
      exact hpr hist₂' hist₂ I next₂ next₂ hreach₂' hreach₂
    have hagree₂ :
        ∀ tok ∈ playerHistory S i hist₂, πᵢ (some tok.1) = tok.2 := by
      intro tok htok
      have htok' : tok ∈ playerHistory S i hist₂' := by
        simpa [hplayer₂'] using htok
      exact playerHistory_agrees_of_historyCompatibleCore_update
        (S := S) (Outcome := Outcome) (t := t) hcompat₂' tok htok'
    have hagree₁ :
        ∀ tok ∈ playerHistory S i hist₁, πᵢ (some tok.1) = tok.2 := by
      intro tok htok
      have htok₂ : tok ∈ playerHistory S i hist₂ := by
        simpa [hplayer] using htok
      exact hagree₂ tok htok₂
    have hcompat₁' :=
      historyCompatibleCore_update_of_playerHistory
        (S := S) (Outcome := Outcome) (t := t) hcompat₁ hagree₁
    have hlen₁ : ss₁.length - 1 = n₁ := by
      have := Math.ParameterizedChain.pureRun_length
        ((compiledCoreObs (S := S) (Outcome := Outcome) t).pureStep)
        ((compiledCoreObs (S := S) (Outcome := Outcome) t).init) n₁ π₀ ss₁ h₁
      omega
    simpa [hlen₁] using
      historySupportTrace_pureRun_nonzero
        (S := S) (Outcome := Outcome) (t := t) hsupp₁ hcompat₁'

private noncomputable def treeHeight : GameTree S Outcome → Nat
  | .terminal _ => 0
  | .chance _k _μ _hk next => Nat.succ <| Finset.univ.sup fun b => treeHeight (next b)
  | .decision _ next => Nat.succ <| Finset.univ.sup fun a => treeHeight (next a)

private theorem treeHeight_pos_of_nonterminal
    {u : GameTree S Outcome} (hnterm : ∀ z, u ≠ .terminal z) :
    0 < treeHeight (S := S) (Outcome := Outcome) u := by
  cases u with
  | terminal z =>
      exact (hnterm z rfl).elim
  | chance k μ hk next =>
      simp [treeHeight]
  | decision I next =>
      simp [treeHeight]

private theorem historyStepStep_height_lt
    {src dst : GameTree S Outcome} {ℓ : HistoryStep S}
    (hstep : HistoryStepStep (S := S) (Outcome := Outcome) ℓ src dst) :
    treeHeight (S := S) (Outcome := Outcome) dst <
      treeHeight (S := S) (Outcome := Outcome) src := by
  cases ℓ with
  | chance k b =>
      rcases hstep with ⟨μ, hk, next, rfl, rfl⟩
      simp only [treeHeight, Nat.succ_eq_add_one, Order.lt_add_one_iff]
      exact Finset.le_sup
        (f := fun b : Fin k => treeHeight (S := S) (Outcome := Outcome) (next b))
        (by simp)
  | action p I a =>
      rcases hstep with ⟨next, rfl, rfl⟩
      simp only [treeHeight, Nat.succ_eq_add_one, Order.lt_add_one_iff]
      exact Finset.le_sup
        (f := fun a : S.Act I => treeHeight (S := S) (Outcome := Outcome) (next a))
        (by simp)

private theorem reachBy_length_add_height_le
    {src dst : GameTree S Outcome} {h : List (HistoryStep S)}
    (hr : ReachBy h src dst) :
    h.length + treeHeight (S := S) (Outcome := Outcome) dst ≤
      treeHeight (S := S) (Outcome := Outcome) src := by
  induction hr with
  | nil =>
      simp only [List.length_nil, zero_add, le_refl]
  | @cons ℓ rest src mid dst hstep hreach ih =>
      have hlt :
          treeHeight (S := S) (Outcome := Outcome) mid <
            treeHeight (S := S) (Outcome := Outcome) src :=
        historyStepStep_height_lt (S := S) (Outcome := Outcome) hstep
      have hle :
          rest.length + treeHeight (S := S) (Outcome := Outcome) dst + 1 ≤
            treeHeight (S := S) (Outcome := Outcome) src := by
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hlt)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hle

private theorem historySupportStep_source_nonterminal
    {src dst : GameTree S Outcome} {ℓ : HistoryStep S}
    (hstep : HistorySupportStep (S := S) (Outcome := Outcome) ℓ src dst) :
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
    (hw : HistorySupportTrace (S := S) (Outcome := Outcome) t ss h)
    (hnterm : ∀ z,
      (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss ≠ .terminal z) :
    ss.length = h.length + 1 := by
  induction hw with
  | init =>
      simp
  | @stutter ss h z hw hterm ih =>
      exfalso
      exact hnterm z (by
        have :
            (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState (ss ++ [.terminal z]) =
              .terminal z := by
          simp [ObsModelCore.lastState]
        exact this)
  | @snoc ss h u ℓ hw hstep ih =>
      have hsrc_nonterm :
          ∀ z,
            (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss ≠ .terminal z :=
        historySupportStep_source_nonterminal (S := S) (Outcome := Outcome) hstep
      have hlen := ih hsrc_nonterm
      simp [List.length_append, hlen]

private theorem lastState_terminal_of_pureRun_height
    {π : ObsModelCore.PureProfile (compiledCoreObs (S := S) (Outcome := Outcome) t)}
    {ss : List (GameTree S Outcome)}
    (h :
      Math.ParameterizedChain.pureRun
        ((compiledCoreObs (S := S) (Outcome := Outcome) t).pureStep)
        ((compiledCoreObs (S := S) (Outcome := Outcome) t).init)
        (treeHeight (S := S) (Outcome := Outcome) t) π ss ≠ 0) :
    ∃ z,
      (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss = .terminal z := by
  obtain ⟨hist, ⟨hsupp⟩, hcompat⟩ :=
    pureRun_nonzero_to_historySupportTrace (S := S) (Outcome := Outcome) (t := t) h
  by_contra hnot
  have hnterm :
      ∀ z, (compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss ≠ .terminal z := by
    intro z hz
    exact hnot ⟨z, hz⟩
  have hlenTrace := Math.ParameterizedChain.pureRun_length
    ((compiledCoreObs (S := S) (Outcome := Outcome) t).pureStep)
    ((compiledCoreObs (S := S) (Outcome := Outcome) t).init)
    (treeHeight (S := S) (Outcome := Outcome) t) π ss h
  have hlenHist :
      hist.length = treeHeight (S := S) (Outcome := Outcome) t := by
    have hlenSupport :=
      historySupportTrace_length_eq_of_nonterminal
        (S := S) (Outcome := Outcome) (t := t) hsupp hnterm
    omega
  have hreach :=
    historySupportTrace_reachBy (S := S) (Outcome := Outcome) (t := t) hsupp
  have hbound :=
    reachBy_length_add_height_le (S := S) (Outcome := Outcome) hreach
  have hpos :
      0 < treeHeight (S := S) (Outcome := Outcome)
        ((compiledCoreObs (S := S) (Outcome := Outcome) t).lastState ss) := by
    exact treeHeight_pos_of_nonterminal (S := S) (Outcome := Outcome) hnterm
  omega

end ObsModelCoreBridge

-- ============================================================================
-- Tree-level Kuhn theorems (bridge from ObsModel to evalDist)
-- ============================================================================

/-- Two behavioral profiles agreeing on all infosets in `t` give the same `evalDist`. -/
theorem evalDist_eq_of_behavioral_agree (t : GameTree S Outcome)
    (σ₁ σ₂ : BehavioralProfile S)
    (h : ∀ {q} {J : S.Infoset q}, DecisionNodeIn J t → σ₁ q J = σ₂ q J) :
    t.evalDist σ₁ = t.evalDist σ₂ := by
  induction t with
  | terminal _ => rfl
  | chance _k _μ _hk next ih =>
    simp only [GameTree.evalDist]; congr 1; funext b
    exact ih b (fun hd => h (.in_chance _ _ _ _ b hd))
  | decision I next ih =>
    simp only [GameTree.evalDist]
    have hI := h (DecisionNodeIn.root next)
    rw [hI]
    congr 1; funext a
    exact ih a (fun hd => h (.in_decision I next a hd))

/-- The tree-level B→M core: the product PMF `productProfile σ` induces the
    same `evalDist` as `σ` when no info set repeats. -/
theorem behavioral_to_mixed (σ : BehavioralProfile S)
    (t : GameTree S Outcome) (hnr : NoInfoSetRepeat t) :
    (productProfile σ).bind (fun s => t.evalDist (flatToBehavioral s)) =
    t.evalDist σ := by
  induction t with
  | terminal z =>
    simp [GameTree.evalDist]
  | chance _k _μ _hk next ih =>
    simp only [GameTree.evalDist]
    -- Need: (productProfile σ).bind (fun s => μ.bind (fun b => ...)) =
    --       μ.bind (fun b => ...)
    -- Swap the two binds, then apply the IH per branch.
    rw [show (productProfile σ).bind
          (fun s => _μ.bind
            (fun b => (next b).evalDist (flatToBehavioral s))) =
        _μ.bind (fun b => (productProfile σ).bind
          (fun s => (next b).evalDist (flatToBehavioral s))) from
      PMF.bind_comm (productProfile σ) _μ
        (fun s b => (next b).evalDist (flatToBehavioral s))]
    congr 1; funext b
    exact ih b (hnr b)
  | @decision p I next ih =>
    obtain ⟨hnodup, hnr_sub⟩ := hnr
    simp only [GameTree.evalDist]
    simp only [flatToBehavioral, PMF.pure_bind]
    let j : FlatIdx S := ⟨p, I⟩
    let fam : (idx : FlatIdx S) → PMF (S.Act idx.2) := fun idx => σ idx.1 idx.2
    let g : S.Act I → FlatProfile S → PMF Outcome :=
      fun a s => (next a).evalDist (flatToBehavioral s)
    have hg : ∀ a,
        Math.PMFProduct.Ignores
          (A := fun idx : FlatIdx S => S.Act idx.2) j (g a) := by
      intro a
      refine Math.PMFProduct.Ignores_of_pointwise
        (A := fun idx : FlatIdx S => S.Act idx.2) j (g a) ?_
      intro s₁ s₂ hagree
      apply evalDist_eq_of_behavioral_agree (t := next a)
        (σ₁ := flatToBehavioral s₁) (σ₂ := flatToBehavioral s₂)
      intro q J hJ
      have hneq : (⟨q, J⟩ : FlatIdx S) ≠ j := by
        intro heq
        dsimp [j] at heq
        cases heq
        exact (hnodup a) hJ
      simp [flatToBehavioral, hagree _ hneq]
    have hdecomp :
        productProfile σ =
          (σ p I).bind (fun a =>
            Math.PMFProduct.pmfPi (A := fun idx : FlatIdx S => S.Act idx.2)
              (Function.update fam j (PMF.pure a))) := by
      simpa [productProfile, fam, j] using
        (Math.PMFProduct.pmfPi_update_bind (σ := fam) j (σ p I))
    rw [hdecomp, PMF.bind_bind]
    congr 1
    funext a
    calc
      (Math.PMFProduct.pmfPi (A := fun idx : FlatIdx S => S.Act idx.2)
          (Function.update fam j (PMF.pure a))).bind
          (fun s => (next (s j)).evalDist (flatToBehavioral s))
          =
        ((Math.PMFProduct.pmfPi (A := fun idx : FlatIdx S => S.Act idx.2) fam).bind
          (fun s => PMF.pure (Function.update s j a))).bind
            (fun s => (next (s j)).evalDist (flatToBehavioral s)) := by
              rw [Math.PMFProduct.pmfPi_bind_update_pure]
      _ =
        (Math.PMFProduct.pmfPi (A := fun idx : FlatIdx S => S.Act idx.2) fam).bind
          (g a) := by
            rw [PMF.bind_bind]
            congr 1
            funext s
            rw [PMF.pure_bind]
            have hignore := hg a s a
            simpa [g, j, flatToBehavioral, Function.update_self] using hignore
      _ =
        (productProfile σ).bind (fun s => (next a).evalDist (flatToBehavioral s)) := by
            rfl
      _ = (next a).evalDist σ := ih a (hnr_sub a)

/-- Kuhn's theorem (behavioral → mixed direction):
    For any behavioral profile σ and tree with perfect recall,
    there exists a product distribution over flat profiles
    that induces the same outcome distribution. -/
theorem kuhn_behavioral_to_mixed (σ : BehavioralProfile S) (t : GameTree S Outcome)
    (hpr : PerfectRecall t) :
    ∃ μ : PMF (FlatProfile S),
      μ.bind (fun s => t.evalDist (flatToBehavioral s)) = t.evalDist σ :=
  ⟨productProfile σ, behavioral_to_mixed σ t
    (PerfectRecall_implies_NoInfoSetRepeat t hpr)⟩

open GameTheory in
/-- Kuhn's theorem lifted to utility distributions (behavioral → mixed). -/
theorem kuhn_behavioral_to_mixed_udist (G : EFGGame)
    (σ : BehavioralProfile G.inf) (hpr : PerfectRecall G.tree) :
    ∃ μ : PMF (FlatProfile G.inf),
      μ.bind (fun s => G.toKernelGame.udist (flatToBehavioral s)) =
      G.toKernelGame.udist σ := by
  obtain ⟨μ, hμ⟩ := kuhn_behavioral_to_mixed σ G.tree hpr
  exact ⟨μ, by
    simp only [KernelGame.udist, EFGGame.toKernelGame]
    rw [← hμ, PMF.bind_bind]⟩

private theorem kuhn_mixed_to_behavioral_core
    (t : GameTree S Outcome)
    (hpr : PerfectRecall t)
    (muP : MixedProfile S) :
    ∃ β : (compiledCoreObs (S := S) (Outcome := Outcome) t).BehavioralProfile,
      let O := compiledCoreObs (S := S) (Outcome := Outcome) t
      let k := treeHeight (S := S) (Outcome := Outcome) t
      let μ := GameTheory.EFG.liftMixedProfileCore (S := S) (Outcome := Outcome) t muP
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k) := by
  let O := compiledCoreObs (S := S) (Outcome := Outcome) t
  let k := treeHeight (S := S) (Outcome := Outcome) t
  let μ := GameTheory.EFG.liftMixedProfileCore (S := S) (Outcome := Outcome) t muP
  have hMass :
      ObsModelCore.StepMassInvariant O := by
    intro ss u π₁ π₂ h₁ h₂
    exact stepMassInvariant_compiledCore (S := S) (Outcome := Outcome) (t := t) π₁ π₂ h₁ h₂
  have hFactor :
      ObsModelCore.StepSupportFactorization O := by
    intro ss u π₀ π h₀
    exact stepSupportFactorization_compiledCore (S := S) (Outcome := Outcome) (t := t) π₀ π h₀
  obtain ⟨β, hβ⟩ :=
    ObsModelCore.kuhn_mixed_to_behavioral_semantic (O := O)
      hMass hFactor
      (fun i =>
        ObsModelCore.actionPosteriorLocal_of_obsLocalFeasibility (O := O)
          hMass i
          (by
            simpa [O] using
              obsLocalFeasibility_compiledCore (S := S) (Outcome := Outcome) (t := t) hpr i))
      μ k
  exact ⟨β, hβ⟩

private theorem compiledCore_runEq_to_evalDistEq
    (t : GameTree S Outcome)
    (muP : MixedProfile S)
    {β : (compiledCoreObs (S := S) (Outcome := Outcome) t).BehavioralProfile}
    (hβ :
      let O := compiledCoreObs (S := S) (Outcome := Outcome) t
      let k := treeHeight (S := S) (Outcome := Outcome) t
      let μ := GameTheory.EFG.liftMixedProfileCore (S := S) (Outcome := Outcome) t muP
      O.runDist k β = (pmfPi μ).bind (O.runDistPure k)) :
    let σ := GameTheory.EFG.descendBehavioralProfileCore (S := S) (Outcome := Outcome) t β
    t.evalDist σ =
      (mixedProfileJoint (S := S) muP).bind
        (fun pi => t.evalDist (pureToBehavioral (S := S) pi)) := by
  let O := compiledCoreObs (S := S) (Outcome := Outcome) t
  let k := treeHeight (S := S) (Outcome := Outcome) t
  let μ := GameTheory.EFG.liftMixedProfileCore (S := S) (Outcome := Outcome) t muP
  let σ : BehavioralProfile S :=
    GameTheory.EFG.descendBehavioralProfileCore (S := S) (Outcome := Outcome) t β
  have hleft :
      (O.runDist k β).bind (fun ss => (O.lastState ss).evalDist σ) = t.evalDist σ := by
    simpa [O, k, σ, GameTheory.EFG.liftBehavioralProfileCore_descendBehavioralProfileCore] using
      runDist_bind_evalDist_core (S := S) (Outcome := Outcome) (t := t) σ k
  have hright :
      ((pmfPi μ).bind (O.runDistPure k)).bind
          (fun ss => (O.lastState ss).evalDist σ) =
        (mixedProfileJoint (S := S) muP).bind
          (fun pi => t.evalDist (pureToBehavioral (S := S) pi)) := by
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
                      (S := S) (Outcome := Outcome) t π)))) := by
            refine Math.ProbabilityMassFunction.bind_congr_on_support (pmfPi μ) _ _ ?_
            intro π _hπ
            refine Math.ProbabilityMassFunction.bind_congr_on_support (O.runDistPure k π) _ _ ?_
            intro ss hss
            have hss' :
                Math.ParameterizedChain.pureRun (O.pureStep) O.init k π ss ≠ 0 := by
              simpa [O, k, ObsModelCore.runDistPure_eq_pureRun] using hss
            obtain ⟨z, hz⟩ :=
              lastState_terminal_of_pureRun_height
                (S := S) (Outcome := Outcome) (t := t)
                (by simpa [O, k] using hss')
            simp [O, hz]
      _ =
        (pmfPi μ).bind
          (fun π =>
            t.evalDist
              (pureToBehavioral
                (GameTheory.EFG.descendPureProfileCore
                  (S := S) (Outcome := Outcome) t π))) := by
          refine Math.ProbabilityMassFunction.bind_congr_on_support (pmfPi μ) _ _ ?_
          intro π _hπ
          simpa [O, k] using
            runDistPure_bind_evalDist_core (S := S) (Outcome := Outcome) (t := t) π k
      _ =
        (Math.ProbabilityMassFunction.pushforward
          (mixedProfileJoint (S := S) muP)
          (GameTheory.EFG.liftPureProfileCore (S := S) (Outcome := Outcome) t)).bind
            (fun π =>
              t.evalDist
                (pureToBehavioral
                  (GameTheory.EFG.descendPureProfileCore
                    (S := S) (Outcome := Outcome) t π))) := by
          rw [liftMixedProfileCore_joint (S := S) (Outcome := Outcome) (t := t) muP]
      _ =
        (mixedProfileJoint (S := S) muP).bind
          (fun pi => t.evalDist (pureToBehavioral (S := S) pi)) := by
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
      (mixedProfileJoint (S := S) muP).bind
        (fun pi => t.evalDist (pureToBehavioral (S := S) pi)) := hright

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
      (mixedProfileJoint (S := S) muP).bind
        (fun pi => t.evalDist
          (pureToBehavioral (S := S) pi)) := by
  obtain ⟨β, hβ⟩ :=
    kuhn_mixed_to_behavioral_core (S := S) (Outcome := Outcome) t hpr muP
  let σ : BehavioralProfile S :=
    GameTheory.EFG.descendBehavioralProfileCore (S := S) (Outcome := Outcome) t β
  refine ⟨σ, ?_⟩
  simpa [σ] using
    compiledCore_runEq_to_evalDistEq (S := S) (Outcome := Outcome) t muP hβ

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
