/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Probability.Distributions.Uniform
import GameTheory.Concepts.Stochastic.Basic

/-!
# A jointly controlled one-stage public XOR coin

Two distinct players each have two distinguished actions encoding a bit.  If
both prescribed bit marginals are uniform and the public signal is their XOR,
then every unilateral deviation leaves that signal uniform: at least one of
the two independent controller bits remains uniform.

This is only a statement about the marginal public bit.  A next-state law is
also deviation-invariant when the transition kernel factors through that bit.
Without this factorization the transition may retain information about an
individual controller's action, and the uniform XOR marginal gives no child
law guarantee.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.PMFProduct Math.ProbabilityMassFunction

variable {ι : Type} {G : StochasticGame ι}

/-- Two distinguished actions which publicly encode false and true. -/
structure DistinguishedBitActions (G : StochasticGame ι)
    (controller : ι) where
  falseAction : G.Act controller
  trueAction : G.Act controller
  bit : G.Act controller → Bool
  bit_falseAction : bit falseAction = false
  bit_trueAction : bit trueAction = true

namespace DistinguishedBitActions

variable {controller : ι}

/-- The distinguished action selected by a Boolean input. -/
def action
    (source : DistinguishedBitActions G controller) :
    Bool → G.Act controller
  | false => source.falseAction
  | true => source.trueAction

@[simp] theorem bit_action
    (source : DistinguishedBitActions G controller) (value : Bool) :
    source.bit (source.action value) = value := by
  cases value
  · exact source.bit_falseAction
  · exact source.bit_trueAction

/-- Uniform randomization over the two distinguished bit actions. -/
def uniform
    (source : DistinguishedBitActions G controller) :
    PMF (G.Act controller) :=
  (PMF.uniformOfFintype Bool).map source.action

/-- The observable bit marginal of the distinguished mixture is uniform. -/
theorem map_bit_uniform
    (source : DistinguishedBitActions G controller) :
    (source.uniform).map source.bit =
      PMF.uniformOfFintype Bool := by
  unfold uniform
  rw [PMF.map_comp]
  have hcomp : source.bit ∘ source.action = id := by
    funext value
    exact source.bit_action value
  rw [hcomp, PMF.map_id]

end DistinguishedBitActions

/-- Two distinct controllers whose distinguished action bits are combined by
public XOR. -/
structure JointPublicXorCoin (G : StochasticGame ι) where
  left : ι
  right : ι
  controllers_ne : left ≠ right
  leftSource : DistinguishedBitActions G left
  rightSource : DistinguishedBitActions G right

namespace JointPublicXorCoin

/-- The public XOR bit read from a joint action. -/
def signal
    (coin : JointPublicXorCoin G) (action : G.JointAct) : Bool :=
  coin.leftSource.bit (action coin.left) ^^
    coin.rightSource.bit (action coin.right)

/-- Independent XOR of two Boolean laws. -/
def xorLaw (leftLaw rightLaw : PMF Bool) : PMF Bool :=
  leftLaw.bind fun leftBit =>
    rightLaw.bind fun rightBit =>
      PMF.pure (leftBit ^^ rightBit)

/-- XOR with an independent uniform right bit is uniform. -/
theorem xorLaw_uniform_right (leftLaw : PMF Bool) :
    xorLaw leftLaw (PMF.uniformOfFintype Bool) =
      PMF.uniformOfFintype Bool := by
  have hfixed : ∀ leftBit : Bool,
      (PMF.uniformOfFintype Bool).bind
          (fun rightBit => PMF.pure (leftBit ^^ rightBit)) =
        PMF.uniformOfFintype Bool := by
    intro leftBit
    ext value
    rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    simp only [PMF.uniformOfFintype_apply, PMF.pure_apply,
      Fintype.card_bool]
    cases leftBit <;> cases value <;> simp
  unfold xorLaw
  simp_rw [hfixed]
  exact PMF.bind_const _ _

/-- XOR with an independent uniform left bit is uniform. -/
theorem xorLaw_uniform_left (rightLaw : PMF Bool) :
    xorLaw (PMF.uniformOfFintype Bool) rightLaw =
      PMF.uniformOfFintype Bool := by
  have hfixed : ∀ rightBit : Bool,
      (PMF.uniformOfFintype Bool).bind
          (fun leftBit => PMF.pure (leftBit ^^ rightBit)) =
        PMF.uniformOfFintype Bool := by
    intro rightBit
    ext value
    rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    simp only [PMF.uniformOfFintype_apply, PMF.pure_apply,
      Fintype.card_bool]
    cases rightBit <;> cases value <;> simp
  unfold xorLaw
  rw [PMF.bind_comm]
  simp_rw [hfixed]
  exact PMF.bind_const _ _

/-- The joint-action XOR law factors through the two controller marginals. -/
theorem signalLaw_eq_xorLaw
    [Fintype ι] [∀ player, Finite (G.Act player)]
    (coin : JointPublicXorCoin G)
    (marginal : ∀ player, PMF (G.Act player)) :
    (pmfPi marginal).map coin.signal =
      (marginal coin.left).bind fun leftAction =>
        (marginal coin.right).bind fun rightAction =>
          PMF.pure
            (coin.leftSource.bit leftAction ^^
              coin.rightSource.bit rightAction) := by
  classical
  rw [← PMF.bind_pure_comp]
  change
    (pmfPi marginal).bind
        (fun action =>
          PMF.pure
            (coin.leftSource.bit (action coin.left) ^^
              coin.rightSource.bit (action coin.right))) =
      _
  let continuation :
      G.Act coin.left → G.JointAct → PMF Bool :=
    fun leftAction action =>
      PMF.pure
        (coin.leftSource.bit leftAction ^^
          coin.rightSource.bit (action coin.right))
  have hignore :
      Ignores₂ (A := G.Act) coin.left continuation := by
    intro leftAction action replacement
    simp [continuation, Function.update, coin.controllers_ne.symm]
  change
    (pmfPi marginal).bind
        (fun action => continuation (action coin.left) action) =
      _
  rw [pmfPi_bind_factor marginal coin.left continuation hignore]
  apply congrArg ((marginal coin.left).bind)
  funext leftAction
  exact pmfPi_bind_eval marginal coin.right
    (fun rightAction =>
      PMF.pure
        (coin.leftSource.bit leftAction ^^
          coin.rightSource.bit rightAction))

/-- Uniformity of the right controller's observable bit suffices for a
uniform public XOR bit, regardless of every other marginal. -/
theorem signalLaw_eq_uniform_of_right
    [Fintype ι] [∀ player, Finite (G.Act player)]
    (coin : JointPublicXorCoin G)
    (marginal : ∀ player, PMF (G.Act player))
    (hright :
      (marginal coin.right).map coin.rightSource.bit =
        PMF.uniformOfFintype Bool) :
    (pmfPi marginal).map coin.signal =
      PMF.uniformOfFintype Bool := by
  classical
  rw [coin.signalLaw_eq_xorLaw]
  have hinner : ∀ leftAction,
      (marginal coin.right).bind
          (fun rightAction =>
            PMF.pure
              (coin.leftSource.bit leftAction ^^
                coin.rightSource.bit rightAction)) =
        PMF.uniformOfFintype Bool := by
    intro leftAction
    calc
      (marginal coin.right).bind
          (fun rightAction =>
            PMF.pure
              (coin.leftSource.bit leftAction ^^
                coin.rightSource.bit rightAction)) =
        ((marginal coin.right).map coin.rightSource.bit).bind
          (fun rightBit =>
            PMF.pure
              (coin.leftSource.bit leftAction ^^ rightBit)) := by
                rw [← PMF.bind_pure_comp, PMF.bind_bind]
                simp
      _ = (PMF.uniformOfFintype Bool).bind
          (fun rightBit =>
            PMF.pure
              (coin.leftSource.bit leftAction ^^ rightBit)) := by
            rw [hright]
      _ = PMF.uniformOfFintype Bool := by
        simpa [xorLaw] using
          xorLaw_uniform_right
            (PMF.pure (coin.leftSource.bit leftAction))
  simp_rw [hinner]
  exact PMF.bind_const _ _

/-- Uniformity of the left controller's observable bit likewise suffices. -/
theorem signalLaw_eq_uniform_of_left
    [Fintype ι] [∀ player, Finite (G.Act player)]
    (coin : JointPublicXorCoin G)
    (marginal : ∀ player, PMF (G.Act player))
    (hleft :
      (marginal coin.left).map coin.leftSource.bit =
        PMF.uniformOfFintype Bool) :
    (pmfPi marginal).map coin.signal =
      PMF.uniformOfFintype Bool := by
  classical
  rw [coin.signalLaw_eq_xorLaw]
  rw [PMF.bind_comm]
  have hinner : ∀ rightAction,
      (marginal coin.left).bind
          (fun leftAction =>
            PMF.pure
              (coin.leftSource.bit leftAction ^^
                coin.rightSource.bit rightAction)) =
        PMF.uniformOfFintype Bool := by
    intro rightAction
    calc
      (marginal coin.left).bind
          (fun leftAction =>
            PMF.pure
              (coin.leftSource.bit leftAction ^^
                coin.rightSource.bit rightAction)) =
        ((marginal coin.left).map coin.leftSource.bit).bind
          (fun leftBit =>
            PMF.pure
              (leftBit ^^
                coin.rightSource.bit rightAction)) := by
                rw [← PMF.bind_pure_comp, PMF.bind_bind]
                simp
      _ = (PMF.uniformOfFintype Bool).bind
          (fun leftBit =>
            PMF.pure
              (leftBit ^^
                coin.rightSource.bit rightAction)) := by
            rw [hleft]
      _ = PMF.uniformOfFintype Bool := by
        simpa [xorLaw] using
          xorLaw_uniform_left
            (PMF.pure (coin.rightSource.bit rightAction))
  simp_rw [hinner]
  exact PMF.bind_const _ _

/-- Prescribed marginals put both controllers on their distinguished uniform
bit mixtures and leave all other players unchanged. -/
def prescribedMarginal
    [DecidableEq ι]
    (coin : JointPublicXorCoin G)
    (fallback : ∀ player, PMF (G.Act player)) :
    ∀ player, PMF (G.Act player) :=
  Function.update
    (Function.update fallback coin.left coin.leftSource.uniform)
    coin.right coin.rightSource.uniform

@[simp] theorem prescribedMarginal_left
    [DecidableEq ι]
    (coin : JointPublicXorCoin G)
    (fallback : ∀ player, PMF (G.Act player)) :
    coin.prescribedMarginal fallback coin.left =
      coin.leftSource.uniform := by
  simp [prescribedMarginal, coin.controllers_ne]

@[simp] theorem prescribedMarginal_right
    [DecidableEq ι]
    (coin : JointPublicXorCoin G)
    (fallback : ∀ player, PMF (G.Act player)) :
    coin.prescribedMarginal fallback coin.right =
      coin.rightSource.uniform := by
  simp [prescribedMarginal]

/-- With both controllers prescribed, the public XOR bit is uniform. -/
theorem signalLaw_prescribedMarginal_eq_uniform
    [Fintype ι] [DecidableEq ι] [∀ player, Finite (G.Act player)]
    (coin : JointPublicXorCoin G)
    (fallback : ∀ player, PMF (G.Act player)) :
    (pmfPi (coin.prescribedMarginal fallback)).map coin.signal =
      PMF.uniformOfFintype Bool := by
  apply coin.signalLaw_eq_uniform_of_left
  rw [coin.prescribedMarginal_left]
  exact coin.leftSource.map_bit_uniform

/-- Any one-coordinate replacement leaves the public XOR bit uniform.  This
includes deviations by either controller and by every other player. -/
theorem signalLaw_update_eq_uniform
    [Fintype ι] [DecidableEq ι] [∀ player, Finite (G.Act player)]
    (coin : JointPublicXorCoin G)
    (fallback : ∀ player, PMF (G.Act player))
    (who : ι) (deviation : PMF (G.Act who)) :
    (pmfPi
        (Function.update
          (coin.prescribedMarginal fallback) who deviation)).map
        coin.signal =
      PMF.uniformOfFintype Bool := by
  by_cases hwho : who = coin.left
  · subst who
    apply coin.signalLaw_eq_uniform_of_right
    rw [Function.update_of_ne coin.controllers_ne.symm]
    simpa using coin.rightSource.map_bit_uniform
  · apply coin.signalLaw_eq_uniform_of_left
    rw [Function.update_of_ne (Ne.symm hwho)]
    simpa using coin.leftSource.map_bit_uniform

/-- The corresponding public behavior profile. -/
def prescribedProfile
    [DecidableEq ι]
    (coin : JointPublicXorCoin G)
    (fallback : G.BehaviorProfile) :
    G.BehaviorProfile :=
  fun player stage history =>
    coin.prescribedMarginal
      (fun other => fallback other stage history) player

/-- At every public history, the XOR bit is uniform after every unilateral
behavior deviation. -/
theorem stageActionDist_signal_update_eq_uniform
    [Fintype ι] [DecidableEq ι] [∀ player, Finite (G.Act player)]
    (coin : JointPublicXorCoin G)
    (fallback : G.BehaviorProfile)
    (who : ι) (deviation : G.BehaviorStrategy who)
    {stage : ℕ} (history : G.Hist stage) :
    (G.stageActionDist
        (Function.update
          (coin.prescribedProfile fallback) who deviation)
        history).map coin.signal =
      PMF.uniformOfFintype Bool := by
  unfold stageActionDist prescribedProfile
  have hmarginal :
      (fun player =>
        Function.update
          (fun other stage history =>
            coin.prescribedMarginal
              (fun source => fallback source stage history) other)
          who deviation player stage history) =
        Function.update
          (coin.prescribedMarginal
            (fun player => fallback player stage history))
          who (deviation stage history) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp
    · simp [Function.update_of_ne hplayer]
  rw [hmarginal]
  exact coin.signalLaw_update_eq_uniform
    (fun player => fallback player stage history)
    who (deviation stage history)

/-- The one-step next-state law induced by independent action marginals. -/
def oneStepNextStateLaw
    [Fintype ι]
    (marginal : ∀ player, PMF (G.Act player))
    (state : G.State) : PMF G.State :=
  (pmfPi marginal).bind (G.transition state)

/-- If the transition kernel factors through the public XOR bit, the complete
next-state law depends only on the marginal law of that bit. -/
theorem oneStepNextStateLaw_eq_signal_bind
    [Fintype ι] [Finite G.State]
    [∀ player, Finite (G.Act player)]
    (coin : JointPublicXorCoin G)
    (marginal : ∀ player, PMF (G.Act player))
    (state : G.State) (kernel : Bool → PMF G.State)
    (hfactor :
      ∀ action, G.transition state action = kernel (coin.signal action)) :
    oneStepNextStateLaw marginal state =
      ((pmfPi marginal).map coin.signal).bind kernel := by
  unfold oneStepNextStateLaw
  calc
    (pmfPi marginal).bind (G.transition state) =
      (pmfPi marginal).bind
        (fun action => kernel (coin.signal action)) := by
          apply congrArg ((pmfPi marginal).bind)
          funext action
          exact hfactor action
    _ = ((pmfPi marginal).map coin.signal).bind kernel := by
      rw [← PMF.bind_pure_comp, PMF.bind_bind]
      simp

/-- Under transition factorization, every unilateral deviation induces the
same next-state law: a uniform public bit followed by the bit kernel. -/
theorem oneStepNextStateLaw_update_eq_uniform_bind
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ player, Finite (G.Act player)]
    (coin : JointPublicXorCoin G)
    (fallback : ∀ player, PMF (G.Act player))
    (who : ι) (deviation : PMF (G.Act who))
    (state : G.State) (kernel : Bool → PMF G.State)
    (hfactor :
      ∀ action, G.transition state action = kernel (coin.signal action)) :
    oneStepNextStateLaw
        (Function.update
          (coin.prescribedMarginal fallback) who deviation)
        state =
      (PMF.uniformOfFintype Bool).bind kernel := by
  rw [
    coin.oneStepNextStateLaw_eq_signal_bind
      _ state kernel hfactor,
    coin.signalLaw_update_eq_uniform
  ]

end JointPublicXorCoin

/-! ## Uniform XOR does not determine the next-state law -/

namespace PublicXorTransitionObstruction

abbrev Player := Bool

/-- Both players have Boolean actions; the state records only the left
controller's action.  Thus XOR discards transition-relevant information. -/
abbrev game : StochasticGame Player where
  State := Bool
  Act := fun _ => Bool
  stagePayoff := fun _ _ _ => 0
  transition := fun _ action => PMF.pure (action false)
  discount := 0
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

instance : Fintype game.State := inferInstanceAs (Fintype Bool)
instance : DecidableEq game.State := inferInstanceAs (DecidableEq Bool)
instance (who : Player) : Fintype (game.Act who) :=
  inferInstanceAs (Fintype Bool)
instance (who : Player) : DecidableEq (game.Act who) :=
  inferInstanceAs (DecidableEq Bool)

def source (controller : Player) :
    DistinguishedBitActions game controller where
  falseAction := false
  trueAction := true
  bit := id
  bit_falseAction := rfl
  bit_trueAction := rfl

@[simp] theorem source_uniform (controller : Player) :
    (source controller).uniform =
      PMF.uniformOfFintype Bool := by
  unfold DistinguishedBitActions.uniform
  have haction :
      (source controller).action = id := by
    funext value
    cases value <;> rfl
  rw [haction, PMF.map_id]

def coin : JointPublicXorCoin game where
  left := false
  right := true
  controllers_ne := by decide
  leftSource := source false
  rightSource := source true

def fallback : ∀ player, PMF (game.Act player) :=
  fun _ => PMF.uniformOfFintype Bool

def prescribed : ∀ player, PMF (game.Act player) :=
  coin.prescribedMarginal fallback

def deviating : ∀ player, PMF (game.Act player) :=
  Function.update prescribed false (PMF.pure true)

/-- Prescribed play and the unilateral deviation have the same uniform public
XOR bit. -/
theorem signal_laws_eq_uniform :
    (pmfPi prescribed).map coin.signal =
        PMF.uniformOfFintype Bool ∧
      (pmfPi deviating).map coin.signal =
        PMF.uniformOfFintype Bool := by
  constructor
  · exact coin.signalLaw_prescribedMarginal_eq_uniform fallback
  · exact coin.signalLaw_update_eq_uniform fallback false
      (PMF.pure true)

/-- Under prescribed play, the next state is the uniform left action. -/
theorem nextStateLaw_prescribed :
    JointPublicXorCoin.oneStepNextStateLaw prescribed false =
      PMF.uniformOfFintype Bool := by
  unfold JointPublicXorCoin.oneStepNextStateLaw
  change
    (pmfPi prescribed).bind
        (fun action => PMF.pure (action false)) =
      PMF.uniformOfFintype Bool
  rw [pmfPi_bind_eval]
  rw [PMF.bind_pure]
  rw [show prescribed false = (source false).uniform by
    simp [prescribed, coin,
      JointPublicXorCoin.prescribedMarginal]]
  exact source_uniform false

/-- A unilateral deviation by the left controller makes the next state
deterministically true. -/
theorem nextStateLaw_deviating :
    JointPublicXorCoin.oneStepNextStateLaw deviating false =
      PMF.pure true := by
  unfold JointPublicXorCoin.oneStepNextStateLaw
  change
    (pmfPi deviating).bind
        (fun action => PMF.pure (action false)) =
      PMF.pure true
  rw [pmfPi_bind_eval]
  simp [deviating]

/-- Equal uniform XOR marginals do not imply equal next-state laws. -/
theorem equal_uniform_signal_but_nextStateLaw_ne :
    (pmfPi prescribed).map coin.signal =
        (pmfPi deviating).map coin.signal ∧
      JointPublicXorCoin.oneStepNextStateLaw prescribed false ≠
        JointPublicXorCoin.oneStepNextStateLaw deviating false := by
  constructor
  · rw [signal_laws_eq_uniform.1, signal_laws_eq_uniform.2]
  · rw [nextStateLaw_prescribed, nextStateLaw_deviating]
    intro heq
    have hfalse := congrArg (fun law : PMF Bool => law false) heq
    norm_num [PMF.uniformOfFintype_apply, PMF.pure_apply] at hfalse

end PublicXorTransitionObstruction

end StochasticGame
end GameTheory
