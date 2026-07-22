/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.Bridges.OpenGame_EFG
import GameTheory.Languages.OpenGame.Correlation
import GameTheory.Languages.NFG.Stackelberg
import GameTheory.Languages.NFG.MatchingPenniesMixed
import GameTheory.Concepts.Correlation.SignalTiming

/-!
# Open-Game Examples

Prisoner's Dilemma illustrates context-indexed Nash recovery for the closed
simultaneous shape.  `false` denotes cooperation and `true` defection.
-/

namespace OpenGames.Examples

/-- Standard Prisoner's Dilemma utility pair. -/
def prisonersDilemmaPayoff : Bool × Bool → ℝ × ℝ
  | (false, false) => (3, 3)
  | (false, true) => (0, 5)
  | (true, false) => (5, 0)
  | (true, true) => (1, 1)

/-- Utility profile used as the closing continuation. -/
def prisonersDilemmaUtility (a : Bool → Bool) (i : Bool) : ℝ :=
  if i then (prisonersDilemmaPayoff (a false, a true)).2
  else (prisonersDilemmaPayoff (a false, a true)).1

/-- A closed, two-player simultaneous Prisoner's Dilemma. -/
def prisonersDilemma :
    OpenGame (Bool → Unit) (Bool → Unit) (Bool → Bool) (Bool → ℝ) :=
  ShapeN (fun _i : Bool => Unit) (fun _i : Bool => Bool)

/-- The constant contingent plan selecting action `a`. -/
def constantClosedStrategy (a : Bool) : Bool → Unit → Bool :=
  fun _i _u => a

/-- Mutual defection is selected compositionally. -/
theorem defect_is_equilibrium :
    prisonersDilemma.IsEquilibriumIn (fun _i => ())
      prisonersDilemmaUtility (constantClosedStrategy true) := by
  simp [prisonersDilemma, ShapeN, prisonersDilemmaUtility,
    prisonersDilemmaPayoff, constantClosedStrategy, Function.update]

/-- Mutual cooperation is not an equilibrium: either player can defect. -/
theorem cooperate_not_equilibrium :
    ¬prisonersDilemma.IsEquilibriumIn (fun _i => ())
      prisonersDilemmaUtility (constantClosedStrategy false) := by
  simp [prisonersDilemma, ShapeN, prisonersDilemmaUtility,
    prisonersDilemmaPayoff, constantClosedStrategy, Function.update]
  norm_num

/-- The compositional result is exactly the kernel-level Nash statement. -/
theorem defect_is_kernelNash :
    (ShapeN.compileAction (fun _i : Bool => Bool) prisonersDilemmaUtility).IsNash
      (fun _i => true) := by
  have hn := (ShapeN.closed_isEquilibriumIn_iff_isNash
    prisonersDilemmaUtility (constantClosedStrategy true)).mp
      defect_is_equilibrium
  simpa [ShapeN.closedStrategyEquiv, constantClosedStrategy] using hn

/-! ## Entry deterrence and non-credible threats -/

/-- Entry-deterrence payoffs.  For the leader, `false` is Out and `true` is
Enter.  For the follower, `false` is Accommodate and `true` is Fight. -/
def entryDeterrencePayoff : Bool × Bool → ℝ × ℝ
  | (false, false) => (1, 1)
  | (false, true) => (1, 1)
  | (true, false) => (2, 2)
  | (true, true) => (0, 0)

/-- The non-credible deterrence profile: stay out, with a contingent threat to
fight. -/
def deterrenceThreat : Bool × (Bool → Bool) :=
  (false, fun _entry => true)

/-- The threat is a plain sequential equilibrium. -/
theorem deterrenceThreat_is_plainEquilibrium :
    (ShapeS Bool Bool).IsEquilibriumIn () entryDeterrencePayoff
      deterrenceThreat := by
  simp [ShapeS, entryDeterrencePayoff, deterrenceThreat]

/-- The same profile fails the conditioned predicate because fighting after
entry is not optimal. -/
theorem deterrenceThreat_not_conditioned :
    ¬ShapeS.IsConditionedEquilibrium entryDeterrencePayoff deterrenceThreat := by
  simp [ShapeS.IsConditionedEquilibrium, entryDeterrencePayoff, deterrenceThreat]

/-- Enter followed by accommodation is subgame perfect (the off-path Out
subgame leaves the follower indifferent). -/
def entryAccommodation : Bool × (Bool → Bool) :=
  (true, fun _entry => false)

theorem entryAccommodation_is_conditioned :
    ShapeS.IsConditionedEquilibrium entryDeterrencePayoff entryAccommodation := by
  simp [ShapeS.IsConditionedEquilibrium, entryDeterrencePayoff, entryAccommodation]

/-- The non-credible threat is nevertheless Nash in the compiled sequential
strategic form. -/
theorem deterrenceThreat_is_kernelNash :
    (ShapeS.compileAction Bool Bool entryDeterrencePayoff).IsNash
      (ShapeS.toProfile deterrenceThreat) :=
  (ShapeS.isEquilibriumIn_iff_isNash entryDeterrencePayoff deterrenceThreat).mp
    deterrenceThreat_is_plainEquilibrium

/-! ## Stackelberg compatibility -/

/-- The conditioned two-stage predicate is exactly the existing Stackelberg
equilibrium predicate when the continuation is built from leader/follower
utilities. -/
theorem conditioned_iff_isStackelbergEq (G : GameTheory.StackelbergGame)
    (l : G.L) (br : G.L → G.F) :
    (ShapeS.conditioned G.L G.F).IsEquilibriumIn ()
        (fun x => (G.uL x.1 x.2, G.uF x.1 x.2)) (l, br) ↔
      G.IsStackelbergEq l br := by
  constructor
  · intro h
    exact ⟨fun l' f' => h.2 l' f', fun l' => h.1 l'⟩
  · intro h
    exact ⟨fun l' => h.2 l', fun l' f' => h.1 l' f'⟩

/-- The repository's entry-deterrence Stackelberg solution is therefore a
conditioned open-game equilibrium. -/
theorem stackelberg_entry_is_conditioned :
    (ShapeS.conditioned Bool Bool).IsEquilibriumIn ()
        (fun x => (GameTheory.EntryDeterrence.uL x.1 x.2,
          GameTheory.EntryDeterrence.uF x.1 x.2))
        (GameTheory.EntryDeterrence.fight, GameTheory.EntryDeterrence.br) :=
  (conditioned_iff_isStackelbergEq GameTheory.EntryDeterrence.game
    GameTheory.EntryDeterrence.fight GameTheory.EntryDeterrence.br).2
      GameTheory.EntryDeterrence.game_stackelberg_eq_fight

/-- The same Stackelberg solution is subgame-perfect in the staged EFG
encoding, by the genuine bridge correspondence. -/
theorem stackelberg_entry_is_efgSubgamePerfect :
    (ShapeS.toEFG Bool Bool fun x =>
      (GameTheory.EntryDeterrence.uL x.1 x.2,
        GameTheory.EntryDeterrence.uF x.1 x.2)).IsSubgamePerfectEq
      (ShapeS.toPureProfile Bool Bool
        (GameTheory.EntryDeterrence.fight, GameTheory.EntryDeterrence.br)) :=
  (ShapeS.conditioned_isEquilibriumIn_iff_efg_isSubgamePerfectEq Bool Bool
    (fun x => (GameTheory.EntryDeterrence.uL x.1 x.2,
      GameTheory.EntryDeterrence.uF x.1 x.2))
    (GameTheory.EntryDeterrence.fight, GameTheory.EntryDeterrence.br)).1
      stackelberg_entry_is_conditioned

/-! ## Strict separation of correlation regimes -/

noncomputable section

/-- The verified signal-timing CCE is an ex-ante device equilibrium but not a
private recommendation equilibrium.  This witnesses the strict CCE/CE gap at
the device level. -/
theorem signalTiming_exAnte_not_private :
    (PrivateDevice.canonical GameTheory.SignalTiming.earlySignalGame
      GameTheory.SignalTiming.earlyCCEWitness).IsExAnteEquilibrium ∧
    ¬(PrivateDevice.canonical GameTheory.SignalTiming.earlySignalGame
      GameTheory.SignalTiming.earlyCCEWitness).IsEquilibrium := by
  constructor
  · exact (PrivateDevice.canonical_isExAnteEquilibrium_iff_isCoarseCorrelatedEq
      GameTheory.SignalTiming.earlyCCEWitness).2
        GameTheory.SignalTiming.earlyCCEWitness_isCCE
  · rw [PrivateDevice.canonical_isEquilibrium_iff_isCorrelatedEq]
    intro hCE
    have hmem : (fun i => GameTheory.SignalTiming.earlySignalGame.correlatedEu
        GameTheory.SignalTiming.earlyCCEWitness i) ∈
        GameTheory.SignalTiming.earlySignalGame.correlatedPayoffSet :=
      ⟨GameTheory.SignalTiming.earlyCCEWitness, hCE, rfl⟩
    have hcap := GameTheory.SignalTiming.early_correlated_p1_cap _ hmem
    exact (not_le_of_gt GameTheory.SignalTiming.earlyCCE_p1_value_gt_cap) hcap

/-- The fair matching-pennies law is correlated equilibrium but cannot be a
fully revealing broadcast equilibrium, since matching pennies has no pure
Nash profile in its support (or anywhere else). -/
theorem matchingPennies_private_not_broadcast :
    (PrivateDevice.canonical NFG.matchingPennies.toKernelGame
      (Math.PMFProduct.pmfPi NFG.matchingPenniesFairMixed)).IsEquilibrium ∧
    ¬(BroadcastDevice.canonical NFG.matchingPennies.toKernelGame
      (Math.PMFProduct.pmfPi NFG.matchingPenniesFairMixed)).IsEquilibrium := by
  constructor
  · exact (PrivateDevice.canonical_isEquilibrium_iff_isCorrelatedEq _).2
      NFG.matchingPennies_fair_correlated_eq
  · rw [BroadcastDevice.canonical_isEquilibrium_iff_nashSupport]
    intro h
    obtain ⟨profile, hpos⟩ :=
      (Math.PMFProduct.pmfPi NFG.matchingPenniesFairMixed).support_nonempty
    have hn := h profile hpos
    have hnNFG := (NFG.IsNashPure_iff_kernelGame NFG.matchingPennies profile).2 hn
    exact NFG.matchingPennies_no_pure_nash profile hnNFG

end

end OpenGames.Examples
