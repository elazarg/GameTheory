/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.Bridges.OpenGame_EFG
import GameTheory.Languages.Bridges.OpenGame_Mixed
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

/-! ## Probabilistic open games -/

/-- A deliberately non-convex probabilistic game used to expose the exact
left-unit behavior of relational Kleisli composition. -/
def nonconvexSelection : ProbOpenGame Unit ℝ Unit ℝ where
  Strategy := Bool
  play _ _ := ()
  coplay _ _ r := r
  IsEquilibriumIn _ _ μ :=
    μ = Math.FinPMF.pure false ∨ μ = Math.FinPMF.pure true

/-- Fair randomization on `Bool`, with finite support carried in the type. -/
def fairBoolFin : Math.FinPMF Bool :=
  Math.FinPMF.ofPMF (PMF.uniformOfFintype Bool)

private theorem fairBoolFin_mem_nonconvexClosure :
    fairBoolFin ∈ Math.FinPMF.convexClosure
      {ψ | nonconvexSelection.IsEquilibriumIn () (fun _ => 0) ψ} := by
  refine ⟨Math.FinPMF.map Math.FinPMF.pure fairBoolFin, ?_, by simp⟩
  intro ψ hψ
  rw [Math.FinPMF.support_map] at hψ
  rcases hψ with ⟨b, _hb, rfl⟩
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem fairBoolFin_not_nonconvexEquilibrium :
    ¬nonconvexSelection.IsEquilibriumIn () (fun _ => 0) fairBoolFin := by
  intro h
  rcases h with h | h
  · have hmass := congrArg
      (fun μ : Math.FinPMF Bool => (μ.toPMF false).toReal) h
    norm_num [fairBoolFin, PMF.uniformOfFintype_apply] at hmass
  · have hmass := congrArg
      (fun μ : Math.FinPMF Bool => (μ.toPMF true).toReal) h
    norm_num [fairBoolFin, PMF.uniformOfFintype_apply] at hmass

/-- Without convex-closed equilibrium sets, the paper-style left identity
law fails: `D̄#` admits the fair barycenter although the original game admits
only the two point masses. -/
theorem probabilistic_leftIdentity_requires_convexity :
    (ProbOpenGame.idWire Unit ℝ ;ₚ nonconvexSelection).IsEquilibriumIn ()
        (fun _ => 0)
        (Math.FinPMF.product (Math.FinPMF.pure ()) fairBoolFin) ∧
      ¬nonconvexSelection.IsEquilibriumIn () (fun _ => 0) fairBoolFin := by
  constructor
  · exact (ProbOpenGame.idWire_seq_isEquilibriumIn_product_iff
      nonconvexSelection () (fun _ => 0) fairBoolFin).2
        fairBoolFin_mem_nonconvexClosure
  · exact fairBoolFin_not_nonconvexEquilibrium

/-- Perfectly correlated fair bits. -/
def diagonalBoolFin : Math.FinPMF (Bool × Bool) :=
  Math.FinPMF.map (fun b => (b, b)) fairBoolFin

private theorem fairBoolFin_fullSupport (b : Bool) :
    b ∈ fairBoolFin.support := by
  change PMF.uniformOfFintype Bool b ≠ 0
  rw [PMF.uniformOfFintype_apply]
  norm_num

private theorem diagonalBoolFin_mem_convexClosure_of_pureProducts
    (S : Set (Math.FinPMF (Bool × Bool)))
    (hpure : ∀ b, Math.FinPMF.product (Math.FinPMF.pure b)
      (Math.FinPMF.pure b) ∈ S) :
    diagonalBoolFin ∈ Math.FinPMF.convexClosure S := by
  let vertices : Math.FinPMF (Math.FinPMF (Bool × Bool)) :=
    Math.FinPMF.map
      (fun b => Math.FinPMF.product (Math.FinPMF.pure b)
        (Math.FinPMF.pure b)) fairBoolFin
  refine ⟨vertices, ?_, ?_⟩
  · intro ψ hψ
    rw [show vertices.support =
      (fun b => Math.FinPMF.product (Math.FinPMF.pure b)
        (Math.FinPMF.pure b)) '' fairBoolFin.support by
          exact Math.FinPMF.support_map _ _] at hψ
    rcases hψ with ⟨b, _hb, rfl⟩
    exact hpure b
  · have hvertices : vertices =
        Math.FinPMF.map Math.FinPMF.pure diagonalBoolFin := by
      simp only [vertices, diagonalBoolFin, Math.FinPMF.product_pure,
        Math.FinPMF.map_comp]
      congr 1
    change Math.FinPMF.join vertices = diagonalBoolFin
    rw [hvertices, Math.FinPMF.join_map_pure]

private theorem diagonalBoolFin_not_productOfMarginals :
    diagonalBoolFin ≠
      Math.FinPMF.product (Math.FinPMF.map Prod.fst diagonalBoolFin)
        (Math.FinPMF.map Prod.snd diagonalBoolFin) := by
  intro hfactor
  have hfst : Math.FinPMF.map Prod.fst diagonalBoolFin = fairBoolFin := by
    rw [diagonalBoolFin, Math.FinPMF.map_comp]
    change Math.FinPMF.map id fairBoolFin = fairBoolFin
    exact Math.FinPMF.map_id fairBoolFin
  have hsnd : Math.FinPMF.map Prod.snd diagonalBoolFin = fairBoolFin := by
    rw [diagonalBoolFin, Math.FinPMF.map_comp]
    change Math.FinPMF.map id fairBoolFin = fairBoolFin
    exact Math.FinPMF.map_id fairBoolFin
  have hoffProduct : (false, true) ∈
      (Math.FinPMF.product fairBoolFin fairBoolFin).support :=
    (Math.FinPMF.mem_support_product_iff _ _ _ _).2
      ⟨fairBoolFin_fullSupport false, fairBoolFin_fullSupport true⟩
  have hoffDiagonal : (false, true) ∉ diagonalBoolFin.support := by
    rw [diagonalBoolFin, Math.FinPMF.support_map]
    rintro ⟨b, _hb, hpair⟩
    cases b <;> simp at hpair
  apply hoffDiagonal
  rw [hfactor, hfst, hsnd]
  exact hoffProduct

private theorem diagonalBoolFin_mem_tensorClosure :
    diagonalBoolFin ∈ Math.FinPMF.convexClosure
      {φ | (ProbOpenGame.actionDecision Bool ⊗ₚ
        ProbOpenGame.actionDecision Bool).IsEquilibriumIn ((), ())
          (fun _ => (0, 0)) φ} := by
  apply diagonalBoolFin_mem_convexClosure_of_pureProducts
  intro b
  simp [ProbOpenGame.tensor, ProbOpenGame.actionDecision,
    Math.FinPMF.expect]

private theorem diagonalBoolFin_not_tensorEquilibrium :
    ¬(ProbOpenGame.actionDecision Bool ⊗ₚ
      ProbOpenGame.actionDecision Bool).IsEquilibriumIn ((), ())
        (fun _ => (0, 0)) diagonalBoolFin := by
  intro h
  exact diagonalBoolFin_not_productOfMarginals h.1

/-- Convex closure is not preserved by parallel composition: each pure
diagonal profile is an equilibrium of the zero-payoff decision tensor, but
their correlated fair mixture violates the required independence factor. -/
theorem probabilistic_tensor_equilibria_need_not_be_convex :
    diagonalBoolFin ∈ Math.FinPMF.convexClosure
      {φ | (ProbOpenGame.actionDecision Bool ⊗ₚ
        ProbOpenGame.actionDecision Bool).IsEquilibriumIn ((), ())
          (fun _ => (0, 0)) φ} ∧
      ¬(ProbOpenGame.actionDecision Bool ⊗ₚ
        ProbOpenGame.actionDecision Bool).IsEquilibriumIn ((), ())
          (fun _ => (0, 0)) diagonalBoolFin :=
  ⟨diagonalBoolFin_mem_tensorClosure,
    diagonalBoolFin_not_tensorEquilibrium⟩

/-- Although individual mixed decisions have convex equilibrium sets,
parallel composition need not preserve that property: the tensor requires an
independent joint law, while a convex mixture of independent laws may be
correlated. -/
theorem probabilistic_tensor_does_not_preserve_convexEquilibria :
    ProbOpenGame.HasConvexEquilibria
        (ProbOpenGame.actionDecision Bool) ∧
      ¬ProbOpenGame.HasConvexEquilibria
        (ProbOpenGame.actionDecision Bool ⊗ₚ
          ProbOpenGame.actionDecision Bool) := by
  constructor
  · exact ProbOpenGame.actionDecision_hasConvexEquilibria Bool
  · intro hconvex
    exact diagonalBoolFin_not_tensorEquilibrium
      (hconvex ((), ()) (fun _ => (0, 0))
        diagonalBoolFin_mem_tensorClosure)

/-- A strategically free wire.  It is useful for isolating structural
properties of probabilistic composition from payoff optimality. -/
def freeStrategyWire (StrategyType X S : Type*) : ProbOpenGame X S X S where
  Strategy := StrategyType
  play _ x := x
  coplay _ _ s := s
  IsEquilibriumIn _ _ _ := True

theorem freeStrategyWire_hasConvexEquilibria (StrategyType X S : Type*) :
    ProbOpenGame.HasConvexEquilibria
      (freeStrategyWire StrategyType X S) := by
  intro _ _ _ _
  trivial

private theorem diagonalBoolFin_mem_freeSeqClosure :
    diagonalBoolFin ∈ Math.FinPMF.convexClosure
      {φ | (freeStrategyWire Bool Unit ℝ ;ₚ
        freeStrategyWire Bool Unit ℝ).IsEquilibriumIn ()
          (fun _ => 0) φ} := by
  apply diagonalBoolFin_mem_convexClosure_of_pureProducts
  intro b
  change (freeStrategyWire Bool Unit ℝ ;ₚ
    freeStrategyWire Bool Unit ℝ).IsEquilibriumIn () (fun _ => 0)
      (Math.FinPMF.product (Math.FinPMF.pure b)
        (Math.FinPMF.pure b))
  unfold ProbOpenGame.seq
  simp only [Math.FinPMF.map_fst_product,
    Math.FinPMF.map_snd_product, freeStrategyWire, true_and,
    Math.FinPMF.map_pure]
  apply Math.FinPMF.relKleisli_pure_of_mem
  trivial

private theorem diagonalBoolFin_not_freeSeqEquilibrium :
    ¬(freeStrategyWire Bool Unit ℝ ;ₚ
      freeStrategyWire Bool Unit ℝ).IsEquilibriumIn ()
        (fun _ => 0) diagonalBoolFin := by
  intro h
  exact diagonalBoolFin_not_productOfMarginals h.1

/-- Convex equilibrium sets are not closed under the current sequential
composition either.  Both factors select every mixed strategy, but the
composite additionally requires the joint strategy law to be independent;
the convex mixture of two diagonal point masses is correlated. -/
theorem probabilistic_seq_does_not_preserve_convexEquilibria :
    ProbOpenGame.HasConvexEquilibria
        (freeStrategyWire Bool Unit ℝ) ∧
      ¬ProbOpenGame.HasConvexEquilibria
        (freeStrategyWire Bool Unit ℝ ;ₚ
          freeStrategyWire Bool Unit ℝ) := by
  constructor
  · exact freeStrategyWire_hasConvexEquilibria Bool Unit ℝ
  · intro hconvex
    exact diagonalBoolFin_not_freeSeqEquilibrium
      (hconvex () (fun _ => 0) diagonalBoolFin_mem_freeSeqClosure)

/-- A nonconvex source whose pure strategy is also the emitted history. -/
def binaryHistorySource : ProbOpenGame Unit ℝ Bool ℝ where
  Strategy := Bool
  play b _ := b
  coplay _ _ r := r
  IsEquilibriumIn _ _ μ :=
    μ = Math.FinPMF.pure false ∨ μ = Math.FinPMF.pure true

/-- At history `b`, select exactly the point strategy `b`. -/
def echoHistory : ProbOpenGame Bool ℝ Unit ℝ where
  Strategy := Bool
  play _ _ := ()
  coplay _ _ r := r
  IsEquilibriumIn b _ μ := μ = Math.FinPMF.pure b

/-- The same echo selector, forwarding its chosen bit as the next history. -/
def echoForward : ProbOpenGame Bool ℝ Bool ℝ where
  Strategy := Bool
  play b _ := b
  coplay _ _ r := r
  IsEquilibriumIn b _ μ := μ = Math.FinPMF.pure b

private theorem echoForward_hasConvexEquilibria :
    ProbOpenGame.HasConvexEquilibria echoForward := by
  intro b _ μ hμ
  change μ = Math.FinPMF.pure b
  change μ ∈ Math.FinPMF.convexClosure {Math.FinPMF.pure b} at hμ
  rw [Math.FinPMF.convexClosure_singleton] at hμ
  exact Set.mem_singleton_iff.mp hμ

private theorem relKleisli_echo_fair :
    Math.FinPMF.RelKleisli
      (fun b : Bool => {ψ | ψ = Math.FinPMF.pure b})
      fairBoolFin fairBoolFin := by
  refine ⟨fun b => Math.FinPMF.pure (Math.FinPMF.pure b), ?_, ?_⟩
  · intro b _hb ψ hψ
    simpa using hψ
  · simp only [Math.FinPMF.join]
    simp [Math.FinPMF.bind_bind]

private theorem fairBoolFin_mem_binaryHistorySourceClosure :
    fairBoolFin ∈ Math.FinPMF.convexClosure
      {ψ | binaryHistorySource.IsEquilibriumIn () (fun _ => 0) ψ} := by
  refine ⟨Math.FinPMF.map Math.FinPMF.pure fairBoolFin, ?_, by simp⟩
  intro ψ hψ
  rw [Math.FinPMF.support_map] at hψ
  rcases hψ with ⟨b, _hb, rfl⟩
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem convexifiedHistoryComposition_admits_fairProduct :
    (ProbOpenGame.convexify binaryHistorySource ;ₚ
      echoHistory).IsEquilibriumIn () (fun _ => 0)
        (Math.FinPMF.product fairBoolFin fairBoolFin) := by
  rw [ProbOpenGame.seq_isEquilibriumIn_product_iff]
  constructor
  · exact fairBoolFin_mem_binaryHistorySourceClosure
  · refine ⟨fun b => Math.FinPMF.pure (Math.FinPMF.pure b), ?_, ?_⟩
    · intro b _hb ψ hψ
      simpa [echoHistory] using hψ
    · simp only [Math.FinPMF.join, ProbOpenGame.convexify,
      binaryHistorySource]
      simp only [Math.FinPMF.bind_map, Math.FinPMF.bind_bind,
        Function.comp_apply, Math.FinPMF.pure_bind, id_eq]
      change Math.FinPMF.bind fairBoolFin Math.FinPMF.pure = fairBoolFin
      exact Math.FinPMF.bind_pure fairBoolFin

private theorem binaryHistoryComposition_no_offDiagonal
    (ρ : Math.FinPMF (Bool × Bool))
    (hρ : (binaryHistorySource ;ₚ echoHistory).IsEquilibriumIn ()
      (fun _ => 0) ρ) :
    (false, true) ∉ ρ.support := by
  let μ := Math.FinPMF.map Prod.fst ρ
  let ν := Math.FinPMF.map Prod.snd ρ
  have hfactor : ρ = Math.FinPMF.product μ ν := hρ.1
  have hμ : μ = Math.FinPMF.pure false ∨
      μ = Math.FinPMF.pure true := hρ.2.1
  have hlift := hρ.2.2
  rcases hμ with hμ | hμ
  · have hlift' : Math.FinPMF.RelKleisli
        (fun b => {ψ | ψ = Math.FinPMF.pure b})
        (Math.FinPMF.pure false) ν := by
      simpa [μ, ν, hμ, binaryHistorySource, echoHistory] using hlift
    have hν : ν = Math.FinPMF.pure false := by
      have hclosure := (Math.FinPMF.relKleisli_pure_iff
        (fun b => {ψ | ψ = Math.FinPMF.pure b}) false ν).1 hlift'
      simpa using hclosure
    rw [hfactor, hμ, hν, Math.FinPMF.product_pure]
    simp
  · have hlift' : Math.FinPMF.RelKleisli
        (fun b => {ψ | ψ = Math.FinPMF.pure b})
        (Math.FinPMF.pure true) ν := by
      simpa [μ, ν, hμ, binaryHistorySource, echoHistory] using hlift
    have hν : ν = Math.FinPMF.pure true := by
      have hclosure := (Math.FinPMF.relKleisli_pure_iff
        (fun b => {ψ | ψ = Math.FinPMF.pure b}) true ν).1 hlift'
      simpa using hclosure
    rw [hfactor, hμ, hν, Math.FinPMF.product_pure]
    simp

private theorem fairProduct_not_binaryHistoryCompositionClosure :
    ¬(binaryHistorySource ;ₚ echoHistory).IsConvexEquilibriumIn ()
      (fun _ => 0) (Math.FinPMF.product fairBoolFin fairBoolFin) := by
  rintro ⟨θ, hθ, hjoin⟩
  change Math.FinPMF (Math.FinPMF (Bool × Bool)) at θ
  change ∀ ψ : Math.FinPMF (Bool × Bool), ψ ∈ θ.support →
    (binaryHistorySource ;ₚ echoHistory).IsEquilibriumIn ()
      (fun _ => 0) ψ at hθ
  have hoffJoin : (false, true) ∉ (Math.FinPMF.join θ).support := by
    intro hoff
    change (false, true) ∈
      (θ.toPMF.bind fun ρ => ρ.toPMF).support at hoff
    rw [PMF.mem_support_bind_iff] at hoff
    rcases hoff with ⟨ρ, hρ, hoff⟩
    exact binaryHistoryComposition_no_offDiagonal ρ (hθ ρ hρ) hoff
  have hoffProduct : (false, true) ∈
      (Math.FinPMF.product fairBoolFin fairBoolFin).support :=
    (Math.FinPMF.mem_support_product_iff _ _ _ _).2
      ⟨fairBoolFin_fullSupport false, fairBoolFin_fullSupport true⟩
  apply hoffJoin
  exact (congrArg Math.FinPMF.support hjoin).symm ▸ hoffProduct

/-- Convex-semantic equivalence repairs the unit equations but is not a left
congruence for raw sequential composition.  Saturating the history source
admits independent fair marginals; the unsaturated composite's convex closure
contains only correlated diagonal laws. -/
theorem convexIso_not_left_seq_congruence :
    Nonempty (ProbOpenGame.ConvexIso binaryHistorySource
        (ProbOpenGame.convexify binaryHistorySource)) ∧
      (ProbOpenGame.convexify binaryHistorySource ;ₚ
        echoHistory).IsEquilibriumIn () (fun _ => 0)
          (Math.FinPMF.product fairBoolFin fairBoolFin) ∧
      ¬(binaryHistorySource ;ₚ echoHistory).IsConvexEquilibriumIn ()
        (fun _ => 0) (Math.FinPMF.product fairBoolFin fairBoolFin) :=
  ⟨⟨ProbOpenGame.convexifyConvexIso binaryHistorySource⟩,
    convexifiedHistoryComposition_admits_fairProduct,
    fairProduct_not_binaryHistoryCompositionClosure⟩

private theorem echoForward_seq_equilibrium_eq_pure
    (b : Bool) (ρ : Math.FinPMF (Bool × Bool))
    (hρ : (echoForward ;ₚ echoForward).IsEquilibriumIn b
      (fun _ => 0) ρ) :
    ρ = Math.FinPMF.pure (b, b) := by
  let μ := Math.FinPMF.map Prod.fst ρ
  let ν := Math.FinPMF.map Prod.snd ρ
  have hfactor : ρ = Math.FinPMF.product μ ν := hρ.1
  have hμ : μ = Math.FinPMF.pure b := hρ.2.1
  have hlift : Math.FinPMF.RelKleisli
      (fun y => {ψ | ψ = Math.FinPMF.pure y})
      (Math.FinPMF.pure b) ν := by
    simpa [μ, ν, hμ, echoForward] using hρ.2.2
  have hν : ν = Math.FinPMF.pure b := by
    have hclosure := (Math.FinPMF.relKleisli_pure_iff
      (fun y => {ψ | ψ = Math.FinPMF.pure y}) b ν).1 hlift
    simpa using hclosure
  rw [hfactor, hμ, hν, Math.FinPMF.product_pure]

private theorem rightAssociatedHistory_no_offDiagonal
    (ρ : Math.FinPMF (Bool × (Bool × Bool)))
    (hρ : (ProbOpenGame.convexify binaryHistorySource ;ₚ
      (echoForward ;ₚ echoForward)).IsEquilibriumIn ()
        (fun _ => 0) ρ) :
    (false, (false, true)) ∉ ρ.support := by
  let τ := Math.FinPMF.map Prod.snd ρ
  have hfactor : ρ = Math.FinPMF.product
      (Math.FinPMF.map Prod.fst ρ) τ := hρ.1
  have hdiag : ∀ p, p ∈ τ.support → p.1 = p.2 := by
    apply Math.FinPMF.relKleisli_support hρ.2.2
      (fun p => p.1 = p.2)
    intro b _hb ψ hψ p hp
    have hψeq := echoForward_seq_equilibrium_eq_pure b ψ hψ
    rw [hψeq] at hp
    change Bool × Bool at p
    change p ∈ (Math.FinPMF.pure (b, b) :
      Math.FinPMF (Bool × Bool)).support at hp
    rw [Math.FinPMF.support_pure] at hp
    have hpEq : p = (b, b) := Set.mem_singleton_iff.mp hp
    rw [hpEq]
  intro hoff
  rw [hfactor] at hoff
  have hoff' := (Math.FinPMF.mem_support_product_iff _ _ _ _).1 hoff
  have heq := hdiag (false, true) hoff'.2
  simp at heq

private theorem rightPostRawHistory_no_offDiagonal
    (ρ : Math.FinPMF (Bool × (Bool × Bool)))
    (hρ : (ProbOpenGame.convexify binaryHistorySource ;ₚ
      ProbOpenGame.convexify (echoForward ;ₚ echoForward)).IsEquilibriumIn ()
        (fun _ => 0) ρ) :
    (false, (false, true)) ∉ ρ.support := by
  apply rightAssociatedHistory_no_offDiagonal ρ
  exact (ProbOpenGame.seq_convexify_right_isEquilibriumIn_iff
    (ProbOpenGame.convexify binaryHistorySource)
    (echoForward ;ₚ echoForward) () (fun _ => 0) ρ).1 hρ

private theorem fairRightTriple_not_rightPostClosure :
    ¬(ProbOpenGame.convexify binaryHistorySource ;ₚ
      ProbOpenGame.convexify (echoForward ;ₚ echoForward)
      ).IsConvexEquilibriumIn () (fun _ => 0)
        (Math.FinPMF.product fairBoolFin
          (Math.FinPMF.product fairBoolFin fairBoolFin)) := by
  rintro ⟨θ, hθ, hjoin⟩
  change Math.FinPMF
    (Math.FinPMF (Bool × (Bool × Bool))) at θ
  change ∀ ψ : Math.FinPMF (Bool × (Bool × Bool)), ψ ∈ θ.support →
    (ProbOpenGame.convexify binaryHistorySource ;ₚ
      ProbOpenGame.convexify (echoForward ;ₚ echoForward)
      ).IsEquilibriumIn () (fun _ => 0) ψ at hθ
  have hoffJoin : (false, (false, true)) ∉
      (Math.FinPMF.join θ).support := by
    intro hoff
    change (false, (false, true)) ∈
      (θ.toPMF.bind fun ρ => ρ.toPMF).support at hoff
    rw [PMF.mem_support_bind_iff] at hoff
    rcases hoff with ⟨ρ, hρ, hoff⟩
    exact rightPostRawHistory_no_offDiagonal ρ (hθ ρ hρ) hoff
  have hoffProduct : (false, (false, true)) ∈
      (Math.FinPMF.product fairBoolFin
        (Math.FinPMF.product fairBoolFin fairBoolFin)).support :=
    (Math.FinPMF.mem_support_product_iff _ _ _ _).2
      ⟨fairBoolFin_fullSupport false,
        (Math.FinPMF.mem_support_product_iff _ _ _ _).2
          ⟨fairBoolFin_fullSupport false, fairBoolFin_fullSupport true⟩⟩
  apply hoffJoin
  exact (congrArg Math.FinPMF.support hjoin).symm ▸ hoffProduct

/-- Convex-closed source used by the post-composition repair candidate. -/
def saturatedHistorySource :
    ProbOpenGame.Saturated Unit ℝ Bool ℝ :=
  ⟨ProbOpenGame.convexify binaryHistorySource,
    ProbOpenGame.convexify_hasConvexEquilibria _⟩

/-- Convex-closed echo component. -/
def saturatedEchoForward :
    ProbOpenGame.Saturated Bool ℝ Bool ℝ :=
  ⟨echoForward, echoForward_hasConvexEquilibria⟩

/-- Fully independent fair laws in left-associated strategy coordinates. -/
def fairTripleLeft : Math.FinPMF ((Bool × Bool) × Bool) :=
  Math.FinPMF.product
    (Math.FinPMF.product fairBoolFin fairBoolFin) fairBoolFin

/-- The same independent law in right-associated coordinates. -/
def fairTripleRight : Math.FinPMF (Bool × (Bool × Bool)) :=
  Math.FinPMF.product fairBoolFin
    (Math.FinPMF.product fairBoolFin fairBoolFin)

private theorem convexifiedSource_seq_echo_admits_fairProduct :
    (ProbOpenGame.convexify binaryHistorySource ;ₚ
      echoForward).IsEquilibriumIn () (fun _ => 0)
        (Math.FinPMF.product fairBoolFin fairBoolFin) := by
  rw [ProbOpenGame.seq_isEquilibriumIn_product_iff]
  constructor
  · exact fairBoolFin_mem_binaryHistorySourceClosure
  · change Math.FinPMF.RelKleisli
      (fun b : Bool => {ψ | ψ = Math.FinPMF.pure b})
      (Math.FinPMF.map (fun b => b) fairBoolFin) fairBoolFin
    have hmap : Math.FinPMF.map (fun b => b) fairBoolFin =
        fairBoolFin := by
      change Math.FinPMF.map id fairBoolFin = fairBoolFin
      exact Math.FinPMF.map_id fairBoolFin
    rw [hmap]
    exact relKleisli_echo_fair

private theorem rawLeftAssociated_admits_fairTriple :
    ((ProbOpenGame.convexify binaryHistorySource ;ₚ echoForward) ;ₚ
      echoForward).IsEquilibriumIn () (fun _ => 0) fairTripleLeft := by
  change ((ProbOpenGame.convexify binaryHistorySource ;ₚ echoForward) ;ₚ
    echoForward).IsEquilibriumIn () (fun _ => 0)
      (Math.FinPMF.product
        (Math.FinPMF.product fairBoolFin fairBoolFin) fairBoolFin)
  unfold ProbOpenGame.seq
  simp only [Math.FinPMF.map_fst_product,
    Math.FinPMF.map_snd_product, true_and]
  constructor
  · constructor
    · exact fairBoolFin_mem_binaryHistorySourceClosure
    · change Math.FinPMF.RelKleisli
        (fun b : Bool => {ψ | ψ = Math.FinPMF.pure b})
        (Math.FinPMF.map (fun b => b) fairBoolFin) fairBoolFin
      have hmap : Math.FinPMF.map (fun b => b) fairBoolFin =
          fairBoolFin := by
        change Math.FinPMF.map id fairBoolFin = fairBoolFin
        exact Math.FinPMF.map_id fairBoolFin
      rw [hmap]
      exact relKleisli_echo_fair
  · simpa [ProbOpenGame.seq, ProbOpenGame.convexify,
      binaryHistorySource, echoForward] using relKleisli_echo_fair

private theorem rawRightAssociated_rejects_fairTriple :
    ¬(ProbOpenGame.convexify binaryHistorySource ;ₚ
      (echoForward ;ₚ echoForward)).IsEquilibriumIn ()
        (fun _ => 0) fairTripleRight := by
  intro h
  apply rightAssociatedHistory_no_offDiagonal fairTripleRight h
  exact (Math.FinPMF.mem_support_product_iff _ _ _ _).2
    ⟨fairBoolFin_fullSupport false,
      (Math.FinPMF.mem_support_product_iff _ _ _ _).2
        ⟨fairBoolFin_fullSupport false, fairBoolFin_fullSupport true⟩⟩

/-- The paper-style raw sequential composition fails the claimed canonical
associativity law (Theorem 15): reassociation transports the fully independent
fair law, but the right grouping forces its two downstream coordinates to be
diagonally correlated. -/
theorem probabilistic_seq_not_associative :
    Math.FinPMF.map (fun p => (p.1.1, (p.1.2, p.2))) fairTripleLeft =
        fairTripleRight ∧
      ((ProbOpenGame.convexify binaryHistorySource ;ₚ echoForward) ;ₚ
        echoForward).IsEquilibriumIn () (fun _ => 0) fairTripleLeft ∧
      ¬(ProbOpenGame.convexify binaryHistorySource ;ₚ
        (echoForward ;ₚ echoForward)).IsEquilibriumIn ()
          (fun _ => 0) fairTripleRight := by
  constructor
  · exact Math.FinPMF.map_assoc_product fairBoolFin fairBoolFin fairBoolFin
  · exact ⟨rawLeftAssociated_admits_fairTriple,
      rawRightAssociated_rejects_fairTriple⟩

private theorem leftPostRaw_admits_fairTriple :
    (ProbOpenGame.convexify
        (ProbOpenGame.convexify binaryHistorySource ;ₚ echoForward) ;ₚ
      echoForward).IsEquilibriumIn () (fun _ => 0) fairTripleLeft := by
  change (ProbOpenGame.convexify
      (ProbOpenGame.convexify binaryHistorySource ;ₚ echoForward) ;ₚ
    echoForward).IsEquilibriumIn () (fun _ => 0)
      (Math.FinPMF.product
        (Math.FinPMF.product fairBoolFin fairBoolFin) fairBoolFin)
  unfold ProbOpenGame.seq
  simp only [Math.FinPMF.map_fst_product,
    Math.FinPMF.map_snd_product, true_and]
  constructor
  · exact Math.FinPMF.subset_convexClosure _
      convexifiedSource_seq_echo_admits_fairProduct
  · simpa [ProbOpenGame.seq, ProbOpenGame.convexify,
      binaryHistorySource, echoForward] using relKleisli_echo_fair

private theorem leftPostClosed_admits_fairTriple :
    (ProbOpenGame.Saturated.seq
      (ProbOpenGame.Saturated.seq saturatedHistorySource
        saturatedEchoForward)
      saturatedEchoForward).1.IsEquilibriumIn () (fun _ => 0)
        fairTripleLeft := by
  change fairTripleLeft ∈ Math.FinPMF.convexClosure
    {ψ | (ProbOpenGame.convexify
      (ProbOpenGame.convexify binaryHistorySource ;ₚ echoForward) ;ₚ
        echoForward).IsEquilibriumIn () (fun _ => 0) ψ}
  exact Math.FinPMF.subset_convexClosure _
    leftPostRaw_admits_fairTriple

private theorem rightPostClosed_rejects_fairTriple :
    ¬(ProbOpenGame.Saturated.seq saturatedHistorySource
      (ProbOpenGame.Saturated.seq saturatedEchoForward
        saturatedEchoForward)).1.IsEquilibriumIn () (fun _ => 0)
          fairTripleRight := by
  exact fairRightTriple_not_rightPostClosure

/-- Post-closing composition on convex games still fails the canonical
associativity law.  The left grouping admits three independent fair laws; the
right grouping forces the two echo strategies to remain diagonally
correlated. -/
theorem saturated_seq_not_associative :
    Math.FinPMF.map (fun p => (p.1.1, (p.1.2, p.2))) fairTripleLeft =
        fairTripleRight ∧
      (ProbOpenGame.Saturated.seq
        (ProbOpenGame.Saturated.seq saturatedHistorySource
          saturatedEchoForward)
        saturatedEchoForward).1.IsEquilibriumIn () (fun _ => 0)
          fairTripleLeft ∧
      ¬(ProbOpenGame.Saturated.seq saturatedHistorySource
        (ProbOpenGame.Saturated.seq saturatedEchoForward
          saturatedEchoForward)).1.IsEquilibriumIn () (fun _ => 0)
            fairTripleRight := by
  constructor
  · exact Math.FinPMF.map_assoc_product fairBoolFin fairBoolFin fairBoolFin
  · exact ⟨leftPostClosed_admits_fairTriple,
      rightPostClosed_rejects_fairTriple⟩

private instance matchingPenniesOutcomeFinite :
    Finite NFG.matchingPennies.Outcome := by
  change Finite (∀ _ : Bool, NFG.MPAction)
  infer_instance

/-- The fair action marginal, now carrying finite support in its type. -/
def matchingPenniesFairFin : Math.FinPMF NFG.MPAction :=
  Math.FinPMF.ofPMF (PMF.uniformOfFintype NFG.MPAction)

/-- The `GProb` decision tensor solves Matching Pennies at the fair product
strategy, through the generic bridge to the existing mixed-Nash theorem. -/
theorem matchingPennies_fair_probabilistic_equilibrium :
    (ProbOpenGame.actionDecision NFG.MPAction ⊗ₚ
      ProbOpenGame.actionDecision NFG.MPAction).IsEquilibriumIn ((), ())
        (ProbOpenGame.boolPayoffPair NFG.matchingPennies)
        (Math.FinPMF.product matchingPenniesFairFin
          matchingPenniesFairFin) := by
  rw [ProbOpenGame.actionDecision_tensor_isEquilibriumIn_iff_isNashMixed]
  have heq :
      ProbOpenGame.boolMixedProfile matchingPenniesFairFin
          matchingPenniesFairFin = NFG.matchingPenniesFairMixed := by
    funext i
    cases i <;> rfl
  rw [heq]
  exact NFG.matchingPennies_fair_mixed_nash

/-- Complete solution of the probabilistic open-game presentation of
Matching Pennies: both marginals put probability one half on heads. -/
theorem matchingPennies_probabilistic_equilibrium_iff_half
    (μfalse μtrue : Math.FinPMF NFG.MPAction) :
    (ProbOpenGame.actionDecision NFG.MPAction ⊗ₚ
      ProbOpenGame.actionDecision NFG.MPAction).IsEquilibriumIn ((), ())
        (ProbOpenGame.boolPayoffPair NFG.matchingPennies)
        (Math.FinPMF.product μfalse μtrue) ↔
      (μtrue.toPMF NFG.MPAction.heads).toReal = (1 / 2 : ℝ) ∧
        (μfalse.toPMF NFG.MPAction.heads).toReal = (1 / 2 : ℝ) := by
  rw [ProbOpenGame.actionDecision_tensor_isEquilibriumIn_iff_isNashMixed]
  exact NFG.matchingPennies_mixed_nash_iff_half
    (ProbOpenGame.boolMixedProfile μfalse μtrue)

end

end OpenGames.Examples
