/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.FiniteRankedTerminalChildNashClosure

/-!
# Terminal perturbation robustness of the finite public-tree backward-Nash profile

The backward-induction Nash construction of
`FinitePublicTerminalNashSystem.lean` selects one
behavior profile from one terminal obstacle.  This file measures what happens
to that *already selected* profile when the terminal obstacle is replaced by a
uniformly close one.  Nothing is reselected: the profile stays the profile of
the original obstacle.

Write `σ` for `FinitePublicTerminalNashSystem.profile obstacle` and suppose
`|perturbed history who - obstacle history who| ≤ error` at every terminal
public history and for every player.  Then:

* the prescribed terminal expectation moves by at most `error`
  (`abs_expect_perturbed_sub_expect_obstacle_le`);
* every history-dependent unilateral behavior deviation gains at most
  `2 * error` against the perturbed obstacle
  (`expect_perturbed_deviation_le_expect_perturbed`);
* the same `2 * error` deviation bound holds at *every* node of the bounded
  public-history tree, not just at the root
  (`worstUnilateral_le_prescribed_add_two_error`).

The constant is depth free.  The middle step of the deviation estimate uses
the *exact* Nash property of `σ` for `obstacle`, so no per-level error
accumulates; the tree depth `fuel` never enters the bound.

## Sharpness

`TerminalPerturbationSharpness.exists_gain_eq` exhibits, for every accuracy
`error ≥ 0` and every margin `slack > 0`, a one-stage one-player game and a
pair of terminal payoff systems at uniform distance `error` for which one
behavior deviation gains *exactly* `2 * error - slack` against the perturbed
system.  Letting `slack` tend to zero shows the constant `2` cannot be
lowered; `TerminalPerturbationSharpness.exists_gain_gt_error` records the
weaker but immediate consequence that `error` alone never suffices.

## Relation to `FiniteRankedTerminalChildCoverage.ObstacleCloseness`

`FiniteRankedTerminalChildCoverage.ObstacleCloseness` is an *assumed*
hypothesis of `FiniteRankedTerminalChildNashClosure`: it says that the three
delayed child obstacles (`lowerObstacle`, `upperObstacle`,
`deviationObstacle`) are each within `childError` of the fixed child-target
obstacle at every terminal public history.  That is a statement about the
chosen child adaptive-potential witnesses, not about the backward-Nash
selection, and terminal perturbation robustness therefore cannot *derive* it.
What this file supplies is the missing *consequence* of that hypothesis:
`ObstacleCloseness` is consumed there only to anchor the three roots within
`childError` of `parentTarget`, and the surrounding file explicitly claims no
incentive-safety for the composed object.  The theorems
`FiniteRankedTerminalChildCoverage.selection_lowerObstacle_deviation_le`,
`…_upperObstacle_deviation_le` and `…_deviationObstacle_deviation_le` below
take exactly that structure as input and conclude that the unchanged
backward-Nash selection is a `2 * childError`-equilibrium for each of the
three actual delayed obstacles.  They are stated against the real
`ObstacleCloseness` structure and need no adapter; the mismatch is only in
direction — the structure is consumed here, never produced.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.PMFProduct Math.Probability
open Math.ProbabilityMassFunction

variable {ι : Type} {G : StochasticGame ι}

namespace FinitePublicTerminalNashSystem

open FiniteFullHistoryControlledStoppingModel

/-- Uniform terminal closeness of two payoff systems on the same finite
public tree: at every complete public history and for every player the two
terminal payoffs differ by at most `error`. -/
def TerminalObstacleClose {fuel : ℕ}
    (obstacle perturbed : G.Hist fuel → Payoff ι) (error : ℝ) : Prop :=
  ∀ (history : G.Hist fuel) (who : ι),
    |perturbed history who - obstacle history who| ≤ error

section Basic

variable
    [Fintype ι] [DecidableEq ι]
    [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)]
    {fuel : ℕ}

omit [∀ who, Nonempty (G.Act who)] in
/-- Two uniformly close integrands have uniformly close expectations. -/
private theorem abs_expect_sub_expect_le
    {Ω : Type} [Finite Ω] (law : PMF Ω) (left right : Ω → ℝ)
    {bound : ℝ}
    (close : ∀ point, |left point - right point| ≤ bound) :
    |expect law left - expect law right| ≤ bound := by
  rw [← expect_sub]
  exact abs_expect_le_of_abs_le law _ close

omit [∀ who, Nonempty (G.Act who)] in
/-- Monotonicity of `expect` needs the pointwise bound only on the support. -/
private theorem expect_mono_on_support
    {Ω : Type} [Finite Ω] (law : PMF Ω) (left right : Ω → ℝ)
    (hle : ∀ point ∈ law.support, left point ≤ right point) :
    expect law left ≤ expect law right := by
  classical
  let patched : Ω → ℝ :=
    fun point => if law point = 0 then right point else left point
  calc
    expect law left = expect law patched := by
      refine expect_congr_on_support law _ _ (fun point member => ?_)
      have nonzero : law point ≠ 0 := by
        simpa [PMF.mem_support_iff] using member
      simp [patched, nonzero]
    _ ≤ expect law right := by
      refine expect_mono law _ _ (fun point => ?_)
      by_cases zero : law point = 0
      · simp [patched, zero]
      · have member : point ∈ law.support := by
          simpa [PMF.mem_support_iff] using zero
        simpa [patched, zero] using hle point member

omit [∀ who, Nonempty (G.Act who)] in
/-- One-sided form of `abs_expect_sub_expect_le`. -/
private theorem expect_le_expect_add
    {Ω : Type} [Finite Ω] (law : PMF Ω) (left right : Ω → ℝ)
    {bound : ℝ}
    (close : ∀ point, |left point - right point| ≤ bound) :
    expect law left ≤ expect law right + bound := by
  have bounded := abs_expect_sub_expect_le law left right close
  have := (abs_le.mp bounded).2
  linarith

variable [Finite G.State]

/-- **Prescribed-payoff displacement.** Evaluating a uniformly close terminal
payoff system along the *unchanged* backward-Nash history law moves the
prescribed expectation by at most `error`, for each player separately. -/
theorem abs_expect_perturbed_sub_expect_obstacle_le
    (obstacle perturbed : G.Hist fuel → Payoff ι) {error : ℝ}
    (close : TerminalObstacleClose obstacle perturbed error)
    (initial : G.State) (who : ι) :
    |expect
        (G.histDist (profile (G := G) obstacle) initial fuel)
        (fun history => perturbed history who) -
      expect
        (G.histDist (profile (G := G) obstacle) initial fuel)
        (fun history => obstacle history who)| ≤ error :=
  abs_expect_sub_expect_le
    (G.histDist (profile (G := G) obstacle) initial fuel)
    (fun history => perturbed history who)
    (fun history => obstacle history who)
    (fun history => close history who)

/-- The same displacement bound stated against the endogenous
backward-induction root payoff of the original obstacle. -/
theorem abs_expect_perturbed_sub_rootPayoff_le
    (obstacle perturbed : G.Hist fuel → Payoff ι) {error : ℝ}
    (close : TerminalObstacleClose obstacle perturbed error)
    (initial : G.State) (who : ι) :
    |expect
        (G.histDist (profile (G := G) obstacle) initial fuel)
        (fun history => perturbed history who) -
      rootPayoff (G := G) obstacle initial who| ≤ error := by
  have root_eq :
      rootPayoff (G := G) obstacle initial who =
        expect
          (G.histDist (profile (G := G) obstacle) initial fuel)
          (fun history => obstacle history who) :=
    (expect_obstacle_profile_eq_root obstacle initial who).symm
  rw [root_eq]
  exact abs_expect_perturbed_sub_expect_obstacle_le
    obstacle perturbed close initial who

/-- **Depth-free deviation robustness.** Against the perturbed terminal
payoff system, every history-dependent unilateral behavior deviation from the
unchanged backward-Nash profile gains at most `2 * error`.

The middle step is the *exact* Nash property of the profile for the original
obstacle, so nothing accumulates with the tree depth. -/
theorem expect_perturbed_deviation_le_expect_perturbed
    (obstacle perturbed : G.Hist fuel → Payoff ι) {error : ℝ}
    (close : TerminalObstacleClose obstacle perturbed error)
    (initial : G.State) (who : ι) (deviation : G.BehaviorStrategy who) :
    expect
        (G.histDist
          (Function.update (profile (G := G) obstacle) who deviation)
          initial fuel)
        (fun history => perturbed history who) ≤
      expect
        (G.histDist (profile (G := G) obstacle) initial fuel)
        (fun history => perturbed history who) +
        2 * error := by
  have deviated :
      expect
          (G.histDist
            (Function.update (profile (G := G) obstacle) who deviation)
            initial fuel)
          (fun history => perturbed history who) ≤
        expect
          (G.histDist
            (Function.update (profile (G := G) obstacle) who deviation)
            initial fuel)
          (fun history => obstacle history who) + error :=
    expect_le_expect_add _ _ _ (fun history => close history who)
  have nash :=
    expect_obstacle_deviation_le_profile obstacle initial who deviation
  have prescribed :
      expect
          (G.histDist (profile (G := G) obstacle) initial fuel)
          (fun history => obstacle history who) ≤
        expect
          (G.histDist (profile (G := G) obstacle) initial fuel)
          (fun history => perturbed history who) + error := by
    refine expect_le_expect_add _ _ _ (fun history => ?_)
    rw [abs_sub_comm]
    exact close history who
  linarith

/-- Deviation robustness stated against the endogenous root payoff of the
original obstacle. -/
theorem expect_perturbed_deviation_le_rootPayoff
    (obstacle perturbed : G.Hist fuel → Payoff ι) {error : ℝ}
    (close : TerminalObstacleClose obstacle perturbed error)
    (initial : G.State) (who : ι) (deviation : G.BehaviorStrategy who) :
    expect
        (G.histDist
          (Function.update (profile (G := G) obstacle) who deviation)
          initial fuel)
        (fun history => perturbed history who) ≤
      rootPayoff (G := G) obstacle initial who + error := by
  have deviated :
      expect
          (G.histDist
            (Function.update (profile (G := G) obstacle) who deviation)
            initial fuel)
          (fun history => perturbed history who) ≤
        expect
          (G.histDist
            (Function.update (profile (G := G) obstacle) who deviation)
            initial fuel)
          (fun history => obstacle history who) + error :=
    expect_le_expect_add _ _ _ (fun history => close history who)
  have nash :=
    expect_obstacle_deviation_le_profile obstacle initial who deviation
  have root_eq :
      rootPayoff (G := G) obstacle initial who =
        expect
          (G.histDist (profile (G := G) obstacle) initial fuel)
          (fun history => obstacle history who) :=
    (expect_obstacle_profile_eq_root obstacle initial who).symm
  rw [root_eq]
  linarith

/-- **Approximate equilibrium existence without reselection.** The profile
selected by backward induction for `obstacle` supports a single payoff vector
which is the exact prescribed expectation of the perturbed terminal payoff
system and which no unilateral behavior deviation can beat by more than
`2 * error`. -/
theorem exists_perturbed_approximateNashPayoff
    (obstacle perturbed : G.Hist fuel → Payoff ι) {error : ℝ}
    (close : TerminalObstacleClose obstacle perturbed error)
    (initial : G.State) :
    ∃ target : Payoff ι,
      (∀ who,
        expect
            (G.histDist (profile (G := G) obstacle) initial fuel)
            (fun history => perturbed history who) =
          target who) ∧
      (∀ who,
        |target who - rootPayoff (G := G) obstacle initial who| ≤ error) ∧
      (∀ who (deviation : G.BehaviorStrategy who),
        expect
            (G.histDist
              (Function.update (profile (G := G) obstacle) who deviation)
              initial fuel)
            (fun history => perturbed history who) ≤
          target who + 2 * error) := by
  refine
    ⟨fun who =>
      expect
        (G.histDist (profile (G := G) obstacle) initial fuel)
        (fun history => perturbed history who),
      fun _ => rfl, ?_, ?_⟩
  · intro who
    exact abs_expect_perturbed_sub_rootPayoff_le
      obstacle perturbed close initial who
  · intro who deviation
    exact expect_perturbed_deviation_le_expect_perturbed
      obstacle perturbed close initial who deviation

end Basic

section Subgame

variable
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)]
    {fuel : ℕ}

/-- The finite controlled stopping model driven by the backward-Nash profile
of `obstacle` while reading `terminalPayoff` at the horizon. -/
private abbrev selectedModel
    (obstacle terminalPayoff : G.Hist fuel → Payoff ι) :
    FiniteControlledStoppingModel
      ι (G.BoundedStoppedHistory fuel) G.Act :=
  G.finiteFullHistoryControlledStoppingModel
    (profile (G := G) obstacle) terminalPayoff

omit [Finite G.State] in
/-- At a full-horizon node the model obstacle is the terminal payoff. -/
private theorem modelObstacle_eq
    (obstacle terminalPayoff : G.Hist fuel → Payoff ι)
    (node : G.BoundedStoppedHistory fuel)
    (full : G.IsFullHorizonNode node) (who : ι) :
    (selectedModel obstacle terminalPayoff).obstacle node who =
      terminalPayoff (G.fullHistoryOfBoundedNode node full) who := by
  change G.fullPublicHistoryObstacle terminalPayoff node who = _
  unfold fullPublicHistoryObstacle
  rw [dif_pos full]

omit [Finite G.State] in
/-- Away from the horizon the model obstacle vanishes. -/
private theorem modelObstacle_eq_zero
    (obstacle terminalPayoff : G.Hist fuel → Payoff ι)
    (node : G.BoundedStoppedHistory fuel)
    (not_full : ¬G.IsFullHorizonNode node) (who : ι) :
    (selectedModel obstacle terminalPayoff).obstacle node who = 0 := by
  change G.fullPublicHistoryObstacle terminalPayoff node who = 0
  unfold fullPublicHistoryObstacle
  rw [dif_neg not_full]

omit [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Fintype (G.Act who)] [∀ who, Nonempty (G.Act who)] in
/-- A nonterminal bounded node has not yet exhausted the horizon. -/
private theorem lt_fuel_of_not_full
    (node : G.BoundedStoppedHistory fuel)
    (not_full : ¬G.IsFullHorizonNode node) :
    node.1.val < fuel := by
  unfold IsFullHorizonNode at not_full
  have length_le : node.1.val ≤ fuel := Nat.lt_succ_iff.mp node.1.isLt
  omega

/-- One prescribed step of the selected model is one stage of the
backward-Nash local profile followed by the transition kernel. -/
private theorem expect_prescribedKernel_eq
    (obstacle : G.Hist fuel → Payoff ι)
    (node : G.BoundedStoppedHistory fuel)
    (strict : node.1.val < fuel)
    (value : G.BoundedStoppedHistory fuel → ℝ) :
    expect
        (G.boundedPublicHistoryPrescribedKernel
          (profile (G := G) obstacle) node) value =
      expect (pmfPi (nodeMixed (obstacle := obstacle) node)) fun action =>
        expect (G.transition node.2.2 action) fun next =>
          value
            (G.boundedPublicHistorySuccessor node strict action next) := by
  rw [boundedPublicHistoryPrescribedKernel, dif_pos strict, expect_bind]
  have actions :
      G.stageActionDist (profile (G := G) obstacle) node.2 =
        pmfPi (nodeMixed (obstacle := obstacle) node) := by
    unfold stageActionDist
    congr 1
    funext player
    exact profile_of_lt obstacle player node.2 strict
  rw [actions]
  apply congrArg
  funext action
  rw [expect_bind]
  apply congrArg
  funext next
  rw [expect_pure]

/-- One controlled step of the selected model replaces the deviator's local
mixed action by a pure one. -/
private theorem expect_controlledKernel_eq
    (obstacle : G.Hist fuel → Payoff ι)
    (node : G.BoundedStoppedHistory fuel)
    (strict : node.1.val < fuel) (who : ι) (pure : G.Act who)
    (value : G.BoundedStoppedHistory fuel → ℝ) :
    expect
        (G.boundedPublicHistoryControlledKernel
          (profile (G := G) obstacle) node who pure) value =
      expect
          (pmfPi
            (Function.update (nodeMixed (obstacle := obstacle) node) who
              (PMF.pure pure))) fun action =>
        expect (G.transition node.2.2 action) fun next =>
          value
            (G.boundedPublicHistorySuccessor node strict action next) := by
  rw [boundedPublicHistoryControlledKernel, dif_pos strict, expect_bind]
  have actions :
      (fun player => profile (G := G) obstacle player node.1.val node.2) =
        nodeMixed (obstacle := obstacle) node := by
    funext player
    exact profile_of_lt obstacle player node.2 strict
  rw [actions]
  apply congrArg
  funext action
  rw [expect_bind]
  apply congrArg
  funext next
  rw [expect_pure]

omit [Finite G.State] in
/-- Terminal case of the node-level prescribed/backward-value identity. -/
private theorem prescribedNodePotential_of_full
    (obstacle : G.Hist fuel → Payoff ι) (who : ι)
    (node : G.BoundedStoppedHistory fuel)
    (full : G.IsFullHorizonNode node) :
    prescribedNodePotential
        (profile (G := G) obstacle) obstacle who node =
      nodeValue (obstacle := obstacle) node who := by
  have terminal : (selectedModel obstacle obstacle).terminal node := full
  change (selectedModel obstacle obstacle).prescribedPotential who node = _
  rw [(selectedModel obstacle obstacle).prescribedPotential_eq_obstacle_of_terminal
    who node terminal]
  rw [modelObstacle_eq obstacle obstacle node full who]
  rw [nodeValue_of_full obstacle node full]

omit [Finite G.State] in
/-- Terminal case of the node-level worst-unilateral estimate. -/
private theorem worstUnilateralNodePotential_of_full
    (obstacle : G.Hist fuel → Payoff ι) (who : ι)
    (node : G.BoundedStoppedHistory fuel)
    (full : G.IsFullHorizonNode node) :
    worstUnilateralNodePotential
        (profile (G := G) obstacle) obstacle who node =
      nodeValue (obstacle := obstacle) node who := by
  have terminal : (selectedModel obstacle obstacle).terminal node := full
  change (selectedModel obstacle obstacle).worstCasePotential who node = _
  rw [(selectedModel obstacle obstacle).worstCasePotential_eq_obstacle_of_terminal
    who node terminal]
  rw [modelObstacle_eq obstacle obstacle node full who]
  rw [nodeValue_of_full obstacle node full]

/-- The prescribed node envelope of the backward-Nash model is exactly the
backward-induction node value, at every node of the bounded tree. -/
theorem prescribedNodePotential_eq_nodeValue
    (obstacle : G.Hist fuel → Payoff ι) (who : ι)
    (node : G.BoundedStoppedHistory fuel) :
    prescribedNodePotential
        (profile (G := G) obstacle) obstacle who node =
      nodeValue (obstacle := obstacle) node who := by
  have key :
      ∀ bound (base : G.BoundedStoppedHistory fuel),
        G.boundedPublicHistoryRank base ≤ bound →
          prescribedNodePotential
              (profile (G := G) obstacle) obstacle who base =
            nodeValue (obstacle := obstacle) base who := by
    intro bound
    induction bound with
    | zero =>
        intro base rank_le
        refine prescribedNodePotential_of_full obstacle who base ?_
        unfold boundedPublicHistoryRank at rank_le
        unfold IsFullHorizonNode
        have length_le : base.1.val ≤ fuel := Nat.lt_succ_iff.mp base.1.isLt
        omega
    | succ bound ih =>
        intro base rank_le
        by_cases full : G.IsFullHorizonNode base
        · exact prescribedNodePotential_of_full obstacle who base full
        · have nonterminal :
              ¬(selectedModel obstacle obstacle).terminal base := full
          have strict : base.1.val < fuel := lt_fuel_of_not_full base full
          have harmonic :=
            (selectedModel obstacle obstacle).prescribedPotential_harmonic
              who base nonterminal
          change
            (selectedModel obstacle obstacle).prescribedPotential who base = _
          refine Eq.trans harmonic.symm ?_
          have congr_support :
              expect
                  ((selectedModel obstacle obstacle).prescribedKernel base)
                  ((selectedModel obstacle obstacle).prescribedPotential
                    who) =
                expect
                  (G.boundedPublicHistoryPrescribedKernel
                    (profile (G := G) obstacle) base)
                  (fun next =>
                    nodeValue (obstacle := obstacle) next who) := by
            refine expect_congr_on_support _ _ _ (fun next member => ?_)
            have nonzero :
                (selectedModel obstacle obstacle).prescribedKernel base
                    next ≠ 0 := by
              simpa [PMF.mem_support_iff] using member
            have step :=
              (selectedModel obstacle obstacle).prescribed_step_rank
                base next nonterminal nonzero
            have step' :
                G.boundedPublicHistoryRank next + 1 =
                  G.boundedPublicHistoryRank base := step
            exact ih next (by omega)
          rw [congr_support, expect_prescribedKernel_eq obstacle base strict]
          exact (nodeValue_of_not_full obstacle base full who).symm
  exact key (G.boundedPublicHistoryRank node) node le_rfl

/-- The worst-unilateral node envelope of the backward-Nash model never
exceeds the backward-induction node value. -/
theorem worstUnilateralNodePotential_le_nodeValue
    (obstacle : G.Hist fuel → Payoff ι) (who : ι)
    (node : G.BoundedStoppedHistory fuel) :
    worstUnilateralNodePotential
        (profile (G := G) obstacle) obstacle who node ≤
      nodeValue (obstacle := obstacle) node who := by
  have key :
      ∀ bound (base : G.BoundedStoppedHistory fuel),
        G.boundedPublicHistoryRank base ≤ bound →
          worstUnilateralNodePotential
              (profile (G := G) obstacle) obstacle who base ≤
            nodeValue (obstacle := obstacle) base who := by
    intro bound
    induction bound with
    | zero =>
        intro base rank_le
        refine le_of_eq
          (worstUnilateralNodePotential_of_full obstacle who base ?_)
        unfold boundedPublicHistoryRank at rank_le
        unfold IsFullHorizonNode
        have length_le : base.1.val ≤ fuel := Nat.lt_succ_iff.mp base.1.isLt
        omega
    | succ bound ih =>
        intro base rank_le
        by_cases full : G.IsFullHorizonNode base
        · exact le_of_eq
            (worstUnilateralNodePotential_of_full obstacle who base full)
        · have nonterminal :
              ¬(selectedModel obstacle obstacle).terminal base := full
          have strict : base.1.val < fuel := lt_fuel_of_not_full base full
          obtain ⟨depth, rank_eq⟩ :=
            (selectedModel obstacle obstacle).rank_eq_succ_of_nonterminal
              base nonterminal
          have base_rank :
              G.boundedPublicHistoryRank base = depth + 1 := rank_eq
          obtain ⟨pure, pure_eq⟩ :=
            (selectedModel obstacle
                obstacle).exists_controlled_expect_eq_maxControlledValue
              who base
              ((selectedModel obstacle obstacle).deviationEnvelope depth who)
          have unfold_worst :
              worstUnilateralNodePotential
                  (profile (G := G) obstacle) obstacle who base =
                expect
                  ((selectedModel obstacle obstacle).controlledKernel
                    base who pure)
                  ((selectedModel obstacle obstacle).deviationEnvelope
                    depth who) := by
            change
              (selectedModel obstacle obstacle).deviationEnvelope
                ((selectedModel obstacle obstacle).rank base) who base = _
            rw [rank_eq,
              (selectedModel obstacle
                  obstacle).deviationEnvelope_succ_of_nonterminal
                depth who base nonterminal,
              ← pure_eq]
          rw [unfold_worst]
          calc
            expect
                ((selectedModel obstacle obstacle).controlledKernel
                  base who pure)
                ((selectedModel obstacle obstacle).deviationEnvelope
                  depth who) =
              expect
                ((selectedModel obstacle obstacle).controlledKernel
                  base who pure)
                (worstUnilateralNodePotential
                  (profile (G := G) obstacle) obstacle who) := by
                  refine expect_congr_on_support _ _ _
                    (fun next member => ?_)
                  have nonzero :
                      (selectedModel obstacle obstacle).controlledKernel
                          base who pure next ≠ 0 := by
                    simpa [PMF.mem_support_iff] using member
                  have step :=
                    (selectedModel obstacle obstacle).controlled_step_rank
                      base who pure next nonterminal nonzero
                  have step' :
                      G.boundedPublicHistoryRank next + 1 =
                        G.boundedPublicHistoryRank base := step
                  have rank_next :
                      G.boundedPublicHistoryRank next = depth := by omega
                  change
                    (selectedModel obstacle obstacle).deviationEnvelope
                        depth who next =
                      (selectedModel obstacle obstacle).deviationEnvelope
                        (G.boundedPublicHistoryRank next) who next
                  rw [rank_next]
            _ ≤
              expect
                ((selectedModel obstacle obstacle).controlledKernel
                  base who pure)
                (fun next => nodeValue (obstacle := obstacle) next who) := by
                  refine expect_mono_on_support _ _ _
                    (fun next member => ?_)
                  have nonzero :
                      (selectedModel obstacle obstacle).controlledKernel
                          base who pure next ≠ 0 := by
                    simpa [PMF.mem_support_iff] using member
                  have step :=
                    (selectedModel obstacle obstacle).controlled_step_rank
                      base who pure next nonterminal nonzero
                  have step' :
                      G.boundedPublicHistoryRank next + 1 =
                        G.boundedPublicHistoryRank base := step
                  exact ih next (by omega)
            _ ≤ nodeValue (obstacle := obstacle) base who := by
                  have kernel_eq :
                      (selectedModel obstacle obstacle).controlledKernel
                          base who pure =
                        G.boundedPublicHistoryControlledKernel
                          (profile (G := G) obstacle) base who pure := rfl
                  rw [kernel_eq,
                    expect_controlledKernel_eq obstacle base strict who pure]
                  exact unilateralContinuation_le_nodeValue
                    obstacle base full who (PMF.pure pure)
  exact key (G.boundedPublicHistoryRank node) node le_rfl

/-- **Exact subgame perfection of the backward-Nash selection.** At every node
of the bounded public-history tree the worst-unilateral and prescribed
envelopes of the selected profile against its own terminal obstacle coincide.
This upgrades the root-only
`FinitePublicTerminalNashSystem.worstCasePotential_eq_prescribedPotential`. -/
theorem worstUnilateralNodePotential_eq_prescribedNodePotential
    (obstacle : G.Hist fuel → Payoff ι) (who : ι)
    (node : G.BoundedStoppedHistory fuel) :
    worstUnilateralNodePotential
        (profile (G := G) obstacle) obstacle who node =
      prescribedNodePotential
        (profile (G := G) obstacle) obstacle who node := by
  refine le_antisymm ?_ ?_
  · rw [prescribedNodePotential_eq_nodeValue obstacle who node]
    exact worstUnilateralNodePotential_le_nodeValue obstacle who node
  · exact FiniteControlledStoppingModel.prescribedPotential_le_worstCasePotential
      (selectedModel obstacle obstacle) who node

omit [Finite G.State] in
/-- Uniform closeness of the terminal payoffs transfers to the model
obstacles, which agree (at value `0`) away from the horizon. -/
private theorem abs_modelObstacle_sub_le
    (obstacle left right : G.Hist fuel → Payoff ι) {error : ℝ}
    (error_nonneg : 0 ≤ error)
    (close : ∀ (history : G.Hist fuel) (who : ι),
      |left history who - right history who| ≤ error)
    (node : G.BoundedStoppedHistory fuel) (who : ι) :
    |(selectedModel obstacle left).obstacle node who -
      (selectedModel obstacle right).obstacle node who| ≤ error := by
  by_cases full : G.IsFullHorizonNode node
  · rw [modelObstacle_eq obstacle left node full who,
      modelObstacle_eq obstacle right node full who]
    exact close _ _
  · rw [modelObstacle_eq_zero obstacle left node full who,
      modelObstacle_eq_zero obstacle right node full who]
    simpa using error_nonneg

/-- Backward induction on the prescribed value is `1`-Lipschitz in the
terminal payoff, uniformly in the depth. -/
private theorem abs_prescribedValue_sub_le
    (obstacle left right : G.Hist fuel → Payoff ι) {error : ℝ}
    (error_nonneg : 0 ≤ error)
    (close : ∀ (history : G.Hist fuel) (who : ι),
      |left history who - right history who| ≤ error)
    (depth : ℕ) (who : ι) :
    ∀ node : G.BoundedStoppedHistory fuel,
      |(selectedModel obstacle left).prescribedValue depth who node -
        (selectedModel obstacle right).prescribedValue depth who node| ≤
      error := by
  induction depth with
  | zero =>
      intro node
      exact abs_modelObstacle_sub_le obstacle left right error_nonneg close
        node who
  | succ depth ih =>
      intro node
      by_cases full : G.IsFullHorizonNode node
      · rw [(selectedModel obstacle left).prescribedValue_of_terminal
          (depth + 1) who node full,
          (selectedModel obstacle right).prescribedValue_of_terminal
          (depth + 1) who node full]
        exact abs_modelObstacle_sub_le obstacle left right error_nonneg close
          node who
      · rw [(selectedModel obstacle left).prescribedValue_succ_of_nonterminal
          depth who node full,
          (selectedModel obstacle right).prescribedValue_succ_of_nonterminal
          depth who node full]
        have kernel_eq :
            (selectedModel obstacle right).prescribedKernel node =
              (selectedModel obstacle left).prescribedKernel node := rfl
        rw [kernel_eq]
        exact abs_expect_sub_expect_le _ _ _ ih

/-- The one-step unilateral maximum is `1`-Lipschitz in its continuation. -/
private theorem maxControlledValue_le_add
    (obstacle terminalPayoff : G.Hist fuel → Payoff ι) {error : ℝ}
    (leftValue rightValue : G.BoundedStoppedHistory fuel → ℝ)
    (close : ∀ next, |leftValue next - rightValue next| ≤ error)
    (who : ι) (node : G.BoundedStoppedHistory fuel) :
    (selectedModel obstacle terminalPayoff).maxControlledValue
        who node leftValue ≤
      (selectedModel obstacle terminalPayoff).maxControlledValue
        who node rightValue + error := by
  obtain ⟨pure, pure_eq⟩ :=
    (selectedModel obstacle
        terminalPayoff).exists_controlled_expect_eq_maxControlledValue
      who node leftValue
  rw [← pure_eq]
  have bounded :=
    expect_le_expect_add
      ((selectedModel obstacle terminalPayoff).controlledKernel
        node who pure)
      leftValue rightValue close
  have maximal :=
    (selectedModel obstacle
        terminalPayoff).controlled_expect_le_maxControlledValue
      who node rightValue pure
  linarith

omit [Finite G.State] in
/-- The two selected models share their controlled kernels, hence their
one-step unilateral maxima. -/
private theorem maxControlledValue_model_eq
    (obstacle left right : G.Hist fuel → Payoff ι)
    (value : G.BoundedStoppedHistory fuel → ℝ)
    (who : ι) (node : G.BoundedStoppedHistory fuel) :
    (selectedModel obstacle left).maxControlledValue who node value =
      (selectedModel obstacle right).maxControlledValue who node value :=
  rfl

/-- Backward induction on the worst-unilateral envelope is `1`-Lipschitz in
the terminal payoff, uniformly in the depth. -/
private theorem abs_deviationEnvelope_sub_le
    (obstacle left right : G.Hist fuel → Payoff ι) {error : ℝ}
    (error_nonneg : 0 ≤ error)
    (close : ∀ (history : G.Hist fuel) (who : ι),
      |left history who - right history who| ≤ error)
    (depth : ℕ) (who : ι) :
    ∀ node : G.BoundedStoppedHistory fuel,
      |(selectedModel obstacle left).deviationEnvelope depth who node -
        (selectedModel obstacle right).deviationEnvelope depth who node| ≤
      error := by
  have symmetric : ∀ (history : G.Hist fuel) (player : ι),
      |right history player - left history player| ≤ error := by
    intro history player
    rw [abs_sub_comm]
    exact close history player
  induction depth with
  | zero =>
      intro node
      exact abs_modelObstacle_sub_le obstacle left right error_nonneg close
        node who
  | succ depth ih =>
      intro node
      by_cases full : G.IsFullHorizonNode node
      · rw [(selectedModel obstacle left).deviationEnvelope_of_terminal
          (depth + 1) who node full,
          (selectedModel obstacle right).deviationEnvelope_of_terminal
          (depth + 1) who node full]
        exact abs_modelObstacle_sub_le obstacle left right error_nonneg close
          node who
      · have reverse : ∀ next : G.BoundedStoppedHistory fuel,
            |(selectedModel obstacle right).deviationEnvelope depth who next -
              (selectedModel obstacle left).deviationEnvelope depth who
                next| ≤ error := by
          intro next
          rw [abs_sub_comm]
          exact ih next
        rw [(selectedModel obstacle
            left).deviationEnvelope_succ_of_nonterminal depth who node full,
          (selectedModel obstacle
            right).deviationEnvelope_succ_of_nonterminal depth who node full]
        refine abs_le.mpr ⟨?_, ?_⟩
        · have upper :=
            maxControlledValue_le_add obstacle right
              ((selectedModel obstacle right).deviationEnvelope depth who)
              ((selectedModel obstacle left).deviationEnvelope depth who)
              reverse who node
          have transfer :=
            maxControlledValue_model_eq obstacle right left
              ((selectedModel obstacle left).deviationEnvelope depth who)
              who node
          linarith
        · have upper :=
            maxControlledValue_le_add obstacle left
              ((selectedModel obstacle left).deviationEnvelope depth who)
              ((selectedModel obstacle right).deviationEnvelope depth who)
              ih who node
          have transfer :=
            maxControlledValue_model_eq obstacle left right
              ((selectedModel obstacle right).deviationEnvelope depth who)
              who node
          linarith

/-- Node-level `1`-Lipschitz dependence of the prescribed envelope on the
terminal payoff, at the unchanged backward-Nash profile. -/
theorem abs_prescribedNodePotential_sub_le
    (obstacle left right : G.Hist fuel → Payoff ι) {error : ℝ}
    (error_nonneg : 0 ≤ error)
    (close : ∀ (history : G.Hist fuel) (who : ι),
      |left history who - right history who| ≤ error)
    (who : ι) (node : G.BoundedStoppedHistory fuel) :
    |prescribedNodePotential (profile (G := G) obstacle) left who node -
      prescribedNodePotential (profile (G := G) obstacle) right who node| ≤
    error :=
  abs_prescribedValue_sub_le obstacle left right error_nonneg close
    (G.boundedPublicHistoryRank node) who node

/-- Node-level `1`-Lipschitz dependence of the worst-unilateral envelope on
the terminal payoff, at the unchanged backward-Nash profile. -/
theorem abs_worstUnilateralNodePotential_sub_le
    (obstacle left right : G.Hist fuel → Payoff ι) {error : ℝ}
    (error_nonneg : 0 ≤ error)
    (close : ∀ (history : G.Hist fuel) (who : ι),
      |left history who - right history who| ≤ error)
    (who : ι) (node : G.BoundedStoppedHistory fuel) :
    |worstUnilateralNodePotential (profile (G := G) obstacle) left who node -
      worstUnilateralNodePotential
        (profile (G := G) obstacle) right who node| ≤ error :=
  abs_deviationEnvelope_sub_le obstacle left right error_nonneg close
    (G.boundedPublicHistoryRank node) who node

/-- **Subgame-perfect terminal perturbation robustness.**  At *every* node of
the bounded public-history tree, the worst-unilateral envelope of the
unchanged backward-Nash profile against the perturbed terminal payoff exceeds
its prescribed envelope by at most `2 * error`.  The bound does not depend on
the node, on its depth, or on `fuel`. -/
theorem worstUnilateralNodePotential_le_prescribedNodePotential_add
    (obstacle perturbed : G.Hist fuel → Payoff ι) {error : ℝ}
    (error_nonneg : 0 ≤ error)
    (close : TerminalObstacleClose obstacle perturbed error)
    (who : ι) (node : G.BoundedStoppedHistory fuel) :
    worstUnilateralNodePotential
        (profile (G := G) obstacle) perturbed who node ≤
      prescribedNodePotential
          (profile (G := G) obstacle) perturbed who node +
        2 * error := by
  have worst_close :=
    abs_worstUnilateralNodePotential_sub_le obstacle perturbed obstacle
      error_nonneg (fun history player => close history player) who node
  have prescribed_close :=
    abs_prescribedNodePotential_sub_le obstacle obstacle perturbed
      error_nonneg
      (fun history player => by
        rw [abs_sub_comm]
        exact close history player)
      who node
  have exact_eq :=
    worstUnilateralNodePotential_eq_prescribedNodePotential obstacle who node
  have worst_upper := (abs_le.mp worst_close).2
  have prescribed_upper := (abs_le.mp prescribed_close).2
  linarith

/-- History-potential form of the subgame-perfect `2 * error` bound, at every
public history no longer than the horizon. -/
theorem worstUnilateralHistoryPotential_le_prescribedHistoryPotential_add
    (obstacle perturbed : G.Hist fuel → Payoff ι) {error : ℝ}
    (error_nonneg : 0 ≤ error)
    (close : TerminalObstacleClose obstacle perturbed error)
    (who : ι) {time : ℕ} (history : G.Hist time) (time_le : time ≤ fuel) :
    worstUnilateralHistoryPotential
        (profile (G := G) obstacle) perturbed who time history ≤
      prescribedHistoryPotential
          (profile (G := G) obstacle) perturbed who time history +
        2 * error := by
  rw [worstUnilateralHistoryPotential_of_le
      (profile (G := G) obstacle) perturbed who history time_le,
    prescribedHistoryPotential_of_le
      (profile (G := G) obstacle) perturbed who history time_le]
  exact worstUnilateralNodePotential_le_prescribedNodePotential_add
    obstacle perturbed error_nonneg close who _

end Subgame

end FinitePublicTerminalNashSystem

namespace FiniteRankedTerminalChildCoverage

variable
    {Child : Type}
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)]
    [Fintype Child]
    {entry : Child → G.State} {childTarget : Child → Payoff ι}
    {childError : ℝ} {fuel : ℕ}
    (coverage : G.FiniteRankedTerminalChildCoverage entry fuel)
    (family :
      G.FiniteChildAdaptivePotentialFamily entry childTarget childError)

/-- Deviation safety of the backward-Nash selection against *any* terminal
obstacle uniformly close to the fixed child-target obstacle.

This is the reusable core behind the three `ObstacleCloseness` corollaries
below: its hypothesis is exactly the shape of one `ObstacleCloseness`
field. -/
theorem selection_deviation_le_of_close
    {perturbed : G.Hist fuel → Payoff ι}
    (close : ∀ (history : G.Hist fuel) (who : ι),
      |perturbed history who -
        coverage.targetObstacle childTarget history who| ≤ childError)
    (who : ι) (deviation : G.BehaviorStrategy who) :
    expect
        (G.histDist
          (Function.update (coverage.selection childTarget) who deviation)
          coverage.initial fuel)
        (fun history => perturbed history who) ≤
      expect
        (G.histDist (coverage.selection childTarget) coverage.initial fuel)
        (fun history => perturbed history who) +
        2 * childError :=
  FinitePublicTerminalNashSystem.expect_perturbed_deviation_le_expect_perturbed
    (coverage.targetObstacle childTarget) perturbed close
    coverage.initial who deviation

/-- Under `ObstacleCloseness`, the unchanged backward-Nash selection is a
`2 * childError`-equilibrium for the *actual* delayed lower obstacle. -/
theorem selection_lowerObstacle_deviation_le
    (close : coverage.ObstacleCloseness family)
    (who : ι) (deviation : G.BehaviorStrategy who) :
    expect
        (G.histDist
          (Function.update (coverage.selection childTarget) who deviation)
          coverage.initial fuel)
        (fun history =>
          (coverage.delayedData family).lowerObstacle history who) ≤
      expect
        (G.histDist (coverage.selection childTarget) coverage.initial fuel)
        (fun history =>
          (coverage.delayedData family).lowerObstacle history who) +
        2 * childError :=
  coverage.selection_deviation_le_of_close
    (fun history player => close.lower history player) who deviation

/-- Under `ObstacleCloseness`, the unchanged backward-Nash selection is a
`2 * childError`-equilibrium for the actual delayed upper obstacle. -/
theorem selection_upperObstacle_deviation_le
    (close : coverage.ObstacleCloseness family)
    (who : ι) (deviation : G.BehaviorStrategy who) :
    expect
        (G.histDist
          (Function.update (coverage.selection childTarget) who deviation)
          coverage.initial fuel)
        (fun history =>
          (coverage.delayedData family).upperObstacle history who) ≤
      expect
        (G.histDist (coverage.selection childTarget) coverage.initial fuel)
        (fun history =>
          (coverage.delayedData family).upperObstacle history who) +
        2 * childError :=
  coverage.selection_deviation_le_of_close
    (fun history player => close.upper history player) who deviation

/-- Under `ObstacleCloseness`, the unchanged backward-Nash selection is a
`2 * childError`-equilibrium for the actual delayed deviation obstacle. -/
theorem selection_deviationObstacle_deviation_le
    (close : coverage.ObstacleCloseness family)
    (who : ι) (deviation : G.BehaviorStrategy who) :
    expect
        (G.histDist
          (Function.update (coverage.selection childTarget) who deviation)
          coverage.initial fuel)
        (fun history =>
          (coverage.delayedData family).deviationObstacle history who) ≤
      expect
        (G.histDist (coverage.selection childTarget) coverage.initial fuel)
        (fun history =>
          (coverage.delayedData family).deviationObstacle history who) +
        2 * childError :=
  coverage.selection_deviation_le_of_close
    (fun history player => close.deviation history player) who deviation

end FiniteRankedTerminalChildCoverage

namespace TerminalPerturbationSharpness

open FinitePublicTerminalNashSystem

/-- A one-player, one-state game with a public Boolean action. -/
def game : StochasticGame Unit where
  State := Unit
  Act := fun _ => Bool
  stagePayoff := fun _ _ _ => 0
  transition := fun _ _ => PMF.pure ()
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := by norm_num

instance : Finite game.State := inferInstanceAs (Finite Unit)

instance (who : Unit) : Fintype (game.Act who) := inferInstanceAs (Fintype Bool)

instance (who : Unit) : Nonempty (game.Act who) :=
  inferInstanceAs (Nonempty Bool)

/-- The single public action recorded by a one-stage history. -/
def lastMove (history : game.Hist 1) : Bool := (history.1 0).2 ()

/-- The complete one-stage history in which the public action is `move`. -/
def historyOf (move : Bool) : game.Hist 1 :=
  (Fin.snoc Fin.elim0 ((), fun _ => move), ())

@[simp] theorem lastMove_historyOf (move : Bool) :
    lastMove (historyOf move) = move := rfl

/-- Reference terminal payoff: the public action `true` is strictly better by
the margin `slack`, so the backward-Nash selection is forced. -/
def baseObstacle (slack : ℝ) : game.Hist 1 → Payoff Unit :=
  fun history _ => cond (lastMove history) 0 (-slack)

/-- Perturbed terminal payoff: `true` is pushed down and `false` is pushed up,
each by exactly `error`. -/
def perturbedObstacle (error slack : ℝ) : game.Hist 1 → Payoff Unit :=
  fun history _ => cond (lastMove history) (-error) (error - slack)

theorem baseObstacle_apply (slack : ℝ) (history : game.Hist 1) (who : Unit) :
    baseObstacle slack history who = cond (lastMove history) 0 (-slack) := rfl

theorem perturbedObstacle_apply
    (error slack : ℝ) (history : game.Hist 1) (who : Unit) :
    perturbedObstacle error slack history who =
      cond (lastMove history) (-error) (error - slack) := rfl

/-- The two terminal payoff systems are at uniform distance exactly
`error`. -/
theorem terminalObstacleClose
    (error slack : ℝ) (error_nonneg : 0 ≤ error) :
    TerminalObstacleClose (G := game)
      (baseObstacle slack) (perturbedObstacle error slack) error := by
  intro history who
  cases move : lastMove history with
  | false =>
      have value :
          perturbedObstacle error slack history who -
            baseObstacle slack history who = error := by
        rw [perturbedObstacle_apply, baseObstacle_apply, move]
        change error - slack - -slack = error
        ring
      rw [value, abs_of_nonneg error_nonneg]
  | true =>
      have value :
          perturbedObstacle error slack history who -
            baseObstacle slack history who = -error := by
        rw [perturbedObstacle_apply, baseObstacle_apply, move]
        change -error - 0 = -error
        ring
      rw [value, abs_neg, abs_of_nonneg error_nonneg]

/-- The backward-Nash profile selected for the reference obstacle. -/
def selectedProfile (slack : ℝ) : game.BehaviorProfile :=
  profile (G := game) (baseObstacle slack)

/-- The root node of the depth-one bounded public-history tree. -/
def rootNode : game.BoundedStoppedHistory 1 :=
  game.boundedPublicHistoryNode (game.emptyHist ()) (Nat.zero_le 1)

/-- The mixed action selected by backward induction at the root. -/
def rootMixed (slack : ℝ) : PMF Bool :=
  nodeMixed (obstacle := baseObstacle slack) rootNode ()

private theorem not_full_rootNode : ¬game.IsFullHorizonNode rootNode := by
  intro full
  have absurdity : (0 : ℕ) = 1 := full
  omega

private theorem strict_rootNode : rootNode.1.val < 1 := Nat.zero_lt_one

/-- Under a single player the product of mixed actions is the single mixed
action itself. -/
private theorem expect_pmfPi_unit
    {A : Type} [Finite A] (mixed : Unit → PMF A) (value : (Unit → A) → ℝ) :
    expect (pmfPi (A := fun _ : Unit => A) mixed) value =
      expect (mixed ()) (fun move => value (fun _ => move)) := by
  have collapse :
      expect (pmfPi (A := fun _ : Unit => A) mixed) value =
        expect
          ((pmfPi (A := fun _ : Unit => A) mixed).bind
            (fun s => PMF.pure (s ())))
          (fun move => value (fun _ => move)) := by
    rw [expect_bind]
    refine congrArg (expect (pmfPi (A := fun _ : Unit => A) mixed))
      (funext fun s => ?_)
    rw [expect_pure]
  rw [collapse, pmfPi_bind_eval mixed () (fun move => PMF.pure move),
    PMF.bind_pure]

/-- The terminal backward value after one public action. -/
private theorem nodeValue_successor (slack : ℝ) (action : game.JointAct)
    (next : game.State) :
    nodeValue (obstacle := baseObstacle slack)
        (game.boundedPublicHistorySuccessor rootNode strict_rootNode action
          next) () =
      cond (action ()) 0 (-slack) := by
  have full :
      game.IsFullHorizonNode
        (game.boundedPublicHistorySuccessor rootNode strict_rootNode action
          next) := rfl
  rw [nodeValue_of_full (baseObstacle slack) _ full]
  rfl

/-- One stage of the root game evaluated against an arbitrary joint mixed
action. -/
private theorem expect_rootStage (slack : ℝ)
    (mixed : ∀ who : Unit, PMF (game.Act who)) :
    (expect (pmfPi mixed) fun action =>
      expect (game.transition rootNode.2.2 action) fun next =>
        nodeValue (obstacle := baseObstacle slack)
          (game.boundedPublicHistorySuccessor rootNode strict_rootNode action
            next) ()) =
      expect (mixed ()) (fun move => cond move 0 (-slack)) := by
  have integrand :
      (fun action : game.JointAct =>
          expect (game.transition rootNode.2.2 action) fun next =>
            nodeValue (obstacle := baseObstacle slack)
              (game.boundedPublicHistorySuccessor rootNode strict_rootNode
                action next) ()) =
        fun action => cond (action ()) 0 (-slack) := by
    funext action
    have kernel :
        game.transition rootNode.2.2 action = PMF.pure rootNode.2.2 := rfl
    rw [kernel, expect_pure]
    exact nodeValue_successor slack action rootNode.2.2
  rw [integrand]
  exact expect_pmfPi_unit mixed _

/-- The backward value at the root is the selected mixed action's expected
terminal payoff. -/
private theorem nodeValue_root (slack : ℝ) :
    nodeValue (obstacle := baseObstacle slack) rootNode () =
      expect (rootMixed slack) (fun move => cond move 0 (-slack)) := by
  refine Eq.trans
    (nodeValue_of_not_full (baseObstacle slack) rootNode not_full_rootNode ())
    ?_
  change
    (expect (pmfPi (nodeMixed (obstacle := baseObstacle slack) rootNode))
      fun action =>
        expect (game.transition rootNode.2.2 action) fun next =>
          nodeValue (obstacle := baseObstacle slack)
            (game.boundedPublicHistorySuccessor rootNode strict_rootNode
              action next) ()) =
      expect (rootMixed slack) (fun move => cond move 0 (-slack))
  exact expect_rootStage slack _

/-- No pure public action beats the backward value at the root. -/
private theorem cond_le_nodeValue_root (slack : ℝ) (move : Bool) :
    cond move 0 (-slack) ≤
      nodeValue (obstacle := baseObstacle slack) rootNode () := by
  have nash :=
    unilateralContinuation_le_nodeValue
      (baseObstacle slack) rootNode not_full_rootNode () (PMF.pure move)
  have rewritten :
      (expect
        (pmfPi
          (Function.update (nodeMixed (obstacle := baseObstacle slack)
            rootNode) () (PMF.pure move))) fun action =>
        expect (game.transition rootNode.2.2 action) fun next =>
          nodeValue (obstacle := baseObstacle slack)
            (game.boundedPublicHistorySuccessor rootNode strict_rootNode
              action next) ()) =
        cond move 0 (-slack) := by
    refine Eq.trans (expect_rootStage slack _) ?_
    exact expect_pure _ _
  calc
    cond move 0 (-slack) = _ := rewritten.symm
    _ ≤ nodeValue (obstacle := baseObstacle slack) rootNode () := nash

/-- With a strictly positive margin the selected mixed action never plays
`false`. -/
private theorem rootMixed_false (slack : ℝ) (slack_pos : 0 < slack) :
    rootMixed slack false = 0 := by
  by_contra nonzero
  have upper : ∀ move : Bool, cond move 0 (-slack) ≤ (0 : ℝ) := by
    intro move
    cases move with
    | false =>
        change (-slack : ℝ) ≤ 0
        linarith
    | true =>
        change (0 : ℝ) ≤ 0
        linarith
  have strictly :
      expect (rootMixed slack) (fun move => cond move 0 (-slack)) <
        expect (rootMixed slack) (fun _ => (0 : ℝ)) := by
    refine expect_lt_of_le_of_exists_lt _ _ _ upper ⟨false, nonzero, ?_⟩
    change (-slack : ℝ) < 0
    linarith
  rw [expect_const] at strictly
  have lower : (0 : ℝ) ≤ nodeValue (obstacle := baseObstacle slack) rootNode ()
    := cond_le_nodeValue_root slack true
  rw [nodeValue_root slack] at lower
  linarith

/-- Consequently the selected root law is concentrated on `true`. -/
private theorem expect_rootMixed (slack : ℝ) (slack_pos : 0 < slack)
    (value : Bool → ℝ) :
    expect (rootMixed slack) value = value true := by
  have support : ∀ move ∈ (rootMixed slack).support, value move = value true := by
    intro move member
    cases move with
    | false =>
        have nonzero : rootMixed slack false ≠ 0 := by
          simpa [PMF.mem_support_iff] using member
        exact absurd (rootMixed_false slack slack_pos) nonzero
    | true => rfl
  rw [expect_congr_on_support (rootMixed slack) value
    (fun _ => value true) support, expect_const]

/-- One-stage terminal expectation under an arbitrary behavior profile. -/
private theorem expect_histDist
    (behavior : game.BehaviorProfile)
    (mixed : ∀ who : Unit, PMF (game.Act who))
    (behavior_eq : ∀ who, behavior who 0 (game.emptyHist ()) = mixed who)
    (value : game.Hist 1 → ℝ) :
    expect (game.histDist behavior () 1) value =
      expect (mixed ()) (fun move => value (historyOf move)) := by
  rw [game.histDist_succ behavior () 0, game.histDist_zero]
  simp only [expect_bind, expect_pure]
  have actions :
      game.stageActionDist behavior (game.emptyHist ()) = pmfPi mixed := by
    unfold stageActionDist
    congr 1
    funext who
    exact behavior_eq who
  rw [actions]
  have integrand :
      (fun action : game.JointAct =>
          expect (game.transition (game.emptyHist ()).2 action) fun next =>
            value
              (Fin.snoc (game.emptyHist ()).1
                ((game.emptyHist ()).2, action), next)) =
        fun action => value (historyOf (action ())) := by
    funext action
    have kernel :
        game.transition (game.emptyHist ()).2 action =
          PMF.pure (game.emptyHist ()).2 := rfl
    rw [kernel, expect_pure]
    rfl
  rw [integrand]
  exact expect_pmfPi_unit mixed _

/-- **Sharpness of the constant `2`.**  For every accuracy `error ≥ 0` and
every margin `0 < slack`, this depth-one one-player game carries two terminal
payoff systems at uniform distance `error` for which a single behavior
deviation from the *unchanged* backward-Nash profile gains exactly
`2 * error - slack` against the perturbed system.  Letting `slack` tend to
zero shows that no constant smaller than `2` is admissible, and in particular
that `error` alone never suffices. -/
theorem exists_gain_eq
    (error slack : ℝ) (error_nonneg : 0 ≤ error) (slack_pos : 0 < slack) :
    TerminalObstacleClose (G := game)
        (baseObstacle slack) (perturbedObstacle error slack) error ∧
      ∃ deviation : game.BehaviorStrategy (),
        expect
            (game.histDist
              (Function.update (selectedProfile slack) () deviation) () 1)
            (fun history => perturbedObstacle error slack history ()) =
          expect (game.histDist (selectedProfile slack) () 1)
              (fun history => perturbedObstacle error slack history ()) +
            (2 * error - slack) := by
  refine ⟨terminalObstacleClose error slack error_nonneg,
    fun _ _ => PMF.pure false, ?_⟩
  have selected_eq : ∀ who : Unit,
      selectedProfile slack who 0 (game.emptyHist ()) = rootMixed slack := by
    intro who
    obtain rfl : who = () := Subsingleton.elim who ()
    exact profile_of_lt (baseObstacle slack) () (game.emptyHist ())
      Nat.zero_lt_one
  have deviated_eq : ∀ who : Unit,
      Function.update (selectedProfile slack) ()
          (fun _ _ => PMF.pure false) who 0 (game.emptyHist ()) =
        PMF.pure false := by
    intro who
    obtain rfl : who = () := Subsingleton.elim who ()
    rfl
  have prescribed :
      expect (game.histDist (selectedProfile slack) () 1)
          (fun history => perturbedObstacle error slack history ()) =
        -error := by
    refine Eq.trans
      (expect_histDist (selectedProfile slack) (fun _ => rootMixed slack)
        selected_eq _) ?_
    exact Eq.trans (expect_rootMixed slack slack_pos _) rfl
  have deviated :
      expect
          (game.histDist
            (Function.update (selectedProfile slack) ()
              (fun _ _ => PMF.pure false)) () 1)
          (fun history => perturbedObstacle error slack history ()) =
        error - slack := by
    refine Eq.trans
      (expect_histDist _ (fun _ => PMF.pure false) deviated_eq _) ?_
    exact Eq.trans (expect_pure _ _) rfl
  rw [prescribed, deviated]
  ring

/-- Cross-check that the sharp example really is an instance of the general
theorem: the same profile, the same two obstacles, and the general `2 * error`
ceiling.  Together with `exists_gain_eq` this pins the optimal constant
between `2 - slack / error` and `2` for every `slack > 0`. -/
theorem gain_le_two_error
    (error slack : ℝ) (error_nonneg : 0 ≤ error)
    (deviation : game.BehaviorStrategy ()) :
    expect
        (game.histDist
          (Function.update (selectedProfile slack) () deviation) () 1)
        (fun history => perturbedObstacle error slack history ()) ≤
      expect (game.histDist (selectedProfile slack) () 1)
          (fun history => perturbedObstacle error slack history ()) +
        2 * error :=
  expect_perturbed_deviation_le_expect_perturbed
    (baseObstacle slack) (perturbedObstacle error slack)
    (terminalObstacleClose error slack error_nonneg) () () deviation

/-- **`error` alone never suffices.**  Choosing the margin below the accuracy
makes the deviation gain strictly larger than `error`. -/
theorem exists_gain_gt_error (error : ℝ) (error_pos : 0 < error) :
    ∃ slack : ℝ,
      TerminalObstacleClose (G := game)
          (baseObstacle slack) (perturbedObstacle error slack) error ∧
        ∃ deviation : game.BehaviorStrategy (),
          expect
              (game.histDist
                (Function.update (selectedProfile slack) () deviation) () 1)
              (fun history => perturbedObstacle error slack history ()) >
            expect (game.histDist (selectedProfile slack) () 1)
                (fun history => perturbedObstacle error slack history ()) +
              error := by
  obtain ⟨close, deviation, gain⟩ :=
    exists_gain_eq error (error / 2) (le_of_lt error_pos) (by linarith)
  refine ⟨error / 2, close, deviation, ?_⟩
  rw [gain]
  linarith

end TerminalPerturbationSharpness

end StochasticGame
end GameTheory
