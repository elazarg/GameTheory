/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Existence.NashExistenceMixed
import UniformEquilibrium.Certificates.Public.FullHorizonPublicHistoryOptimalDeviation

/-!
# Finite public terminal Nash systems

For an arbitrary payoff vector attached to complete public histories of one
fixed finite horizon, backward induction selects a mixed Nash equilibrium in
the continuation game at every shorter public history.  The resulting
behavior profile is subgame-perfect for this terminal-payoff problem.

The construction supplies:

* a history potential equal to the terminal obstacle at the horizon;
* pointwise harmonicity under the selected profile before the horizon;
* pointwise superharmonicity under every unilateral mixed replacement;
* a finite-horizon terminal expectation bound for every history-dependent
  unilateral behavior deviation.

Consequently the prescribed and worst-unilateral full-history Bellman
envelopes coincide.  This is a finite terminal-payoff result only.  Its root
value is the endogenous backward-induction payoff of the supplied obstacle;
the theorem does not identify that value with an arbitrary external parent
target.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.PMFProduct Math.Probability
open Math.ProbabilityMassFunction

variable {ι : Type} {G : StochasticGame ι}

namespace FinitePublicTerminalNashSystem

open FiniteFullHistoryControlledStoppingModel

variable
    [Fintype ι] [DecidableEq ι]
    [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)]
    {fuel : ℕ}
    (obstacle : G.Hist fuel → Payoff ι)

/-- Value and local mixed action profile selected at one bounded public
history node. -/
private abbrev NodeData :=
  Payoff ι × (∀ who, PMF (G.Act who))

private def arbitraryMixedProfile : ∀ who, PMF (G.Act who) :=
  fun who => PMF.pure (Classical.choice (inferInstance : Nonempty (G.Act who)))

/-- A fixed mixed Nash selection for a finite one-shot payoff function. -/
private def mixedNashProfile
    (payoff : G.JointAct → Payoff ι) :
    ∀ who, PMF (G.Act who) := by
  let stageGame : KernelGame ι :=
    KernelGame.ofPureEU G.Act payoff
  haveI : ∀ who, Finite (stageGame.Strategy who) :=
    fun who => inferInstanceAs (Finite (G.Act who))
  haveI : ∀ who, Nonempty (stageGame.Strategy who) :=
    fun who => inferInstanceAs (Nonempty (G.Act who))
  haveI : Finite stageGame.Outcome :=
    inferInstanceAs (Finite G.JointAct)
  exact Classical.choose stageGame.mixed_nash_exists

/-- The selected profile is Nash in its defining one-shot game. -/
private theorem mixedNashProfile_isNash
    (payoff : G.JointAct → Payoff ι) :
    (KernelGame.ofPureEU G.Act payoff).mixedExtension.IsNash
      (mixedNashProfile (G := G) payoff) := by
  let stageGame : KernelGame ι :=
    KernelGame.ofPureEU G.Act payoff
  haveI : ∀ who, Finite (stageGame.Strategy who) :=
    fun who => inferInstanceAs (Finite (G.Act who))
  haveI : ∀ who, Nonempty (stageGame.Strategy who) :=
    fun who => inferInstanceAs (Nonempty (G.Act who))
  haveI : Finite stageGame.Outcome :=
    inferInstanceAs (Finite G.JointAct)
  exact Classical.choose_spec stageGame.mixed_nash_exists

/-- Backward-induction data on the finite public-history tree.

At a full-horizon node the value is the obstacle.  At an earlier node the
continuation payoffs define a finite normal-form game, a mixed Nash profile
is selected, and the node value is its expected continuation payoff. -/
def backwardData (node : G.BoundedStoppedHistory fuel) : NodeData (G := G) := by
  classical
  by_cases full : G.IsFullHorizonNode node
  · exact
      (obstacle (G.fullHistoryOfBoundedNode node full),
        arbitraryMixedProfile (G := G))
  · have strict : node.1.val < fuel := by
      unfold IsFullHorizonNode at full
      have length_le : node.1.val ≤ fuel :=
        Nat.lt_succ_iff.mp node.1.isLt
      omega
    let continuationPayoff :
        G.JointAct → Payoff ι :=
      fun action who =>
        expect (G.transition node.2.2 action) fun next =>
          (backwardData
            (G.boundedPublicHistorySuccessor
              node strict action next)).1 who
    let mixed : ∀ who, PMF (G.Act who) :=
      mixedNashProfile (G := G) continuationPayoff
    exact
      (fun who =>
        expect (pmfPi mixed) fun action =>
          continuationPayoff action who,
        mixed)
termination_by G.boundedPublicHistoryRank node
decreasing_by
  unfold boundedPublicHistoryRank
  simp only [boundedPublicHistorySuccessor_length]
  omega

/-- Backward-induction value at one bounded node. -/
def nodeValue (node : G.BoundedStoppedHistory fuel) : Payoff ι :=
  (backwardData (obstacle := obstacle) node).1

/-- Local mixed Nash action profile at one bounded node. -/
def nodeMixed (node : G.BoundedStoppedHistory fuel) :
    ∀ who, PMF (G.Act who) :=
  (backwardData (obstacle := obstacle) node).2

/-- Behavior profile assembled from the local backward-induction Nash
profiles.  Behavior at and after the terminal horizon is irrelevant and is
completed by a fixed pure profile. -/
def profile : G.BehaviorProfile :=
  fun who time history =>
    if time_lt : time < fuel then
      nodeMixed (obstacle := obstacle)
        (G.boundedPublicHistoryNode history
          (Nat.le_of_lt time_lt)) who
    else
      arbitraryMixedProfile (G := G) who

/-- History potential induced by the backward-induction node values. -/
def potential : ι → G.HistoryPotential :=
  fun who time history =>
    if time_le : time ≤ fuel then
      nodeValue (obstacle := obstacle)
        (G.boundedPublicHistoryNode history time_le) who
    else
      0

/-- Unfolding backward induction at a terminal node. -/
theorem backwardData_of_full
    (node : G.BoundedStoppedHistory fuel)
    (full : G.IsFullHorizonNode node) :
    backwardData (obstacle := obstacle) node =
      (obstacle (G.fullHistoryOfBoundedNode node full),
        arbitraryMixedProfile (G := G)) := by
  rw [backwardData]
  simp only [full, ↓reduceDIte]

/-- Unfolding backward induction at a nonterminal node. -/
theorem backwardData_of_not_full
    (node : G.BoundedStoppedHistory fuel)
    (not_full : ¬G.IsFullHorizonNode node) :
    backwardData (obstacle := obstacle) node =
      let strict : node.1.val < fuel := by
        unfold IsFullHorizonNode at not_full
        have length_le : node.1.val ≤ fuel :=
          Nat.lt_succ_iff.mp node.1.isLt
        omega
      let continuationPayoff : G.JointAct → Payoff ι :=
        fun action who =>
          expect (G.transition node.2.2 action) fun next =>
            nodeValue (obstacle := obstacle)
              (G.boundedPublicHistorySuccessor
                node strict action next) who
      let mixed : ∀ who, PMF (G.Act who) :=
        mixedNashProfile (G := G) continuationPayoff
      (fun who =>
        expect (pmfPi mixed) fun action =>
          continuationPayoff action who,
        mixed) := by
  rw [backwardData]
  simp only [not_full, ↓reduceDIte]
  rfl

/-- The backward value at a terminal public history is exactly the supplied
terminal obstacle. -/
theorem nodeValue_of_full
    (node : G.BoundedStoppedHistory fuel)
    (full : G.IsFullHorizonNode node) :
    nodeValue (obstacle := obstacle) node =
      obstacle (G.fullHistoryOfBoundedNode node full) := by
  unfold nodeValue
  rw [backwardData_of_full obstacle node full]

/-- Bellman equality for the backward value at a nonterminal node. -/
theorem nodeValue_of_not_full
    (node : G.BoundedStoppedHistory fuel)
    (not_full : ¬G.IsFullHorizonNode node) (who : ι) :
    nodeValue (obstacle := obstacle) node who =
      let strict : node.1.val < fuel := by
        unfold IsFullHorizonNode at not_full
        have length_le : node.1.val ≤ fuel :=
          Nat.lt_succ_iff.mp node.1.isLt
        omega
      expect (pmfPi (nodeMixed (obstacle := obstacle) node)) fun action =>
        expect (G.transition node.2.2 action) fun next =>
          nodeValue (obstacle := obstacle)
            (G.boundedPublicHistorySuccessor
              node strict action next) who := by
  unfold nodeValue nodeMixed
  rw [backwardData_of_not_full obstacle node not_full]
  rfl

/-- The nonterminal local action profile is the selected mixed Nash profile
of the continuation game. -/
theorem nodeMixed_of_not_full
    (node : G.BoundedStoppedHistory fuel)
    (not_full : ¬G.IsFullHorizonNode node) :
    nodeMixed (obstacle := obstacle) node =
      let strict : node.1.val < fuel := by
        unfold IsFullHorizonNode at not_full
        have length_le : node.1.val ≤ fuel :=
          Nat.lt_succ_iff.mp node.1.isLt
        omega
      let continuationPayoff : G.JointAct → Payoff ι :=
        fun action who =>
          expect (G.transition node.2.2 action) fun next =>
            nodeValue (obstacle := obstacle)
              (G.boundedPublicHistorySuccessor
                node strict action next) who
      mixedNashProfile (G := G) continuationPayoff := by
  unfold nodeMixed
  rw [backwardData_of_not_full obstacle node not_full]

/-- At a nonterminal node no unilateral mixed action replacement improves
the expected backward continuation value. -/
theorem unilateralContinuation_le_nodeValue
    (node : G.BoundedStoppedHistory fuel)
    (not_full : ¬G.IsFullHorizonNode node)
    (who : ι) (deviation : PMF (G.Act who)) :
    let strict : node.1.val < fuel := by
      unfold IsFullHorizonNode at not_full
      have length_le : node.1.val ≤ fuel :=
        Nat.lt_succ_iff.mp node.1.isLt
      omega
    (expect
        (pmfPi
          (Function.update
            (nodeMixed (obstacle := obstacle) node)
            who deviation)) fun action =>
      expect (G.transition node.2.2 action) fun next =>
        nodeValue (obstacle := obstacle)
          (G.boundedPublicHistorySuccessor
            node strict action next) who) ≤
      nodeValue (obstacle := obstacle) node who := by
  classical
  let strict : node.1.val < fuel := by
    unfold IsFullHorizonNode at not_full
    have length_le : node.1.val ≤ fuel :=
      Nat.lt_succ_iff.mp node.1.isLt
    omega
  let continuationPayoff : G.JointAct → Payoff ι :=
    fun action player =>
      expect (G.transition node.2.2 action) fun next =>
        nodeValue (obstacle := obstacle)
          (G.boundedPublicHistorySuccessor
            node strict action next) player
  have nash :=
    mixedNashProfile_isNash
      (G := G) continuationPayoff
  have best_response :=
    nash who deviation
  haveI :
      Finite
        (KernelGame.ofPureEU G.Act continuationPayoff).Outcome :=
    inferInstanceAs (Finite G.JointAct)
  rw [
    KernelGame.mixedExtension_eu,
    KernelGame.mixedExtension_eu
  ] at best_response
  simp only [KernelGame.eu_ofPureEU] at best_response
  rw [nodeValue_of_not_full obstacle node not_full who]
  rw [nodeMixed_of_not_full obstacle node not_full]
  exact best_response

@[simp] theorem profile_of_lt
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_lt : time < fuel) :
    profile (G := G) obstacle who time history =
      nodeMixed (obstacle := obstacle)
        (G.boundedPublicHistoryNode history
          (Nat.le_of_lt time_lt)) who := by
  simp [profile, time_lt]

@[simp] theorem potential_of_le
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_le : time ≤ fuel) :
    potential (G := G) obstacle who time history =
      nodeValue (obstacle := obstacle)
        (G.boundedPublicHistoryNode history time_le) who := by
  simp [potential, time_le]

/-- The public-history potential equals the arbitrary supplied obstacle at
the terminal horizon. -/
@[simp] theorem potential_at_horizon
    (who : ι) (history : G.Hist fuel) :
    potential (G := G) obstacle who fuel history =
      obstacle history who := by
  rw [potential_of_le obstacle who history (le_refl fuel)]
  rw [nodeValue_of_full obstacle
    (G.boundedPublicHistoryNode history (le_refl fuel)) rfl]
  rfl

/-- Pointwise Bellman equality under the selected backward-induction
profile. -/
theorem potential_harmonic
    (who : ι) {time : ℕ} (history : G.Hist time)
    (time_lt : time < fuel) :
    G.historyContinuationEU
        (profile (G := G) obstacle)
        (potential (G := G) obstacle who) history =
      potential (G := G) obstacle who time history := by
  let node :=
    G.boundedPublicHistoryNode history (Nat.le_of_lt time_lt)
  have not_full : ¬G.IsFullHorizonNode node := by
    simpa [node, IsFullHorizonNode] using ne_of_lt time_lt
  rw [potential_of_le obstacle who history
    (Nat.le_of_lt time_lt)]
  rw [nodeValue_of_not_full obstacle node not_full who]
  unfold historyContinuationEU stageActionDist
  simp only [profile_of_lt obstacle _ history time_lt]
  apply congrArg
  funext action
  apply congrArg
  funext next
  rw [potential_of_le obstacle who
    ((Fin.snoc history.1 (history.2, action), next) :
      G.Hist (time + 1))
    (Nat.succ_le_of_lt time_lt)]
  rfl

/-- Pointwise superharmonicity under an arbitrary current mixed replacement
of one player's action. -/
theorem potential_mixed_superharmonic
    (who : ι) (mixed : PMF (G.Act who))
    {time : ℕ} (history : G.Hist time)
    (time_lt : time < fuel) :
    (expect
        (pmfPi
          (Function.update
            (fun player =>
              profile (G := G) obstacle player time history)
            who mixed)) fun action =>
      expect (G.transition history.2 action) fun next =>
        potential (G := G) obstacle who (time + 1)
          (Fin.snoc history.1 (history.2, action), next)) ≤
      potential (G := G) obstacle who time history := by
  let node :=
    G.boundedPublicHistoryNode history (Nat.le_of_lt time_lt)
  have not_full : ¬G.IsFullHorizonNode node := by
    simpa [node, IsFullHorizonNode] using ne_of_lt time_lt
  rw [potential_of_le obstacle who history
    (Nat.le_of_lt time_lt)]
  apply le_trans _ <|
    unilateralContinuation_le_nodeValue
      obstacle node not_full who mixed
  apply le_of_eq
  simp only [profile_of_lt obstacle _ history time_lt]
  apply congrArg
  funext action
  apply congrArg
  funext next
  rw [potential_of_le obstacle who
    ((Fin.snoc history.1 (history.2, action), next) :
      G.Hist (time + 1))
    (Nat.succ_le_of_lt time_lt)]
  rfl

/-- Pointwise superharmonicity under every history-dependent unilateral
behavior deviation. -/
theorem potential_deviation_superharmonic
    (who : ι) (deviation : G.BehaviorStrategy who)
    {time : ℕ} (history : G.Hist time)
    (time_lt : time < fuel) :
    G.historyContinuationEU
        (Function.update
          (profile (G := G) obstacle) who deviation)
        (potential (G := G) obstacle who) history ≤
      potential (G := G) obstacle who time history := by
  have action_dist :
      G.stageActionDist
          (Function.update
            (profile (G := G) obstacle) who deviation)
          history =
        pmfPi
          (Function.update
            (fun player =>
              profile (G := G) obstacle player time history)
            who (deviation time history)) := by
    unfold stageActionDist
    congr 1
    funext player
    by_cases same : player = who
    · subst same
      simp
    · simp [Function.update_of_ne same]
  unfold historyContinuationEU
  rw [action_dist]
  exact potential_mixed_superharmonic
    obstacle who (deviation time history) history time_lt

variable [Finite G.State]

/-- The expected backward-induction potential is constant under the
prescribed profile through the finite horizon. -/
theorem expectedPotential_eq_root
    (initial : G.State) (who : ι) :
    ∀ time, time ≤ fuel →
      G.expectedHistoryValue
          (profile (G := G) obstacle) initial
          (potential (G := G) obstacle who) time =
        potential (G := G) obstacle who 0
          (G.emptyHist initial) := by
  intro time time_le
  induction time with
  | zero =>
      simp [expectedHistoryValue]
  | succ time ih =>
      have time_lt : time < fuel := by omega
      rw [G.expectedHistoryValue_succ]
      calc
        expect
            (G.histDist (profile (G := G) obstacle)
              initial time)
            (fun history =>
              G.historyContinuationEU
                (profile (G := G) obstacle)
                (potential (G := G) obstacle who)
                history) =
          expect
            (G.histDist (profile (G := G) obstacle)
              initial time)
            (potential (G := G) obstacle who time) := by
                apply congrArg
                funext history
                exact potential_harmonic
                  obstacle who history time_lt
        _ =
          potential (G := G) obstacle who 0
            (G.emptyHist initial) :=
              ih (Nat.le_of_lt time_lt)

/-- Under every unilateral behavior deviation, the expected terminal
potential is bounded by its prescribed root value. -/
theorem expectedPotential_deviation_le_root
    (initial : G.State) (who : ι)
    (deviation : G.BehaviorStrategy who) :
    ∀ time, time ≤ fuel →
      G.expectedHistoryValue
          (Function.update
            (profile (G := G) obstacle) who deviation)
          initial
          (potential (G := G) obstacle who) time ≤
        potential (G := G) obstacle who 0
          (G.emptyHist initial) := by
  intro time time_le
  induction time with
  | zero =>
      simp [expectedHistoryValue]
  | succ time ih =>
      have time_lt : time < fuel := by omega
      rw [G.expectedHistoryValue_succ]
      calc
        expect
            (G.histDist
              (Function.update
                (profile (G := G) obstacle) who deviation)
              initial time)
            (fun history =>
              G.historyContinuationEU
                (Function.update
                  (profile (G := G) obstacle) who deviation)
                (potential (G := G) obstacle who)
                history) ≤
          expect
            (G.histDist
              (Function.update
                (profile (G := G) obstacle) who deviation)
              initial time)
            (potential (G := G) obstacle who time) := by
                apply expect_mono
                intro history
                exact potential_deviation_superharmonic
                  obstacle who deviation history time_lt
        _ ≤
          potential (G := G) obstacle who 0
            (G.emptyHist initial) :=
              ih (Nat.le_of_lt time_lt)

/-- Prescribed terminal obstacle expectation equals the endogenous
backward-induction root payoff. -/
theorem expect_obstacle_profile_eq_root
    (initial : G.State) (who : ι) :
    expect
        (G.histDist (profile (G := G) obstacle)
          initial fuel)
        (fun history => obstacle history who) =
      potential (G := G) obstacle who 0
        (G.emptyHist initial) := by
  calc
    expect
        (G.histDist (profile (G := G) obstacle)
          initial fuel)
        (fun history => obstacle history who) =
      G.expectedHistoryValue
        (profile (G := G) obstacle) initial
        (potential (G := G) obstacle who) fuel := by
          unfold expectedHistoryValue
          apply congrArg
          funext history
          exact (potential_at_horizon obstacle who history).symm
    _ =
      potential (G := G) obstacle who 0
        (G.emptyHist initial) :=
          expectedPotential_eq_root obstacle initial who
            fuel (le_refl fuel)

/-- Every history-dependent unilateral deviation has terminal obstacle
expectation at most the prescribed terminal obstacle expectation. -/
theorem expect_obstacle_deviation_le_profile
    (initial : G.State) (who : ι)
    (deviation : G.BehaviorStrategy who) :
    expect
        (G.histDist
          (Function.update
            (profile (G := G) obstacle) who deviation)
          initial fuel)
        (fun history => obstacle history who) ≤
      expect
        (G.histDist (profile (G := G) obstacle)
          initial fuel)
        (fun history => obstacle history who) := by
  rw [expect_obstacle_profile_eq_root obstacle initial who]
  calc
    expect
        (G.histDist
          (Function.update
            (profile (G := G) obstacle) who deviation)
          initial fuel)
        (fun history => obstacle history who) =
      G.expectedHistoryValue
        (Function.update
          (profile (G := G) obstacle) who deviation)
        initial
        (potential (G := G) obstacle who) fuel := by
          unfold expectedHistoryValue
          apply congrArg
          funext history
          exact (potential_at_horizon obstacle who history).symm
    _ ≤
      potential (G := G) obstacle who 0
        (G.emptyHist initial) :=
          expectedPotential_deviation_le_root
            obstacle initial who deviation fuel (le_refl fuel)

/-- The prescribed full-history Bellman envelope has terminal obstacle
expectation as its root value. -/
theorem expect_obstacle_profile_eq_prescribedPotential
    (initial : G.State) (who : ι) :
    expect
        (G.histDist (profile (G := G) obstacle)
          initial fuel)
        (fun history => obstacle history who) =
      (G.finiteFullHistoryControlledStoppingModel
        (profile (G := G) obstacle) obstacle).prescribedPotential
          who
          (FinitePublicHistoryControlledStoppingModel.root
            (fuel := fuel) initial) := by
  let envelope :=
    FiniteFullHistoryControlledStoppingModel.prescribedHistoryPotential
        (profile (G := G) obstacle) obstacle who
  have expected_eq_root :
      ∀ time, time ≤ fuel →
        G.expectedHistoryValue
            (profile (G := G) obstacle) initial
            envelope time =
          envelope 0 (G.emptyHist initial) := by
    intro time time_le
    induction time with
    | zero =>
        simp [expectedHistoryValue]
    | succ time ih =>
        have time_lt : time < fuel := by omega
        rw [G.expectedHistoryValue_succ]
        calc
          expect
              (G.histDist (profile (G := G) obstacle)
                initial time)
              (fun history =>
                G.historyContinuationEU
                  (profile (G := G) obstacle)
                  envelope history) =
            expect
              (G.histDist (profile (G := G) obstacle)
                initial time)
              (envelope time) := by
                  apply congrArg
                  funext history
                  exact
                    FiniteFullHistoryControlledStoppingModel.prescribedHistoryPotential_harmonic
                        (profile (G := G) obstacle) obstacle
                        who history time_lt
          _ = envelope 0 (G.emptyHist initial) :=
            ih (Nat.le_of_lt time_lt)
  calc
    expect
        (G.histDist (profile (G := G) obstacle)
          initial fuel)
        (fun history => obstacle history who) =
      G.expectedHistoryValue
        (profile (G := G) obstacle) initial envelope fuel := by
          unfold expectedHistoryValue
          apply congrArg
          funext history
          exact
            (FiniteFullHistoryControlledStoppingModel.prescribedHistoryPotential_at_horizon
                (profile (G := G) obstacle) obstacle who history).symm
    _ = envelope 0 (G.emptyHist initial) :=
      expected_eq_root fuel (le_refl fuel)
    _ =
      (G.finiteFullHistoryControlledStoppingModel
        (profile (G := G) obstacle) obstacle).prescribedPotential
          who
          (FinitePublicHistoryControlledStoppingModel.root
            (fuel := fuel) initial) := by
              rfl

/-- Backward-induction Nash selection makes the prescribed and
worst-unilateral full-horizon envelopes equal at every initial state. -/
theorem worstCasePotential_eq_prescribedPotential
    (initial : G.State) (who : ι) :
    (G.finiteFullHistoryControlledStoppingModel
      (profile (G := G) obstacle) obstacle).worstCasePotential
        who
        (FinitePublicHistoryControlledStoppingModel.root
          (fuel := fuel) initial) =
      (G.finiteFullHistoryControlledStoppingModel
        (profile (G := G) obstacle) obstacle).prescribedPotential
          who
          (FinitePublicHistoryControlledStoppingModel.root
            (fuel := fuel) initial) := by
  let canonicalDeviation :=
    FiniteFullHistoryControlledStoppingModel.optimalFiniteHorizonDeviation
        (profile (G := G) obstacle) obstacle who
  apply le_antisymm
  · calc
      (G.finiteFullHistoryControlledStoppingModel
        (profile (G := G) obstacle) obstacle).worstCasePotential
          who
          (FinitePublicHistoryControlledStoppingModel.root
            (fuel := fuel) initial) =
        expect
          (G.histDist
            (Function.update
              (profile (G := G) obstacle) who
              canonicalDeviation)
            initial fuel)
          (fun history => obstacle history who) := by
            exact
              (expect_obstacle_optimalFiniteHorizonDeviation_eq_worstCasePotential
                  (profile (G := G) obstacle) obstacle
                  initial who).symm
      _ ≤
        expect
          (G.histDist (profile (G := G) obstacle)
            initial fuel)
          (fun history => obstacle history who) :=
            expect_obstacle_deviation_le_profile
              obstacle initial who canonicalDeviation
      _ =
        (G.finiteFullHistoryControlledStoppingModel
          (profile (G := G) obstacle) obstacle).prescribedPotential
            who
            (FinitePublicHistoryControlledStoppingModel.root
              (fuel := fuel) initial) :=
                expect_obstacle_profile_eq_prescribedPotential
                  obstacle initial who
  · exact
      Math.Probability.FiniteControlledStoppingModel.prescribedPotential_le_worstCasePotential
          (G.finiteFullHistoryControlledStoppingModel
            (profile (G := G) obstacle) obstacle)
          who
          (FinitePublicHistoryControlledStoppingModel.root
            (fuel := fuel) initial)

/-- Endogenous parent payoff selected by backward induction from the
terminal obstacle. -/
def rootPayoff (initial : G.State) : Payoff ι :=
  fun who =>
    potential (G := G) obstacle who 0
      (G.emptyHist initial)

/-- Exact existential target statement.

Backward induction always supplies one parent payoff vector: its prescribed
terminal expectation.  Every unilateral behavior deviation is coordinatewise
bounded by that vector.  Nothing here asserts that this endogenous vector
equals an externally specified target. -/
theorem exists_terminalNashPayoff
    (initial : G.State) :
    ∃ target : Payoff ι,
      (∀ who,
        expect
            (G.histDist (profile (G := G) obstacle)
              initial fuel)
            (fun history => obstacle history who) =
          target who) ∧
      (∀ who (deviation : G.BehaviorStrategy who),
        expect
            (G.histDist
              (Function.update
                (profile (G := G) obstacle) who deviation)
              initial fuel)
            (fun history => obstacle history who) ≤
          target who) := by
  refine ⟨rootPayoff (G := G) obstacle initial, ?_, ?_⟩
  · intro who
    exact expect_obstacle_profile_eq_root
      obstacle initial who
  · intro who deviation
    calc
      expect
          (G.histDist
            (Function.update
              (profile (G := G) obstacle) who deviation)
            initial fuel)
          (fun history => obstacle history who) ≤
        expect
          (G.histDist (profile (G := G) obstacle)
            initial fuel)
          (fun history => obstacle history who) :=
            expect_obstacle_deviation_le_profile
              obstacle initial who deviation
      _ = rootPayoff (G := G) obstacle initial who :=
        expect_obstacle_profile_eq_root obstacle initial who

end FinitePublicTerminalNashSystem

end StochasticGame
end GameTheory
