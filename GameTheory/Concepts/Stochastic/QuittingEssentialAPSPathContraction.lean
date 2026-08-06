/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPSUniformWindowMassLive
import GameTheory.Concepts.Stochastic.QuittingEssentialAPSOpponentContraction
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Block contraction along essential-APS successor paths

This module composes the compact `nu`-lemma with the bounded-drift opponent
mass estimate.

For every possible starting owner, compact active-face separation gives a
positive total-mass constant on its successor orbit. There are only finitely
many owners, so the minimum of these constants is still positive and works at
every time shift of one infinite path. The strict Flesch cross-gain also has a
positive finite minimum. Concatenating enough `nu`-windows then makes the
playerwise opponent-mass lower bound positive, and the singleton-root product
estimate yields a uniform block contraction factor `rho < 1`.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Iterates of a displayed successor map, written recursively to expose the
zero and successor equations directly. -/
def quittingEssentialAPSSuccessorOrbit
    (successor : ι → ι) (start : ι) : ℕ → ι
  | 0 => start
  | time + 1 => successor
      (quittingEssentialAPSSuccessorOrbit successor start time)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingEssentialAPSSuccessorOrbit_zero
    (successor : ι → ι) (start : ι) :
    quittingEssentialAPSSuccessorOrbit successor start 0 = start := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingEssentialAPSSuccessorOrbit_succ
    (successor : ι → ι) (start : ι) (time : ℕ) :
    quittingEssentialAPSSuccessorOrbit successor start (time + 1) =
      successor (quittingEssentialAPSSuccessorOrbit successor start time) := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- A path following `successor` agrees after every shift with the canonical
successor orbit from its shifted owner. -/
theorem quittingEssentialAPS_owner_add_eq_successorOrbit
    (successor : ι → ι) (owner : ℕ → ι)
    (hownerNext : ∀ time,
      owner (time + 1) = successor (owner time)) :
    ∀ start time,
      owner (start + time) =
        quittingEssentialAPSSuccessorOrbit successor (owner start) time := by
  intro start time
  induction time with
  | zero => simp
  | succ time ih =>
      rw [show start + time.succ = start + time + 1 by omega,
        hownerNext, ih]
      rfl

omit [Fintype ι] [DecidableEq ι] in
/-- The forward cross-gains of a finite Flesch successor map have one uniform
strictly positive lower bound. -/
theorem exists_uniform_quittingFleschSuccessor_forwardGap [Finite ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (successor : ι → ι) (base : ι)
    (hedge : ∀ player,
      QuittingFleschSuccessor reward player (successor player)) :
    ∃ gap : ℝ, 0 < gap ∧
      ∀ player,
        gap ≤ quittingSoloReward reward player (successor player) -
          quittingSoloReward reward (successor player) (successor player) := by
  let gain : ι → ℝ := fun player ↦
    quittingSoloReward reward player (successor player) -
      quittingSoloReward reward (successor player) (successor player)
  have hgainPos : ∀ player, 0 < gain player := by
    intro player
    exact sub_pos.mpr (hedge player).2
  have hcompact : IsCompact (Set.range gain) :=
    (Set.finite_range gain).isCompact
  have hnonempty : (Set.range gain).Nonempty :=
    ⟨gain base, ⟨base, rfl⟩⟩
  obtain ⟨_minimum, ⟨minPlayer, rfl⟩, hleast⟩ :=
    hcompact.exists_isLeast hnonempty
  have hleastPlayer : ∀ player, gain minPlayer ≤ gain player := by
    intro player
    exact hleast ⟨player, rfl⟩
  exact ⟨gain minPlayer, hgainPos minPlayer, hleastPlayer⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **One total-mass constant works at every shifted start.** The local
compact separation constants are minimized over the finite owner type. Empty
greatest fibers are assigned an arbitrary positive constant and never enter
the path argument. -/
theorem
    exists_uniform_quittingEssentialAPSWindowMass_along_successor_path_unique_live
    [Finite ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrierCompact : ∀ player, IsCompact (carrier player))
    (hcarrierConvex : ∀ player, Convex ℝ (carrier player))
    (successor : ι → ι)
    (hedge : ∀ player,
      QuittingFleschSuccessor reward player (successor player))
    (huniqueLive : ∀ player candidate,
      QuittingFleschSuccessor reward player candidate →
        candidate ≠ successor player →
          quittingEssentialAPSGreatestFamily reward carrier candidate = ∅)
    (horizon : ℕ)
    (hfaceAvoidance : ∀ player current,
      current ∈ quittingEssentialAPSGreatestFamily reward carrier player →
        ¬ IsQuittingEssentialAPSActiveAlong reward
          (quittingEssentialAPSSuccessorOrbit successor player)
          current horizon)
    {bound : ℝ} (hbound : 0 < bound)
    (hrootBound : ∀ quitter who,
      |quittingSoloReward reward quitter who| ≤ bound)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (hownerNext : ∀ time,
      owner (time + 1) = successor (owner time))
    (hvalueMem : ∀ time,
      value time ∈
        quittingEssentialAPSGreatestFamily reward carrier (owner time))
    (hmass0 : ∀ time, 0 ≤ mass time)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hvalueBound : ∀ time who, |value time who| ≤ bound) :
    ∃ nu : ℝ, 0 < nu ∧
      ∀ start,
        nu ≤ quittingEssentialAPSWindowMass mass start horizon := by
  classical
  have hlocal : ∀ player, ∃ nu : ℝ, 0 < nu ∧
      ∀ (shiftMass : ℕ → ℝ) (shiftValue : ℕ → Payoff ι),
        shiftValue 0 ∈
            quittingEssentialAPSGreatestFamily reward carrier player →
        (∀ time, 0 ≤ shiftMass time) →
        (∀ time,
          shiftValue time = quittingSingletonArcPayoff (shiftMass time)
            (quittingSoloReward reward
              (quittingEssentialAPSSuccessorOrbit successor player time))
            (shiftValue (time + 1))) →
        (∀ time,
          shiftValue time
              (quittingEssentialAPSSuccessorOrbit successor player time) =
            quittingSoloReward reward
              (quittingEssentialAPSSuccessorOrbit successor player time)
              (quittingEssentialAPSSuccessorOrbit successor player time)) →
        (∀ time who, |shiftValue time who| ≤ bound) →
        nu ≤ ∑ time ∈ Finset.range horizon, shiftMass time := by
    intro player
    by_cases hnonempty :
        (quittingEssentialAPSGreatestFamily reward carrier player).Nonempty
    · exact
        exists_uniform_quittingEssentialAPS_windowMass_of_greatest_faceAvoidance_unique_live
          reward carrier hcarrierCompact hcarrierConvex successor hedge
            huniqueLive
            (quittingEssentialAPSSuccessorOrbit successor player)
            horizon hnonempty (hfaceAvoidance player) hbound
            (fun time who ↦ hrootBound _ _)
    · refine ⟨1, zero_lt_one, ?_⟩
      intro shiftMass shiftValue hvalue0 _ _ _ _
      exact False.elim (hnonempty ⟨shiftValue 0, hvalue0⟩)
  choose localNu hlocalNuPos hlocalBound using hlocal
  have hnuCompact : IsCompact (Set.range localNu) :=
    (Set.finite_range localNu).isCompact
  have hnuNonempty : (Set.range localNu).Nonempty :=
    ⟨localNu (owner 0), ⟨owner 0, rfl⟩⟩
  obtain ⟨_minimum, ⟨minPlayer, rfl⟩, hminimum⟩ :=
    hnuCompact.exists_isLeast hnuNonempty
  have hminimumPlayer : ∀ player,
      localNu minPlayer ≤ localNu player := by
    intro player
    exact hminimum ⟨player, rfl⟩
  refine ⟨localNu minPlayer, hlocalNuPos minPlayer, ?_⟩
  intro start
  have hshift := hlocalBound (owner start)
    (fun time ↦ mass (start + time))
    (fun time ↦ value (start + time))
    (by simpa using hvalueMem start)
    (fun time ↦ hmass0 (start + time))
    (by
      intro time
      have hownerEq := quittingEssentialAPS_owner_add_eq_successorOrbit
        successor owner hownerNext start time
      rw [← hownerEq]
      simpa only [Nat.add_assoc] using harc (start + time))
    (by
      intro time
      have hownerEq := quittingEssentialAPS_owner_add_eq_successorOrbit
        successor owner hownerNext start time
      rw [← hownerEq]
      exact hactive (start + time))
    (fun time who ↦ hvalueBound (start + time) who)
  calc
    localNu minPlayer ≤ localNu (owner start) := hminimumPlayer (owner start)
    _ ≤ quittingEssentialAPSWindowMass mass start horizon := by
      simpa only [quittingEssentialAPSWindowMass] using hshift

/-- **Compact face avoidance gives executable opponent block contraction.**
For any bounded active APS path following a finite unique-live successor map,
there are explicit constants `K > 0` and `rho < 1` satisfying the block
contraction hypothesis for the implemented singleton roots. -/
theorem
    exists_quittingEssentialAPSPath_opponentBlockContraction_unique_live
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrierCompact : ∀ player, IsCompact (carrier player))
    (hcarrierConvex : ∀ player, Convex ℝ (carrier player))
    (successor : ι → ι)
    (hedge : ∀ player,
      QuittingFleschSuccessor reward player (successor player))
    (huniqueLive : ∀ player candidate,
      QuittingFleschSuccessor reward player candidate →
        candidate ≠ successor player →
          quittingEssentialAPSGreatestFamily reward carrier candidate = ∅)
    {horizon : ℕ} (horizonPos : 0 < horizon)
    (hfaceAvoidance : ∀ player current,
      current ∈ quittingEssentialAPSGreatestFamily reward carrier player →
        ¬ IsQuittingEssentialAPSActiveAlong reward
          (quittingEssentialAPSSuccessorOrbit successor player)
          current horizon)
    {bound : ℝ} (hbound : 0 < bound)
    (hrootBound : ∀ quitter who,
      |quittingSoloReward reward quitter who| ≤ bound)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (hownerNext : ∀ time,
      owner (time + 1) = successor (owner time))
    (hvalueMem : ∀ time,
      value time ∈
        quittingEssentialAPSGreatestFamily reward carrier (owner time))
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hvalueBound : ∀ time who, |value time who| ≤ bound) :
    ∃ K : ℕ, ∃ eta rho : ℝ,
      0 < K ∧ 0 < eta ∧ 0 ≤ rho ∧ rho < 1 ∧
        IsQuittingOpponentBlockContraction
          (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
          K rho := by
  obtain ⟨nu, hnuPos, hwindow⟩ :=
    exists_uniform_quittingEssentialAPSWindowMass_along_successor_path_unique_live
      reward carrier hcarrierCompact hcarrierConvex successor hedge
        huniqueLive horizon hfaceAvoidance hbound hrootBound
        owner mass value hownerNext hvalueMem hmass0 harc hactive hvalueBound
  obtain ⟨gap, hgapPos, hgap⟩ :=
    exists_uniform_quittingFleschSuccessor_forwardGap
      reward successor (owner 0) hedge
  have hscale : 0 < gap * nu := mul_pos hgapPos hnuPos
  obtain ⟨blocks, hblocksGt⟩ :=
    exists_nat_gt (2 * bound / (gap * nu))
  have hratio0 : 0 ≤ 2 * bound / (gap * nu) := by
    exact div_nonneg (by positivity) hscale.le
  have hblocksReal : 0 < (blocks : ℝ) :=
    hratio0.trans_lt hblocksGt
  have hblocksPos : 0 < blocks := by
    exact_mod_cast hblocksReal
  have hlarge : 2 * bound < gap * ((blocks : ℝ) * nu) := by
    calc
      2 * bound = (2 * bound / (gap * nu)) * (gap * nu) :=
        (div_mul_cancel₀ _ (ne_of_gt hscale)).symm
      _ < (blocks : ℝ) * (gap * nu) :=
        mul_lt_mul_of_pos_right hblocksGt hscale
      _ = gap * ((blocks : ℝ) * nu) := by ring
  let K := blocks * horizon
  let eta :=
    (gap * ((blocks : ℝ) * nu) - 2 * bound) / (gap + 2 * bound)
  let rho := 1 / (1 + eta)
  refine ⟨K, eta, rho, ?_⟩
  have hcertificate :=
    isQuittingOpponentBlockContraction_singletonRoots_of_windowMass
      reward successor owner mass value hgapPos hbound.le hnuPos hwindow
        horizonPos hblocksPos hlarge hmass0 hmass1 harc hactive hownerNext
        hgap (fun time who ↦ hrootBound _ _) hvalueBound
  simpa only [K, eta, rho] using hcertificate

end GameTheory
