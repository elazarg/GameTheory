/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteDynamicDebtPositiveLimit
import GameTheory.Concepts.Stochastic.QuittingPositiveDynamicDebtProvenance

/-!
# Two-ended compactification of finite exact-D chains

The ordinary projective limit of the selected finite exact-D minimizers keeps
every fixed distance from the initial root.  It necessarily forgets every
fixed distance from the zero boundary.  This file retains both views at once:

* a forward ray, indexed by distance from the initial root; and
* a reverse ray, indexed by distance from the terminal zero boundary.

The two rays are extracted along one common subsequence.  The forward ray has
ordinary exact-D edges.  The reverse ray has exact-D edges in the opposite
index direction and starts on the literal zero-payoff, singleton-cap terminal
face.  Positive optimized debt selects one owner who remains positive at
reverse depth one, where the terminal edge supplies a quantitative full-action
opponent-advantage packet.

This is deliberately only the **unscaled two-end core**.  It does not retain
bridge-survival products, convergence of a preselected terminal action or its
transported cylinder mass, a bi-infinite orbit, a splice between the two ends,
or an equilibrium repair.  Those require a separate bridge/holonomy theorem.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The selected finite min-max exact-D chain, read backward from its terminal
zero boundary and padded by its initial point after the available depth. -/
def quittingFiniteMinMaxDynamicDebtReverseTail [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff distance : ℕ) : QuittingDebtPoint ι :=
  if _hdistance : distance ≤ cutoff then
    quittingFiniteMinMaxDynamicDebtTail reward cutoff (cutoff - distance)
  else
    quittingFiniteMinMaxDynamicDebtTail reward cutoff 0

/-- Every reverse-tail point remains in the common exact-D box. -/
theorem quittingFiniteMinMaxDynamicDebtReverseTail_mem_box [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff distance : ℕ) :
    quittingFiniteMinMaxDynamicDebtReverseTail reward cutoff distance ∈
      quittingDebtBox reward := by
  unfold quittingFiniteMinMaxDynamicDebtReverseTail
  split_ifs
  · exact quittingFiniteMinMaxDynamicDebtTail_mem_box reward _ _
  · exact quittingFiniteMinMaxDynamicDebtTail_mem_box reward _ _

/-- Before the available depth, increasing reverse distance by one traverses
one literal exact-D edge backward. -/
theorem quittingFiniteMinMaxDynamicDebtReverseTail_edge [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff distance : ℕ) (hdistance : distance < cutoff) :
    IsQuittingDynamicDebtEdge reward
      (quittingFiniteMinMaxDynamicDebtReverseTail
        reward cutoff (distance + 1))
      (quittingFiniteMinMaxDynamicDebtReverseTail
        reward cutoff distance) := by
  obtain ⟨remaining, rfl⟩ :=
    Nat.exists_eq_add_of_le (Nat.succ_le_iff.mpr hdistance)
  have hfar : distance + 1 + remaining - (distance + 1) = remaining :=
    Nat.add_sub_cancel_left (distance + 1) remaining
  have hnear : distance + 1 + remaining - distance = remaining + 1 := by
    rw [show distance + 1 + remaining = distance + (remaining + 1) by omega,
      Nat.add_sub_cancel_left]
  rw [quittingFiniteMinMaxDynamicDebtReverseTail,
    dif_pos (by omega : distance + 1 ≤ distance + 1 + remaining),
    quittingFiniteMinMaxDynamicDebtReverseTail,
    dif_pos (by omega : distance ≤ distance + 1 + remaining), hfar, hnear]
  exact quittingFiniteMinMaxDynamicDebtTail_edge reward
    (distance + 1 + remaining) remaining (by omega)

/-- The reverse tail starts at the literal zero-payoff terminal face. -/
theorem quittingFiniteMinMaxDynamicDebtReverseTail_zero_payoff
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    (quittingFiniteMinMaxDynamicDebtReverseTail reward cutoff 0).1.1 = 0 := by
  rw [quittingFiniteMinMaxDynamicDebtReverseTail, dif_pos (Nat.zero_le cutoff)]
  unfold quittingFiniteMinMaxDynamicDebtTail
  simp only [Nat.sub_zero, quittingFiniteNashBellmanPathDynamicDebtPoint,
    dif_pos le_rfl]
  simpa [Fin.last] using
    (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward cutoff).2.1

/-- Its terminal debt vector is exactly the fixed singleton-cap vector. -/
theorem quittingFiniteMinMaxDynamicDebtReverseTail_zero_debt
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    (quittingFiniteMinMaxDynamicDebtReverseTail reward cutoff 0).2 =
      quittingPositiveSingletonDebtCap reward := by
  rw [quittingFiniteMinMaxDynamicDebtReverseTail, dif_pos (Nat.zero_le cutoff)]
  unfold quittingFiniteMinMaxDynamicDebtTail
  simp only [Nat.sub_zero, quittingFiniteNashBellmanPathDynamicDebtPoint,
    dif_pos le_rfl]
  funext who
  simp [quittingFiniteNashBellmanPathDynamicDebt]

/-- Every root debt coordinate is bounded by the same coordinate one step
before the terminal boundary.  At cutoff zero the reverse tail is padded by
the root, so the statement remains literal. -/
theorem quittingFiniteMinMaxDynamicDebtTail_zero_le_reverseTail_one
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (owner : ι) :
    (quittingFiniteMinMaxDynamicDebtTail reward cutoff 0).2 owner ≤
      (quittingFiniteMinMaxDynamicDebtReverseTail reward cutoff 1).2 owner := by
  rcases cutoff with _ | last
  · simp [quittingFiniteMinMaxDynamicDebtReverseTail]
  · let path :=
      quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
        reward (last + 1)
    have hpath : path ∈
        quittingFiniteZeroBoundaryNashBellmanChainSet reward (last + 1) :=
      quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
        reward (last + 1)
    have hraw :=
      quittingFiniteNashBellmanPathDynamicDebt_le_survival_mul_later
        reward (last + 1) path hpath owner 0 last (by omega) (by omega)
    have hsurvival := quittingOpponentSurvivalWeight_le_one
      (quittingFiniteNashBellmanPathRoots (last + 1) path) owner 0 last
    have hlater := quittingFiniteNashBellmanPathDynamicDebt_nonneg
      reward (last + 1) path hpath owner last
    have hle :
        quittingFiniteNashBellmanPathDynamicDebt
            reward (last + 1) path owner 0 ≤
          quittingFiniteNashBellmanPathDynamicDebt
            reward (last + 1) path owner last := by
      calc
        quittingFiniteNashBellmanPathDynamicDebt
            reward (last + 1) path owner 0 ≤
          quittingOpponentSurvivalWeight
              (quittingFiniteNashBellmanPathRoots (last + 1) path)
              owner 0 last *
            quittingFiniteNashBellmanPathDynamicDebt
              reward (last + 1) path owner last := by
                simpa using hraw
        _ ≤ quittingFiniteNashBellmanPathDynamicDebt
              reward (last + 1) path owner last :=
          mul_le_of_le_one_left hlater hsurvival
    simpa [quittingFiniteMinMaxDynamicDebtTail,
      quittingFiniteMinMaxDynamicDebtReverseTail,
      quittingFiniteNashBellmanPathDynamicDebtPoint, path] using hle

/-! ## Simultaneous compactness of both ends -/

/-- The fixed terminal face remembered by the reverse view: zero displayed
payoff and the canonical singleton-cap debt vector.  Its terminal simplex
coordinate remains free, exactly as in the finite chain definition. -/
def quittingDynamicDebtTerminalFace
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingDebtPoint ι) :=
  {point | point.1.1 = 0 ∧
    point.2 = quittingPositiveSingletonDebtCap reward}

omit [DecidableEq ι] in
/-- The anchored terminal face is closed. -/
theorem isClosed_quittingDynamicDebtTerminalFace
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsClosed (quittingDynamicDebtTerminalFace reward) := by
  unfold quittingDynamicDebtTerminalFace
  exact (isClosed_eq (by fun_prop) (by fun_prop)).inter
    (isClosed_eq (by fun_prop) (by fun_prop))

/-- Every selected reverse tail begins on the same closed terminal face. -/
theorem quittingFiniteMinMaxDynamicDebtReverseTail_zero_mem_terminalFace
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    quittingFiniteMinMaxDynamicDebtReverseTail reward cutoff 0 ∈
      quittingDynamicDebtTerminalFace reward := by
  exact ⟨quittingFiniteMinMaxDynamicDebtReverseTail_zero_payoff reward cutoff,
    quittingFiniteMinMaxDynamicDebtReverseTail_zero_debt reward cutoff⟩

/-- The quantitative full-action packet carried by a positive incoming
terminal edge. -/
def HasQuittingTerminalOpponentAdvantagePacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current : QuittingDebtPoint ι) (owner : ι) : Prop :=
  ∃ action : ι → Bool,
    0 < ((pmfPi (Function.update
      (quittingRootOfSimplex current.1.2) owner
        (PMF.pure false))) action).toReal ∧
    0 < quittingTerminalOpponentAdvantage reward owner action ∧
    current.2 owner ≤ (Fintype.card (ι → Bool) : ℝ) *
      ((pmfPi (Function.update
        (quittingRootOfSimplex current.1.2) owner
          (PMF.pure false))) action).toReal *
        quittingTerminalOpponentAdvantage reward owner action

/-- A positive exact-D edge into the terminal face already contains the
quantitative residual-depth-one full-action packet.  Thus the reverse limit
does not merely remember a boundary point: positive incoming debt forces an
actual opponent action with positive product mass and positive advantage. -/
theorem exists_terminalOpponentAdvantage_atom_of_dynamicDebt_terminalEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current terminal : QuittingDebtPoint ι) (owner : ι)
    (hterminalBox : terminal ∈ quittingDebtBox reward)
    (hterminal : terminal ∈ quittingDynamicDebtTerminalFace reward)
    (hedge : IsQuittingDynamicDebtEdge reward current terminal)
    (hpositive : 0 < current.2 owner) :
    HasQuittingTerminalOpponentAdvantagePacket reward current owner := by
  unfold HasQuittingTerminalOpponentAdvantagePacket
  let root := quittingRootOfSimplex current.1.2
  let singleton := reward (quittingSingletonTerminal owner) owner
  let quitValue := quittingRootQuitPayoff reward terminal.1.1 root owner
  let augmented :=
    quittingRootContinuePayoff reward terminal.1.1 root owner +
      quittingDebtOpponentContinueMass current owner * terminal.2 owner
  have hmul := quittingDynamicDebtUpdate_le_mul reward current terminal
    hedge.1 hterminalBox.2.1 owner
  rw [← hedge.2 owner] at hmul
  have hproduct : 0 <
      quittingDebtOpponentContinueMass current owner * terminal.2 owner :=
    hpositive.trans_le hmul
  have hterminalDebtPositive : 0 < terminal.2 owner :=
    pos_of_mul_pos_right hproduct
      (quittingDebtOpponentContinueMass_nonneg current owner)
  have hcapPositive :
      0 < quittingPositiveSingletonDebtCap reward owner := by
    rw [← congrFun hterminal.2 owner]
    exact hterminalDebtPositive
  have hsingleton : 0 < singleton := by
    unfold quittingPositiveSingletonDebtCap at hcapPositive
    dsimp only [singleton]
    by_contra hnot
    rw [max_eq_left (le_of_not_gt hnot)] at hcapPositive
    exact (lt_irrefl 0 hcapPositive).elim
  have hcapEq : quittingPositiveSingletonDebtCap reward owner = singleton :=
    max_eq_right (le_of_lt hsingleton)
  have hquitLe : quitValue ≤ current.1.1 owner := by
    exact quittingRootQuitPayoff_le_currentValue_of_nashBellmanEdge
      reward current.1 terminal.1 hedge.1 owner
  have hupdatePositive :
      0 < quittingDynamicDebtUpdate reward current terminal owner := by
    rwa [← hedge.2 owner]
  have haugmentedGreater : current.1.1 owner < augmented := by
    by_contra hnot
    have haugmentedLe : augmented ≤ current.1.1 owner := le_of_not_gt hnot
    have hmaxLe : max quitValue augmented ≤ current.1.1 owner :=
      max_le hquitLe haugmentedLe
    unfold quittingDynamicDebtUpdate at hupdatePositive
    change 0 < max quitValue augmented - current.1.1 owner at hupdatePositive
    linarith
  have hdebtEq : current.2 owner = augmented - current.1.1 owner := by
    rw [hedge.2 owner]
    unfold quittingDynamicDebtUpdate
    change max quitValue augmented - current.1.1 owner = _
    rw [max_eq_right (hquitLe.trans (le_of_lt haugmentedGreater))]
  have hdebtLe : current.2 owner ≤ augmented - quitValue := by
    rw [hdebtEq]
    linarith
  have haugmentedEq :
      augmented = quittingRootContinuePayoff reward
        (fun _ ↦ singleton) root owner := by
    let roots : ℕ → ι → PMF Bool := fun _ ↦ root
    have hzero := quittingRootContinuePayoff_eq_fixedOpponents
      reward roots owner terminal.1.1 0
    have hsingletonContinue := quittingRootContinuePayoff_eq_fixedOpponents
      reward roots owner (fun _ ↦ singleton) 0
    have hmass : quittingFixedOpponentsContinueMass roots owner 0 =
        quittingDebtOpponentContinueMass current owner := by
      unfold quittingFixedOpponentsContinueMass roots root
      exact (quittingDebtOpponentContinueMass_eq_stationary
        current owner).symm
    simp only [roots] at hzero hsingletonContinue
    dsimp only [augmented]
    rw [hterminal.1, congrFun hterminal.2 owner, hcapEq]
    rw [hterminal.1] at hzero
    rw [hzero, hsingletonContinue, hmass]
    simp
  have hexpect :
      expect (pmfPi (Function.update root owner (PMF.pure false)))
          (quittingTerminalOpponentAdvantage reward owner) =
        augmented - quitValue := by
    rw [expect_terminalOpponentAdvantage, ← haugmentedEq]
    simp [quitValue, root, hterminal.1]
  have hdebtExpectation : current.2 owner ≤
      expect (pmfPi (Function.update root owner (PMF.pure false)))
        (quittingTerminalOpponentAdvantage reward owner) := by
    rw [hexpect]
    exact hdebtLe
  obtain ⟨action, hmass, hadvantage, hweighted, _⟩ :=
    exists_terminalOpponentAdvantage_atom_quantitative_of_pos
      reward root owner (current.2 owner) hpositive hdebtExpectation
  exact ⟨action, hmass, hadvantage, hweighted⟩

-- The nested compactness/subsequence extraction is substantially more
-- expensive than the local edge lemmas above.
/-- **Two-ended exact-D compactification.**  The independently selected
finite min-max chains admit one subsequence on which both their root view and
their terminal view converge.  The root view is a forward exact-D ray.  The
terminal view is a reverse exact-D ray ending at the literal terminal face.

This is deliberately not a bi-infinite orbit: no finite or limiting bridge
between the two rays is asserted. -/
theorem exists_twoEnded_projective_quittingDynamicDebtTail [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ (forward reverse : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
          subseq) atTop (nhds forward) ∧
      Tendsto
        ((fun cutoff ↦
          quittingFiniteMinMaxDynamicDebtReverseTail reward cutoff) ∘
          subseq) atTop (nhds reverse) ∧
      (∀ time, forward time ∈ quittingDebtBox reward) ∧
      (∀ time, reverse time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (forward time) (forward (time + 1))) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (reverse (time + 1)) (reverse time)) ∧
      reverse 0 ∈ quittingDynamicDebtTerminalFace reward := by
  obtain ⟨forward, firstSubseq, hfirstSubseq, hforward,
      hforwardBox, hforwardEdge⟩ :=
    exists_projective_quittingDynamicDebtTail_of_residualDepth_tendsto
      reward id (quittingFiniteMinMaxDynamicDebtTail reward)
      (quittingFiniteMinMaxDynamicDebtTail_mem_box reward)
      (quittingFiniteMinMaxDynamicDebtTail_edge reward) tendsto_id
  let pathBox : Set (ℕ → QuittingDebtPoint ι) :=
    {path | ∀ time, path time ∈ quittingDebtBox reward}
  have hpathBoxCompact : IsCompact pathBox := by
    dsimp only [pathBox]
    exact isCompact_pi_infinite fun _ ↦ quittingDebtBox_isCompact reward
  have hreverseFamily : ∀ family,
      (fun time ↦ quittingFiniteMinMaxDynamicDebtReverseTail reward
        (firstSubseq family) time) ∈ pathBox := by
    intro family time
    exact quittingFiniteMinMaxDynamicDebtReverseTail_mem_box reward _ _
  obtain ⟨reverse, hreverseBox, secondSubseq, hsecondSubseq, hreverse⟩ :=
    hpathBoxCompact.tendsto_subseq hreverseFamily
  let subseq := firstSubseq ∘ secondSubseq
  have hsubseq : StrictMono subseq := hfirstSubseq.comp hsecondSubseq
  have hsubseqAtTop : Tendsto subseq atTop atTop := hsubseq.tendsto_atTop
  have hforward' : Tendsto
      ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
        subseq) atTop (nhds forward) := by
    simpa [subseq, Function.comp_def] using
      hforward.comp hsecondSubseq.tendsto_atTop
  have hreverse' : Tendsto
      ((fun cutoff ↦
        quittingFiniteMinMaxDynamicDebtReverseTail reward cutoff) ∘
        subseq) atTop (nhds reverse) := by
    simpa [subseq, Function.comp_def] using hreverse
  refine ⟨forward, reverse, subseq, hsubseq, hforward', hreverse',
    hforwardBox, hreverseBox, hforwardEdge, ?_, ?_⟩
  · intro time
    have hfar : Tendsto
        (fun family ↦ quittingFiniteMinMaxDynamicDebtReverseTail reward
          (subseq family) (time + 1))
        atTop (nhds (reverse (time + 1))) := by
      exact ((continuous_apply (time + 1)).tendsto reverse).comp hreverse'
    have hnear : Tendsto
        (fun family ↦ quittingFiniteMinMaxDynamicDebtReverseTail reward
          (subseq family) time)
        atTop (nhds (reverse time)) := by
      exact ((continuous_apply time).tendsto reverse).comp hreverse'
    have hpairs : Tendsto
        (fun family ↦
          (quittingFiniteMinMaxDynamicDebtReverseTail reward
              (subseq family) (time + 1),
            quittingFiniteMinMaxDynamicDebtReverseTail reward
              (subseq family) time))
        atTop (nhds (reverse (time + 1), reverse time)) :=
      hfar.prodMk_nhds hnear
    have heventually : ∀ᶠ family in atTop,
        (quittingFiniteMinMaxDynamicDebtReverseTail reward
            (subseq family) (time + 1),
          quittingFiniteMinMaxDynamicDebtReverseTail reward
            (subseq family) time) ∈
          quittingDynamicDebtEdgeGraph reward := by
      filter_upwards [tendsto_atTop.1 hsubseqAtTop (time + 1)] with
        family hfamily
      exact ⟨
        quittingFiniteMinMaxDynamicDebtReverseTail_mem_box reward _ _,
        quittingFiniteMinMaxDynamicDebtReverseTail_mem_box reward _ _,
        quittingFiniteMinMaxDynamicDebtReverseTail_edge reward _ time
          (by omega)⟩
    exact ((isClosed_quittingDynamicDebtEdgeGraph reward).mem_of_tendsto
      hpairs heventually).2.2
  · have hzero : Tendsto
        (fun family ↦ quittingFiniteMinMaxDynamicDebtReverseTail reward
          (subseq family) 0)
        atTop (nhds (reverse 0)) :=
      ((continuous_apply 0).tendsto reverse).comp hreverse'
    exact (isClosed_quittingDynamicDebtTerminalFace reward).mem_of_tendsto
      hzero (Filter.Eventually.of_forall fun family ↦
        quittingFiniteMinMaxDynamicDebtReverseTail_zero_mem_terminalFace
          reward (subseq family))

/-! ## The positive optimized-debt branch with both ends retained -/

-- This theorem combines the two-ended extraction with the calibrated-owner
-- limit and therefore needs the same enlarged elaboration budget.
/-- A positive optimized exact-debt infimum admits a two-ended limit whose
forward ray retains a positive debt coordinate and its summable opponent
clock, while the reverse ray retains the literal terminal face. -/
theorem exists_twoEnded_positiveDynamicDebtTail_of_iInf_minMax_pos
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpositive : 0 < ⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
        reward cutoff) :
    ∃ (forward reverse : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ)
        (owner : ι),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
          subseq) atTop (nhds forward) ∧
      Tendsto
        ((fun cutoff ↦
          quittingFiniteMinMaxDynamicDebtReverseTail reward cutoff) ∘
          subseq) atTop (nhds reverse) ∧
      (∀ time, forward time ∈ quittingDebtBox reward) ∧
      (∀ time, reverse time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (forward time) (forward (time + 1))) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (reverse (time + 1)) (reverse time)) ∧
      reverse 0 ∈ quittingDynamicDebtTerminalFace reward ∧
      0 < (forward 0).2 owner ∧
      0 < (reverse 1).2 owner ∧
      HasQuittingTerminalOpponentAdvantagePacket reward (reverse 1) owner ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots forward) owner) := by
  obtain ⟨forward, reverse, subseq, hsubseq, hforward, hreverse,
      hforwardBox, hreverseBox, hforwardEdge, hreverseEdge,
      hterminal⟩ :=
    exists_twoEnded_projective_quittingDynamicDebtTail reward
  have hpointZero : Tendsto
      (fun family ↦ quittingFiniteMinMaxDynamicDebtTail reward
        (subseq family) 0)
      atTop (nhds (forward 0)) :=
    ((continuous_apply 0).tendsto forward).comp hforward
  have hmax : Tendsto
      (fun family ↦ quittingDebtPointMaxDebt
        (quittingFiniteMinMaxDynamicDebtTail reward (subseq family) 0))
      atTop (nhds (quittingDebtPointMaxDebt (forward 0))) :=
    (continuous_quittingDebtPointMaxDebt.tendsto (forward 0)).comp hpointZero
  have hbdd : BddBelow (Set.range fun cutoff : ℕ ↦
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
        reward cutoff) := by
    refine ⟨0, ?_⟩
    rintro value ⟨cutoff, rfl⟩
    exact quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_nonneg
      reward cutoff
  have hlower : ∀ family,
      (⨅ cutoff : ℕ,
          quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
            reward cutoff) ≤
        quittingDebtPointMaxDebt
          (quittingFiniteMinMaxDynamicDebtTail
            reward (subseq family) 0) := by
    intro family
    rw [quittingDebtPointMaxDebt_finiteMinMaxTail_zero]
    exact ciInf_le hbdd (subseq family)
  have hlimitLower :
      (⨅ cutoff : ℕ,
          quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
            reward cutoff) ≤
        quittingDebtPointMaxDebt (forward 0) :=
    ge_of_tendsto' hmax hlower
  have hmaxPositive : 0 < quittingDebtPointMaxDebt (forward 0) :=
    hpositive.trans_le hlimitLower
  obtain ⟨owner, _, howner⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (forward 0).2
  have hownerPositive : 0 < (forward 0).2 owner := by
    unfold quittingDebtPointMaxDebt at hmaxPositive
    rwa [howner] at hmaxPositive
  have hforwardDebt : Tendsto
      (fun family ↦
        (quittingFiniteMinMaxDynamicDebtTail reward (subseq family) 0).2
          owner)
      atTop (nhds ((forward 0).2 owner)) := by
    have hcontinuous : Continuous
        (fun point : QuittingDebtPoint ι ↦ point.2 owner) := by fun_prop
    exact (hcontinuous.tendsto (forward 0)).comp hpointZero
  have hreversePointOne : Tendsto
      (fun family ↦ quittingFiniteMinMaxDynamicDebtReverseTail reward
        (subseq family) 1)
      atTop (nhds (reverse 1)) :=
    ((continuous_apply 1).tendsto reverse).comp hreverse
  have hreverseDebt : Tendsto
      (fun family ↦
        (quittingFiniteMinMaxDynamicDebtReverseTail reward
          (subseq family) 1).2 owner)
      atTop (nhds ((reverse 1).2 owner)) := by
    have hcontinuous : Continuous
        (fun point : QuittingDebtPoint ι ↦ point.2 owner) := by fun_prop
    exact (hcontinuous.tendsto (reverse 1)).comp hreversePointOne
  have hgap : Tendsto
      (fun family ↦
        (quittingFiniteMinMaxDynamicDebtReverseTail reward
            (subseq family) 1).2 owner -
          (quittingFiniteMinMaxDynamicDebtTail reward
            (subseq family) 0).2 owner)
      atTop (nhds ((reverse 1).2 owner - (forward 0).2 owner)) :=
    hreverseDebt.sub hforwardDebt
  have hgapNonneg :
      0 ≤ (reverse 1).2 owner - (forward 0).2 owner :=
    ge_of_tendsto' hgap fun family ↦ sub_nonneg.mpr
      (quittingFiniteMinMaxDynamicDebtTail_zero_le_reverseTail_one
        reward (subseq family) owner)
  have hreversePositive : 0 < (reverse 1).2 owner := by linarith
  have hterminalPacket :=
    exists_terminalOpponentAdvantage_atom_of_dynamicDebt_terminalEdge
      reward (reverse 1) (reverse 0) owner (hreverseBox 0) hterminal
        (hreverseEdge 0) hreversePositive
  have hclock := summable_clock_of_quittingDynamicDebtTail_pos
    reward forward hforwardBox hforwardEdge owner 0 hownerPositive
  exact ⟨forward, reverse, subseq, owner, hsubseq, hforward, hreverse,
    hforwardBox, hreverseBox, hforwardEdge, hreverseEdge, hterminal,
    hownerPositive, hreversePositive, hterminalPacket, hclock⟩

/-- The production finite-chain program can therefore retain a terminal-end
ray even in its exceptional branch: either compilation already succeeds, or
one common subsequence yields a positive forward exact-D ray and an anchored
reverse exact-D ray. -/
theorem quittingGame_uniformEquilibriumPayoff_or_twoEndedPositiveDynamicDebtTail
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
    ∃ (forward reverse : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ)
        (owner : ι),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
          subseq) atTop (nhds forward) ∧
      Tendsto
        ((fun cutoff ↦
          quittingFiniteMinMaxDynamicDebtReverseTail reward cutoff) ∘
          subseq) atTop (nhds reverse) ∧
      (∀ time, forward time ∈ quittingDebtBox reward) ∧
      (∀ time, reverse time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (forward time) (forward (time + 1))) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (reverse (time + 1)) (reverse time)) ∧
      reverse 0 ∈ quittingDynamicDebtTerminalFace reward ∧
      0 < (forward 0).2 owner ∧
      0 < (reverse 1).2 owner ∧
      HasQuittingTerminalOpponentAdvantagePacket reward (reverse 1) owner ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots forward) owner) := by
  let obstruction := ⨅ cutoff : ℕ,
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff
  by_cases hzero : obstruction = 0
  · exact Or.inl
      (quittingGame_exists_uniformEquilibriumPayoff_of_iInf_finiteMinMaxDynamicDebt_eq_zero
        reward hzero)
  · apply Or.inr
    apply exists_twoEnded_positiveDynamicDebtTail_of_iInf_minMax_pos reward
    exact lt_of_le_of_ne
      (iInf_quittingFiniteMinMaxDynamicDebt_nonneg reward)
      (Ne.symm hzero)

end GameTheory
