/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingDebtOccupationCompactness

/-!
# Projective chronological limits of finite quitting debt tails

Repeated player flags need not advance time: they may only re-mark one
bounded-depth terminal packet.  This file therefore separates the elementary
residual-depth alternative before applying compactness.

When the residual depths genuinely tend to infinity, a family of actual
rooted finite tails in the compact debt box has a coordinatewise convergent
subsequence.  Closedness of the exact edge graph makes its limit one
chronologically compatible infinite debt tail.  If every fixed local loss
also tends to zero, all limit edges are zero-loss and inherit the finite
All-Continue/solo support classification.

No finite-graph recurrence, hazard divergence, or equilibrium conclusion is
claimed.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Residual-depth alternative -/

/-- A sequence of residual depths either escapes every finite bound, or one
finite bound is visited infinitely often.  The second branch is the
bounded-depth terminal-packet branch, not temporal recurrence. -/
theorem residualDepth_tendsto_atTop_or_frequently_bounded
    (depth : ℕ → ℕ) :
    Tendsto depth atTop atTop ∨
      ∃ bound, ∃ᶠ index in atTop, depth index ≤ bound := by
  by_cases hdepth : Tendsto depth atTop atTop
  · exact Or.inl hdepth
  · right
    simp only [tendsto_atTop, not_forall, not_eventually] at hdepth
    obtain ⟨bound, hbound⟩ := hdepth
    refine ⟨bound, ?_⟩
    exact hbound.mono fun index hindex ↦ by omega

/-! ## Projective chronological extraction -/

omit [DecidableEq ι] in
/-- Coordinatewise continuity of total debt-edge loss. -/
theorem continuous_quittingDebtEdgeLoss :
    Continuous (fun edge : QuittingDebtPoint ι × QuittingDebtPoint ι ↦
      quittingDebtEdgeLoss edge.1 edge.2) := by
  unfold quittingDebtEdgeLoss quittingDebtCoordinateLoss
  fun_prop

omit [DecidableEq ι] in
/-- A family of debt paths contained coordinatewise in the compact debt box
has a coordinatewise convergent subsequence whose limit remains in that box. -/
theorem exists_projective_quittingDebtTail_limit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ℕ → ℕ → QuittingDebtPoint ι)
    (hbox : ∀ family time, tail family time ∈ quittingDebtBox reward) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
      Tendsto ((fun family ↦ tail family) ∘ subseq) atTop (nhds limit) ∧
      ∀ time, limit time ∈ quittingDebtBox reward := by
  let pathBox : Set (ℕ → QuittingDebtPoint ι) :=
    {path | ∀ time, path time ∈ quittingDebtBox reward}
  have hpathBoxCompact : IsCompact pathBox := by
    dsimp only [pathBox]
    exact isCompact_pi_infinite fun _ ↦ quittingDebtBox_isCompact reward
  have htailMem : ∀ family, (fun time ↦ tail family time) ∈ pathBox :=
    fun family time ↦ hbox family time
  obtain ⟨limit, hlimitBox, subseq, hsubseq, hlimit⟩ :=
    hpathBoxCompact.tendsto_subseq htailMem
  exact ⟨limit, subseq, hsubseq, hlimit, hlimitBox⟩

omit [DecidableEq ι] in
/-- Coordinatewise projective convergence implies convergence of every
fixed adjacent pair. -/
theorem tendsto_projective_adjacentPair
    (tail : ℕ → ℕ → QuittingDebtPoint ι)
    (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ)
    (hlimit : Tendsto ((fun family ↦ tail family) ∘ subseq)
      atTop (nhds limit))
    (time : ℕ) : Tendsto
      (fun family ↦
        (tail (subseq family) time, tail (subseq family) (time + 1)))
      atTop (nhds (limit time, limit (time + 1))) := by
  have hcurrent : Tendsto (fun family ↦ tail (subseq family) time)
      atTop (nhds (limit time)) := by
    exact ((continuous_apply time).tendsto limit).comp hlimit
  have hsuccessor : Tendsto (fun family ↦ tail (subseq family) (time + 1))
      atTop (nhds (limit (time + 1))) := by
    exact ((continuous_apply (time + 1)).tendsto limit).comp hlimit
  exact hcurrent.prodMk_nhds hsuccessor

/-- Every fixed adjacent pair eventually lies in the exact debt-edge graph
when residual depth tends to infinity. -/
theorem eventually_projective_adjacentPair_mem_debtEdgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (depth : ℕ → ℕ)
    (tail : ℕ → ℕ → QuittingDebtPoint ι)
    (hbox : ∀ family time, tail family time ∈ quittingDebtBox reward)
    (hedge : ∀ family time, time < depth family →
      IsQuittingDebtEdge reward (tail family time) (tail family (time + 1)))
    (hdepth : Tendsto depth atTop atTop)
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq) (time : ℕ) :
    ∀ᶠ family in atTop,
      (tail (subseq family) time, tail (subseq family) (time + 1)) ∈
        quittingDebtEdgeGraph reward := by
  have hdepthSubseq : Tendsto (depth ∘ subseq) atTop atTop :=
    hdepth.comp hsubseq.tendsto_atTop
  filter_upwards [tendsto_atTop.1 hdepthSubseq (time + 1)] with family hfamily
  change time + 1 ≤ depth (subseq family) at hfamily
  exact ⟨hbox (subseq family) time, hbox (subseq family) (time + 1),
    hedge (subseq family) time (by omega)⟩

omit [DecidableEq ι] in
/-- Vanishing loss along a convergent projective subsequence passes to each
fixed adjacent pair. -/
theorem quittingDebtEdgeLoss_eq_zero_of_projective_limit
    (tail : ℕ → ℕ → QuittingDebtPoint ι)
    (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hlimit : Tendsto ((fun family ↦ tail family) ∘ subseq)
      atTop (nhds limit))
    (hloss : ∀ time, Tendsto
      (fun family ↦
        quittingDebtEdgeLoss (tail family time) (tail family (time + 1)))
      atTop (nhds 0))
    (time : ℕ) :
    quittingDebtEdgeLoss (limit time) (limit (time + 1)) = 0 := by
  have hpairs := tendsto_projective_adjacentPair tail limit subseq hlimit time
  have hlimitLoss := (continuous_quittingDebtEdgeLoss.tendsto
    (limit time, limit (time + 1))).comp hpairs
  have hzeroLoss := (hloss time).comp hsubseq.tendsto_atTop
  exact tendsto_nhds_unique hlimitLoss hzeroLoss

/-- If every fixed chronological edge has vanishing debt loss along the
extracted family, the projective limit consists entirely of zero-loss exact
edges. -/
theorem exists_projective_zeroLoss_quittingDebtTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (depth : ℕ → ℕ)
    (tail : ℕ → ℕ → QuittingDebtPoint ι)
    (hbox : ∀ family time, tail family time ∈ quittingDebtBox reward)
    (hedge : ∀ family time, time < depth family →
      IsQuittingDebtEdge reward (tail family time) (tail family (time + 1)))
    (hdepth : Tendsto depth atTop atTop)
    (hloss : ∀ time, Tendsto
      (fun family ↦
        quittingDebtEdgeLoss (tail family time) (tail family (time + 1)))
      atTop (nhds 0)) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
      Tendsto ((fun family ↦ tail family) ∘ subseq) atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      (∀ time,
        IsQuittingDebtEdge reward (limit time) (limit (time + 1))) ∧
      ∀ time,
        quittingDebtEdgeLoss (limit time) (limit (time + 1)) = 0 := by
  obtain ⟨limit, subseq, hsubseq, hlimit, hlimitBox⟩ :=
    exists_projective_quittingDebtTail_limit
      (reward := reward) (tail := tail) hbox
  have hedgeLimit : ∀ time,
      IsQuittingDebtEdge reward (limit time) (limit (time + 1)) := by
    intro time
    exact isQuittingDebtEdge_of_tendsto_edgeGraph
      (edge := (limit time, limit (time + 1)))
      (candidate := fun family ↦
        (tail (subseq family) time, tail (subseq family) (time + 1)))
      reward (tendsto_projective_adjacentPair tail limit subseq hlimit time)
      (eventually_projective_adjacentPair_mem_debtEdgeGraph
        reward depth tail hbox hedge hdepth subseq hsubseq time)
  have hzeroLimit : ∀ time,
      quittingDebtEdgeLoss (limit time) (limit (time + 1)) = 0 := by
    intro time
    exact quittingDebtEdgeLoss_eq_zero_of_projective_limit
      tail limit subseq hsubseq hlimit hloss time
  exact ⟨limit, subseq, hsubseq, hlimit, hlimitBox, hedgeLimit, hzeroLimit⟩

/-- Pointwise zero-loss support classification on a projective debt tail:
a positive successor debt coordinate forces every opponent of that owner to
Continue at the current root. -/
theorem projective_zeroLoss_debtTail_opponents_continue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (limit : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, limit time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDebtEdge reward (limit time) (limit (time + 1)))
    (hloss : ∀ time,
      quittingDebtEdgeLoss (limit time) (limit (time + 1)) = 0)
    (time : ℕ) (owner : ι) (hdebt : 0 < (limit (time + 1)).2 owner) :
    ∀ other, other ≠ owner →
      quittingRootOfSimplex (limit time).1.2 other = PMF.pure false := by
  intro other hne
  exact quittingRootOfSimplex_eq_pure_false_of_zeroDebtLoss_of_other
    reward (limit time) (limit (time + 1)) (hbox time) (hbox (time + 1))
      (hedge time) (hloss time) owner hdebt other hne

/-- Two positive debt coordinates on a zero-loss projective edge force its
current root to be all-Continue. -/
theorem projective_zeroLoss_debtTail_allContinue_of_two_debts
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (limit : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, limit time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDebtEdge reward (limit time) (limit (time + 1)))
    (hloss : ∀ time,
      quittingDebtEdgeLoss (limit time) (limit (time + 1)) = 0)
    (time : ℕ) (first second : ι) (hne : first ≠ second)
    (hfirst : 0 < (limit (time + 1)).2 first)
    (hsecond : 0 < (limit (time + 1)).2 second) :
    quittingRootOfSimplex (limit time).1.2 =
      (quittingAllContinueRoot : ι → PMF Bool) :=
  quittingRootOfSimplex_eq_allContinue_of_zeroDebtLoss_of_two_debts
    reward (limit time) (limit (time + 1)) (hbox time) (hbox (time + 1))
      (hedge time) (hloss time) first second hne hfirst hsecond

end GameTheory
