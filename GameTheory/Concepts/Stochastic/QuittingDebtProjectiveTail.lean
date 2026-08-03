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

/-- Coordinatewise continuity of total debt-edge loss. -/
theorem continuous_quittingDebtEdgeLoss :
    Continuous (fun edge : QuittingDebtPoint ι × QuittingDebtPoint ι ↦
      quittingDebtEdgeLoss edge.1 edge.2) := by
  unfold quittingDebtEdgeLoss quittingDebtCoordinateLoss
  fun_prop

set_option maxHeartbeats 800000 in
/-- Genuine residual-horizon escape extracts one projectively compatible
infinite tail from actual finite exact debt tails.

`tail family time` is understood as a rooted finite suffix, padded after
`depth family`; only edges strictly before that residual depth are assumed to
be actual.  Convergence is in the product topology, hence coordinatewise. -/
theorem exists_projective_quittingDebtTail_of_residualDepth_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (depth : ℕ → ℕ)
    (tail : ℕ → ℕ → QuittingDebtPoint ι)
    (hbox : ∀ family time, tail family time ∈ quittingDebtBox reward)
    (hedge : ∀ family time, time < depth family →
      IsQuittingDebtEdge reward (tail family time) (tail family (time + 1)))
    (hdepth : Tendsto depth atTop atTop) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
      Tendsto ((fun family ↦ tail family) ∘ subseq) atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      ∀ time,
        IsQuittingDebtEdge reward (limit time) (limit (time + 1)) := by
  let pathBox : Set (ℕ → QuittingDebtPoint ι) :=
    {path | ∀ time, path time ∈ quittingDebtBox reward}
  have hpathBoxCompact : IsCompact pathBox := by
    dsimp only [pathBox]
    exact isCompact_pi_infinite fun _ ↦ quittingDebtBox_isCompact reward
  have htailMem : ∀ family, (fun time ↦ tail family time) ∈ pathBox :=
    fun family time ↦ hbox family time
  obtain ⟨limit, hlimitBox, subseq, hsubseq, hlimit⟩ :=
    hpathBoxCompact.tendsto_subseq htailMem
  refine ⟨limit, subseq, hsubseq, hlimit, hlimitBox, ?_⟩
  intro time
  have hdepthSubseq : Tendsto (depth ∘ subseq) atTop atTop :=
    hdepth.comp hsubseq.tendsto_atTop
  have hcurrent : Tendsto (fun family ↦ tail (subseq family) time)
      atTop (nhds (limit time)) := by
    exact ((continuous_apply time).tendsto limit).comp hlimit
  have hsuccessor : Tendsto (fun family ↦ tail (subseq family) (time + 1))
      atTop (nhds (limit (time + 1))) := by
    exact ((continuous_apply (time + 1)).tendsto limit).comp hlimit
  have hpairs : Tendsto
      (fun family ↦
        (tail (subseq family) time, tail (subseq family) (time + 1)))
      atTop (nhds (limit time, limit (time + 1))) :=
    hcurrent.prodMk_nhds hsuccessor
  have heventually : ∀ᶠ family in atTop,
      (tail (subseq family) time, tail (subseq family) (time + 1)) ∈
        quittingDebtEdgeGraph reward := by
    filter_upwards [tendsto_atTop.1 hdepthSubseq (time + 1)] with family hfamily
    change time + 1 ≤ depth (subseq family) at hfamily
    exact ⟨hbox (subseq family) time, hbox (subseq family) (time + 1),
      hedge (subseq family) time (by omega)⟩
  exact ((isClosed_quittingDebtEdgeGraph reward).mem_of_tendsto
    hpairs heventually).2.2

set_option maxHeartbeats 800000 in
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
  obtain ⟨limit, subseq, hsubseq, hlimit, hlimitBox, hedgeLimit⟩ :=
    exists_projective_quittingDebtTail_of_residualDepth_tendsto
      reward depth tail hbox hedge hdepth
  refine ⟨limit, subseq, hsubseq, hlimit, hlimitBox, hedgeLimit, ?_⟩
  intro time
  have hcurrent : Tendsto (fun family ↦ tail (subseq family) time)
      atTop (nhds (limit time)) :=
    ((continuous_apply time).tendsto limit).comp hlimit
  have hsuccessor : Tendsto (fun family ↦ tail (subseq family) (time + 1))
      atTop (nhds (limit (time + 1))) :=
    ((continuous_apply (time + 1)).tendsto limit).comp hlimit
  have hpairs : Tendsto
      (fun family ↦
        (tail (subseq family) time, tail (subseq family) (time + 1)))
      atTop (nhds (limit time, limit (time + 1))) :=
    hcurrent.prodMk_nhds hsuccessor
  have hlimitLoss : Tendsto
      (fun family ↦
        quittingDebtEdgeLoss (tail (subseq family) time)
          (tail (subseq family) (time + 1)))
      atTop
      (nhds (quittingDebtEdgeLoss (limit time) (limit (time + 1)))) :=
    (continuous_quittingDebtEdgeLoss.tendsto
      (limit time, limit (time + 1))).comp hpairs
  have hzeroLoss := (hloss time).comp hsubseq.tendsto_atTop
  exact tendsto_nhds_unique hlimitLoss hzeroLoss

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
