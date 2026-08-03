/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingFiniteDynamicDebtChains

/-!
# Compact optimization of exact finite-chain dynamic debt

This file turns the exact-D finite-chain criterion into an attained compact
optimization problem.  The exact Bellman debt depends continuously on the
finite Nash--Bellman path.  Hence both its aggregate sum and, for a nonempty
finite player set, its playerwise maximum attain minima on the nonempty
compact zero-boundary chain space.

The later monotonicity question is kept separate: attainment at each cutoff
does not make independently selected minimizers nested.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Continuous finite-path coordinates -/

/-- Simplex-valued version of the all-Continue extension of a finite path. -/
def quittingFiniteNashBellmanPathSimplexRoot
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (time : ℕ) : QuittingRootSimplex ι :=
  if htime : time < cutoff then
    (path ⟨time, Nat.lt_succ_of_lt htime⟩).2
  else
    fun _ ↦ stdSimplexEquiv (PMF.pure false)

omit [DecidableEq ι] in
/-- Converting the simplex extension back to PMFs gives the operational root
extension used by the finite-chain compiler. -/
theorem quittingRootOfSimplex_finiteNashBellmanPathSimplexRoot
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (time : ℕ) :
    quittingRootOfSimplex
        (quittingFiniteNashBellmanPathSimplexRoot cutoff path time) =
      quittingFiniteNashBellmanPathRoots cutoff path time := by
  unfold quittingFiniteNashBellmanPathSimplexRoot
    quittingFiniteNashBellmanPathRoots
  split_ifs
  · rfl
  · funext who
    exact (stdSimplexEquiv (α := Bool)).symm_apply_apply
      (PMF.pure false)

omit [DecidableEq ι] in
/-- A fixed displayed simplex root is continuous in the full finite path. -/
theorem continuous_quittingFiniteNashBellmanPathSimplexRoot
    (cutoff time : ℕ) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFiniteNashBellmanPathSimplexRoot cutoff path time) := by
  unfold quittingFiniteNashBellmanPathSimplexRoot
  split_ifs
  · fun_prop
  · exact continuous_const

omit [DecidableEq ι] in
/-- A fixed displayed scalar payoff coordinate is continuous in the full
finite path. -/
theorem continuous_quittingFiniteNashBellmanPathValue_apply
    (cutoff time : ℕ) (who : ι) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFiniteNashBellmanPathValue cutoff path time who) := by
  unfold quittingFiniteNashBellmanPathValue
  split_ifs
  · fun_prop
  · exact continuous_const

/-- A fixed operational opponent-Continue mass is continuous in the full
finite path. -/
theorem continuous_quittingFixedOpponentsContinueMass_finitePath
    (cutoff time : ℕ) (who : ι) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFixedOpponentsContinueMass
        (quittingFiniteNashBellmanPathRoots cutoff path) who time) := by
  have heq : (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFixedOpponentsContinueMass
        (quittingFiniteNashBellmanPathRoots cutoff path) who time) =
      fun path ↦ ∏ other ∈ (Finset.univ.erase who : Finset ι),
        quittingFiniteNashBellmanPathSimplexRoot cutoff path time
          other false := by
    funext path
    unfold quittingFixedOpponentsContinueMass
    rw [← quittingRootOfSimplex_finiteNashBellmanPathSimplexRoot]
    exact quittingFixedOpponentsContinueMass_quittingRootOfSimplex
      (quittingFiniteNashBellmanPathSimplexRoot cutoff path time) who
  rw [heq]
  apply continuous_finsetProd
  intro other _
  exact (continuous_apply false).comp
    (continuous_subtype_val.comp
      ((continuous_apply other).comp
        (continuous_quittingFiniteNashBellmanPathSimplexRoot cutoff time)))

/-! ## Continuous exact Bellman recursion -/

/-- One finite dynamic-debt step written with the two root endpoints. -/
theorem quittingFiniteDynamicDebt_succ_eq_endpoints
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (prescribed : ℕ → ℝ) (terminalDebt : ℝ)
    (start fuel : ℕ) :
    quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start (fuel + 1) =
      max
          (quittingRootQuitPayoff reward
            (fun _ ↦ prescribed (start + 1)) (roots start) who)
          (quittingRootContinuePayoff reward
              (fun _ ↦ prescribed (start + 1)) (roots start) who +
            quittingFixedOpponentsContinueMass roots who start *
              quittingFiniteDynamicDebt reward roots who prescribed
                terminalDebt (start + 1) fuel) -
        prescribed start := by
  rw [quittingFiniteDynamicDebt_succ]
  have hquit := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
    reward roots who (fun _ ↦ prescribed (start + 1)) start
  have hcontinue := quittingRootContinuePayoff_eq_fixedOpponents
    reward roots who (fun _ ↦ prescribed (start + 1)) start
  rw [hquit, hcontinue]
  ring_nf

set_option maxHeartbeats 800000 in
-- Recursive composition through the finite simplex path is elaboration-heavy.
/-- Exact finite dynamic debt is continuous in every displayed coordinate of
the underlying finite path. -/
theorem continuous_quittingFiniteDynamicDebt_finitePath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (who : ι) (terminalDebt : ℝ)
    (start fuel : ℕ) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFiniteDynamicDebt reward
        (quittingFiniteNashBellmanPathRoots cutoff path) who
        (fun time ↦
          quittingFiniteNashBellmanPathValue cutoff path time who)
        terminalDebt start fuel) := by
  induction fuel generalizing start with
  | zero =>
      simpa only [quittingFiniteDynamicDebt_zero] using
        (continuous_const : Continuous
          (fun _ : QuittingFiniteNashBellmanPath ι cutoff ↦ terminalDebt))
  | succ fuel ih =>
      let simplex := fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
        quittingFiniteNashBellmanPathSimplexRoot cutoff path start
      let scalarTail := fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
        quittingFiniteNashBellmanPathValue cutoff path (start + 1) who
      let endpointData := fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
        ((fun _ : ι ↦ scalarTail path), simplex path)
      have hscalarTail : Continuous scalarTail := by
        exact continuous_quittingFiniteNashBellmanPathValue_apply
          cutoff (start + 1) who
      have hsimplex : Continuous simplex := by
        exact continuous_quittingFiniteNashBellmanPathSimplexRoot cutoff start
      have hendpointData : Continuous endpointData := by
        dsimp only [endpointData]
        exact (continuous_pi fun _ ↦ hscalarTail).prodMk hsimplex
      have hquitRaw : Continuous
          (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
            quittingRootQuitPayoff reward (endpointData path).1
              (quittingRootOfSimplex (endpointData path).2) who) :=
        (continuous_quittingRootQuitPayoff_simplex reward who).comp
          hendpointData
      have hquit : Continuous
          (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
            quittingRootQuitPayoff reward (fun _ ↦ scalarTail path)
              (quittingRootOfSimplex (simplex path)) who) := by
        simpa only [endpointData] using hquitRaw
      have hcontinueRaw : Continuous
          (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
            quittingRootContinuePayoff reward (endpointData path).1
              (quittingRootOfSimplex (endpointData path).2) who) :=
        (continuous_quittingRootContinuePayoff_simplex reward who).comp
          hendpointData
      have hcontinue : Continuous
          (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
            quittingRootContinuePayoff reward (fun _ ↦ scalarTail path)
              (quittingRootOfSimplex (simplex path)) who) := by
        simpa only [endpointData] using hcontinueRaw
      have hmass :=
        continuous_quittingFixedOpponentsContinueMass_finitePath
          cutoff start who
      have hnext := ih (start + 1)
      have hcurrent :=
        continuous_quittingFiniteNashBellmanPathValue_apply cutoff start who
      have hformula : (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
          quittingFiniteDynamicDebt reward
            (quittingFiniteNashBellmanPathRoots cutoff path) who
            (fun time ↦
              quittingFiniteNashBellmanPathValue cutoff path time who)
            terminalDebt start (fuel + 1)) =
          fun path ↦
            max
                (quittingRootQuitPayoff reward (fun _ ↦ scalarTail path)
                  (quittingRootOfSimplex (simplex path)) who)
                (quittingRootContinuePayoff reward (fun _ ↦ scalarTail path)
                    (quittingRootOfSimplex (simplex path)) who +
                  quittingFixedOpponentsContinueMass
                      (quittingFiniteNashBellmanPathRoots cutoff path)
                      who start *
                    quittingFiniteDynamicDebt reward
                      (quittingFiniteNashBellmanPathRoots cutoff path) who
                      (fun time ↦
                        quittingFiniteNashBellmanPathValue
                          cutoff path time who)
                      terminalDebt (start + 1) fuel) -
              quittingFiniteNashBellmanPathValue cutoff path start who := by
        funext path
        rw [quittingFiniteDynamicDebt_succ_eq_endpoints]
        rw [← quittingRootOfSimplex_finiteNashBellmanPathSimplexRoot]
      rw [hformula]
      exact (hquit.max (hcontinue.add (hmass.mul hnext))).sub hcurrent

/-- Every playerwise initial exact-D objective is continuous. -/
theorem continuous_quittingFiniteNashBellmanPathDynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (who : ι) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFiniteNashBellmanPathDynamicDebt
        reward cutoff path who 0) := by
  simpa only [quittingFiniteNashBellmanPathDynamicDebt, Nat.sub_zero] using
    continuous_quittingFiniteDynamicDebt_finitePath reward cutoff who
      (quittingPositiveSingletonDebtCap reward who) 0 cutoff

/-- The aggregate initial exact-D objective is continuous. -/
theorem continuous_quittingFiniteNashBellmanPathAggregateDynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward cutoff path) := by
  unfold quittingFiniteNashBellmanPathAggregateDynamicDebt
  exact continuous_finsetSum Finset.univ fun who _ ↦
    continuous_quittingFiniteNashBellmanPathDynamicDebt reward cutoff who

/-! ## Attained aggregate objective -/

/-- At each cutoff, aggregate exact dynamic debt attains a minimum over the
compact nonempty zero-boundary exact Nash--Bellman chain space. -/
theorem exists_quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    ∃ path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff,
      IsMinOn
        (quittingFiniteNashBellmanPathAggregateDynamicDebt reward cutoff)
        (quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) path := by
  exact
    (quittingFiniteZeroBoundaryNashBellmanChainSet_isCompact
      reward cutoff).exists_isMinOn
      (quittingFiniteZeroBoundaryNashBellmanChainSet_nonempty reward cutoff)
      (continuous_quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward cutoff).continuousOn

/-- A zero-boundary exact chain minimizing aggregate exact dynamic debt at
one fixed cutoff. -/
def quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) : QuittingFiniteNashBellmanPath ι cutoff :=
  Classical.choose
    (exists_quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
      reward cutoff)

/-- The attained minimum aggregate exact dynamic debt at one cutoff. -/
def quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) : ℝ :=
  quittingFiniteNashBellmanPathAggregateDynamicDebt reward cutoff
    (quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer reward cutoff)

/-- The selected aggregate exact-D minimizer is admissible. -/
theorem quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer reward cutoff ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
  (Classical.choose_spec
    (exists_quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
      reward cutoff)).1

/-- The attained aggregate exact-D value is below every admissible
competitor at the same cutoff. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff ≤
      quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward cutoff path := by
  exact (Classical.choose_spec
    (exists_quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer
      reward cutoff)).2 hpath

/-- The attained minimum aggregate exact dynamic debt is nonnegative. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    0 ≤ quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff :=
  quittingFiniteNashBellmanPathAggregateDynamicDebt_nonneg reward cutoff _
    (quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer_mem
      reward cutoff)

/-! ## Attained playerwise maximum objective -/

/-- The largest initial exact dynamic debt among the finitely many players.
The nonempty-player assumption prevents an artificial default value. -/
def quittingFiniteNashBellmanPathMaxDynamicDebt [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun who ↦
    quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0

/-- The playerwise maximum exact-D objective is continuous. -/
theorem continuous_quittingFiniteNashBellmanPathMaxDynamicDebt [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFiniteNashBellmanPathMaxDynamicDebt
        reward cutoff path) := by
  unfold quittingFiniteNashBellmanPathMaxDynamicDebt
  exact Continuous.finset_sup'_apply Finset.univ_nonempty fun who _ ↦
    continuous_quittingFiniteNashBellmanPathDynamicDebt reward cutoff who

/-- Every player's initial exact dynamic debt is below the literal maximum. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_le_max [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (who : ι) :
    quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who 0 ≤
      quittingFiniteNashBellmanPathMaxDynamicDebt reward cutoff path := by
  exact Finset.le_sup'
    (fun player ↦
      quittingFiniteNashBellmanPathDynamicDebt
        reward cutoff path player 0)
    (Finset.mem_univ who)

/-- The playerwise maximum exact dynamic debt is nonnegative on every
admissible chain. -/
theorem quittingFiniteNashBellmanPathMaxDynamicDebt_nonneg [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    0 ≤ quittingFiniteNashBellmanPathMaxDynamicDebt
      reward cutoff path := by
  let who : ι := Classical.choice inferInstance
  exact (quittingFiniteNashBellmanPathDynamicDebt_nonneg
      reward cutoff path hpath who 0).trans
    (quittingFiniteNashBellmanPathDynamicDebt_le_max
      reward cutoff path who)

/-- The literal maximum is below the nonnegative aggregate objective. -/
theorem quittingFiniteNashBellmanPathMaxDynamicDebt_le_aggregate
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteNashBellmanPathMaxDynamicDebt reward cutoff path ≤
      quittingFiniteNashBellmanPathAggregateDynamicDebt
        reward cutoff path := by
  unfold quittingFiniteNashBellmanPathMaxDynamicDebt
  exact Finset.sup'_le Finset.univ_nonempty _ fun who _ ↦
    quittingFiniteNashBellmanPathDynamicDebt_le_aggregate
      reward cutoff path hpath who

/-- At each cutoff, the literal maximum exact dynamic debt attains a minimum
over the compact nonempty chain space. -/
theorem exists_quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    ∃ path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff,
      IsMinOn
        (quittingFiniteNashBellmanPathMaxDynamicDebt reward cutoff)
        (quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) path := by
  exact
    (quittingFiniteZeroBoundaryNashBellmanChainSet_isCompact
      reward cutoff).exists_isMinOn
      (quittingFiniteZeroBoundaryNashBellmanChainSet_nonempty reward cutoff)
      (continuous_quittingFiniteNashBellmanPathMaxDynamicDebt
        reward cutoff).continuousOn

/-- A zero-boundary exact chain minimizing the largest player's exact debt
at one fixed cutoff. -/
def quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) : QuittingFiniteNashBellmanPath ι cutoff :=
  Classical.choose
    (exists_quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
      reward cutoff)

/-- The attained minimum, over chains, of the largest playerwise exact debt. -/
def quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) : ℝ :=
  quittingFiniteNashBellmanPathMaxDynamicDebt reward cutoff
    (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
      reward cutoff)

/-- The selected max-exact-D minimizer is admissible. -/
theorem quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer reward cutoff ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
  (Classical.choose_spec
    (exists_quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
      reward cutoff)).1

/-- The attained min-max exact-D value is below every admissible competitor
at the same cutoff. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_le
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff ≤
      quittingFiniteNashBellmanPathMaxDynamicDebt reward cutoff path := by
  exact (Classical.choose_spec
    (exists_quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
      reward cutoff)).2 hpath

/-- The attained min-max exact dynamic debt is nonnegative. -/
theorem quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_nonneg
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    0 ≤ quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
      reward cutoff :=
  quittingFiniteNashBellmanPathMaxDynamicDebt_nonneg reward cutoff _
    (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward cutoff)

/-! ## Vanishing-minimum criteria -/

/-- If the infimum over cutoffs of the attained minimum aggregate exact debt
is zero, the quitting game has a uniform-equilibrium payoff. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_iInf_finiteMinDynamicDebt_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hmin : (⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt
        reward cutoff) = 0) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply
    quittingGame_exists_uniformEquilibriumPayoff_of_finiteNashBellmanPathDynamicDebt
      reward
  intro ε hε
  have hinf : (⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinDynamicDebt reward cutoff) <
        ε := by
    rw [hmin]
    exact hε
  obtain ⟨cutoff, hcutoff⟩ := exists_lt_of_ciInf_lt hinf
  exact ⟨cutoff,
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer reward cutoff,
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer_mem
      reward cutoff,
    hcutoff.le⟩

/-- The literal positive answer to the finite-chain optimization question:
if the infimum over cutoffs of the attained minimum playerwise maximum exact
debt is zero, the quitting game has a uniform-equilibrium payoff.  No
converse or universal vanishing assertion is made here. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_iInf_finiteMinMaxDynamicDebt_eq_zero
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hmin : (⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt
        reward cutoff) = 0) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_finiteDynamicDebtChains
    reward
  intro ε hε
  have hinf : (⨅ cutoff : ℕ,
      quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt reward cutoff) <
        ε := by
    rw [hmin]
    exact hε
  obtain ⟨cutoff, hcutoff⟩ := exists_lt_of_ciInf_lt hinf
  let path :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer reward cutoff
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward cutoff
  refine ⟨quittingFiniteNashBellmanPathRoots cutoff path,
    quittingFiniteNashBellmanPathValue cutoff path, cutoff,
    quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
      cutoff path,
    quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
      reward cutoff path hpath,
    quittingFiniteNashBellmanPathValue_eq_successor
      reward cutoff path hpath, ?_⟩
  intro who
  exact (quittingFiniteNashBellmanPathDynamicDebt_le_max
      reward cutoff path who).trans hcutoff.le

end GameTheory
