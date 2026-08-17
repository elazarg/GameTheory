/-
# EXP-113: coherence of the canonical infinite stochastic path

The transition kernel was built from support-preserving one-step laws.  This
file records the resulting pathwise coherence seam without introducing a
second runner.
-/

import GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure

open MeasureTheory ProbabilityTheory
open GameTheory.Math.Probability
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Stochastic

universe uι us ua

namespace Game

variable {ι : Type uι} (G : Stochastic.Game.{uι, us, ua} ι)
variable [Fintype ι]
variable (initial : G.State) [∀ i, Nonempty (G.Action i)]
variable (profile : G.BehaviorProfile initial)

private theorem pathStepLaw_support_coherent
    (n : ℕ) (history : PathHistory G initial n)
    {result : PathHistory G initial (n + 1)}
    (hresult : result ∈ (pathStepLaw G initial profile n history).support) :
    ∃ (joint : ∀ i, Option (G.Action i))
      (isLegal : (G.toExecution initial).Legal history.1.state joint)
      (realized : result.1.state ∈
        ((G.toExecution initial).step history.1.state ⟨joint, isLegal⟩).support),
      result.1 = history.1.extend isLegal realized := by
  unfold pathStepLaw at hresult
  rw [FinDist.support_bindOnSupport] at hresult
  obtain ⟨outcome, houtcome, hresult⟩ := Set.mem_iUnion₂.mp hresult
  have heq := FinDist.mem_support_pure.mp hresult
  subst result
  have hbehavior : outcome ∈
      ((G.perfectMonitoring initial).runBehavioralFrom profile 1 history.1).support :=
    houtcome
  rw [(G.perfectMonitoring initial).runBehavioralFrom_succ_of_not_terminal
    profile 0 (by simp)] at hbehavior
  rw [FinDist.support_bind] at hbehavior
  obtain ⟨draw, hdraw, hbehavior⟩ := Set.mem_iUnion₂.mp hbehavior
  rw [FinDist.support_bindOnSupport] at hbehavior
  obtain ⟨target, realized, hbehavior⟩ := Set.mem_iUnion₂.mp hbehavior
  rw [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_zero] at hbehavior
  rw [FinDist.mem_support_pure] at hbehavior
  subst outcome
  exact ⟨draw.1, draw.2, realized, rfl⟩

private theorem trajectoryKernel_ae_support
    [Countable (CanonicalHistory G initial)] (n : ℕ)
    (historyPrefix : ∀ i : Finset.Iic n, PathHistory G initial i) :
    ∀ᵐ result ∂trajectoryKernel G initial profile n historyPrefix,
      result ∈ (pathStepLaw G initial profile n
        (lastPathHistory G initial n historyPrefix)).support := by
  apply (ae_iff_prob_eq_one Measurable.of_discrete).2
  unfold trajectoryKernel
  rw [Kernel.comp_apply, Kernel.deterministic_apply]
  rw [Measure.dirac_bind (Kernel.measurable _)]
  have hmeasure :
      (pathStepLaw G initial profile n
        (lastPathHistory G initial n historyPrefix)).toPMF.toMeasure
          {a | a ∈ (pathStepLaw G initial profile n
            (lastPathHistory G initial n historyPrefix)).support} = 1 := by
    rw [PMF.toMeasure_apply_eq_one_iff
      (pathStepLaw G initial profile n
        (lastPathHistory G initial n historyPrefix)).toPMF
      MeasurableSet.of_discrete]
    exact Set.Subset.rfl
  exact hmeasure

theorem ae_pathStepLaw_support
    [Countable (CanonicalHistory G initial)] (n : ℕ) :
    ∀ᵐ play ∂infinitePlayMeasure G initial profile,
      play (n + 1) ∈
        (pathStepLaw G initial profile n (play n)).support := by
  let restrict := Preorder.frestrictLe
    (π := fun k : ℕ => PathHistory G initial k) n
  let pairMap := fun play : ∀ k, PathHistory G initial k =>
    (restrict play, play (n + 1))
  have hpair := Kernel.partialTraj_compProd_eq_map_traj
    (X := fun k => PathHistory G initial k)
    (κ := trajectoryKernel G initial profile) (a := 0) (b := n)
    (x₀ := initialPathPrefix G initial) (Nat.zero_le n)
  have hinner : ∀ᵐ historyPrefix ∂Kernel.partialTraj
      (trajectoryKernel G initial profile) 0 n (initialPathPrefix G initial),
      ∀ᵐ result ∂trajectoryKernel G initial profile n historyPrefix,
        result ∈ (pathStepLaw G initial profile n
          (lastPathHistory G initial n historyPrefix)).support :=
    Filter.Eventually.of_forall (trajectoryKernel_ae_support G initial profile n)
  have hpair' : ∀ᵐ pair ∂((Kernel.partialTraj
      (trajectoryKernel G initial profile) 0 n (initialPathPrefix G initial)) ⊗ₘ
        (trajectoryKernel G initial profile n)),
      pair.2 ∈ (pathStepLaw G initial profile n
        (lastPathHistory G initial n pair.1)).support := by
    exact Measure.ae_compProd_of_ae_ae MeasurableSet.of_discrete hinner
  rw [hpair] at hpair'
  have hpairMap : Measurable pairMap := by
    fun_prop
  have hresult := ae_of_ae_map
    hpairMap.aemeasurable hpair'
  simpa [infinitePlayMeasure, pairMap, restrict, lastPathHistory] using hresult

theorem ae_all_pathStepLaw_support
    [Countable (CanonicalHistory G initial)] :
    ∀ᵐ play ∂infinitePlayMeasure G initial profile, ∀ n : ℕ,
      play (n + 1) ∈
        (pathStepLaw G initial profile n (play n)).support :=
  ae_all_iff.2 (fun n => ae_pathStepLaw_support G initial profile n)

theorem ae_all_path_coherent
    [Countable (CanonicalHistory G initial)] :
    ∀ᵐ play ∂infinitePlayMeasure G initial profile, ∀ n : ℕ,
      ∃ (joint : ∀ i, Option (G.Action i))
        (isLegal : (G.toExecution initial).Legal (play n).1.state joint)
        (realized : (play (n + 1)).1.state ∈
          ((G.toExecution initial).step (play n).1.state ⟨joint, isLegal⟩).support),
        (play (n + 1)).1 = (play n).1.extend isLegal realized := by
  filter_upwards [ae_all_pathStepLaw_support G initial profile] with play hplay
  intro n
  exact pathStepLaw_support_coherent G initial profile n (play n) (hplay n)

end Game

end GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure
