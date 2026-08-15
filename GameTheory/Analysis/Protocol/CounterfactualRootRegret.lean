/-
# Finite local CFR bounds control root deviations

This module combines the D46 local regret-matching processes through the
finite aggregation theorem. Its semantic premise is a D48
scalar root-gain decomposition or upper decomposition for a family of
deviations; bounded common-depth topological chains supply that premise. No
second runner or regret semantics is introduced here.
-/

import GameTheory.Analysis.Protocol.CounterfactualDecomposition
import GameTheory.Analysis.Protocol.CounterfactualRegretMatching
import GameTheory.Math.RegretAggregation

noncomputable section

namespace GameTheory.Protocol

open Filter GameTheory GameTheory.Math.Probability Protocol
open GameTheory.Analysis.Approachability
open GameTheory.Math.Approachability GameTheory.Math.OrthantProjection
open GameTheory.Math.RegretAggregation

universe uι us ua up uq uk uv

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}
variable (M : InformationModel.{uι, us, ua, up, uq, uk} E)

namespace InformationModel

/-- The actual running average of local D45 action-regret vectors generated
when regret matching selects the current law. -/
def counterfactualRegretMatchAverage
    {Q : Type uv}
    [Fintype ι] [DecidableEq ι]
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    [Fintype (M.Choice who site.1)] [Nonempty (M.Choice who site.1)]
    (strategyOf : FinDist (M.Choice who site.1) → Q →
      (player : ι) → M.BehavioralPolicy player)
    (payoffOf : Q → E.History → ℝ) (fuel : ℕ)
    (environment : ℕ → Q) (t : ℕ) :
    EuclideanSpace ℝ (M.Choice who site.1) :=
  avgVec
    (fun law current => localCounterfactualRegretVector M
      (strategyOf law current) who site (payoffOf current) fuel)
    regretMatch environment t

/-- The named local average is exactly the Cesaro sum of the instantaneous
counterfactual-regret vectors played by its regret matcher. -/
theorem counterfactualRegretMatchAverage_smul_eq_sum
    {Q : Type uv}
    [Fintype ι] [DecidableEq ι]
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : M.InformationSite who)
    [Fintype (M.InformationHistory who site.1)]
    [Fintype (M.Choice who site.1)] [Nonempty (M.Choice who site.1)]
    (strategyOf : FinDist (M.Choice who site.1) → Q →
      (player : ι) → M.BehavioralPolicy player)
    (payoffOf : Q → E.History → ℝ) (fuel : ℕ)
    (environment : ℕ → Q) (t : ℕ) :
    (t : ℝ) • counterfactualRegretMatchAverage M who site strategyOf
        payoffOf fuel environment t =
      ∑ round ∈ Finset.range t,
        localCounterfactualRegretVector M
          (strategyOf
            (regretMatch
              (counterfactualRegretMatchAverage M who site strategyOf
                payoffOf fuel environment round))
            (environment round))
          who site (payoffOf (environment round)) fuel := by
  exact avgVec_smul_eq_sum
    (fun law current => localCounterfactualRegretVector M
      (strategyOf law current) who site (payoffOf current) fuel)
    regretMatch environment t

/-- **Finite root-regret aggregation.** If an actual scalar root gain at every
round is the D48 weighted sum of the local regret-matching vectors, then its
positive average is bounded by the sum of the local orthant distances. -/
theorem counterfactualRegretMatches_positiveRootGain_le
    {Site : Type*} [Fintype Site]
    (Q : Site → Type uv)
    [Fintype ι] [DecidableEq ι]
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : Site → M.InformationSite who)
    [∀ key, Fintype (M.InformationHistory who (site key).1)]
    [∀ key, Fintype (M.Choice who (site key).1)]
    [∀ key, Nonempty (M.Choice who (site key).1)]
    (strategyOf : ∀ key,
      FinDist (M.Choice who (site key).1) → Q key →
        (player : ι) → M.BehavioralPolicy player)
    (payoffOf : ∀ key, Q key → E.History → ℝ)
    (fuel : Site → ℕ) (environment : ∀ key, ℕ → Q key)
    (gain : ℕ → ℝ) (reach : Site → ℝ)
    (hreach : ∀ key, reach key ∈ Set.Icc 0 1)
    (deviation : ∀ key, M.Choice who (site key).1)
    (hgain : ∀ round,
      gain round = ∑ key,
        reach key *
          (localCounterfactualRegretVector M
            (strategyOf key
              (regretMatch
                (counterfactualRegretMatchAverage M who (site key)
                  (strategyOf key) (payoffOf key) (fuel key)
                  (environment key) round))
              (environment key round))
            who (site key) (payoffOf key (environment key round))
              (fuel key)).ofLp (deviation key))
    (t : ℕ) (ht : 0 < t) :
    max ((∑ round ∈ Finset.range t, gain round) / (t : ℝ)) 0 ≤
      ∑ key, Metric.infDist
        (counterfactualRegretMatchAverage M who (site key)
          (strategyOf key) (payoffOf key) (fuel key)
          (environment key) t)
        nonposOrthant := by
  apply positiveAverageGain_le_sum_infDist
    (fun round key => localCounterfactualRegretVector M
      (strategyOf key
        (regretMatch
          (counterfactualRegretMatchAverage M who (site key)
            (strategyOf key) (payoffOf key) (fuel key)
            (environment key) round))
        (environment key round))
      who (site key) (payoffOf key (environment key round)) (fuel key))
    (fun key => counterfactualRegretMatchAverage M who (site key)
      (strategyOf key) (payoffOf key) (fuel key) (environment key) t)
    gain reach hreach deviation t ht
  · intro key
    exact counterfactualRegretMatchAverage_smul_eq_sum M who (site key)
      (strategyOf key) (payoffOf key) (fuel key) (environment key) t
  · intro round _
    exact hgain round

/-- **Uniform finite-deviation root-regret aggregation.** One collection of
local regret matchers controls every deviation in a family when each
deviation's scalar gain is upper-bounded by selected coordinates of those
same local vectors.  Reach weights and selected actions may depend on the
deviation, but the orthant-distance bound does not. -/
theorem counterfactualRegretMatches_positiveRootGains_le
    {Site : Type*} [Fintype Site]
    {Deviation : Type*}
    (Q : Site → Type uv)
    [Fintype ι] [DecidableEq ι]
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : Site → M.InformationSite who)
    [∀ key, Fintype (M.InformationHistory who (site key).1)]
    [∀ key, Fintype (M.Choice who (site key).1)]
    [∀ key, Nonempty (M.Choice who (site key).1)]
    (strategyOf : ∀ key,
      FinDist (M.Choice who (site key).1) → Q key →
        (player : ι) → M.BehavioralPolicy player)
    (payoffOf : ∀ key, Q key → E.History → ℝ)
    (fuel : Site → ℕ) (environment : ∀ key, ℕ → Q key)
    (gain : Deviation → ℕ → ℝ)
    (reach : Deviation → Site → ℝ)
    (hreach : ∀ deviation key, reach deviation key ∈ Set.Icc 0 1)
    (choice : Deviation → ∀ key, M.Choice who (site key).1)
    (hgain : ∀ deviation, ∀ round,
      gain deviation round ≤ ∑ key,
        reach deviation key *
          (localCounterfactualRegretVector M
            (strategyOf key
              (regretMatch
                (counterfactualRegretMatchAverage M who (site key)
                  (strategyOf key) (payoffOf key) (fuel key)
                  (environment key) round))
              (environment key round))
            who (site key) (payoffOf key (environment key round))
              (fuel key)).ofLp (choice deviation key))
    (t : ℕ) (ht : 0 < t) :
    ∀ deviation,
      max ((∑ round ∈ Finset.range t, gain deviation round) / (t : ℝ)) 0 ≤
        ∑ key, Metric.infDist
          (counterfactualRegretMatchAverage M who (site key)
            (strategyOf key) (payoffOf key) (fuel key)
            (environment key) t)
          nonposOrthant := by
  apply positiveAverageGains_le_sum_infDist
    (fun round key => localCounterfactualRegretVector M
      (strategyOf key
        (regretMatch
          (counterfactualRegretMatchAverage M who (site key)
            (strategyOf key) (payoffOf key) (fuel key)
            (environment key) round))
        (environment key round))
      who (site key) (payoffOf key (environment key round)) (fuel key))
    (fun key => counterfactualRegretMatchAverage M who (site key)
      (strategyOf key) (payoffOf key) (fuel key) (environment key) t)
    gain reach hreach choice t ht
  · intro key
    exact counterfactualRegretMatchAverage_smul_eq_sum M who (site key)
      (strategyOf key) (payoffOf key) (fuel key) (environment key) t
  · intro deviation round _
    exact hgain deviation round

/-- If every local D46 process approaches its orthant, the uniform finite
deviation bound gives vanishing positive average root gain for every deviation.
The convergence is derived from the local processes, not accepted as a root
premise. -/
theorem counterfactualRegretMatches_positiveRootGains_tendsto_zero
    {Site : Type*} [Fintype Site]
    {Deviation : Type*}
    (Q : Site → Type uv)
    [Fintype ι] [DecidableEq ι]
    (who : ι) [DecidableEq (M.InfoState who)]
    (site : Site → M.InformationSite who)
    [∀ key, Fintype (M.InformationHistory who (site key).1)]
    [∀ key, Fintype (M.Choice who (site key).1)]
    [∀ key, Nonempty (M.Choice who (site key).1)]
    (strategyOf : ∀ key,
      FinDist (M.Choice who (site key).1) → Q key →
        (player : ι) → M.BehavioralPolicy player)
    (payoffOf : ∀ key, Q key → E.History → ℝ)
    (fuel : Site → ℕ) (environment : ∀ key, ℕ → Q key)
    (gain : Deviation → ℕ → ℝ)
    (reach : Deviation → Site → ℝ)
    (hreach : ∀ deviation key, reach deviation key ∈ Set.Icc 0 1)
    (choice : Deviation → ∀ key, M.Choice who (site key).1)
    (hgain : ∀ deviation, ∀ round,
      gain deviation round ≤ ∑ key,
        reach deviation key *
          (localCounterfactualRegretVector M
            (strategyOf key
              (regretMatch
                (counterfactualRegretMatchAverage M who (site key)
                  (strategyOf key) (payoffOf key) (fuel key)
                  (environment key) round))
              (environment key round))
            who (site key) (payoffOf key (environment key round))
              (fuel key)).ofLp (choice deviation key))
    (hlocal : ∀ key,
      Tendsto
        (fun t => Metric.infDist
          (counterfactualRegretMatchAverage M who (site key)
            (strategyOf key) (payoffOf key) (fuel key)
            (environment key) t)
          nonposOrthant)
        atTop (nhds 0)) :
    ∀ deviation,
      Tendsto
        (fun t => max
          ((∑ round ∈ Finset.range t, gain deviation round) / (t : ℝ)) 0)
        atTop (nhds 0) := by
  apply positiveAverageGains_tendsto_zero
    (fun round key => localCounterfactualRegretVector M
      (strategyOf key
        (regretMatch
          (counterfactualRegretMatchAverage M who (site key)
            (strategyOf key) (payoffOf key) (fuel key)
            (environment key) round))
        (environment key round))
      who (site key) (payoffOf key (environment key round)) (fuel key))
    (fun key t => counterfactualRegretMatchAverage M who (site key)
      (strategyOf key) (payoffOf key) (fuel key) (environment key) t)
    gain reach hreach choice
  · intro key t
    exact counterfactualRegretMatchAverage_smul_eq_sum M who (site key)
      (strategyOf key) (payoffOf key) (fuel key) (environment key) t
  · exact hgain
  · exact hlocal

end InformationModel

end GameTheory.Protocol
