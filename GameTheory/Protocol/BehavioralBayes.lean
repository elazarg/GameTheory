/-
# Bayesian consistency at information sites

This leaf derives event mass and normalized beliefs from the canonical
behavioral assessment and history runner.
-/

import GameTheory.Protocol.HistoryEvents

noncomputable section

namespace GameTheory.Protocol

open GameTheory GameTheory.Math.Probability
open scoped ENNReal

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace InformationModel

variable (M : InformationModel E)
section Bayes

variable [Fintype ι]

/-- The atomic occupancy mass of a decision information fiber. The
history-antichain premise in the Bayes theorem below is what makes this tsum
the mass of a disjoint first-arrival event rather than a repeated occupancy
count. No finite history or action carrier is assumed. -/
def informationMass
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (i : ι) (site : M.InformationSite i) : ℝ≥0∞ :=
  ∑' history : M.InformationHistory i site.1,
    M.historyReachWeight strategy history.1

/-- Positive information mass is equivalent to a positive history in its
fiber, without any finiteness assumption on that fiber. -/
theorem informationMass_pos_iff
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (i : ι) (site : M.InformationSite i) :
    0 < M.informationMass strategy i site ↔
      ∃ history : M.InformationHistory i site.1,
        0 < M.historyReachWeight strategy history.1 := by
  unfold informationMass
  rw [pos_iff_ne_zero, ENNReal.summable.tsum_ne_zero_iff]
  simp only [ne_eq, pos_iff_ne_zero]

/-- An antichain information site's reach weights form a subprobability law,
including when the fiber contains histories at unbounded and varying depths. -/
theorem informationMass_le_one
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (i : ι) (site : M.InformationSite i)
    (hanti : site.IsHistoryAntichain) :
    M.informationMass strategy i site ≤ 1 := by
  unfold informationMass historyReachWeight
  exact ENNReal.summable.tsum_le_of_sum_le fun s =>
    InformationSite.sum_reach_le_one M site hanti strategy s

/-- A disjoint outside history leaves strictly less than total probability
available for the information site whenever that history has positive weight. -/
theorem informationMass_add_outside_le_one
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (i : ι) (site : M.InformationSite i)
    (hanti : site.IsHistoryAntichain) (outside : E.History)
    (houtside : ∀ history : M.InformationHistory i site.1,
      Disjoint (historyCone history.1) (historyCone outside)) :
    M.informationMass strategy i site + M.historyReachWeight strategy outside ≤ 1 := by
  unfold informationMass historyReachWeight
  rw [ENNReal.tsum_eq_iSup_sum, ENNReal.iSup_add]
  exact iSup_le fun s =>
    InformationSite.sum_reach_add_outside_le_one M site hanti strategy outside
      houtside s

theorem informationMass_lt_one_of_outside_pos
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (i : ι) (site : M.InformationSite i)
    (hanti : site.IsHistoryAntichain) (outside : E.History)
    (houtside : ∀ history : M.InformationHistory i site.1,
      Disjoint (historyCone history.1) (historyCone outside))
    (hpositive : 0 < M.historyReachWeight strategy outside) :
    M.informationMass strategy i site < 1 := by
  have hbound := M.informationMass_add_outside_le_one strategy i site
    hanti outside houtside
  have hfinite : M.informationMass strategy i site ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (M.informationMass_le_one strategy i site hanti)
      ENNReal.one_lt_top)
  exact lt_of_lt_of_le (ENNReal.lt_add_right hfinite hpositive.ne') hbound

/-- Normalize a positive information event into a belief on its actual
history fiber. The mass bound comes from the antichain event theorem. -/
def bayesBelief
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (i : ι) (site : M.InformationSite i)
    (hanti : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy i site) :
    PMF (M.InformationHistory i site.1) :=
  PMF.normalize
    (fun history => M.historyReachWeight strategy history.1)
    (ne_of_gt hmass)
    (ne_of_lt (lt_of_le_of_lt (M.informationMass_le_one strategy i site hanti)
      ENNReal.one_lt_top))

@[simp]
theorem bayesBelief_apply
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (i : ι) (site : M.InformationSite i)
    (hanti : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass strategy i site)
    (history : M.InformationHistory i site.1) :
    M.bayesBelief strategy i site hanti hmass history =
      M.historyReachWeight strategy history.1 /
        M.informationMass strategy i site := by
  simp only [bayesBelief, PMF.normalize_apply, informationMass]
  rfl

/-- Bayes' rule at a positive-mass information site. The predicate places
no requirement on a belief when the site's mass is zero. -/
def BehavioralAssessment.IsBayesConsistentAt
    (A : M.BehavioralAssessment)
    (i : ι) (site : M.InformationSite i)
    (_hanti : site.IsHistoryAntichain)
    (_hmass : 0 < M.informationMass A.strategy i site) : Prop :=
  ∀ history : M.InformationHistory i site.1,
    A.belief i site history =
      M.historyReachWeight A.strategy history.1 /
        M.informationMass A.strategy i site

/-- Bayes' rule at every positive-mass decision information site. -/
def BehavioralAssessment.IsBayesConsistent
    (A : M.BehavioralAssessment)
    (hanti : M.DecisionInformationAntichain) : Prop :=
  ∀ (i : ι) (site : M.InformationSite i),
    ∀ hmass : 0 < M.informationMass A.strategy i site,
      BehavioralAssessment.IsBayesConsistentAt M A i site (hanti i site) hmass

/-- At a positive-mass site, pointwise Bayes consistency is equality with the
normalized belief law. -/
theorem BehavioralAssessment.isBayesConsistentAt_iff
    (A : M.BehavioralAssessment)
    (i : ι) (site : M.InformationSite i)
    (hanti : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass A.strategy i site) :
    BehavioralAssessment.IsBayesConsistentAt M A i site hanti hmass ↔
      A.belief i site = M.bayesBelief A.strategy i site hanti hmass := by
  constructor
  · intro h
    apply PMF.ext
    intro history
    exact (h history).trans (M.bayesBelief_apply A.strategy i site hanti hmass history).symm
  · intro h history
    rw [h]
    exact M.bayesBelief_apply A.strategy i site hanti hmass history

end Bayes

end InformationModel

end GameTheory.Protocol
