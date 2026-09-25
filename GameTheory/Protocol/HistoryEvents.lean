/-
# Reach events of complete histories

Finite-depth cylinder facts for the canonical PMF history runner.
-/

import GameTheory.Protocol.BehavioralAssessment

noncomputable section

namespace GameTheory.Protocol

open GameTheory GameTheory.Math.Probability
open scoped ENNReal

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace ExecutionProtocol

/-- A bounded continuation adds at most its fuel to trace depth. -/
theorem ReachesWithin.trace_length_le_add {fuel : ℕ}
    {start target : E.History} (hreach : E.ReachesWithin fuel start target) :
    target.trace.length ≤ start.trace.length + fuel := by
  induction hreach with
  | refl => simp
  | step joint legal realized rest ih =>
      simpa only [History.extend, Trace.length, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using ih

end ExecutionProtocol

namespace InformationModel

variable (M : InformationModel E)

section ReachWeight

variable [Fintype ι]

/-- The probability weight of one complete history, evaluated at exactly its
trace depth in the canonical behavioral runner. -/
def historyReachWeight
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (history : E.History) : ℝ≥0∞ :=
  M.runBehavioral strategy history.trace.length history

end ReachWeight

/-- The finite-depth runner's support contains only histories reachable from
its starting history within the supplied fuel. -/
theorem runBehavioralFrom_reachesWithin
    [Fintype ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (fuel : ℕ) (start target : E.History)
    (h : target ∈ (M.runBehavioralFrom strategy fuel start).support) :
    E.ReachesWithin fuel start target := by
  exact E.runRandomizedFor_reachesWithin (M.randomizedChooser strategy) fuel
    start target h

/-- A history antichain has disjoint continuation cones, even when its
histories occur at different depths. -/
theorem InformationSite.eq_of_common_descendant {i : ι}
    (site : M.InformationSite i) (hanti : site.IsHistoryAntichain)
    (first second : M.InformationHistory i site.1) (target : E.History)
    {firstFuel secondFuel : ℕ}
    (hfirst : E.ReachesWithin firstFuel first.1 target)
    (hsecond : E.ReachesWithin secondFuel second.1 target) :
    first = second := by
  have hcmp : first.1 = second.1 := by
    rcases le_total first.1.trace.length second.1.trace.length with hle | hle
    · have hreach := hfirst.ancestor_comparable hsecond hle
      rcases hreach.eq_or_step with heq | ⟨joint, legal, reached, realized, fuel, rest⟩
      · exact heq
      · exact False.elim (hanti first second joint legal reached realized fuel rest)
    · have hreach := hsecond.ancestor_comparable hfirst hle
      rcases hreach.eq_or_step with heq | ⟨joint, legal, reached, realized, fuel, rest⟩
      · exact heq.symm
      · exact False.elim (hanti second first joint legal reached realized fuel rest)
  exact Subtype.ext hcmp

/-- The cone of all realized continuations of one complete history. -/
def historyCone (history : E.History) : Set E.History :=
  {target | ∃ fuel, E.ReachesWithin fuel history target}

theorem mem_historyCone_of_reachesWithin {history target : E.History}
    {fuel : ℕ} (hreach : E.ReachesWithin fuel history target) :
    target ∈ historyCone history := ⟨fuel, hreach⟩

/-- A depth-`d` run can contribute to a history cone rooted at depth `d`
only from that root itself. Terminal absorption handles early stopping. -/
theorem eq_of_runBehavioral_support_and_cone
    [Fintype ι]
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (history prior target : E.History)
    (hdepth : prior ∈ (M.runBehavioral strategy history.trace.length).support)
    {extra : ℕ}
    (htarget : target ∈ (M.runBehavioralFrom strategy extra prior).support)
    (hcone : target ∈ historyCone history) : prior = history := by
  obtain ⟨coneFuel, hreach⟩ := hcone
  have hprefix := M.runBehavioralFrom_reachesWithin strategy
    history.trace.length E.initHistory prior hdepth
  have hupper : prior.trace.length ≤ history.trace.length := by
    simpa [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length]
      using hprefix.trace_length_le_add
  have hlower : history.trace.length ≤ prior.trace.length := by
    rcases E.runRandomizedFor_terminal_or_length (M.randomizedChooser strategy)
        history.trace.length E.initHistory prior hdepth with hterminal | hlength
    · have htargeteq : target = prior := by
        have hpure := M.runBehavioralFrom_of_terminal strategy extra hterminal
        rw [hpure, PMF.mem_support_pure_iff] at htarget
        exact htarget
      subst target
      exact hreach.trace_length_le
    · simpa [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length]
        using hlength
  have hsame := hreach.eq_start_of_same_length
    (M.runBehavioralFrom_reachesWithin strategy extra prior target htarget)
    (Nat.le_antisymm hlower hupper)
  exact hsame.symm

/-- At any later depth, a history cone has exactly the reach weight of its
root at the root's own depth. -/
theorem runBehavioral_cone_mass
    [Fintype ι] (strategy : (i : ι) → M.BehavioralPolicy i)
    (history : E.History) (extra : ℕ) :
    (M.runBehavioral strategy (history.trace.length + extra)).toOuterMeasure
        (historyCone history) =
      M.runBehavioral strategy history.trace.length history := by
  classical
  let p := M.runBehavioral strategy history.trace.length
  have hkernel : ∀ prior : E.History,
      p prior * (M.runBehavioralFrom strategy extra prior).toOuterMeasure
        (historyCone history) = if prior = history then p prior else 0 := by
    intro prior
    by_cases hsupp : prior ∈ p.support
    · by_cases heq : prior = history
      · subst prior
        have hfull : (M.runBehavioralFrom strategy extra history).support ⊆
            historyCone history := by
          intro target htarget
          exact mem_historyCone_of_reachesWithin
            (M.runBehavioralFrom_reachesWithin strategy extra history target htarget)
        rw [(PMF.toOuterMeasure_apply_eq_one_iff _ _).2 hfull]
        simp
      · have hempty : Disjoint (M.runBehavioralFrom strategy extra prior).support
            (historyCone history) := by
          apply Set.disjoint_left.mpr
          intro target htarget hcone
          exact heq (M.eq_of_runBehavioral_support_and_cone strategy history
            prior target hsupp htarget hcone)
        rw [(PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 hempty]
        simp [heq]
    · have hzero : p prior = 0 := (PMF.apply_eq_zero_iff p prior).2 hsupp
      simp [hzero]
  calc
    _ = (p.bind (M.runBehavioralFrom strategy extra)).toOuterMeasure
        (historyCone history) := by
          rw [runBehavioral, M.runBehavioralFrom_add]
          rfl
    _ = ∑' prior, p prior * (M.runBehavioralFrom strategy extra prior).toOuterMeasure
        (historyCone history) := PMF.toOuterMeasure_bind_apply _ _ _
    _ = ∑' prior, if prior = history then p prior else 0 :=
      tsum_congr hkernel
    _ = p history := by simp

section FiniteConeMass

/-- Discrete measurability for the finite union of history cones used below. -/
local instance : MeasurableSpace E.History := ⊤

/-- Any finite collection of histories in an information antichain has total
reach weight at most one. Branching and the history carrier may be infinite. -/
theorem InformationSite.sum_reach_le_one [Fintype ι] {i : ι}
    (site : M.InformationSite i) (hanti : site.IsHistoryAntichain)
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (s : Finset (M.InformationHistory i site.1)) :
    (∑ history ∈ s,
      M.runBehavioral strategy history.1.trace.length history.1) ≤ 1 := by
  classical
  let depth := s.sup (fun history => history.1.trace.length)
  let μ := (M.runBehavioral strategy depth).toMeasure
  have hdisj : Set.PairwiseDisjoint (↑s : Set (M.InformationHistory i site.1))
      (fun history => historyCone history.1) := by
    intro first hfirst second hsecond hne
    apply Set.disjoint_left.mpr
    intro target htfirst htsecond
    obtain ⟨firstFuel, hfirstReach⟩ := htfirst
    obtain ⟨secondFuel, hsecondReach⟩ := htsecond
    exact hne (InformationSite.eq_of_common_descendant M site hanti first second target
      hfirstReach hsecondReach)
  have hmeas : ∀ history ∈ s, MeasurableSet (historyCone history.1) := by
    intro history hhistory
    exact MeasurableSpace.measurableSet_top
  calc
    _ = ∑ history ∈ s, μ (historyCone history.1) := by
      apply Finset.sum_congr rfl
      intro history hh
      have hle : history.1.trace.length ≤ depth :=
        Finset.le_sup (f := fun history : M.InformationHistory i site.1 =>
          history.1.trace.length) hh
      obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le hle
      have hmass := M.runBehavioral_cone_mass strategy history.1 extra
      rw [← heq] at hmass
      exact ((PMF.toMeasure_apply_eq_toOuterMeasure_apply
        (M.runBehavioral strategy depth) (hmeas history hh)).trans hmass).symm
    _ = μ (⋃ history ∈ s, historyCone history.1) :=
      (MeasureTheory.measure_biUnion_finset hdisj hmeas).symm
    _ ≤ μ Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
    _ = 1 := by
      rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ MeasurableSet.univ]
      simp [PMF.toOuterMeasure_apply]

/-- A disjoint outside history consumes probability mass in addition to a
finite part of an information antichain. -/
theorem InformationSite.sum_reach_add_outside_le_one [Fintype ι] {i : ι}
    (site : M.InformationSite i) (hanti : site.IsHistoryAntichain)
    (strategy : (i : ι) → M.BehavioralPolicy i)
    (outside : E.History)
    (houtside : ∀ history : M.InformationHistory i site.1,
      Disjoint (historyCone history.1) (historyCone outside))
    (s : Finset (M.InformationHistory i site.1)) :
    (∑ history ∈ s,
      M.runBehavioral strategy history.1.trace.length history.1) +
      M.runBehavioral strategy outside.trace.length outside ≤ 1 := by
  classical
  let depth := max outside.trace.length
    (s.sup fun history => history.1.trace.length)
  let μ := (M.runBehavioral strategy depth).toMeasure
  let sites := ⋃ history ∈ s, historyCone history.1
  have hdisj : Set.PairwiseDisjoint (↑s : Set (M.InformationHistory i site.1))
      (fun history => historyCone history.1) := by
    intro first hfirst second hsecond hne
    apply Set.disjoint_left.mpr
    intro target htfirst htsecond
    obtain ⟨firstFuel, hfirstReach⟩ := htfirst
    obtain ⟨secondFuel, hsecondReach⟩ := htsecond
    exact hne (InformationSite.eq_of_common_descendant M site hanti first second target
      hfirstReach hsecondReach)
  have hmeas : ∀ history ∈ s, MeasurableSet (historyCone history.1) := by
    intro history hhistory
    exact MeasurableSpace.measurableSet_top
  have hdisjOutside : Disjoint sites (historyCone outside) := by
    apply Set.disjoint_left.mpr
    intro target hsite htarget
    obtain ⟨history, hsite⟩ := Set.mem_iUnion.mp hsite
    obtain ⟨hh, hcone⟩ := Set.mem_iUnion.mp hsite
    exact (Set.disjoint_left.mp (houtside history)) hcone htarget
  have hsiteMass :
      (∑ history ∈ s, μ (historyCone history.1)) =
        ∑ history ∈ s,
          M.runBehavioral strategy history.1.trace.length history.1 := by
    apply Finset.sum_congr rfl
    intro history hh
    have hle : history.1.trace.length ≤ depth :=
      le_trans (Finset.le_sup (f := fun history : M.InformationHistory i site.1 =>
        history.1.trace.length) hh) (Nat.le_max_right _ _)
    obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le hle
    have hmass := M.runBehavioral_cone_mass strategy history.1 extra
    rw [← heq] at hmass
    exact (PMF.toMeasure_apply_eq_toOuterMeasure_apply
      (M.runBehavioral strategy depth) (hmeas history hh)).trans hmass
  have houtsideMass : μ (historyCone outside) =
      M.runBehavioral strategy outside.trace.length outside := by
    have hle : outside.trace.length ≤ depth := Nat.le_max_left _ _
    obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le hle
    have hmass := M.runBehavioral_cone_mass strategy outside extra
    rw [← heq] at hmass
    exact (PMF.toMeasure_apply_eq_toOuterMeasure_apply
      (M.runBehavioral strategy depth) MeasurableSpace.measurableSet_top).trans hmass
  calc
    _ = (∑ history ∈ s, μ (historyCone history.1)) +
        μ (historyCone outside) := by rw [hsiteMass, houtsideMass]
    _ = μ sites + μ (historyCone outside) := by
      rw [MeasureTheory.measure_biUnion_finset hdisj hmeas]
    _ = μ (sites ∪ historyCone outside) :=
      (MeasureTheory.measure_union hdisjOutside MeasurableSpace.measurableSet_top).symm
    _ ≤ μ Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
    _ = 1 := by
      rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ MeasurableSet.univ]
      simp [PMF.toOuterMeasure_apply]

end FiniteConeMass

end InformationModel

end GameTheory.Protocol
