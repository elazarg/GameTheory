/-
# EXP-135: arbitrary epistemic events with PMF beliefs

This gate checks the Setoid epistemic API on an infinite-support prior and an
infinite information cell. Its quantitative witness has distinct agent
partitions and reports. It also tests exact agreement at a nonempty null
public event and separates knowledge from positive scalar belief at a null cell.
-/

import GameTheory.Epistemic.ApproximateAgreement
import GameTheory.Epistemic.Agreement
import GameTheory.Experimental.PostArchitecture.PMFRestorationProbe

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.PMFEpistemicGate

open GameTheory.Epistemic GameTheory.Math.Probability
open GameTheory.Experimental.PMFRestoration
open Classical

def firstObservation (n : ℕ) : ℕ :=
  if n = 1 then 0 else if 3 ≤ n then 3 else n

def secondObservation (n : ℕ) : ℕ :=
  if n = 2 then 0 else if 3 ≤ n then 3 else n

def partition : Bool → Setoid ℕ
  | true => {
      r := fun first second => firstObservation first = firstObservation second
      iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩ }
  | false => {
      r := fun first second => secondObservation first = secondObservation second
      iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩ }

theorem firstCell_zero : cell (partition true) 0 = {0, 1} := by
  ext n
  show firstObservation 0 = firstObservation n ↔ n = 0 ∨ n = 1
  by_cases hn1 : n = 1
  · subst n
    simp [firstObservation]
  · by_cases hn3 : 3 ≤ n
    · simp [firstObservation, hn1, hn3]
      omega
    · simp [firstObservation, hn1, hn3]
      omega

theorem secondCell_zero : cell (partition false) 0 = {0, 2} := by
  ext n
  show secondObservation 0 = secondObservation n ↔ n = 0 ∨ n = 2
  by_cases hn2 : n = 2
  · subst n
    simp [secondObservation]
  · by_cases hn3 : 3 ≤ n
    · simp [secondObservation, hn2, hn3]
      omega
    · simp [secondObservation, hn2, hn3]
      omega

private theorem geometric_mass_pair (a b : ℕ) (hab : a ≠ b) :
    geometric.toOuterMeasure ({a, b} : Set ℕ) = geometric a + geometric b := by
  rw [PMF.toOuterMeasure_apply]
  have hzero : ∀ n, n ∉ ({a, b} : Finset ℕ) →
      ({a, b} : Set ℕ).indicator geometric n = 0 := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    simp [Set.indicator, hn]
  rw [tsum_eq_sum (s := {a, b}) hzero]
  simp [Set.indicator, hab, Ne.symm hab]

private theorem geometric_mass_singleton (n : ℕ) :
    geometric.toOuterMeasure ({n} : Set ℕ) = geometric n :=
  geometric.toOuterMeasure_apply_singleton n

private theorem geometric_mass_first_cell :
    geometric.toOuterMeasure (cell (partition true) 0) =
      geometric 0 + geometric 1 := by
  rw [firstCell_zero, geometric_mass_pair 0 1 (by decide)]

private theorem geometric_mass_second_cell :
    geometric.toOuterMeasure (cell (partition false) 0) =
      geometric 0 + geometric 2 := by
  rw [secondCell_zero, geometric_mass_pair 0 2 (by decide)]

private theorem geometric_report_first :
    GameTheory.Epistemic.posterior geometric (partition true) {1} 0 =
      (1 / 3 : ℝ) := by
  rw [GameTheory.Epistemic.posterior, firstCell_zero]
  rw [show ({1} : Set ℕ) ∩ {0, 1} = {1} by ext n; simp]
  rw [geometric_mass_singleton, geometric_mass_pair 0 1 (by decide)]
  rw [ENNReal.toReal_add (geometric.apply_ne_top 0) (geometric.apply_ne_top 1),
    geometric_real 0, geometric_real 1]
  norm_num

private theorem geometric_report_second :
    GameTheory.Epistemic.posterior geometric (partition false) {1} 0 = 0 := by
  rw [GameTheory.Epistemic.posterior, secondCell_zero]
  rw [show ({1} : Set ℕ) ∩ {0, 2} = (∅ : Set ℕ) by ext n; simp]
  have hempty : geometric.toOuterMeasure (∅ : Set ℕ) = 0 := by
    rw [geometric.toOuterMeasure_apply]
    simp
  rw [hempty, geometric_mass_pair 0 2 (by decide)]
  simp

def reportStates : Set ℕ :=
  {n | ∀ agent : Bool,
    GameTheory.Epistemic.posterior geometric (partition agent) {1} n =
      if agent then (1 / 3 : ℝ) else 0}

theorem zero_mem_reportStates : 0 ∈ reportStates := by
  intro agent
  cases agent
  · exact geometric_report_second
  · exact geometric_report_first

private theorem posterior_ge_of_mem_zero (agent : Bool) (event : Set ℕ)
    (hzero : 0 ∈ event) :
    (2 / 3 : ℝ) ≤
      GameTheory.Epistemic.posterior geometric (partition agent) event 0 := by
  have hnumerator : geometric.toOuterMeasure {0} ≤
      geometric.toOuterMeasure (event ∩ cell (partition agent) 0) :=
    geometric.toOuterMeasure_mono (by
      intro n hn
      rcases hn with ⟨hn, hsupport⟩
      have hn0 : n = 0 := Set.mem_singleton_iff.mp hn
      subst n
      exact ⟨hzero, (partition agent).refl 0⟩)
  have hdenominator :
      (geometric.toOuterMeasure (cell (partition agent) 0)).toReal =
        if agent then (3 / 4 : ℝ) else (5 / 8 : ℝ) := by
    cases agent
    · rw [geometric_mass_second_cell]
      rw [ENNReal.toReal_add (geometric.apply_ne_top 0)
        (geometric.apply_ne_top 2), geometric_real 0, geometric_real 2]
      norm_num
    · rw [geometric_mass_first_cell]
      rw [ENNReal.toReal_add (geometric.apply_ne_top 0)
        (geometric.apply_ne_top 1), geometric_real 0, geometric_real 1]
      norm_num
  have hzeroMass : (geometric.toOuterMeasure {0}).toReal = (1 / 2 : ℝ) := by
    rw [geometric_mass_singleton]
    simpa using geometric_real 0
  have hnumReal :
      (geometric.toOuterMeasure (event ∩ cell (partition agent) 0)).toReal ≥
        (1 / 2 : ℝ) := by
    calc
      (geometric.toOuterMeasure (event ∩ cell (partition agent) 0)).toReal ≥
          (geometric.toOuterMeasure {0}).toReal :=
        ENNReal.toReal_mono (outerMeasure_ne_top geometric _) hnumerator
      _ = 1 / 2 := hzeroMass
  rw [GameTheory.Epistemic.posterior, hdenominator]
  have hbound : (2 / 3 : ℝ) ≤
      (geometric.toOuterMeasure (event ∩ cell (partition agent) 0)).toReal /
        (if agent then (3 / 4 : ℝ) else (5 / 8 : ℝ)) := by
    cases agent <;> norm_num at * <;> nlinarith
  exact hbound

def tail : Set ℕ := {n | 3 ≤ n}

theorem first_tail_cell (n : ℕ) (hn : 3 ≤ n) :
    cell (partition true) n = tail := by
  ext m
  show firstObservation n = firstObservation m ↔ 3 ≤ m
  have hn1 : n ≠ 1 := by omega
  have hobs : firstObservation n = 3 := by
    simp [firstObservation, hn, hn1]
  constructor
  · intro heq
    by_contra hm
    rw [hobs] at heq
    have hmCases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hmCases with hm0 | hm1 | hm2
    · subst m
      simp [firstObservation] at heq
    · subst m
      simp [firstObservation] at heq
    · subst m
      simp [firstObservation] at heq
  · intro hm
    have hm1 : m ≠ 1 := by omega
    have hobsM : firstObservation m = 3 := by
      simp [firstObservation, hm, hm1]
    rw [hobs, hobsM]

theorem second_tail_cell (n : ℕ) (hn : 3 ≤ n) :
    cell (partition false) n = tail := by
  ext m
  show secondObservation n = secondObservation m ↔ 3 ≤ m
  have hn2 : n ≠ 2 := by omega
  have hobs : secondObservation n = 3 := by
    simp [secondObservation, hn, hn2]
  constructor
  · intro heq
    by_contra hm
    rw [hobs] at heq
    have hmCases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hmCases with hm0 | hm1 | hm2
    · subst m
      simp [secondObservation] at heq
    · subst m
      simp [secondObservation] at heq
    · subst m
      simp [secondObservation] at heq
  · intro hm
    have hm2 : m ≠ 2 := by omega
    have hobsM : secondObservation m = 3 := by
      simp [secondObservation, hm, hm2]
    rw [hobs, hobsM]

theorem partition_first_infinite_cell : (cell (partition true) 3).Infinite := by
  rw [first_tail_cell 3 (by norm_num)]
  have hrange : Set.range (fun n : ℕ => n + 3) ⊆ tail := by
    intro n hn
    obtain ⟨m, rfl⟩ := hn
    simp [tail]
  exact (Set.infinite_range_of_injective (fun a b h => by omega)).mono hrange

theorem partition_second_infinite_cell : (cell (partition false) 3).Infinite := by
  rw [second_tail_cell 3 (by norm_num)]
  have hrange : Set.range (fun n : ℕ => n + 3) ⊆ tail := by
    intro n hn
    obtain ⟨m, rfl⟩ := hn
    simp [tail]
  exact (Set.infinite_range_of_injective (fun a b h => by omega)).mono hrange

theorem exact_agreement_on_infinite_public_cell : (0 : ℝ) = 0 := by
  have hself (agent : Bool) : IsSelfEvident (partition agent) tail := by
    intro state hstate other hother
    cases agent with
    | false =>
        rw [second_tail_cell state hstate] at hother
        exact hother
    | true =>
        rw [first_tail_cell state hstate] at hother
        exact hother
  have hreport (agent : Bool) :
      ∀ state ∈ tail,
        GameTheory.Epistemic.posterior geometric (partition agent) {0} state = 0 := by
    intro state hstate
    unfold GameTheory.Epistemic.posterior
    have hcell : cell (partition agent) state = tail := by
      cases agent with
      | false => exact second_tail_cell state hstate
      | true => exact first_tail_cell state hstate
    rw [hcell]
    have hzero : geometric.toOuterMeasure (({0} : Set ℕ) ∩ tail) = 0 := by
      rw [PMF.toOuterMeasure_apply_eq_zero_iff]
      rw [Set.disjoint_left]
      intro n hsupport hmem
      have hn0 : n = 0 := Set.mem_singleton_iff.mp hmem.1
      have hn3 : 3 ≤ n := by simpa [tail] using hmem.2
      omega
    rw [hzero]
    simp
  exact aumann_full_agreement geometric (partition true) (partition false)
    {0} ⟨3, by norm_num [tail]⟩ (hself true) (hself false)
    (firstReport := 0) (secondReport := 0) (hreport true) (hreport false)

theorem geometric_common_p_belief_distinct_reports :
    CommonPBeliefAt geometric partition (2 / 3 : ℝ) reportStates 0 := by
  refine ⟨{0}, by simp, ?_, ?_⟩
  · intro agent n hn
    have hn0 : n = 0 := Set.mem_singleton_iff.mp hn
    subst n
    rw [mem_PBelief_iff]
    exact posterior_ge_of_mem_zero agent {0} (by simp)
  · intro n hn
    have hn0 : n = 0 := Set.mem_singleton_iff.mp hn
    subst n
    intro agent'
    exact posterior_ge_of_mem_zero agent' reportStates zero_mem_reportStates

theorem geometric_approximate_agreement_distinct_reports :
    |(1 / 3 : ℝ) - 0| ≤ 2 * (1 - (2 / 3 : ℝ)) := by
  exact commonPBelief_posterior_reports_close (by norm_num)
    geometric_common_p_belief_distinct_reports true false

def mappedGeometric : PMF (Option ℕ) := geometric.map some

def singletonInformation : Setoid (Option ℕ) where
  r first second := first = second
  iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩

theorem mappedGeometric_support_infinite : mappedGeometric.support.Infinite := by
  rw [mappedGeometric, PMF.support_map, geometric_support]
  apply (Set.infinite_image_iff (by
    intro a _ b _ h
    exact Option.some.inj h)).2
  exact Set.infinite_univ

private theorem mappedGeometric_none_mass : mappedGeometric none = 0 := by
  apply (mappedGeometric.apply_eq_zero_iff none).2
  rw [mappedGeometric, PMF.support_map]
  rintro ⟨n, hn, hnone⟩
  cases hnone

private theorem mappedGeometric_none_event_mass :
    mappedGeometric.toOuterMeasure {none} = 0 := by
  rw [mappedGeometric.toOuterMeasure_apply_singleton, mappedGeometric_none_mass]

private theorem mappedGeometric_nullCell_posterior
    (event : Set (Option ℕ)) :
    posterior mappedGeometric singletonInformation event none = 0 := by
  have hcell : cell singletonInformation none = {none} := by
    ext world
    show none = world ↔ world = none
    exact eq_comm
  have hnum :
      mappedGeometric.toOuterMeasure (event ∩ {none}) = 0 := by
    have hnot : none ∉ mappedGeometric.support := by
      rw [mappedGeometric, PMF.support_map]
      rintro ⟨n, hn, hnone⟩
      cases hnone
    have hdisjoint : Disjoint mappedGeometric.support (event ∩ {none}) := by
      rw [Set.disjoint_left]
      intro world hsupport hmem
      have hnone : world = none := Set.mem_singleton_iff.mp hmem.2
      subst world
      exact (hnot hsupport).elim
    rw [PMF.toOuterMeasure_apply_eq_zero_iff]
    exact hdisjoint
  unfold GameTheory.Epistemic.posterior
  rw [hcell, hnum, mappedGeometric_none_event_mass]
  simp

theorem nullSingleton_knows_but_has_zero_posterior :
    none ∈ Knows singletonInformation Set.univ ∧
      none ∉ PBelief mappedGeometric singletonInformation (1 / 2)
        Set.univ := by
  constructor
  · exact Set.subset_univ _
  · rw [mem_PBelief_iff, mappedGeometric_nullCell_posterior]
    norm_num

theorem mappedGeometric_null_public_agreement : (0 : ℝ) = 0 := by
  have hcell (state : Option ℕ) :
      cell singletonInformation state = {state} := by
    ext other
    show state = other ↔ other = state
    exact eq_comm
  have hself : IsSelfEvident singletonInformation ({none} : Set (Option ℕ)) := by
    intro state hstate other hother
    have hstate' : state = none := Set.mem_singleton_iff.mp hstate
    subst state
    rw [hcell] at hother
    exact Set.mem_singleton_iff.mpr (Set.mem_singleton_iff.mp hother)
  have hreport : ∀ state ∈ ({none} : Set (Option ℕ)),
      GameTheory.Epistemic.posterior mappedGeometric singletonInformation
        {some 0} state = 0 := by
    intro state hstate
    have hstate' : state = none := Set.mem_singleton_iff.mp hstate
    subst state
    exact mappedGeometric_nullCell_posterior {some 0}
  exact aumann_full_agreement mappedGeometric singletonInformation
    singletonInformation {some 0} (publicEvent := {none})
    ⟨none, rfl⟩ hself hself (firstReport := 0) (secondReport := 0)
    hreport hreport

end GameTheory.Experimental.PostArchitecture.PMFEpistemicGate
