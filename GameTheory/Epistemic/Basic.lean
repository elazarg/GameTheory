/-
# Setoid epistemic partitions

Knowledge is represented by an explicit setoid on the state space. Bayesian
reports use an ordinary PMF and arbitrary set events; no finiteness capability
is stored in the epistemic data.
-/

import GameTheory.Epistemic.Knowledge
import GameTheory.Math.Probability.Bounds
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheory.Math.Probability.Support

noncomputable section

namespace GameTheory.Epistemic

open GameTheory.Math.Probability
open Classical

universe uΩ

variable {Ω : Type uΩ}

/-- The scalar posterior of an event given the state’s information cell.
At a zero-mass cell both numerator and denominator are zero, so the value is
defined to be zero by real division. -/
def posterior (prior : PMF Ω) (partition : Setoid Ω)
    (event : Set Ω) (state : Ω) : ℝ :=
  (prior.toOuterMeasure (event ∩ cell partition state)).toReal /
  (prior.toOuterMeasure (cell partition state)).toReal

/-- Quotient observation associated with a setoid information structure. -/
def observation (partition : Setoid Ω) : Ω → Quotient partition :=
  Quotient.mk partition

/-- A quotient fiber is exactly the corresponding information cell. -/
theorem observation_fiber (partition : Setoid Ω) (state : Ω) :
    observation partition ⁻¹' {observation partition state} =
      cell partition state := by
  ext other
  simp only [Set.mem_preimage, Set.mem_singleton_iff, observation, cell,
    Set.mem_ofPred_eq, Quotient.eq]
  exact ⟨partition.symm, partition.symm⟩

/-- States in one cell have identical scalar posteriors. -/
theorem posterior_eq_of_mem_cell (prior : PMF Ω) (partition : Setoid Ω)
    (event : Set Ω) (state other : Ω)
    (hother : other ∈ cell partition state) :
    posterior prior partition event state =
      posterior prior partition event other := by
  have hcells : cell partition state = cell partition other := by
    ext candidate
    constructor
    · intro hcandidate
      exact partition.trans (partition.symm hother) hcandidate
    · intro hcandidate
      exact partition.trans hother hcandidate
  simp only [posterior, hcells]

/-- On a positive-mass information cell, the scalar posterior is the event
probability under the existing subtype-free fiber posterior. This connects
setoid cells to the canonical quotient-observation disintegration. -/
theorem posterior_eq_fiberPosterior_expect
    (prior : PMF Ω) (partition : Setoid Ω) (event : Set Ω) (state : Ω)
    (hcell : ∃ other ∈ cell partition state, other ∈ prior.support) :
    posterior prior partition event state =
      expect
        (fiberPosterior prior (observation partition)
          (observation partition state) (by
            rw [PMF.support_map]
            obtain ⟨other, hother, hsupport⟩ := hcell
            refine ⟨other, hsupport, ?_⟩
            exact Quotient.eq.mpr (partition.symm hother)))
        (fun other => if other ∈ event then 1 else 0)
        (payoffIntegrable_fiberPosterior prior (observation partition)
          (fun other => if other ∈ event then 1 else 0)
          (payoffIntegrable_indicator event
            (payoffIntegrable_constant prior 1))
          (observation partition state) (by
            rw [PMF.support_map]
            obtain ⟨other, hother, hsupport⟩ := hcell
            refine ⟨other, hsupport, ?_⟩
            exact Quotient.eq.mpr (partition.symm hother))) := by
  classical
  let obs := observation partition
  let observed := obs state
  have hobs : observed ∈ (PMF.map obs prior).support := by
    rw [PMF.support_map]
    obtain ⟨other, hother, hsupport⟩ := hcell
    exact ⟨other, hsupport, Quotient.eq.mpr (partition.symm hother)⟩
  let conditional := fiberPosterior prior obs observed hobs
  let indicator : Ω → ℝ := fun other => if other ∈ event then 1 else 0
  have hpriorIndicator : PayoffIntegrable prior indicator :=
    payoffIntegrable_indicator event (payoffIntegrable_constant prior 1)
  have hconditional := payoffIntegrable_fiberPosterior prior obs indicator
    hpriorIndicator observed hobs
  have hfiber : obs ⁻¹' {observed} = cell partition state := by
    simpa only [obs, observed] using observation_fiber partition state
  have hnum :
      expect prior ((obs ⁻¹' {observed}).indicator indicator)
        (payoffIntegrable_indicator (obs ⁻¹' {observed}) hpriorIndicator) =
      (prior.toOuterMeasure (event ∩ cell partition state)).toReal := by
    let rhs := (event ∩ cell partition state).indicator (fun _ => (1 : ℝ))
    have hrhs : PayoffIntegrable prior rhs :=
      payoffIntegrable_indicator (event ∩ cell partition state)
        (payoffIntegrable_constant prior 1)
    have hfunc : ∀ other ∈ prior.support,
        (obs ⁻¹' {observed}).indicator indicator other = rhs other := by
      intro other _
      by_cases hcell' : other ∈ cell partition state
      · by_cases hevent : other ∈ event <;>
          simp [rhs, Set.indicator, indicator, hfiber, hcell', hevent]
      · simp [rhs, Set.indicator, indicator, hfiber, hcell']
    calc
      expect prior ((obs ⁻¹' {observed}).indicator indicator)
          (payoffIntegrable_indicator (obs ⁻¹' {observed}) hpriorIndicator) =
        expect prior rhs hrhs := expect_congr_on_support hfunc _ _
      _ = (prior.toOuterMeasure (event ∩ cell partition state)).toReal :=
        expect_indicator prior (event ∩ cell partition state) hrhs
  have hden :
      (∑' other, (obs ⁻¹' {observed}).indicator prior other) =
        prior.toOuterMeasure (cell partition state) := by
    rw [← PMF.toOuterMeasure_apply prior, hfiber]
  have hformula := expect_fiberPosterior prior obs indicator hpriorIndicator
    observed hobs
  unfold posterior
  simpa only [conditional, hnum, hden, obs, observed, ENNReal.toReal_div] using
    hformula.symm

/-- A self-evident event has posterior one at any state whose information
cell has positive prior mass. -/
theorem posterior_eq_one_of_selfEvident_of_cell_mass_pos
    (prior : PMF Ω) (partition : Setoid Ω) (event : Set Ω) (state : Ω)
    (hstate : state ∈ event) (hself : IsSelfEvident partition event)
    (hpositive : 0 < prior.toOuterMeasure (cell partition state)) :
    posterior prior partition event state = 1 := by
  have hinter : event ∩ cell partition state = cell partition state := by
    ext other
    simp only [Set.mem_inter_iff]
    constructor
    · exact And.right
    · intro hcell
      exact ⟨hself state hstate hcell, hcell⟩
  have hfinite : prior.toOuterMeasure (cell partition state) ≠ ⊤ := by
    apply ne_of_lt
    have hmass := PMF.toOuterMeasure_apply prior (cell partition state)
    rw [hmass]
    calc
      ∑' other : Ω, (cell partition state).indicator prior other ≤
          ∑' other : Ω, prior other := by
        apply ENNReal.tsum_le_tsum
        intro other
        by_cases hmem : other ∈ cell partition state <;>
          simp [Set.indicator, hmem]
      _ = 1 := prior.tsum_coe
      _ < ⊤ := ENNReal.one_lt_top
  unfold posterior
  rw [hinter, div_self]
  exact ne_of_gt (ENNReal.toReal_pos hpositive.ne' hfinite)

/-- Under full support, a self-evident event has posterior one at its states. -/
theorem posterior_eq_one_of_selfEvident
    (prior : PMF Ω) (hfull : FullSupport prior)
    (partition : Setoid Ω) (event : Set Ω) (state : Ω)
    (hstate : state ∈ event) (hself : IsSelfEvident partition event) :
    posterior prior partition event state = 1 := by
  apply posterior_eq_one_of_selfEvident_of_cell_mass_pos prior partition
    event state hstate hself
  exact outerMeasure_pos_of_mem_support state
    (partition.refl state) (hfull state)

/-- A cell contained in an event has posterior one when that cell has positive
prior mass. -/
theorem posterior_eq_one_of_cell_subset_of_cell_mass_pos
    (prior : PMF Ω) (partition : Setoid Ω) {event : Set Ω} {state : Ω}
    (hcell : cell partition state ⊆ event)
    (hpositive : 0 < prior.toOuterMeasure (cell partition state)) :
    posterior prior partition event state = 1 := by
  have hinter : event ∩ cell partition state = cell partition state := by
    ext other
    simp only [Set.mem_inter_iff]
    constructor
    · exact And.right
    · intro hother
      exact ⟨hcell hother, hother⟩
  have hfinite : prior.toOuterMeasure (cell partition state) ≠ ⊤ := by
    apply ne_of_lt
    rw [PMF.toOuterMeasure_apply prior (cell partition state)]
    calc
      ∑' other : Ω, (cell partition state).indicator prior other ≤
          ∑' other : Ω, prior other := by
        apply ENNReal.tsum_le_tsum
        intro other
        by_cases hmem : other ∈ cell partition state <;>
          simp [Set.indicator, hmem]
      _ = 1 := prior.tsum_coe
      _ < ⊤ := ENNReal.one_lt_top
  unfold posterior
  rw [hinter, div_self]
  exact ne_of_gt (ENNReal.toReal_pos hpositive.ne' hfinite)

/-- Under full support, a cell contained in an event has posterior one. -/
theorem posterior_eq_one_of_cell_subset
    (prior : PMF Ω) (hfull : FullSupport prior)
    (partition : Setoid Ω) {event : Set Ω} {state : Ω}
    (hcell : cell partition state ⊆ event) :
    posterior prior partition event state = 1 := by
  apply posterior_eq_one_of_cell_subset_of_cell_mass_pos prior partition hcell
  exact outerMeasure_pos_of_mem_support state
    (partition.refl state) (hfull state)

/-- Outside a self-evident event, its posterior is zero. -/
theorem posterior_eq_zero_of_not_mem_selfEvident
    (prior : PMF Ω) (partition : Setoid Ω) (event : Set Ω)
    (state : Ω) (hstate : state ∉ event)
    (hself : IsSelfEvident partition event) :
    posterior prior partition event state = 0 := by
  have hinter : event ∩ cell partition state = ∅ :=
    Set.disjoint_iff_inter_eq_empty.mp
      (cell_disjoint_of_not_mem_selfEvident partition event state hstate hself).symm
  unfold posterior
  rw [hinter, PMF.toOuterMeasure_apply, Set.indicator_empty]
  simp

end GameTheory.Epistemic
