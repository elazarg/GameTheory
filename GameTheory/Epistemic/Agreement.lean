/-
# Agreement over finite epistemic partitions

Finite cell decomposition and Aumann's agreement theorem over the canonical
finite probability law.
-/

import GameTheory.Epistemic.Basic

noncomputable section

namespace GameTheory.Epistemic

open GameTheory.Probability

universe uΩ

variable {Ω : Type uΩ}

/-- Distinct cells of a partition are disjoint. -/
theorem cells_disjoint (partition : InfoPartition Ω) {first second : Ω}
    (hne : partition.cell first ≠ partition.cell second) :
    Disjoint (partition.cell first) (partition.cell second) := by
  rw [Finset.disjoint_left]
  intro state hfirst hsecond
  apply hne
  rw [← partition.coherent first state hfirst,
    partition.coherent second state hsecond]

/-- A self-evident event is the disjoint union of the cells it contains. -/
theorem selfEvident_eq_biUnion_cells [DecidableEq Ω]
    (partition : InfoPartition Ω) {event : Finset Ω}
    (hself : IsSelfEvident partition event) :
    event = (event.image partition.cell).biUnion id := by
  ext state
  simp only [Finset.mem_biUnion, Finset.mem_image, id]
  refine ⟨fun hstate => ?_, ?_⟩
  · exact ⟨partition.cell state, ⟨state, hstate, rfl⟩,
      partition.reflexive state⟩
  · rintro ⟨_, ⟨source, hsource, rfl⟩, hstate⟩
    exact hself source hsource hstate

/-- Finite sums over a self-evident event decompose over its distinct cells. -/
theorem selfEvident_sum_decomp [DecidableEq Ω]
    (partition : InfoPartition Ω) {event : Finset Ω}
    (hself : IsSelfEvident partition event) (value : Ω → ℝ) :
    ∑ state ∈ event, value state =
      ∑ cell ∈ event.image partition.cell, ∑ state ∈ cell, value state := by
  have hdisjoint :
      (event.image partition.cell : Set (Finset Ω)).PairwiseDisjoint id := by
    intro first hfirst second hsecond hne
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hfirst hsecond
    obtain ⟨firstState, _, rfl⟩ := hfirst
    obtain ⟨secondState, _, rfl⟩ := hsecond
    exact cells_disjoint partition (fun h => hne h)
  conv_lhs => rw [selfEvident_eq_biUnion_cells partition hself]
  rw [Finset.sum_biUnion hdisjoint]
  rfl

/-- **Aumann full agreement.** On a common nonempty event that is self-evident
for both partitions, two posteriors that are constant throughout that event
are equal. -/
theorem aumann_full_agreement [DecidableEq Ω]
    (prior : FinDist Ω) (hfull : prior.FullSupport)
    (first second : InfoPartition Ω) (event : Finset Ω)
    {publicEvent : Finset Ω} (hnonempty : publicEvent.Nonempty)
    (hfirst : IsSelfEvident first publicEvent)
    (hsecond : IsSelfEvident second publicEvent)
    {firstReport secondReport : ℝ}
    (hfirstReport :
      ∀ state ∈ publicEvent,
        posterior prior first event state = firstReport)
    (hsecondReport :
      ∀ state ∈ publicEvent,
        posterior prior second event state = secondReport) :
    firstReport = secondReport := by
  have hprior_pos : ∀ state, 0 < prior.prob state :=
    fun state => FinDist.prob_pos_iff.mpr (hfull state)
  have hpublic_pos : 0 < ∑ state ∈ publicEvent, prior.prob state :=
    Finset.sum_pos (fun state _ => hprior_pos state) hnonempty
  have hcellIdentity : ∀ {partition : InfoPartition Ω} {report : ℝ},
      IsSelfEvident partition publicEvent →
      (∀ state ∈ publicEvent,
        posterior prior partition event state = report) →
      ∀ {cell : Finset Ω}, cell ∈ publicEvent.image partition.cell →
        ∑ state ∈ cell ∩ event, prior.prob state =
          report * ∑ state ∈ cell, prior.prob state := by
    intro partition report hself hreport cell hcell
    rw [Finset.mem_image] at hcell
    obtain ⟨state, hstate, hcellState⟩ := hcell
    have hposterior := hreport state hstate
    have hcell_pos : 0 < ∑ other ∈ partition.cell state, prior.prob other :=
      Finset.sum_pos (fun other _ => hprior_pos other)
        ⟨state, partition.reflexive state⟩
    have hquotient :
        (∑ other ∈ partition.cell state ∩ event, prior.prob other) /
            ∑ other ∈ partition.cell state, prior.prob other =
          report :=
      hposterior
    field_simp at hquotient
    rw [← hcellState]
    linarith
  have htotal : ∀ {partition : InfoPartition Ω} {report : ℝ},
      IsSelfEvident partition publicEvent →
      (∀ state ∈ publicEvent,
        posterior prior partition event state = report) →
      ∑ state ∈ publicEvent ∩ event, prior.prob state =
        report * ∑ state ∈ publicEvent, prior.prob state := by
    intro partition report hself hreport
    rw [selfEvident_sum_decomp partition hself prior.prob,
      Finset.mul_sum]
    have hinter :
        publicEvent ∩ event =
          (publicEvent.image partition.cell).biUnion
            (fun cell => cell ∩ event) := by
      conv_lhs => rw [selfEvident_eq_biUnion_cells partition hself]
      rw [Finset.biUnion_inter]
      rfl
    rw [hinter]
    have hdisjoint :
        (publicEvent.image partition.cell : Set (Finset Ω)).PairwiseDisjoint
          (fun cell => cell ∩ event) := by
      intro firstCell hfirstCell secondCell hsecondCell hne
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hfirstCell hsecondCell
      obtain ⟨firstState, _, rfl⟩ := hfirstCell
      obtain ⟨secondState, _, rfl⟩ := hsecondCell
      exact (cells_disjoint partition (fun h => hne h)).mono
        Finset.inter_subset_left Finset.inter_subset_left
    rw [Finset.sum_biUnion hdisjoint]
    exact Finset.sum_congr rfl fun cell hmem =>
      hcellIdentity hself hreport hmem
  have hfirstTotal := htotal hfirst hfirstReport
  have hsecondTotal := htotal hsecond hsecondReport
  have hequal :
      firstReport * ∑ state ∈ publicEvent, prior.prob state =
        secondReport * ∑ state ∈ publicEvent, prior.prob state := by
    rw [← hfirstTotal, ← hsecondTotal]
  exact mul_right_cancel₀ hpublic_pos.ne' hequal

end GameTheory.Epistemic
