/-
# Quantitative approximate agreement

The private finite-mass lemmas establish the Monderer--Samet bound for the
public `p`-belief operators. They use the canonical `FinDist` prior throughout.
-/

import GameTheory.Epistemic.Agreement
import GameTheory.Epistemic.Approximate

noncomputable section

namespace GameTheory.Epistemic

open GameTheory.Probability

universe uι uΩ

variable {Ω : Type uΩ} [Fintype Ω] [DecidableEq Ω]

private def eventMass (prior : FinDist Ω) (event : Finset Ω) : ℝ :=
  ∑ state ∈ event, prior.prob state

private theorem eventMass_decomp_cells
    (prior : FinDist Ω) (partition : InfoPartition Ω) (event : Finset Ω) :
    eventMass prior event =
      ∑ cell ∈ Finset.univ.image partition.cell,
        eventMass prior (cell ∩ event) := by
  unfold eventMass
  have hself :
      IsSelfEvident partition (Finset.univ : Finset Ω) := by
    intro _ _ state _
    exact Finset.mem_univ state
  have hdecomp :=
    selfEvident_sum_decomp partition hself
      (fun state => if state ∈ event then prior.prob state else 0)
  simpa [Finset.sum_filter, Finset.mem_inter, and_left_comm, and_assoc] using
    hdecomp

omit [Fintype Ω] [DecidableEq Ω] in
private theorem eventMass_mono (prior : FinDist Ω)
    {smaller larger : Finset Ω} (hsubset : smaller ⊆ larger) :
    eventMass prior smaller ≤ eventMass prior larger := by
  unfold eventMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (by intro state _ _; exact FinDist.prob_nonneg prior state)

omit [Fintype Ω] [DecidableEq Ω] in
private theorem eventMass_nonneg
    (prior : FinDist Ω) (event : Finset Ω) :
    0 ≤ eventMass prior event := by
  unfold eventMass
  exact Finset.sum_nonneg fun state _ => FinDist.prob_nonneg prior state

omit [Fintype Ω] [DecidableEq Ω] in
private theorem eventMass_pos_of_nonempty
    (prior : FinDist Ω) (hfull : prior.FullSupport)
    {event : Finset Ω} (hnonempty : event.Nonempty) :
    0 < eventMass prior event := by
  unfold eventMass
  exact Finset.sum_pos
    (fun state _ => FinDist.prob_pos_iff.mpr (hfull state)) hnonempty

omit [Fintype Ω] in
private theorem eventMass_inter_add_sdiff
    (prior : FinDist Ω) (cell event : Finset Ω) :
    eventMass prior (cell ∩ event) +
        eventMass prior (cell \ event) =
      eventMass prior cell := by
  unfold eventMass
  rw [← Finset.sum_union]
  · have hunion : cell ∩ event ∪ cell \ event = cell := by
      ext state
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro (hstate | hstate) <;> exact hstate.1
      · intro hstate
        by_cases hevent : state ∈ event
        · exact Or.inl ⟨hstate, hevent⟩
        · exact Or.inr ⟨hstate, hevent⟩
    rw [hunion]
  · rw [Finset.disjoint_left]
    intro state hfirst hsecond
    simp only [Finset.mem_inter, Finset.mem_sdiff] at hfirst hsecond
    exact hsecond.2 hfirst.2

private theorem PBelief_mono_event
    (prior : FinDist Ω) (hfull : prior.FullSupport)
    (partition : InfoPartition Ω) (threshold : ℝ)
    {smaller larger : Finset Ω} (hsubset : smaller ⊆ larger) :
    PBelief prior partition threshold smaller ⊆
      PBelief prior partition threshold larger := by
  intro state hstate
  rw [mem_PBelief_iff] at hstate ⊢
  unfold posterior at hstate ⊢
  have hdenominator :
      0 < ∑ other ∈ partition.cell state, prior.prob other :=
    Finset.sum_pos
      (fun other _ => FinDist.prob_pos_iff.mpr (hfull other))
      ⟨state, partition.reflexive state⟩
  have hnumerator :
      (∑ other ∈ partition.cell state ∩ smaller, prior.prob other) ≤
        ∑ other ∈ partition.cell state ∩ larger, prior.prob other := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro other hother
        exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp hother).1,
            hsubset (Finset.mem_inter.mp hother).2⟩)
      (by intro other _ _; exact FinDist.prob_nonneg prior other)
  exact le_trans hstate <|
    (div_le_div_iff_of_pos_right hdenominator).2 hnumerator

private theorem PBelief_cell_inter_nonempty
    (prior : FinDist Ω) (hfull : prior.FullSupport)
    (partition : InfoPartition Ω) {threshold : ℝ}
    (hthreshold : 0 < threshold) {event : Finset Ω} {state : Ω}
    (hstate : state ∈ PBelief prior partition threshold event) :
    (partition.cell state ∩ event).Nonempty := by
  rw [mem_PBelief_iff] at hstate
  unfold posterior at hstate
  have hdenominator :
      0 < ∑ other ∈ partition.cell state, prior.prob other :=
    Finset.sum_pos
      (fun other _ => FinDist.prob_pos_iff.mpr (hfull other))
      ⟨state, partition.reflexive state⟩
  have hnumerator :
      0 < ∑ other ∈ partition.cell state ∩ event, prior.prob other := by
    have hmul :
        threshold *
            (∑ other ∈ partition.cell state, prior.prob other) ≤
          ∑ other ∈ partition.cell state ∩ event, prior.prob other :=
      (le_div_iff₀ hdenominator).1 hstate
    nlinarith [mul_pos hthreshold hdenominator]
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  rw [hempty, Finset.sum_empty] at hnumerator
  linarith

private theorem posterior_eq_of_mem_PBelief_const
    (prior : FinDist Ω) (hfull : prior.FullSupport)
    (partition : InfoPartition Ω) {threshold : ℝ}
    (hthreshold : 0 < threshold)
    {beliefEvent reportEvent : Finset Ω} {report : ℝ} {state : Ω}
    (hstate :
      state ∈ PBelief prior partition threshold beliefEvent)
    (hreport :
      ∀ other ∈ beliefEvent,
        posterior prior partition reportEvent other = report) :
    posterior prior partition reportEvent state = report := by
  obtain ⟨other, hother⟩ :=
    PBelief_cell_inter_nonempty
      prior hfull partition hthreshold hstate
  rw [Finset.mem_inter] at hother
  rw [posterior_eq_of_mem_cell
    prior partition reportEvent state other hother.1]
  exact hreport other hother.2

private theorem PBelief_of_PBelief_subset_PBelief
    (prior : FinDist Ω) (hfull : prior.FullSupport)
    (partition : InfoPartition Ω) {threshold : ℝ}
    (hthreshold : 0 < threshold)
    {first second : Finset Ω} {state : Ω}
    (hstate : state ∈ PBelief prior partition threshold first)
    (hsubset : first ⊆ PBelief prior partition threshold second) :
    state ∈ PBelief prior partition threshold second := by
  rw [mem_PBelief_iff]
  obtain ⟨other, hother⟩ :=
    PBelief_cell_inter_nonempty
      prior hfull partition hthreshold hstate
  rw [Finset.mem_inter] at hother
  have hsecond := hsubset hother.2
  rw [mem_PBelief_iff] at hsecond
  rw [posterior_eq_of_mem_cell
    prior partition second state other hother.1]
  exact hsecond

private lemma commonPBelief_atom_real_arith
    {conditional share report threshold remainder : ℝ}
    (hconditional0 : 0 ≤ conditional) (hconditional1 : conditional ≤ 1)
    (hshare1 : share ≤ 1) (hthreshold : threshold ≤ share)
    (hremainder0 : 0 ≤ remainder)
    (hremainder1 : remainder ≤ 1 - share)
    (heq : report = conditional * share + remainder) :
    |conditional - report| ≤ 1 - threshold := by
  have hshare0 : (0 : ℝ) ≤ 1 - share := by
    linarith
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;>
    nlinarith [
      mul_le_mul_of_nonneg_right hconditional1 hshare0,
      mul_nonneg hconditional0 hshare0]

private theorem commonPBelief_atom_bound
    (prior : FinDist Ω) (hfull : prior.FullSupport)
    (partition : InfoPartition Ω)
    {threshold report : ℝ} {witness reportEvent cell : Finset Ω}
    (hevident :
      witness ⊆ PBelief prior partition threshold witness)
    (hreports :
      ∀ state ∈ witness,
        posterior prior partition reportEvent state = report)
    (hcell : cell ∈ Finset.univ.image partition.cell)
    (hcellWitness : 0 < eventMass prior (cell ∩ witness)) :
    |eventMass prior ((cell ∩ reportEvent) ∩ witness) /
          eventMass prior (cell ∩ witness) -
        report| ≤
      1 - threshold := by
  obtain ⟨source, _, rfl⟩ := Finset.mem_image.mp hcell
  have hnonempty : (partition.cell source ∩ witness).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at hcellWitness
    unfold eventMass at hcellWitness
    simp at hcellWitness
  obtain ⟨state, hstate⟩ := hnonempty
  rw [Finset.mem_inter] at hstate
  have hcellState :
      partition.cell state = partition.cell source :=
    partition.coherent source state hstate.1
  have hcellPos : 0 < eventMass prior (partition.cell source) :=
    eventMass_pos_of_nonempty prior hfull
      ⟨source, partition.reflexive source⟩
  have hreportWitness :
      eventMass prior
          ((partition.cell source ∩ reportEvent) ∩ witness) ≤
        eventMass prior (partition.cell source ∩ witness) :=
    eventMass_mono prior <| by
      intro other hother
      rw [Finset.mem_inter] at hother ⊢
      exact ⟨(Finset.mem_inter.mp hother.1).1, hother.2⟩
  have hreportCell :
      eventMass prior
          ((partition.cell source ∩ reportEvent) ∩ witness) ≤
        eventMass prior (partition.cell source ∩ reportEvent) :=
    eventMass_mono prior <| by
      intro other hother
      exact (Finset.mem_inter.mp hother).1
  have hwitnessCell :
      eventMass prior (partition.cell source ∩ witness) ≤
        eventMass prior (partition.cell source) :=
    eventMass_mono prior Finset.inter_subset_left
  have hreportEq :
      eventMass prior (partition.cell source ∩ reportEvent) =
        report * eventMass prior (partition.cell source) := by
    have hposterior := hreports state hstate.2
    unfold posterior at hposterior
    rw [hcellState] at hposterior
    have hposteriorMass :
        eventMass prior (partition.cell source ∩ reportEvent) /
          eventMass prior (partition.cell source) =
          report := by
      simpa only [eventMass] using hposterior
    field_simp [hcellPos.ne'] at hposteriorMass
    simpa [mul_comm] using hposteriorMass
  have hthresholdShare :
      threshold ≤
        eventMass prior (partition.cell source ∩ witness) /
          eventMass prior (partition.cell source) := by
    have hbelief := hevident hstate.2
    rw [mem_PBelief_iff] at hbelief
    unfold posterior at hbelief
    rw [hcellState] at hbelief
    have hbeliefMass :
        eventMass prior (partition.cell source ∩ witness) /
            eventMass prior (partition.cell source) ≥
          threshold := by
      simpa only [eventMass] using hbelief
    exact hbeliefMass
  have hremainderBound :
      eventMass prior (partition.cell source ∩ reportEvent) -
            eventMass prior
              ((partition.cell source ∩ reportEvent) ∩ witness) ≤
        eventMass prior (partition.cell source) -
          eventMass prior (partition.cell source ∩ witness) := by
    have hreportDecomp :=
      eventMass_inter_add_sdiff
        prior (partition.cell source ∩ reportEvent) witness
    have hcellDecomp :=
      eventMass_inter_add_sdiff prior (partition.cell source) witness
    have houtside :
        eventMass prior ((partition.cell source ∩ reportEvent) \ witness) ≤
          eventMass prior (partition.cell source \ witness) :=
      eventMass_mono prior <| by
        intro other hother
        rw [Finset.mem_sdiff] at hother ⊢
        exact ⟨(Finset.mem_inter.mp hother.1).1, hother.2⟩
    linarith
  have hconditional :
      eventMass prior
            ((partition.cell source ∩ reportEvent) ∩ witness) /
          eventMass prior (partition.cell source ∩ witness) ∈
        Set.Icc (0 : ℝ) 1 := by
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · exact div_nonneg (eventMass_nonneg prior _) hcellWitness.le
    · exact (div_le_one hcellWitness).2 hreportWitness
  have hremainder0 :
      0 ≤
        (eventMass prior (partition.cell source ∩ reportEvent) -
            eventMass prior
              ((partition.cell source ∩ reportEvent) ∩ witness)) /
          eventMass prior (partition.cell source) :=
    div_nonneg (sub_nonneg.mpr hreportCell) hcellPos.le
  have hremainder1 :
      (eventMass prior (partition.cell source ∩ reportEvent) -
            eventMass prior
              ((partition.cell source ∩ reportEvent) ∩ witness)) /
          eventMass prior (partition.cell source) ≤
        1 -
          eventMass prior (partition.cell source ∩ witness) /
            eventMass prior (partition.cell source) := by
    have hrewrite :
        1 -
            eventMass prior (partition.cell source ∩ witness) /
              eventMass prior (partition.cell source) =
          (eventMass prior (partition.cell source) -
              eventMass prior (partition.cell source ∩ witness)) /
            eventMass prior (partition.cell source) := by
      field_simp [hcellPos.ne']
    rw [hrewrite]
    exact div_le_div_of_nonneg_right hremainderBound hcellPos.le
  have heq :
      report =
        (eventMass prior
              ((partition.cell source ∩ reportEvent) ∩ witness) /
            eventMass prior (partition.cell source ∩ witness)) *
            (eventMass prior (partition.cell source ∩ witness) /
              eventMass prior (partition.cell source)) +
          (eventMass prior (partition.cell source ∩ reportEvent) -
              eventMass prior
                ((partition.cell source ∩ reportEvent) ∩ witness)) /
            eventMass prior (partition.cell source) := by
    have hcellNe : eventMass prior (partition.cell source) ≠ 0 :=
      hcellPos.ne'
    have hwitnessNe :
        eventMass prior (partition.cell source ∩ witness) ≠ 0 :=
      hcellWitness.ne'
    rw [show
      report =
          eventMass prior (partition.cell source ∩ reportEvent) /
            eventMass prior (partition.cell source) by
      rw [hreportEq]
      field_simp [hcellNe]]
    field_simp [hcellNe, hwitnessNe]
    ring
  exact commonPBelief_atom_real_arith
    hconditional.1 hconditional.2
    ((div_le_one hcellPos).2 hwitnessCell)
    hthresholdShare hremainder0 hremainder1 heq

private theorem commonPBelief_core_bound
    (prior : FinDist Ω) (hfull : prior.FullSupport)
    (partition : InfoPartition Ω)
    {threshold report : ℝ} {witness reportEvent : Finset Ω}
    (hnonempty : witness.Nonempty)
    (hevident :
      witness ⊆ PBelief prior partition threshold witness)
    (hreports :
      ∀ state ∈ witness,
        posterior prior partition reportEvent state = report) :
    |report -
        eventMass prior (witness ∩ reportEvent) /
          eventMass prior witness| ≤
      1 - threshold := by
  let cells : Finset (Finset Ω) :=
    Finset.univ.image partition.cell
  have hwitnessPos : 0 < eventMass prior witness :=
    eventMass_pos_of_nonempty prior hfull hnonempty
  have hwitnessDecomp :
      eventMass prior witness =
        ∑ cell ∈ cells, eventMass prior (cell ∩ witness) := by
    simpa [cells] using eventMass_decomp_cells prior partition witness
  have hreportDecomp :
      eventMass prior (witness ∩ reportEvent) =
        ∑ cell ∈ cells,
          eventMass prior ((cell ∩ reportEvent) ∩ witness) := by
    calc
      eventMass prior (witness ∩ reportEvent) =
          ∑ cell ∈ cells,
            eventMass prior (cell ∩ (witness ∩ reportEvent)) := by
        simpa [cells] using
          eventMass_decomp_cells
            prior partition (witness ∩ reportEvent)
      _ = ∑ cell ∈ cells,
            eventMass prior ((cell ∩ reportEvent) ∩ witness) := by
        refine Finset.sum_congr rfl fun cell _ => ?_
        rw [Finset.inter_assoc]
        congr 1
        ext state
        simp [and_assoc, and_comm]
  have hweighted :
      |report * eventMass prior witness -
          eventMass prior (witness ∩ reportEvent)| ≤
        eventMass prior witness * (1 - threshold) := by
    calc
      |report * eventMass prior witness -
          eventMass prior (witness ∩ reportEvent)| =
          |∑ cell ∈ cells,
            (report * eventMass prior (cell ∩ witness) -
              eventMass prior
                ((cell ∩ reportEvent) ∩ witness))| := by
        rw [hwitnessDecomp, hreportDecomp, Finset.mul_sum,
          ← Finset.sum_sub_distrib]
      _ ≤ ∑ cell ∈ cells,
          |report * eventMass prior (cell ∩ witness) -
            eventMass prior
              ((cell ∩ reportEvent) ∩ witness)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ cell ∈ cells,
          eventMass prior (cell ∩ witness) *
            (1 - threshold) := by
        refine Finset.sum_le_sum fun cell hcell => ?_
        by_cases hcellPos : 0 < eventMass prior (cell ∩ witness)
        · have hbound :=
            commonPBelief_atom_bound
              prior hfull partition hevident hreports hcell hcellPos
          rw [abs_sub_comm] at hbound
          have hcellNe : eventMass prior (cell ∩ witness) ≠ 0 :=
            hcellPos.ne'
          have hcellNonneg :
              0 ≤ eventMass prior (cell ∩ witness) :=
            eventMass_nonneg prior _
          have hterm :
              |report * eventMass prior (cell ∩ witness) -
                  eventMass prior
                    ((cell ∩ reportEvent) ∩ witness)| =
                eventMass prior (cell ∩ witness) *
                  |report -
                    eventMass prior
                        ((cell ∩ reportEvent) ∩ witness) /
                      eventMass prior (cell ∩ witness)| := by
            rw [show
              report * eventMass prior (cell ∩ witness) -
                    eventMass prior
                      ((cell ∩ reportEvent) ∩ witness) =
                  eventMass prior (cell ∩ witness) *
                    (report -
                      eventMass prior
                          ((cell ∩ reportEvent) ∩ witness) /
                        eventMass prior (cell ∩ witness)) by
              field_simp [hcellNe]]
            rw [abs_mul, abs_of_pos hcellPos]
          rw [hterm]
          exact mul_le_mul_of_nonneg_left hbound hcellNonneg
        · have hcellNonpos :
              eventMass prior (cell ∩ witness) ≤ 0 :=
            le_of_not_gt hcellPos
          have hcellZero :
              eventMass prior (cell ∩ witness) = 0 :=
            le_antisymm hcellNonpos (eventMass_nonneg prior _)
          have hreportLe :
              eventMass prior
                  ((cell ∩ reportEvent) ∩ witness) ≤
                eventMass prior (cell ∩ witness) :=
            eventMass_mono prior <| by
              intro state hstate
              rw [Finset.mem_inter] at hstate ⊢
              exact ⟨(Finset.mem_inter.mp hstate.1).1, hstate.2⟩
          have hreportZero :
              eventMass prior
                  ((cell ∩ reportEvent) ∩ witness) = 0 :=
            le_antisymm (by simpa [hcellZero] using hreportLe)
              (eventMass_nonneg prior _)
          have hreportZero' :
              eventMass prior (cell ∩ (reportEvent ∩ witness)) = 0 := by
            simpa [Finset.inter_assoc, Finset.inter_comm,
              Finset.inter_left_comm] using hreportZero
          simp [hcellZero, hreportZero']
      _ = eventMass prior witness * (1 - threshold) := by
        rw [← Finset.sum_mul, ← hwitnessDecomp]
  have hscaled :
      |report -
          eventMass prior (witness ∩ reportEvent) /
            eventMass prior witness| ≤
        1 - threshold := by
    have hwitnessNe : eventMass prior witness ≠ 0 :=
      hwitnessPos.ne'
    have hrewrite :
        report -
            eventMass prior (witness ∩ reportEvent) /
              eventMass prior witness =
          (report * eventMass prior witness -
              eventMass prior (witness ∩ reportEvent)) /
            eventMass prior witness := by
      field_simp [hwitnessNe]
    rw [hrewrite, abs_div, abs_of_pos hwitnessPos]
    have hweighted' :
        |report * eventMass prior witness -
            eventMass prior (witness ∩ reportEvent)| ≤
          (1 - threshold) * eventMass prior witness := by
      simpa [mul_comm] using hweighted
    exact (div_le_iff₀ hwitnessPos).2 hweighted'
  simpa [abs_sub_comm] using hscaled

/-- **Monderer--Samet approximate agreement.** Common `p`-belief that every
agent reports a fixed posterior makes any two reports differ by at most
`2 * (1 - p)`. -/
theorem commonPBelief_posterior_reports_close
    {ι : Type uι} [Fintype ι]
    {prior : FinDist Ω} (hfull : prior.FullSupport)
    {partition : ι → InfoPartition Ω}
    {reportEvent : Finset Ω} {state : Ω}
    {threshold : ℝ} (hthreshold : 0 < threshold)
    {report : ι → ℝ}
    (hcommon :
      CommonPBeliefAt prior partition threshold
        (Finset.univ.filter fun world =>
          ∀ agent : ι,
            posterior prior (partition agent) reportEvent world =
              report agent)
        state) :
    ∀ first second,
      |report first - report second| ≤
        2 * (1 - threshold) := by
  intro first second
  obtain ⟨initial, hstateInitial, hinitialEvident, hinitialBelief⟩ :=
    hcommon
  let reportStates : Finset Ω :=
    Finset.univ.filter fun world =>
      ∀ agent : ι,
        posterior prior (partition agent) reportEvent world =
          report agent
  let witness : Finset Ω :=
    PBelief prior (partition first) threshold initial ∩
      PBelief prior (partition second) threshold initial
  have hinitialWitness : initial ⊆ witness := by
    intro world hworld
    rw [Finset.mem_inter]
    exact ⟨hinitialEvident first hworld,
      hinitialEvident second hworld⟩
  have hwitnessNonempty : witness.Nonempty :=
    ⟨state, hinitialWitness hstateInitial⟩
  have hfirstEvident :
      witness ⊆
        PBelief prior (partition first) threshold witness := by
    intro world hworld
    rw [Finset.mem_inter] at hworld
    exact PBelief_mono_event
      prior hfull (partition first) threshold
      hinitialWitness hworld.1
  have hsecondEvident :
      witness ⊆
        PBelief prior (partition second) threshold witness := by
    intro world hworld
    rw [Finset.mem_inter] at hworld
    exact PBelief_mono_event
      prior hfull (partition second) threshold
      hinitialWitness hworld.2
  have hfirstReports :
      witness ⊆
        PBelief prior (partition first) threshold reportStates := by
    intro world hworld
    rw [Finset.mem_inter] at hworld
    exact PBelief_of_PBelief_subset_PBelief
      prior hfull (partition first) hthreshold hworld.1 <| by
        intro other hother
        have hmutual := hinitialBelief hother
        rw [mem_mutualPBelief_iff] at hmutual
        rw [mem_PBelief_iff]
        exact hmutual first
  have hsecondReports :
      witness ⊆
        PBelief prior (partition second) threshold reportStates := by
    intro world hworld
    rw [Finset.mem_inter] at hworld
    exact PBelief_of_PBelief_subset_PBelief
      prior hfull (partition second) hthreshold hworld.2 <| by
        intro other hother
        have hmutual := hinitialBelief hother
        rw [mem_mutualPBelief_iff] at hmutual
        rw [mem_PBelief_iff]
        exact hmutual second
  have hfirstConstant :
      ∀ world ∈ witness,
        posterior prior (partition first) reportEvent world =
          report first := by
    intro world hworld
    exact posterior_eq_of_mem_PBelief_const
      prior hfull (partition first) hthreshold
      (hfirstReports hworld) <| by
        intro other hother
        have hfilter :
            other ∈ Finset.univ.filter
              (fun candidate =>
                ∀ agent : ι,
                  posterior prior (partition agent) reportEvent candidate =
                    report agent) := by
          simpa only [reportStates] using hother
        rw [Finset.mem_filter] at hfilter
        exact hfilter.2 first
  have hsecondConstant :
      ∀ world ∈ witness,
        posterior prior (partition second) reportEvent world =
          report second := by
    intro world hworld
    exact posterior_eq_of_mem_PBelief_const
      prior hfull (partition second) hthreshold
      (hsecondReports hworld) <| by
        intro other hother
        have hfilter :
            other ∈ Finset.univ.filter
              (fun candidate =>
                ∀ agent : ι,
                  posterior prior (partition agent) reportEvent candidate =
                    report agent) := by
          simpa only [reportStates] using hother
        rw [Finset.mem_filter] at hfilter
        exact hfilter.2 second
  have hfirstBound :=
    commonPBelief_core_bound
      prior hfull (partition first) hwitnessNonempty
      hfirstEvident hfirstConstant
  have hsecondBound :=
    commonPBelief_core_bound
      prior hfull (partition second) hwitnessNonempty
      hsecondEvident hsecondConstant
  have htriangle :=
    abs_sub_le
      (report first)
      (eventMass prior (witness ∩ reportEvent) /
        eventMass prior witness)
      (report second)
  rw [abs_sub_comm] at hsecondBound
  linarith

end GameTheory.Epistemic
