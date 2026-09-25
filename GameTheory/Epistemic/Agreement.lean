/-
# Agreement over epistemic setoids

Posterior aggregation uses the ordinary PMF quotient-observation disintegration.
The proof ranges over supported quotient fibers and does not enumerate states
or information cells.

Primary reference: R. J. Aumann, “Agreeing to Disagree,” *Annals of
Statistics* 4 (1976).
-/

import GameTheory.Epistemic.Basic

noncomputable section

namespace GameTheory.Epistemic

open GameTheory.Math.Probability

universe uΩ

variable {Ω : Type uΩ}

private theorem expect_indicator_inter_eq_report_mul_mass
    (prior : PMF Ω) (partition : Setoid Ω) (event publicEvent : Set Ω)
    (hself : IsSelfEvident partition publicEvent) (report : ℝ)
    (hreport : ∀ state ∈ publicEvent,
      posterior prior partition event state = report) :
    expect prior
        ((publicEvent ∩ event).indicator (fun _ => (1 : ℝ)))
        (payoffIntegrable_indicator (publicEvent ∩ event)
          (payoffIntegrable_constant prior 1)) =
      report * (prior.toOuterMeasure publicEvent).toReal := by
  classical
  let obs := observation partition
  let marginal := PMF.map obs prior
  let qPublic : Set (Quotient partition) := obs '' publicEvent
  let kernel := fun b hb => fiberPosterior prior obs b hb
  let integrand : Ω → ℝ :=
    (publicEvent ∩ event).indicator (fun _ => (1 : ℝ))
  let outerValue : Quotient partition → ℝ := fun b =>
    report * if b ∈ qPublic then 1 else 0
  have hsource : PayoffIntegrable prior integrand :=
    payoffIntegrable_indicator _ (payoffIntegrable_constant prior 1)
  have hbind : PayoffIntegrable (marginal.bindOnSupport kernel) integrand :=
    payoffIntegrable_congr_law (fiberPosterior_reconstruct prior obs).symm
      hsource
  have houterValue : PayoffIntegrable marginal outerValue := by
    exact payoffIntegrable_const_mul
      (payoffIntegrable_indicator qPublic
        (payoffIntegrable_constant marginal 1))
  have hconditional : ∀ b, ∀ hb : b ∈ marginal.support,
      outerValue b =
        expect (kernel b hb) integrand
          (payoffIntegrable_bindOnSupport_conditional_on_support
            marginal kernel integrand hbind b hb) := by
    intro b hb
    rcases (PMF.mem_support_map_iff (f := obs) (p := prior) (b := b)).mp hb
      with ⟨representative,
      hrepresentative, hrepresentativeEq⟩
    have hkSupport : (kernel b hb).support =
        {other | obs other = b} ∩ prior.support := by
      simp only [kernel, fiberPosterior_support]
    by_cases hbPublic : b ∈ qPublic
    · obtain ⟨publicState, hpublicState, hpublicEq⟩ := hbPublic
      have hclass : obs representative = obs publicState :=
        hrepresentativeEq.trans hpublicEq.symm
      have hrepresentativeCell :
          representative ∈ cell partition publicState := by
        rw [cell]
        exact partition.symm (Quotient.eq.mp hclass)
      have hrepresentativePublic : representative ∈ publicEvent :=
        hself publicState hpublicState hrepresentativeCell
      have hposterior := hreport representative hrepresentativePublic
      have hcellWitness :
          ∃ other ∈ cell partition representative, other ∈ prior.support :=
        ⟨representative, partition.refl representative, hrepresentative⟩
      have hposteriorBridge := posterior_eq_fiberPosterior_expect
        prior partition event representative hcellWitness
      have hkernelEq : kernel b hb =
          fiberPosterior prior obs (obs representative) (by
            rw [PMF.support_map]
            exact ⟨representative, hrepresentative, rfl⟩) := by
        subst b
        rfl
      have hconditionalSupport :
          ∀ other ∈ (kernel b hb).support,
            other ∈ publicEvent := by
        intro other hother
        rw [hkSupport, Set.mem_inter_iff] at hother
        have hotherClass : obs other = obs publicState :=
          hother.1.trans hpublicEq.symm
        have hotherCell : other ∈ cell partition publicState := by
          rw [cell]
          exact partition.symm (Quotient.eq.mp hotherClass)
        exact hself publicState hpublicState hotherCell
      have hintegrandEq : ∀ other ∈ (kernel b hb).support,
          integrand other = if other ∈ event then 1 else 0 := by
        intro other hother
        have hpublic := hconditionalSupport other hother
        simp [integrand, Set.indicator, hpublic]
      have hconstGuard : PayoffIntegrable (kernel b hb)
          (fun _ : Ω => (1 : ℝ)) := payoffIntegrable_constant _ 1
      have heventGuard : PayoffIntegrable (kernel b hb)
          (fun other => if other ∈ event then 1 else 0) :=
        payoffIntegrable_indicator event hconstGuard
      have heqExpect := expect_congr_on_support hintegrandEq
        (payoffIntegrable_bindOnSupport_conditional_on_support
          marginal kernel integrand hbind b hb) heventGuard
      have hposteriorValue : expect (kernel b hb) integrand
          (payoffIntegrable_bindOnSupport_conditional_on_support
            marginal kernel integrand hbind b hb) = report := by
        have hfiberGuard := payoffIntegrable_congr_law hkernelEq heventGuard
        calc
          expect (kernel b hb) integrand
              (payoffIntegrable_bindOnSupport_conditional_on_support
                marginal kernel integrand hbind b hb) =
              expect (kernel b hb)
                (fun other => if other ∈ event then 1 else 0) heventGuard :=
            heqExpect
          _ = expect (fiberPosterior prior obs (obs representative) _)
                (fun other => if other ∈ event then 1 else 0) hfiberGuard :=
            expect_congr_law hkernelEq _ _ _
          _ = report := by
            simpa only [kernel] using hposteriorBridge.symm.trans hposterior
      calc
        outerValue b = report := by
          have hpublic : b ∈ qPublic := ⟨publicState, hpublicState, hpublicEq⟩
          simp [outerValue, hpublic]
        _ = expect (kernel b hb) integrand
              (payoffIntegrable_bindOnSupport_conditional_on_support
                marginal kernel integrand hbind b hb) := hposteriorValue.symm
    · have hzeroOnSupport : ∀ other ∈ (kernel b hb).support,
          integrand other = 0 := by
        intro other hother
        rw [hkSupport, Set.mem_inter_iff] at hother
        have hnotPublic : other ∉ publicEvent := by
          intro hotherPublic
          exact hbPublic ⟨other, hotherPublic, hother.1⟩
        simp [integrand, hnotPublic]
      have hzeroGuard : PayoffIntegrable (kernel b hb)
          (fun _ : Ω => (0 : ℝ)) := payoffIntegrable_zero _
      have hzero := expect_congr_on_support hzeroOnSupport
        (payoffIntegrable_bindOnSupport_conditional_on_support
          marginal kernel integrand hbind b hb) hzeroGuard
      have hzero' : expect (kernel b hb) (fun _ => (0 : ℝ)) hzeroGuard = 0 := by
        exact expect_constant _ 0 hzeroGuard
      calc
        outerValue b = 0 := by simp [outerValue, hbPublic]
        _ = expect (kernel b hb) integrand
              (payoffIntegrable_bindOnSupport_conditional_on_support
                marginal kernel integrand hbind b hb) := (hzero.trans hzero').symm
  have htower := expect_bindOnSupport_tower_on_support marginal kernel
    integrand hbind outerValue hconditional
  have hboundLaw := fiberPosterior_reconstruct prior obs
  have hsourceEq := expect_congr_law hboundLaw integrand hbind hsource
  have hpreimage : obs ⁻¹' qPublic = publicEvent := by
    ext state
    constructor
    · rintro ⟨publicState, hpublicState, hclass⟩
      have hstatePublic : state ∈ cell partition publicState := by
        rw [cell]
        exact Quotient.eq.mp hclass
      exact hself publicState hpublicState hstatePublic
    · intro hstate
      exact ⟨state, hstate, rfl⟩
  have hmass : (marginal.toOuterMeasure qPublic).toReal =
      (prior.toOuterMeasure publicEvent).toReal := by
    rw [PMF.toOuterMeasure_map_apply, hpreimage]
  have houterEval : expect marginal outerValue houterValue =
      report * (prior.toOuterMeasure publicEvent).toReal := by
    have hind : PayoffIntegrable marginal
        (fun b => if b ∈ qPublic then (1 : ℝ) else 0) :=
      payoffIntegrable_indicator qPublic (payoffIntegrable_constant marginal 1)
    calc
      expect marginal outerValue houterValue =
          report * expect marginal (fun b => if b ∈ qPublic then (1 : ℝ) else 0) hind := by
        simpa only [outerValue] using expect_const_mul hind
      _ = report * (marginal.toOuterMeasure qPublic).toReal := by
        rw [expect_indicator marginal qPublic hind]
      _ = report * (prior.toOuterMeasure publicEvent).toReal := by
        rw [hmass]
  calc
    expect prior integrand hsource =
        expect (marginal.bindOnSupport kernel) integrand hbind := hsourceEq.symm
    _ = expect marginal outerValue houterValue := by
      simpa only [marginal, kernel] using htower
    _ = report * (prior.toOuterMeasure publicEvent).toReal := houterEval

/-- **Aumann full agreement.** On a common nonempty event that is
self-evident for both partitions, two posteriors that are constant throughout
that event are equal. The state space, PMF support, and cells may be infinite. -/
theorem aumann_full_agreement
    (prior : PMF Ω)
    (first second : Setoid Ω) (event : Set Ω)
    {publicEvent : Set Ω} (hnonempty : publicEvent.Nonempty)
    (hfirst : IsSelfEvident first publicEvent)
    (hsecond : IsSelfEvident second publicEvent)
    {firstReport secondReport : ℝ}
    (hfirstReport : ∀ state ∈ publicEvent,
      posterior prior first event state = firstReport)
    (hsecondReport : ∀ state ∈ publicEvent,
      posterior prior second event state = secondReport) :
    firstReport = secondReport := by
  by_cases hpublicZero : prior.toOuterMeasure publicEvent = 0
  · have hdisjoint : Disjoint prior.support publicEvent := by
      rw [← PMF.toOuterMeasure_apply_eq_zero_iff]
      exact hpublicZero
    have hposteriorZero (partition : Setoid Ω)
        (hself : IsSelfEvident partition publicEvent)
        {state : Ω} (hstate : state ∈ publicEvent) :
        posterior prior partition event state = 0 := by
      have hnumeratorZero :
          prior.toOuterMeasure (event ∩ cell partition state) = 0 := by
        rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
        intro other hsupport hother
        have hpublic : other ∈ publicEvent :=
          hself state hstate hother.2
        exact Set.disjoint_left.mp hdisjoint hsupport hpublic
      simp [posterior, hnumeratorZero]
    obtain ⟨state, hstate⟩ := hnonempty
    have hfirstZero := hfirstReport state hstate
    have hsecondZero := hsecondReport state hstate
    rw [hposteriorZero first hfirst hstate] at hfirstZero
    rw [hposteriorZero second hsecond hstate] at hsecondZero
    exact hfirstZero.symm.trans hsecondZero
  have hpublicPos : 0 < prior.toOuterMeasure publicEvent :=
    pos_iff_ne_zero.mpr hpublicZero
  have hpublicFinite := outerMeasure_ne_top prior publicEvent
  have hfirstMass := expect_indicator_inter_eq_report_mul_mass prior first
    event publicEvent hfirst firstReport hfirstReport
  have hsecondMass := expect_indicator_inter_eq_report_mul_mass prior second
    event publicEvent hsecond secondReport hsecondReport
  have hequal :
      firstReport * (prior.toOuterMeasure publicEvent).toReal =
        secondReport * (prior.toOuterMeasure publicEvent).toReal := by
    rw [← hfirstMass, ← hsecondMass]
  exact mul_right_cancel₀
    (ne_of_gt (ENNReal.toReal_pos hpublicPos.ne' hpublicFinite)) hequal

/-- **Aumann agreement from common knowledge.** The common-knowledge witness
supplies the public event self-evident for both selected agents. -/
theorem aumann_full_agreement_of_commonKnowledgeAt {agents : Type*}
    (prior : PMF Ω)
    (partition : agents → Setoid Ω) (first second : agents)
    (event reportEvent : Set Ω) {state : Ω}
    {firstReport secondReport : ℝ}
    (hcommon : CommonKnowledgeAt partition reportEvent state)
    (hfirstReport : ∀ world ∈ reportEvent,
      posterior prior (partition first) event world = firstReport)
    (hsecondReport : ∀ world ∈ reportEvent,
      posterior prior (partition second) event world = secondReport) :
    firstReport = secondReport := by
  obtain ⟨publicEvent, hsubset, hstate, hself⟩ := hcommon
  exact aumann_full_agreement prior (partition first) (partition second)
    event ⟨state, hstate⟩ (hself first) (hself second)
    (fun world hworld => hfirstReport world (hsubset hworld))
    (fun world hworld => hsecondReport world (hsubset hworld))

end GameTheory.Epistemic
