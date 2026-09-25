/-
# Quantitative approximate agreement

The Monderer--Samet bound is obtained by comparing event indicators inside
each information fiber and aggregating with the PMF fiberwise expectation law.
The state space, event cells, and probability support may be infinite.
-/

import GameTheory.Epistemic.Approximate
import GameTheory.Math.Probability.ExpectationConditioning

noncomputable section

namespace GameTheory.Epistemic

open GameTheory.Math.Probability
open Classical

universe uι uΩ

variable {Ω : Type uΩ}

private def eventMass (prior : PMF Ω) (event : Set Ω) : ℝ :=
  (prior.toOuterMeasure event).toReal

private def eventIndicator (event : Set Ω) : Ω → ℝ :=
  fun state => if state ∈ event then 1 else 0

private theorem eventIndicator_integrable (prior : PMF Ω) (event : Set Ω) :
    PayoffIntegrable prior (eventIndicator event) := by
  apply payoffIntegrable_congr_on_support
    (μ := prior) (f := event.indicator (fun _ => (1 : ℝ)))
    (g := eventIndicator event)
  · intro state _
    by_cases hstate : state ∈ event <;> simp [eventIndicator, Set.indicator, hstate]
  · exact payoffIntegrable_indicator event (payoffIntegrable_constant prior 1)

private theorem eventMass_indicator (prior : PMF Ω) (event : Set Ω) :
    expect prior (eventIndicator event) (eventIndicator_integrable prior event) =
      eventMass prior event := by
  show expect prior (fun state => if state ∈ event then 1 else 0)
      (eventIndicator_integrable prior event) =
    (prior.toOuterMeasure event).toReal
  exact expect_indicator prior event (eventIndicator_integrable prior event)

private theorem eventMass_nonneg (prior : PMF Ω) (event : Set Ω) :
    0 ≤ eventMass prior event := ENNReal.toReal_nonneg

private theorem eventMass_mono (prior : PMF Ω)
    {smaller larger : Set Ω} (hsubset : smaller ⊆ larger) :
    eventMass prior smaller ≤ eventMass prior larger := by
  rw [← eventMass_indicator, ← eventMass_indicator]
  apply expect_mono
  · intro state _
    by_cases hsmall : state ∈ smaller
    · simp [eventIndicator, hsmall, hsubset hsmall]
    · by_cases hlarge : state ∈ larger <;>
        simp [eventIndicator, hsmall, hlarge]

private theorem eventMass_pos_iff_support (prior : PMF Ω) (event : Set Ω) :
    0 < eventMass prior event ↔ ∃ state ∈ event, state ∈ prior.support := by
  constructor
  · intro hpos
    by_contra hnone
    have hdisjoint : Disjoint prior.support event := by
      rw [Set.disjoint_left]
      intro state hsupport hevent
      exact hnone ⟨state, hevent, hsupport⟩
    have hzero : prior.toOuterMeasure event = 0 := by
      rw [PMF.toOuterMeasure_apply_eq_zero_iff]
      exact hdisjoint
    unfold eventMass at hpos
    rw [hzero] at hpos
    norm_num at hpos
  · rintro ⟨state, hevent, hsupport⟩
    have hpositive := outerMeasure_pos_of_mem_support state hevent hsupport
    exact ENNReal.toReal_pos hpositive.ne' (outerMeasure_ne_top prior event)

private theorem eventMass_inter_sdiff (prior : PMF Ω) (event witness : Set Ω) :
    eventMass prior event =
      eventMass prior (event ∩ witness) + eventMass prior (event \ witness) := by
  let firstGuard := eventIndicator_integrable prior (event ∩ witness)
  let secondGuard := eventIndicator_integrable prior (event \ witness)
  let eventGuard := eventIndicator_integrable prior event
  calc
    eventMass prior event = expect prior (eventIndicator event) eventGuard :=
      (eventMass_indicator prior event).symm
    _ = expect prior
        (fun state => eventIndicator (event ∩ witness) state +
          eventIndicator (event \ witness) state)
        (payoffIntegrable_add firstGuard secondGuard) := by
      apply expect_congr_on_support
      · intro state _
        by_cases hevent : state ∈ event <;>
          by_cases hwitness : state ∈ witness <;>
          simp [eventIndicator, hevent, hwitness]
    _ = expect prior (eventIndicator (event ∩ witness)) firstGuard +
          expect prior (eventIndicator (event \ witness)) secondGuard :=
      expect_add firstGuard secondGuard
    _ = eventMass prior (event ∩ witness) + eventMass prior (event \ witness) := by
      rw [eventMass_indicator, eventMass_indicator]

private theorem PBelief_cell_inter_nonempty
    (prior : PMF Ω)
    (partition : Setoid Ω) {threshold : ℝ}
    (hthreshold : 0 < threshold) {event : Set Ω} {state : Ω}
    (hstate : state ∈ PBelief prior partition threshold event) :
    (cell partition state ∩ event).Nonempty := by
  rw [mem_PBelief_iff] at hstate
  have hnumerator : 0 < eventMass prior (event ∩ cell partition state) := by
    by_contra hnot
    have hzero : eventMass prior (event ∩ cell partition state) = 0 :=
      le_antisymm (le_of_not_gt hnot) (eventMass_nonneg prior _)
    have htoReal :
        (prior.toOuterMeasure (event ∩ cell partition state)).toReal = 0 := by
      simpa [eventMass] using hzero
    have hzeroPosterior : posterior prior partition event state = 0 := by
      rw [posterior, htoReal]
      exact zero_div _
    rw [hzeroPosterior] at hstate
    exact (not_le_of_gt hthreshold) hstate
  obtain ⟨other, hotherEvent, hotherSupport⟩ :=
    (eventMass_pos_iff_support prior (event ∩ cell partition state)).1 hnumerator
  exact ⟨other, ⟨hotherEvent.2, hotherEvent.1⟩⟩

private theorem PBelief_cell_inter_mass_pos
    (prior : PMF Ω) (partition : Setoid Ω) {threshold : ℝ}
    (hthreshold : 0 < threshold) {event : Set Ω} {state : Ω}
    (hstate : state ∈ PBelief prior partition threshold event) :
    0 < eventMass prior (event ∩ cell partition state) := by
  rw [mem_PBelief_iff] at hstate
  by_contra hnot
  have hzero : eventMass prior (event ∩ cell partition state) = 0 :=
    le_antisymm (le_of_not_gt hnot) (eventMass_nonneg prior _)
  have htoReal :
      (prior.toOuterMeasure (event ∩ cell partition state)).toReal = 0 := by
    simpa [eventMass] using hzero
  have hzeroPosterior : posterior prior partition event state = 0 := by
    rw [posterior, htoReal]
    exact zero_div _
  rw [hzeroPosterior] at hstate
  exact (not_le_of_gt hthreshold) hstate

private theorem posterior_eq_of_mem_PBelief_const
    (prior : PMF Ω)
    (partition : Setoid Ω) {threshold : ℝ}
    (hthreshold : 0 < threshold)
    {beliefEvent reportEvent : Set Ω} {report : ℝ} {state : Ω}
    (hstate : state ∈ PBelief prior partition threshold beliefEvent)
    (hreport : ∀ other ∈ beliefEvent,
      posterior prior partition reportEvent other = report) :
    posterior prior partition reportEvent state = report := by
  obtain ⟨other, hcell⟩ := PBelief_cell_inter_nonempty
    prior partition hthreshold hstate
  exact (posterior_eq_of_mem_cell prior partition reportEvent state other hcell.1).trans
    (hreport other hcell.2)

private theorem commonPBelief_atom_real_arith
    {conditional share report threshold remainder : ℝ}
    (hconditional0 : 0 ≤ conditional) (hconditional1 : conditional ≤ 1)
    (hshare1 : share ≤ 1) (hthreshold : threshold ≤ share)
    (hremainder0 : 0 ≤ remainder)
    (hremainder1 : remainder ≤ 1 - share)
    (heq : report = conditional * share + remainder) :
    |conditional - report| ≤ 1 - threshold := by
  have hshare0 : (0 : ℝ) ≤ 1 - share := by linarith
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;>
    nlinarith [mul_le_mul_of_nonneg_right hconditional1 hshare0,
      mul_nonneg hconditional0 hshare0]

private theorem commonPBelief_core_bound
    (prior : PMF Ω)
    (partition : Setoid Ω)
    {threshold report : ℝ} {witness reportEvent : Set Ω}
    (hmassWitness : 0 < eventMass prior witness)
    (hevident : witness ⊆ PBelief prior partition threshold witness)
    (hreports : ∀ state ∈ witness,
      posterior prior partition reportEvent state = report) :
    |report - eventMass prior (witness ∩ reportEvent) /
        eventMass prior witness| ≤ 1 - threshold := by
  let indicatorWitness := eventIndicator witness
  let indicatorReport := eventIndicator (witness ∩ reportEvent)
  let difference : Ω → ℝ := fun state =>
    report * indicatorWitness state - indicatorReport state
  let bound : Ω → ℝ := fun state => (1 - threshold) * indicatorWitness state
  have hI : PayoffIntegrable prior indicatorWitness :=
    eventIndicator_integrable prior witness
  have hR : PayoffIntegrable prior indicatorReport :=
    eventIndicator_integrable prior (witness ∩ reportEvent)
  have hD : PayoffIntegrable prior difference := by
    exact payoffIntegrable_sub (payoffIntegrable_const_mul hI) hR
  have hB : PayoffIntegrable prior bound :=
    payoffIntegrable_const_mul hI
  have hDneg : PayoffIntegrable prior (fun state => -difference state) :=
    payoffIntegrable_neg hD
  have hboundFiber : ∀ b (hb : b ∈ (PMF.map (observation partition) prior).support),
      |expect (fiberPosterior prior (observation partition) b hb) difference
        (payoffIntegrable_fiberPosterior prior (observation partition)
          difference hD b hb)| ≤
      expect (fiberPosterior prior (observation partition) b hb) bound
        (payoffIntegrable_fiberPosterior prior (observation partition)
          bound hB b hb) := by
    intro b hb
    let conditional := fiberPosterior prior (observation partition) b hb
    have hconditionalSupport := fiberPosterior_support prior
      (observation partition) b hb
    let share := eventMass conditional witness
    let remainder := eventMass conditional (reportEvent \ witness)
    let ratio := eventMass conditional (witness ∩ reportEvent) / share
    have hshareNonneg : 0 ≤ share := eventMass_nonneg conditional witness
    have hshareLe : share ≤ 1 := by
      simpa only [share, eventMass, ENNReal.toReal_one] using
        ENNReal.toReal_mono ENNReal.one_ne_top
        (outerMeasure_le_one conditional witness)
    by_cases hsharePos : 0 < share
    · obtain ⟨state, hstateWitness, hstateSupport⟩ :=
        (eventMass_pos_iff_support conditional witness).1 hsharePos
      have hstateSupport' := hstateSupport
      rw [hconditionalSupport] at hstateSupport'
      have hstatePrior := hstateSupport'.2
      have hcell : state ∈ cell partition state := partition.refl state
      have hposteriorWitness := posterior_eq_fiberPosterior_expect
        prior partition witness state ⟨state, hcell, hstatePrior⟩
      have hposteriorReport := posterior_eq_fiberPosterior_expect
        prior partition reportEvent state ⟨state, hcell, hstatePrior⟩
      have hobservation : observation partition state = b := hstateSupport'.1
      have hconditionalEq : conditional =
          fiberPosterior prior (observation partition)
            (observation partition state) (by
              rw [hobservation]
              exact hb) := by
        dsimp [conditional]
        cases hobservation
        rfl
      have hconditionalWitness : share =
          posterior prior partition witness state := by
        calc
          share = expect conditional (eventIndicator witness)
              (eventIndicator_integrable conditional witness) :=
            (eventMass_indicator conditional witness).symm
          _ = expect (fiberPosterior prior (observation partition)
              (observation partition state) (by
                rw [hobservation]
                exact hb)) (eventIndicator witness)
              (eventIndicator_integrable _ witness) := by
            rw [hconditionalEq]
          _ = posterior prior partition witness state :=
            hposteriorWitness.symm
      have hthreshold : threshold ≤ share := by
        rw [hconditionalWitness]
        exact hevident hstateWitness
      have hconditionalReport :
          eventMass conditional reportEvent = report := by
        calc
          eventMass conditional reportEvent =
              expect conditional (eventIndicator reportEvent)
                (eventIndicator_integrable conditional reportEvent) :=
            (eventMass_indicator conditional reportEvent).symm
          _ = posterior prior partition reportEvent state := by
            rw [hconditionalEq]
            exact hposteriorReport.symm
          _ = report := hreports state hstateWitness
      have hreportBound : 0 ≤ report ∧ report ≤ 1 := by
        have hmass := eventMass_nonneg conditional reportEvent
        have hmass' : eventMass conditional reportEvent ≤ 1 := by
          simpa only [eventMass, ENNReal.toReal_one] using
            ENNReal.toReal_mono ENNReal.one_ne_top
            (outerMeasure_le_one conditional reportEvent)
        rw [hconditionalReport] at hmass hmass'
        exact ⟨hmass, hmass'⟩
      have hratio0 : 0 ≤ ratio :=
        div_nonneg (eventMass_nonneg conditional _) hshareNonneg
      have hratio1 : ratio ≤ 1 := by
        apply (div_le_one hsharePos).2
        exact eventMass_mono conditional (by
          intro other hother
          exact hother.1)
      have hremainder0 : 0 ≤ remainder :=
        eventMass_nonneg conditional _
      have houtside : remainder ≤ 1 - share := by
        have hcompl : eventMass conditional (Set.univ \ witness) = 1 - share := by
          have huniv : eventMass conditional Set.univ = 1 := by
            unfold eventMass
            rw [PMF.toOuterMeasure_apply]
            simp [Set.indicator, conditional.tsum_coe]
          have hdecomp := eventMass_inter_sdiff conditional Set.univ witness
          have hdecomp' : 1 = share +
              eventMass conditional (Set.univ \ witness) := by
            rw [huniv] at hdecomp
            simpa [share, Set.univ_inter] using hdecomp
          linarith [hdecomp']
        exact le_trans (eventMass_mono conditional
          (smaller := reportEvent \ witness)
          (larger := Set.univ \ witness) (by
          intro other hother
          exact ⟨Set.mem_univ other, hother.2⟩)) (by rw [hcompl])
      have heq : report = ratio * share + remainder := by
        have hsplit' : eventMass conditional reportEvent =
            eventMass conditional (witness ∩ reportEvent) + remainder := by
          simpa [remainder, Set.inter_comm] using
            eventMass_inter_sdiff conditional reportEvent witness
        calc
          report = eventMass conditional reportEvent := hconditionalReport.symm
          _ = eventMass conditional (witness ∩ reportEvent) + remainder := hsplit'
          _ = ratio * share + remainder := by
            dsimp [ratio, share]
            rw [div_mul_cancel₀ _ (ne_of_gt hsharePos)]
      have hatom := commonPBelief_atom_real_arith hratio0 hratio1
        hshareLe hthreshold hremainder0 houtside heq
      have hdiffEval : expect conditional difference
          (payoffIntegrable_fiberPosterior _ _ difference hD b hb) =
          share * (report - ratio) := by
        calc
          expect conditional difference
              (payoffIntegrable_fiberPosterior _ _ difference hD b hb) =
              report * expect conditional indicatorWitness
                (eventIndicator_integrable conditional witness) -
                expect conditional indicatorReport
                  (eventIndicator_integrable conditional
                    (witness ∩ reportEvent)) := by
            dsimp [difference, indicatorWitness, indicatorReport]
            rw [expect_sub (payoffIntegrable_const_mul
              (eventIndicator_integrable conditional witness))
              (eventIndicator_integrable conditional
                (witness ∩ reportEvent)),
              expect_const_mul (eventIndicator_integrable conditional witness)]
          _ = report * share - eventMass conditional
                (witness ∩ reportEvent) := by
            rw [eventMass_indicator, eventMass_indicator]
          _ = share * (report - ratio) := by
            dsimp [ratio, share]
            rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hsharePos)]
            ring
      have hboundEval : expect conditional bound
          (payoffIntegrable_fiberPosterior _ _ bound hB b hb) =
          (1 - threshold) * share := by
        calc
          expect conditional bound
              (payoffIntegrable_fiberPosterior _ _ bound hB b hb) =
              (1 - threshold) * expect conditional indicatorWitness
                (eventIndicator_integrable conditional witness) := by
            dsimp [bound, indicatorWitness]
            exact expect_const_mul (eventIndicator_integrable conditional witness)
          _ = (1 - threshold) * share := by rw [eventMass_indicator]
      rw [hdiffEval, hboundEval, abs_mul, abs_of_nonneg hshareNonneg]
      rw [abs_sub_comm] at hatom
      nlinarith
    · have hshareZero : share = 0 :=
        le_antisymm (le_of_not_gt hsharePos) hshareNonneg
      have hintersectionZero :
          eventMass conditional (witness ∩ reportEvent) = 0 := by
        apply le_antisymm
        · exact eventMass_mono conditional Set.inter_subset_left |> fun h =>
            le_trans h (le_of_eq hshareZero)
        · exact eventMass_nonneg conditional _
      have hdiffEval : expect conditional difference
          (payoffIntegrable_fiberPosterior _ _ difference hD b hb) = 0 := by
        calc
          expect conditional difference
              (payoffIntegrable_fiberPosterior _ _ difference hD b hb) =
              report * share - eventMass conditional
                (witness ∩ reportEvent) := by
            dsimp [difference, indicatorWitness, indicatorReport]
            rw [expect_sub (payoffIntegrable_const_mul
              (eventIndicator_integrable conditional witness))
              (eventIndicator_integrable conditional
                (witness ∩ reportEvent)),
              expect_const_mul (eventIndicator_integrable conditional witness),
              eventMass_indicator, eventMass_indicator]
          _ = 0 := by rw [hshareZero, hintersectionZero]; ring
      have hboundEval : expect conditional bound
          (payoffIntegrable_fiberPosterior _ _ bound hB b hb) = 0 := by
        calc
          expect conditional bound
              (payoffIntegrable_fiberPosterior _ _ bound hB b hb) =
              (1 - threshold) * share := by
            dsimp [bound, indicatorWitness]
            rw [expect_const_mul (eventIndicator_integrable conditional witness),
              eventMass_indicator]
          _ = 0 := by rw [hshareZero]; ring
      rw [hdiffEval, hboundEval]
      simp
  have hnegativeFiber : ∀ b (hb : b ∈
      (PMF.map (observation partition) prior).support),
      expect (fiberPosterior prior (observation partition) b hb)
        (fun state => -difference state)
        (payoffIntegrable_fiberPosterior _ _ (fun state => -difference state)
          hDneg b hb) ≤
      expect (fiberPosterior prior (observation partition) b hb) bound
        (payoffIntegrable_fiberPosterior _ _ bound hB b hb) := by
    intro b hb
    have hpositive := hboundFiber b hb
    have hnegative := (abs_le.mp hpositive).1
    calc
      expect (fiberPosterior prior (observation partition) b hb)
          (fun state => -difference state)
          (payoffIntegrable_fiberPosterior _ _ (fun state => -difference state)
            hDneg b hb) =
          -expect (fiberPosterior prior (observation partition) b hb)
            difference (payoffIntegrable_fiberPosterior _ _ difference hD b hb) := by
        rw [expect_neg (payoffIntegrable_fiberPosterior _ _ difference hD b hb)]
      _ ≤ expect (fiberPosterior prior (observation partition) b hb) bound
          (payoffIntegrable_fiberPosterior _ _ bound hB b hb) := by
        linarith [hnegative]
  have hpositiveFiber : ∀ b (hb : b ∈
      (PMF.map (observation partition) prior).support),
      expect (fiberPosterior prior (observation partition) b hb) difference
        (payoffIntegrable_fiberPosterior _ _ difference hD b hb) ≤
      expect (fiberPosterior prior (observation partition) b hb) bound
        (payoffIntegrable_fiberPosterior _ _ bound hB b hb) := by
    intro b hb
    exact (abs_le.mp (hboundFiber b hb)).2
  have hglobal := expect_fiberwise_le prior (observation partition)
    difference bound hD hB hpositiveFiber
  have hglobalNeg := expect_fiberwise_le prior (observation partition)
    (fun state => -difference state) bound hDneg hB hnegativeFiber
  have hglobalEval : expect prior difference hD =
      report * eventMass prior witness -
        eventMass prior (witness ∩ reportEvent) := by
    dsimp [difference, indicatorWitness, indicatorReport]
    rw [expect_sub (payoffIntegrable_const_mul
      (eventIndicator_integrable prior witness))
      (eventIndicator_integrable prior (witness ∩ reportEvent)),
      expect_const_mul (eventIndicator_integrable prior witness),
      eventMass_indicator, eventMass_indicator]
  have hboundEval : expect prior bound hB =
      (1 - threshold) * eventMass prior witness := by
    dsimp [bound, indicatorWitness]
    rw [expect_const_mul (eventIndicator_integrable prior witness),
      eventMass_indicator]
  have hscaledUpper := hglobal
  rw [hglobalEval, hboundEval] at hscaledUpper
  have hscaledLower := hglobalNeg
  rw [expect_neg hD, hglobalEval, hboundEval] at hscaledLower
  have hrewrite : report -
      eventMass prior (witness ∩ reportEvent) / eventMass prior witness =
    (report * eventMass prior witness -
      eventMass prior (witness ∩ reportEvent)) / eventMass prior witness := by
    field_simp [ne_of_gt hmassWitness]
  rw [hrewrite, abs_div, abs_of_pos hmassWitness]
  apply (div_le_iff₀ hmassWitness).2
  exact (abs_le).2 ⟨by linarith, by linarith⟩

/-- **Monderer--Samet approximate agreement.** Common `p`-belief that every
agent reports a fixed posterior makes any two reports differ by at most
`2 * (1 - p)`. -/
theorem commonPBelief_posterior_reports_close
    {agents : Type uι} {prior : PMF Ω}
    {partition : agents → Setoid Ω} {reportEvent : Set Ω} {state : Ω}
    {threshold : ℝ} (hthreshold : 0 < threshold)
    {report : agents → ℝ}
    (hcommon : CommonPBeliefAt prior partition threshold
      {world | ∀ agent, posterior prior (partition agent) reportEvent world =
        report agent} state) :
    ∀ first second, |report first - report second| ≤ 2 * (1 - threshold) := by
  obtain ⟨witness, hstate, hevident, hbelief⟩ := hcommon
  intro first second
  have hmassWitness : 0 < eventMass prior witness := by
    have hpositive := PBelief_cell_inter_mass_pos prior (partition first)
      hthreshold (hevident first hstate)
    have hmono : eventMass prior (witness ∩ cell (partition first) state) ≤
        eventMass prior witness :=
      eventMass_mono prior (by intro world hworld; exact hworld.1)
    exact lt_of_lt_of_le hpositive
      hmono
  have hfirstBound := commonPBelief_core_bound prior (partition first)
    hmassWitness (hevident first) (by
      intro world hworld
      exact posterior_eq_of_mem_PBelief_const prior (partition first)
        hthreshold (hbelief hworld first) (by
          intro other hother
          exact hother first))
  have hsecondBound := commonPBelief_core_bound prior (partition second)
    hmassWitness (hevident second) (by
      intro world hworld
      exact posterior_eq_of_mem_PBelief_const prior (partition second)
        hthreshold (hbelief hworld second) (by
          intro other hother
          exact hother second))
  rw [abs_sub_comm] at hsecondBound
  have htriangle := abs_sub_le (report first)
    (eventMass prior (witness ∩ reportEvent) / eventMass prior witness)
    (report second)
  linarith

end GameTheory.Epistemic
