/-
# Welfare-maximizing knapsack mechanism

Mechanism and equilibrium semantics reuse the canonical auction report,
profile update, VCG, and Nash surfaces.
-/

import GameTheory.Mechanism.Knapsack.Basic
import GameTheory.Mechanism.Groves

noncomputable section

namespace GameTheory.Mechanism.Knapsack

open scoped BigOperators

variable {Agent : Type} [Fintype Agent] [DecidableEq Agent]

/-- Welfare maximization over the full finite player universe. -/
noncomputable def allocationRule (A : Data Agent) (hcap : 0 ≤ A.capacity)
    (bids : GameTheory.Mechanism.Auction.BidProfile Agent) : Finset Agent :=
  welfareMaximizer A bids Finset.univ hcap

/-- The certified allocation rule used as the VCG outcome. -/
noncomputable def feasibleAllocationRule (A : Data Agent) (hcap : 0 ≤ A.capacity)
    (bids : GameTheory.Mechanism.Auction.BidProfile Agent) : FeasibleAllocation A :=
  ⟨allocationRule A hcap bids,
    welfareMaximizer_feasible A bids Finset.univ hcap⟩

omit [Fintype Agent] in
private theorem welfare_update_of_mem
    (bids : GameTheory.Mechanism.Auction.BidProfile Agent) (who : Agent)
    (bid : ℝ) {selected : Finset Agent} (hmem : who ∈ selected) :
    welfare (Profile.update bids who bid) selected =
      welfare bids selected + (bid - bids who) := by
  unfold welfare aggregate
  rw [← Finset.add_sum_erase selected _ hmem,
    ← Finset.add_sum_erase selected _ hmem]
  have hothers :
      (∑ other ∈ selected.erase who, Profile.update bids who bid other) =
        ∑ other ∈ selected.erase who, bids other := by
    apply Finset.sum_congr rfl
    intro other hother
    exact Profile.update_of_ne _ _ (Finset.mem_erase.mp hother).1
  rw [hothers]
  simp only [Profile.update_same]
  ring

omit [Fintype Agent] in
private theorem welfare_update_of_not_mem
    (bids : GameTheory.Mechanism.Auction.BidProfile Agent) (who : Agent)
    (bid : ℝ) {selected : Finset Agent} (hnotmem : who ∉ selected) :
    welfare (Profile.update bids who bid) selected = welfare bids selected := by
  unfold welfare aggregate
  apply Finset.sum_congr rfl
  intro other hother
  have hne : other ≠ who := by
    intro heq
    subst other
    exact hnotmem hother
  exact Profile.update_of_ne _ _ hne

omit [Fintype Agent] in
/-- Updating one reported value changes welfare by exactly that coordinate's
contribution when the agent is selected. -/
theorem welfare_update
    (bids : GameTheory.Mechanism.Auction.BidProfile Agent) (who : Agent)
    (bid : ℝ) (selected : Finset Agent) :
    welfare (Profile.update bids who bid) selected =
      welfare bids selected + if who ∈ selected then bid - bids who else 0 := by
  by_cases hmem : who ∈ selected
  · simpa [hmem] using welfare_update_of_mem bids who bid hmem
  · simp [hmem, welfare_update_of_not_mem bids who bid hmem]

/-- Raising one report cannot remove an agent selected by the chosen welfare
maximizer, even though ties are resolved by arbitrary classical choice. -/
theorem mem_allocationRule_of_le (A : Data Agent) (hcap : 0 ≤ A.capacity)
    (bids : GameTheory.Mechanism.Auction.BidProfile Agent) (who : Agent)
    (bid : ℝ) (hle : bids who ≤ bid)
    (hselected : who ∈ allocationRule A hcap bids) :
    who ∈ allocationRule A hcap (Profile.update bids who bid) := by
  by_cases heq : bids who = bid
  · subst bid
    simpa [Profile.update_eq_self] using hselected
  · have hlt : bids who < bid := lt_of_le_of_ne hle heq
    by_contra hnotSelected
    let low := allocationRule A hcap bids
    let high := allocationRule A hcap (Profile.update bids who bid)
    have hlowMem : low ∈ feasibleAllocations A Finset.univ := by
      exact welfareMaximizer_mem A bids Finset.univ hcap
    have hhighMem : high ∈ feasibleAllocations A Finset.univ := by
      exact welfareMaximizer_mem A (Profile.update bids who bid) Finset.univ hcap
    have hlowOptimal : welfare bids high ≤ welfare bids low :=
      welfareMaximizer_ge A bids Finset.univ hcap hhighMem
    have hhighOptimal :
        welfare (Profile.update bids who bid) low ≤
          welfare (Profile.update bids who bid) high :=
      welfareMaximizer_ge A (Profile.update bids who bid) Finset.univ hcap hlowMem
    have hwhoLow : who ∈ low := by simpa [low, allocationRule] using hselected
    have hwhoHigh : who ∉ high := by
      simpa [high, allocationRule] using hnotSelected
    rw [welfare_update_of_mem bids who bid hwhoLow,
      welfare_update_of_not_mem bids who bid hwhoHigh] at hhighOptimal
    linarith

/-- The zero/one allocation coordinate is monotone in an agent's report. -/
theorem allocationRule_monotone (A : Data Agent) (hcap : 0 ≤ A.capacity)
    (bids : GameTheory.Mechanism.Auction.BidProfile Agent) (who : Agent)
    (bid : ℝ) (hle : bids who ≤ bid) :
    indicator (allocationRule A hcap bids) who ≤
      indicator (allocationRule A hcap (Profile.update bids who bid)) who := by
  by_cases hselected : who ∈ allocationRule A hcap bids
  · have hselected' := mem_allocationRule_of_le A hcap bids who bid hle hselected
    simp [indicator, hselected, hselected']
  · by_cases hselected' :
        who ∈ allocationRule A hcap (Profile.update bids who bid)
    · simp [indicator, hselected, hselected']
    · simp [indicator, hselected, hselected']

/-- Welfare available after normalizing one bidder's report to zero. -/
noncomputable def pivotOffset (A : Data Agent) (hcap : 0 ≤ A.capacity)
    (who : Agent) (reports : GameTheory.Mechanism.Auction.BidProfile Agent) : ℝ :=
  maximalWelfare A (Profile.update reports who 0) Finset.univ hcap

/-- Canonical pivot-normalized Groves setup for the welfare-maximizing
knapsack allocation. -/
@[reducible]
noncomputable def vcgSetup (A : Data Agent) (hcap : 0 ≤ A.capacity) :
    GameTheory.Mechanism.GrovesSetup Agent where
  Θ := fun _ => ℝ
  Outcome := FeasibleAllocation A
  val := fun who report outcome => report * indicator outcome.1 who
  alloc := feasibleAllocationRule A hcap
  h := pivotOffset A hcap

/-- The selected feasible allocation maximizes reported welfare over the VCG
outcome space. -/
theorem vcgSetup_efficient (A : Data Agent) (hcap : 0 ≤ A.capacity) :
    (vcgSetup A hcap).IsEfficient := by
  intro reports outcome
  let selected : FeasibleAllocation A := outcome
  let bids : GameTheory.Mechanism.Auction.BidProfile Agent := reports
  have houtcome : selected.1 ∈ feasibleAllocations A Finset.univ := by
    classical
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr (by simp), selected.2⟩
  have hoptimal := welfareMaximizer_ge A bids Finset.univ hcap houtcome
  have hsum (chosen : Finset Agent) :
      (∑ who, if who ∈ chosen then reports who else 0) =
        welfare reports chosen := by
    unfold welfare aggregate
    conv_lhs =>
      rw [Finset.sum_ite_mem,
        Finset.inter_eq_right.mpr (Finset.subset_univ chosen)]
  dsimp only [vcgSetup, feasibleAllocationRule, allocationRule]
  simp only [indicator, mul_ite, mul_one, mul_zero]
  rw [hsum (welfareMaximizer A reports Finset.univ hcap), hsum outcome.1]
  simpa only [selected, bids] using hoptimal

/-- The pivot offset is independent of the bidder's own report. -/
theorem vcgSetup_offset_independent (A : Data Agent) (hcap : 0 ≤ A.capacity) :
    ∀ (who : Agent)
      (reports : GameTheory.Mechanism.Auction.BidProfile Agent)
      (replacement : ℝ),
      (vcgSetup A hcap).h who (Profile.update reports who replacement) =
        (vcgSetup A hcap).h who reports := by
  intro who reports replacement
  simp only [pivotOffset, Profile.update_idem]

/-- Under the pivot normalization, a bidder reporting zero is charged zero. -/
theorem vcgPayment_update_zero (A : Data Agent) (hcap : 0 ≤ A.capacity)
    (reports : GameTheory.Mechanism.Auction.BidProfile Agent) (who : Agent) :
    (vcgSetup A hcap).grovesPayment (Profile.update reports who 0) who = 0 := by
  simp only [GameTheory.Mechanism.GrovesSetup.grovesPayment, vcgSetup,
    pivotOffset, Profile.update_idem, feasibleAllocationRule, allocationRule]
  rw [sub_eq_zero]
  unfold maximalWelfare welfare aggregate
  simp only [indicator, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem]
  have hintersection :
      Finset.univ.erase who ∩
          welfareMaximizer A (Profile.update reports who 0) Finset.univ hcap =
        (welfareMaximizer A (Profile.update reports who 0) Finset.univ hcap).erase who := by
    ext other
    simp
  rw [hintersection]
  by_cases hselected :
      who ∈ welfareMaximizer A (Profile.update reports who 0) Finset.univ hcap
  · rw [← Finset.add_sum_erase _ _ hselected]
    simp only [Profile.update_same, zero_add]
  · rw [Finset.erase_eq_self.mpr hselected]

/-- Canonical VCG truthfulness gives ex-post Nash for the knapsack setup. -/
theorem vcgSetup_truthful_isExPostNash (A : Data Agent)
    (hcap : 0 ≤ A.capacity) :
    ∀ trueTypes : (vcgSetup A hcap).ReportProfile,
      IsNash ((vcgSetup A hcap).toUtilityGame trueTypes).form
        (euPreference ((vcgSetup A hcap).toUtilityGame trueTypes).utility)
        trueTypes :=
  (vcgSetup A hcap).truthfulStrategy_isExPostNash
    (vcgSetup_efficient A hcap) (vcgSetup_offset_independent A hcap)

/-- The welfare-maximizing pivot mechanism is DSIC through the canonical
quasilinear direct-mechanism predicate. -/
theorem vcgSetup_isDSIC (A : Data Agent) (hcap : 0 ≤ A.capacity) :
    (vcgSetup A hcap).toQuasiLinearMechanism.IsDSIC :=
  (vcgSetup A hcap).toQuasiLinearMechanism_isDSIC
    (vcgSetup_efficient A hcap) (vcgSetup_offset_independent A hcap)

end GameTheory.Mechanism.Knapsack
