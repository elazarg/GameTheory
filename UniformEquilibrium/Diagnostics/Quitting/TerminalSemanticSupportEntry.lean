/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerExactRoot
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEqualityStratum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSoloSpineOccupation

/-!
# Support entry from a minimum semantic solo row

Fix an interior solo-owner rate at which one inactive outsider is exactly
indifferent.  If the owner's reciprocal collision row is neutral and every
other inactive row is strict, continuity lets the tight outsider acquire a
small positive Quit rate while retaining exact root Nash at the same tail.

This local repair is impossible at a minimum semantic pair carrying positive
owner debt: a positive outsider hazard would contract the owner's deleted
survival below one.  Hence every such tight outsider satisfies the finite
alternative

* the owner's reciprocal collision increment is nonzero; or
* another inactive coordinate is simultaneously tight.

The second outcome is a concrete escalation from a two-coordinate entry seam
to a three-coordinate equality stratum.  The results construct one exact
fixed-tail root; they do not by themselves attach a return or compile a
uniform equilibrium.

The final global reduction retains the semantic edge which produces an
atomic solo row.  A counterexample therefore has either a positive minimum
all-Continue plateau, or an isolated-negative atomic solo edge between two
minimum carrier points.  The atomic hazard is split into pure Quit and an
interior case; in the interior case the edge also carries the finite
nonzero-collision-or-cotight boundary certificate.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

theorem continuous_gainValue_twoOwner_secondHazard
    (tail : Payoff ι) (owner entrant who : ι) (ownerRate : ℝ)
    (hne : owner ≠ entrant) :
    Continuous (fun entrantRate : ℝ =>
      gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant ownerRate entrantRate)
        who (tail who)) := by
  let x : ℝ → (ι → ℝ) := fun entrantRate =>
    quittingTwoOwnerHazard owner entrant ownerRate entrantRate
  have hx : Continuous x := by
    apply continuous_pi
    intro i
    by_cases hiOwner : i = owner
    · simpa [x, quittingTwoOwnerHazard, hiOwner] using
        (continuous_const : Continuous (fun _ : ℝ => ownerRate))
    · by_cases hiEntrant : i = entrant
      · simp only [x, quittingTwoOwnerHazard,
          quittingTwoOwnerLeadingVariation, hiEntrant, hne.symm,
          ↓reduceIte, Matrix.cons_val_one, Matrix.cons_val_zero]
        fun_prop
      · simp only [x, quittingTwoOwnerHazard,
          quittingTwoOwnerLeadingVariation, hiOwner, hiEntrant,
          ↓reduceIte]
        fun_prop
  change Continuous (fun entrantRate : ℝ =>
    gainValue (weightOfReward reward) (x entrantRate) who (tail who))
  unfold gainValue gammaValue sigmaValue excludedValue continueMassExcl
  fun_prop

theorem continuous_gainValue_twoOwner_firstHazard
    (tail : Payoff ι) (owner anchor who : ι) (hne : owner ≠ anchor) :
    Continuous (fun ownerRate : ℝ =>
      gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner anchor ownerRate 0)
        who (tail who)) := by
  have hcontinuous := continuous_gainValue_twoOwner_secondHazard
    (reward := reward) tail anchor owner who 0 hne.symm
  simpa only [quittingTwoOwnerHazard_swap anchor owner 0 _ hne.symm] using
    hcontinuous

theorem gainValue_twoOwner_first_fixedTail
    (tail : Payoff ι) (owner entrant : ι)
    (ownerRate entrantRate : ℝ) (hne : owner ≠ entrant) :
    gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant ownerRate entrantRate)
        owner (tail owner) =
      (1 - entrantRate) *
          reward (quittingSingletonTerminal owner) owner +
        entrantRate * reward (quittingPairJoinTerminal owner entrant) owner -
        (entrantRate * reward (quittingSingletonTerminal entrant) owner +
          (1 - entrantRate) * tail owner) := by
  unfold gainValue gammaValue
  rw [sigmaValue_twoOwner_first owner entrant ownerRate entrantRate hne,
    excludedValue_twoOwner_first owner entrant ownerRate entrantRate hne,
    continueMassExcl_twoOwner_first owner entrant ownerRate entrantRate hne]

theorem gainValue_twoOwner_second_fixedTail
    (tail : Payoff ι) (owner entrant : ι)
    (ownerRate entrantRate : ℝ) (hne : owner ≠ entrant) :
    gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant ownerRate entrantRate)
        entrant (tail entrant) =
      (1 - ownerRate) *
          reward (quittingSingletonTerminal entrant) entrant +
        ownerRate * reward (quittingPairJoinTerminal entrant owner) entrant -
        (ownerRate * reward (quittingSingletonTerminal owner) entrant +
          (1 - ownerRate) * tail entrant) := by
  unfold gainValue gammaValue
  rw [sigmaValue_twoOwner_second owner entrant ownerRate entrantRate hne,
    excludedValue_twoOwner_second owner entrant ownerRate entrantRate hne,
    continueMassExcl_twoOwner_second owner entrant ownerRate entrantRate hne]

/-- Starting from any interior feasible solo-owner rate, an outsider which
is profitable at rate zero selects a first positive feasible rate.  Every
outsider is nonprofitable there and at least one outsider is exactly tight;
the pinned owner remains exactly indifferent. -/
theorem exists_positive_minimalSoloRate_tight_outsider
    (tail : Payoff ι) (owner anchor : ι) (displayedRate : ℝ)
    (hne : owner ≠ anchor)
    (hdisplayedPos : 0 < displayedRate)
    (hownerPin : tail owner =
      reward (quittingSingletonTerminal owner) owner)
    (hdisplayedComplementary : IsExactRowComplementary
      (quittingTwoOwnerHazard owner anchor displayedRate 0)
      (fun who => gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner anchor displayedRate 0)
        who (tail who)))
    (hanchorProfitable : 0 <
      gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner anchor 0 0)
        anchor (tail anchor)) :
    ∃ rate entrant, 0 < rate ∧ rate ≤ displayedRate ∧
      entrant ≠ owner ∧
      IsExactRowComplementary
        (quittingTwoOwnerHazard owner anchor rate 0)
        (fun who => gainValue (weightOfReward reward)
          (quittingTwoOwnerHazard owner anchor rate 0)
          who (tail who)) ∧
      gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner anchor rate 0)
        entrant (tail entrant) = 0 := by
  let gain : ℝ → ι → ℝ := fun rate who =>
    gainValue (weightOfReward reward)
      (quittingTwoOwnerHazard owner anchor rate 0) who (tail who)
  let feasible : Set ℝ := {rate |
    rate ∈ Set.Icc 0 displayedRate ∧
      ∀ who, who ≠ owner → gain rate who ≤ 0}
  have hgainContinuous : ∀ who, Continuous (fun rate => gain rate who) := by
    intro who
    exact continuous_gainValue_twoOwner_firstHazard
      (reward := reward) tail owner anchor who hne
  have hrowsClosed : IsClosed {rate : ℝ |
      ∀ who, who ≠ owner → gain rate who ≤ 0} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro who
    apply isClosed_iInter
    intro _hwho
    change IsClosed ((fun rate => gain rate who) ⁻¹' Set.Iic 0)
    exact isClosed_Iic.preimage (hgainContinuous who)
  have hfeasibleCompact : IsCompact feasible := by
    have heq : feasible = Set.Icc 0 displayedRate ∩
        {rate : ℝ | ∀ who, who ≠ owner → gain rate who ≤ 0} := by
      ext rate
      rfl
    rw [heq]
    exact isCompact_Icc.inter_right hrowsClosed
  have hdisplayedFeasible : displayedRate ∈ feasible := by
    refine ⟨⟨hdisplayedPos.le, le_rfl⟩, ?_⟩
    intro who hwho
    have hzero : quittingTwoOwnerHazard owner anchor displayedRate 0 who = 0 := by
      simp [quittingTwoOwnerHazard, quittingTwoOwnerLeadingVariation, hwho]
    exact (hdisplayedComplementary who).2 (by rw [hzero]; norm_num)
  obtain ⟨rate, hrateFeasible, hrateMin⟩ :=
    hfeasibleCompact.exists_isMinOn
      ⟨displayedRate, hdisplayedFeasible⟩ continuous_id.continuousOn
  have hrateNonneg : 0 ≤ rate := hrateFeasible.1.1
  have hrateLe : rate ≤ displayedRate := hrateFeasible.1.2
  have hratePos : 0 < rate := by
    rcases eq_or_lt_of_le hrateNonneg with hzero | hpos
    · subst rate
      have := hrateFeasible.2 anchor hne.symm
      exact absurd this (not_le.mpr hanchorProfitable)
    · exact hpos
  have htight : ∃ entrant, entrant ≠ owner ∧ gain rate entrant = 0 := by
    by_contra hnot
    push Not at hnot
    have hstrict : ∀ who, who ≠ owner → gain rate who < 0 := by
      intro who hwho
      exact lt_of_le_of_ne (hrateFeasible.2 who hwho) (hnot who hwho)
    have hstrictEventually : ∀ᶠ candidate in 𝓝 rate,
        ∀ who, who ≠ owner → gain candidate who < 0 := by
      rw [Filter.eventually_all]
      intro who
      by_cases hwho : who = owner
      · exact Filter.Eventually.of_forall fun _ hneWho =>
          (hneWho hwho).elim
      · exact ((hgainContinuous who).continuousAt.eventually_lt
          continuousAt_const (hstrict who hwho)).mono
            (fun _ hlt _ => hlt)
    have hpositiveEventually : ∀ᶠ candidate in 𝓝 rate,
        0 < candidate :=
      continuousAt_const.eventually_lt continuousAt_id hratePos
    have hleftEvent : ∀ᶠ candidate : ℝ in 𝓝[<] rate,
        candidate < rate := self_mem_nhdsWithin
    obtain ⟨candidate, hcandidate, hcandidateLt⟩ :=
      ((((hstrictEventually.and hpositiveEventually).filter_mono
        nhdsWithin_le_nhds).and hleftEvent).exists)
    have hcandidateFeasible : candidate ∈ feasible := by
      refine ⟨⟨hcandidate.2.le,
        (hcandidateLt.le.trans hrateLe)⟩, ?_⟩
      intro who hwho
      exact (hcandidate.1 who hwho).le
    have hmin := hrateMin hcandidateFeasible
    exact (not_lt_of_ge hmin) hcandidateLt
  obtain ⟨entrant, hentrantNe, hentrantTight⟩ := htight
  have hownerGain : gain rate owner = 0 := by
    dsimp only [gain]
    rw [gainValue_twoOwner_first_fixedTail tail owner anchor rate 0 hne,
      hownerPin]
    ring
  have hcomplementary : IsExactRowComplementary
      (quittingTwoOwnerHazard owner anchor rate 0)
      (fun who => gain rate who) := by
    intro who
    by_cases hwho : who = owner
    · subst who
      change (0 < quittingTwoOwnerHazard owner anchor rate 0 owner →
          0 ≤ gain rate owner) ∧
        (quittingTwoOwnerHazard owner anchor rate 0 owner < 1 →
          gain rate owner ≤ 0)
      rw [hownerGain]
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
    · have hzero : quittingTwoOwnerHazard owner anchor rate 0 who = 0 := by
        simp [quittingTwoOwnerHazard, quittingTwoOwnerLeadingVariation, hwho]
      rw [hzero]
      exact ⟨fun hpos => (lt_irrefl 0 hpos).elim,
        fun _ => hrateFeasible.2 who hwho⟩
  exact ⟨rate, entrant, hratePos, hrateLe, hentrantNe,
    hcomplementary, hentrantTight⟩

/-- A tight outsider can be activated at fixed tail whenever the owner's
reciprocal collision row is neutral and every remaining inactive row is
strict. -/
theorem exists_exact_twoOwnerSupportEntry_of_neutral_isolated
    (tail : Payoff ι) (owner entrant : ι) (ownerRate : ℝ)
    (hne : owner ≠ entrant)
    (hownerRatePos : 0 < ownerRate) (hownerRateLt : ownerRate < 1)
    (hownerPin : tail owner =
      reward (quittingSingletonTerminal owner) owner)
    (hownerNeutral :
      quittingActiveMixingCollisionIncrement reward owner entrant = 0)
    (hentrantTight :
      gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant ownerRate 0)
        entrant (tail entrant) = 0)
    (hotherStrict : ∀ who, who ≠ owner → who ≠ entrant →
      gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant ownerRate 0)
        who (tail who) < 0) :
    ∃ entrantRate : ℝ, ∃ root : ι → PMF Bool,
      0 < entrantRate ∧ entrantRate < 1 ∧
      hazardOfRoot root =
        quittingTwoOwnerHazard owner entrant ownerRate entrantRate ∧
      IsεQuittingRootNash reward tail 0 root := by
  have hotherEventually : ∀ᶠ entrantRate in 𝓝 (0 : ℝ),
      ∀ who, who ≠ owner → who ≠ entrant →
        gainValue (weightOfReward reward)
          (quittingTwoOwnerHazard owner entrant ownerRate entrantRate)
          who (tail who) < 0 := by
    rw [Filter.eventually_all]
    intro who
    by_cases hwhoOwner : who = owner
    · exact Filter.Eventually.of_forall fun _ hneOwner _ =>
        (hneOwner hwhoOwner).elim
    · by_cases hwhoEntrant : who = entrant
      · exact Filter.Eventually.of_forall fun _ _ hneEntrant =>
          (hneEntrant hwhoEntrant).elim
      · have hzero := hotherStrict who hwhoOwner hwhoEntrant
        exact ((continuous_gainValue_twoOwner_secondHazard
          (reward := reward) tail owner entrant who ownerRate hne).continuousAt
            |>.eventually_lt continuousAt_const hzero).mono
          (fun _ hlt _ _ => hlt)
  have hltOne : ∀ᶠ entrantRate in 𝓝 (0 : ℝ), entrantRate < 1 :=
    continuousAt_id.eventually_lt continuousAt_const zero_lt_one
  have hpositiveEvent : ∀ᶠ entrantRate : ℝ in 𝓝[>] (0 : ℝ),
      0 < entrantRate := self_mem_nhdsWithin
  obtain ⟨entrantRate, hproperties, hentrantRatePos⟩ :=
    (((hotherEventually.and hltOne).filter_mono nhdsWithin_le_nhds).and
      hpositiveEvent).exists
  have hentrantRateLt : entrantRate < 1 := hproperties.2
  let hazard := quittingTwoOwnerHazard owner entrant ownerRate entrantRate
  have hhazardNonneg : ∀ who, 0 ≤ hazard who := by
    intro who
    by_cases hwhoOwner : who = owner
    · simp [hazard, quittingTwoOwnerHazard, hwhoOwner, hownerRatePos.le]
    · by_cases hwhoEntrant : who = entrant
      · subst who
        change 0 ≤ quittingTwoOwnerHazard owner entrant ownerRate entrantRate entrant
        rw [quittingTwoOwnerHazard_second owner entrant ownerRate entrantRate hne]
        exact hentrantRatePos.le
      · simp [hazard, quittingTwoOwnerHazard,
          quittingTwoOwnerLeadingVariation, hwhoOwner, hwhoEntrant]
  have hhazardLeOne : ∀ who, hazard who ≤ 1 := by
    intro who
    by_cases hwhoOwner : who = owner
    · simp [hazard, quittingTwoOwnerHazard, hwhoOwner, hownerRateLt.le]
    · by_cases hwhoEntrant : who = entrant
      · subst who
        change quittingTwoOwnerHazard owner entrant ownerRate entrantRate entrant ≤ 1
        rw [quittingTwoOwnerHazard_second owner entrant ownerRate entrantRate hne]
        exact hentrantRateLt.le
      · simp [hazard, quittingTwoOwnerHazard,
          quittingTwoOwnerLeadingVariation, hwhoOwner, hwhoEntrant]
  let root := rootOfHazard hazard hhazardNonneg hhazardLeOne
  have hownerGain : gainValue (weightOfReward reward) hazard owner
      (tail owner) = 0 := by
    rw [gainValue_twoOwner_first_fixedTail tail owner entrant ownerRate
      entrantRate hne, hownerPin]
    unfold quittingActiveMixingCollisionIncrement at hownerNeutral
    have hcollision := sub_eq_zero.mp hownerNeutral
    rw [hcollision]
    ring
  have hentrantGain : gainValue (weightOfReward reward) hazard entrant
      (tail entrant) = 0 := by
    rw [gainValue_twoOwner_second_fixedTail tail owner entrant ownerRate
      entrantRate hne]
    rw [gainValue_twoOwner_second_fixedTail tail owner entrant ownerRate 0 hne]
      at hentrantTight
    exact hentrantTight
  have hcomplementary : IsExactRowComplementary hazard
      (fun who => gainValue (weightOfReward reward) hazard who (tail who)) := by
    intro who
    by_cases hwhoOwner : who = owner
    · subst who
      change (0 < hazard owner → 0 ≤ gainValue (weightOfReward reward)
          hazard owner (tail owner)) ∧
        (hazard owner < 1 → gainValue (weightOfReward reward)
          hazard owner (tail owner) ≤ 0)
      rw [hownerGain]
      exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
    · by_cases hwhoEntrant : who = entrant
      · subst who
        change (0 < hazard entrant → 0 ≤ gainValue (weightOfReward reward)
            hazard entrant (tail entrant)) ∧
          (hazard entrant < 1 → gainValue (weightOfReward reward)
            hazard entrant (tail entrant) ≤ 0)
        rw [hentrantGain]
        exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
      · have hzero : hazard who = 0 := by
          simp [hazard, quittingTwoOwnerHazard,
            quittingTwoOwnerLeadingVariation, hwhoOwner, hwhoEntrant]
        have hstrict := hproperties.1 who hwhoOwner hwhoEntrant
        rw [hzero]
        exact ⟨fun hpos => (lt_irrefl 0 hpos).elim,
          fun _ => hstrict.le⟩
  refine ⟨entrantRate, root, hentrantRatePos, hentrantRateLt, ?_, ?_⟩
  · exact hazardOfRoot_rootOfHazard hazard hhazardNonneg hhazardLeOne
  · apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).mp
    apply (isExactRowComplementary_hazardOfRoot_iff reward tail root).mp
    simpa [root, hazardOfRoot_rootOfHazard] using hcomplementary

/-- At a minimum positive-debt semantic tail, a tight inactive outsider
cannot be both collision-neutral for the debtor and isolated among the tight
inactive rows.  Otherwise the outsider enters support at a small positive
rate, contradicting exact unit deleted survival of the positive debt. -/
theorem collision_nonzero_or_exists_cotight_outsider_of_minimumSemanticDebt
    (pair : QuittingTerminalSemanticPair ι)
    (owner entrant : ι) (ownerRate : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hownerDebt : 0 < quittingTerminalSemanticDebt pair owner)
    (hne : owner ≠ entrant)
    (hownerRatePos : 0 < ownerRate) (hownerRateLt : ownerRate < 1)
    (hownerPin : pair.1 owner =
      reward (quittingSingletonTerminal owner) owner)
    (hsoloComplementary : IsExactRowComplementary
      (quittingTwoOwnerHazard owner entrant ownerRate 0)
      (fun who => gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant ownerRate 0)
        who (pair.1 who)))
    (hentrantTight :
      gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant ownerRate 0)
        entrant (pair.1 entrant) = 0) :
    quittingActiveMixingCollisionIncrement reward owner entrant ≠ 0 ∨
      ∃ who, who ≠ owner ∧ who ≠ entrant ∧
        gainValue (weightOfReward reward)
          (quittingTwoOwnerHazard owner entrant ownerRate 0)
          who (pair.1 who) = 0 := by
  by_cases hcollision :
      quittingActiveMixingCollisionIncrement reward owner entrant = 0
  · right
    by_contra hnot
    push Not at hnot
    have hotherStrict : ∀ who, who ≠ owner → who ≠ entrant →
        gainValue (weightOfReward reward)
          (quittingTwoOwnerHazard owner entrant ownerRate 0)
          who (pair.1 who) < 0 := by
      intro who hwhoOwner hwhoEntrant
      have hzeroHazard :
          quittingTwoOwnerHazard owner entrant ownerRate 0 who = 0 :=
        quittingTwoOwnerHazard_eq_zero_of_ne owner entrant who ownerRate 0
          hwhoOwner hwhoEntrant
      have hnonpos :=
        (hsoloComplementary who).2 (by rw [hzeroHazard]; norm_num)
      exact lt_of_le_of_ne hnonpos (hnot who hwhoOwner hwhoEntrant)
    obtain ⟨entrantRate, root, hentrantRatePos, _hentrantRateLt,
        hrootHazard, hnash⟩ :=
      exists_exact_twoOwnerSupportEntry_of_neutral_isolated
        (reward := reward) pair.1 owner entrant ownerRate hne
          hownerRatePos hownerRateLt hownerPin hcollision hentrantTight
          hotherStrict
    have hzero :=
      quittingTerminalSemantic_minimum_positiveDebt_opponents_quit_eq_zero
        reward pair root hM hreward hpair hminimum hnash hownerDebt hne.symm
    have hpositive : 0 < (root entrant true).toReal := by
      change 0 < hazardOfRoot root entrant
      rw [hrootHazard,
        quittingTwoOwnerHazard_second owner entrant ownerRate entrantRate hne]
      exact hentrantRatePos
    linarith
  · exact Or.inl hcollision

/-- **First feasible solo boundary at the minimum semantic stratum.**  An
interior exact solo row which deters an outsider profitable at rate zero has
a positive first feasible rate with a tight outsider.  At a minimum
positive-debt tail that outsider either moves the owner's reciprocal
collision row, or belongs to a simultaneous multi-outsider equality seam. -/
theorem exists_minimalSoloBoundary_collision_nonzero_or_cotight
    (pair : QuittingTerminalSemanticPair ι)
    (owner anchor : ι) (displayedRate : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hownerDebt : 0 < quittingTerminalSemanticDebt pair owner)
    (hne : owner ≠ anchor)
    (hdisplayedPos : 0 < displayedRate)
    (hdisplayedLt : displayedRate < 1)
    (hownerPin : pair.1 owner =
      reward (quittingSingletonTerminal owner) owner)
    (hdisplayedComplementary : IsExactRowComplementary
      (quittingTwoOwnerHazard owner anchor displayedRate 0)
      (fun who => gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner anchor displayedRate 0)
        who (pair.1 who)))
    (hanchorProfitable : 0 <
      gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner anchor 0 0)
        anchor (pair.1 anchor)) :
    ∃ rate entrant, 0 < rate ∧ rate ≤ displayedRate ∧
      entrant ≠ owner ∧
      IsExactRowComplementary
        (quittingTwoOwnerHazard owner entrant rate 0)
        (fun who => gainValue (weightOfReward reward)
          (quittingTwoOwnerHazard owner entrant rate 0)
          who (pair.1 who)) ∧
      gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant rate 0)
        entrant (pair.1 entrant) = 0 ∧
      (quittingActiveMixingCollisionIncrement reward owner entrant ≠ 0 ∨
        ∃ who, who ≠ owner ∧ who ≠ entrant ∧
          gainValue (weightOfReward reward)
            (quittingTwoOwnerHazard owner entrant rate 0)
            who (pair.1 who) = 0) := by
  obtain ⟨rate, entrant, hratePos, hrateLe, hentrantNe,
      hcomplementary, hentrantTight⟩ :=
    exists_positive_minimalSoloRate_tight_outsider
      (reward := reward) pair.1 owner anchor displayedRate hne
        hdisplayedPos hownerPin hdisplayedComplementary hanchorProfitable
  have hhazard : quittingTwoOwnerHazard owner anchor rate 0 =
      quittingTwoOwnerHazard owner entrant rate 0 := by
    funext who
    by_cases hwho : who = owner
    · subst who
      simp
    · simp [quittingTwoOwnerHazard, quittingTwoOwnerLeadingVariation, hwho]
  have hcomplementary' : IsExactRowComplementary
      (quittingTwoOwnerHazard owner entrant rate 0)
      (fun who => gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant rate 0)
        who (pair.1 who)) := by
    rw [← hhazard]
    exact hcomplementary
  have hentrantTight' : gainValue (weightOfReward reward)
      (quittingTwoOwnerHazard owner entrant rate 0)
      entrant (pair.1 entrant) = 0 := by
    rw [← hhazard]
    exact hentrantTight
  have hrateLt : rate < 1 := hrateLe.trans_lt hdisplayedLt
  have hresidual :=
    collision_nonzero_or_exists_cotight_outsider_of_minimumSemanticDebt
      (reward := reward) pair owner entrant rate hM hreward hpair hminimum
        hownerDebt hentrantNe.symm hratePos hrateLt hownerPin
        hcomplementary' hentrantTight'
  exact ⟨rate, entrant, hratePos, hrateLe, hentrantNe,
    hcomplementary', hentrantTight', hresidual⟩

omit [Fintype ι] in
/-- Hazard-vector form of a concrete solo-stationary root.  The second
displayed owner is only a harmless coordinate used to reuse the two-owner
finite formulas. -/
theorem hazardOfRoot_soloStationaryRoot_eq_twoOwnerHazard
    (owner anchor : ι) (hazard : PMF Bool) :
    hazardOfRoot (quittingSoloStationaryRoot owner hazard) =
      quittingTwoOwnerHazard owner anchor (hazard true).toReal 0 := by
  funext who
  by_cases hwho : who = owner
  · subst who
    simp [hazardOfRoot, quittingSoloStationaryRoot]
  · simp [hazardOfRoot, quittingSoloStationaryRoot,
      quittingTwoOwnerHazard, quittingTwoOwnerLeadingVariation, hwho]

/-- Game-facing producer.  At a minimum positive-debt semantic tail, an
interior exact solo row and one attractive inactive singleton automatically
select the first feasible tight outsider.  The remaining support-entry seam
is the finite nonzero-collision-or-cotight alternative. -/
theorem exists_minimalSoloBoundary_collision_nonzero_or_cotight_of_soloRoot
    (pair : QuittingTerminalSemanticPair ι)
    (owner anchor : ι) (hazard : PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hownerDebt : 0 < quittingTerminalSemanticDebt pair owner)
    (hne : owner ≠ anchor)
    (hquit : 0 < (hazard true).toReal)
    (hcontinue : 0 < (hazard false).toReal)
    (hownerPin : pair.1 owner =
      reward (quittingSingletonTerminal owner) owner)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingSoloStationaryRoot owner hazard))
    (hattractive : pair.1 anchor <
      reward (quittingSingletonTerminal anchor) anchor) :
    ∃ rate entrant, 0 < rate ∧ rate ≤ (hazard true).toReal ∧
      entrant ≠ owner ∧
      IsExactRowComplementary
        (quittingTwoOwnerHazard owner entrant rate 0)
        (fun who => gainValue (weightOfReward reward)
          (quittingTwoOwnerHazard owner entrant rate 0)
          who (pair.1 who)) ∧
      gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant rate 0)
        entrant (pair.1 entrant) = 0 ∧
      (quittingActiveMixingCollisionIncrement reward owner entrant ≠ 0 ∨
        ∃ who, who ≠ owner ∧ who ≠ entrant ∧
          gainValue (weightOfReward reward)
            (quittingTwoOwnerHazard owner entrant rate 0)
            who (pair.1 who) = 0) := by
  let displayedRate := (hazard true).toReal
  have hmass := quittingSoloHazardMass_add hazard
  have hdisplayedLt : displayedRate < 1 := by
    dsimp only [displayedRate]
    linarith
  have hrootHazard :=
    hazardOfRoot_soloStationaryRoot_eq_twoOwnerHazard
      owner anchor hazard
  have hendpoint : IsεQuittingRootEndpointNash reward pair.1 0
      (quittingSoloStationaryRoot owner hazard) :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward pair.1 (quittingSoloStationaryRoot owner hazard)).mpr hnash
  have hdisplayedComplementary : IsExactRowComplementary
      (quittingTwoOwnerHazard owner anchor displayedRate 0)
      (fun who => gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner anchor displayedRate 0)
        who (pair.1 who)) := by
    rw [← hrootHazard]
    exact (isExactRowComplementary_hazardOfRoot_iff reward pair.1
      (quittingSoloStationaryRoot owner hazard)).mpr hendpoint
  have hanchorProfitable : 0 <
      gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner anchor 0 0)
        anchor (pair.1 anchor) := by
    rw [gainValue_twoOwner_second_fixedTail pair.1 owner anchor 0 0 hne]
    simpa using hattractive
  exact exists_minimalSoloBoundary_collision_nonzero_or_cotight
    (reward := reward) pair owner anchor displayedRate hM hreward hpair
      hminimum hownerDebt hne hquit hdisplayedLt hownerPin
      hdisplayedComplementary hanchorProfitable

/-! ## Provenance-preserving global reduction -/

/-- The finite support-entry certificate exposed by an interior atomic solo
edge at a minimum positive-debt semantic tail. -/
def HasMinimumSemanticSoloSupportBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : QuittingTerminalSemanticPair ι) (owner : ι)
    (hazard : PMF Bool) : Prop :=
  ∃ rate entrant, 0 < rate ∧ rate ≤ (hazard true).toReal ∧
    entrant ≠ owner ∧
    IsExactRowComplementary
      (quittingTwoOwnerHazard owner entrant rate 0)
      (fun who => gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant rate 0)
        who (tail.1 who)) ∧
    gainValue (weightOfReward reward)
      (quittingTwoOwnerHazard owner entrant rate 0)
      entrant (tail.1 entrant) = 0 ∧
    (quittingActiveMixingCollisionIncrement reward owner entrant ≠ 0 ∨
      ∃ who, who ≠ owner ∧ who ≠ entrant ∧
        gainValue (weightOfReward reward)
          (quittingTwoOwnerHazard owner entrant rate 0)
          who (tail.1 who) = 0)

/-- An atomic solo row together with the minimum-carrier semantic edge that
produced it.  Besides the quantitative isolated-negative restrictions, this
retains both endpoints of the prefix edge, the exact fixed-tail Nash witness,
the unique positive-debt owner, and an attractive inactive outsider.

The last disjunction records whether the owner surely Quits.  If the owner
also has positive Continue mass, the data include a first feasible tight
support boundary at which either the owner's collision increment is nonzero
or a second outsider is cotight. -/
def HasProvenanceAtomicMinimumSemanticSoloRow
    (regime : QuittingCounterexampleRegime reward) : Prop :=
  ∃ (current tail : QuittingTerminalSemanticPair ι)
      (owner : ι) (hazard : PMF Bool) (anchor : ι),
    current ∈ quittingTerminalSemanticCarrier reward ∧
    tail ∈ quittingTerminalSemanticCarrier reward ∧
    (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum current ≤
        quittingTerminalSemanticDebtSum candidate) ∧
    (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum tail ≤
        quittingTerminalSemanticDebtSum candidate) ∧
    current = quittingTerminalSemanticPrefix reward
      (quittingSoloStationaryRoot owner hazard) tail ∧
    IsεQuittingRootNash reward tail.1 0
      (quittingSoloStationaryRoot owner hazard) ∧
    0 < quittingTerminalSemanticDebt current owner ∧
    0 < quittingTerminalSemanticDebt tail owner ∧
    (∀ player, player ≠ owner →
      quittingTerminalSemanticDebt current player = 0 ∧
      quittingTerminalSemanticDebt tail player = 0) ∧
    tail.1 owner = reward (quittingSingletonTerminal owner) owner ∧
    anchor ≠ owner ∧
    tail.1 anchor < reward (quittingSingletonTerminal anchor) anchor ∧
    0 < (hazard true).toReal ∧
    IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner hazard) ∧
    HasIsolatedNegativeAbsorbingQuittingCycle reward ∧
    quittingSoloReward reward owner owner ≤ -regime.terminalGap ∧
    quittingSoloReward reward owner owner <
      quittingPunishmentValue reward owner ∧
    ((hazard false).toReal = 0 ∨
      (0 < (hazard false).toReal ∧
        HasMinimumSemanticSoloSupportBoundary reward tail owner hazard))

/-- **Provenance-preserving two-branch reduction.**  If a finite quitting
game has no uniform-equilibrium payoff, then either it has a positive-debt
minimum all-Continue semantic plateau, or it has an atomic isolated-negative
solo row carried by an explicit exact prefix edge between two minimum
semantic pairs.  In the interior-hazard case the same tail exposes the
nonzero-collision-or-cotight support-entry boundary. -/
theorem exists_semanticPlateau_or_provenanceAtomicSolo_of_noUE
    [Nonempty ι]
    (regime : QuittingCounterexampleRegime reward)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    HasPositiveMinimumTerminalSemanticPlateau reward ∨
      HasProvenanceAtomicMinimumSemanticSoloRow regime := by
  rcases
      exists_positiveMinimumPlateau_or_fixedOwnerSoloSemanticSpine_of_no_uniformPayoff
        reward hM hreward regime.not_exists_uniformEquilibriumPayoff with
    hplateau | ⟨pair, root, owner, debt, hdebt, hpair, hminimum,
      hprefix, hnash, _hnoPlateau, hnoMinimumPlateau, hownerDebt,
      hotherDebt, hquit, hpure, hrootSolo, _hopponentSurvival,
      htightNext, hblocker⟩
  · exact Or.inl hplateau
  · right
    have hendpoint : IsεQuittingRootEndpointNash reward
        (quittingSoloReward reward owner) 0 (root 0) := by
      by_contra hnotEndpoint
      have hcontinue : 0 < (root 0 owner false).toReal := by
        by_contra hnot
        have hzero : (root 0 owner false).toReal = 0 :=
          le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
        exact hnotEndpoint
          (isZeroSoloEndpointNash_of_soloRoot_continue_eq_zero
            (pair 1).1 (root 0) owner (hnash 0) (hpure 0) hzero)
      have hsurvivalNot : ¬ Tendsto
          (quittingSoloSemanticSurvival root owner 0) atTop (nhds 0) := by
        intro hsurvival
        exact hnotEndpoint
          (isZeroSoloEndpointNash_of_terminalSemanticSoloSpine_survival_tendsto_zero
            pair root owner hM hreward hpair hprefix hnash hpure
              hcontinue hsurvival)
      obtain ⟨lower, hlower, hsurvivalLower⟩ :=
        exists_pos_le_quittingSoloSemanticSurvival_of_not_tendsto_zero
          root owner 0 hsurvivalNot
      obtain ⟨candidate, hcandidate, hcandidateMin, hnashAll⟩ :=
        exists_minimum_allContinueNash_of_soloSemanticSpine_survival_lower
          pair root owner hM hreward hpair hminimum hnash hpure
            hlower hsurvivalLower
      exact False.elim
        (hnoMinimumPlateau
          ⟨candidate, hcandidate, hcandidateMin, hnashAll⟩)
    let hazard := root 0 owner
    have hendpointSolo : IsεQuittingRootEndpointNash reward
        (quittingSoloReward reward owner) 0
        (quittingSoloStationaryRoot owner hazard) := by
      rw [← hrootSolo 0]
      exact hendpoint
    obtain ⟨anchor, hanchorNe, hattractive, _hdeterrence⟩ := hblocker 0
    have hcurrentPrefix : pair 0 = quittingTerminalSemanticPrefix reward
        (quittingSoloStationaryRoot owner hazard) (pair 1) := by
      rw [← hrootSolo 0]
      exact hprefix 0
    have hnashSolo : IsεQuittingRootNash reward (pair 1).1 0
        (quittingSoloStationaryRoot owner hazard) := by
      rw [← hrootSolo 0]
      exact hnash 0
    have hcurrentDebt : 0 < quittingTerminalSemanticDebt (pair 0) owner := by
      rw [hownerDebt 0]
      exact hdebt
    have htailDebt : 0 < quittingTerminalSemanticDebt (pair 1) owner := by
      rw [hownerDebt 1]
      exact hdebt
    have hisolated :=
      exists_isolatedNegativeCycle_and_soloReward_le_neg_terminalGap
        regime owner hazard (hquit 0) hendpointSolo
    have hpunishment : quittingSoloReward reward owner owner <
        quittingPunishmentValue reward owner :=
      regime.soloReward_lt_punishmentValue_of_soloEndpointNash
        owner hazard (hquit 0) hendpointSolo
    refine ⟨pair 0, pair 1, owner, hazard, anchor,
      hpair 0, hpair 1, hminimum 0, hminimum 1,
      hcurrentPrefix, hnashSolo, hcurrentDebt, htailDebt, ?_,
      (htightNext 0).symm, hanchorNe, hattractive, hquit 0,
      hendpointSolo, hisolated.1, hisolated.2, hpunishment, ?_⟩
    · intro player hplayer
      exact ⟨hotherDebt 0 player hplayer, hotherDebt 1 player hplayer⟩
    · by_cases hcontinueZero : (hazard false).toReal = 0
      · exact Or.inl hcontinueZero
      · right
        have hcontinuePos : 0 < (hazard false).toReal :=
          lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hcontinueZero)
        refine ⟨hcontinuePos, ?_⟩
        exact
          exists_minimalSoloBoundary_collision_nonzero_or_cotight_of_soloRoot
            (reward := reward) (pair 1) owner anchor hazard hM hreward
              (hpair 1) (hminimum 1) htailDebt hanchorNe.symm
              (hquit 0) hcontinuePos (htightNext 0).symm hnashSolo
              hattractive

end GameTheory
