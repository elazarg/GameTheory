/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSupportEntry
import UniformEquilibrium.Quitting.Stationary.MinMax

/-!
# Sharp support boundary on the atomic semantic branch

The minimum-semantic support-entry obstruction extends to a sure-Quit owner.
At owner rate one, activating a tight outsider preserves exact root Nash not
only when the owner's collision increment vanishes, but whenever that
increment is nonnegative: the owner is already at the upper hazard boundary,
so only the lower complementary inequality remains.  Positive owner debt and
minimum semanticity then forbid the resulting two-owner root.

Consequently every atomic solo edge selected by the global semantic reduction
has a finite support boundary.  Below owner rate one the residual is the
previous nonzero-collision-or-cotight alternative.  At owner rate one it
sharpens to a negative-collision-or-cotight alternative.  In particular the
pure-Quit atomic branch no longer loses the support-entry certificate.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## The punishment gap retained by a semantic tail -/

/-- Every terminal-semantic envelope lies above the behavioral punishment
value.  This is first true for literal profiles because their envelope is the
best reply to one particular opponent plan, and then passes to the carrier by
closure. -/
theorem quittingPunishmentValue_le_terminalSemanticEnvelope
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) (who : ι) :
    quittingPunishmentValue reward who ≤ pair.2 who := by
  change pair ∈ {candidate : QuittingTerminalSemanticPair ι |
    quittingPunishmentValue reward who ≤ candidate.2 who}
  apply (closure_minimal ?_ ?_) hpair
  · rintro candidate ⟨profile, rfl⟩
    have hfloor := quittingPunishmentValue_le reward who profile
    change quittingPunishmentValue reward who ≤
      quittingContinuationBestResponseValue reward profile who
    simpa [quittingBestReplyValue, iSup,
      quittingContinuationBestResponseValue] using hfloor
  · exact isClosed_le continuous_const
      ((continuous_apply who).comp (continuous_snd.comp continuous_id))

/-- If the prescribed owner coordinate is its singleton payoff, semantic
debt carries the entire strict individual-rationality gap. -/
theorem punishmentGap_le_terminalSemanticDebt_of_ownerPin
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) (owner : ι)
    (hownerPin : pair.1 owner =
      quittingSoloReward reward owner owner) :
    quittingPunishmentValue reward owner -
        quittingSoloReward reward owner owner ≤
      quittingTerminalSemanticDebt pair owner := by
  have hfloor :=
    quittingPunishmentValue_le_terminalSemanticEnvelope pair hpair owner
  unfold quittingTerminalSemanticDebt
  linarith

/-- The exact stationary cap faced by an owner when one distinct outsider
quits surely and every other opponent Continues. -/
def quittingOneOutsiderPunishmentCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner entrant : ι) : ℝ :=
  max (reward (quittingPairJoinTerminal owner entrant) owner)
    (reward (quittingSingletonTerminal entrant) owner)

/-- A one-outsider cap is the ordinary stationary unilateral cap of the
corresponding pure singleton opponent root. -/
theorem quittingOneOutsiderPunishmentCap_eq_stationaryCap
    (owner entrant : ι) (hne : owner ≠ entrant) :
    quittingOneOutsiderPunishmentCap reward owner entrant =
      quittingStationaryUnilateralCap reward
        (quittingPureSetRoot ({entrant} : Finset ι)) owner := by
  rw [quittingStationaryUnilateralCap_pureSetRoot]
  simp [quittingOneOutsiderPunishmentCap, quittingSetReward,
    quittingPairJoinTerminal, quittingSingletonTerminal, hne,
    Finset.pair_comm]

/-- Weak duality for the one-outsider punishment candidate. -/
theorem quittingPunishmentValue_le_oneOutsiderPunishmentCap
    (owner entrant : ι) (hne : owner ≠ entrant) :
    quittingPunishmentValue reward owner ≤
      quittingOneOutsiderPunishmentCap reward owner entrant := by
  rw [quittingOneOutsiderPunishmentCap_eq_stationaryCap
    (reward := reward) owner entrant hne]
  exact quittingPunishmentValue_le_stationaryUnilateralCap
    reward owner (quittingPureSetRoot ({entrant} : Finset ι))

/-- Quantitative form of one-outsider weak duality, normalized by the atomic
owner's singleton payoff. -/
theorem punishmentGap_le_oneOutsiderPunishmentCap_sub_soloReward
    (owner entrant : ι) (hne : owner ≠ entrant) :
    quittingPunishmentValue reward owner -
        quittingSoloReward reward owner owner ≤
      quittingOneOutsiderPunishmentCap reward owner entrant -
        quittingSoloReward reward owner owner := by
  linarith [quittingPunishmentValue_le_oneOutsiderPunishmentCap
    (reward := reward) owner entrant hne]

/-- A strict atomic punishment gap excludes every one-outsider stationary
punishment cap at the owner's singleton level.  This is the elementary dual
restriction carried through every selected support pivot. -/
theorem soloReward_lt_oneOutsiderPunishmentCap_of_lt_punishmentValue
    (owner entrant : ι) (hne : owner ≠ entrant)
    (hstrict : quittingSoloReward reward owner owner <
      quittingPunishmentValue reward owner) :
    quittingSoloReward reward owner owner <
      quittingOneOutsiderPunishmentCap reward owner entrant :=
  hstrict.trans_le
    (quittingPunishmentValue_le_oneOutsiderPunishmentCap
      (reward := reward) owner entrant hne)

/-- At a sure-Quit owner boundary, a tight outsider can enter support when
the owner's reciprocal collision increment is nonnegative and every other
inactive row is strict. -/
theorem exists_exact_twoOwnerSupportEntry_of_pureOwner_nonnegative_isolated
    (tail : Payoff ι) (owner entrant : ι)
    (hne : owner ≠ entrant)
    (hownerPin : tail owner =
      reward (quittingSingletonTerminal owner) owner)
    (hownerNonneg :
      0 ≤ quittingActiveMixingCollisionIncrement reward owner entrant)
    (hentrantTight :
      gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant 1 0)
        entrant (tail entrant) = 0)
    (hotherStrict : ∀ who, who ≠ owner → who ≠ entrant →
      gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant 1 0)
        who (tail who) < 0) :
    ∃ entrantRate : ℝ, ∃ root : ι → PMF Bool,
      0 < entrantRate ∧ entrantRate < 1 ∧
      hazardOfRoot root =
        quittingTwoOwnerHazard owner entrant 1 entrantRate ∧
      IsεQuittingRootNash reward tail 0 root := by
  have hotherEventually : ∀ᶠ entrantRate in 𝓝 (0 : ℝ),
      ∀ who, who ≠ owner → who ≠ entrant →
        gainValue (weightOfReward reward)
          (quittingTwoOwnerHazard owner entrant 1 entrantRate)
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
          (reward := reward) tail owner entrant who 1 hne).continuousAt
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
  let hazard := quittingTwoOwnerHazard owner entrant 1 entrantRate
  have hhazardNonneg : ∀ who, 0 ≤ hazard who := by
    intro who
    by_cases hwhoOwner : who = owner
    · simp [hazard, quittingTwoOwnerHazard, hwhoOwner]
    · by_cases hwhoEntrant : who = entrant
      · subst who
        change 0 ≤ quittingTwoOwnerHazard owner entrant 1 entrantRate entrant
        rw [quittingTwoOwnerHazard_second owner entrant 1 entrantRate hne]
        exact hentrantRatePos.le
      · simp [hazard, quittingTwoOwnerHazard,
          quittingTwoOwnerLeadingVariation, hwhoOwner, hwhoEntrant]
  have hhazardLeOne : ∀ who, hazard who ≤ 1 := by
    intro who
    by_cases hwhoOwner : who = owner
    · simp [hazard, quittingTwoOwnerHazard, hwhoOwner]
    · by_cases hwhoEntrant : who = entrant
      · subst who
        change quittingTwoOwnerHazard owner entrant 1 entrantRate entrant ≤ 1
        rw [quittingTwoOwnerHazard_second owner entrant 1 entrantRate hne]
        exact hentrantRateLt.le
      · simp [hazard, quittingTwoOwnerHazard,
          quittingTwoOwnerLeadingVariation, hwhoOwner, hwhoEntrant]
  let root := rootOfHazard hazard hhazardNonneg hhazardLeOne
  have hownerGainEq : gainValue (weightOfReward reward) hazard owner
      (tail owner) = entrantRate *
        quittingActiveMixingCollisionIncrement reward owner entrant := by
    rw [gainValue_twoOwner_first_fixedTail tail owner entrant 1
      entrantRate hne, hownerPin]
    unfold quittingActiveMixingCollisionIncrement
    ring
  have hownerGain : 0 ≤ gainValue (weightOfReward reward) hazard owner
      (tail owner) := by
    rw [hownerGainEq]
    exact mul_nonneg hentrantRatePos.le hownerNonneg
  have hentrantGain : gainValue (weightOfReward reward) hazard entrant
      (tail entrant) = 0 := by
    rw [gainValue_twoOwner_second_fixedTail tail owner entrant 1
      entrantRate hne]
    rw [gainValue_twoOwner_second_fixedTail tail owner entrant 1 0 hne]
      at hentrantTight
    exact hentrantTight
  have hcomplementary : IsExactRowComplementary hazard
      (fun who => gainValue (weightOfReward reward) hazard who (tail who)) := by
    intro who
    by_cases hwhoOwner : who = owner
    · subst who
      have hownerHazard : hazard owner = 1 := by
        simp [hazard]
      rw [hownerHazard]
      exact ⟨fun _ => hownerGain,
        fun hlt => (lt_irrefl (1 : ℝ) hlt).elim⟩
    · by_cases hwhoEntrant : who = entrant
      · subst who
        change (0 < hazard entrant →
            0 ≤ gainValue (weightOfReward reward) hazard entrant
              (tail entrant)) ∧
          (hazard entrant < 1 →
            gainValue (weightOfReward reward) hazard entrant
              (tail entrant) ≤ 0)
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

/-- At a minimum positive-debt tail, a tight outsider at owner rate one
forces either a strictly negative owner collision increment or a second
tight outsider.  A nonnegative increment would allow actual support entry,
which contracts the owner's deleted survival and contradicts minimum debt. -/
theorem collision_negative_or_exists_cotight_outsider_of_pureOwner_minimumSemanticDebt
    (pair : QuittingTerminalSemanticPair ι)
    (owner entrant : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hownerDebt : 0 < quittingTerminalSemanticDebt pair owner)
    (hne : owner ≠ entrant)
    (hownerPin : pair.1 owner =
      reward (quittingSingletonTerminal owner) owner)
    (hsoloComplementary : IsExactRowComplementary
      (quittingTwoOwnerHazard owner entrant 1 0)
      (fun who => gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant 1 0)
        who (pair.1 who)))
    (hentrantTight :
      gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant 1 0)
        entrant (pair.1 entrant) = 0) :
    quittingActiveMixingCollisionIncrement reward owner entrant < 0 ∨
      ∃ who, who ≠ owner ∧ who ≠ entrant ∧
        gainValue (weightOfReward reward)
          (quittingTwoOwnerHazard owner entrant 1 0)
          who (pair.1 who) = 0 := by
  by_cases hcollision :
      quittingActiveMixingCollisionIncrement reward owner entrant < 0
  · exact Or.inl hcollision
  · right
    by_contra hnot
    push Not at hnot
    have hotherStrict : ∀ who, who ≠ owner → who ≠ entrant →
        gainValue (weightOfReward reward)
          (quittingTwoOwnerHazard owner entrant 1 0)
          who (pair.1 who) < 0 := by
      intro who hwhoOwner hwhoEntrant
      have hzeroHazard :
          quittingTwoOwnerHazard owner entrant 1 0 who = 0 :=
        quittingTwoOwnerHazard_eq_zero_of_ne owner entrant who 1 0
          hwhoOwner hwhoEntrant
      have hnonpos :=
        (hsoloComplementary who).2 (by rw [hzeroHazard]; norm_num)
      exact lt_of_le_of_ne hnonpos (hnot who hwhoOwner hwhoEntrant)
    obtain ⟨entrantRate, root, hentrantRatePos, _hentrantRateLt,
        hrootHazard, hnash⟩ :=
      exists_exact_twoOwnerSupportEntry_of_pureOwner_nonnegative_isolated
        (reward := reward) pair.1 owner entrant hne hownerPin
          (le_of_not_gt hcollision) hentrantTight hotherStrict
    have hzero :=
      quittingTerminalSemantic_minimum_positiveDebt_opponents_quit_eq_zero
        reward pair root hM hreward hpair hminimum hnash hownerDebt hne.symm
    have hpositive : 0 < (root entrant true).toReal := by
      change 0 < hazardOfRoot root entrant
      rw [hrootHazard,
        quittingTwoOwnerHazard_second owner entrant 1 entrantRate hne]
      exact hentrantRatePos
    linarith

/-- The sharp finite certificate at a minimum semantic solo boundary.  The
selected rate is positive and at most the displayed solo rate.  Below one,
the collision residual is merely nonzero; at the upper rate boundary it must
be strictly negative.  Either residual can be replaced by a third cotight
outsider. -/
def HasSharpMinimumSemanticSoloSupportBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : QuittingTerminalSemanticPair ι) (owner : ι)
    (displayedRate : ℝ) : Prop :=
  ∃ rate entrant, 0 < rate ∧ rate ≤ displayedRate ∧
    entrant ≠ owner ∧
    IsExactRowComplementary
      (quittingTwoOwnerHazard owner entrant rate 0)
      (fun who => gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant rate 0)
        who (tail.1 who)) ∧
    gainValue (weightOfReward reward)
      (quittingTwoOwnerHazard owner entrant rate 0)
      entrant (tail.1 entrant) = 0 ∧
    ((rate < 1 ∧
        (quittingActiveMixingCollisionIncrement reward owner entrant ≠ 0 ∨
          ∃ who, who ≠ owner ∧ who ≠ entrant ∧
            gainValue (weightOfReward reward)
              (quittingTwoOwnerHazard owner entrant rate 0)
              who (tail.1 who) = 0)) ∨
      (rate = 1 ∧
        (quittingActiveMixingCollisionIncrement reward owner entrant < 0 ∨
          ∃ who, who ≠ owner ∧ who ≠ entrant ∧
            gainValue (weightOfReward reward)
              (quittingTwoOwnerHazard owner entrant rate 0)
              who (tail.1 who) = 0)))

/-- First-boundary selection with the rate-one collision sign sharpened. -/
theorem exists_sharp_minimalSoloBoundary
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
    (hdisplayedLe : displayedRate ≤ 1)
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
    HasSharpMinimumSemanticSoloSupportBoundary
      reward pair owner displayedRate := by
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
  have hrateLeOne : rate ≤ 1 := hrateLe.trans hdisplayedLe
  refine ⟨rate, entrant, hratePos, hrateLe, hentrantNe,
    hcomplementary', hentrantTight', ?_⟩
  by_cases hrateLt : rate < 1
  · left
    refine ⟨hrateLt, ?_⟩
    exact collision_nonzero_or_exists_cotight_outsider_of_minimumSemanticDebt
      (reward := reward) pair owner entrant rate hM hreward hpair hminimum
        hownerDebt hentrantNe.symm hratePos hrateLt hownerPin
        hcomplementary' hentrantTight'
  · right
    have hrateEq : rate = 1 := le_antisymm hrateLeOne (le_of_not_gt hrateLt)
    refine ⟨hrateEq, ?_⟩
    subst rate
    exact
      collision_negative_or_exists_cotight_outsider_of_pureOwner_minimumSemanticDebt
        (reward := reward) pair owner entrant hM hreward hpair hminimum
          hownerDebt hentrantNe.symm hownerPin hcomplementary' hentrantTight'

/-- Game-facing sharp boundary producer.  Unlike the earlier producer, this
requires no positive Continue mass: a pure-Quit solo row is handled by the
rate-one collision-sign theorem. -/
theorem exists_sharp_minimalSoloBoundary_of_soloRoot
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
    (hownerPin : pair.1 owner =
      reward (quittingSingletonTerminal owner) owner)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingSoloStationaryRoot owner hazard))
    (hattractive : pair.1 anchor <
      reward (quittingSingletonTerminal anchor) anchor) :
    HasSharpMinimumSemanticSoloSupportBoundary reward pair owner
      (hazard true).toReal := by
  let displayedRate := (hazard true).toReal
  have hdisplayedLe : displayedRate ≤ 1 := by
    dsimp only [displayedRate]
    exact (ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one hazard true)).trans_eq (by norm_num)
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
  exact exists_sharp_minimalSoloBoundary
    (reward := reward) pair owner anchor displayedRate hM hreward hpair
      hminimum hownerDebt hne hquit hdisplayedLe hownerPin
      hdisplayedComplementary hanchorProfitable

/-- A sharp support boundary with the atomic punishment gap carried through
the selected entrant.  At rate one, tightness makes the reverse collision
increment zero.  If the owner-side increment is negative, weak punishment
duality identifies the precise escape: the entrant's singleton exit pays the
owner strictly more than the owner's own singleton payoff. -/
def HasPunishmentSeparatedSharpMinimumSemanticSoloSupportBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : QuittingTerminalSemanticPair ι) (owner : ι)
    (displayedRate : ℝ) : Prop :=
  ∃ rate entrant, 0 < rate ∧ rate ≤ displayedRate ∧
    entrant ≠ owner ∧
    IsExactRowComplementary
      (quittingTwoOwnerHazard owner entrant rate 0)
      (fun who => gainValue (weightOfReward reward)
        (quittingTwoOwnerHazard owner entrant rate 0)
        who (tail.1 who)) ∧
    gainValue (weightOfReward reward)
      (quittingTwoOwnerHazard owner entrant rate 0)
      entrant (tail.1 entrant) = 0 ∧
    quittingSoloReward reward owner owner <
      quittingOneOutsiderPunishmentCap reward owner entrant ∧
    quittingPunishmentValue reward owner -
        quittingSoloReward reward owner owner ≤
      quittingOneOutsiderPunishmentCap reward owner entrant -
        quittingSoloReward reward owner owner ∧
    ((rate < 1 ∧
        (quittingActiveMixingCollisionIncrement reward owner entrant ≠ 0 ∨
          ∃ who, who ≠ owner ∧ who ≠ entrant ∧
            gainValue (weightOfReward reward)
              (quittingTwoOwnerHazard owner entrant rate 0)
              who (tail.1 who) = 0)) ∨
      (rate = 1 ∧
        quittingActiveMixingCollisionIncrement reward entrant owner = 0 ∧
        ((quittingActiveMixingCollisionIncrement reward owner entrant < 0 ∧
            quittingSoloReward reward owner owner <
              reward (quittingSingletonTerminal entrant) owner ∧
            quittingPunishmentValue reward owner -
                quittingSoloReward reward owner owner ≤
              reward (quittingSingletonTerminal entrant) owner -
                quittingSoloReward reward owner owner) ∨
          ∃ who, who ≠ owner ∧ who ≠ entrant ∧
            gainValue (weightOfReward reward)
              (quittingTwoOwnerHazard owner entrant rate 0)
              who (tail.1 who) = 0)))

/-- Carry strict punishment separation through the selected finite support
boundary. -/
theorem exists_punishmentSeparated_sharp_minimalSoloBoundary_of_soloRoot
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
    (hownerPin : pair.1 owner =
      reward (quittingSingletonTerminal owner) owner)
    (hnash : IsεQuittingRootNash reward pair.1 0
      (quittingSoloStationaryRoot owner hazard))
    (hattractive : pair.1 anchor <
      reward (quittingSingletonTerminal anchor) anchor)
    (hpunishment : quittingSoloReward reward owner owner <
      quittingPunishmentValue reward owner) :
    HasPunishmentSeparatedSharpMinimumSemanticSoloSupportBoundary
      reward pair owner (hazard true).toReal := by
  rcases exists_sharp_minimalSoloBoundary_of_soloRoot
      (reward := reward) pair owner anchor hazard hM hreward hpair hminimum
        hownerDebt hne hquit hownerPin hnash hattractive with
    ⟨rate, entrant, hratePos, hrateLe, hentrantNe,
      hcomplementary, hentrantTight, hsharp⟩
  have hcap := soloReward_lt_oneOutsiderPunishmentCap_of_lt_punishmentValue
    (reward := reward) owner entrant hentrantNe.symm hpunishment
  have hcapGap :=
    punishmentGap_le_oneOutsiderPunishmentCap_sub_soloReward
      (reward := reward) owner entrant hentrantNe.symm
  refine ⟨rate, entrant, hratePos, hrateLe, hentrantNe,
    hcomplementary, hentrantTight, hcap, hcapGap, ?_⟩
  rcases hsharp with ⟨hrateLt, hresidual⟩ |
      ⟨hrateEq, hresidual⟩
  · exact Or.inl ⟨hrateLt, hresidual⟩
  · right
    have hreverse :
        quittingActiveMixingCollisionIncrement reward entrant owner = 0 := by
      have htight := hentrantTight
      rw [hrateEq,
        gainValue_twoOwner_second_fixedTail pair.1 owner entrant 1 0
          hentrantNe.symm] at htight
      simpa [quittingActiveMixingCollisionIncrement] using htight
    refine ⟨hrateEq, hreverse, ?_⟩
    rcases hresidual with hnegative | hcotight
    · left
      have hpairLe :
          reward (quittingPairJoinTerminal owner entrant) owner ≤
            reward (quittingSingletonTerminal entrant) owner := by
        unfold quittingActiveMixingCollisionIncrement at hnegative
        linarith
      refine ⟨hnegative, ?_, ?_⟩
      · simpa [quittingOneOutsiderPunishmentCap,
          max_eq_right hpairLe] using hcap
      · simpa [quittingOneOutsiderPunishmentCap,
          max_eq_right hpairLe] using hcapGap
    · exact Or.inr hcotight

/-- The globally selected atomic semantic edge, strengthened by a sharp
support boundary at its own minimum tail. -/
def HasSharpBoundaryProvenanceAtomicMinimumSemanticSoloRow
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
    0 < quittingPunishmentValue reward owner -
      quittingSoloReward reward owner owner ∧
    quittingPunishmentValue reward owner -
        quittingSoloReward reward owner owner ≤
      quittingTerminalSemanticDebt tail owner ∧
    ((hazard false).toReal = 0 ∨ 0 < (hazard false).toReal) ∧
    HasPunishmentSeparatedSharpMinimumSemanticSoloSupportBoundary
      reward tail owner (hazard true).toReal

/-- **Sharp global atomic reduction.**  Every counterexample has either the
existing positive minimum all-Continue plateau or a provenance-preserving
atomic solo edge with a sharp finite support boundary.  This strengthens the
pure-Quit branch as well as the interior branch. -/
theorem exists_semanticPlateau_or_sharpBoundaryProvenanceAtomicSolo_of_noUE
    [Nonempty ι]
    (regime : QuittingCounterexampleRegime reward)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    HasPositiveMinimumTerminalSemanticPlateau reward ∨
      HasSharpBoundaryProvenanceAtomicMinimumSemanticSoloRow regime := by
  rcases exists_semanticPlateau_or_provenanceAtomicSolo_of_noUE
      regime hM hreward with hplateau | hatomic
  · exact Or.inl hplateau
  · right
    rcases hatomic with
      ⟨current, tail, owner, hazard, anchor, hcurrentCarrier, htailCarrier,
        hcurrentMin, htailMin, hprefix, hnash, hcurrentDebt, htailDebt,
        hotherDebt, hownerPin, hanchorNe, hattractive, hquit, hendpoint,
        hisolated, hgap, hpunishment, hcontinue⟩
    have hpunishmentGap : 0 < quittingPunishmentValue reward owner -
        quittingSoloReward reward owner owner := by
      linarith
    have hpunishmentGapDebt : quittingPunishmentValue reward owner -
          quittingSoloReward reward owner owner ≤
        quittingTerminalSemanticDebt tail owner :=
      punishmentGap_le_terminalSemanticDebt_of_ownerPin
        tail htailCarrier owner (by
          simpa [quittingSoloReward, quittingSingletonTerminal] using
            hownerPin)
    have hsharpPunishment :=
      exists_punishmentSeparated_sharp_minimalSoloBoundary_of_soloRoot
        (reward := reward) tail owner anchor hazard hM hreward htailCarrier
          htailMin htailDebt hanchorNe.symm hquit hownerPin hnash
          hattractive hpunishment
    refine ⟨current, tail, owner, hazard, anchor, hcurrentCarrier,
      htailCarrier, hcurrentMin, htailMin, hprefix, hnash, hcurrentDebt,
      htailDebt, hotherDebt, hownerPin, hanchorNe, hattractive, hquit,
      hendpoint, hisolated, hgap, hpunishment, hpunishmentGap,
      hpunishmentGapDebt, ?_, hsharpPunishment⟩
    rcases hcontinue with hzero | ⟨hpositive, _hboundary⟩
    · exact Or.inl hzero
    · exact Or.inr hpositive

end GameTheory
