/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionTemporalSplit
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectStratification
import UniformEquilibrium.Quitting.Paths.OpponentActionMass
import UniformEquilibrium.Quitting.Debt.Marked.FencePacket

/-!
# Matching a diffuse reprojection clock to a deleted-player chronology

The coalition clock in a diffuse reprojection packet is tied to literal rows
of actual profiles.  If its fixed coalition contains an opponent of the reset
owner, it is dominated row by row by that owner's deleted-player absorption
clock.  This file normalizes the latter clock on the same finite windows.

There is one sharp obstruction: the larger deleted clock may have a fixed-size
stage atom even though the selected coalition clock is diffuse.  Otherwise
the deleted clock is diffuse, complete on every window, and its cutoffs tend
to infinity.  Thus the surviving branch gives arbitrary-depth finite pieces
of one actual shifted-tail/deleted-player chronology; no independently
selected state is introduced.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Actual survival-weighted probability that some opponent of `owner` Quits
at one live row. -/
def quittingStageOpponentAbsorptionMass
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (time : ℕ) : ℝ :=
  quittingLiveMass reward profile time *
    quittingRootOpponentAbsorptionMass
      (quittingProfileLiveRoot reward profile time) owner

/-- Total deleted-player absorption mass in a finite actual-profile window.
-/
def quittingFiniteWindowOpponentAbsorptionMass
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    quittingStageOpponentAbsorptionMass profile owner time

/-- The deleted-player absorption clock normalized on the same finite window.
-/
def quittingFiniteWindowOpponentAbsorptionClock
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (cutoff time : ℕ) : ℝ :=
  if time < cutoff then
    quittingStageOpponentAbsorptionMass profile owner time /
      quittingFiniteWindowOpponentAbsorptionMass profile owner cutoff
  else 0

theorem quittingStageOpponentAbsorptionMass_nonneg
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (time : ℕ) :
    0 ≤ quittingStageOpponentAbsorptionMass profile owner time := by
  exact mul_nonneg (quittingLiveMass_nonneg reward profile time)
    (quittingRootOpponentAbsorptionMass_nonneg
      (quittingProfileLiveRoot reward profile time) owner)

/-- The opponent-absorption hazard is the expectation of the literal
opponent-quit indicator under the original product root.  No owner marginal
is deleted from the realized action law. -/
theorem quittingRootOpponentAbsorptionMass_eq_expect_someOpponentQuits
    (root : ι → PMF Bool) (owner : ι) :
    quittingRootOpponentAbsorptionMass root owner =
      expect (pmfPi root) (quittingSomeOpponentQuitsIndicator owner) := by
  have hinvariant := expect_pmfPi_someOpponentQuits_update_invariant
    root owner (root owner)
  have hupdate : Function.update root owner (root owner) = root := by
    exact Function.update_eq_self owner root
  rw [hupdate] at hinvariant
  rw [hinvariant,
    expect_pmfPi_someOpponentQuits_eq_one_sub_continueMass]
  unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
  congr 1

@[simp] theorem quittingCoalitionAction_quittingQuitters
    (action : ι → Bool) :
    quittingCoalitionAction (quittingQuitters action) = action := by
  funext player
  cases haction : action player <;>
    simp [quittingCoalitionAction, quittingQuitters, haction]

/-- A positive deleted-player stage atom contains a positive exact coalition
atom on the same profile and row.  The finite loss is only the number of
Boolean action profiles. -/
theorem exists_exactCoalition_of_stageOpponentAbsorptionMass
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (time : ℕ) {resolution : ℝ}
    (hresolution : 0 < resolution)
    (hatom : resolution ≤
      quittingStageOpponentAbsorptionMass profile owner time) :
    ∃ other : ι, ∃ terminal : {S : Finset ι // S.Nonempty},
      other ≠ owner ∧ other ∈ terminal.val ∧
        resolution ≤ (Fintype.card (ι → Bool) : ℝ) *
          quittingStageCoalitionMass reward profile time terminal := by
  classical
  let root := quittingProfileLiveRoot reward profile time
  let live := quittingLiveMass reward profile time
  let term : (ι → Bool) → ℝ := fun action =>
    live * ((pmfPi root) action).toReal *
      quittingSomeOpponentQuitsIndicator owner action
  have hsum : quittingStageOpponentAbsorptionMass profile owner time =
      ∑ action, term action := by
    unfold quittingStageOpponentAbsorptionMass
    rw [quittingRootOpponentAbsorptionMass_eq_expect_someOpponentQuits,
      expect_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro action _
    dsimp only [term, live, root]
    ring
  obtain ⟨action, _haction, havg⟩ :=
    QuittingMarkedFencePacket.exists_sum_le_card_mul
      (Finset.univ : Finset (ι → Bool)) Finset.univ_nonempty term
  have hterm : resolution ≤
      (Fintype.card (ι → Bool) : ℝ) * term action := by
    rw [hsum] at hatom
    exact hatom.trans (by simpa using havg)
  have htermPos : 0 < term action := by
    have hcardNonneg : 0 ≤ (Fintype.card (ι → Bool) : ℝ) := by positivity
    by_contra hnot
    have hnonpos : term action ≤ 0 := le_of_not_gt hnot
    nlinarith
  have hflag : quittingOpponentQuitFlag owner action = true := by
    by_contra hnot
    have hfalse : quittingOpponentQuitFlag owner action = false :=
      Bool.eq_false_of_not_eq_true hnot
    have hzero : term action = 0 := by
      simp [term, quittingSomeOpponentQuitsIndicator, hfalse]
    rw [hzero] at htermPos
    exact (lt_irrefl 0 htermPos).elim
  have hindicator :
      quittingSomeOpponentQuitsIndicator owner action = 1 := by
    simp [quittingSomeOpponentQuitsIndicator, hflag]
  have hopponent : quittingSomeOpponentQuits owner action := by
    exact (quittingOpponentQuitFlag_eq_true_iff owner action).1 hflag
  obtain ⟨other, hne, hotherAction⟩ := hopponent
  have hotherMem : other ∈ quittingQuitters action := by
    simp [quittingQuitters, hotherAction]
  have hnonempty : (quittingQuitters action).Nonempty :=
    ⟨other, hotherMem⟩
  let terminal : {S : Finset ι // S.Nonempty} :=
    ⟨quittingQuitters action, hnonempty⟩
  have htermEq : term action =
      quittingStageCoalitionMass reward profile time terminal := by
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
      quittingRootCoalitionMass_eq_pmfPi]
    dsimp only [term, live, root, terminal]
    rw [quittingCoalitionAction_quittingQuitters, hindicator]
    ring
  refine ⟨other, terminal, hne, hotherMem, ?_⟩
  rwa [htermEq] at hterm

/-- **Deleted-stage atom to concentrated reprojection.**  A recurrent atom of
the owner-deleted stage clock freezes to one exact coalition containing one
fixed opponent.  The concentrated packet uses the same profiles and rows.
Its moving owner-defect normalization is obtained by extending the selected
mark back to the source index set and then restricting along the extracted
subsequence. -/
theorem QuittingReprojectionDiffuseWindowPacket.exists_concentratedPacket_of_deletedStageAtom
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : ι} {terminal : {S : Finset ι // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ} {lower : ℝ}
    (packet : QuittingReprojectionDiffuseWindowPacket
      reward profiles owner terminal cutoff scale lower)
    {resolution : ℝ} (hresolution : 0 < resolution)
    (hatom : ∃ᶠ n in atTop, ∃ time < cutoff n,
      resolution ≤ quittingStageOpponentAbsorptionMass
        (profiles n) owner time)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M) :
    ∃ other : ι, ∃ exact : {S : Finset ι // S.Nonempty},
      other ≠ owner ∧ other ∈ exact.val ∧
        Nonempty (QuittingReprojectionConcentratedPacket
          reward profiles owner exact cutoff scale) := by
  classical
  let actionCard : ℝ := Fintype.card (ι → Bool)
  let concentratedResolution := resolution / actionCard
  have hactionCard : 0 < actionCard := by
    dsimp only [actionCard]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (ι → Bool))
  have hconcentratedResolution : 0 < concentratedResolution :=
    div_pos hresolution hactionCard
  let good : ℕ → {S : Finset ι // S.Nonempty} → Prop := fun n exact =>
    (∃ other, other ≠ owner ∧ other ∈ exact.val) ∧
      ∃ time < cutoff n,
        concentratedResolution ≤
          quittingStageCoalitionMass reward (profiles n) time exact
  have hsome : ∃ᶠ n in atTop, ∃ exact, good n exact := by
    apply hatom.mono
    intro n hn
    obtain ⟨time, htime, hstage⟩ := hn
    obtain ⟨other, exact, hne, hmem, hexact⟩ :=
      exists_exactCoalition_of_stageOpponentAbsorptionMass
        (reward := reward) (profiles n) owner time hresolution hstage
    have hscaled : concentratedResolution ≤
        quittingStageCoalitionMass reward (profiles n) time exact := by
      apply (div_le_iff₀ hactionCard).2
      simpa only [concentratedResolution, actionCard, mul_comm] using hexact
    exact ⟨exact, ⟨other, hne, hmem⟩, time, htime, hscaled⟩
  have hfixed : ∃ exact, ∃ᶠ n in atTop, good n exact := by
    by_contra hnot
    have hnot' : ∀ exact, ¬ ∃ᶠ n in atTop, good n exact := by
      simpa using hnot
    have hall : ∀ᶠ n in atTop, ∀ exact, ¬ good n exact := by
      rw [eventually_all]
      intro exact
      exact not_frequently.1 (hnot' exact)
    obtain ⟨n, hn, halln⟩ := (hsome.and_eventually hall).exists
    obtain ⟨exact, hexact⟩ := hn
    exact (halln exact) hexact
  obtain ⟨exact, hexactFrequent⟩ := hfixed
  obtain ⟨_sample, hsample⟩ := hexactFrequent.exists
  obtain ⟨other, hne, hmem⟩ := hsample.1
  obtain ⟨subseq, hsubseq, hwitness⟩ :=
    extraction_of_frequently_atTop hexactFrequent
  choose mark hmarkLt hmarkMass using fun rank => (hwitness rank).2
  let extendedMark : ℕ → ℕ := Function.extend subseq mark (fun _ => 0)
  have hextendedMark : ∀ rank, extendedMark (subseq rank) = mark rank := by
    intro rank
    exact hsubseq.injective.extend_apply mark (fun _ => 0) rank
  have hdefect := packet.defect_tendsto extendedMark
  have hdefectSubseq := hdefect.comp hsubseq.tendsto_atTop
  refine ⟨other, exact, hne, hmem, ⟨{
    resolution := concentratedResolution
    resolution_pos := hconcentratedResolution
    subseq := subseq
    subseq_strictMono := hsubseq
    mark := mark
    mark_lt := hmarkLt
    stageMass := hmarkMass
    semanticPrefix := ?_
    defect_tendsto := ?_ }⟩⟩
  · intro rank
    exact positive_stageCoalitionMass_has_semanticPrefixIncidence
      reward (profiles (subseq rank)) (mark rank) exact hM hreward
        (hconcentratedResolution.trans_le (hmarkMass rank))
  · convert hdefectSubseq using 1
    funext rank
    simp only [Function.comp_apply, hextendedMark]

/-- A fixed coalition containing an opponent is dominated by the matching
deleted-player stage clock on the identical actual row. -/
theorem quittingStageCoalitionMass_le_stageOpponentAbsorptionMass
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) (owner other : ι)
    (time : ℕ) (hother : other ∈ terminal.val) (hne : other ≠ owner) :
    quittingStageCoalitionMass reward profile time terminal ≤
      quittingStageOpponentAbsorptionMass profile owner time := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
  unfold quittingStageOpponentAbsorptionMass
  exact mul_le_mul_of_nonneg_left
    (quittingRootCoalitionMass_le_opponentAbsorptionMass_of_other_mem
      (quittingProfileLiveRoot reward profile time) terminal.val owner other
        hother hne)
    (quittingLiveMass_nonneg reward profile time)

theorem quittingFiniteWindowCoalitionMass_le_opponentAbsorptionMass
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) (owner other : ι)
    (cutoff : ℕ) (hother : other ∈ terminal.val) (hne : other ≠ owner) :
    quittingFiniteWindowCoalitionMass profile terminal cutoff ≤
      quittingFiniteWindowOpponentAbsorptionMass profile owner cutoff := by
  unfold quittingFiniteWindowCoalitionMass
    quittingFiniteWindowOpponentAbsorptionMass
  exact Finset.sum_le_sum fun time _ =>
    quittingStageCoalitionMass_le_stageOpponentAbsorptionMass
      profile terminal owner other time hother hne

theorem sum_quittingFiniteWindowOpponentAbsorptionClock_eq_one
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (cutoff : ℕ)
    (hpositive : 0 <
      quittingFiniteWindowOpponentAbsorptionMass profile owner cutoff) :
    ∑ time ∈ Finset.range cutoff,
      quittingFiniteWindowOpponentAbsorptionClock
        profile owner cutoff time = 1 := by
  calc
    ∑ time ∈ Finset.range cutoff,
        quittingFiniteWindowOpponentAbsorptionClock
          profile owner cutoff time =
      ∑ time ∈ Finset.range cutoff,
        quittingStageOpponentAbsorptionMass profile owner time /
          quittingFiniteWindowOpponentAbsorptionMass profile owner cutoff := by
      apply Finset.sum_congr rfl
      intro time htime
      unfold quittingFiniteWindowOpponentAbsorptionClock
      rw [if_pos (Finset.mem_range.mp htime)]
    _ = quittingFiniteWindowOpponentAbsorptionMass profile owner cutoff /
        quittingFiniteWindowOpponentAbsorptionMass profile owner cutoff := by
      rw [← Finset.sum_div]
      rfl
    _ = 1 := div_self hpositive.ne'

/-- A unit diffuse finite clock must occupy arbitrarily long windows. -/
theorem QuittingReprojectionDiffuseWindowPacket.cutoff_tendsto_atTop
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : ι} {terminal : {S : Finset ι // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ} {lower : ℝ}
    (packet : QuittingReprojectionDiffuseWindowPacket
      reward profiles owner terminal cutoff scale lower) :
    Tendsto cutoff atTop atTop := by
  rw [tendsto_atTop]
  intro bound
  let epsilon : ℝ := 1 / ((bound : ℝ) + 1)
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    positivity
  filter_upwards [packet.clock_sum,
    packet.clock_mesh epsilon hepsilon] with n hsum hmesh
  by_contra hnot
  have hcutoff : cutoff n ≤ bound := Nat.le_of_not_ge hnot
  have hsumLe :
      ∑ time ∈ Finset.range (cutoff n),
          quittingFiniteWindowCoalitionClock
            (profiles n) terminal (cutoff n) time ≤
        (cutoff n : ℝ) * epsilon := by
    calc
      ∑ time ∈ Finset.range (cutoff n),
          quittingFiniteWindowCoalitionClock
            (profiles n) terminal (cutoff n) time ≤
        ∑ _time ∈ Finset.range (cutoff n), epsilon := by
          exact Finset.sum_le_sum fun time _ => (hmesh time).le
      _ = (cutoff n : ℝ) * epsilon := by simp
  have hcast : (cutoff n : ℝ) ≤ bound := by exact_mod_cast hcutoff
  have hbound : (cutoff n : ℝ) * epsilon ≤ bound * epsilon :=
    mul_le_mul_of_nonneg_right hcast hepsilon.le
  have hfrac : (bound : ℝ) * epsilon < 1 := by
    dsimp only [epsilon]
    rw [one_div, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < bound + 1)).2
    linarith
  linarith

/-- The diffuse deleted-clock branch on the original profile windows. -/
structure QuittingReprojectionDiffuseDeletedWindowPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (owner : ι) (terminal : {S : Finset ι // S.Nonempty})
    (cutoff : ℕ → ℕ) (scale : ℕ → ℝ) (lower : ℝ) where
  source : QuittingReprojectionDiffuseWindowPacket
    reward profiles owner terminal cutoff scale lower
  deletedMassLower : ∀ᶠ n in atTop, lower <
    quittingFiniteWindowOpponentAbsorptionMass
      (profiles n) owner (cutoff n)
  clock_nonneg : ∀ n time, 0 ≤
    quittingFiniteWindowOpponentAbsorptionClock
      (profiles n) owner (cutoff n) time
  clock_sum : ∀ᶠ n in atTop,
    ∑ time ∈ Finset.range (cutoff n),
      quittingFiniteWindowOpponentAbsorptionClock
        (profiles n) owner (cutoff n) time = 1
  clock_mesh : ∀ ε, 0 < ε → ∀ᶠ n in atTop, ∀ time,
    quittingFiniteWindowOpponentAbsorptionClock
      (profiles n) owner (cutoff n) time < ε

theorem quittingFiniteWindowOpponentAbsorptionClock_nonneg
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (cutoff time : ℕ) :
    0 ≤ quittingFiniteWindowOpponentAbsorptionClock
      profile owner cutoff time := by
  unfold quittingFiniteWindowOpponentAbsorptionClock
  split_ifs
  · exact div_nonneg
      (quittingStageOpponentAbsorptionMass_nonneg profile owner time)
      (Finset.sum_nonneg fun stage _ =>
        quittingStageOpponentAbsorptionMass_nonneg profile owner stage)
  · exact le_rfl

/-- If the actual deleted-player stage clock has no recurrent atom, then its
normalization on the original windows is itself a complete diffuse clock.
All rows, shifted tails, and cutoffs remain those of the source profiles. -/
theorem QuittingReprojectionDiffuseWindowPacket.toDiffuseDeletedWindowPacket
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : ι} {terminal : {S : Finset ι // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ} {lower : ℝ}
    (packet : QuittingReprojectionDiffuseWindowPacket
      reward profiles owner terminal cutoff scale lower)
    (other : ι) (hother : other ∈ terminal.val) (hne : other ≠ owner)
    (hdiffuse : ∀ resolution, 0 < resolution →
      ∀ᶠ n in atTop, ∀ time < cutoff n,
        quittingStageOpponentAbsorptionMass
          (profiles n) owner time < resolution) :
    Nonempty (QuittingReprojectionDiffuseDeletedWindowPacket
      reward profiles owner terminal cutoff scale lower) := by
  have hdeletedLower : ∀ᶠ n in atTop, lower <
      quittingFiniteWindowOpponentAbsorptionMass
        (profiles n) owner (cutoff n) := by
    filter_upwards [packet.windowMass] with n hn
    exact hn.trans_le
      (quittingFiniteWindowCoalitionMass_le_opponentAbsorptionMass
        (profiles n) terminal owner other (cutoff n) hother hne)
  refine ⟨{
    source := packet
    deletedMassLower := hdeletedLower
    clock_nonneg := fun n time =>
      quittingFiniteWindowOpponentAbsorptionClock_nonneg
        (profiles n) owner (cutoff n) time
    clock_sum := ?_
    clock_mesh := ?_ }⟩
  · filter_upwards [hdeletedLower] with n hn
    exact sum_quittingFiniteWindowOpponentAbsorptionClock_eq_one
      (profiles n) owner (cutoff n) (packet.lower_pos.trans hn)
  · intro epsilon hepsilon
    have hthreshold : 0 < epsilon * lower :=
      mul_pos hepsilon packet.lower_pos
    filter_upwards [hdeletedLower,
      hdiffuse (epsilon * lower) hthreshold] with n hn hmesh time
    unfold quittingFiniteWindowOpponentAbsorptionClock
    split_ifs with htime
    · apply (div_lt_iff₀ (packet.lower_pos.trans hn)).2
      calc
        quittingStageOpponentAbsorptionMass (profiles n) owner time <
            epsilon * lower := hmesh time htime
        _ < epsilon * quittingFiniteWindowOpponentAbsorptionMass
            (profiles n) owner (cutoff n) :=
          mul_lt_mul_of_pos_left hn hepsilon
    · exact hepsilon

/-- **Deleted-clock temporal split.**  On the original profile windows,
either the owner-deleted absorption clock has a cofinally recurring stage
atom, or its normalization is a complete diffuse deleted-player clock.  This
is exhaustive and retains the source packet's universal moving-mark defect
estimate in the second branch. -/
theorem QuittingReprojectionDiffuseWindowPacket.exists_deletedStageAtom_or_diffuseDeleted
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : ι} {terminal : {S : Finset ι // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ} {lower : ℝ}
    (packet : QuittingReprojectionDiffuseWindowPacket
      reward profiles owner terminal cutoff scale lower)
    (other : ι) (hother : other ∈ terminal.val) (hne : other ≠ owner) :
    (∃ resolution, 0 < resolution ∧
      ∃ᶠ n in atTop, ∃ time < cutoff n,
        resolution ≤ quittingStageOpponentAbsorptionMass
          (profiles n) owner time) ∨
      Nonempty (QuittingReprojectionDiffuseDeletedWindowPacket
        reward profiles owner terminal cutoff scale lower) := by
  by_cases hatom : ∃ resolution, 0 < resolution ∧
      ∃ᶠ n in atTop, ∃ time < cutoff n,
        resolution ≤ quittingStageOpponentAbsorptionMass
          (profiles n) owner time
  · exact Or.inl hatom
  · right
    apply packet.toDiffuseDeletedWindowPacket other hother hne
    intro resolution hresolution
    by_contra hnot
    push Not at hnot
    apply hatom
    exact ⟨resolution, hresolution, hnot⟩

/-- The game-facing form of the deleted-clock split: the atomic branch is an
actual concentrated reprojection packet with a fixed opponent/coalition label
and the correct owner-defect normalization; otherwise the original windows
carry a complete diffuse deleted-player clock. -/
theorem QuittingReprojectionDiffuseWindowPacket.exists_concentrated_or_diffuseDeleted
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : ι} {terminal : {S : Finset ι // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ} {lower : ℝ}
    (packet : QuittingReprojectionDiffuseWindowPacket
      reward profiles owner terminal cutoff scale lower)
    (other : ι) (hother : other ∈ terminal.val) (hne : other ≠ owner)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M) :
    (∃ fixedOther : ι,
      ∃ exact : {S : Finset ι // S.Nonempty},
        fixedOther ≠ owner ∧ fixedOther ∈ exact.val ∧
          Nonempty (QuittingReprojectionConcentratedPacket
            reward profiles owner exact cutoff scale)) ∨
      Nonempty (QuittingReprojectionDiffuseDeletedWindowPacket
        reward profiles owner terminal cutoff scale lower) := by
  rcases packet.exists_deletedStageAtom_or_diffuseDeleted
      other hother hne with hatom | hdiffuse
  · obtain ⟨resolution, hresolution, hfrequent⟩ := hatom
    exact Or.inl
      (packet.exists_concentratedPacket_of_deletedStageAtom
        hresolution hfrequent hM hreward)
  · exact Or.inr hdiffuse

/-- **Arbitrary-depth matched semantic chronology.**  Positive global
minimum debt and diffuse cutoff growth put every fixed finite prefix of the
source profiles on one common, literal shifted-tail chronology.  Each tail is
in the carrier and remains above the same positive minimum; each adjacent row
is the exact semantic prefix of that very tail by that very live root.

This is the state-matching part of the conditioned adapter.  It deliberately
does not assert exact root Nash or positive eventual absorption beyond the
finite window. -/
theorem QuittingReprojectionDiffuseWindowPacket.eventually_matchedChronology
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : ι} {terminal : {S : Finset ι // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ} {lower : ℝ}
    (packet : QuittingReprojectionDiffuseWindowPacket
      reward profiles owner terminal cutoff scale lower)
    (minimum : QuittingTerminalSemanticPair ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (depth : ℕ) :
    ∀ᶠ n in atTop, depth ≤ cutoff n ∧
      ∀ time < depth,
        let current := quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward (profiles n) time)
        let tail := quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward (profiles n) (time + 1))
        let root := quittingProfileLiveRoot reward (profiles n) time
        current ∈ quittingTerminalSemanticCarrier reward ∧
          tail ∈ quittingTerminalSemanticCarrier reward ∧
          0 < quittingTerminalSemanticDebtSum minimum ∧
          quittingTerminalSemanticDebtSum minimum ≤
            quittingTerminalSemanticDebtSum tail ∧
          current = quittingTerminalSemanticPrefix reward root tail := by
  have hcutoff : ∀ᶠ n in atTop, depth ≤ cutoff n :=
    (packet.cutoff_tendsto_atTop.eventually (Ici_mem_atTop depth))
  filter_upwards [hcutoff] with n hn
  refine ⟨hn, ?_⟩
  intro time _htime
  let current := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward (profiles n) time)
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward (profiles n) (time + 1))
  let root := quittingProfileLiveRoot reward (profiles n) time
  have hcurrent : current ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have htail : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  refine ⟨hcurrent, htail, hpositive, hminimum tail htail, ?_⟩
  exact quittingTerminalSemanticPair_spine_eq_prefix
    reward (profiles n) time hM hreward

end GameTheory
