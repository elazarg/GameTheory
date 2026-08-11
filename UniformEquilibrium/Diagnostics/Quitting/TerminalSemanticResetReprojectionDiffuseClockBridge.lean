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

/-- An exact coalition containing two distinct players is bounded by the
product of their two Quit probabilities.  This is the fixed-label form of
the product-law collision estimate and has no cardinality loss. -/
theorem quittingRootCoalitionMass_le_mul_quitProbability_of_mem
    (root : ι → PMF Bool) (coalition : Finset ι)
    {first second : ι} (hne : first ≠ second)
    (hfirst : first ∈ coalition) (hsecond : second ∈ coalition) :
    quittingRootCoalitionMass root coalition ≤
      (root first true).toReal * (root second true).toReal := by
  let rate : ι → ℝ := fun who => (root who true).toReal
  have hrate0 : ∀ who, 0 ≤ rate who := fun _ => ENNReal.toReal_nonneg
  have hrate1 : ∀ who, rate who ≤ 1 := fun who =>
    ENNReal.toReal_mono ENNReal.one_ne_top ((root who).coe_le_one true)
  have hsecondErase : second ∈ coalition.erase first := by
    exact Finset.mem_erase.mpr ⟨hne.symm, hsecond⟩
  have hrest0 : 0 ≤ ∏ who ∈ (coalition.erase first).erase second, rate who :=
    Finset.prod_nonneg fun who _ => hrate0 who
  have hrest1 : (∏ who ∈ (coalition.erase first).erase second, rate who) ≤ 1 :=
    Finset.prod_le_one
      (fun who _ => hrate0 who)
      (fun who _ => hrate1 who)
  have hout0 : 0 ≤ ∏ who ∈ coalitionᶜ, (1 - rate who) :=
    Finset.prod_nonneg fun who _ => sub_nonneg.mpr (hrate1 who)
  have hout1 : (∏ who ∈ coalitionᶜ, (1 - rate who)) ≤ 1 :=
    Finset.prod_le_one
      (fun who _ => sub_nonneg.mpr (hrate1 who))
      (fun who _ => by linarith [hrate0 who])
  have hinside : (∏ who ∈ coalition, rate who) =
      ((∏ who ∈ (coalition.erase first).erase second, rate who) *
          rate second) * rate first := by
    calc
      (∏ who ∈ coalition, rate who) =
          (∏ who ∈ coalition.erase first, rate who) * rate first := by
            simpa using (Finset.prod_erase_mul coalition rate hfirst).symm
      _ = ((∏ who ∈ (coalition.erase first).erase second, rate who) *
          rate second) * rate first := by
            rw [show (∏ who ∈ coalition.erase first, rate who) =
              (∏ who ∈ (coalition.erase first).erase second, rate who) *
                rate second by
              simpa using (Finset.prod_erase_mul
                (coalition.erase first) rate hsecondErase).symm]
  have hinsideLe : (∏ who ∈ coalition, rate who) ≤
      rate first * rate second := by
    rw [hinside]
    calc
      ((∏ who ∈ (coalition.erase first).erase second, rate who) *
          rate second) * rate first =
          (∏ who ∈ (coalition.erase first).erase second, rate who) *
            (rate first * rate second) := by ring
      _ ≤ 1 * (rate first * rate second) :=
        mul_le_mul_of_nonneg_right hrest1
          (mul_nonneg (hrate0 first) (hrate0 second))
      _ = rate first * rate second := one_mul _
  unfold quittingRootCoalitionMass Math.PMFProduct.coalitionMass
    quittingRootQuitRates
  change (∏ who ∈ coalition, rate who) *
      (∏ who ∈ coalitionᶜ, (1 - rate who)) ≤ rate first * rate second
  exact (mul_le_of_le_one_right
    (Finset.prod_nonneg fun who _ => hrate0 who) hout1).trans hinsideLe

/-- One exact terminal cylinder is paid by the loss of live mass across the
same finite suffix.  The statement is deliberately offset-indexed so that it
can be applied after the first large raw opponent hazard. -/
theorem sum_quittingStageCoalitionMass_add_le_liveMass
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) (start fuel : ℕ) :
    ∑ offset ∈ Finset.range fuel,
        quittingStageCoalitionMass reward profile (start + offset) terminal ≤
      quittingLiveMass reward profile start := by
  have hstep : ∀ time,
      quittingStageCoalitionMass reward profile time terminal ≤
        quittingLiveMass reward profile time -
          quittingLiveMass reward profile (time + 1) := by
    intro time
    let root := quittingProfileLiveRoot reward profile time
    have hrootMass : quittingRootCoalitionMass root terminal.val ≤
        quittingRootAbsorptionMass root := by
      unfold quittingRootAbsorptionMass
      rw [← quittingRootCoalitionMass_sum_nonempty]
      apply Finset.single_le_sum
      · intro coalition _
        exact MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
          root coalition
      · simp [terminal.property.ne_empty]
    have hjoint : quittingJointContinueMass reward profile time =
        quittingStationaryContinueMass root := by
      rw [quittingJointContinueMass_eq_product,
        quittingStationaryContinueMass_eq_prod_continueProbability]
      rfl
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
      quittingLiveMass_succ, hjoint]
    calc
      quittingLiveMass reward profile time *
          quittingRootCoalitionMass
            (quittingProfileLiveRoot reward profile time) terminal.val ≤
        quittingLiveMass reward profile time *
          quittingRootAbsorptionMass root :=
            mul_le_mul_of_nonneg_left hrootMass
              (quittingLiveMass_nonneg reward profile time)
      _ = quittingLiveMass reward profile time -
          quittingLiveMass reward profile time *
            quittingStationaryContinueMass root := by
        unfold quittingRootAbsorptionMass
        ring
  have htelescope : ∀ fuel,
      (∑ offset ∈ Finset.range fuel,
          quittingStageCoalitionMass reward profile (start + offset) terminal) ≤
        quittingLiveMass reward profile start -
          quittingLiveMass reward profile (start + fuel) := by
    intro length
    induction length with
    | zero => simp
    | succ length ih =>
        rw [Finset.sum_range_succ]
        have hlast := hstep (start + length)
        norm_num [Nat.add_assoc] at hlast ⊢
        linarith
  have h := htelescope fuel
  linarith [quittingLiveMass_nonneg reward profile (start + fuel)]

omit [DecidableEq ι] in
theorem quittingRoot_quitProbability_le_absorptionMass'
    (root : ι → PMF Bool) (who : ι) :
    (root who true).toReal ≤ quittingRootAbsorptionMass root := by
  have hcontinue :=
    quittingStationaryContinueMass_le_ownContinueProbability root who
  have hprobability :=
    quittingRoot_continueProbability_add_quitProbability root who
  unfold quittingRootAbsorptionMass
  linarith

omit [DecidableEq ι] in
/-- Total absorption in a finite suffix is at most the mass live at its
entrance. -/
theorem sum_quittingLiveMass_mul_rootAbsorptionMass_add_le_liveMass
    (profile : (quittingGame reward).BehaviorProfile) (start fuel : ℕ) :
    ∑ offset ∈ Finset.range fuel,
        quittingLiveMass reward profile (start + offset) *
          quittingRootAbsorptionMass
            (quittingProfileLiveRoot reward profile (start + offset)) ≤
      quittingLiveMass reward profile start := by
  have hstep : ∀ time,
      quittingLiveMass reward profile time *
          quittingRootAbsorptionMass
            (quittingProfileLiveRoot reward profile time) =
        quittingLiveMass reward profile time -
          quittingLiveMass reward profile (time + 1) := by
    intro time
    have hjoint : quittingJointContinueMass reward profile time =
        quittingStationaryContinueMass
          (quittingProfileLiveRoot reward profile time) := by
      rw [quittingJointContinueMass_eq_product,
        quittingStationaryContinueMass_eq_prod_continueProbability]
      rfl
    rw [quittingLiveMass_succ, hjoint]
    unfold quittingRootAbsorptionMass
    ring
  have htelescope : ∀ fuel,
      (∑ offset ∈ Finset.range fuel,
          quittingLiveMass reward profile (start + offset) *
            quittingRootAbsorptionMass
              (quittingProfileLiveRoot reward profile (start + offset))) =
        quittingLiveMass reward profile start -
          quittingLiveMass reward profile (start + fuel) := by
    intro length
    induction length with
    | zero => simp
    | succ length ih =>
        rw [Finset.sum_range_succ, ih, hstep]
        norm_num [Nat.add_assoc]
  rw [htelescope]
  exact sub_le_self _
    (quittingLiveMass_nonneg reward profile (start + fuel))

theorem quittingFiniteWindowOpponentAbsorptionMass_le_one
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (cutoff : ℕ) :
    quittingFiniteWindowOpponentAbsorptionMass profile owner cutoff ≤ 1 := by
  unfold quittingFiniteWindowOpponentAbsorptionMass
    quittingStageOpponentAbsorptionMass
  calc
    (∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingRootOpponentAbsorptionMass
            (quittingProfileLiveRoot reward profile time) owner) ≤
        ∑ time ∈ Finset.range cutoff,
          quittingLiveMass reward profile time *
            quittingRootAbsorptionMass
              (quittingProfileLiveRoot reward profile time) := by
      apply Finset.sum_le_sum
      intro time _
      exact mul_le_mul_of_nonneg_left
        (quittingRootOpponentAbsorptionMass_le_absorptionMass
          (quittingProfileLiveRoot reward profile time) owner)
        (quittingLiveMass_nonneg reward profile time)
    _ ≤ quittingLiveMass reward profile 0 := by
      simpa using
        (sum_quittingLiveMass_mul_rootAbsorptionMass_add_le_liveMass
          (reward := reward) profile 0 cutoff)
    _ = 1 := by simp [quittingLiveMass]

/-- **First-large-hazard estimate.**  Suppose a fixed exact coalition is
bounded at every row by `gate * opponentHazard`, where `gate` is itself paid
by joint absorption.  If every normalized survival-weighted opponent atom is
smaller than `delta`, then the coalition's normalized finite-window mass is
smaller than `eta / lower + delta / eta`.

The raw opponent hazard need not be small.  At its first `eta`-large row the
clock bound makes the remaining live mass small; the whole suffix is then
paid by that live mass. -/
theorem quittingFiniteWindowCoalitionMass_div_opponentAbsorptionMass_lt
    (profile : (quittingGame reward).BehaviorProfile)
    (owner : ι) (terminal : {S : Finset ι // S.Nonempty})
    (cutoff : ℕ) (gate : ℕ → ℝ)
    (hgate0 : ∀ time, 0 ≤ gate time)
    (hgateAbsorption : ∀ time, gate time ≤
      quittingRootAbsorptionMass
        (quittingProfileLiveRoot reward profile time))
    (hcoalition : ∀ time,
      quittingRootCoalitionMass
          (quittingProfileLiveRoot reward profile time) terminal.val ≤
        gate time * quittingRootOpponentAbsorptionMass
          (quittingProfileLiveRoot reward profile time) owner)
    {lower delta eta : ℝ} (hlower : 0 < lower)
    (hwindow : lower <
      quittingFiniteWindowOpponentAbsorptionMass profile owner cutoff)
    (hdelta : 0 ≤ delta) (heta : 0 < eta)
    (hmesh : ∀ time < cutoff,
      quittingFiniteWindowOpponentAbsorptionClock
        profile owner cutoff time < delta) :
    quittingFiniteWindowCoalitionMass profile terminal cutoff /
        quittingFiniteWindowOpponentAbsorptionMass profile owner cutoff <
      eta / lower + delta / eta := by
  let live : ℕ → ℝ := fun time => quittingLiveMass reward profile time
  let root : ℕ → ι → PMF Bool := fun time =>
    quittingProfileLiveRoot reward profile time
  let opponent : ℕ → ℝ := fun time =>
    quittingRootOpponentAbsorptionMass (root time) owner
  let total := quittingFiniteWindowOpponentAbsorptionMass
    profile owner cutoff
  have htotal : 0 < total := hlower.trans hwindow
  have hlive0 : ∀ time, 0 ≤ live time := fun time =>
    quittingLiveMass_nonneg reward profile time
  have hopponent0 : ∀ time, 0 ≤ opponent time := fun time =>
    quittingRootOpponentAbsorptionMass_nonneg (root time) owner
  have hclock : ∀ time < cutoff,
      live time * opponent time / total < delta := by
    intro time htime
    have h := hmesh time htime
    simpa [quittingFiniteWindowOpponentAbsorptionClock,
      quittingStageOpponentAbsorptionMass, live, root, opponent, total,
      htime] using h
  have hsmallPrefix : ∀ length ≤ cutoff,
      (∀ time < length, opponent time < eta) →
      (∑ time ∈ Finset.range length,
          quittingStageCoalitionMass reward profile time terminal) ≤ eta := by
    intro length hlength hsmall
    have hgateSum :
        (∑ time ∈ Finset.range length, live time * gate time) ≤ 1 := by
      calc
        (∑ time ∈ Finset.range length, live time * gate time) ≤
            ∑ time ∈ Finset.range length,
              live time * quittingRootAbsorptionMass (root time) := by
          apply Finset.sum_le_sum
          intro time _
          exact mul_le_mul_of_nonneg_left (by
            simpa [root] using hgateAbsorption time) (hlive0 time)
        _ ≤ live 0 := by
          simpa [live, root] using
            (sum_quittingLiveMass_mul_rootAbsorptionMass_add_le_liveMass
              (reward := reward) profile 0 length)
        _ = 1 := by simp [live, quittingLiveMass]
    calc
      (∑ time ∈ Finset.range length,
          quittingStageCoalitionMass reward profile time terminal) ≤
          ∑ time ∈ Finset.range length,
            live time * (gate time * opponent time) := by
        apply Finset.sum_le_sum
        intro time _
        rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
        exact mul_le_mul_of_nonneg_left (by
          simpa [root, opponent] using hcoalition time) (hlive0 time)
      _ ≤ ∑ time ∈ Finset.range length,
          eta * (live time * gate time) := by
        apply Finset.sum_le_sum
        intro time htime
        have hopponentLt := hsmall time (Finset.mem_range.mp htime)
        have hgateLive : 0 ≤ live time * gate time :=
          mul_nonneg (hlive0 time) (hgate0 time)
        calc
          live time * (gate time * opponent time) =
              (live time * gate time) * opponent time := by ring
          _ ≤ (live time * gate time) * eta :=
            mul_le_mul_of_nonneg_left hopponentLt.le hgateLive
          _ = eta * (live time * gate time) := by ring
      _ = eta * ∑ time ∈ Finset.range length,
          live time * gate time := by rw [Finset.mul_sum]
      _ ≤ eta * 1 := mul_le_mul_of_nonneg_left hgateSum heta.le
      _ = eta := mul_one eta
  by_cases hlarge : ∃ time < cutoff, eta ≤ opponent time
  · let first := Nat.find hlarge
    have hfirst := Nat.find_spec hlarge
    have hfirstCutoff : first < cutoff := hfirst.1
    have hfirstLarge : eta ≤ opponent first := hfirst.2
    have hbefore : ∀ time < first, opponent time < eta := by
      intro time htime
      have htimeCutoff : time < cutoff := htime.trans hfirstCutoff
      exact lt_of_not_ge fun hge => by
        have hle : first ≤ time :=
          Nat.find_min' hlarge ⟨htimeCutoff, hge⟩
        omega
    have hprefix :
        (∑ time ∈ Finset.range first,
          quittingStageCoalitionMass reward profile time terminal) ≤ eta :=
      hsmallPrefix first hfirstCutoff.le hbefore
    have htail :
        (∑ offset ∈ Finset.range (cutoff - first),
          quittingStageCoalitionMass reward profile (first + offset)
            terminal) ≤ live first := by
      simpa [live] using sum_quittingStageCoalitionMass_add_le_liveMass
        (reward := reward) profile terminal first (cutoff - first)
    have hliveRatio : live first / total < delta / eta := by
      apply (div_lt_div_iff₀ htotal heta).2
      have hstage := (div_lt_iff₀ htotal).1
        (hclock first hfirstCutoff)
      have hlowerStage : live first * eta ≤
          live first * opponent first :=
        mul_le_mul_of_nonneg_left hfirstLarge (hlive0 first)
      nlinarith
    have htotalSplit : quittingFiniteWindowCoalitionMass
        profile terminal cutoff =
        (∑ time ∈ Finset.range first,
          quittingStageCoalitionMass reward profile time terminal) +
        ∑ offset ∈ Finset.range (cutoff - first),
          quittingStageCoalitionMass reward profile (first + offset)
            terminal := by
      unfold quittingFiniteWindowCoalitionMass
      conv_lhs =>
        rw [show cutoff = first + (cutoff - first) by omega,
          Finset.sum_range_add]
    rw [htotalSplit, add_div]
    have hprefixRatio :
        (∑ time ∈ Finset.range first,
          quittingStageCoalitionMass reward profile time terminal) / total <
            eta / lower := by
      exact (div_le_div_of_nonneg_right hprefix htotal.le).trans_lt
        ((div_lt_div_iff_of_pos_left heta htotal hlower).2 hwindow)
    exact add_lt_add hprefixRatio
      ((div_le_div_of_nonneg_right htail htotal.le).trans_lt hliveRatio)
  · have hsmall : ∀ time < cutoff, opponent time < eta := by
      intro time htime
      exact lt_of_not_ge fun hge => hlarge ⟨time, htime, hge⟩
    have hall := hsmallPrefix cutoff le_rfl hsmall
    have hratio : quittingFiniteWindowCoalitionMass
        profile terminal cutoff / total < eta / lower :=
      (div_le_div_of_nonneg_right hall htotal.le).trans_lt
        ((div_lt_div_iff_of_pos_left heta htotal hlower).2 hwindow)
    exact hratio.trans_le (le_add_of_nonneg_right (div_nonneg hdelta heta.le))

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

/-- **Diffuse deleted clocks force a fixed positive coalition to be one
opponent singleton.**  Two opponent members are second order in the raw
opponent hazard.  An owner--opponent coalition is bounded by the owner's Quit
hazard times the opponent hazard.  The first-large-hazard estimate kills both
possibilities while retaining the source packet's absolute positive window
mass. -/
theorem QuittingReprojectionDiffuseDeletedWindowPacket.terminal_eq_singleton
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : ι} {terminal : {S : Finset ι // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ} {lower : ℝ}
    (packet : QuittingReprojectionDiffuseDeletedWindowPacket
      reward profiles owner terminal cutoff scale lower)
    (other : ι) (hother : other ∈ terminal.val) (hne : other ≠ owner) :
    terminal.val = {other} := by
  classical
  let eta := lower ^ 2 / 4
  let delta := eta * lower / 4
  have heta : 0 < eta := by
    dsimp only [eta]
    exact div_pos (sq_pos_of_pos packet.source.lower_pos) (by norm_num)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact div_pos (mul_pos heta packet.source.lower_pos) (by norm_num)
  have hparameter : eta / lower + delta / eta = lower / 2 := by
    dsimp only [eta, delta]
    field_simp [packet.source.lower_pos.ne']
    ring
  let ratio : ℕ → ℝ := fun n =>
    quittingFiniteWindowCoalitionMass
        (profiles n) terminal (cutoff n) /
      quittingFiniteWindowOpponentAbsorptionMass
        (profiles n) owner (cutoff n)
  have impossible_of_upper :
      (∀ᶠ n in atTop, ratio n < lower / 2) → False := by
    intro hupper
    obtain ⟨n, hcoalition, htotal, hnupper⟩ :=
      (packet.source.windowMass.and
        (packet.deletedMassLower.and hupper)).exists
    have htotalPos : 0 < quittingFiniteWindowOpponentAbsorptionMass
        (profiles n) owner (cutoff n) :=
      packet.source.lower_pos.trans htotal
    have htotalOne := quittingFiniteWindowOpponentAbsorptionMass_le_one
      (reward := reward) (profiles n) owner (cutoff n)
    have hnLower : lower < ratio n := by
      apply (lt_div_iff₀ htotalPos).2
      nlinarith [packet.source.lower_pos]
    dsimp only [ratio] at hnupper
    linarith [packet.source.lower_pos]
  have hownerNot : owner ∉ terminal.val := by
    intro howner
    apply impossible_of_upper
    filter_upwards [packet.deletedMassLower,
      packet.clock_mesh delta hdelta] with n htotal hmesh
    let root : ℕ → ι → PMF Bool := fun time =>
      quittingProfileLiveRoot reward (profiles n) time
    let gate : ℕ → ℝ := fun time => (root time owner true).toReal
    have hbound :=
      quittingFiniteWindowCoalitionMass_div_opponentAbsorptionMass_lt
        (reward := reward) (profiles n) owner terminal (cutoff n) gate
        (fun time => ENNReal.toReal_nonneg)
        (fun time => by
          simpa [gate, root] using
            quittingRoot_quitProbability_le_absorptionMass'
              (root time) owner)
        (fun time => by
          have hpair :=
            quittingRootCoalitionMass_le_mul_quitProbability_of_mem
              (root time) terminal.val hne.symm howner hother
          have hotherRate :=
            quittingRoot_quitProbability_le_opponentAbsorptionMass_of_ne
              (root time) hne
          exact hpair.trans (mul_le_mul_of_nonneg_left hotherRate
            ENNReal.toReal_nonneg))
        packet.source.lower_pos htotal hdelta.le heta
        (fun time htime => hmesh time)
    rw [hparameter] at hbound
    exact hbound
  apply Finset.Subset.antisymm
  · intro player hplayer
    simp only [Finset.mem_singleton]
    by_contra hplayerOther
    have hplayerOwner : player ≠ owner := by
      intro heq
      subst player
      exact hownerNot hplayer
    apply impossible_of_upper
    filter_upwards [packet.deletedMassLower,
      packet.clock_mesh delta hdelta] with n htotal hmesh
    let root : ℕ → ι → PMF Bool := fun time =>
      quittingProfileLiveRoot reward (profiles n) time
    let gate : ℕ → ℝ := fun time =>
      quittingRootOpponentAbsorptionMass (root time) owner
    have hbound :=
      quittingFiniteWindowCoalitionMass_div_opponentAbsorptionMass_lt
        (reward := reward) (profiles n) owner terminal (cutoff n) gate
        (fun time => quittingRootOpponentAbsorptionMass_nonneg
          (root time) owner)
        (fun time => quittingRootOpponentAbsorptionMass_le_absorptionMass
          (root time) owner)
        (fun time => by
          have hpair :=
            quittingRootCoalitionMass_le_mul_quitProbability_of_mem
              (root time) terminal.val (Ne.symm hplayerOther) hother hplayer
          have hotherRate :=
            quittingRoot_quitProbability_le_opponentAbsorptionMass_of_ne
              (root time) hne
          have hplayerRate :=
            quittingRoot_quitProbability_le_opponentAbsorptionMass_of_ne
              (root time) hplayerOwner
          have hfirst :
              (root time other true).toReal *
                  (root time player true).toReal ≤
                gate time * (root time player true).toReal :=
            mul_le_mul_of_nonneg_right hotherRate ENNReal.toReal_nonneg
          have hsecond : gate time * (root time player true).toReal ≤
              gate time * gate time :=
            mul_le_mul_of_nonneg_left hplayerRate
              (quittingRootOpponentAbsorptionMass_nonneg
                (root time) owner)
          exact hpair.trans (hfirst.trans hsecond))
        packet.source.lower_pos htotal hdelta.le heta
        (fun time htime => hmesh time)
    rw [hparameter] at hbound
    exact hbound
  · intro player hplayer
    simp only [Finset.mem_singleton] at hplayer
    subst player
    exact hother

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
