/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionWindow

/-!
# Temporal concentration or diffusion at a reset reprojection

The executable reprojection packet retains a fixed coalition in finite windows,
but those windows may drift.  This file gives the exact exhaustive temporal
split.  Either a fixed positive stage atom recurs cofinally, producing a
literal marked semantic edge, or the window mass defines a unit finite clock
whose mesh tends to zero.  Both branches retain the same survival-weighted
Bellman-defect normalization.

The diffuse clock is profile-owned and coalition-specific.  It is not by
itself a conditioned-diffuse certificate: no exact-Nash policy or common
shifted-tail state is inferred from temporal disintegration.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- Total mass of one coalition inside a selected finite chronological
window. -/
def quittingFiniteWindowCoalitionMass
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset iota // S.Nonempty}) (cutoff : ℕ) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    quittingStageCoalitionMass reward profile time terminal

/-- The coalition's stage mass normalized by its selected finite-window mass,
and extended by zero outside that window. -/
def quittingFiniteWindowCoalitionClock
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset iota // S.Nonempty}) (cutoff time : ℕ) : ℝ :=
  if time < cutoff then
    quittingStageCoalitionMass reward profile time terminal /
      quittingFiniteWindowCoalitionMass profile terminal cutoff
  else 0

theorem quittingFiniteWindowCoalitionClock_nonneg
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset iota // S.Nonempty}) (cutoff time : ℕ) :
    0 ≤ quittingFiniteWindowCoalitionClock profile terminal cutoff time := by
  unfold quittingFiniteWindowCoalitionClock
  split_ifs
  · exact div_nonneg
      (quittingStageCoalitionMass_nonneg reward profile time terminal)
      (Finset.sum_nonneg fun stage _ =>
        quittingStageCoalitionMass_nonneg reward profile stage terminal)
  · exact le_rfl

theorem sum_quittingFiniteWindowCoalitionClock_eq_one
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset iota // S.Nonempty}) (cutoff : ℕ)
    (hpositive : 0 <
      quittingFiniteWindowCoalitionMass profile terminal cutoff) :
    ∑ time ∈ Finset.range cutoff,
      quittingFiniteWindowCoalitionClock profile terminal cutoff time = 1 := by
  calc
    ∑ time ∈ Finset.range cutoff,
        quittingFiniteWindowCoalitionClock profile terminal cutoff time =
      ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time terminal /
          quittingFiniteWindowCoalitionMass profile terminal cutoff := by
      apply Finset.sum_congr rfl
      intro time htime
      unfold quittingFiniteWindowCoalitionClock
      rw [if_pos (Finset.mem_range.mp htime)]
    _ = quittingFiniteWindowCoalitionMass profile terminal cutoff /
        quittingFiniteWindowCoalitionMass profile terminal cutoff := by
      rw [← Finset.sum_div]
      rfl
    _ = 1 := div_self hpositive.ne'

/-- The normalized moving-row defect conclusion, separated for reuse in both
temporal branches. -/
theorem tendsto_normalized_moving_coordinateNashDefect_zero
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (owner : iota) (scale : ℕ → ℝ) (mark : ℕ → ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hscale : ∀ n, 0 < scale n)
    (hratio : Tendsto (fun n ↦
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (profiles n)) owner /
        scale n) atTop (nhds 0)) :
    Tendsto (fun n ↦
      (quittingLiveMass reward (profiles n) (mark n) *
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward (profiles n)
              (mark n + 1))).1
          (quittingProfileLiveRoot reward (profiles n) (mark n)) owner) /
        scale n) atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact div_nonneg
      (mul_nonneg (quittingLiveMass_nonneg reward (profiles n) (mark n))
        (quittingRootCoordinateNashDefect_nonneg reward _ _ owner))
      (hscale n).le
  · intro n
    apply (div_le_div_iff_of_pos_right (hscale n)).2
    exact quittingLiveMass_mul_coordinateNashDefect_le_initialDebt
      (reward := reward) (profiles n) owner (mark n) hM hreward
  · exact hratio

/-- A cofinally recurring positive stage atom, with its literal semantic edge
and matched normalized owner defect. -/
structure QuittingReprojectionConcentratedPacket
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (owner : iota) (terminal : {S : Finset iota // S.Nonempty})
    (cutoff : ℕ → ℕ) (scale : ℕ → ℝ) where
  resolution : ℝ
  resolution_pos : 0 < resolution
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  mark : ℕ → ℕ
  mark_lt : ∀ rank, mark rank < cutoff (subseq rank)
  stageMass : ∀ rank, resolution ≤
    quittingStageCoalitionMass reward (profiles (subseq rank))
      (mark rank) terminal
  semanticPrefix : ∀ rank,
    let profile := profiles (subseq rank)
    let time := mark rank
    let current := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile time)
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (time + 1))
    let root := quittingProfileLiveRoot reward profile time
    current ∈ quittingTerminalSemanticCarrier reward ∧
      tail ∈ quittingTerminalSemanticCarrier reward ∧
      current = quittingTerminalSemanticPrefix reward root tail ∧
      0 < quittingRootCoalitionMass root terminal.val
  defect_tendsto : Tendsto (fun rank ↦
    (quittingLiveMass reward (profiles (subseq rank)) (mark rank) *
      quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward (profiles (subseq rank))
            (mark rank + 1))).1
        (quittingProfileLiveRoot reward (profiles (subseq rank))
          (mark rank)) owner) /
      scale (subseq rank)) atTop (nhds 0)

/-- A positive finite coalition clock with asymptotically vanishing mesh,
retaining the same moving-row defect normalization. -/
structure QuittingReprojectionDiffuseWindowPacket
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (owner : iota) (terminal : {S : Finset iota // S.Nonempty})
    (cutoff : ℕ → ℕ) (scale : ℕ → ℝ) (lower : ℝ) where
  lower_pos : 0 < lower
  windowMass : ∀ᶠ n in atTop, lower <
    quittingFiniteWindowCoalitionMass (profiles n) terminal (cutoff n)
  clock_nonneg : ∀ n time, 0 ≤
    quittingFiniteWindowCoalitionClock (profiles n) terminal (cutoff n) time
  clock_sum : ∀ᶠ n in atTop,
    ∑ time ∈ Finset.range (cutoff n),
      quittingFiniteWindowCoalitionClock
        (profiles n) terminal (cutoff n) time = 1
  clock_mesh : ∀ ε, 0 < ε → ∀ᶠ n in atTop, ∀ time,
    quittingFiniteWindowCoalitionClock
      (profiles n) terminal (cutoff n) time < ε
  defect_tendsto : ∀ mark : ℕ → ℕ,
    Tendsto (fun n ↦
      (quittingLiveMass reward (profiles n) (mark n) *
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward (profiles n)
              (mark n + 1))).1
          (quittingProfileLiveRoot reward (profiles n) (mark n)) owner) /
        scale n) atTop (nhds 0)

/-- **Exact temporal tightness split.**  A uniformly positive coalition mass
in profile-dependent finite windows either has a cofinally recurring atom of
fixed size, or its normalized finite clock has mesh tending to zero.  No mass,
profile provenance, or Bellman-defect normalization is discarded. -/
theorem exists_concentrated_or_diffuseWindowPacket
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (owner : iota) (terminal : {S : Finset iota // S.Nonempty})
    (cutoff : ℕ → ℕ) (scale : ℕ → ℝ) (lower : ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hlower : 0 < lower)
    (hwindow : ∀ᶠ n in atTop, lower <
      quittingFiniteWindowCoalitionMass (profiles n) terminal (cutoff n))
    (hscale : ∀ n, 0 < scale n)
    (hratio : Tendsto (fun n ↦
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (profiles n)) owner /
        scale n) atTop (nhds 0)) :
    Nonempty (QuittingReprojectionConcentratedPacket
      reward profiles owner terminal cutoff scale) ∨
    Nonempty (QuittingReprojectionDiffuseWindowPacket
      reward profiles owner terminal cutoff scale lower) := by
  classical
  by_cases hconcentrated : ∃ resolution : ℝ, 0 < resolution ∧
      ∃ᶠ n in atTop, ∃ time < cutoff n,
        resolution ≤ quittingStageCoalitionMass reward (profiles n)
          time terminal
  · obtain ⟨resolution, hresolution, hfrequent⟩ := hconcentrated
    obtain ⟨subseq, hsubseq, hwitness⟩ :=
      extraction_of_frequently_atTop hfrequent
    choose mark hmarkLt hmarkMass using hwitness
    left
    refine ⟨{
      resolution := resolution
      resolution_pos := hresolution
      subseq := subseq
      subseq_strictMono := hsubseq
      mark := mark
      mark_lt := hmarkLt
      stageMass := hmarkMass
      semanticPrefix := ?_
      defect_tendsto := ?_ }⟩
    · intro rank
      exact positive_stageCoalitionMass_has_semanticPrefixIncidence
        reward (profiles (subseq rank)) (mark rank) terminal hM hreward
          (hresolution.trans_le (hmarkMass rank))
    · exact
        (tendsto_normalized_moving_coordinateNashDefect_zero
          (reward := reward) (fun rank => profiles (subseq rank)) owner
          (fun rank => scale (subseq rank)) mark hM hreward
          (fun rank => hscale (subseq rank))
          (hratio.comp hsubseq.tendsto_atTop))
  · have hdiffuse : ∀ resolution : ℝ, 0 < resolution →
        ∀ᶠ n in atTop, ∀ time < cutoff n,
          quittingStageCoalitionMass reward (profiles n) time terminal <
            resolution := by
      intro resolution hresolution
      by_contra hnot
      push Not at hnot
      apply hconcentrated
      refine ⟨resolution, hresolution, ?_⟩
      exact hnot
    right
    refine ⟨{
      lower_pos := hlower
      windowMass := hwindow
      clock_nonneg := fun n time =>
        quittingFiniteWindowCoalitionClock_nonneg
          (reward := reward) (profiles n) terminal (cutoff n) time
      clock_sum := ?_
      clock_mesh := ?_
      defect_tendsto := fun mark =>
        tendsto_normalized_moving_coordinateNashDefect_zero
          (reward := reward) profiles owner scale mark hM hreward hscale
            hratio }⟩
    · filter_upwards [hwindow] with n hn
      exact sum_quittingFiniteWindowCoalitionClock_eq_one
        (reward := reward) (profiles n) terminal (cutoff n)
          (hlower.trans hn)
    · intro ε hε
      have hthreshold : 0 < ε * lower := mul_pos hε hlower
      filter_upwards [hwindow, hdiffuse (ε * lower) hthreshold] with n
          hn hmesh time
      unfold quittingFiniteWindowCoalitionClock
      split_ifs with htime
      · apply (div_lt_iff₀ (hlower.trans hn)).2
        calc
          quittingStageCoalitionMass reward (profiles n) time terminal <
              ε * lower := hmesh time htime
          _ < ε * quittingFiniteWindowCoalitionMass
                (profiles n) terminal (cutoff n) :=
            mul_lt_mul_of_pos_left hn hε
      · exact hε

/-- **Game-facing temporal-tightness capstone.**  The literal profiles supplied
by an executable positive-incidence germ share one fixed opponent/coalition
and an exhaustive concentrated-or-diffuse chronological packet on the same
surface-tension scale. -/
theorem exists_sameProfile_temporalTightnessSplit
    (contact : QuittingTerminalSemanticLawPoint iota)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (owner : iota) (scale : ℕ → ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcontact : contact ∈ quittingTerminalSemanticLawCarrier reward)
    (hprofiles : Tendsto (fun n ↦
      (quittingTerminalSemanticPair reward (profiles n),
        quittingTerminalOutcomeMass reward (profiles n)))
      atTop (nhds contact))
    (hincidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner contact.2)
    (hscale : ∀ n, 0 < scale n)
    (hratio : Tendsto (fun n ↦
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (profiles n)) owner /
        scale n) atTop (nhds 0)) :
    ∃ other : iota, ∃ terminal : {S : Finset iota // S.Nonempty},
      ∃ lower : ℝ, ∃ cutoff : ℕ → ℕ,
      other ≠ owner ∧ other ∈ terminal.val ∧ 0 < lower ∧
      (Nonempty (QuittingReprojectionConcentratedPacket
          reward profiles owner terminal cutoff scale) ∨
        Nonempty (QuittingReprojectionDiffuseWindowPacket
          reward profiles owner terminal cutoff scale lower)) := by
  obtain ⟨other, terminal, lower, cutoff, hother, hterminal, hlower,
      hwindow, _hdefect⟩ :=
    exists_sameProfile_finiteWindow_defectPacket
      (reward := reward) contact profiles owner scale hM hreward hcontact
        hprofiles hincidence hscale hratio
  have hsplit := exists_concentrated_or_diffuseWindowPacket
    (reward := reward) profiles owner terminal cutoff scale lower hM hreward
      hlower (by simpa [quittingFiniteWindowCoalitionMass] using hwindow)
        hscale hratio
  exact ⟨other, terminal, lower, cutoff, hother, hterminal, hlower, hsplit⟩

end GameTheory
