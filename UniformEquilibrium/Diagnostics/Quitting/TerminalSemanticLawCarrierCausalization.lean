/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionWindow
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashChronology

/-!
# Causal finite-window realizers for the joint terminal-law carrier

A positive finite-coalition coordinate of a joint semantic/law carrier point
is not merely a simplex annotation.  It is approximated by executable
profiles in which a fixed positive fraction of that coordinate is already
present in a finite chronological window.  Consequently an actual stage of
the same profile carries the displayed coalition with positive mass.

The cutoff may drift and the exposed row need not be Nash or lie on the
minimum-debt fiber.  Those are separate strategic requirements; this module
isolates the unconditional causal content of joint carrier membership.
-/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Exact transport through a finite root word -/

/-- A chronological atom in the terminal continuation is shifted by the
length of a literal root word and scaled by the word's exact joint survival
product. -/
theorem quittingStageCoalitionMass_literalRootStack_add_length
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (time : ℕ) (coalition : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (quittingLiteralRootStackProfile reward roots terminal)
        (roots.length + time) coalition =
      quittingCapNashStackContinueProduct roots *
        quittingStageCoalitionMass reward terminal time coalition := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      rw [quittingLiteralRootStackProfile_cons, List.length_cons,
        quittingCapNashStackContinueProduct_cons]
      rw [show roots.length + 1 + time = (roots.length + time) + 1 by omega,
        quittingStageCoalitionMass_rootThenContinuation_succ, ih]
      ring

/-- **Positive-infimum cap prefixes cannot erase a literal atom.**

An arbitrarily deep exact cap--Nash word may shift a suffix atom, but in the
positive literal-debt-infimum regime it retains an explicit fraction of that
atom.  The fraction is the global infimum divided by the terminal profile's
total debt.  In particular, the shifted atom remains strictly positive.

The selected atom is still a row of the declared terminal suffix, not one of
the exact cap--Nash prefix roots.  This is therefore a provenance/access
theorem rather than the final Nash-row causalization theorem. -/
theorem exists_capNashRootStack_retaining_positiveStage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (time depth : ℕ)
    (coalition : {S : Finset ι // S.Nonempty})
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hinf : 0 < quittingTerminalDebtSumInf reward)
    (hpositive : 0 <
      quittingStageCoalitionMass reward terminal time coalition) :
    ∃ roots : List (ι → PMF Bool),
      roots.length = depth ∧
      IsQuittingCapNashRootStack reward roots terminal ∧
      quittingTerminalDebtSumInf reward /
            quittingTerminalDebtSum reward terminal *
          quittingStageCoalitionMass reward terminal time coalition ≤
        quittingStageCoalitionMass reward
          (quittingLiteralRootStackProfile reward roots terminal)
          (depth + time) coalition ∧
      0 < quittingStageCoalitionMass reward
        (quittingLiteralRootStackProfile reward roots terminal)
        (depth + time) coalition := by
  obtain ⟨roots, hlength, hstack⟩ :=
    exists_quittingCapNashRootStack reward terminal depth
  have hterminalPos : 0 < quittingTerminalDebtSum reward terminal :=
    hinf.trans_le
      (quittingTerminalDebtSumInf_le (reward := reward) terminal hM hreward)
  have hproductLower :
      quittingTerminalDebtSumInf reward /
          quittingTerminalDebtSum reward terminal ≤
        quittingCapNashStackContinueProduct roots :=
    capNashStack_continueProduct_lowerBound
      (reward := reward) roots terminal hM hreward hinf hstack
  have hscaledLower :
      quittingTerminalDebtSumInf reward /
            quittingTerminalDebtSum reward terminal *
          quittingStageCoalitionMass reward terminal time coalition ≤
        quittingCapNashStackContinueProduct roots *
          quittingStageCoalitionMass reward terminal time coalition :=
    mul_le_mul_of_nonneg_right hproductLower hpositive.le
  have htransport :=
    quittingStageCoalitionMass_literalRootStack_add_length
      reward roots terminal time coalition
  have hshiftedPositive : 0 < quittingStageCoalitionMass reward
      (quittingLiteralRootStackProfile reward roots terminal)
      (depth + time) coalition := by
    rw [← hlength, htransport]
    exact mul_pos
      ((div_pos hinf hterminalPos).trans_le hproductLower) hpositive
  refine ⟨roots, hlength, hstack, ?_, hshiftedPositive⟩
  rw [← hlength, htransport]
  exact hscaledLower

/-- **Joint-carrier mass has a same-profile causal realization.**

If a finite terminal coalition has positive mass at a point of the joint
semantic/law carrier, there are literal profiles converging jointly to that
point and finite (possibly drifting) windows which retain more than half of
the limiting coalition mass.  In every sufficiently late profile, some
actual stage in that very window carries the coalition with positive mass.

This is the unconditional law-to-chronology part of the terminal-law
causalization problem.  It deliberately makes no exact-Nash or minimum-fiber
claim about the selected stage. -/
theorem exists_jointRealizers_finiteWindow_positiveStage_of_lawMass_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (terminal : {S : Finset ι // S.Nonempty})
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hmass : 0 < point.2 (some terminal)) :
    ∃ profiles : ℕ → (quittingGame reward).BehaviorProfile,
      ∃ cutoff : ℕ → ℕ,
        Tendsto (fun n ↦
          (quittingTerminalSemanticPair reward (profiles n),
            quittingTerminalOutcomeMass reward (profiles n)))
          atTop (nhds point) ∧
        0 < point.2 (some terminal) / 2 ∧
        ∀ᶠ n in atTop,
          point.2 (some terminal) / 2 <
              ∑ time ∈ Finset.range (cutoff n),
                quittingStageCoalitionMass reward (profiles n) time terminal ∧
            ∃ time < cutoff n,
              0 < quittingStageCoalitionMass reward
                (profiles n) time terminal := by
  rw [quittingTerminalSemanticLawCarrier, mem_closure_iff_seq_limit] at hpoint
  obtain ⟨points, hpoints, hpointsTendsto⟩ := hpoint
  choose profiles hprofiles using hpoints
  have hprofilesTendsto : Tendsto (fun n ↦
      (quittingTerminalSemanticPair reward (profiles n),
        quittingTerminalOutcomeMass reward (profiles n)))
      atTop (nhds point) := by
    simpa only [hprofiles] using hpointsTendsto
  have hmassTendsto : Tendsto (fun n ↦
      quittingTerminalOutcomeMass reward (profiles n) (some terminal))
      atTop (nhds (point.2 (some terminal))) :=
    ((continuous_apply (some terminal)).comp continuous_snd).tendsto point |>.comp
      hprofilesTendsto
  have hpersistent : ∀ᶠ n in atTop,
      point.2 (some terminal) / 2 <
        quittingTerminalOutcomeMass reward (profiles n) (some terminal) :=
    hmassTendsto.eventually (Ioi_mem_nhds (by linarith))
  let cutoff : ℕ → ℕ := fun n ↦
    if h : point.2 (some terminal) / 2 <
        quittingTerminalOutcomeMass reward (profiles n) (some terminal) then
      Classical.choose
        (exists_finiteWindow_sum_stageCoalitionMass_gt
          (reward := reward) (profiles n) terminal h)
    else 0
  have hwindow : ∀ᶠ n in atTop,
      point.2 (some terminal) / 2 <
        ∑ time ∈ Finset.range (cutoff n),
          quittingStageCoalitionMass reward (profiles n) time terminal := by
    filter_upwards [hpersistent] with n hn
    dsimp only [cutoff]
    rw [dif_pos hn]
    exact Classical.choose_spec
      (exists_finiteWindow_sum_stageCoalitionMass_gt
        (reward := reward) (profiles n) terminal hn)
  refine ⟨profiles, cutoff, hprofilesTendsto, by linarith, ?_⟩
  filter_upwards [hwindow] with n hn
  refine ⟨hn, ?_⟩
  have hsumPos : 0 < ∑ time ∈ Finset.range (cutoff n),
      quittingStageCoalitionMass reward (profiles n) time terminal := by
    linarith
  have hnonneg : ∀ time ∈ Finset.range (cutoff n),
      0 ≤ quittingStageCoalitionMass reward (profiles n) time terminal := by
    intro time _
    exact quittingStageCoalitionMass_nonneg reward (profiles n) time terminal
  obtain ⟨time, htime, htimePos⟩ :=
    (Finset.sum_pos_iff_of_nonneg hnonneg).mp hsumPos
  exact ⟨time, Finset.mem_range.mp htime, htimePos⟩

/-! ## Near-minimum exact-prefix packet -/

/-- **Positive joint law admits arbitrarily deep near-minimum cap
chronologies with a surviving literal atom.**

Suppose the semantic component of the joint carrier point has debt equal to
the global literal debt infimum, and that infimum is positive.  Then the
same-profile causal realizers above can be equipped with cap--Nash root words
of depth tending to infinity.  Their front total debt still converges to the
global infimum, while the selected suffix atom survives at its literally
shifted stage.

This reaches an exact state-matched prefix and an actual causal atom in one
finite executable profile.  The remaining fence is precise: the atom row is
in the declared terminal suffix, and is not asserted to be one of the exact
cap--Nash prefix rows. -/
theorem exists_deep_nearMinimum_capNashChronologies_with_causalSuffixAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (point : QuittingTerminalSemanticLawPoint ι)
    (terminal : {S : Finset ι // S.Nonempty})
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward)
    (hmass : 0 < point.2 (some terminal))
    (hinf : 0 < quittingTerminalDebtSumInf reward)
    (hminimum : quittingTerminalSemanticDebtSum point.1 =
      quittingTerminalDebtSumInf reward) :
    ∃ profiles : ℕ → (quittingGame reward).BehaviorProfile,
      ∃ cutoff mark : ℕ → ℕ,
      ∃ roots : ℕ → List (ι → PMF Bool),
        Tendsto (fun n ↦
          (quittingTerminalSemanticPair reward (profiles n),
            quittingTerminalOutcomeMass reward (profiles n)))
          atTop (nhds point) ∧
        (∀ n, (roots n).length = n + 1) ∧
        (∀ n, IsQuittingCapNashRootStack reward (roots n) (profiles n)) ∧
        Tendsto (fun n ↦ quittingTerminalDebtSum reward
          (quittingLiteralRootStackProfile reward (roots n) (profiles n)))
          atTop (nhds (quittingTerminalDebtSumInf reward)) ∧
        ∀ᶠ n in atTop,
          point.2 (some terminal) / 2 <
              ∑ time ∈ Finset.range (cutoff n),
                quittingStageCoalitionMass reward (profiles n) time terminal ∧
            mark n < cutoff n ∧
            0 < quittingStageCoalitionMass reward
              (profiles n) (mark n) terminal ∧
            0 < quittingStageCoalitionMass reward
              (quittingLiteralRootStackProfile reward (roots n) (profiles n))
              (n + 1 + mark n) terminal := by
  obtain ⟨profiles, cutoff, hprofiles, _hhalf, hcausal⟩ :=
    exists_jointRealizers_finiteWindow_positiveStage_of_lawMass_pos
      reward point terminal hpoint hmass
  let mark : ℕ → ℕ := fun n ↦
    if h : ∃ time < cutoff n,
        0 < quittingStageCoalitionMass reward (profiles n) time terminal then
      Classical.choose h
    else 0
  have hmark : ∀ᶠ n in atTop,
      point.2 (some terminal) / 2 <
          ∑ time ∈ Finset.range (cutoff n),
            quittingStageCoalitionMass reward (profiles n) time terminal ∧
        mark n < cutoff n ∧
        0 < quittingStageCoalitionMass reward
          (profiles n) (mark n) terminal := by
    filter_upwards [hcausal] with n hn
    have hexists := hn.2
    dsimp only [mark]
    rw [dif_pos hexists]
    exact ⟨hn.1, (Classical.choose_spec hexists).1,
      (Classical.choose_spec hexists).2⟩
  have hrootChoice : ∀ n : ℕ,
      ∃ word : List (ι → PMF Bool),
        word.length = n + 1 ∧
          IsQuittingCapNashRootStack reward word (profiles n) := by
    intro n
    exact exists_quittingCapNashRootStack reward (profiles n) (n + 1)
  choose roots hrootsLength hrootsNash using hrootChoice
  let tailDebt : ℕ → ℝ := fun n ↦
    quittingTerminalDebtSum reward (profiles n)
  let prefixDebt : ℕ → ℝ := fun n ↦
    quittingTerminalDebtSum reward
      (quittingLiteralRootStackProfile reward (roots n) (profiles n))
  have htailDebt : Tendsto tailDebt atTop
      (nhds (quittingTerminalDebtSumInf reward)) := by
    have hpair : Tendsto (fun n ↦
        quittingTerminalSemanticPair reward (profiles n))
        atTop (nhds point.1) :=
      continuous_fst.tendsto point |>.comp hprofiles
    have hsum := continuous_quittingTerminalSemanticDebtSum.tendsto point.1 |>.comp
      hpair
    rw [hminimum] at hsum
    simpa [Function.comp_def, tailDebt, quittingTerminalDebtSum,
      quittingTerminalSemanticDebtSum,
      quittingTerminalSemanticPair, quittingTerminalSemanticDebt,
      quittingTerminalDeviationDebt] using hsum
  have hlower : ∀ n, quittingTerminalDebtSumInf reward ≤ prefixDebt n := by
    intro n
    exact quittingTerminalDebtSumInf_le (reward := reward)
      (quittingLiteralRootStackProfile reward (roots n) (profiles n))
      hM hreward
  have hupper : ∀ n, prefixDebt n ≤ tailDebt n := by
    intro n
    have htailNonneg : 0 ≤ tailDebt n := by
      dsimp only [tailDebt, quittingTerminalDebtSum]
      exact Finset.sum_nonneg fun who _ ↦
        quittingTerminalDeviationDebt_nonneg reward (profiles n) who hM hreward
    rw [show prefixDebt n =
        quittingCapNashStackContinueProduct (roots n) * tailDebt n by
      simpa only [prefixDebt, tailDebt] using
        (quittingTerminalDebtSum_capNashRootStack_eq
          (reward := reward) (roots n) (profiles n) hM hreward
            (hrootsNash n))]
    exact mul_le_of_le_one_left htailNonneg
      (quittingCapNashStackContinueProduct_le_one (roots n))
  have hprefixDebt : Tendsto prefixDebt atTop
      (nhds (quittingTerminalDebtSumInf reward)) := by
    have htailGap : Tendsto (fun n ↦
        tailDebt n - quittingTerminalDebtSumInf reward) atTop (nhds 0) := by
      simpa using htailDebt.sub_const (quittingTerminalDebtSumInf reward)
    have hprefixGap : Tendsto (fun n ↦
        prefixDebt n - quittingTerminalDebtSumInf reward) atTop (nhds 0) := by
      apply squeeze_zero'
      · exact Eventually.of_forall fun n ↦ sub_nonneg.mpr (hlower n)
      · exact Eventually.of_forall fun n ↦
          sub_le_sub_right (hupper n) _
      · exact htailGap
    have hadd := hprefixGap.add_const (quittingTerminalDebtSumInf reward)
    simpa only [sub_add_cancel, zero_add] using hadd
  have hshifted : ∀ᶠ n in atTop,
      0 < quittingStageCoalitionMass reward
        (quittingLiteralRootStackProfile reward (roots n) (profiles n))
        (n + 1 + mark n) terminal := by
    filter_upwards [hmark] with n hn
    have htailPos := hn.2.2
    have hterminalDebtPos : 0 < quittingTerminalDebtSum reward (profiles n) :=
      hinf.trans_le
        (quittingTerminalDebtSumInf_le (reward := reward) (profiles n) hM hreward)
    have hproductLower := capNashStack_continueProduct_lowerBound
      (reward := reward) (roots n) (profiles n) hM hreward hinf (hrootsNash n)
    have hproductPos : 0 < quittingCapNashStackContinueProduct (roots n) :=
      (div_pos hinf hterminalDebtPos).trans_le hproductLower
    rw [← hrootsLength n,
      quittingStageCoalitionMass_literalRootStack_add_length]
    exact mul_pos hproductPos htailPos
  refine ⟨profiles, cutoff, mark, roots, hprofiles, hrootsLength,
    hrootsNash, hprefixDebt, ?_⟩
  filter_upwards [hmark, hshifted] with n hn hshift
  exact ⟨hn.1, hn.2.1, hn.2.2, hshift⟩

end GameTheory
