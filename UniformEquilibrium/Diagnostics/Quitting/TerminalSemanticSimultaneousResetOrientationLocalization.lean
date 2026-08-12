/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSimultaneousResetMinimumDichotomy
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeAtom

/-!
# Recovering orientation from a flat simultaneous stopping-law reset

An active player's unilateral reset has an exact negative debt coordinate.
Other players' simultaneous resets can erase that sign at the joint target,
so the unilateral passport cannot simply be copied to the simultaneous
profile.  The loss is nevertheless localizable.

Hold the active player's mixed stopping law fixed and insert the other mixed
laws one at a time.  If half of the active player's unilateral debt drop
survives at a flat joint target, flatness supplies an actual positive debt
recipient at that target.  Otherwise the missing half telescopes across the
finite hybrid path.  One literal one-player stopping-law edge then raises the
active player's debt at normalized rate

`gain / (2 * card (univ.erase active))`.

That edge is immediately consumed by the coordinate positive-slope decoder,
which returns a prescribed-law terminal atom or a same-deviation rectangle
atom.  Thus simultaneous witness switching may destroy the joint coordinate
orientation, but it cannot do so invisibly.  No common maximizing deviation,
envelope modularity, or abstract tangent integration is assumed.
-/

open scoped BigOperators

namespace GameTheory

private theorem finite_hybrid_sub_lt_card_mul
    {ι : Type*} [DecidableEq ι]
    (value : Finset ι → ℝ) (bound : ℝ) :
    ∀ S : Finset ι, S.Nonempty →
      (∀ moved, moved ⊆ S → ∀ mover ∈ S, mover ∉ moved →
        value (insert mover moved) - value moved < bound) →
      value S - value ∅ < (S.card : ℝ) * bound := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro hnonempty
      simp at hnonempty
  | @insert mover S hmover ih =>
      intro _hnonempty hedge
      have hlast : value (insert mover S) - value S < bound :=
        hedge S (Finset.subset_insert mover S) mover
          (Finset.mem_insert_self mover S) hmover
      by_cases hS : S.Nonempty
      · have hprefix : value S - value ∅ < (S.card : ℝ) * bound := by
          apply ih hS
          intro moved hmoved candidate hcandidate hcandidateMoved
          exact hedge moved (hmoved.trans (Finset.subset_insert mover S))
            candidate (Finset.mem_insert_of_mem hcandidate) hcandidateMoved
        calc
          value (insert mover S) - value ∅ =
              (value (insert mover S) - value S) +
                (value S - value ∅) := by ring
          _ < bound + (S.card : ℝ) * bound :=
            add_lt_add hlast hprefix
          _ = ((insert mover S).card : ℝ) * bound := by
            rw [Finset.card_insert_of_notMem hmover]
            push_cast
            ring
      · rw [Finset.not_nonempty_iff_eq_empty.mp hS] at hlast ⊢
        simpa using hlast

private theorem exists_subset_insert_increment_ge_average
    {ι : Type*} [DecidableEq ι]
    (value : Finset ι → ℝ) (S : Finset ι) (charge : ℝ)
    (hS : S.Nonempty) (hcharge : charge ≤ value S - value ∅) :
    ∃ moved ⊆ S, ∃ mover ∈ S, mover ∉ moved ∧
      charge / (S.card : ℝ) ≤
        value (insert mover moved) - value moved := by
  by_contra hnot
  have hedge : ∀ moved, moved ⊆ S → ∀ mover ∈ S, mover ∉ moved →
      value (insert mover moved) - value moved <
        charge / (S.card : ℝ) := by
    intro moved hmoved mover hmover hmoverMoved
    exact lt_of_not_ge (fun hge => hnot
      ⟨moved, hmoved, mover, hmover, hmoverMoved, hge⟩)
  have hstrict := finite_hybrid_sub_lt_card_mul value
    (charge / (S.card : ℝ)) S hS hedge
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr hS))
  have hcancel : (S.card : ℝ) * (charge / (S.card : ℝ)) = charge := by
    field_simp
  rw [hcancel] at hstrict
  linarith

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingStoppingLawMixtureSubsetProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (replacement : ∀ who, (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (moved : Finset ι) : (quittingGame reward).BehaviorProfile :=
  fun who => if who ∈ moved then
    quittingStoppingLawMixtureBehaviorStrategy reward who
      (profile who) (replacement who) lambda hlambda0 hlambda1
  else profile who

theorem quittingStoppingLawMixtureSubsetProfile_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (replacement : ∀ who, (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingStoppingLawMixtureSubsetProfile reward profile replacement
      lambda hlambda0 hlambda1 ∅ = profile := by
  funext who
  simp [quittingStoppingLawMixtureSubsetProfile]

theorem quittingStoppingLawMixtureSubsetProfile_univ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (replacement : ∀ who, (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    quittingStoppingLawMixtureSubsetProfile reward profile replacement
      lambda hlambda0 hlambda1 Finset.univ =
      quittingSimultaneousStoppingLawMixtureProfile reward profile replacement
        lambda hlambda0 hlambda1 := by
  funext who
  simp [quittingStoppingLawMixtureSubsetProfile,
    quittingSimultaneousStoppingLawMixtureProfile]

theorem quittingStoppingLawMixtureSubsetProfile_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (replacement : ∀ who, (quittingGame reward).BehaviorStrategy who)
    (owner : ι) (lambda : ℝ) (hlambda0 : 0 ≤ lambda)
    (hlambda1 : lambda ≤ 1) :
    quittingStoppingLawMixtureSubsetProfile reward profile replacement
      lambda hlambda0 hlambda1 {owner} =
      quittingUnilateralStoppingLawMixtureProfile reward profile replacement
        owner lambda hlambda0 hlambda1 := by
  funext who
  by_cases hwho : who = owner
  · subst who
    simp [quittingStoppingLawMixtureSubsetProfile,
      quittingUnilateralStoppingLawMixtureProfile]
  · simp [quittingStoppingLawMixtureSubsetProfile,
      quittingUnilateralStoppingLawMixtureProfile, hwho]

theorem quittingStoppingLawMixtureSubsetProfile_insert
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (replacement : ∀ who, (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (moved : Finset ι) (mover : ι) (hmover : mover ∉ moved) :
    quittingStoppingLawMixtureSubsetProfile reward profile replacement
        lambda hlambda0 hlambda1 (insert mover moved) =
      Function.update
        (quittingStoppingLawMixtureSubsetProfile reward profile replacement
          lambda hlambda0 hlambda1 moved)
        mover
        (quittingStoppingLawMixtureBehaviorStrategy reward mover
          ((quittingStoppingLawMixtureSubsetProfile reward profile replacement
            lambda hlambda0 hlambda1 moved) mover)
          (replacement mover) lambda hlambda0 hlambda1) := by
  have hsource : quittingStoppingLawMixtureSubsetProfile reward profile replacement
      lambda hlambda0 hlambda1 moved mover = profile mover := by
    simp [quittingStoppingLawMixtureSubsetProfile, hmover]
  rw [hsource]
  funext who
  by_cases hwho : who = mover
  · subst who
    simp [quittingStoppingLawMixtureSubsetProfile]
  · simp [quittingStoppingLawMixtureSubsetProfile, hwho]

def quittingStoppingLawMixtureHybridProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (replacement : ∀ who, (quittingGame reward).BehaviorStrategy who)
    (owner : ι) (lambda : ℝ) (hlambda0 : 0 ≤ lambda)
    (hlambda1 : lambda ≤ 1) (movedOpponents : Finset ι) :
    (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawMixtureSubsetProfile reward profile replacement
    lambda hlambda0 hlambda1 (insert owner movedOpponents)

theorem quittingStoppingLawMixtureHybridProfile_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (replacement : ∀ who, (quittingGame reward).BehaviorStrategy who)
    (owner : ι) (lambda : ℝ) (hlambda0 : 0 ≤ lambda)
    (hlambda1 : lambda ≤ 1) :
    quittingStoppingLawMixtureHybridProfile reward profile replacement owner
      lambda hlambda0 hlambda1 ∅ =
      quittingUnilateralStoppingLawMixtureProfile reward profile replacement
        owner lambda hlambda0 hlambda1 := by
  simpa [quittingStoppingLawMixtureHybridProfile] using
    quittingStoppingLawMixtureSubsetProfile_singleton reward profile replacement
      owner lambda hlambda0 hlambda1

theorem quittingStoppingLawMixtureHybridProfile_allOpponents
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (replacement : ∀ who, (quittingGame reward).BehaviorStrategy who)
    (owner : ι) (lambda : ℝ) (hlambda0 : 0 ≤ lambda)
    (hlambda1 : lambda ≤ 1) :
    quittingStoppingLawMixtureHybridProfile reward profile replacement owner
        lambda hlambda0 hlambda1 (Finset.univ.erase owner) =
      quittingSimultaneousStoppingLawMixtureProfile reward profile replacement
        lambda hlambda0 hlambda1 := by
  unfold quittingStoppingLawMixtureHybridProfile
  rw [Finset.insert_erase (Finset.mem_univ owner)]
  exact quittingStoppingLawMixtureSubsetProfile_univ reward profile replacement
    lambda hlambda0 hlambda1

theorem quittingStoppingLawMixtureHybridProfile_insert
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (replacement : ∀ who, (quittingGame reward).BehaviorStrategy who)
    (owner mover : ι) (hne : mover ≠ owner)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (movedOpponents : Finset ι) (hmover : mover ∉ movedOpponents) :
    quittingStoppingLawMixtureHybridProfile reward profile replacement owner
        lambda hlambda0 hlambda1 (insert mover movedOpponents) =
      Function.update
        (quittingStoppingLawMixtureHybridProfile reward profile replacement owner
          lambda hlambda0 hlambda1 movedOpponents)
        mover
        (quittingStoppingLawMixtureBehaviorStrategy reward mover
          ((quittingStoppingLawMixtureHybridProfile reward profile replacement owner
            lambda hlambda0 hlambda1 movedOpponents) mover)
          (replacement mover) lambda hlambda0 hlambda1) := by
  unfold quittingStoppingLawMixtureHybridProfile
  rw [Finset.insert_comm owner mover]
  apply quittingStoppingLawMixtureSubsetProfile_insert
  simp [hmover, hne]

def HasQuittingStoppingLawPositiveSlopeAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (target : (quittingGame reward).BehaviorStrategy mover)
    (charge : ℝ) : Prop :=
  (∃ terminal : {S : Finset ι // S.Nonempty},
      charge / 2 ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
          quittingTerminalPayoffDifferenceAtom reward profile
            (Function.update profile mover target) observer (some terminal)) ∨
    ∃ deviation : (quittingGame reward).BehaviorStrategy observer,
      ∃ terminal : {S : Finset ι // S.Nonempty},
        charge / 4 ≤
          (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
            quittingTerminalPayoffDifferenceAtom reward
              (Function.update (Function.update profile mover target)
                observer deviation)
              (Function.update profile observer deviation) observer
                (some terminal)

theorem sum_erase_terminalSemanticDebtChange_eq
    (source target : QuittingTerminalSemanticPair ι) (who : ι) :
    (∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source target other) =
      (quittingTerminalSemanticDebtSum target -
          quittingTerminalSemanticDebtSum source) -
        quittingTerminalSemanticDebtChange source target who := by
  unfold quittingTerminalSemanticDebtChange
    quittingTerminalSemanticDebtSum
  have htarget := Finset.sum_erase_add (Finset.univ)
    (fun other => quittingTerminalSemanticDebt target other)
    (Finset.mem_univ who)
  have hsource := Finset.sum_erase_add (Finset.univ)
    (fun other => quittingTerminalSemanticDebt source other)
    (Finset.mem_univ who)
  calc
    (∑ other ∈ Finset.univ.erase who,
        (quittingTerminalSemanticDebt target other -
          quittingTerminalSemanticDebt source other)) =
        (∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebt target other) -
        (∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebt source other) := by
      rw [Finset.sum_sub_distrib]
    _ = ((∑ other, quittingTerminalSemanticDebt target other) -
          (∑ other, quittingTerminalSemanticDebt source other)) -
        (quittingTerminalSemanticDebt target who -
          quittingTerminalSemanticDebt source who) := by
      linarith

theorem activePassport_flatSimultaneous_directed_or_localizedPositiveSlope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (replacement : ∀ who, (quittingGame reward).BehaviorStrategy who)
    (who : ι) (terminal : {S : Finset ι // S.Nonempty}) (cutoff : ℕ)
    (lambda : ℝ) (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hpassport : IsQuittingStoppingLawMinimumResetPassport reward profile who
      (replacement who) terminal cutoff)
    (hflat : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingSimultaneousStoppingLawMixtureProfile reward profile
            replacement lambda hlambda0.le hlambda1)) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile)) :
    let source := quittingTerminalSemanticPair reward profile
    let simultaneousProfile :=
      quittingSimultaneousStoppingLawMixtureProfile reward profile replacement
        lambda hlambda0.le hlambda1
    let simultaneousTarget :=
      quittingTerminalSemanticPair reward simultaneousProfile
    let endpointProfile := Function.update profile who (replacement who)
    let gain := quittingTerminalPayoff reward endpointProfile who -
      quittingTerminalPayoff reward profile who
    let opponents := Finset.univ.erase who
    let charge := gain / (2 * (opponents.card : ℝ))
    ((quittingTerminalSemanticDebt simultaneousTarget who ≤
          quittingTerminalSemanticDebt source who - lambda * gain / 2) ∧
        ∃ recipient ∈ opponents,
          lambda * charge ≤
            quittingTerminalSemanticDebtChange source simultaneousTarget
              recipient) ∨
      ∃ moved ⊆ opponents, ∃ mover ∈ opponents, mover ∉ moved ∧
        let edgeSource := quittingStoppingLawMixtureHybridProfile reward profile
          replacement who lambda hlambda0.le hlambda1 moved
        let edgeTarget := quittingStoppingLawMixtureHybridProfile reward profile
          replacement who lambda hlambda0.le hlambda1 (insert mover moved)
        lambda * charge ≤
            quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward edgeTarget) who -
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward edgeSource) who ∧
          HasQuittingStoppingLawPositiveSlopeAtom reward edgeSource mover who
            (replacement mover) charge := by
  dsimp only
  let source := quittingTerminalSemanticPair reward profile
  let simultaneousProfile :=
    quittingSimultaneousStoppingLawMixtureProfile reward profile replacement
      lambda hlambda0.le hlambda1
  let simultaneousTarget :=
    quittingTerminalSemanticPair reward simultaneousProfile
  let endpointProfile := Function.update profile who (replacement who)
  let gain := quittingTerminalPayoff reward endpointProfile who -
    quittingTerminalPayoff reward profile who
  let opponents := Finset.univ.erase who
  let charge := gain / (2 * (opponents.card : ℝ))
  dsimp only [IsQuittingStoppingLawMinimumResetPassport] at hpassport
  obtain ⟨_hgainLower, hgainPos, hray⟩ := hpassport
  obtain ⟨hdecrease, htransfer, _hretention⟩ :=
    hray lambda hlambda0.le hlambda1
  have hlambdaGainPos : 0 < lambda * gain := mul_pos hlambda0 hgainPos
  have hopponents : opponents.Nonempty := by
    by_contra hempty
    have hempty' : opponents = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    change lambda * gain ≤ ∑ other ∈ opponents,
      quittingTerminalSemanticDebtChange source
        (quittingTerminalSemanticPair reward
          (quittingUnilateralStoppingLawMixtureProfile reward profile
            replacement who lambda hlambda0.le hlambda1)) other at htransfer
    rw [hempty'] at htransfer
    simp at htransfer
    linarith
  have hcardPos : 0 < (opponents.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hopponents
  have hchargePos : 0 < charge := by
    dsimp only [charge]
    positivity
  have hscale : lambda * charge =
      (lambda * gain / 2) / (opponents.card : ℝ) := by
    dsimp only [charge]
    field_simp
  by_cases hjoint : quittingTerminalSemanticDebt simultaneousTarget who ≤
      quittingTerminalSemanticDebt source who - lambda * gain / 2
  · left
    refine ⟨hjoint, ?_⟩
    have hsum : lambda * gain / 2 ≤
        ∑ recipient ∈ opponents,
          quittingTerminalSemanticDebtChange source simultaneousTarget
            recipient := by
      rw [sum_erase_terminalSemanticDebtChange_eq source simultaneousTarget who]
      have hflat' : quittingTerminalSemanticDebtSum simultaneousTarget =
          quittingTerminalSemanticDebtSum source := by
        exact hflat
      rw [hflat', sub_self, zero_sub]
      unfold quittingTerminalSemanticDebtChange
      linarith
    obtain ⟨recipient, hrecipient, hrecipientMax⟩ :=
      Finset.exists_max_image opponents
        (quittingTerminalSemanticDebtChange source simultaneousTarget)
        hopponents
    refine ⟨recipient, hrecipient, ?_⟩
    have hsumLe :
        (∑ other ∈ opponents,
            quittingTerminalSemanticDebtChange source simultaneousTarget other) ≤
          (opponents.card : ℝ) *
            quittingTerminalSemanticDebtChange source simultaneousTarget
              recipient := by
      simpa [nsmul_eq_mul, mul_comm] using
        opponents.sum_le_card_nsmul
          (quittingTerminalSemanticDebtChange source simultaneousTarget)
          (quittingTerminalSemanticDebtChange source simultaneousTarget recipient)
          (fun other hother => hrecipientMax other hother)
    have havg : (lambda * gain / 2) / (opponents.card : ℝ) ≤
        quittingTerminalSemanticDebtChange source simultaneousTarget
          recipient := by
      apply (div_le_iff₀ hcardPos).2
      nlinarith
    rw [hscale]
    exact havg
  · right
    have hinteraction : lambda * gain / 2 ≤
        quittingTerminalSemanticDebt simultaneousTarget who -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingUnilateralStoppingLawMixtureProfile reward profile
                replacement who lambda hlambda0.le hlambda1)) who := by
      have hjoint' : quittingTerminalSemanticDebt source who -
          lambda * gain / 2 <
            quittingTerminalSemanticDebt simultaneousTarget who :=
        lt_of_not_ge hjoint
      have hdecrease' :
          quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (quittingUnilateralStoppingLawMixtureProfile reward profile
                  replacement who lambda hlambda0.le hlambda1)) who =
            quittingTerminalSemanticDebt source who - lambda * gain := by
        simpa only [quittingUnilateralStoppingLawMixtureProfile, source, gain,
          endpointProfile] using hdecrease
      rw [hdecrease']
      linarith
    let value : Finset ι → ℝ := fun moved =>
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingStoppingLawMixtureHybridProfile reward profile replacement
            who lambda hlambda0.le hlambda1 moved)) who
    have hinteraction' : lambda * gain / 2 ≤
        value opponents - value ∅ := by
      dsimp only [value]
      rw [quittingStoppingLawMixtureHybridProfile_allOpponents,
        quittingStoppingLawMixtureHybridProfile_empty]
      exact hinteraction
    obtain ⟨moved, hmoved, mover, hmover, hmoverMoved, hedge⟩ :=
      exists_subset_insert_increment_ge_average value opponents
        (lambda * gain / 2) hopponents hinteraction'
    refine ⟨moved, hmoved, mover, hmover, hmoverMoved, ?_⟩
    let edgeSource := quittingStoppingLawMixtureHybridProfile reward profile
      replacement who lambda hlambda0.le hlambda1 moved
    let edgeTarget := quittingStoppingLawMixtureHybridProfile reward profile
      replacement who lambda hlambda0.le hlambda1 (insert mover moved)
    have hmoverNe : mover ≠ who := by
      exact Finset.ne_of_mem_erase hmover
    have hedgeProfile : edgeTarget =
        Function.update edgeSource mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover
            (edgeSource mover) (replacement mover) lambda hlambda0.le
              hlambda1) := by
      exact quittingStoppingLawMixtureHybridProfile_insert reward profile
        replacement who mover hmoverNe lambda hlambda0.le hlambda1 moved
          hmoverMoved
    have hslope : lambda * charge ≤
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward edgeTarget) who -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward edgeSource) who := by
      change lambda * charge ≤ value (insert mover moved) - value moved
      have hedge' : (lambda * gain / 2) / (opponents.card : ℝ) ≤
          value (insert mover moved) - value moved := hedge
      rw [hscale]
      exact hedge'
    refine ⟨hslope, ?_⟩
    unfold HasQuittingStoppingLawPositiveSlopeAtom
    apply exists_prescribedAtom_or_deviationRectangleAtom_of_stoppingLawDebtSlope
      reward edgeSource mover who (replacement mover) lambda charge hlambda0
        hlambda1 hchargePos hM hreward
    rw [← hedgeProfile]
    exact hslope

end

end GameTheory
