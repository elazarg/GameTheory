/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawMinimumTangent

/-!
# Simultaneous stopping-law resets at a minimum-debt source

Mixing every player's complete stopping law at once always gives one literal
behavior profile.  Near-minimality of total semantic debt already gives the
relevant first-order alternative for that profile: either its total debt has
a prescribed positive slope, or its total-debt displacement is quantitatively
near-flat.  No common maximizing deviation and no envelope modularity
hypothesis is needed.

The same chosen replacement family still carries an exact unilateral
passport.  On every one-player reset edge, the mover's payoff and debt are
affine and every marked chronological atom retains its `1 - lambda` share.
These are counterfactual edge statements.  They do not say that the mover's
debt decreases, or that the marked atom has the same orientation, at the
joint simultaneous vertex: the other players' resets can contribute at first
order to that coordinate.

This file is purely terminal-semantic.  It contains no Bellman continuation
matching or chronological return compiler.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Mix every player's prescribed complete stopping law toward the displayed
replacement law, using one common mixing scale. -/
def quittingSimultaneousStoppingLawMixtureProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (replacement : ∀ who, (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  fun who => quittingStoppingLawMixtureBehaviorStrategy reward who
    (profile who) (replacement who) lambda hlambda0 hlambda1

/-- The one-player edge belonging to the same replacement family and scale
as the simultaneous profile. -/
def quittingUnilateralStoppingLawMixtureProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (replacement : ∀ who, (quittingGame reward).BehaviorStrategy who)
    (who : ι) (lambda : ℝ) (hlambda0 : 0 ≤ lambda)
    (hlambda1 : lambda ≤ 1) : (quittingGame reward).BehaviorProfile :=
  Function.update profile who
    (quittingStoppingLawMixtureBehaviorStrategy reward who
      (profile who) (replacement who) lambda hlambda0 hlambda1)

/-- The quantitative information retained on one counterfactual edge of a
simultaneous replacement family.  It includes a half-debt endpoint gain,
exact mover-debt consumption, minimum-forced transfer to opponents, and
cutoff-independent marked-window retention. -/
def IsQuittingStoppingLawMinimumResetPassport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (replacement : (quittingGame reward).BehaviorStrategy who)
    (terminal : {S : Finset ι // S.Nonempty}) (cutoff : ℕ) : Prop :=
  let source := quittingTerminalSemanticPair reward profile
  let endpointProfile := Function.update profile who replacement
  let endpointGain := quittingTerminalPayoff reward endpointProfile who -
    quittingTerminalPayoff reward profile who
  quittingTerminalSemanticDebt source who / 2 ≤ endpointGain ∧
    0 < endpointGain ∧
    ∀ (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1),
      let unilateralProfile := Function.update profile who
        (quittingStoppingLawMixtureBehaviorStrategy reward who (profile who)
          replacement lambda hlambda0 hlambda1)
      let target := quittingTerminalSemanticPair reward unilateralProfile
      quittingTerminalSemanticDebt target who =
          quittingTerminalSemanticDebt source who - lambda * endpointGain ∧
        lambda * endpointGain ≤
          ∑ other ∈ Finset.univ.erase who,
            quittingTerminalSemanticDebtChange source target other ∧
        (1 - lambda) *
            (∑ time ∈ Finset.range cutoff,
              quittingStageCoalitionMass reward profile time terminal) ≤
          ∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward unilateralProfile time terminal

/-- **Minimum-floor simultaneous-reset dichotomy with unilateral passport.**

Suppose the source total debt is within `epsilon` of the global carrier
floor.  For any simultaneous family of complete stopping-law resets and any
nonnegative test slope `eta`, either the joint target has total-debt increase
strictly larger than `lambda * eta`, or its total-debt displacement has
absolute value at most `epsilon + lambda * eta`.

The conclusion also records the exact payoff/debt affine identities and
marked-atom retention on every associated one-player edge.  Those individual
orientations are deliberately not asserted at the simultaneous target. -/
theorem quittingSimultaneousStoppingLawMixture_minimumFloor_slopeOrFlat_withUnilateralPassport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (replacement : ∀ who, (quittingGame reward).BehaviorStrategy who)
    (lambda epsilon eta : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hepsilon : 0 ≤ epsilon) (heta : 0 ≤ eta)
    (time : ℕ) (terminal : {S : Finset ι // S.Nonempty})
    (hminimumFloor : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate + epsilon) :
    let simultaneousProfile :=
      quittingSimultaneousStoppingLawMixtureProfile reward profile replacement
        lambda hlambda0 hlambda1
    let source := quittingTerminalSemanticPair reward profile
    let simultaneousTarget :=
      quittingTerminalSemanticPair reward simultaneousProfile
    (lambda * eta <
          quittingTerminalSemanticDebtSum simultaneousTarget -
            quittingTerminalSemanticDebtSum source ∨
        |quittingTerminalSemanticDebtSum simultaneousTarget -
            quittingTerminalSemanticDebtSum source| ≤
          epsilon + lambda * eta) ∧
      ∀ who,
        let endpointProfile := Function.update profile who (replacement who)
        let unilateralProfile :=
          quittingUnilateralStoppingLawMixtureProfile reward profile replacement
            who lambda hlambda0 hlambda1
        quittingTerminalPayoff reward unilateralProfile who =
            (1 - lambda) * quittingTerminalPayoff reward profile who +
              lambda * quittingTerminalPayoff reward endpointProfile who ∧
          quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward unilateralProfile) who =
            (1 - lambda) * quittingTerminalSemanticDebt source who +
              lambda * quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward endpointProfile) who ∧
          (1 - lambda) *
              quittingStageCoalitionMass reward profile time terminal ≤
            quittingStageCoalitionMass reward unilateralProfile time terminal := by
  dsimp only
  let simultaneousProfile :=
    quittingSimultaneousStoppingLawMixtureProfile reward profile replacement
      lambda hlambda0 hlambda1
  let source := quittingTerminalSemanticPair reward profile
  let simultaneousTarget :=
    quittingTerminalSemanticPair reward simultaneousProfile
  have htargetCarrier : simultaneousTarget ∈
      quittingTerminalSemanticCarrier reward := by
    exact quittingTerminalSemanticPair_mem_carrier reward simultaneousProfile
  have hfloor := hminimumFloor simultaneousTarget htargetCarrier
  have hdeltaLower : -epsilon ≤
      quittingTerminalSemanticDebtSum simultaneousTarget -
        quittingTerminalSemanticDebtSum source := by
    dsimp only [source] at hfloor ⊢
    linarith
  have hlambdaEta : 0 ≤ lambda * eta := mul_nonneg hlambda0 heta
  constructor
  · by_cases hpositive : lambda * eta <
        quittingTerminalSemanticDebtSum simultaneousTarget -
          quittingTerminalSemanticDebtSum source
    · exact Or.inl hpositive
    · right
      apply (abs_le).2
      constructor
      · linarith
      · have hupper :
            quittingTerminalSemanticDebtSum simultaneousTarget -
                quittingTerminalSemanticDebtSum source ≤ lambda * eta :=
          le_of_not_gt hpositive
        linarith
  · intro who
    let endpointProfile := Function.update profile who (replacement who)
    let unilateralProfile :=
      quittingUnilateralStoppingLawMixtureProfile reward profile replacement
        who lambda hlambda0 hlambda1
    have hpayoff := quittingTerminalPayoff_stoppingLawMixture_eq
      reward profile who who (profile who) (replacement who)
        lambda hlambda0 hlambda1
    have hdebt := quittingTerminalSemanticDebt_stoppingLawMixture_eq_self
      reward profile who (profile who) (replacement who)
        lambda hlambda0 hlambda1
    have hmass := one_sub_mul_stageCoalitionMass_le_stoppingLawMixture
      reward profile who (profile who) (replacement who)
        lambda hlambda0 hlambda1 time terminal
    dsimp only [unilateralProfile,
      quittingUnilateralStoppingLawMixtureProfile] at hpayoff hdebt hmass ⊢
    simpa only [Function.update_eq_self, endpointProfile, source] using
      And.intro hpayoff (And.intro hdebt hmass)

/-- At an exact total-debt minimizer, a simultaneous complete stopping-law
reset is either a strict total-debt ascent or an actual point of the same
minimum-debt fiber.  The statement concerns one executable simultaneous
profile and uses no first-order envelope passport. -/
theorem quittingSimultaneousStoppingLawMixture_minimum_strictOrSameFiber
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (replacement : ∀ who, (quittingGame reward).BehaviorStrategy who)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate) :
    let simultaneousProfile :=
      quittingSimultaneousStoppingLawMixtureProfile reward profile replacement
        lambda hlambda0 hlambda1
    let source := quittingTerminalSemanticPair reward profile
    let simultaneousTarget :=
      quittingTerminalSemanticPair reward simultaneousProfile
    quittingTerminalSemanticDebtSum source <
        quittingTerminalSemanticDebtSum simultaneousTarget ∨
      quittingTerminalSemanticDebtSum simultaneousTarget =
        quittingTerminalSemanticDebtSum source := by
  dsimp only
  let simultaneousProfile :=
    quittingSimultaneousStoppingLawMixtureProfile reward profile replacement
      lambda hlambda0 hlambda1
  let source := quittingTerminalSemanticPair reward profile
  let simultaneousTarget :=
    quittingTerminalSemanticPair reward simultaneousProfile
  have hle : quittingTerminalSemanticDebtSum source ≤
      quittingTerminalSemanticDebtSum simultaneousTarget := by
    apply hminimum
    exact quittingTerminalSemanticPair_mem_carrier reward simultaneousProfile
  exact hle.lt_or_eq_dec.imp_right Eq.symm

/-- **One simultaneous family with all active unilateral passports.**

At an exact minimum of total semantic debt, choose one approximate complete
stopping-law best response for every positive debtor.  The choices are made
once, before the common mixing scale is selected.  Every active player then
has the quantitative unilateral passport above at every scale, while the
literal profile which applies all chosen mixtures simultaneously is, at each
scale, either a total-debt ascent larger than a displayed first-order test
`lambda * eta`, or a joint displacement bounded by that test.

The passports belong to the edges based at `profile`; no coordinatewise debt
orientation is claimed at the simultaneous vertex. -/
theorem exists_simultaneousStoppingLawMinimumResetFamily_withActivePassports
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) (cutoff : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ replacement : ∀ who,
        (quittingGame reward).BehaviorStrategy who,
      (∀ who,
        0 < quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward profile) who →
          IsQuittingStoppingLawMinimumResetPassport reward profile who
            (replacement who) terminal cutoff) ∧
      ∀ (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
          (eta : ℝ) (_heta : 0 ≤ eta),
        let simultaneousProfile :=
          quittingSimultaneousStoppingLawMixtureProfile reward profile
            replacement lambda hlambda0 hlambda1
        let source := quittingTerminalSemanticPair reward profile
        let simultaneousTarget :=
          quittingTerminalSemanticPair reward simultaneousProfile
        lambda * eta <
            quittingTerminalSemanticDebtSum simultaneousTarget -
              quittingTerminalSemanticDebtSum source ∨
          |quittingTerminalSemanticDebtSum simultaneousTarget -
              quittingTerminalSemanticDebtSum source| ≤ lambda * eta := by
  classical
  have hchoice : ∀ who, ∃ strategy :
      (quittingGame reward).BehaviorStrategy who,
      0 < quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who →
        IsQuittingStoppingLawMinimumResetPassport reward profile who strategy
          terminal cutoff := by
    intro who
    by_cases hactive : 0 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who
    · obtain ⟨bestResponse, hgainLower, hgainPos, hray⟩ :=
        exists_stoppingLawResetRay_minimum_transfer_and_windowRetention
          reward profile who terminal cutoff hM hreward hactive hminimum
      refine ⟨bestResponse, fun _hactive => ?_⟩
      dsimp only [IsQuittingStoppingLawMinimumResetPassport]
      refine ⟨hgainLower, hgainPos, ?_⟩
      intro lambda hlambda0 hlambda1
      obtain ⟨_htarget, _hgain, hdecrease, htransfer, _hchord, hwindow⟩ :=
        hray lambda hlambda0 hlambda1
      exact ⟨hdecrease, htransfer, hwindow⟩
    · exact ⟨profile who, fun hpositive => False.elim (hactive hpositive)⟩
  choose replacement hreplacement using hchoice
  refine ⟨replacement, hreplacement, ?_⟩
  intro lambda hlambda0 hlambda1 eta _heta
  let simultaneousProfile :=
    quittingSimultaneousStoppingLawMixtureProfile reward profile replacement
      lambda hlambda0 hlambda1
  let source := quittingTerminalSemanticPair reward profile
  let simultaneousTarget :=
    quittingTerminalSemanticPair reward simultaneousProfile
  have hdeltaNonneg : 0 ≤
      quittingTerminalSemanticDebtSum simultaneousTarget -
        quittingTerminalSemanticDebtSum source := by
    have hle := hminimum simultaneousTarget
      (quittingTerminalSemanticPair_mem_carrier reward simultaneousProfile)
    dsimp only [source] at hle ⊢
    linarith
  by_cases hlarge : lambda * eta <
      quittingTerminalSemanticDebtSum simultaneousTarget -
        quittingTerminalSemanticDebtSum source
  · exact Or.inl hlarge
  · right
    rw [abs_of_nonneg hdeltaNonneg]
    exact le_of_not_gt hlarge

end GameTheory
