/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationFiniteClosing

/-!
# Complementary singleton mixtures compile through a one-face circulation

This module supplies the strategic consumer for the complementary branch of
the three-player theorem. The construction itself is valid for every
nonempty finite player type.

Let `nu` be a probability distribution over singleton quitting events and let
`mix` be the corresponding terminal-payoff mixture.  If

* `mix` dominates a floor;
* every positive-mass owner is pinned at its own solo payoff;
* every solo payoff is below the floor; and
* the floor dominates every quitting punishment value,

then the mixture is a period-one `FaceCirculationCertificate`. The
finite-closing circulation compiler consequently supplies an ordinary uniform
equilibrium payoff.  No public randomization or source-theorem assumption is
used here.
-/

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The payoff vector obtained by mixing the singleton quitting rewards with
weights `nu`. -/
def quittingSingletonMixture
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (nu : ι → ℝ) : Payoff ι :=
  fun who => ∑ owner,
    nu owner * reward (quittingSingletonTerminal owner) who

omit [Fintype ι] [DecidableEq ι] in
/-- Extending a quitting reward by zero at the empty coalition does not alter
a singleton reward. -/
@[simp]
theorem weightOfReward_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner who : ι) :
    weightOfReward reward {owner} who =
      reward (quittingSingletonTerminal owner) who := by
  simp [weightOfReward, quittingSingletonTerminal]

omit [DecidableEq ι] in
/-- The circulation layer's `mixTarget` is exactly the quitting singleton
mixture after extending the reward to all coalitions. -/
@[simp]
theorem mixTarget_weightOfReward_eq_quittingSingletonMixture
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (nu : ι → ℝ) :
    mixTarget (weightOfReward reward) nu =
      quittingSingletonMixture reward nu := by
  funext who
  simp only [mixTarget, quittingSingletonMixture,
    weightOfReward_singleton]

/-- A complementary singleton mixture is a period-one face circulation.

The vertex and the phase target are both the singleton mixture, while the
contraction ratio is `1 / 2`.  Thus the circulation step is the tautological
identity `mix = (1/2) mix + (1/2) mix`; the substantive hypotheses are exactly
the floor and complementarity inequalities exposed in the signature. -/
def quittingSingletonMixtureFaceCirculationCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (nu : ι → ℝ) (floor : Payoff ι)
    (hnu_nonneg : ∀ owner, 0 ≤ nu owner)
    (hnu_sum : ∑ owner, nu owner = 1)
    (hmix_ge_floor : ∀ who,
      floor who ≤ quittingSingletonMixture reward nu who)
    (hactive_pinned : ∀ owner, 0 < nu owner →
      quittingSingletonMixture reward nu owner =
        reward (quittingSingletonTerminal owner) owner)
    (hsolo_le_floor : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ floor who) :
    FaceCirculationCertificate (weightOfReward reward) floor 1 where
  vertex := fun _ => quittingSingletonMixture reward nu
  mixWeight := fun _ => nu
  ratio := fun _ => 1 / 2
  mixWeight_nonneg := fun _ owner => hnu_nonneg owner
  mixWeight_sum := fun _ => hnu_sum
  ratio_pos := fun _ => by norm_num
  ratio_lt_one := fun _ => by norm_num
  step := by
    intro phase who
    rw [mixTarget_weightOfReward_eq_quittingSingletonMixture]
    ring
  vertex_ge_floor := fun _ who => hmix_ge_floor who
  vertex_pinned := fun _ owner howner => hactive_pinned owner howner
  target_pinned := by
    intro phase owner howner
    rw [mixTarget_weightOfReward_eq_quittingSingletonMixture]
    exact hactive_pinned owner howner
  solo_le_floor := by
    intro who
    rw [weightOfReward_singleton]
    exact hsolo_le_floor who

/-- **Complementary singleton-mixture compiler.**

A probability mixture of singleton quitting rewards satisfying the displayed
floor, pinning, and punishment inequalities produces an ordinary uniform
equilibrium payoff.  The conclusion is existential because the general
finite-closing circulation theorem selects a compact-limit payoff; no claim
that this selected payoff is definitionally the supplied singleton mixture is
needed for the existence capstone. -/
theorem exists_uniformEquilibriumPayoff_of_complementarySingletonMixture
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (nu : ι → ℝ) (floor : Payoff ι)
    (hnu_nonneg : ∀ owner, 0 ≤ nu owner)
    (hnu_sum : ∑ owner, nu owner = 1)
    (hmix_ge_floor : ∀ who,
      floor who ≤ quittingSingletonMixture reward nu who)
    (hactive_pinned : ∀ owner, 0 < nu owner →
      quittingSingletonMixture reward nu owner =
        reward (quittingSingletonTerminal owner) owner)
    (hsolo_le_floor : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ floor who)
    (hpunishment_le_floor : ∀ who,
      quittingPunishmentValue reward who ≤ floor who) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let certificate :
      FaceCirculationCertificate (weightOfReward reward) floor 1 :=
    quittingSingletonMixtureFaceCirculationCertificate
      reward nu floor hnu_nonneg hnu_sum hmix_ge_floor
        hactive_pinned hsolo_le_floor
  have hweight_bound : ∀ S who,
      |weightOfReward reward S who| ≤ quittingRewardBound reward := by
    intro S who
    by_cases hS : S.Nonempty
    · simpa [weightOfReward, hS] using
        (abs_reward_le_quittingRewardBound reward ⟨S, hS⟩ who)
    · simp [weightOfReward, hS, quittingRewardBound_nonneg reward]
  have hsupport : ∀ phase,
      (mixSupport (certificate.mixWeight phase)).card ≤ Fintype.card ι := by
    intro phase
    exact Finset.card_le_univ _
  have hratio : ∀ phase, certificate.ratio phase ≤ (1 / 2 : ℝ) := by
    intro phase
    rfl
  have hroundtrip : rewardOfWeight (weightOfReward reward) = reward := by
    funext terminal who
    exact rewardOfWeight_weightOfReward reward terminal who
  have hpunishment_roundtrip : ∀ who,
      quittingPunishmentValue
          (rewardOfWeight (weightOfReward reward)) who ≤ floor who := by
    intro who
    rw [hroundtrip]
    exact hpunishment_le_floor who
  have hcompiled :=
    quittingGame_exists_uniformEquilibriumPayoff_of_multiCirculation_finiteClosing
      (C := certificate)
      (M := quittingRewardBound reward)
      (hM0 := quittingRewardBound_nonneg reward)
      (hM := hweight_bound)
      (s := Fintype.card ι)
      (hs := hsupport)
      (a := (1 / 2 : ℝ))
      (ha := hratio)
      (ha1 := by norm_num)
      (hpunishmentFloor := hpunishment_roundtrip)
  rw [hroundtrip] at hcompiled
  exact hcompiled

end GameTheory
