/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingRootContinuation

/-!
# The normalized singleton projective LCP

The positive-cemetery first-event limit of a vanishing-discount quitting
branch has a simple algebraic core.  After nonsingleton quitting packets have
vanished, write `z₀` for cemetery mass, `z i` for the singleton `{i}` mass,
and `value` for the limiting payoff.  The packet identities are

`z₀ + ∑ i, z i = 1`,

`value who = ∑ i, z i * reward {i} who`.

Endpoint complementarity supplies two further facts: every solo payoff is at
most the limiting value, and a singleton with positive mass pins its owner at
that solo payoff.  This file proves that these data are exactly a normalized
linear-complementarity packet.

For

`d i = reward {i} i`,

`a i = -d i`,

`M i j = reward {j} i - d i`,

`w i = value i - d i`,

we obtain

`w i = z₀ * a i + ∑ j, z j * M i j`,

`w i ≥ 0`, and `z i * w i = 0`.

This is the algebraic endpoint of the projective first-event extraction.  The
separate analytic task is to prove that a supplied discounted branch has a
limit packet satisfying the hypotheses below; no strategic realization or
chronological decoder is claimed here.
-/

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The terminal state associated with the singleton quitter set `{who}`. -/
def quittingProjectiveSingletonTerminal (who : ι) :
    {S : Finset ι // S.Nonempty} :=
  ⟨{who}, by simp⟩

/-- Data retained by a normalized singleton first-event packet. -/
structure QuittingProjectiveSingletonPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  cemetery : ℝ
  singleton : ι → ℝ
  value : Payoff ι
  cemetery_nonneg : 0 ≤ cemetery
  singleton_nonneg : ∀ who, 0 ≤ singleton who
  total : cemetery + ∑ who, singleton who = 1
  value_eq_singleton_mix : ∀ who,
    value who = ∑ owner,
      singleton owner * reward (quittingProjectiveSingletonTerminal owner) who
  solo_le_value : ∀ who,
    reward (quittingProjectiveSingletonTerminal who) who ≤ value who
  positive_singleton_pins : ∀ who,
    0 < singleton who →
      value who = reward (quittingProjectiveSingletonTerminal who) who

/-- The affine cemetery direction `a_i = -r_i({i})`. -/
def quittingProjectiveLCPDirection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) : ℝ :=
  -reward (quittingProjectiveSingletonTerminal who) who

/-- The singleton comparison matrix
`M_{ij} = r_i({j}) - r_i({i})`. -/
def quittingProjectiveLCPMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) : ℝ :=
  reward (quittingProjectiveSingletonTerminal owner) who -
    reward (quittingProjectiveSingletonTerminal who) who

/-- The complementary slack `w_i = value_i - r_i({i})`. -/
def quittingProjectiveLCPSlack
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : Payoff ι) (who : ι) : ℝ :=
  value who - reward (quittingProjectiveSingletonTerminal who) who

omit [DecidableEq ι] in
/-- Exact affine LCP balance of a normalized singleton packet. -/
theorem quittingProjectiveSingletonPacket_balance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (packet : QuittingProjectiveSingletonPacket reward) (who : ι) :
    quittingProjectiveLCPSlack reward packet.value who =
      packet.cemetery * quittingProjectiveLCPDirection reward who +
        ∑ owner, packet.singleton owner *
          quittingProjectiveLCPMatrix reward who owner := by
  classical
  unfold quittingProjectiveLCPSlack quittingProjectiveLCPDirection
    quittingProjectiveLCPMatrix
  rw [packet.value_eq_singleton_mix]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hsum : ∑ owner, packet.singleton owner = 1 - packet.cemetery := by
    linarith [packet.total]
  rw [hsum]
  ring

omit [DecidableEq ι] in
/-- Every projective LCP slack is nonnegative. -/
theorem quittingProjectiveSingletonPacket_slack_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (packet : QuittingProjectiveSingletonPacket reward) (who : ι) :
    0 ≤ quittingProjectiveLCPSlack reward packet.value who := by
  classical
  exact sub_nonneg.mpr (packet.solo_le_value who)

omit [DecidableEq ι] in
/-- Singleton mass is complementary to its owner's slack. -/
theorem quittingProjectiveSingletonPacket_complementary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (packet : QuittingProjectiveSingletonPacket reward) (who : ι) :
    packet.singleton who *
      quittingProjectiveLCPSlack reward packet.value who = 0 := by
  classical
  by_cases hzero : packet.singleton who = 0
  · simp [hzero]
  · have hpos : 0 < packet.singleton who :=
      lt_of_le_of_ne (packet.singleton_nonneg who) (Ne.symm hzero)
    rw [quittingProjectiveLCPSlack,
      packet.positive_singleton_pins who hpos, sub_self, mul_zero]

omit [DecidableEq ι] in
/-- **Projective first-event LCP theorem, algebraic form.**
A normalized singleton packet satisfies the affine balance, nonnegative
slack, and complementarity equations simultaneously. -/
theorem quittingProjectiveSingletonPacket_isLCP
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (packet : QuittingProjectiveSingletonPacket reward) :
    (∀ who,
      quittingProjectiveLCPSlack reward packet.value who =
        packet.cemetery * quittingProjectiveLCPDirection reward who +
          ∑ owner, packet.singleton owner *
            quittingProjectiveLCPMatrix reward who owner) ∧
    (∀ who, 0 ≤ quittingProjectiveLCPSlack reward packet.value who) ∧
    ∀ who,
      packet.singleton who *
        quittingProjectiveLCPSlack reward packet.value who = 0 := by
  classical
  exact ⟨quittingProjectiveSingletonPacket_balance reward packet,
    quittingProjectiveSingletonPacket_slack_nonneg reward packet,
    quittingProjectiveSingletonPacket_complementary reward packet⟩

omit [DecidableEq ι] in
/-- At cemetery mass one, every singleton mass vanishes. -/
theorem QuittingProjectiveSingletonPacket.singleton_eq_zero_of_cemetery_eq_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingProjectiveSingletonPacket reward)
    (hcemetery : packet.cemetery = 1) (who : ι) :
    packet.singleton who = 0 := by
  classical
  have hsum : ∑ owner, packet.singleton owner = 0 := by
    linarith [packet.total]
  have hsingle : packet.singleton who ≤ ∑ owner, packet.singleton owner :=
    Finset.single_le_sum
      (fun owner _ => packet.singleton_nonneg owner)
      (Finset.mem_univ who)
  rw [hsum] at hsingle
  exact le_antisymm hsingle (packet.singleton_nonneg who)

omit [DecidableEq ι] in
/-- The cemetery-one boundary is the all-Continue/Never payoff: the packet
value is zero and every solo payoff is nonpositive. -/
theorem QuittingProjectiveSingletonPacket.cemetery_one_boundary
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingProjectiveSingletonPacket reward)
    (hcemetery : packet.cemetery = 1) :
    packet.value = 0 ∧
      ∀ who, reward (quittingProjectiveSingletonTerminal who) who ≤ 0 := by
  classical
  have hzero : ∀ owner, packet.singleton owner = 0 :=
    packet.singleton_eq_zero_of_cemetery_eq_one hcemetery
  have hvalue : packet.value = 0 := by
    funext who
    rw [packet.value_eq_singleton_mix]
    simp [hzero]
  refine ⟨hvalue, ?_⟩
  intro who
  calc
    reward (quittingProjectiveSingletonTerminal who) who ≤ packet.value who :=
      packet.solo_le_value who
    _ = 0 := congrFun hvalue who

end GameTheory
