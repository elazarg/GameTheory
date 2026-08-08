/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Projective.SingletonLCP

/-!
# Anchored normalized singleton projective LCP packets

The initial vanishing-discount compactification uses cemetery payoff `0`, but
projective pivoting may rebase the cemetery event to an affine continuation
anchor `anchor`.  The correct packet identity is then

`value who = cemetery * anchor who +
  ∑ owner, singleton owner * reward {owner} who`.

Writing

`d_i = reward {i} i`,

`a_i = anchor_i - d_i`,

`M_ij = reward {j} i - d_i`,

`w_i = value_i - d_i`,

one obtains the same normalized LCP equations

`w_i = cemetery * a_i + ∑ j, singleton j * M_ij`,

`w_i ≥ 0`, and `singleton i * w_i = 0`.

At cemetery mass one the conclusion is `value = anchor` and
`reward {i} i ≤ anchor i`; this is the Never boundary only in the zero-anchor
specialization.  `QuittingProjectiveSingletonPacket.toAnchored` embeds the
existing zero-anchor packet into this general interface.
-/

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A normalized singleton first-event packet with an affine cemetery anchor. -/
structure QuittingAnchoredProjectiveSingletonPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  anchor : Payoff ι
  cemetery : ℝ
  singleton : ι → ℝ
  value : Payoff ι
  cemetery_nonneg : 0 ≤ cemetery
  singleton_nonneg : ∀ who, 0 ≤ singleton who
  total : cemetery + ∑ who, singleton who = 1
  value_eq_anchored_mix : ∀ who,
    value who = cemetery * anchor who +
      ∑ owner,
        singleton owner * reward (quittingProjectiveSingletonTerminal owner) who
  solo_le_value : ∀ who,
    reward (quittingProjectiveSingletonTerminal who) who ≤ value who
  positive_singleton_pins : ∀ who,
    0 < singleton who →
      value who = reward (quittingProjectiveSingletonTerminal who) who

/-- The anchored cemetery direction `a_i = anchor_i - r_i({i})`. -/
def quittingAnchoredProjectiveLCPDirection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (anchor : Payoff ι) (who : ι) : ℝ :=
  anchor who - reward (quittingProjectiveSingletonTerminal who) who

omit [DecidableEq ι] in
/-- Exact affine LCP balance of an anchored normalized singleton packet. -/
theorem quittingAnchoredProjectiveSingletonPacket_balance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (packet : QuittingAnchoredProjectiveSingletonPacket reward) (who : ι) :
    quittingProjectiveLCPSlack reward packet.value who =
      packet.cemetery *
          quittingAnchoredProjectiveLCPDirection reward packet.anchor who +
        ∑ owner, packet.singleton owner *
          quittingProjectiveLCPMatrix reward who owner := by
  classical
  unfold quittingProjectiveLCPSlack quittingAnchoredProjectiveLCPDirection
    quittingProjectiveLCPMatrix
  rw [packet.value_eq_anchored_mix]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hsum : ∑ owner, packet.singleton owner = 1 - packet.cemetery := by
    linarith [packet.total]
  rw [hsum]
  ring

omit [DecidableEq ι] in
/-- Every anchored projective LCP slack is nonnegative. -/
theorem quittingAnchoredProjectiveSingletonPacket_slack_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (packet : QuittingAnchoredProjectiveSingletonPacket reward) (who : ι) :
    0 ≤ quittingProjectiveLCPSlack reward packet.value who := by
  classical
  exact sub_nonneg.mpr (packet.solo_le_value who)

omit [DecidableEq ι] in
/-- Singleton mass is complementary to its owner's slack in an anchored packet. -/
theorem quittingAnchoredProjectiveSingletonPacket_complementary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (packet : QuittingAnchoredProjectiveSingletonPacket reward) (who : ι) :
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
/-- **Anchored projective first-event LCP theorem.** -/
theorem quittingAnchoredProjectiveSingletonPacket_isLCP
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (packet : QuittingAnchoredProjectiveSingletonPacket reward) :
    (∀ who,
      quittingProjectiveLCPSlack reward packet.value who =
        packet.cemetery *
            quittingAnchoredProjectiveLCPDirection reward packet.anchor who +
          ∑ owner, packet.singleton owner *
            quittingProjectiveLCPMatrix reward who owner) ∧
    (∀ who, 0 ≤ quittingProjectiveLCPSlack reward packet.value who) ∧
    ∀ who,
      packet.singleton who *
        quittingProjectiveLCPSlack reward packet.value who = 0 := by
  classical
  exact ⟨quittingAnchoredProjectiveSingletonPacket_balance reward packet,
    quittingAnchoredProjectiveSingletonPacket_slack_nonneg reward packet,
    quittingAnchoredProjectiveSingletonPacket_complementary reward packet⟩

omit [DecidableEq ι] in
/-- Every singleton mass vanishes at cemetery mass one. -/
theorem QuittingAnchoredProjectiveSingletonPacket.singleton_eq_zero_of_cemetery_eq_one
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingAnchoredProjectiveSingletonPacket reward)
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
/-- At cemetery mass one, the packet reproduces its affine anchor and every
solo payoff lies below that anchor. -/
theorem QuittingAnchoredProjectiveSingletonPacket.cemetery_one_boundary
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingAnchoredProjectiveSingletonPacket reward)
    (hcemetery : packet.cemetery = 1) :
    packet.value = packet.anchor ∧
      ∀ who,
        reward (quittingProjectiveSingletonTerminal who) who ≤ packet.anchor who := by
  classical
  have hzero : ∀ owner, packet.singleton owner = 0 :=
    packet.singleton_eq_zero_of_cemetery_eq_one hcemetery
  have hvalue : packet.value = packet.anchor := by
    funext who
    rw [packet.value_eq_anchored_mix, hcemetery]
    simp [hzero]
  refine ⟨hvalue, ?_⟩
  intro who
  calc
    reward (quittingProjectiveSingletonTerminal who) who ≤ packet.value who :=
      packet.solo_le_value who
    _ = packet.anchor who := congrFun hvalue who

/-- The original normalized singleton packet is the zero-anchor specialization
of the anchored packet. -/
def QuittingProjectiveSingletonPacket.toAnchored
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (packet : QuittingProjectiveSingletonPacket reward) :
    QuittingAnchoredProjectiveSingletonPacket reward where
  anchor := 0
  cemetery := packet.cemetery
  singleton := packet.singleton
  value := packet.value
  cemetery_nonneg := packet.cemetery_nonneg
  singleton_nonneg := packet.singleton_nonneg
  total := packet.total
  value_eq_anchored_mix := by
    intro who
    simpa using packet.value_eq_singleton_mix who
  solo_le_value := packet.solo_le_value
  positive_singleton_pins := packet.positive_singleton_pins

omit [DecidableEq ι] in
/-- The anchored LCP theorem specializes definitionally to the original
zero-anchor packet. -/
theorem quittingProjectiveSingletonPacket_isAnchoredLCP
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (packet : QuittingProjectiveSingletonPacket reward) :
    (∀ who,
      quittingProjectiveLCPSlack reward packet.value who =
        packet.cemetery *
            quittingAnchoredProjectiveLCPDirection reward 0 who +
          ∑ owner, packet.singleton owner *
            quittingProjectiveLCPMatrix reward who owner) ∧
    (∀ who, 0 ≤ quittingProjectiveLCPSlack reward packet.value who) ∧
    ∀ who,
      packet.singleton who *
        quittingProjectiveLCPSlack reward packet.value who = 0 := by
  classical
  simpa [QuittingProjectiveSingletonPacket.toAnchored] using
    quittingAnchoredProjectiveSingletonPacket_isLCP reward packet.toAnchored

end GameTheory
