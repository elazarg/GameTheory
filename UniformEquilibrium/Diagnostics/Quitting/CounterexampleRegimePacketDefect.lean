/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketSurplus

/-!
# A uniform compact defect for normalized singleton packets

For a fixed reward table, normalized singleton source packets form a compact
finite-dimensional set once active pinning is written as the closed
complementarity equation

`mass i * (target i - solo i) = 0`.

The continuous defect

`max_i mass i * (singletonMixture i - target i)`

is strictly positive at every packet of a counterexample regime: zero defect
would make every active row complementary, and the singleton-circulation
compiler would produce a uniform equilibrium.  Compactness therefore gives
one positive margin for all normalized packets of the fixed reward table.

The maximizing coordinate turns that defect into a refusal advantage of at
least the same margin.  This robustifies the finite packet obstruction
against small reconstruction errors, but does not identify packet mass with
the occupation law of a late dynamic-debt window.
-/

noncomputable section

namespace GameTheory

open Finset Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Raw mass/target coordinates for the closed normalized packet model. -/
abbrev QuittingNormalizedSingletonPacketData (ι : Type) :=
  (ι → ℝ) × Payoff ι

/-- The closed coordinate model equivalent to a normalized singleton source
packet. -/
def quittingNormalizedSingletonPacketDataSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingNormalizedSingletonPacketData ι) :=
  {data |
    (∀ owner, 0 ≤ data.1 owner) ∧
    (∑ owner, data.1 owner = 1) ∧
    (∀ who, data.2 who ≤ quittingSingletonMixture reward data.1 who) ∧
    (∀ who, reward (quittingSingletonTerminal who) who ≤ data.2 who) ∧
    (∀ who, quittingPunishmentValue reward who ≤ data.2 who) ∧
    (∀ owner, data.1 owner *
      (data.2 owner - reward (quittingSingletonTerminal owner) owner) = 0)}

omit [DecidableEq ι] in
/-- Singleton mixtures depend continuously on their mass vector. -/
theorem continuous_quittingSingletonMixture_apply (who : ι) :
    Continuous (fun mass : ι → ℝ ↦
      quittingSingletonMixture reward mass who) := by
  unfold quittingSingletonMixture
  apply continuous_finsetSum
  intro owner _
  exact (continuous_apply owner).mul continuous_const

/-- The raw normalized packet model is closed. -/
theorem quittingNormalizedSingletonPacketDataSet_isClosed :
    IsClosed (quittingNormalizedSingletonPacketDataSet reward) := by
  let massNonneg : Set (QuittingNormalizedSingletonPacketData ι) :=
    {data | ∀ owner, 0 ≤ data.1 owner}
  let massOne : Set (QuittingNormalizedSingletonPacketData ι) :=
    {data | ∑ owner, data.1 owner = 1}
  let mixDominates : Set (QuittingNormalizedSingletonPacketData ι) :=
    {data | ∀ who,
      data.2 who ≤ quittingSingletonMixture reward data.1 who}
  let soloDominates : Set (QuittingNormalizedSingletonPacketData ι) :=
    {data | ∀ who,
      reward (quittingSingletonTerminal who) who ≤ data.2 who}
  let punishmentDominates : Set (QuittingNormalizedSingletonPacketData ι) :=
    {data | ∀ who, quittingPunishmentValue reward who ≤ data.2 who}
  let complementary : Set (QuittingNormalizedSingletonPacketData ι) :=
    {data | ∀ owner, data.1 owner *
      (data.2 owner - reward (quittingSingletonTerminal owner) owner) = 0}
  have hmassNonneg : IsClosed massNonneg := by
    rw [show massNonneg = ⋂ owner,
        {data | data.1 owner ∈ Set.Ici (0 : ℝ)} by
      ext data
      simp [massNonneg]]
    exact isClosed_iInter fun owner ↦
      isClosed_Ici.preimage ((continuous_apply owner).comp continuous_fst)
  have hmassOne : IsClosed massOne := by
    have hcontinuous : Continuous (fun data :
        QuittingNormalizedSingletonPacketData ι ↦ ∑ owner, data.1 owner) := by
      exact continuous_finsetSum _ fun owner _ ↦
        (continuous_apply owner).comp continuous_fst
    exact isClosed_singleton.preimage hcontinuous
  have hmix : IsClosed mixDominates := by
    rw [show mixDominates = ⋂ who,
        {data | data.2 who -
          quittingSingletonMixture reward data.1 who ∈ Set.Iic (0 : ℝ)} by
      ext data
      simp [mixDominates]]
    exact isClosed_iInter fun who ↦ isClosed_Iic.preimage
      (((continuous_apply who).comp continuous_snd).sub
        ((continuous_quittingSingletonMixture_apply
          (reward := reward) who).comp continuous_fst))
  have hsolo : IsClosed soloDominates := by
    rw [show soloDominates = ⋂ who,
        {data | data.2 who ∈ Set.Ici
          (reward (quittingSingletonTerminal who) who)} by
      ext data
      simp [soloDominates]]
    exact isClosed_iInter fun who ↦ isClosed_Ici.preimage
      ((continuous_apply who).comp continuous_snd)
  have hpunishment : IsClosed punishmentDominates := by
    rw [show punishmentDominates = ⋂ who,
        {data | data.2 who ∈ Set.Ici
          (quittingPunishmentValue reward who)} by
      ext data
      simp [punishmentDominates]]
    exact isClosed_iInter fun who ↦ isClosed_Ici.preimage
      ((continuous_apply who).comp continuous_snd)
  have hcomplementary : IsClosed complementary := by
    rw [show complementary = ⋂ owner,
        {data | data.1 owner *
          (data.2 owner - reward (quittingSingletonTerminal owner) owner) ∈
            ({0} : Set ℝ)} by
      ext data
      simp [complementary]]
    exact isClosed_iInter fun owner ↦ isClosed_singleton.preimage
      (((continuous_apply owner).comp continuous_fst).mul
        (((continuous_apply owner).comp continuous_snd).sub continuous_const))
  rw [show quittingNormalizedSingletonPacketDataSet reward =
      massNonneg ∩ (massOne ∩ (mixDominates ∩ (soloDominates ∩
        (punishmentDominates ∩ complementary)))) by
    ext data
    simp [quittingNormalizedSingletonPacketDataSet, massNonneg, massOne,
      mixDominates, soloDominates, punishmentDominates, complementary]]
  exact hmassNonneg.inter (hmassOne.inter (hmix.inter
    (hsolo.inter (hpunishment.inter hcomplementary))))

omit [DecidableEq ι] in
/-- A probability mixture of singleton rewards lies in the canonical reward
interval. -/
theorem abs_quittingSingletonMixture_le_rewardBound_of_probability
    (mass : ι → ℝ) (hmass : ∀ owner, 0 ≤ mass owner)
    (hsum : ∑ owner, mass owner = 1) (who : ι) :
    |quittingSingletonMixture reward mass who| ≤ quittingRewardBound reward := by
  have hupper : quittingSingletonMixture reward mass who ≤
      quittingRewardBound reward := by
    unfold quittingSingletonMixture
    calc
      (∑ owner, mass owner * reward (quittingSingletonTerminal owner) who) ≤
          ∑ owner, mass owner * quittingRewardBound reward :=
        Finset.sum_le_sum fun owner _ ↦
          mul_le_mul_of_nonneg_left
            ((le_abs_self _).trans
              (abs_reward_le_quittingRewardBound reward
                (quittingSingletonTerminal owner) who))
            (hmass owner)
      _ = quittingRewardBound reward := by
        rw [← Finset.sum_mul, hsum, one_mul]
  have hlower : -quittingRewardBound reward ≤
      quittingSingletonMixture reward mass who := by
    unfold quittingSingletonMixture
    calc
      -quittingRewardBound reward =
          ∑ owner, mass owner * (-quittingRewardBound reward) := by
        rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ owner,
          mass owner * reward (quittingSingletonTerminal owner) who :=
        Finset.sum_le_sum fun owner _ ↦
          mul_le_mul_of_nonneg_left
            (neg_le_of_abs_le
              (abs_reward_le_quittingRewardBound reward
                (quittingSingletonTerminal owner) who))
            (hmass owner)
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- The closed raw packet model is compact. -/
theorem quittingNormalizedSingletonPacketDataSet_isCompact :
    IsCompact (quittingNormalizedSingletonPacketDataSet reward) := by
  let lowerMass : ι → ℝ := 0
  let upperMass : ι → ℝ := 1
  let lowerTarget : Payoff ι := fun _ ↦ -quittingRewardBound reward
  let upperTarget : Payoff ι := fun _ ↦ quittingRewardBound reward
  have hambient : IsCompact
      (Set.Icc lowerMass upperMass ×ˢ Set.Icc lowerTarget upperTarget) :=
    isCompact_Icc.prod isCompact_Icc
  apply hambient.of_isClosed_subset
    quittingNormalizedSingletonPacketDataSet_isClosed
  intro data hdata
  rcases hdata with ⟨hmass, hsum, hmix, hsolo, -, -⟩
  constructor
  · constructor
    · exact hmass
    · intro owner
      change data.1 owner ≤ 1
      rw [← hsum]
      exact Finset.single_le_sum (fun other _ ↦ hmass other)
        (Finset.mem_univ owner)
  · constructor
    · intro who
      change -quittingRewardBound reward ≤ data.2 who
      exact (neg_le_of_abs_le
        (abs_reward_le_quittingRewardBound reward
          (quittingSingletonTerminal who) who)).trans (hsolo who)
    · intro who
      change data.2 who ≤ quittingRewardBound reward
      exact (hmix who).trans
        (abs_le.mp (abs_quittingSingletonMixture_le_rewardBound_of_probability
          data.1 hmass hsum who)).2

namespace QuittingNormalizedSingletonSourcePacket

/-- The mass/target coordinates of a packet belong to the closed raw model. -/
theorem data_mem
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    (packet.mass, packet.target) ∈
      quittingNormalizedSingletonPacketDataSet reward := by
  refine ⟨packet.mass_nonneg, packet.mass_sum, packet.mix_ge_target,
    packet.solo_le_target, packet.punishment_le_target, ?_⟩
  intro owner
  change packet.mass owner *
    (packet.target owner - reward (quittingSingletonTerminal owner) owner) = 0
  by_cases hzero : packet.mass owner = 0
  · rw [hzero, zero_mul]
  · have hpos : 0 < packet.mass owner :=
      lt_of_le_of_ne (packet.mass_nonneg owner) (Ne.symm hzero)
    rw [packet.positive_mass_pins_target owner hpos, sub_self, mul_zero]

end QuittingNormalizedSingletonSourcePacket

/-- Reconstruct a packet from any point in the closed raw model. -/
def quittingNormalizedSingletonSourcePacketOfData
    (data : QuittingNormalizedSingletonPacketData ι)
    (hdata : data ∈ quittingNormalizedSingletonPacketDataSet reward) :
    QuittingNormalizedSingletonSourcePacket reward where
  mass := data.1
  target := data.2
  mass_nonneg := hdata.1
  mass_sum := hdata.2.1
  mix_ge_target := hdata.2.2.1
  solo_le_target := hdata.2.2.2.1
  punishment_le_target := hdata.2.2.2.2.1
  positive_mass_pins_target := fun owner hpos ↦ by
    have hproduct := hdata.2.2.2.2.2 owner
    rcases mul_eq_zero.mp hproduct with hmass | hgap
    · exact (hpos.ne' hmass).elim
    · linarith

section Defect

variable [Nonempty ι]

/-- Continuous complementarity defect of raw packet coordinates. -/
def quittingNormalizedSingletonPacketDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (data : QuittingNormalizedSingletonPacketData ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun who ↦
    data.1 who *
      (quittingSingletonMixture reward data.1 who - data.2 who)

omit [DecidableEq ι] in
/-- The raw packet defect is continuous. -/
theorem continuous_quittingNormalizedSingletonPacketDefect :
    Continuous (quittingNormalizedSingletonPacketDefect reward) := by
  unfold quittingNormalizedSingletonPacketDefect
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro who _
  exact ((continuous_apply who).comp continuous_fst).mul
    (((continuous_quittingSingletonMixture_apply
      (reward := reward) who).comp continuous_fst).sub
      ((continuous_apply who).comp continuous_snd))

/-- In a counterexample regime, the defect is positive at every raw packet. -/
theorem quittingNormalizedSingletonPacketDefect_pos
    (regime : QuittingCounterexampleRegime reward)
    (data : QuittingNormalizedSingletonPacketData ι)
    (hdata : data ∈ quittingNormalizedSingletonPacketDataSet reward) :
    0 < quittingNormalizedSingletonPacketDefect reward data := by
  let packet := quittingNormalizedSingletonSourcePacketOfData data hdata
  obtain ⟨owner, hmass, hsurplus⟩ :=
    regime.exists_active_strictSingletonSurplus packet
  have hterm : 0 < data.1 owner *
      (quittingSingletonMixture reward data.1 owner - data.2 owner) :=
    mul_pos hmass (sub_pos.mpr hsurplus)
  exact hterm.trans_le (Finset.le_sup'
    (f := fun who ↦ data.1 who *
      (quittingSingletonMixture reward data.1 who - data.2 who))
    (Finset.mem_univ owner))

namespace QuittingCounterexampleRegime

/-- **Uniform packet-defect margin.**  One positive number works for every
normalized singleton packet of the fixed counterexample reward table. -/
theorem exists_pos_uniform_normalizedSingletonPacketDefect
    (regime : QuittingCounterexampleRegime reward) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ packet : QuittingNormalizedSingletonSourcePacket reward,
        δ ≤ quittingNormalizedSingletonPacketDefect reward
          (packet.mass, packet.target) := by
  obtain ⟨packet⟩ := regime.nonempty_normalizedSingletonSourcePacket
  have hnonempty :
      (quittingNormalizedSingletonPacketDataSet reward).Nonempty :=
    ⟨(packet.mass, packet.target), packet.data_mem⟩
  obtain ⟨data, hdata, hmin⟩ :=
    quittingNormalizedSingletonPacketDataSet_isCompact.exists_isMinOn
      hnonempty
      continuous_quittingNormalizedSingletonPacketDefect.continuousOn
  exact ⟨quittingNormalizedSingletonPacketDefect reward data,
    quittingNormalizedSingletonPacketDefect_pos regime data hdata,
    fun candidate ↦ hmin candidate.data_mem⟩

/-- The uniform defect is a uniform refusal advantage on one active atom of
every normalized packet. -/
theorem exists_pos_uniform_normalizedSingletonPacketRefusal
    (regime : QuittingCounterexampleRegime reward) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ packet : QuittingNormalizedSingletonSourcePacket reward,
        ∃ owner,
          0 < packet.mass owner ∧ packet.mass owner < 1 ∧
          packet.target owner <
            quittingSingletonMixture reward packet.mass owner ∧
          quittingSingletonMixture reward packet.mass owner + δ ≤
            quittingSingletonRefusalValue reward packet.mass owner owner := by
  obtain ⟨δ, hδ, hdefect⟩ :=
    regime.exists_pos_uniform_normalizedSingletonPacketDefect
  refine ⟨δ, hδ, fun packet ↦ ?_⟩
  obtain ⟨owner, _, howner⟩ := Finset.exists_mem_eq_sup'
    Finset.univ_nonempty
    (fun who ↦ packet.mass who *
      (quittingSingletonMixture reward packet.mass who - packet.target who))
  have hproduct : δ ≤ packet.mass owner *
      (quittingSingletonMixture reward packet.mass owner -
        packet.target owner) := by
    rw [← howner]
    exact hdefect packet
  have hproductPos : 0 < packet.mass owner *
      (quittingSingletonMixture reward packet.mass owner -
        packet.target owner) := hδ.trans_le hproduct
  have hmass : 0 < packet.mass owner := by
    by_contra hnot
    have hle : packet.mass owner ≤ 0 := le_of_not_gt hnot
    have hsurplusNonneg := sub_nonneg.mpr (packet.mix_ge_target owner)
    have : packet.mass owner *
        (quittingSingletonMixture reward packet.mass owner -
          packet.target owner) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hsurplusNonneg
    linarith
  have hsurplus : packet.target owner <
      quittingSingletonMixture reward packet.mass owner := by
    have hmassNonneg := hmass.le
    by_contra hnot
    have hle : quittingSingletonMixture reward packet.mass owner -
        packet.target owner ≤ 0 := by linarith
    have : packet.mass owner *
        (quittingSingletonMixture reward packet.mass owner -
          packet.target owner) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hmassNonneg hle
    linarith
  have hmassLt : packet.mass owner < 1 := by
    apply lt_of_le_of_ne (packet.mass_le_one owner)
    intro hone
    rw [packet.singletonMixture_eq_singleton_of_mass_eq_one hone owner,
      ← packet.positive_mass_pins_target owner hmass] at hsurplus
    exact (lt_irrefl _ hsurplus)
  have hodds : packet.mass owner ≤
      packet.mass owner / (1 - packet.mass owner) := by
    apply (le_div_iff₀ (sub_pos.mpr hmassLt)).2
    nlinarith [packet.mass_nonneg owner]
  have hgain := packet.refusal_sub_mixture_eq_mass_div_mul_surplus
    hmass hmassLt
  have hscaled := mul_le_mul_of_nonneg_right hodds (sub_pos.mpr hsurplus).le
  refine ⟨owner, hmass, hmassLt, hsurplus, ?_⟩
  linarith

end QuittingCounterexampleRegime

end Defect

end GameTheory
