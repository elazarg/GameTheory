/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationPath
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Projective.FiniteForwardProjectiveLasso

/-!
# Finite charged closing for face circulations

The original circulation producer has the quantifier shape

`∀ ε > 0, ∀ Q, ∃ finite forward orbit with prefix charge at least Q`.

This file retains the interval and PMF data hidden by the older public tuple,
places every such orbit in one compact carrier independent of `Q`, and feeds
that finite producer through compact charged return and the single-seam
projective-lasso compiler.  It therefore verifies the finite-quantifier route
against the motivating producer without using
`exists_multiCirculation_orbit_uniform_prefix`.
-/

noncomputable section

namespace GameTheory

open Finset Set Math.PMFProduct Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {r : Finset ι → ι → ℝ} {floor : ι → ℝ} {L : ℕ} [NeZero L]

/-- Rich finite-prefix form of `exists_multiCirculation_orbit`.  In addition
to its original conclusions it retains the phase-survival interval and the
identity `β_l ^ N = ratio_l`, which are needed to turn the real hazard rows
into PMF roots and to obtain a common compact value carrier. -/
theorem exists_multiCirculation_finiteOrbitData [Nonempty ι]
    (C : FaceCirculationCertificate r floor L)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M)
    (s : ℕ) (hs : ∀ l, (mixSupport (C.mixWeight l)).card ≤ s)
    (a : ℝ) (ha : ∀ l, C.ratio l ≤ a) (ha1 : a < 1)
    (ε : ℝ) (hε : 0 < ε) (Q : ℝ) :
    ∃ (N : ℕ) (β : ZMod L → ℝ) (word : ZMod L → ℕ → ι), 0 < N ∧
      (∀ l, 0 ≤ β l) ∧
      (∀ l, β l ≤ 1) ∧
      (∀ l, β l ^ N = C.ratio l) ∧
      (∀ n j, multiActual C word β N (n + 1) j =
        oneStageNext r (multiRow word β N n)
          (multiActual C word β N n) j) ∧
      (∀ n, IsSupportPerfectRow r (multiRow word β N n)
        (multiActual C word β N n) ε) ∧
      (∀ n j, floor j - ε ≤ multiActual C word β N n j) ∧
      ∃ T : ℕ, Q ≤ ∑ n ∈ Finset.range T,
        (1 - continueMass (multiRow word β N n)) := by
  have hs1 : 1 ≤ s :=
    le_trans (Finset.card_pos.mpr
      (mixSupport_nonempty _ (C.mixWeight_nonneg 0) (C.mixWeight_sum 0))) (hs 0)
  have hs1' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  set B : ℝ := 2 * M * ((s : ℝ) - 1) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; nlinarith
  have ha0 : (0 : ℝ) < 1 - a := by linarith
  set D : ℝ := 2 * M + B * (3 - a) / (1 - a) + 1 with hDdef
  have hD0 : 0 < D := by
    have hfrac : 0 ≤ B * (3 - a) / (1 - a) :=
      div_nonneg (mul_nonneg hB0 (by linarith)) ha0.le
    rw [hDdef]
    linarith
  set H : ℝ := ε / D with hHdef
  have hH0 : 0 < H := by
    rw [hHdef]
    exact div_pos hε hD0
  have hHD : H * D = ε := by
    rw [hHdef]
    field_simp
  set K : ℝ := 2 * H * B / (1 - a) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact div_nonneg (by nlinarith [hH0.le]) ha0.le
  have hne : (Finset.univ : Finset (ZMod L)).Nonempty :=
    ⟨0, Finset.mem_univ 0⟩
  set amin : ℝ := Finset.univ.inf' hne C.ratio with hamindef
  have hamin_le : ∀ l, amin ≤ C.ratio l :=
    fun l => Finset.inf'_le _ (Finset.mem_univ l)
  have hamin0 : 0 < amin := by
    rw [hamindef, Finset.lt_inf'_iff]
    exact fun l _ => C.ratio_pos l
  have hamin1 : amin < 1 :=
    lt_of_le_of_lt (hamin_le 0) (C.ratio_lt_one 0)
  obtain ⟨N, b, hN, hb0, hb1, hbN, hbH⟩ :=
    exists_pow_eq_and_one_sub_le amin hamin0 hamin1 H hH0
  have hN0 : N ≠ 0 := hN.ne'
  set β : ZMod L → ℝ := fun l =>
    C.ratio l ^ ((N : ℝ)⁻¹) with hβdef
  have hβ0 : ∀ l, 0 ≤ β l :=
    fun l => Real.rpow_nonneg (C.ratio_pos l).le _
  have hβN : ∀ l, β l ^ N = C.ratio l :=
    fun l => Real.rpow_inv_natCast_pow (C.ratio_pos l).le hN0
  have hβlt : ∀ l, β l < 1 := fun l =>
    Real.rpow_lt_one (C.ratio_pos l).le (C.ratio_lt_one l) (by positivity)
  have hβ1 : ∀ l, β l ≤ 1 := fun l => (hβlt l).le
  have hbβ : ∀ l, b ≤ β l := by
    intro l
    refine le_of_pow_le_pow_left₀ hN0 (hβ0 l) ?_
    rw [hbN, hβN]
    exact hamin_le l
  have hH : ∀ l, 1 - β l ≤ H := fun l => by
    linarith [hbβ l, hbH]
  set word : ZMod L → ℕ → ι :=
    fun l => balancedWord (C.mixWeight l) with hworddef
  have hword : ∀ l t, 0 < C.mixWeight l (word l t) :=
    fun l t => balancedWord_mem_support _
      (C.mixWeight_nonneg l) (C.mixWeight_sum l) t
  have hdrift : ∀ l T j,
      |wordDrift r (C.mixWeight l) (word l) T j| ≤ B := by
    intro l T j
    refine le_trans (abs_wordDrift_balancedWord_le r
      (C.mixWeight l) M hM0 hM
      (C.mixWeight_nonneg l) (C.mixWeight_sum l) T j) ?_
    have hcard :
        ((mixSupport (C.mixWeight l)).card : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hs l
    rw [hBdef]
    nlinarith
  have hK : ∀ l,
      C.ratio l * K + (1 - β l) * B * (2 - C.ratio l) ≤ K := by
    intro l
    have h1 :
        (1 - β l) * B * (2 - C.ratio l) ≤ H * B * 2 := by
      have h2 : (0 : ℝ) ≤ 2 - C.ratio l := by
        linarith [C.ratio_lt_one l]
      nlinarith [hH l, C.ratio_pos l,
        mul_nonneg (by linarith [hβ1 l] : (0 : ℝ) ≤ 1 - β l) hB0]
    have h3 : (1 - a) * K = 2 * H * B := by
      rw [hKdef]
      field_simp
    nlinarith [ha l]
  have hεbound : K + H * B + 2 * M * H ≤ ε := by
    have hsum : K + H * B + 2 * M * H = H * (D - 1) := by
      rw [hKdef, hDdef]
      field_simp
      ring
    rw [hsum]
    nlinarith [hHD]
  refine ⟨N, β, word, hN, hβ0, hβ1, hβN,
    fun n j => rfl, ?_, ?_, ?_⟩
  · exact fun n =>
      isSupportPerfectRow_multi C word β N hN hβ0 hβ1 hβN
        hword M B K H hM0 hM hB0 hdrift hK hH ε hεbound n
  · exact fun n j =>
      multiActual_ge_floor_sub C word β N hN hβ0 hβ1 hβN
        M B K H hM0 hB0 hdrift hK hH ε hεbound n j
  · exact exists_prefix_quitMass_multi_ge
      C word β N hN hβ0 hβN a ha ha1 Q

/-- One compact value carrier, independent of the requested charge target. -/
def multiCirculationFiniteValueCarrier
    (C : FaceCirculationCertificate r floor L) (M : ℝ) :
    Set (Payoff ι) :=
  Set.pi Set.univ fun _ =>
    Set.Icc (-(M + ∑ who, |C.vertex 0 who|))
      (M + ∑ who, |C.vertex 0 who|)

omit [DecidableEq ι] in
theorem isCompact_multiCirculationFiniteValueCarrier
    (C : FaceCirculationCertificate r floor L) (M : ℝ) :
    IsCompact (multiCirculationFiniteValueCarrier C M) := by
  unfold multiCirculationFiniteValueCarrier
  exact isCompact_univ_pi fun _ => isCompact_Icc

/-- The original `∀ Q, ∃ finite orbit` circulation theorem, with its hidden
interval data retained, is a finite forward packet in the common carrier. -/
theorem exists_finiteForwardPacket_of_multiCirculation [Nonempty ι]
    (C : FaceCirculationCertificate r floor L)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M)
    (s : ℕ) (hs : ∀ l, (mixSupport (C.mixWeight l)).card ≤ s)
    (a : ℝ) (ha : ∀ l, C.ratio l ≤ a) (ha1 : a < 1)
    (hpunishmentFloor : ∀ who,
      quittingPunishmentValue (rewardOfWeight r) who ≤ floor who)
    (supportError : ℝ) (hsupportError : 0 < supportError)
    (chargeTarget : ℝ) :
    Nonempty (QuittingFiniteForwardPacket (rewardOfWeight r)
      (multiCirculationFiniteValueCarrier C M)
      supportError chargeTarget) := by
  obtain ⟨N, β, word, hN, hβ0, hβ1, hβN,
      hforwardPolicy, hforwardSupport, hforwardFloor, T, hT⟩ :=
    exists_multiCirculation_finiteOrbitData
      C M hM0 hM s hs a ha ha1
        supportError hsupportError chargeTarget
  let row : ℕ → ι → ℝ := multiRow word β N
  let forward : ℕ → Payoff ι := multiActual C word β N
  have hrow0 : ∀ time who, 0 ≤ row time who := by
    intro time who
    have hinterval := singletonRow_mem_unitInterval
      (1 - β (chainPhase L N time))
      (sub_nonneg.mpr (hβ1 (chainPhase L N time)))
      (by linarith [hβ0 (chainPhase L N time)])
      (word (chainPhase L N time) (chainStep L N time)) who
    simpa [row, multiRow] using hinterval.1
  have hrow1 : ∀ time who, row time who ≤ 1 := by
    intro time who
    have hinterval := singletonRow_mem_unitInterval
      (1 - β (chainPhase L N time))
      (sub_nonneg.mpr (hβ1 (chainPhase L N time)))
      (by linarith [hβ0 (chainPhase L N time)])
      (word (chainPhase L N time) (chainStep L N time)) who
    simpa [row, multiRow] using hinterval.2
  let roots : ℕ → ι → PMF Bool := fun time =>
    rootOfHazard (row time) (hrow0 time) (hrow1 time)
  refine ⟨{
    roots := roots
    value := forward
    horizon := T
    value_mem := ?_
    policy := ?_
    support := ?_
    rational := ?_
    chargeTarget_le := ?_
  }⟩
  · intro time _
    unfold multiCirculationFiniteValueCarrier
    intro who _
    exact abs_le.mp
      (abs_multiActual_le_reward_add_vertex
        C word β N hβ0 hβ1 M hM0 hM time who)
  · intro time _
    calc
      forward (time + 1) =
          oneStageNext r (row time) (forward time) := by
        funext who
        simpa [forward, row] using hforwardPolicy time who
      _ = quittingRootSuccessorPayoff
          (rewardOfWeight r) (forward time) (roots time) := by
        symm
        exact quittingRootSuccessorPayoff_rootOfHazard_eq_oneStageNext
          r (row time) (hrow0 time) (hrow1 time) (forward time)
  · intro time _
    exact isQuittingRootSupportApproxNash_rootOfHazard_of_isSupportPerfectRow
      r (row time) (hrow0 time) (hrow1 time)
        (forward time) supportError
        (by simpa [row, forward] using hforwardSupport time)
  · intro target time _
    have hfloor := hforwardFloor time target
    have hpunishment := hpunishmentFloor target
    dsimp only [forward]
    linarith
  · calc
      chargeTarget ≤
          ∑ time ∈ Finset.range T,
            (1 - continueMass (multiRow word β N time)) := hT
      _ = ∑ time ∈ Finset.range T,
          quittingRootAbsorptionMass (roots time) := by
        apply Finset.sum_congr rfl
        intro time _
        dsimp only [roots]
        rw [quittingRootAbsorptionMass_rootOfHazard]

/-- **Circulation regression for finite charged closing.**  The motivating
multi-owner circulation producer compiles through the new finite packet
interface and no longer needs one orbit that works for every charge target. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_multiCirculation_finiteClosing
    [Nonempty ι]
    (C : FaceCirculationCertificate r floor L)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M)
    (s : ℕ) (hs : ∀ l, (mixSupport (C.mixWeight l)).card ≤ s)
    (a : ℝ) (ha : ∀ l, C.ratio l ≤ a) (ha1 : a < 1)
    (hpunishmentFloor : ∀ who,
      quittingPunishmentValue (rewardOfWeight r) who ≤ floor who) :
    ∃ payoff : Payoff ι,
      (quittingGame (rewardOfWeight r)).IsUniformEquilibriumPayoff
        none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_finiteForwardPackets
    (rewardOfWeight r) (multiCirculationFiniteValueCarrier C M)
      (isCompact_multiCirculationFiniteValueCarrier C M)
  intro supportError hsupportError chargeTarget _
  exact exists_finiteForwardPacket_of_multiCirculation
    C M hM0 hM s hs a ha ha1 hpunishmentFloor
      supportError hsupportError chargeTarget

end GameTheory
