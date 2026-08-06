/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPSCompactFixedPointLive
import Mathlib.Topology.Order.Compact

/-!
# Uniform upper bounds on terminal-free essential-APS hazards

A proper APS witness only states `p < 1` pointwise.  For nonperiodic mesh
subdivision one needs one ceiling `pStar < 1` along the whole infinite run.
Compactness and terminal-freeness provide it.

For an owner `i`, measure the distance from the singleton root `R_i` by the
sum of the coordinatewise absolute gaps.  This continuous function is
strictly positive on a terminal-free greatest fiber: a zero is exactly
`R_i`, and greatest-family membership supplies viability, making that point a
terminal APS endpoint.  Compactness gives a positive minimum, and finiteness
of the player set gives one minimum for all owners.

Along an arc `v = p R_i + (1-p) w`, the root gap of `v` is at most
`(1-p)` times a common bound on the root gap of `w`.  The positive compact
minimum therefore forces `1-p` uniformly positive.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Coordinatewise `ℓ¹` gap from the active owner's singleton root. -/
def quittingEssentialAPSSoloGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (current : Payoff ι) : ℝ :=
  ∑ who, |current who - quittingSoloReward reward owner who|

/-- The singleton-root gap is continuous in the current payoff. -/
theorem continuous_quittingEssentialAPSSoloGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) :
    Continuous (quittingEssentialAPSSoloGap reward owner) := by
  unfold quittingEssentialAPSSoloGap
  fun_prop

/-- The singleton-root gap is nonnegative. -/
theorem quittingEssentialAPSSoloGap_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (current : Payoff ι) :
    0 ≤ quittingEssentialAPSSoloGap reward owner current := by
  unfold quittingEssentialAPSSoloGap
  exact Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)

/-- The gap vanishes exactly at the active singleton reward vector. -/
theorem quittingEssentialAPSSoloGap_eq_zero_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (current : Payoff ι) :
    quittingEssentialAPSSoloGap reward owner current = 0 ↔
      current = quittingSoloReward reward owner := by
  constructor
  · intro hzero
    funext who
    unfold quittingEssentialAPSSoloGap at hzero
    have hall :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun player (_ : player ∈ (Finset.univ : Finset ι)) ↦
          abs_nonneg
            (current player - quittingSoloReward reward owner player))).1
        hzero
    have hwho := hall who (Finset.mem_univ who)
    exact sub_eq_zero.mp (abs_eq_zero.mp hwho)
  · rintro rfl
    simp [quittingEssentialAPSSoloGap]

/-- Greatest-family membership always supplies individual viability. -/
theorem quittingEssentialAPSGreatestFamily_viable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    {owner : ι} {current : Payoff ι}
    (hcurrent : current ∈
      quittingEssentialAPSGreatestFamily reward carrier owner) :
    QuittingEssentialAPSViable reward current := by
  have hfixedOwner := congrFun
    (quittingEssentialAPSGreatestFamily_fixed reward carrier) owner
  have hrestricted : current ∈
      quittingEssentialAPSRestrictedOperator reward carrier
        (quittingEssentialAPSGreatestFamily reward carrier) owner := by
    rw [hfixedOwner]
    exact hcurrent
  rcases hrestricted.2 with hterminal | hprefix
  · exact hterminal.2
  · exact hprefix.1

/-- On a terminal-free greatest fiber, the singleton-root gap is positive. -/
theorem quittingEssentialAPSSoloGap_pos_of_terminalFree
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    {owner : ι} {current : Payoff ι}
    (hcurrent : current ∈
      quittingEssentialAPSGreatestFamily reward carrier owner)
    (hterminalFree : current ∉
      quittingEssentialAPSTerminal reward owner) :
    0 < quittingEssentialAPSSoloGap reward owner current := by
  have hnonneg := quittingEssentialAPSSoloGap_nonneg reward owner current
  have hne : quittingEssentialAPSSoloGap reward owner current ≠ 0 := by
    intro hzero
    have hroot :=
      (quittingEssentialAPSSoloGap_eq_zero_iff reward owner current).1 hzero
    apply hterminalFree
    exact ⟨hroot,
      quittingEssentialAPSGreatestFamily_viable reward carrier hcurrent⟩
  exact lt_of_le_of_ne hnonneg hne.symm

/-- Compact separation from one owner's viable singleton endpoint. -/
theorem exists_uniform_quittingEssentialAPSSoloGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι)) (owner : ι)
    (hcompact : IsCompact
      (quittingEssentialAPSGreatestFamily reward carrier owner))
    (hnonempty :
      (quittingEssentialAPSGreatestFamily reward carrier owner).Nonempty)
    (hterminalFree : ∀ current,
      current ∈ quittingEssentialAPSGreatestFamily reward carrier owner →
        current ∉ quittingEssentialAPSTerminal reward owner) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ current,
        current ∈ quittingEssentialAPSGreatestFamily reward carrier owner →
          delta ≤ quittingEssentialAPSSoloGap reward owner current := by
  obtain ⟨minimizer, hminimizer, _hsInf, hminimal⟩ :=
    hcompact.exists_sInf_image_eq_and_le hnonempty
      (continuous_quittingEssentialAPSSoloGap reward owner).continuousOn
  refine ⟨quittingEssentialAPSSoloGap reward owner minimizer, ?_, ?_⟩
  · exact quittingEssentialAPSSoloGap_pos_of_terminalFree
      reward carrier hminimizer (hterminalFree minimizer hminimizer)
  · intro current hcurrent
    exact hminimal current hcurrent

/-- One positive singleton-root separation works for every greatest fiber.
Empty fibers receive an arbitrary positive local constant and never contribute
a point to the conclusion. -/
theorem exists_uniform_quittingEssentialAPSSoloGap_all_players
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcompact : ∀ player, IsCompact
      (quittingEssentialAPSGreatestFamily reward carrier player))
    (hterminalFree : ∀ player current,
      current ∈ quittingEssentialAPSGreatestFamily reward carrier player →
        current ∉ quittingEssentialAPSTerminal reward player)
    (base : ι) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ player current,
        current ∈ quittingEssentialAPSGreatestFamily reward carrier player →
          delta ≤ quittingEssentialAPSSoloGap reward player current := by
  classical
  have hlocal : ∀ player, ∃ delta : ℝ, 0 < delta ∧
      ∀ current,
        current ∈ quittingEssentialAPSGreatestFamily reward carrier player →
          delta ≤ quittingEssentialAPSSoloGap reward player current := by
    intro player
    by_cases hnonempty :
        (quittingEssentialAPSGreatestFamily reward carrier player).Nonempty
    · exact exists_uniform_quittingEssentialAPSSoloGap
        reward carrier player (hcompact player) hnonempty
          (hterminalFree player)
    · refine ⟨1, zero_lt_one, ?_⟩
      intro current hcurrent
      exact False.elim (hnonempty ⟨current, hcurrent⟩)
  choose localDelta hlocalDeltaPos hlocalBound using hlocal
  have hdeltaCompact : IsCompact (Set.range localDelta) :=
    (Set.finite_range localDelta).isCompact
  have hdeltaNonempty : (Set.range localDelta).Nonempty :=
    ⟨localDelta base, ⟨base, rfl⟩⟩
  obtain ⟨_minimum, ⟨minPlayer, rfl⟩, hminimum⟩ :=
    hdeltaCompact.exists_isLeast hdeltaNonempty
  have hminimumPlayer : ∀ player,
      localDelta minPlayer ≤ localDelta player := by
    intro player
    exact hminimum ⟨player, rfl⟩
  refine ⟨localDelta minPlayer, hlocalDeltaPos minPlayer, ?_⟩
  intro player current hcurrent
  exact (hminimumPlayer player).trans
    (hlocalBound player current hcurrent)

/-- A bounded singleton arc has root gap at most its Continue probability
multiplied by the common coordinatewise diameter bound. -/
theorem quittingEssentialAPSSoloGap_le_continue_mul_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {p bound : ℝ} {current next : Payoff ι}
    (hp1 : p ≤ 1)
    (harc : current = quittingSingletonArcPayoff p
      (quittingSoloReward reward owner) next)
    (hrootBound : ∀ who,
      |quittingSoloReward reward owner who| ≤ bound)
    (hnextBound : ∀ who, |next who| ≤ bound) :
    quittingEssentialAPSSoloGap reward owner current ≤
      (1 - p) * ((Fintype.card ι : ℝ) * (2 * bound)) := by
  unfold quittingEssentialAPSSoloGap
  calc
    (∑ who,
        |current who - quittingSoloReward reward owner who|) ≤
      ∑ _who : ι, (1 - p) * (2 * bound) := by
        apply Finset.sum_le_sum
        intro who _
        have harcWho := congrFun harc who
        have hrewrite :
            current who - quittingSoloReward reward owner who =
              (1 - p) *
                (next who - quittingSoloReward reward owner who) := by
          rw [harcWho]
          simp only [quittingSingletonArcPayoff]
          ring
        rw [hrewrite, abs_mul, abs_of_nonneg (sub_nonneg.mpr hp1)]
        apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hp1)
        calc
          |next who - quittingSoloReward reward owner who| ≤
              |next who| + |quittingSoloReward reward owner who| :=
            abs_sub _ _
          _ ≤ bound + bound := add_le_add
            (hnextBound who) (hrootBound who)
          _ = 2 * bound := by ring
    _ = (1 - p) * ((Fintype.card ι : ℝ) * (2 * bound)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- **Uniform terminal-free hazard ceiling.**  Along any bounded APS arc path
inside compact terminal-free greatest fibers, all coarse hazards lie below one
common `pStar < 1`. -/
theorem exists_uniform_quittingEssentialAPSHazardCeiling
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hgreatestCompact : ∀ player, IsCompact
      (quittingEssentialAPSGreatestFamily reward carrier player))
    (hterminalFree : ∀ player current,
      current ∈ quittingEssentialAPSGreatestFamily reward carrier player →
        current ∉ quittingEssentialAPSTerminal reward player)
    {bound : ℝ} (hbound : 0 < bound)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (hvalueMem : ∀ time,
      value time ∈
        quittingEssentialAPSGreatestFamily reward carrier (owner time))
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hrootBound : ∀ quitter who,
      |quittingSoloReward reward quitter who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound) :
    ∃ pStar : ℝ, 0 ≤ pStar ∧ pStar < 1 ∧
      ∀ time, mass time ≤ pStar := by
  obtain ⟨delta, hdeltaPos, hdelta⟩ :=
    exists_uniform_quittingEssentialAPSSoloGap_all_players
      reward carrier hgreatestCompact hterminalFree (owner 0)
  let coefficient : ℝ := (Fintype.card ι : ℝ) * (2 * bound)
  have hcard : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr ⟨owner 0⟩
  have hcoefficientPos : 0 < coefficient := by
    dsimp only [coefficient]
    positivity
  let pStar : ℝ := 1 - delta / coefficient
  have hmassLe : ∀ time, mass time ≤ pStar := by
    intro time
    have hgapLower := hdelta (owner time) (value time) (hvalueMem time)
    have hgapUpper :=
      quittingEssentialAPSSoloGap_le_continue_mul_bound
        reward (owner time) (hmass1 time) (harc time)
          (hrootBound (owner time)) (hvalueBound (time + 1))
    have hscaled : delta ≤ (1 - mass time) * coefficient :=
      hgapLower.trans (by
        simpa only [coefficient] using hgapUpper)
    have hcontinue : delta / coefficient ≤ 1 - mass time :=
      (div_le_iff₀ hcoefficientPos).2 (by
        simpa only [mul_comm] using hscaled)
    dsimp only [pStar]
    linarith
  have hpStar0 : 0 ≤ pStar :=
    (hmass0 0).trans (hmassLe 0)
  have hpStar1 : pStar < 1 := by
    dsimp only [pStar]
    exact sub_lt_self _ (div_pos hdeltaPos hcoefficientPos)
  exact ⟨pStar, hpStar0, hpStar1, hmassLe⟩

/-- Carrier-level form: compact convex carriers and unique live successors
supply the compact greatest fibers used by the hazard-ceiling theorem. -/
theorem exists_uniform_quittingEssentialAPSHazardCeiling_unique_live
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrierCompact : ∀ player, IsCompact (carrier player))
    (hcarrierConvex : ∀ player, Convex ℝ (carrier player))
    (successor : ι → ι)
    (hedge : ∀ player,
      QuittingFleschSuccessor reward player (successor player))
    (huniqueLive : ∀ player candidate,
      QuittingFleschSuccessor reward player candidate →
        candidate ≠ successor player →
          quittingEssentialAPSGreatestFamily reward carrier candidate = ∅)
    (hterminalFree : ∀ player current,
      current ∈ quittingEssentialAPSGreatestFamily reward carrier player →
        current ∉ quittingEssentialAPSTerminal reward player)
    {bound : ℝ} (hbound : 0 < bound)
    (owner : ℕ → ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    (hvalueMem : ∀ time,
      value time ∈
        quittingEssentialAPSGreatestFamily reward carrier (owner time))
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hrootBound : ∀ quitter who,
      |quittingSoloReward reward quitter who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound) :
    ∃ pStar : ℝ, 0 ≤ pStar ∧ pStar < 1 ∧
      ∀ time, mass time ≤ pStar := by
  exact exists_uniform_quittingEssentialAPSHazardCeiling
    reward carrier
    (fun player ↦
      isCompact_quittingEssentialAPSGreatestFamily_of_compact_convex_unique_live
        reward carrier hcarrierCompact hcarrierConvex successor hedge
          huniqueLive player)
    hterminalFree hbound owner mass value hvalueMem hmass0 hmass1 harc
      hrootBound hvalueBound

end GameTheory
