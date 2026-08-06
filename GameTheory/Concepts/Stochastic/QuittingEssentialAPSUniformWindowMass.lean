/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingEssentialAPSCompactFixedPoint
import Mathlib.Topology.Order.Compact

/-!
# Uniform positive absorption mass on finite essential-APS windows

The qualitative circuit-progress theorem says that a chain of zero-mass
unique-successor APS steps can persist only when one unchanged payoff lies on
every active hyperplane in the window.  Compactness upgrades this pointwise
statement to a quantitative one.

For a payoff `current`, define its finite active-face gap as the sum of the
absolute discrepancies from all active hyperplanes visited in the window.  On
a compact set avoiding their common intersection, this continuous gap has a
strictly positive minimum `delta`.

Along a singleton-flow arc

`value t = p_t * root_t + (1-p_t) * value (t+1)`,

the displacement in one step is at most `2 * bound * p_t` when roots and path
values are uniformly bounded by `bound`.  Telescoping therefore controls every
active-face gap of `value 0` by the cumulative mass `sum p_t`.  Combining the
telescoping estimate with the compact positive minimum produces one constant
`nu > 0` which works for every admissible arc path.

This is the quantitative `nu`-lemma used in the simple-circuit argument: every
window carries uniformly positive total absorption mass.  It is stated for the
unique-successor singleton-flow stratum and does not assert the general
quitting-game existence theorem.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type}

/-- Sum of the absolute gaps from the active hyperplanes visited through the
specified finite horizon. -/
def quittingEssentialAPSActiveGapSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (horizon : ℕ) (current : Payoff ι) : ℝ :=
  ∑ time in Finset.range (horizon + 1),
    |current (owner time) -
      quittingSoloReward reward (owner time) (owner time)|

/-- The finite active-face gap is continuous in the payoff vector. -/
theorem continuous_quittingEssentialAPSActiveGapSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (horizon : ℕ) :
    Continuous (quittingEssentialAPSActiveGapSum reward owner horizon) := by
  unfold quittingEssentialAPSActiveGapSum
  fun_prop

/-- The finite active-face gap is nonnegative. -/
theorem quittingEssentialAPSActiveGapSum_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (horizon : ℕ) (current : Payoff ι) :
    0 ≤ quittingEssentialAPSActiveGapSum reward owner horizon current := by
  unfold quittingEssentialAPSActiveGapSum
  exact Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)

/-- Vanishing finite active-face gap is equivalent to simultaneous membership
in every active hyperplane in the window. -/
theorem quittingEssentialAPSActiveGapSum_eq_zero_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (horizon : ℕ) (current : Payoff ι) :
    quittingEssentialAPSActiveGapSum reward owner horizon current = 0 ↔
      IsQuittingEssentialAPSActiveAlong reward owner current horizon := by
  constructor
  · intro hzero time htime
    have htermZero :
        |current (owner time) -
          quittingSoloReward reward (owner time) (owner time)| = 0 := by
      have hall :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun index (_ : index ∈ Finset.range (horizon + 1)) ↦
            abs_nonneg
              (current (owner index) -
                quittingSoloReward reward (owner index) (owner index)))).1
          hzero
      apply hall time
      exact Finset.mem_range.mpr (by omega)
    exact sub_eq_zero.mp (abs_eq_zero.mp htermZero)
  · intro hactive
    unfold quittingEssentialAPSActiveGapSum
    apply Finset.sum_eq_zero
    intro time htime
    have hle : time ≤ horizon := by
      have hlt := Finset.mem_range.mp htime
      omega
    rw [hactive time hle, sub_self, abs_zero]

/-- Excluding simultaneous active-face membership makes the finite gap
strictly positive. -/
theorem quittingEssentialAPSActiveGapSum_pos_of_not_activeAlong
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (horizon : ℕ) (current : Payoff ι)
    (hnot : ¬ IsQuittingEssentialAPSActiveAlong
      reward owner current horizon) :
    0 < quittingEssentialAPSActiveGapSum reward owner horizon current := by
  have hnonneg :=
    quittingEssentialAPSActiveGapSum_nonneg
      reward owner horizon current
  have hne :
      quittingEssentialAPSActiveGapSum reward owner horizon current ≠ 0 := by
    intro hzero
    exact hnot ((quittingEssentialAPSActiveGapSum_eq_zero_iff
      reward owner horizon current).1 hzero)
  exact lt_of_le_of_ne hnonneg hne.symm

/-- **Compact active-face separation.**  A compact nonempty payoff set which
avoids the common active face has a uniform strictly positive active-gap
margin. -/
theorem exists_uniform_quittingEssentialAPSActiveGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (horizon : ℕ)
    {E : Set (Payoff ι)}
    (hEcompact : IsCompact E) (hEnonempty : E.Nonempty)
    (havoid : ∀ current, current ∈ E →
      ¬ IsQuittingEssentialAPSActiveAlong
        reward owner current horizon) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ current, current ∈ E →
        delta ≤ quittingEssentialAPSActiveGapSum
          reward owner horizon current := by
  obtain ⟨minimizer, hminimizer, _hsInf, hminimal⟩ :=
    hEcompact.exists_sInf_image_eq_and_le hEnonempty
      (continuous_quittingEssentialAPSActiveGapSum
        reward owner horizon).continuousOn
  refine ⟨quittingEssentialAPSActiveGapSum
      reward owner horizon minimizer, ?_, ?_⟩
  · exact quittingEssentialAPSActiveGapSum_pos_of_not_activeAlong
      reward owner horizon minimizer (havoid minimizer hminimizer)
  · intro current hcurrent
    exact hminimal current hcurrent

/-- One singleton-flow arc step moves any coordinate by at most the absorption
mass times twice a common absolute bound on the root and continuation value. -/
theorem abs_quittingSingletonArc_step_le_mass_mul_bound
    {p bound : ℝ} {root next current : Payoff ι}
    (hp : 0 ≤ p)
    (harc : current = quittingSingletonArcPayoff p root next)
    (who : ι)
    (hrootBound : |root who| ≤ bound)
    (hnextBound : |next who| ≤ bound) :
    |current who - next who| ≤ p * (2 * bound) := by
  have harcWho := congrFun harc who
  rw [harcWho]
  simp only [quittingSingletonArcPayoff]
  have hrewrite :
      p * root who + (1 - p) * next who - next who =
        p * (root who - next who) := by ring
  rw [hrewrite, abs_mul, abs_of_nonneg hp]
  apply mul_le_mul_of_nonneg_left _ hp
  calc
    |root who - next who| ≤ |root who| + |next who| := abs_sub _ _
    _ ≤ bound + bound := add_le_add hrootBound hnextBound
    _ = 2 * bound := by ring

/-- Telescoping a bounded singleton-flow arc path controls displacement from
its initial payoff by cumulative absorption mass. -/
theorem abs_quittingSingletonArcPath_sub_le_massSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (mass : ℕ → ℝ)
    (value : ℕ → Payoff ι) {bound : ℝ}
    (hmass : ∀ time, 0 ≤ mass time)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time))
        (value (time + 1)))
    (hrootBound : ∀ time who,
      |quittingSoloReward reward (owner time) who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound) :
    ∀ time who,
      |value 0 who - value time who| ≤
        (∑ step in Finset.range time, mass step) * (2 * bound) := by
  intro time
  induction time with
  | zero =>
      intro who
      simp
  | succ time ih =>
      intro who
      have hstep :=
        abs_quittingSingletonArc_step_le_mass_mul_bound
          (hmass time) (harc time) who
          (hrootBound time who) (hvalueBound (time + 1) who)
      have hsplit :
          value 0 who - value (time + 1) who =
            (value 0 who - value time who) +
              (value time who - value (time + 1) who) := by ring
      rw [hsplit]
      calc
        |(value 0 who - value time who) +
            (value time who - value (time + 1) who)| ≤
            |value 0 who - value time who| +
              |value time who - value (time + 1) who| := abs_add _ _
        _ ≤ (∑ step in Finset.range time, mass step) * (2 * bound) +
              mass time * (2 * bound) := add_le_add (ih who) hstep
        _ = (∑ step in Finset.range (time + 1), mass step) *
              (2 * bound) := by
          rw [Finset.sum_range_succ]
          ring

/-- Prefix sums of nonnegative masses are monotone in the time horizon. -/
theorem sum_range_mono_of_nonneg
    (mass : ℕ → ℝ) (hmass : ∀ time, 0 ≤ mass time)
    {first last : ℕ} (hle : first ≤ last) :
    (∑ time in Finset.range first, mass time) ≤
      ∑ time in Finset.range last, mass time := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono hle)
    (fun time _ _ ↦ hmass time)

/-- The initial active-face gap of any bounded active singleton-flow path is
controlled by its total absorption mass in the window. -/
theorem quittingEssentialAPSActiveGapSum_le_windowMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (horizon : ℕ)
    (mass : ℕ → ℝ) (value : ℕ → Payoff ι) {bound : ℝ}
    (hbound : 0 ≤ bound)
    (hmass : ∀ time, 0 ≤ mass time)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time))
        (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hrootBound : ∀ time who,
      |quittingSoloReward reward (owner time) who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound) :
    quittingEssentialAPSActiveGapSum reward owner horizon (value 0) ≤
      (((horizon + 1 : ℕ) : ℝ) * (2 * bound)) *
        (∑ time in Finset.range horizon, mass time) := by
  unfold quittingEssentialAPSActiveGapSum
  calc
    (∑ time in Finset.range (horizon + 1),
        |value 0 (owner time) -
          quittingSoloReward reward (owner time) (owner time)|) ≤
      ∑ _time in Finset.range (horizon + 1),
        (2 * bound) *
          (∑ step in Finset.range horizon, mass step) := by
      apply Finset.sum_le_sum
      intro time htime
      have htimeLe : time ≤ horizon := by
        have htimeLt := Finset.mem_range.mp htime
        omega
      have htelescope :=
        abs_quittingSingletonArcPath_sub_le_massSum
          reward owner mass value hmass harc hrootBound hvalueBound
          time (owner time)
      rw [hactive time] at htelescope
      have hprefix := sum_range_mono_of_nonneg
        mass hmass htimeLe
      have hscale :
          (∑ step in Finset.range time, mass step) * (2 * bound) ≤
            (∑ step in Finset.range horizon, mass step) *
              (2 * bound) :=
        mul_le_mul_of_nonneg_right hprefix (by linarith)
      calc
        |value 0 (owner time) -
            quittingSoloReward reward (owner time) (owner time)| ≤
          (∑ step in Finset.range time, mass step) *
            (2 * bound) := htelescope
        _ ≤ (∑ step in Finset.range horizon, mass step) *
            (2 * bound) := hscale
        _ = (2 * bound) *
            (∑ step in Finset.range horizon, mass step) := by ring
    _ = (((horizon + 1 : ℕ) : ℝ) * (2 * bound)) *
        (∑ time in Finset.range horizon, mass time) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- **Uniform positive finite-window absorption mass.**  On compact convex
carriers with a unique exact successor at every owner, common-active-face
avoidance supplies one positive lower bound on the cumulative mass of every
bounded active singleton-flow path starting in the greatest APS family. -/
theorem exists_uniform_quittingEssentialAPS_windowMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (carrier : ι → Set (Payoff ι))
    (hcarrierCompact : ∀ player, IsCompact (carrier player))
    (hcarrierConvex : ∀ player, Convex ℝ (carrier player))
    (successor : ι → ι)
    (hedge : ∀ player,
      QuittingFleschSuccessor reward player (successor player))
    (hunique : ∀ player candidate,
      QuittingFleschSuccessor reward player candidate →
        candidate = successor player)
    (owner : ℕ → ι) (horizon : ℕ)
    (hgreatestNonempty :
      (quittingEssentialAPSGreatestFamily reward carrier (owner 0)).Nonempty)
    (hfaceAvoidance : ∀ current,
      current ∈ carrier (owner 0) →
        ¬ IsQuittingEssentialAPSActiveAlong
          reward owner current horizon)
    {bound : ℝ} (hbound : 0 < bound)
    (hrootBound : ∀ time who,
      |quittingSoloReward reward (owner time) who| ≤ bound) :
    ∃ nu : ℝ, 0 < nu ∧
      ∀ (mass : ℕ → ℝ) (value : ℕ → Payoff ι),
        value 0 ∈
            quittingEssentialAPSGreatestFamily reward carrier (owner 0) →
        (∀ time, 0 ≤ mass time) →
        (∀ time,
          value time = quittingSingletonArcPayoff (mass time)
            (quittingSoloReward reward (owner time))
            (value (time + 1))) →
        (∀ time,
          value time (owner time) =
            quittingSoloReward reward (owner time) (owner time)) →
        (∀ time who, |value time who| ≤ bound) →
        nu ≤ ∑ time in Finset.range horizon, mass time := by
  let greatest :=
    quittingEssentialAPSGreatestFamily reward carrier
  have hgreatestCompact : IsCompact (greatest (owner 0)) :=
    isCompact_quittingEssentialAPSGreatestFamily_of_compact_convex_unique
      reward carrier hcarrierCompact hcarrierConvex
      successor hedge hunique (owner 0)
  have hgreatestAvoids : ∀ current, current ∈ greatest (owner 0) →
      ¬ IsQuittingEssentialAPSActiveAlong
        reward owner current horizon := by
    intro current hcurrent
    have hwithin :=
      quittingEssentialAPSGreatestFamily_subinvariant
        reward carrier (owner 0) hcurrent
    exact hfaceAvoidance current hwithin.1
  obtain ⟨delta, hdeltaPos, hdeltaLower⟩ :=
    exists_uniform_quittingEssentialAPSActiveGap
      reward owner horizon hgreatestCompact hgreatestNonempty
        hgreatestAvoids
  let coefficient : ℝ :=
    ((horizon + 1 : ℕ) : ℝ) * (2 * bound)
  have hcoefficientPos : 0 < coefficient := by
    dsimp only [coefficient]
    positivity
  refine ⟨delta / coefficient,
    div_pos hdeltaPos hcoefficientPos, ?_⟩
  intro mass value hvalue0 hmass harc hactive hvalueBound
  have hdeltaLe := hdeltaLower (value 0) hvalue0
  have hgapLe :=
    quittingEssentialAPSActiveGapSum_le_windowMass
      reward owner horizon mass value hbound.le hmass harc hactive
        hrootBound hvalueBound
  have hscaled :
      delta ≤ coefficient *
        (∑ time in Finset.range horizon, mass time) := by
    exact hdeltaLe.trans (by
      simpa only [coefficient] using hgapLe)
  exact (div_le_iff₀ hcoefficientPos).2 hscaled

end GameTheory
