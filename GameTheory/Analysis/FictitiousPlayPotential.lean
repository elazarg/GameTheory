/-
# Fictitious-play convergence in finite exact-potential games

This is the analytic consumer of the topology-free gain, empirical-recurrence,
and Lyapunov spine in `Core.FictitiousPlayPotential`.  Harmonic summability
forces aggregate played gain to vanish; the canonical mixed-improvement
certificate then yields eventual approximate Nash equilibrium.
-/

import GameTheory.Core.FictitiousPlayPotential
import GameTheory.Math.HarmonicSequence

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability Filter GameTheory.Math

universe uι us uo

namespace UtilityGame

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable (G : UtilityGame.{uι, us, uo} ι)

/-- The played-gain sequence has finite harmonic energy along fictitious play
in a bounded exact-potential game. -/
theorem IsExactPotential.summable_harmonic_aggregatePlayedGain
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    {C : ℝ} (hbound : ∀ profile, |potential profile| ≤ C)
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) :
    Summable (fun t : ℕ =>
      (1 / ((t : ℝ) + 2)) * G.aggregatePlayedGain history t) := by
  let value : ℕ → ℝ := fun n =>
    G.form.mixedPotential potential (G.form.empiricalBelief history (n + 1))
  let errorScale : ℝ :=
    ((Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)) * (4 * C)
  let error : ℕ → ℝ := fun t =>
    errorScale * ((1 / ((t : ℝ) + 2)) ^ 2)
  have hC : 0 ≤ C := by
    have hprofile := hbound (history 0)
    exact (abs_nonneg _).trans hprofile
  have herrorNonneg : ∀ t : ℕ, 0 ≤ error t := by
    intro t
    dsimp [error, errorScale]
    positivity
  have herrorSummable : Summable error := by
    have hs0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have hs2 : Summable (fun t : ℕ => 1 / (((t : ℝ) + 2) ^ 2)) := by
      simpa [Nat.cast_add] using (summable_nat_add_iff 2).mpr hs0
    have hs3 : Summable (fun t : ℕ => (1 / ((t : ℝ) + 2)) ^ 2) := by
      simpa [one_div, inv_pow, Nat.cast_add] using hs2
    simpa [error] using hs3.mul_left errorScale
  have htermNonneg : ∀ t : ℕ,
      0 ≤ (1 / ((t : ℝ) + 2)) * G.aggregatePlayedGain history t := by
    intro t
    exact mul_nonneg (by positivity)
      (UtilityGame.IsFictitiousPlay.aggregatePlayedGain_nonneg
        (G := G) hplay t)
  have htelescopes : ∀ n : ℕ,
      (∑ t ∈ Finset.range n, (value (t + 1) - value t)) =
        value n - value 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hpartial : ∀ n : ℕ,
      (∑ t ∈ Finset.range n,
          (1 / ((t : ℝ) + 2)) * G.aggregatePlayedGain history t) ≤
        2 * C + ∑' t, error t := by
    intro n
    have hpoint : ∀ t ∈ Finset.range n,
        (1 / ((t : ℝ) + 2)) * G.aggregatePlayedGain history t ≤
          (value (t + 1) - value t) + error t := by
      intro t _
      have hlyapunov :=
        UtilityGame.IsExactPotential.mixedPotential_empiricalBelief_succ_sub_ge
          (G := G) hpotential hbound history t
      dsimp [value, error, errorScale]
      linarith
    calc
      (∑ t ∈ Finset.range n,
          (1 / ((t : ℝ) + 2)) * G.aggregatePlayedGain history t) ≤
          ∑ t ∈ Finset.range n,
            ((value (t + 1) - value t) + error t) :=
        Finset.sum_le_sum hpoint
      _ = (∑ t ∈ Finset.range n, (value (t + 1) - value t)) +
          ∑ t ∈ Finset.range n, error t := by
        rw [Finset.sum_add_distrib]
      _ = (value n - value 0) + ∑ t ∈ Finset.range n, error t := by
        rw [htelescopes]
      _ ≤ 2 * C + ∑' t, error t := by
        have hvalueN := G.mixedPotential_abs_le_of_abs_bound potential hbound
          (G.form.empiricalBelief history (n + 1))
        have hvalue0 := G.mixedPotential_abs_le_of_abs_bound potential hbound
          (G.form.empiricalBelief history (0 + 1))
        have hvalueDiff : value n - value 0 ≤ 2 * C := by
          dsimp [value] at hvalueN hvalue0 ⊢
          linarith [(abs_le.mp hvalue0).1, (abs_le.mp hvalueN).2]
        have herrorPartial :
            ∑ t ∈ Finset.range n, error t ≤ ∑' t, error t :=
          herrorSummable.sum_le_tsum (Finset.range n)
            (fun t _ => herrorNonneg t)
        linarith
  exact summable_of_sum_range_le htermNonneg hpartial

/-- Aggregate played gain is arbitrarily small along arbitrarily late rounds. -/
theorem IsExactPotential.frequently_aggregatePlayedGain_lt
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    {C : ℝ} (hbound : ∀ profile, |potential profile| ≤ C)
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ t in atTop, G.aggregatePlayedGain history t < ε :=
  GameTheory.Math.frequently_lt_of_summable_one_div_mul
    (UtilityGame.IsExactPotential.summable_harmonic_aggregatePlayedGain
      (G := G) hpotential hbound hplay) hε

/-- Aggregate played gain tends to zero along fictitious play in a bounded
exact-potential game. -/
theorem IsExactPotential.aggregatePlayedGain_tendsto_zero
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    {C : ℝ} (hbound : ∀ profile, |potential profile| ≤ C)
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) :
    Tendsto (fun t : ℕ => G.aggregatePlayedGain history t) atTop (nhds 0) := by
  let K : ℝ :=
    ((Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)) * (4 * C)
  have hC : 0 ≤ C := by
    have hprofile := hbound (history 0)
    exact (abs_nonneg _).trans hprofile
  refine GameTheory.Math.tendsto_zero_of_summable_one_div_mul_of_succ_abs_sub_le
    (fun t => UtilityGame.IsFictitiousPlay.aggregatePlayedGain_nonneg
      (G := G) hplay t)
    (UtilityGame.IsExactPotential.summable_harmonic_aggregatePlayedGain
      (G := G) hpotential hbound hplay)
    (K := K) ?_ ?_
  · dsimp [K]
    positivity
  · intro t
    have hslow :=
      UtilityGame.IsExactPotential.aggregatePlayedGain_succ_abs_sub_le
        (G := G) hpotential hbound hplay t
    dsimp [K]
    convert hslow using 1
    ring_nf

variable [∀ who, Fintype (G.form.sig.Strategy who)]

theorem IsFictitiousPlay.weightedPlayedGain_nonneg
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) :
    0 ≤ G.weightedPlayedGain history t := by
  rw [weightedPlayedGain]
  exact Finset.sum_nonneg fun who _ =>
    mul_nonneg (Nat.cast_nonneg _)
      (UtilityGame.IsFictitiousPlay.playedGain_nonneg (G := G) hplay t who)

/-- The cardinality-weighted played gain is bounded by a fixed strategy-size
constant times aggregate played gain. -/
theorem IsFictitiousPlay.weightedPlayedGain_le_cardSum_mul_aggregate
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) :
    G.weightedPlayedGain history t ≤
      (∑ who : ι, (Fintype.card (G.form.sig.Strategy who) : ℝ)) *
        G.aggregatePlayedGain history t := by
  let cardSum : ℝ :=
    ∑ who : ι, (Fintype.card (G.form.sig.Strategy who) : ℝ)
  have hcard : ∀ who : ι,
      (Fintype.card (G.form.sig.Strategy who) : ℝ) ≤ cardSum := by
    intro who
    dsimp [cardSum]
    exact Finset.single_le_sum
      (fun player _ => Nat.cast_nonneg
        (Fintype.card (G.form.sig.Strategy player)))
      (Finset.mem_univ who)
  rw [weightedPlayedGain, aggregatePlayedGain]
  calc
    (∑ who : ι, (Fintype.card (G.form.sig.Strategy who) : ℝ) *
        G.playedGain history t who) ≤
        ∑ who : ι, cardSum * G.playedGain history t who := by
      refine Finset.sum_le_sum fun who _ => ?_
      exact mul_le_mul_of_nonneg_right (hcard who)
        (UtilityGame.IsFictitiousPlay.playedGain_nonneg (G := G) hplay t who)
    _ = cardSum * ∑ who : ι, G.playedGain history t who := by
      rw [Finset.mul_sum]

/-- Cardinality-weighted played gain also tends to zero. -/
theorem IsExactPotential.weightedPlayedGain_tendsto_zero
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    {C : ℝ} (hbound : ∀ profile, |potential profile| ≤ C)
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) :
    Tendsto (fun t : ℕ => G.weightedPlayedGain history t) atTop (nhds 0) := by
  let cardSum : ℝ :=
    ∑ who : ι, (Fintype.card (G.form.sig.Strategy who) : ℝ)
  have hplayed :
      Tendsto (fun t : ℕ => G.aggregatePlayedGain history t) atTop (nhds 0) :=
    UtilityGame.IsExactPotential.aggregatePlayedGain_tendsto_zero
      (G := G) hpotential hbound hplay
  have hupper : ∀ t : ℕ,
      G.weightedPlayedGain history t ≤
        cardSum * G.aggregatePlayedGain history t := by
    intro t
    simpa [cardSum] using
      UtilityGame.IsFictitiousPlay.weightedPlayedGain_le_cardSum_mul_aggregate
        (G := G) hplay t
  have hscaled :
      Tendsto (fun t : ℕ => cardSum * G.aggregatePlayedGain history t)
        atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hplayed :
      Tendsto (fun t : ℕ => cardSum * G.aggregatePlayedGain history t)
        atTop (nhds (cardSum * 0)))
  exact squeeze_zero
    (fun t => UtilityGame.IsFictitiousPlay.weightedPlayedGain_nonneg
      (G := G) hplay t)
    hupper hscaled

/-- The aggregate mixed-improvement certificate of empirical beliefs tends to
zero under bounded exact-potential fictitious play. -/
theorem IsExactPotential.mixedImprovement_empiricalBelief_tendsto_zero_of_abs_bound
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    {C : ℝ} (hbound : ∀ profile, |potential profile| ≤ C)
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) :
    Tendsto (fun t : ℕ =>
      G.mixedImprovement (G.form.empiricalBelief history (t + 1))) atTop (nhds 0) := by
  have hweighted := UtilityGame.IsExactPotential.weightedPlayedGain_tendsto_zero
    (G := G) hpotential hbound hplay
  exact squeeze_zero
    (fun t => G.mixedImprovement_nonneg
      (G.form.empiricalBelief history (t + 1)))
    (fun t =>
      UtilityGame.IsFictitiousPlay.mixedImprovement_le_weightedPlayedGain
        (G := G) hplay t)
    hweighted

/-- Finite pure-profile boundedness discharges the explicit-bound version. -/
theorem IsExactPotential.mixedImprovement_empiricalBelief_tendsto_zero
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) :
    Tendsto (fun t : ℕ =>
      G.mixedImprovement (G.form.empiricalBelief history (t + 1))) atTop (nhds 0) := by
  obtain ⟨C, hbound⟩ := G.exists_profile_abs_bound potential
  exact UtilityGame.IsExactPotential.mixedImprovement_empiricalBelief_tendsto_zero_of_abs_bound
      (G := G) hpotential hbound hplay

/-- A vanishing aggregate positive pure-deviation gap eventually certifies
every positive-error approximate mixed Nash condition. -/
theorem eventually_isεNash_of_mixedImprovement_tendsto_zero
    {mixedProfiles : ℕ → Profile G.form.sig.mixed}
    (hconverges : Tendsto (fun t => G.mixedImprovement (mixedProfiles t))
      atTop (nhds 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, IsεNash G.form.mixed G.utility ε (mixedProfiles t) := by
  have hsmall : ∀ᶠ t in atTop, G.mixedImprovement (mixedProfiles t) < ε :=
    hconverges.eventually (eventually_lt_nhds hε)
  filter_upwards [hsmall] with t ht
  exact G.isεNash_of_mixedImprovement_le (le_of_lt ht)

/-- Bounded exact-potential fictitious play is eventually approximate Nash. -/
theorem IsExactPotential.eventually_isεNash_of_isFictitiousPlay_of_abs_bound
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    {C : ℝ} (hbound : ∀ profile, |potential profile| ≤ C)
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop,
      IsεNash G.form.mixed G.utility ε
        (G.form.empiricalBelief history (t + 1)) :=
  G.eventually_isεNash_of_mixedImprovement_tendsto_zero
    (UtilityGame.IsExactPotential.mixedImprovement_empiricalBelief_tendsto_zero_of_abs_bound
        (G := G) hpotential hbound hplay) hε

/-- **Finite Monderer-Shapley convergence.** Along fictitious play in a finite
exact-potential game, empirical beliefs are eventually ε-Nash for every
positive ε. -/
theorem IsExactPotential.eventually_isεNash_of_isFictitiousPlay
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop,
      IsεNash G.form.mixed G.utility ε
        (G.form.empiricalBelief history (t + 1)) :=
  G.eventually_isεNash_of_mixedImprovement_tendsto_zero
    (UtilityGame.IsExactPotential.mixedImprovement_empiricalBelief_tendsto_zero
      (G := G) hpotential hplay) hε

/-- Any fictitious-play process whose weighted played gain vanishes is
eventually approximate mixed Nash. -/
theorem IsFictitiousPlay.eventually_isεNash_of_weightedPlayedGain_tendsto_zero
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history)
    (hgain : Tendsto (fun t : ℕ => G.weightedPlayedGain history t)
      atTop (nhds 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop,
      IsεNash G.form.mixed G.utility ε
        (G.form.empiricalBelief history (t + 1)) := by
  have himprovement :
      Tendsto (fun t : ℕ =>
        G.mixedImprovement (G.form.empiricalBelief history (t + 1)))
        atTop (nhds 0) :=
    squeeze_zero
      (fun t => G.mixedImprovement_nonneg
        (G.form.empiricalBelief history (t + 1)))
      (fun t => UtilityGame.IsFictitiousPlay.mixedImprovement_le_weightedPlayedGain
        (G := G) hplay t)
      hgain
  exact G.eventually_isεNash_of_mixedImprovement_tendsto_zero
    himprovement hε

end UtilityGame

end GameTheory
