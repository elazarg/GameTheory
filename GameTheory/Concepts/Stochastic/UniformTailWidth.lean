/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.UniformPayoffExistenceClosure

/-!
# A tail-width characterization of uniform-equilibrium payoff existence

A uniform equilibrium must do two things at once: keep prescribed play in a
narrow payoff band and keep every unilateral deviation below the top of that
band.  This file packages that observation without introducing a best-response
supremum or `limsup`/`liminf`.

`HasUniformTailInterval` says that one profile eventually traps prescribed
payoffs above a lower vector and all unilateral behavioral deviations below an
upper vector.  `HasArbitrarilyThinTailIntervals` asks for such intervals of
arbitrarily small coordinatewise width.

The main theorem proves that, for a finite stochastic game, arbitrarily thin
tail intervals are equivalent to existence of a uniform-equilibrium payoff.
The reverse implication passes only the interval midpoints to a convergent
subsequence.  It never passes behavior profiles to a limit.

This is the quantifier-level form of the spectral-width principle: failure of
uniform-equilibrium existence forces a fixed positive tail width for every
behavior profile.
-/

noncomputable section

open Filter

namespace GameTheory
namespace StochasticGame

variable {ι : Type}

/-- A profile has a uniform tail interval `[lower, upper]` when, after one
common horizon threshold, its prescribed payoff is above `lower` and every
unilateral behavioral deviation is below `upper`. -/
def HasUniformTailInterval
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (σ : G.BehaviorProfile)
    (lower upper : Payoff ι) : Prop :=
  ∃ T₀ : ℕ, ∀ T, T₀ ≤ T →
    (∀ who, lower who ≤ G.finiteAveragePayoff s₀ T σ who) ∧
    ∀ who (dev : G.BehaviorStrategy who),
      G.finiteAveragePayoff s₀ T (Function.update σ who dev) who ≤
        upper who

/-- Midpoint of a coordinatewise payoff interval. -/
def tailIntervalMidpoint (lower upper : Payoff ι) : Payoff ι :=
  fun who => (lower who + upper who) / 2

/-- A prescribed payoff trapped in an interval of width at most `δ` is within
`δ` of the interval midpoint.  The deliberately loose constant avoids
unnecessary half-width bookkeeping in downstream uniform estimates. -/
theorem abs_onPath_sub_tailIntervalMidpoint_le
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι]
    {s₀ : G.State} {σ : G.BehaviorProfile} {lower upper : Payoff ι}
    {T : ℕ} {who : ι} {δ : ℝ}
    (hlower : lower who ≤ G.finiteAveragePayoff s₀ T σ who)
    (hupper : G.finiteAveragePayoff s₀ T σ who ≤ upper who)
    (hwidth : upper who - lower who ≤ δ) :
    |G.finiteAveragePayoff s₀ T σ who -
        tailIntervalMidpoint lower upper who| ≤ δ := by
  rw [abs_le]
  dsimp [tailIntervalMidpoint]
  constructor <;> linarith

/-- Every positive width admits one profile and one eventual interval of at
most that coordinatewise width. -/
def HasArbitrarilyThinTailIntervals
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ (σ : G.BehaviorProfile) (lower upper : Payoff ι),
      (∀ who, upper who - lower who ≤ δ) ∧
      G.HasUniformTailInterval s₀ σ lower upper

/-- A uniform-equilibrium payoff supplies arbitrarily thin tail intervals. -/
theorem IsUniformEquilibriumPayoff.hasArbitrarilyThinTailIntervals
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    {s₀ : G.State} {v : Payoff ι}
    (hUE : G.IsUniformEquilibriumPayoff s₀ v) :
    G.HasArbitrarilyThinTailIntervals s₀ := by
  intro δ hδ
  have hthird : 0 < δ / 3 := by linarith
  obtain ⟨σ, T₀, hσ⟩ := hUE (δ / 3) hthird
  let lower : Payoff ι := fun who => v who - δ / 3
  let upper : Payoff ι := fun who => v who + 2 * (δ / 3)
  refine ⟨σ, lower, upper, ?_, ⟨T₀, fun T hT => ?_⟩⟩
  · intro who
    dsimp [lower, upper]
    ring_nf
    exact le_rfl
  · obtain ⟨hNash, hon⟩ := hσ T hT
    constructor
    · intro who
      have hlower := (abs_le.mp (hon who)).1
      dsimp [lower]
      linarith
    · intro who dev
      have hdev := hNash who dev
      have honUpper := (abs_le.mp (hon who)).2
      dsimp [upper]
      linarith

/-- Arbitrarily thin tail intervals produce a uniform-equilibrium payoff.

The midpoint targets live in one compact finite-dimensional cube.  A convergent
subsequence of those targets is selected, while the corresponding behavior
profile is chosen afresh at the requested accuracy. -/
theorem exists_uniformEquilibriumPayoff_of_hasArbitrarilyThinTailIntervals
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State)
    (hthin : G.HasArbitrarilyThinTailIntervals s₀) :
    ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  classical
  let δ : ℕ → ℝ := fun n => (1 : ℝ) / (n + 1)
  have hδpos : ∀ n, 0 < δ n := by
    intro n
    dsimp [δ]
    positivity
  have hδle_one : ∀ n, δ n ≤ 1 := by
    intro n
    dsimp [δ]
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    exact (div_le_one (by positivity)).2 (by simpa using hn)
  choose σ lower upper hwidth htail using fun n => hthin (δ n) (hδpos n)
  let midpoint : ℕ → Payoff ι := fun n => tailIntervalMidpoint (lower n) (upper n)
  obtain ⟨C, hC0, hC⟩ := G.exists_stagePayoff_nonneg_abs_bound
  let K : Set (Payoff ι) :=
    Set.univ.pi (fun _ : ι => Set.Icc (-(C + 1)) (C + 1))
  have hKcompact : IsCompact K :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmidpointK : ∀ n, midpoint n ∈ K := by
    intro n
    obtain ⟨T₀, hT₀⟩ := htail n
    obtain ⟨hlower, hdev⟩ := hT₀ T₀ le_rfl
    rw [Set.mem_univ_pi]
    intro who
    have hupper : G.finiteAveragePayoff s₀ T₀ (σ n) who ≤ upper n who := by
      have h := hdev who ((σ n) who)
      simpa using h
    have havg : |G.finiteAveragePayoff s₀ T₀ (σ n) who| ≤ C :=
      G.abs_finiteAveragePayoff_le hC0 (fun s a => hC s a who)
        s₀ T₀ (σ n)
    have hclose :
        |G.finiteAveragePayoff s₀ T₀ (σ n) who - midpoint n who| ≤ δ n := by
      exact abs_onPath_sub_tailIntervalMidpoint_le
        (hlower who) hupper (hwidth n who)
    rw [Set.mem_Icc]
    have havgBounds := abs_le.mp havg
    have hcloseBounds := abs_le.mp hclose
    constructor <;> linarith [hδle_one n]
  obtain ⟨v, -, φ, hφ, hlim⟩ := hKcompact.tendsto_subseq hmidpointK
  refine ⟨v, ?_⟩
  intro ε hε
  have hquarter : 0 < ε / 4 := by linarith
  have hδlim : Tendsto δ atTop (nhds 0) := by
    simpa [δ] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0))
  have hδsub : Tendsto (δ ∘ φ) atTop (nhds 0) :=
    hδlim.comp hφ.tendsto_atTop
  obtain ⟨Nδ, hNδ⟩ := eventually_atTop.mp
    ((tendsto_order.mp hδsub).2 (ε / 4) hquarter)
  have hEventuallyMidpoint : ∀ᶠ n in atTop,
      ∀ who, |midpoint (φ n) who - v who| ≤ ε / 4 := by
    rw [eventually_all]
    intro who
    obtain ⟨Nm, hNm⟩ := Metric.tendsto_atTop.mp
      ((tendsto_pi_nhds.mp hlim) who) (ε / 4) hquarter
    exact eventually_atTop.mpr ⟨Nm, fun n hn => by
      simpa [Real.dist_eq] using (hNm n hn).le⟩
  obtain ⟨Nm, hNm⟩ := eventually_atTop.mp hEventuallyMidpoint
  let n := max Nδ Nm
  have hδsmall : δ (φ n) ≤ ε / 4 :=
    (hNδ n (Nat.le_max_left Nδ Nm)).le
  have hmidclose : ∀ who, |midpoint (φ n) who - v who| ≤ ε / 4 :=
    hNm n (Nat.le_max_right Nδ Nm)
  obtain ⟨T₀, hT₀⟩ := htail (φ n)
  refine ⟨σ (φ n), T₀, fun T hT => ?_⟩
  obtain ⟨hlower, hdev⟩ := hT₀ T hT
  constructor
  · intro who dev
    have hbaseUpper :
        G.finiteAveragePayoff s₀ T (σ (φ n)) who ≤ upper (φ n) who := by
      have h := hdev who ((σ (φ n)) who)
      simpa using h
    have hdeviate := hdev who dev
    have hw := hwidth (φ n) who
    linarith
  · intro who
    have hbaseUpper :
        G.finiteAveragePayoff s₀ T (σ (φ n)) who ≤ upper (φ n) who := by
      have h := hdev who ((σ (φ n)) who)
      simpa using h
    have hbaseMid :
        |G.finiteAveragePayoff s₀ T (σ (φ n)) who -
          midpoint (φ n) who| ≤ δ (φ n) :=
      abs_onPath_sub_tailIntervalMidpoint_le
        (hlower who) hbaseUpper (hwidth (φ n) who)
    calc
      |G.finiteAveragePayoff s₀ T (σ (φ n)) who - v who|
          ≤ |G.finiteAveragePayoff s₀ T (σ (φ n)) who -
                midpoint (φ n) who| +
              |midpoint (φ n) who - v who| := abs_sub_le _ _ _
      _ ≤ ε / 4 + ε / 4 := add_le_add (hbaseMid.trans hδsmall) (hmidclose who)
      _ ≤ ε := by linarith

/-- Tail-width characterization of uniform-equilibrium payoff existence. -/
theorem exists_uniformEquilibriumPayoff_iff_hasArbitrarilyThinTailIntervals
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) :
    (∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v) ↔
      G.HasArbitrarilyThinTailIntervals s₀ := by
  constructor
  · rintro ⟨v, hv⟩
    exact hv.hasArbitrarilyThinTailIntervals
  · exact G.exists_uniformEquilibriumPayoff_of_hasArbitrarilyThinTailIntervals s₀

end StochasticGame
end GameTheory
