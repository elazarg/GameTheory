/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Basic
import GameTheory.Concepts.Equilibrium.ApproximateNash

/-!
# Uniform Equilibrium in Stochastic Games

Uniform solution concepts for stochastic games under finite-horizon average
payoffs, and the statement of the **uniform equilibrium existence problem**:
every stochastic game with finitely many players, finitely many states, and
finitely many actions admits a uniform equilibrium payoff from every initial
state.

A behavior profile is a *uniform ε-equilibrium* if a single horizon threshold
`T₀`, depending only on `ε`, makes it an ε-Nash equilibrium of every game
with horizon at least `T₀`.  A payoff vector `v` is a *uniform equilibrium
payoff* if for every `ε > 0` some profile is a uniform ε-equilibrium whose
long finite-horizon average payoffs are all within `ε` of `v`.

The ε-formulation is essential: exact (`ε = 0`) uniform equilibria can fail
to exist even in two-player zero-sum games — the Big Match
(Blackwell–Ferguson 1968) has no optimal strategies, only ε-optimal ones.

## Status of the existence problem

* Two-player zero-sum games have a uniform value (Mertens–Neyman 1981).
* Two-player games admit uniform equilibrium payoffs (Vieille 2000).
* Three-player absorbing games admit them (Solan, *Three-Player Absorbing
  Games*, MOR 24(3):669-698, 1999; verified against Solan's own doctoral
  dissertation, the MOR journal PDF itself unread).
* The general n-player case is **open**; it is the central open problem of
  the field (Mertens 1986; Solan–Vieille 2010).

The open construction is isolated here as
`StochasticGame.exists_uniformDeviationCapConstructor`.  Its exact
equivalence with the semantic uniform-payoff property is proved, so
`StochasticGame.exists_uniformEquilibriumPayoff` is a checked corollary.
Special cases live in `GameTheory.Concepts.Stochastic.Absorbing`.

## Main definitions

* `StochasticGame.IsεHorizonNash` — ε-Nash equilibrium of the `T`-stage game
  under expected average payoffs
* `StochasticGame.IsUniformεEquilibrium` — ε-Nash of every sufficiently long
  finite-horizon game, with one horizon threshold
* `StochasticGame.IsUniformEquilibriumPayoff` — uniform equilibrium payoff

## Main statements

* `StochasticGame.exists_uniformDeviationCapConstructor` — the quantitative
  form of the open conjecture
* `StochasticGame.exists_uniformEquilibriumPayoff` — its equivalent semantic
  formulation
* `StochasticGame.exists_isUniformεEquilibrium` — for every `ε > 0` some
  profile is a uniform ε-equilibrium (derived from the conjecture)
* `StochasticGame.isUniformEquilibriumPayoff_of_deviation_caps` — a direct
  proof interface reducing the uniform-payoff goal to asymptotic on-path
  payoff estimates and unilateral deviation caps
* `StochasticGame.isUniformEquilibriumPayoff_of_uniform_stagePayoff_limit` —
  closedness of uniform-equilibrium payoffs under uniform stage-payoff
  perturbations on a fixed game skeleton
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

variable {ι : Type}

/-- `σ` is an ε-Nash equilibrium of the `T`-stage game from `s₀` under
expected average payoffs: no unilateral replacement of a whole behavior
strategy gains more than `ε`. -/
def IsεHorizonNash (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (T : ℕ) (ε : ℝ) (σ : G.BehaviorProfile) : Prop :=
  ∀ who (dev : G.BehaviorStrategy who),
    G.finiteAveragePayoff s₀ T σ who + ε ≥
      G.finiteAveragePayoff s₀ T (Function.update σ who dev) who

/-- Uniform ε-equilibrium from `s₀`: a single horizon threshold `T₀` past
which `σ` is an ε-Nash equilibrium of every longer finite-horizon game. -/
def IsUniformεEquilibrium (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (ε : ℝ) (σ : G.BehaviorProfile) : Prop :=
  ∃ T₀ : ℕ, ∀ T, T₀ ≤ T → G.IsεHorizonNash s₀ T ε σ

/-- `v` is a **uniform equilibrium payoff** of `G` from initial state `s₀`:
for every `ε > 0` there are a behavior profile `σ` and a horizon threshold
`T₀` such that in every game of horizon at least `T₀`, `σ` is an ε-Nash
equilibrium and every player's expected average payoff under `σ` is within
`ε` of `v`. -/
def IsUniformEquilibriumPayoff (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] (s₀ : G.State) (v : Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (σ : G.BehaviorProfile) (T₀ : ℕ), ∀ T, T₀ ≤ T →
    G.IsεHorizonNash s₀ T ε σ ∧
      ∀ who, |G.finiteAveragePayoff s₀ T σ who - v who| ≤ ε

/-- Finite-horizon approximate Nash is monotone in the error allowance. -/
theorem IsεHorizonNash.mono {G : StochasticGame ι} [Fintype ι]
    [DecidableEq ι] {s₀ : G.State} {T : ℕ} {ε ε' : ℝ}
    {σ : G.BehaviorProfile}
    (h : G.IsεHorizonNash s₀ T ε σ) (hε : ε ≤ ε') :
    G.IsεHorizonNash s₀ T ε' σ := by
  intro who dev
  have := h who dev
  linarith

/-- Uniform approximate equilibrium is monotone in the error allowance. -/
theorem IsUniformεEquilibrium.mono {G : StochasticGame ι} [Fintype ι]
    [DecidableEq ι] {s₀ : G.State} {ε ε' : ℝ} {σ : G.BehaviorProfile}
    (h : G.IsUniformεEquilibrium s₀ ε σ) (hε : ε ≤ ε') :
    G.IsUniformεEquilibrium s₀ ε' σ := by
  obtain ⟨T₀, hT₀⟩ := h
  exact ⟨T₀, fun T hT => (hT₀ T hT).mono hε⟩

/-- Per horizon, a stochastic game *is* a kernel game: `IsεHorizonNash` is
exactly `KernelGame.IsεNash` of the horizon game (`horizonGame`), whose
strategies are whole behavior strategies.  What is not a single kernel game
is the uniform concept, which quantifies over every horizon with one profile. -/
theorem isεHorizonNash_iff_horizonGame (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] (s₀ : G.State) (T : ℕ) (ε : ℝ) (σ : G.BehaviorProfile) :
    G.IsεHorizonNash s₀ T ε σ ↔ (G.horizonGame s₀ T).IsεNash ε σ := by
  constructor
  · intro hN who dev
    rw [eu_horizonGame, eu_horizonGame]
    exact hN who dev
  · intro hN who dev
    have h := hN who dev
    rw [eu_horizonGame, eu_horizonGame] at h
    exact h

/-- A proof-facing certificate for uniform equilibrium payoffs.  It is enough
to construct, for every positive `δ`, one profile whose long-horizon payoff is
within `δ` of `v` and under which every unilateral deviation is capped by
`v + δ`.  Applying the certificate with `δ = ε / 2` gives the required
`ε`-Nash inequality and `ε` payoff approximation.

This theorem isolates exactly the quantitative estimates that a direct proof
of `exists_uniformEquilibriumPayoff` must supply. -/
theorem isUniformEquilibriumPayoff_of_deviation_caps
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (v : Payoff ι)
    (hcert : ∀ δ : ℝ, 0 < δ →
      ∃ (σ : G.BehaviorProfile) (T₀ : ℕ), ∀ T, T₀ ≤ T →
        (∀ who, |G.finiteAveragePayoff s₀ T σ who - v who| ≤ δ) ∧
        (∀ who (dev : G.BehaviorStrategy who),
          G.finiteAveragePayoff s₀ T (Function.update σ who dev) who ≤
            v who + δ)) :
    G.IsUniformEquilibriumPayoff s₀ v := by
  intro ε hε
  have hδ : 0 < ε / 2 := by linarith
  obtain ⟨σ, T₀, hσ⟩ := hcert (ε / 2) hδ
  refine ⟨σ, T₀, fun T hT => ?_⟩
  obtain ⟨hon, hdev⟩ := hσ T hT
  constructor
  · intro who dev
    have hlower := (abs_le.mp (hon who)).1
    have hupper := hdev who dev
    linarith
  · intro who
    exact (hon who).trans (by linarith)

/-- The quantitative construction obligation for a uniform equilibrium
payoff.

At every positive accuracy it supplies one behavior profile with a common
horizon threshold, simultaneous on-path payoff approximation, and a cap on
every unilateral behavioral deviation. -/
def HasUniformDeviationCapConstructor
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (v : Payoff ι) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ (σ : G.BehaviorProfile) (T₀ : ℕ), ∀ T, T₀ ≤ T →
      (∀ who, |G.finiteAveragePayoff s₀ T σ who - v who| ≤ δ) ∧
      ∀ who (dev : G.BehaviorStrategy who),
        G.finiteAveragePayoff s₀ T (Function.update σ who dev) who ≤
          v who + δ

/-- The deviation-cap constructor is exactly equivalent to the semantic
uniform-equilibrium-payoff property. -/
theorem hasUniformDeviationCapConstructor_iff
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (v : Payoff ι) :
    G.HasUniformDeviationCapConstructor s₀ v ↔
      G.IsUniformEquilibriumPayoff s₀ v := by
  constructor
  · exact G.isUniformEquilibriumPayoff_of_deviation_caps s₀ v
  · intro hv δ hδ
    have hhalf : 0 < δ / 2 := by linarith
    obtain ⟨σ, T₀, hσ⟩ := hv (δ / 2) hhalf
    refine ⟨σ, T₀, fun T hT => ?_⟩
    obtain ⟨hNash, honPath⟩ := hσ T hT
    constructor
    · intro who
      exact (honPath who).trans (by linarith)
    · intro who dev
      have hdev := hNash who dev
      have honUpper := (abs_le.mp (honPath who)).2
      linarith

-- ============================================================================
-- Stability under stage-payoff perturbations
-- ============================================================================

/-- Replace the stage-payoff table while retaining the state space, actions,
transition kernel, and discount parameter definitionally.  This fixed-skeleton
operation lets one reuse a behavior profile without transporting histories or
strategies. -/
def withStagePayoff (G : StochasticGame ι)
    (reward : G.State → G.JointAct → ι → ℝ) : StochasticGame ι where
  State := G.State
  Act := G.Act
  stagePayoff := reward
  transition := G.transition
  discount := G.discount
  discount_nonneg := G.discount_nonneg
  discount_lt_one := G.discount_lt_one

@[simp] theorem stageActionDist_withStagePayoff
    (G : StochasticGame ι) [Fintype ι]
    (reward : G.State → G.JointAct → ι → ℝ)
    (σ : G.BehaviorProfile) {t : ℕ} (h : G.Hist t) :
    (G.withStagePayoff reward).stageActionDist σ h =
      G.stageActionDist σ h :=
  rfl

/-- Changing only stage payoffs leaves every finite-history law unchanged. -/
@[simp] theorem histDist_withStagePayoff
    (G : StochasticGame ι) [Fintype ι]
    (reward : G.State → G.JointAct → ι → ℝ)
    (σ : G.BehaviorProfile) (s₀ : G.State) (T : ℕ) :
    (G.withStagePayoff reward).histDist σ s₀ T =
      G.histDist σ s₀ T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      simp only [histDist_succ, ih, stageActionDist_withStagePayoff]

/-- A pointwise `ρ` perturbation of one player's stage payoff changes that
player's total payoff along a length-`T` history by at most `T * ρ`. -/
theorem abs_totalPayoff_withStagePayoff_sub_le
    (G : StochasticGame ι)
    (reward : G.State → G.JointAct → ι → ℝ)
    {who : ι} {ρ : ℝ}
    (hρ : ∀ s a, |reward s a who - G.stagePayoff s a who| ≤ ρ)
    {T : ℕ} (h : G.Hist T) :
    |(G.withStagePayoff reward).totalPayoff who h -
        G.totalPayoff who h| ≤ (T : ℝ) * ρ := by
  change
    |(∑ k : Fin T, reward (h.1 k).1 (h.1 k).2 who) -
        ∑ k : Fin T, G.stagePayoff (h.1 k).1 (h.1 k).2 who| ≤
      (T : ℝ) * ρ
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ k : Fin T,
        (reward (h.1 k).1 (h.1 k).2 who -
          G.stagePayoff (h.1 k).1 (h.1 k).2 who)|
        ≤ ∑ k : Fin T,
            |reward (h.1 k).1 (h.1 k).2 who -
              G.stagePayoff (h.1 k).1 (h.1 k).2 who| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin T, ρ :=
      Finset.sum_le_sum fun k _ => hρ _ _
    _ = (T : ℝ) * ρ := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- A uniform pointwise `ρ` perturbation of stage rewards changes every
finite-horizon average payoff, under every behavior profile, by at most `ρ`.
The bound is horizon-independent and therefore also applies to arbitrary
unilateral behavioral deviations. -/
theorem abs_finiteAveragePayoff_withStagePayoff_sub_le
    (G : StochasticGame ι) [Fintype ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (reward : G.State → G.JointAct → ι → ℝ)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ s a who, |reward s a who - G.stagePayoff s a who| ≤ ρ)
    (s₀ : G.State) (T : ℕ) (σ : G.BehaviorProfile) (who : ι) :
    |(G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who -
        G.finiteAveragePayoff s₀ T σ who| ≤ ρ := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst T
    simpa using hρ0
  · have hTreal : (0 : ℝ) < T := by
      exact_mod_cast hT
    change
      |(T : ℝ)⁻¹ *
          Math.Probability.expect
            ((G.withStagePayoff reward).histDist σ s₀ T)
            (fun h => (G.withStagePayoff reward).totalPayoff who h) -
        (T : ℝ)⁻¹ *
          Math.Probability.expect (G.histDist σ s₀ T)
            (fun h => G.totalPayoff who h)| ≤ ρ
    rw [histDist_withStagePayoff, ← mul_sub,
      ← Math.Probability.expect_sub]
    have hExpect :
        |Math.Probability.expect (G.histDist σ s₀ T)
            (fun h => (G.withStagePayoff reward).totalPayoff who h -
              G.totalPayoff who h)| ≤ (T : ℝ) * ρ :=
      Math.Probability.abs_expect_le_of_abs_le _ _ fun h =>
        abs_totalPayoff_withStagePayoff_sub_le G reward
          (fun s a => hρ s a who) h
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (T : ℝ)⁻¹)]
    calc
      (T : ℝ)⁻¹ *
          |Math.Probability.expect (G.histDist σ s₀ T)
            (fun h => (G.withStagePayoff reward).totalPayoff who h -
              G.totalPayoff who h)|
          ≤ (T : ℝ)⁻¹ * ((T : ℝ) * ρ) :=
        mul_le_mul_of_nonneg_left hExpect (by positivity)
      _ = ρ := by
        field_simp [ne_of_gt hTreal]

/-- An `ε`-Nash profile for a payoff-perturbed game is an
`(ε + 2ρ)`-Nash profile for the original game.  One copy of `ρ` pays for the
on-path payoff and one for the deviating payoff. -/
theorem IsεHorizonNash.of_withStagePayoff
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (reward : G.State → G.JointAct → ι → ℝ)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ s a who, |reward s a who - G.stagePayoff s a who| ≤ ρ)
    {s₀ : G.State} {T : ℕ} {ε : ℝ} {σ : G.BehaviorProfile}
    (h : (G.withStagePayoff reward).IsεHorizonNash s₀ T ε σ) :
    G.IsεHorizonNash s₀ T (ε + 2 * ρ) σ := by
  intro who dev
  have hNash := h who dev
  have hon :=
    abs_finiteAveragePayoff_withStagePayoff_sub_le G reward hρ0 hρ
      s₀ T σ who
  have hdev :=
    abs_finiteAveragePayoff_withStagePayoff_sub_le G reward hρ0 hρ
      s₀ T (Function.update σ who dev) who
  have honUpper := (abs_le.mp hon).2
  have hdevLower := (abs_le.mp hdev).1
  linarith

/-- Uniform approximate equilibrium transfers across the same payoff
perturbation with the same horizon threshold. -/
theorem IsUniformεEquilibrium.of_withStagePayoff
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (reward : G.State → G.JointAct → ι → ℝ)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ s a who, |reward s a who - G.stagePayoff s a who| ≤ ρ)
    {s₀ : G.State} {ε : ℝ} {σ : G.BehaviorProfile}
    (h : (G.withStagePayoff reward).IsUniformεEquilibrium s₀ ε σ) :
    G.IsUniformεEquilibrium s₀ (ε + 2 * ρ) σ := by
  obtain ⟨T₀, hT₀⟩ := h
  refine ⟨T₀, fun T hT => ?_⟩
  exact (hT₀ T hT).of_withStagePayoff G reward hρ0 hρ

/-- Dense fixed-skeleton approximation principle.

If, at every positive tolerance, there is a uniformly close stage-payoff table
with a uniformly close uniform-equilibrium target, then the limiting target is
a uniform-equilibrium payoff of the original game.  The proof transfers each
nearby game's profile directly; no strategy compactness or uniform memory bound
is used. -/
theorem isUniformEquilibriumPayoff_of_arbitrarily_close_stagePayoffs
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι)
    (happrox : ∀ η : ℝ, 0 < η →
      ∃ (reward : G.State → G.JointAct → ι → ℝ) (w : Payoff ι),
        (∀ s a who, |reward s a who - G.stagePayoff s a who| ≤ η) ∧
        (∀ who, |w who - v who| ≤ η) ∧
        (G.withStagePayoff reward).IsUniformEquilibriumPayoff s₀ w) :
    G.IsUniformEquilibriumPayoff s₀ v := by
  intro ε hε
  have hquarter : 0 < ε / 4 := by
    linarith
  obtain ⟨reward, w, hreward, hw, hUE⟩ := happrox (ε / 4) hquarter
  obtain ⟨σ, T₀, hσ⟩ := hUE (ε / 4) hquarter
  refine ⟨σ, T₀, fun T hT => ?_⟩
  obtain ⟨hNash, hon⟩ := hσ T hT
  constructor
  · have hTransferred :
        G.IsεHorizonNash s₀ T
          (ε / 4 + 2 * (ε / 4)) σ :=
      hNash.of_withStagePayoff G reward hquarter.le hreward
    exact hTransferred.mono (by linarith)
  · intro who
    have hgame :
        |(G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who -
          G.finiteAveragePayoff s₀ T σ who| ≤ ε / 4 :=
      abs_finiteAveragePayoff_withStagePayoff_sub_le G reward
        hquarter.le hreward s₀ T σ who
    have hgame' :
        |G.finiteAveragePayoff s₀ T σ who -
          (G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who| ≤
            ε / 4 := by
      calc
        |G.finiteAveragePayoff s₀ T σ who -
            (G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who|
            = |(G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who -
                G.finiteAveragePayoff s₀ T σ who| := abs_sub_comm _ _
        _ ≤ ε / 4 := hgame
    calc
      |G.finiteAveragePayoff s₀ T σ who - v who|
          ≤ |G.finiteAveragePayoff s₀ T σ who -
                (G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who| +
              |(G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who -
                v who| := abs_sub_le _ _ _
      _ ≤ |G.finiteAveragePayoff s₀ T σ who -
                (G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who| +
              (|(G.withStagePayoff reward).finiteAveragePayoff s₀ T σ who -
                  w who| + |w who - v who|) :=
        add_le_add_left (abs_sub_le _ _ _) _
      _ ≤ ε / 4 + (ε / 4 + ε / 4) :=
        add_le_add hgame' (add_le_add (hon who) (hw who))
      _ ≤ ε := by
        linarith

/-- Sequential closedness of uniform-equilibrium payoffs under uniform
stage-payoff convergence, for a fixed state/action/transition skeleton. -/
theorem isUniformEquilibriumPayoff_of_uniform_stagePayoff_limit
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State)
    (reward : ℕ → G.State → G.JointAct → ι → ℝ)
    (w : ℕ → Payoff ι) (v : Payoff ι)
    (hreward : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ s a who, |reward n s a who - G.stagePayoff s a who| ≤ η)
    (hw : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ who, |w n who - v who| ≤ η)
    (hUE : ∀ n,
      (G.withStagePayoff (reward n)).IsUniformEquilibriumPayoff s₀ (w n)) :
    G.IsUniformEquilibriumPayoff s₀ v := by
  apply isUniformEquilibriumPayoff_of_arbitrarily_close_stagePayoffs G s₀ v
  intro η hη
  obtain ⟨Nr, hNr⟩ := hreward η hη
  obtain ⟨Nv, hNv⟩ := hw η hη
  let n := max Nr Nv
  refine ⟨reward n, w n, ?_, ?_, hUE n⟩
  · exact hNr n (Nat.le_max_left Nr Nv)
  · exact hNv n (Nat.le_max_right Nr Nv)

end StochasticGame

end GameTheory
