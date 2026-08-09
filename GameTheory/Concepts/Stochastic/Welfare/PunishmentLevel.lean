/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Equilibrium.Uniform

/-!
# Punishment (Min-Max) Levels and Individual Rationality

Every classical construction of uniform equilibrium is built on threats: a
deviating player is punished down to their **min-max (punishment) level**,
the best payoff they can guarantee once every other player coordinates to
minimize it.  This file supplies that notion for stochastic games under
finite-horizon average payoffs — the payoff aggregation
`HasUniformDeviationCapConstructor` quantifies over — and proves the
standard necessary condition: a uniform equilibrium payoff is
**individually rational**, i.e. it is at least each player's punishment
level.

No limit theory is used.  The punishment level is defined at each finite
horizon `T` exactly as `finiteAveragePayoff` is; the necessary condition is
proved with the same `∀ε>0, ∃T₀, ∀T≥T₀` quantifier shape that
`IsUniformEquilibriumPayoff` already carries.

## Main definitions

* `StochasticGame.bestResponseAverageAgainstProfile` — the best average
  payoff `who` can secure at horizon `T` by unilaterally replacing their own
  coordinate of a fixed profile `τ`
* `StochasticGame.punishmentLevel` — player `who`'s punishment (min-max)
  level at horizon `T`: the infimum of the above over every profile `τ`
* `StochasticGame.IsIndividuallyRational` / `StochasticGame.IsεIndividuallyRational` —
  a payoff vector dominates (resp. `ε`-dominates) every player's punishment
  level at a horizon

## Main results

* `StochasticGame.punishmentLevel_le_add_of_isUniformEquilibriumPayoff` — a
  uniform equilibrium payoff eventually `ε`-dominates one player's
  punishment level
* `StochasticGame.eventually_isεIndividuallyRational_of_isUniformEquilibriumPayoff` —
  the vector form: a uniform equilibrium payoff is eventually
  `ε`-individually-rational, simultaneously for every player
* `StochasticGame.not_isUniformEquilibriumPayoff_of_punishmentLevel_gt` — the
  no-go generator: a payoff held below a player's punishment level at every
  sufficiently large horizon is not a uniform equilibrium payoff
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

variable {ι : Type}

/-- A nonempty action set gives a nonempty behavior strategy: play the fixed
mixed action `PMF.pure` of an arbitrary action after every history. -/
theorem nonempty_behaviorStrategy (G : StochasticGame ι) (i : ι)
    [Nonempty (G.Act i)] : Nonempty (G.BehaviorStrategy i) :=
  ⟨fun _ _ => PMF.pure (Classical.arbitrary (G.Act i))⟩

/-- Nonempty action sets for every player give a nonempty behavior
profile. -/
theorem nonempty_behaviorProfile (G : StochasticGame ι)
    [∀ i, Nonempty (G.Act i)] : Nonempty G.BehaviorProfile :=
  ⟨fun i _ _ => PMF.pure (Classical.arbitrary (G.Act i))⟩

/-- Player `who`'s best achievable finite-horizon average payoff at horizon
`T` from `s₀`, replacing their own coordinate of the profile `τ` by a best
response: the supremum over `who`'s behavior strategies of the average
payoff under `Function.update τ who dev`.

`Function.update` overwrites `who`'s own coordinate of `τ`, so only `τ`'s
coordinates at players other than `who` matter; there is no need to first
restrict `τ` to an opponent-only profile type. -/
def bestResponseAverageAgainstProfile
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (T : ℕ) (who : ι) (τ : G.BehaviorProfile) : ℝ :=
  ⨆ dev : G.BehaviorStrategy who,
    G.finiteAveragePayoff s₀ T (Function.update τ who dev) who

/-- Player `who`'s **punishment (min-max) level** at horizon `T` from `s₀`:
the least best-response average payoff the other players can hold `who` to
by coordinating their behavior, over every possible coordination.  This is
the finite-horizon average analogue of the classical min-max / threat
value used to build punishments in the uniform-equilibrium literature. -/
def punishmentLevel
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (T : ℕ) (who : ι) : ℝ :=
  ⨅ τ : G.BehaviorProfile, G.bestResponseAverageAgainstProfile s₀ T who τ

/-- `v` is **individually rational** at horizon `T` from `s₀`: no player's
payoff falls below their punishment level. -/
def IsIndividuallyRational
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (T : ℕ) (v : Payoff ι) : Prop :=
  ∀ who, G.punishmentLevel s₀ T who ≤ v who

/-- `v` is **`ε`-individually rational** at horizon `T` from `s₀`: no
player's punishment level exceeds their payoff by more than `ε`. -/
def IsεIndividuallyRational
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (T : ℕ) (ε : ℝ) (v : Payoff ι) : Prop :=
  ∀ who, G.punishmentLevel s₀ T who ≤ v who + ε

/-- Exact individual rationality implies every weaker `ε`-approximate one. -/
theorem IsIndividuallyRational.isεIndividuallyRational
    {G : StochasticGame ι} [Fintype ι] [DecidableEq ι] {s₀ : G.State} {T : ℕ}
    {v : Payoff ι} (h : G.IsIndividuallyRational s₀ T v)
    {ε : ℝ} (hε : 0 ≤ ε) : G.IsεIndividuallyRational s₀ T ε v :=
  fun who => (h who).trans (by linarith)

/-- A uniform stage payoff bound bounds the best-response average against
any profile. -/
theorem abs_bestResponseAverageAgainstProfile_le
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    {who : ι} [Nonempty (G.Act who)] {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s a, |G.stagePayoff s a who| ≤ C)
    (s₀ : G.State) (T : ℕ) (τ : G.BehaviorProfile) :
    |G.bestResponseAverageAgainstProfile s₀ T who τ| ≤ C := by
  haveI := G.nonempty_behaviorStrategy who
  have hpt : ∀ dev : G.BehaviorStrategy who,
      |G.finiteAveragePayoff s₀ T (Function.update τ who dev) who| ≤ C :=
    fun dev => G.abs_finiteAveragePayoff_le hC0 hC s₀ T _
  unfold bestResponseAverageAgainstProfile
  rw [abs_le]
  refine ⟨?_, ciSup_le fun dev => (abs_le.mp (hpt dev)).2⟩
  obtain ⟨dev₀⟩ := G.nonempty_behaviorStrategy who
  have hbdd : BddAbove (Set.range fun dev : G.BehaviorStrategy who =>
      G.finiteAveragePayoff s₀ T (Function.update τ who dev) who) :=
    ⟨C, by rintro _ ⟨dev, rfl⟩; exact (abs_le.mp (hpt dev)).2⟩
  exact (abs_le.mp (hpt dev₀)).1.trans (le_ciSup hbdd dev₀)

/-- A uniform stage payoff bound bounds the punishment level. -/
theorem abs_punishmentLevel_le
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    {who : ι} [∀ i, Nonempty (G.Act i)] {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s a, |G.stagePayoff s a who| ≤ C)
    (s₀ : G.State) (T : ℕ) :
    |G.punishmentLevel s₀ T who| ≤ C := by
  have hpt : ∀ τ : G.BehaviorProfile,
      |G.bestResponseAverageAgainstProfile s₀ T who τ| ≤ C :=
    G.abs_bestResponseAverageAgainstProfile_le hC0 hC s₀ T
  unfold punishmentLevel
  rw [abs_le]
  obtain ⟨τ₀⟩ := G.nonempty_behaviorProfile
  have hbdd : BddBelow (Set.range (G.bestResponseAverageAgainstProfile s₀ T who)) :=
    ⟨-C, by rintro _ ⟨τ, rfl⟩; exact (abs_le.mp (hpt τ)).1⟩
  refine ⟨le_ciInf fun τ => (abs_le.mp (hpt τ)).1, ?_⟩
  exact (ciInf_le hbdd τ₀).trans (abs_le.mp (hpt τ₀)).2

/-- **Individual rationality, one player at a time.**  If `v` is a uniform
equilibrium payoff of `G` from `s₀`, then for every `ε > 0` there is a
horizon threshold past which player `who`'s punishment level never exceeds
`v who + ε`.

The argument: at accuracy `ε/2`, `IsUniformEquilibriumPayoff` supplies a
profile `σ` and horizon threshold `T₀` past which `σ` is an `ε/2`-Nash
equilibrium with on-path payoff within `ε/2` of `v`.  No unilateral
deviation from `σ` then beats `v who + ε`, so the best-response value
against `σ`'s own coordinates for the other players is itself at most
`v who + ε`; the punishment level, being the *least* best-response value
over *every* profile, is therefore at most `v who + ε` as well.

Read contrapositively: a player held strictly below their punishment level
has, by definition of that level, a deviation beating the prescribed payoff
by a fixed margin — contradicting the deviation cap that a uniform
equilibrium payoff supplies at every sufficiently long horizon. -/
theorem punishmentLevel_le_add_of_isUniformEquilibriumPayoff
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (v : Payoff ι) (who : ι) [Nonempty (G.Act who)]
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s a, |G.stagePayoff s a who| ≤ C)
    (hv : G.IsUniformEquilibriumPayoff s₀ v) {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℕ, ∀ T, T₀ ≤ T → G.punishmentLevel s₀ T who ≤ v who + ε := by
  haveI := G.nonempty_behaviorStrategy who
  obtain ⟨σ, T₀, hσ⟩ := hv (ε / 2) (half_pos hε)
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨hNash, hOnPath⟩ := hσ T hT
  have hcap : ∀ dev : G.BehaviorStrategy who,
      G.finiteAveragePayoff s₀ T (Function.update σ who dev) who ≤ v who + ε := by
    intro dev
    have h1 := hNash who dev
    have h2 := (abs_le.mp (hOnPath who)).2
    linarith
  have hbr : G.bestResponseAverageAgainstProfile s₀ T who σ ≤ v who + ε := by
    unfold bestResponseAverageAgainstProfile
    exact ciSup_le hcap
  have hbddBelow :
      BddBelow (Set.range (G.bestResponseAverageAgainstProfile s₀ T who)) :=
    ⟨-C, by
      rintro _ ⟨τ, rfl⟩
      exact (abs_le.mp
        (G.abs_bestResponseAverageAgainstProfile_le hC0 hC s₀ T τ)).1⟩
  unfold punishmentLevel
  exact (ciInf_le hbddBelow σ).trans hbr

/-- **Individual rationality.**  If `v` is a uniform equilibrium payoff of
`G` from `s₀`, then for every `ε > 0` there is a horizon threshold past
which `v` is `ε`-individually rational: simultaneously for every player,
the punishment level never exceeds that player's payoff by more than `ε`.

This is the necessary condition every uniform equilibrium payoff satisfies,
and the no-go generator dual to it: any candidate payoff held below some
player's punishment level by more than a fixed margin, at arbitrarily large
horizons, is refuted (`not_isUniformEquilibriumPayoff_of_punishmentLevel_gt`
below). -/
theorem eventually_isεIndividuallyRational_of_isUniformEquilibriumPayoff
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (v : Payoff ι) [∀ i, Nonempty (G.Act i)]
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i s a, |G.stagePayoff s a i| ≤ C)
    (hv : G.IsUniformEquilibriumPayoff s₀ v) {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℕ, ∀ T, T₀ ≤ T → G.IsεIndividuallyRational s₀ T ε v := by
  choose T₀ hT₀ using fun who =>
    G.punishmentLevel_le_add_of_isUniformEquilibriumPayoff s₀ v who
      hC0 (hC who) hv hε
  refine ⟨Finset.univ.sup T₀, fun T hT who => ?_⟩
  exact hT₀ who T (le_trans (Finset.le_sup (Finset.mem_univ who)) hT)

/-- **No-go generator.**  If a player's punishment level exceeds a candidate
payoff by more than a fixed margin `ε` at every horizon past `N`, that
payoff is not a uniform equilibrium payoff.  This is the direct corollary
of individual rationality used to refute a concrete candidate payoff table:
exhibit one player and one margin for which the punishment level of a
concrete reward table stays that far above the candidate. -/
theorem not_isUniformEquilibriumPayoff_of_punishmentLevel_gt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (s₀ : G.State) (v : Payoff ι) (who : ι) [Nonempty (G.Act who)]
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s a, |G.stagePayoff s a who| ≤ C)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ)
    (hbad : ∀ T, N ≤ T → v who + ε < G.punishmentLevel s₀ T who) :
    ¬ G.IsUniformEquilibriumPayoff s₀ v := by
  intro hv
  obtain ⟨T₀, hT₀⟩ :=
    G.punishmentLevel_le_add_of_isUniformEquilibriumPayoff s₀ v who hC0 hC hv hε
  exact absurd (hT₀ (max N T₀) (le_max_right _ _))
    (not_le.mpr (hbad _ (le_max_left _ _)))

end StochasticGame

end GameTheory
