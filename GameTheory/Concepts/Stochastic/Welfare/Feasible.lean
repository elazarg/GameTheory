/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Analysis.Convex.Combination
import GameTheory.Concepts.Stochastic.Welfare.PunishmentLevel
import GameTheory.Concepts.Stochastic.Models.Quitting.Game
import GameTheory.Concepts.Welfare.FolkTheorem.Feasible
import Math.PMFProduct.Bool

/-!
# Feasible Payoffs for Stochastic Games

The third item of the folk-theorem bill for stochastic games: `feasibleSet`
for `StochasticGame`, matching `KernelGame.feasibleSet`
(`GameTheory.Concepts.Welfare.FolkTheorem.Feasible`) at the stochastic level.

Two feasible sets are supplied, at the two payoff aggregations already used
by the uniform-equilibrium program:

* `StochasticGame.finiteFeasibleSet` — the finite-horizon feasible set: the
  range of `finiteAveragePayoff` over behavior profiles, at a fixed horizon.
  Unlike `KernelGame.feasibleSet` this is **not** a convex hull: public
  randomization is not part of the model, so nothing convexifies the range of
  independent behavior profiles (`Feasible.FiniteFeasibleSetNotConvex`
  exhibits a two-player instance where it genuinely fails to be convex).
* `StochasticGame.IsAsymptoticFeasible` / `StochasticGame.asymptoticFeasibleSet`
  — the asymptotic feasible set: payoffs approximated, at every accuracy, by
  *some* profile at all sufficiently large horizons.  Its quantifier shape
  matches `StochasticGame.IsUniformEquilibriumPayoff` exactly (drop the
  Nash conjunct), so every uniform equilibrium payoff is asymptotically
  feasible almost by definition
  (`isAsymptoticFeasible_of_isUniformEquilibriumPayoff`).

Combined with the landed individual-rationality necessary condition
(`eventually_isεIndividuallyRational_of_isUniformEquilibriumPayoff` in
`PunishmentLevel.lean`), this gives the full folk-theorem necessary
direction in one theorem:
`isAsymptoticFeasible_and_eventually_isεIndividuallyRational_of_isUniformEquilibriumPayoff`.

For the quitting game, `finiteFeasibleSet_quittingGame_subset_convexHull`
relates the feasible set to the reward table: every finite-horizon feasible
vector is a convex combination of the coalition reward vectors *and the zero
vector*, the zero vector standing for the horizon share spent still active
(not yet absorbed).  This is an unconditional inclusion, not an equality —
whether every point of that hull is itself attained by some profile is a
separate, harder question this file does not address.
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

open Math.Probability

variable {ι : Type}

/-! ## The finite-horizon feasible set -/

/-- The finite-horizon feasible set at horizon `T` from `s₀`: every payoff
vector attainable by some behavior profile's expected average payoff over
the first `T` stages.  There is no convex hull here (contrast
`KernelGame.feasibleSet`): public randomization plays no role in the
behavior-strategy model, so nothing correlates independent players'
randomizations beyond what a single behavior profile already supplies. -/
def finiteFeasibleSet (G : StochasticGame ι) [Fintype ι] (s₀ : G.State) (T : ℕ) :
    Set (Payoff ι) :=
  Set.range (fun σ : G.BehaviorProfile => G.finiteAveragePayoff s₀ T σ)

/-- Membership in the finite-horizon feasible set unfolds to existence of a
realizing behavior profile. -/
theorem mem_finiteFeasibleSet (G : StochasticGame ι) [Fintype ι] (s₀ : G.State) (T : ℕ)
    (v : Payoff ι) :
    v ∈ G.finiteFeasibleSet s₀ T ↔ ∃ σ : G.BehaviorProfile, G.finiteAveragePayoff s₀ T σ = v :=
  Iff.rfl

/-- Every behavior profile's finite-horizon average payoff is feasible. -/
theorem finiteAveragePayoff_mem_finiteFeasibleSet (G : StochasticGame ι) [Fintype ι]
    (s₀ : G.State) (T : ℕ) (σ : G.BehaviorProfile) :
    G.finiteAveragePayoff s₀ T σ ∈ G.finiteFeasibleSet s₀ T :=
  ⟨σ, rfl⟩

/-- The finite-horizon feasible set is exactly the pure-payoff set of the
horizon game (`horizonGame`, the `T`-stage truncation viewed as a one-shot
`KernelGame` whose strategies are whole behavior strategies).  There is no
separate `convexHull` step because a `StochasticGame`'s strategies already
*are* the horizon game's strategies — the two feasible-set notions coincide
exactly where `KernelGame.feasibleSet` would take a convex hull of
`purePayoffSet` to account for correlation that the model does not have. -/
theorem finiteFeasibleSet_eq_purePayoffSet_horizonGame (G : StochasticGame ι) [Fintype ι]
    (s₀ : G.State) (T : ℕ) :
    G.finiteFeasibleSet s₀ T = (G.horizonGame s₀ T).purePayoffSet := by
  unfold finiteFeasibleSet KernelGame.purePayoffSet KernelGame.payoffVector
  congr 1
  funext σ
  funext who
  exact (eu_horizonGame G s₀ T σ who).symm

/-- The finite-horizon feasible set is nonempty whenever every player has an
available action. -/
theorem nonempty_finiteFeasibleSet (G : StochasticGame ι) [Fintype ι]
    [∀ i, Nonempty (G.Act i)] (s₀ : G.State) (T : ℕ) :
    (G.finiteFeasibleSet s₀ T).Nonempty := by
  obtain ⟨σ⟩ := G.nonempty_behaviorProfile
  exact ⟨G.finiteAveragePayoff s₀ T σ, σ, rfl⟩

/-- A uniform stage payoff bound bounds every coordinate of every feasible
payoff vector, by the same bound already proved for `finiteAveragePayoff`. -/
theorem abs_apply_le_of_mem_finiteFeasibleSet (G : StochasticGame ι) [Fintype ι]
    {who : ι} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s a, |G.stagePayoff s a who| ≤ C)
    (s₀ : G.State) (T : ℕ) {v : Payoff ι} (hv : v ∈ G.finiteFeasibleSet s₀ T) :
    |v who| ≤ C := by
  obtain ⟨σ, rfl⟩ := hv
  exact G.abs_finiteAveragePayoff_le hC0 hC s₀ T σ

/-- At horizon `0` the feasible set is the single point `0`: no stage has
been played yet. -/
@[simp] theorem finiteFeasibleSet_zero (G : StochasticGame ι) [Fintype ι]
    [∀ i, Nonempty (G.Act i)] (s₀ : G.State) :
    G.finiteFeasibleSet s₀ 0 = {(0 : Payoff ι)} := by
  haveI := G.nonempty_behaviorProfile
  have hconst : (fun σ : G.BehaviorProfile => G.finiteAveragePayoff s₀ 0 σ) =
      fun _ => (0 : Payoff ι) := by
    funext σ
    funext who
    exact G.finiteAveragePayoff_zero s₀ σ who
  unfold finiteFeasibleSet
  rw [hconst]
  exact Set.range_const

/-- At horizon `1` a behavior profile's average payoff is exactly the
expected stage payoff of its mixed action at the empty history: the
finite-horizon feasible set at horizon `1` is the one-shot mixed-payoff
correspondence of the stage game at `s₀`. -/
theorem finiteAveragePayoff_one (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (s₀ : G.State) (σ : G.BehaviorProfile) (who : ι) :
    G.finiteAveragePayoff s₀ 1 σ who = G.stageEUAt σ (G.emptyHist s₀) who := by
  have h := G.expect_totalPayoff_succ σ s₀ 0 who
  rw [histDist_zero, expect_pure, expect_pure, totalPayoff_zero, zero_add] at h
  unfold StochasticGame.finiteAveragePayoff
  rw [h]
  norm_num

/-- The one-stage expected payoff of a stationary behavior profile at any
history is the mixed stage-payoff of its fixed mixed action, evaluated at
that history's current state. -/
theorem stageEUAt_stationaryBehaviorProfile (G : StochasticGame ι) [Fintype ι]
    (m : ∀ i, PMF (G.Act i)) {t : ℕ} (h : G.Hist t) (who : ι) :
    G.stageEUAt (G.stationaryBehaviorProfile m) h who = G.mixedStageEU h.2 m who := by
  unfold StochasticGame.stageEUAt StochasticGame.mixedStageEU
  rw [stageActionDist_stationaryBehaviorProfile]

/-! ## The asymptotic feasible set -/

/-- `v` is **asymptotically feasible** from `s₀`: for every `ε > 0` some
behavior profile's finite-horizon average payoff is within `ε` of `v`,
simultaneously for every player, at every sufficiently large horizon.  The
quantifier shape matches `IsUniformEquilibriumPayoff` exactly, with the
`IsεHorizonNash` conjunct dropped — the two compose directly. -/
def IsAsymptoticFeasible (G : StochasticGame ι) [Fintype ι] (s₀ : G.State)
    (v : Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (σ : G.BehaviorProfile) (T₀ : ℕ), ∀ T, T₀ ≤ T →
    ∀ who, |G.finiteAveragePayoff s₀ T σ who - v who| ≤ ε

/-- The asymptotic feasible set from `s₀`. -/
def asymptoticFeasibleSet (G : StochasticGame ι) [Fintype ι] (s₀ : G.State) :
    Set (Payoff ι) :=
  {v | G.IsAsymptoticFeasible s₀ v}

@[simp] theorem mem_asymptoticFeasibleSet (G : StochasticGame ι) [Fintype ι]
    (s₀ : G.State) (v : Payoff ι) :
    v ∈ G.asymptoticFeasibleSet s₀ ↔ G.IsAsymptoticFeasible s₀ v :=
  Iff.rfl

/-- **Every uniform equilibrium payoff is asymptotically feasible.**  Nearly
definitional: `IsUniformEquilibriumPayoff` supplies, at every accuracy, a
profile and horizon threshold with both an `ε`-Nash property and the payoff
approximation; dropping the Nash conjunct is exactly `IsAsymptoticFeasible`. -/
theorem isAsymptoticFeasible_of_isUniformEquilibriumPayoff (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] (s₀ : G.State) (v : Payoff ι)
    (hv : G.IsUniformEquilibriumPayoff s₀ v) : G.IsAsymptoticFeasible s₀ v := by
  intro ε hε
  obtain ⟨σ, T₀, hσ⟩ := hv ε hε
  exact ⟨σ, T₀, fun T hT => (hσ T hT).2⟩

/-- **The folk-theorem necessary direction.**  Every uniform equilibrium
payoff is asymptotically feasible *and* eventually approximately
individually rational: the combination of
`isAsymptoticFeasible_of_isUniformEquilibriumPayoff` with the landed
individual-rationality necessary condition
(`eventually_isεIndividuallyRational_of_isUniformEquilibriumPayoff`). -/
theorem isAsymptoticFeasible_and_eventually_isεIndividuallyRational_of_isUniformEquilibriumPayoff
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [∀ i, Nonempty (G.Act i)]
    (s₀ : G.State) (v : Payoff ι)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i s a, |G.stagePayoff s a i| ≤ C)
    (hv : G.IsUniformEquilibriumPayoff s₀ v) :
    G.IsAsymptoticFeasible s₀ v ∧
      ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℕ, ∀ T, T₀ ≤ T → G.IsεIndividuallyRational s₀ T ε v :=
  ⟨G.isAsymptoticFeasible_of_isUniformEquilibriumPayoff s₀ v hv,
    fun _ε hε => G.eventually_isεIndividuallyRational_of_isUniformEquilibriumPayoff
      s₀ v hC0 hC hv hε⟩

end StochasticGame

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι]

/-! ## The quitting-game terminal-payoff characterization -/

/-- The per-state payoff vector of a quitting game: the zero vector while
active, the coalition reward while absorbed at `S`.  Every stage payoff of a
quitting game equals this, regardless of the action played
(`stagePayoff_quittingGame_eq_stateReward`). -/
def stateReward (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingGame reward).State → Payoff ι
  | none => 0
  | some S => reward S

/-- Every state's per-state payoff vector is either `0` or a coalition
reward. -/
theorem stateReward_mem_insert_zero_range
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (s : (quittingGame reward).State) :
    stateReward reward s ∈ insert (0 : Payoff ι) (Set.range reward) := by
  cases s with
  | none => simp [stateReward]
  | some S => exact Set.mem_insert_of_mem _ ⟨S, rfl⟩

/-- The quitting game's stage payoff depends on the state alone: it is
`stateReward` at that state, independent of the joint action played. -/
theorem stagePayoff_quittingGame_eq_stateReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (s : (quittingGame reward).State) (a : (quittingGame reward).JointAct) :
    (quittingGame reward).stagePayoff s a = stateReward reward s := by
  cases s <;> rfl

/-- **The total payoff along a quitting-game history is the sum, over
completed stages, of the per-state payoff vector visited at that stage.**  A
purely combinatorial identity, independent of any probability: it holds for
every realized history, not merely in expectation. -/
theorem totalPayoffVec_quittingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {t : ℕ}
    (h : (quittingGame reward).Hist t) :
    (fun who => (quittingGame reward).totalPayoff who h) =
      ∑ k : Fin t, stateReward reward (h.1 k).1 := by
  funext who
  unfold StochasticGame.totalPayoff
  rw [Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ =>
    congrFun (stagePayoff_quittingGame_eq_stateReward reward (h.1 k).1 (h.1 k).2) who

/-- **Every realized history's time-average payoff is a convex combination of
coalition rewards and the zero vector.**  Deterministic: for any completed
history `h` of positive length `T`, the time-average of the per-state
payoffs visited along `h` is the center of mass of `T` points drawn from
`insert 0 (Set.range reward)`, hence lies in its convex hull.  The zero
vector accounts for every stage at which `h` was still active. -/
theorem smul_totalPayoffVec_mem_convexHull
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {T : ℕ} (hT : T ≠ 0)
    (h : (quittingGame reward).Hist T) :
    (T : ℝ)⁻¹ • (fun who => (quittingGame reward).totalPayoff who h) ∈
      convexHull ℝ (insert (0 : Payoff ι) (Set.range reward)) := by
  have hcard : (∑ _k : Fin T, (1 : ℝ)) = (T : ℝ) := by simp
  have hpos : (0 : ℝ) < ∑ _k : Fin T, (1 : ℝ) := by
    rw [hcard]; exact_mod_cast Nat.pos_of_ne_zero hT
  have hcenter := Finset.centerMass_mem_convexHull (Finset.univ : Finset (Fin T))
    (w := fun _ : Fin T => (1 : ℝ)) (hw₀ := fun k _ => zero_le_one) (hws := hpos)
    (z := fun k => stateReward reward (h.1 k).1)
    (hz := fun k _ => stateReward_mem_insert_zero_range reward (h.1 k).1)
  have heq : (Finset.univ : Finset (Fin T)).centerMass (fun _ : Fin T => (1 : ℝ))
      (fun k => stateReward reward (h.1 k).1) =
      (T : ℝ)⁻¹ • ∑ k : Fin T, stateReward reward (h.1 k).1 := by
    simp [Finset.centerMass, hcard]
  rw [totalPayoffVec_quittingGame reward h, ← heq]
  exact hcenter

/-- **The quitting-game terminal-payoff characterization.**  Every
finite-horizon feasible payoff vector of a quitting game is a convex
combination of the coalition reward vectors and the zero vector — the
"convex combination with remainder" the folk-theorem gap calls for, where
the remainder is the horizon share spent on stages not yet absorbed (they
pay `0`, uniformly across every player).  The inclusion is unconditional: no
hypothesis on the reward table, and no lower bound on `T` (at `T = 0` the
feasible set is `{0}`, and `0` is one of the two kinds of extreme point).
It need not be an equality: whether every point of the hull is itself
attained by some quitting-game profile is a separate, harder question this
file does not address. -/
theorem finiteFeasibleSet_quittingGame_subset_convexHull
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (s₀ : (quittingGame reward).State) (T : ℕ) :
    (quittingGame reward).finiteFeasibleSet s₀ T ⊆
      convexHull ℝ (insert (0 : Payoff ι) (Set.range reward)) := by
  rcases eq_or_ne T 0 with hT | hT
  · subst hT
    rintro v ⟨σ, rfl⟩
    dsimp only
    have h0 : (quittingGame reward).finiteAveragePayoff s₀ 0 σ = (0 : Payoff ι) := by
      funext who
      exact (quittingGame reward).finiteAveragePayoff_zero s₀ σ who
    rw [h0]
    exact subset_convexHull ℝ _ (by simp)
  · haveI : Finite (quittingGame reward).State :=
      inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
    haveI : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
      fun _ => inferInstanceAs (Finite Bool)
    haveI : Finite ((quittingGame reward).Hist T) := by
      unfold StochasticGame.Hist StochasticGame.StageRecord StochasticGame.JointAct
      infer_instance
    haveI : Fintype ((quittingGame reward).Hist T) := Fintype.ofFinite _
    rintro v ⟨σ, rfl⟩
    dsimp only
    have hstep : (quittingGame reward).finiteAveragePayoff s₀ T σ =
        ∑ h : (quittingGame reward).Hist T,
          (((quittingGame reward).histDist σ s₀ T h).toReal •
            ((T : ℝ)⁻¹ • fun who => (quittingGame reward).totalPayoff who h)) := by
      funext who
      have h1 : (quittingGame reward).finiteAveragePayoff s₀ T σ who =
          expect ((quittingGame reward).histDist σ s₀ T)
            (fun h => (T : ℝ)⁻¹ * (quittingGame reward).totalPayoff who h) := by
        unfold StochasticGame.finiteAveragePayoff
        exact (expect_const_mul _ _ _).symm
      rw [h1, expect_eq_sum, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro h _
      simp [Pi.smul_apply, smul_eq_mul]
    rw [hstep]
    apply Convex.sum_mem (convex_convexHull ℝ _)
    · intro h _
      exact ENNReal.toReal_nonneg
    · exact pmf_toReal_sum_one _
    · intro h _
      exact smul_totalPayoffVec_mem_convexHull reward hT h

/-! ## Non-convexity: a two-player instance

Public randomization is not part of the behavior-strategy model, so nothing
forces `finiteFeasibleSet` to be convex.  `battleOfSexes` below is a
single-state, two-player, two-action stochastic game whose horizon-`1`
feasible set is exactly the classical independent-mixing payoff
correspondence of a battle-of-the-sexes bimatrix game — known to be
non-convex, and witnessed so directly here. -/

namespace FiniteFeasibleSetNotConvex

open Math.PMFProduct

/-- **A battle-of-the-sexes stage game, embedded as a single-state
stochastic game.**  Player `true` is the row player, `false` the column
player; coordinating on `true` pays `(2, 1)`, coordinating on `false` pays
`(1, 2)`, and miscoordination pays `(0, 0)`. -/
def battleOfSexes : StochasticGame Bool where
  State := Unit
  Act := fun _ => Bool
  stagePayoff := fun _ a i => if a true = a false then (if a true = i then 2 else 1) else 0
  transition := fun s _ => PMF.pure s
  discount := 0
  discount_nonneg := le_refl 0
  discount_lt_one := zero_lt_one

/-- The stationary profile in which both players always play `true`,
realizing the payoff vector `(2, 1)`. -/
def alwaysTrue : battleOfSexes.BehaviorProfile :=
  battleOfSexes.stationaryBehaviorProfile (fun _ => PMF.pure true)

/-- The stationary profile in which both players always play `false`,
realizing the payoff vector `(1, 2)`. -/
def alwaysFalse : battleOfSexes.BehaviorProfile :=
  battleOfSexes.stationaryBehaviorProfile (fun _ => PMF.pure false)

/-- Under `alwaysTrue`, the row player earns `2` and the column player `1`. -/
theorem finiteAveragePayoff_alwaysTrue (who : Bool) :
    battleOfSexes.finiteAveragePayoff () 1 alwaysTrue who = if who then 2 else 1 := by
  haveI : Finite battleOfSexes.State := inferInstanceAs (Finite Unit)
  haveI : ∀ i, Finite (battleOfSexes.Act i) := fun _ => inferInstanceAs (Finite Bool)
  rw [battleOfSexes.finiteAveragePayoff_one, alwaysTrue,
    battleOfSexes.stageEUAt_stationaryBehaviorProfile]
  unfold StochasticGame.mixedStageEU
  rw [pmfPi_pure, expect_pure]
  unfold battleOfSexes
  cases who <;> simp

/-- Under `alwaysFalse`, the row player earns `1` and the column player `2`. -/
theorem finiteAveragePayoff_alwaysFalse (who : Bool) :
    battleOfSexes.finiteAveragePayoff () 1 alwaysFalse who = if who then 1 else 2 := by
  haveI : Finite battleOfSexes.State := inferInstanceAs (Finite Unit)
  haveI : ∀ i, Finite (battleOfSexes.Act i) := fun _ => inferInstanceAs (Finite Bool)
  rw [battleOfSexes.finiteAveragePayoff_one, alwaysFalse,
    battleOfSexes.stageEUAt_stationaryBehaviorProfile]
  unfold StochasticGame.mixedStageEU
  rw [pmfPi_pure, expect_pure]
  unfold battleOfSexes
  cases who <;> simp

/-- The stage payoff of `battleOfSexes`, spelled out as an explicit table:
a bridging fact that keeps the definitional unfolding of `battleOfSexes`
confined to a single `rfl`. -/
theorem stagePayoff_battleOfSexes (a : Bool → Bool) (who : Bool) :
    battleOfSexes.stagePayoff () a who =
      if a true = a false then (if a true = who then 2 else 1) else 0 :=
  rfl

/-- **The mixed one-shot payoff of `battleOfSexes` under an independent
mixture, in closed form.**  With `p` the row player's probability of `true`
and `q` the column player's probability of `true`, the row player's payoff
is `3pq - p - q + 1` and the column player's is `3pq - 2p - 2q + 2` — the
classical bimatrix independent-mixing formula. -/
theorem mixedStageEU_battleOfSexes (m : Bool → PMF Bool) (who : Bool) :
    battleOfSexes.mixedStageEU () m who =
      3 * (m true true).toReal * (m false true).toReal -
        (if who then 1 else 2) * (m true true).toReal -
        (if who then 1 else 2) * (m false true).toReal +
        (if who then 1 else 2) := by
  have hunfold : battleOfSexes.mixedStageEU () m who =
      expect (pmfPi m) (fun a => battleOfSexes.stagePayoff () a who) := rfl
  rw [hunfold, expect_pmfPi_bool]
  simp only [expect_eq_sum, Fintype.sum_bool, stagePayoff_battleOfSexes]
  rw [pmfBool_false_toReal (m true), pmfBool_false_toReal (m false)]
  cases who <;> simp <;> ring

/-- Any behavior profile's horizon-`1` average payoff is the mixed one-shot
payoff of its mixed action at the empty history. -/
theorem finiteAveragePayoff_eq_mixedStageEU (σ : battleOfSexes.BehaviorProfile) (who : Bool) :
    battleOfSexes.finiteAveragePayoff () 1 σ who =
      battleOfSexes.mixedStageEU () (fun i => σ i 0 (battleOfSexes.emptyHist ())) who := by
  haveI : Finite battleOfSexes.State := inferInstanceAs (Finite Unit)
  haveI : ∀ i, Finite (battleOfSexes.Act i) := fun _ => inferInstanceAs (Finite Bool)
  rw [battleOfSexes.finiteAveragePayoff_one]
  rfl

/-- **`finiteFeasibleSet` is not convex.**  The two coordination payoffs
`(2, 1)` and `(1, 2)` are both feasible at horizon `1`, but their midpoint
`(3/2, 3/2)` is not: writing `p, q` for the two players' probabilities of
`true`, feasibility of the midpoint forces `p + q = 1` and `p * q = 1 / 2`
simultaneously, so `(p - q)^2 = -1`, impossible for reals.  Public
randomization would fix this (a coin flip choosing between the two pure
coordination profiles reaches the midpoint exactly), but it is not part of
the behavior-strategy model. -/
theorem not_convex_finiteFeasibleSet :
    ¬ Convex ℝ (battleOfSexes.finiteFeasibleSet () 1) := by
  intro hconvex
  have hv1 : battleOfSexes.finiteAveragePayoff () 1 alwaysTrue ∈
      battleOfSexes.finiteFeasibleSet () 1 := ⟨alwaysTrue, rfl⟩
  have hv2 : battleOfSexes.finiteAveragePayoff () 1 alwaysFalse ∈
      battleOfSexes.finiteFeasibleSet () 1 := ⟨alwaysFalse, rfl⟩
  obtain ⟨σ, hσ⟩ := hconvex hv1 hv2
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
  have hσtrue := congrFun hσ true
  have hσfalse := congrFun hσ false
  dsimp only at hσtrue hσfalse
  rw [finiteAveragePayoff_eq_mixedStageEU, mixedStageEU_battleOfSexes] at hσtrue hσfalse
  simp only [finiteAveragePayoff_alwaysTrue, finiteAveragePayoff_alwaysFalse,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hσtrue hσfalse
  norm_num at hσtrue hσfalse
  generalize hpdef : (σ true 0 (battleOfSexes.emptyHist ()) true).toReal = p at hσtrue hσfalse
  generalize hqdef : (σ false 0 (battleOfSexes.emptyHist ()) true).toReal = q at hσtrue hσfalse
  have hsum : p + q = 1 := by linarith
  have hprod : p * q = 1 / 2 := by linarith
  have hring : (p - q) ^ 2 = (p + q) ^ 2 - 4 * (p * q) := by ring
  rw [hsum, hprod] at hring
  norm_num at hring
  linarith [sq_nonneg (p - q), hring]

end FiniteFeasibleSetNotConvex

end GameTheory
