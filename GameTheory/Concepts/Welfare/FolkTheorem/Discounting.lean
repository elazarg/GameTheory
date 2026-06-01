/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Math.SimplexApproximation
import GameTheory.Concepts.Mixed.MixedExtension
import GameTheory.Concepts.ZeroSum.SecurityStrategy
import GameTheory.Concepts.Welfare.FolkTheorem.Feasible

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- Average payoff of a nonempty finite cycle of stage profiles. -/
def cycleAveragePayoff (G : KernelGame ι) {n : ℕ} [NeZero n]
    (cycle : Fin n → Profile G) : Payoff ι :=
  fun i => (n : ℝ)⁻¹ * ∑ t : Fin n, G.eu (cycle t) i

/-- The average payoff of a finite pure-profile cycle is feasible. -/
theorem cycleAveragePayoff_mem_feasibleSet (G : KernelGame ι)
    {n : ℕ} [NeZero n] (cycle : Fin n → Profile G) :
    G.cycleAveragePayoff cycle ∈ G.feasibleSet := by
  rw [feasibleSet]
  refine mem_convexHull_of_exists_fintype (s := G.purePayoffSet)
    (ι := Fin n) (fun _ => (n : ℝ)⁻¹) (fun t => G.payoffVector (cycle t)) ?_ ?_ ?_ ?_
  · intro _
    exact inv_nonneg.mpr (Nat.cast_nonneg n)
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_comm, inv_mul_cancel₀ hn]
  · intro t
    exact ⟨cycle t, rfl⟩
  · ext i
    simp [cycleAveragePayoff, payoffVector, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]

/-- Embed a finite pure-profile cycle into the mixed extension pointwise. -/
def pureMixedCycle (G : KernelGame ι) [Fintype ι]
    {n : ℕ} (cycle : Fin n → Profile G) : Fin n → Profile G.mixedExtension :=
  fun t => G.pureMixedProfile (cycle t)

/-- Cycle averages are preserved by embedding the cycle pointwise into the mixed
extension as Dirac mixed profiles. -/
theorem mixedExtension_cycleAveragePayoff_pureMixedCycle
    (G : KernelGame ι) [Fintype ι] {n : ℕ} [NeZero n]
    (cycle : Fin n → Profile G) :
    G.mixedExtension.cycleAveragePayoff (G.pureMixedCycle cycle) =
      G.cycleAveragePayoff cycle := by
  funext i
  simp [cycleAveragePayoff, pureMixedCycle, G.mixedExtension_eu_pureMixedProfile]

/-- For a finite outcome carrier, each player's expected utility is uniformly
bounded over profiles. -/
theorem exists_stageEU_abs_bound_of_finite_outcome
    (G : KernelGame ι) [Finite G.Outcome] (who : ι) :
    ∃ C : ℝ, ∀ σ : Profile G, |G.eu σ who| ≤ C := by
  obtain ⟨C, hC⟩ :=
    Math.Probability.exists_abs_bound_of_finite (fun ω : G.Outcome => G.utility ω who)
  exact ⟨C, fun σ => G.eu_abs_le_of_bounded who hC σ⟩

/-- With finitely many players and finite outcomes, all stage expected utilities
share a single absolute bound. -/
theorem exists_uniform_stageEU_abs_bound_of_finite
    (G : KernelGame ι) [Finite ι] [Finite G.Outcome] :
    ∃ C : ℝ, ∀ (σ : Profile G) (who : ι), |G.eu σ who| ≤ C := by
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype G.Outcome := Fintype.ofFinite G.Outcome
  let C : ℝ := ∑ who : ι, ∑ ω : G.Outcome, |G.utility ω who|
  refine ⟨C, ?_⟩
  intro σ who
  have hbd : ∀ ω : G.Outcome,
      |G.utility ω who| ≤ ∑ ω : G.Outcome, |G.utility ω who| := by
    intro ω
    exact Finset.single_le_sum (fun x _ => abs_nonneg (G.utility x who))
      (Finset.mem_univ ω)
  have heu : |G.eu σ who| ≤ ∑ ω : G.Outcome, |G.utility ω who| :=
    G.eu_abs_le_of_bounded who hbd σ
  have hcoord :
      (∑ ω : G.Outcome, |G.utility ω who|) ≤ C := by
    exact Finset.single_le_sum
      (fun j _ => Finset.sum_nonneg fun ω _ => abs_nonneg (G.utility ω j))
      (Finset.mem_univ who)
  exact heu.trans hcoord

/-- For sufficiently patient players, any fixed positive continuation margin
dominates a bounded one-period gain. -/
theorem exists_discountFactor_threshold_one_step
    {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) :
    ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, δ₀ < δ → δ < 1 → (1 - δ) * M < δ * η := by
  let δ₀ : ℝ := M / (M + η)
  have hden_pos : 0 < M + η := by linarith
  refine ⟨δ₀, div_nonneg hM hden_pos.le, ?_, ?_⟩
  · rw [div_lt_one hden_pos]
    linarith
  · intro δ hδ _hδlt
    have hmul : M < δ * (M + η) := by
      exact (div_lt_iff₀ hden_pos).1 hδ
    nlinarith

/-- Strict coordinatewise domination over a finite player set has a uniform
positive slack. -/
theorem exists_pos_margin_of_mem_strictReservationSet [Finite ι]
    {r v : Payoff ι} (hv : v ∈ strictReservationSet r) :
    ∃ η : ℝ, 0 < η ∧ ∀ i, r i + η ≤ v i := by
  letI : Fintype ι := Fintype.ofFinite ι
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    let m : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i : ι => v i - r i)
    have hmpos : 0 < m := by
      rw [Finset.lt_inf'_iff]
      intro i _hi
      exact sub_pos.mpr (hv i)
    refine ⟨m / 2, half_pos hmpos, ?_⟩
    intro i
    have hmi : m ≤ v i - r i := Finset.inf'_le _ (Finset.mem_univ i)
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro i
    exact False.elim (hι ⟨i⟩)

/-- Strict individual rationality over a finite player set has a uniform
positive slack over the reservation vector. -/
theorem exists_pos_margin_of_mem_strictIndividuallyRationalPayoffSet
    (G : KernelGame ι) [Finite ι] {r v : Payoff ι}
    (hv : v ∈ G.strictIndividuallyRationalPayoffSet r) :
    ∃ η : ℝ, 0 < η ∧ ∀ i, r i + η ≤ v i :=
  exists_pos_margin_of_mem_strictReservationSet hv.2

/-- Public histories of realized period profiles before period `t`.

This is a perfect-public-monitoring profile-history model.  In ordinary
normal-form stage games these profiles are action profiles.  In compiled
`KernelGame`s they may instead be profiles of semantic strategies or policies.
In the final theorem, where `G` is a mixed extension, these public observations
are mixed-action profiles. -/
abbrev PublicHistory (G : KernelGame ι) (t : ℕ) : Type :=
  Fin t → Profile G

/-- A discounted repeated-game strategy: choose the next period's `G.Strategy i`
after every finite public profile history. -/
abbrev DiscountedRepeatedStrategy (G : KernelGame ι) (i : ι) : Type :=
  (t : ℕ) → G.PublicHistory t → G.Strategy i

/-- A repeated-game strategy profile. -/
abbrev DiscountedRepeatedProfile (G : KernelGame ι) : Type :=
  ∀ i, G.DiscountedRepeatedStrategy i

/-- Stationary repeated play of a fixed stage-game profile. -/
def stationaryDiscountedRepeatedProfile (G : KernelGame ι) (σ : Profile G) :
    G.DiscountedRepeatedProfile :=
  fun i _ _ => σ i

/-- Periodic repeated play of a finite cycle of stage-game profiles. -/
def periodicDiscountedRepeatedProfile (G : KernelGame ι)
    {n : ℕ} [NeZero n] (cycle : Fin n → Profile G) :
    G.DiscountedRepeatedProfile :=
  fun i t _ => cycle (Fin.ofNat n t) i

/-- The stage-profile path generated by a repeated-game strategy profile. -/
def discountedRepeatedPlay (G : KernelGame ι)
    (σ : G.DiscountedRepeatedProfile) : (t : ℕ) → Profile G
  | t => fun i => σ i t (fun k => discountedRepeatedPlay G σ k)
termination_by t => t
decreasing_by exact k.isLt

@[simp] theorem discountedRepeatedPlay_stationaryDiscountedRepeatedProfile
    (G : KernelGame ι) (σ : Profile G) (t : ℕ) :
    G.discountedRepeatedPlay (G.stationaryDiscountedRepeatedProfile σ) t = σ := by
  funext i
  simp [discountedRepeatedPlay, stationaryDiscountedRepeatedProfile]

@[simp] theorem discountedRepeatedPlay_periodicDiscountedRepeatedProfile
    (G : KernelGame ι) {n : ℕ} [NeZero n]
    (cycle : Fin n → Profile G) (t : ℕ) :
    G.discountedRepeatedPlay (G.periodicDiscountedRepeatedProfile cycle) t =
      cycle (Fin.ofNat n t) := by
  funext i
  simp [discountedRepeatedPlay, periodicDiscountedRepeatedProfile]

/-- Normalized discounted average payoff in the repeated game.

The definition is total for any real `δ`, as is customary in Lean, but the
mathematical discounted-payoff interpretation and all convergence/Nash lemmas
use the explicit hypotheses `0 ≤ δ` and `δ < 1`. -/
def discountedAveragePayoff (G : KernelGame ι) (δ : ℝ)
    (σ : G.DiscountedRepeatedProfile) (who : ι) : ℝ :=
  (1 - δ) * ∑' t : ℕ, δ ^ t * G.eu (G.discountedRepeatedPlay σ t) who

/-- Normalized discounted continuation payoff of an explicit stage-profile
stream, starting at period `start`.

As with `discountedAveragePayoff`, this is intended as a discounted payoff under
the side conditions `0 ≤ δ` and `δ < 1`. -/
def discountedContinuationPayoff (G : KernelGame ι) (δ : ℝ)
    (play : ℕ → Profile G) (start : ℕ) (who : ι) : ℝ :=
  (1 - δ) * ∑' k : ℕ, δ ^ k * G.eu (play (start + k)) who

/-- A repeated profile's discounted average is the zero-start continuation
payoff of its generated stage-profile stream. -/
theorem discountedAveragePayoff_eq_discountedContinuationPayoff_zero
    (G : KernelGame ι) (δ : ℝ) (σ : G.DiscountedRepeatedProfile) (who : ι) :
    G.discountedAveragePayoff δ σ who =
      G.discountedContinuationPayoff δ (fun t => G.discountedRepeatedPlay σ t) 0 who := by
  simp [discountedAveragePayoff, discountedContinuationPayoff]

/-- Discounted stage utilities are summable when stage utilities are uniformly
bounded and `δ ∈ [0,1)`. -/
theorem summable_discounted_stageEU_of_abs_bound (G : KernelGame ι)
    {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {σ : G.DiscountedRepeatedProfile}
    (who : ι) (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C) :
    Summable fun t : ℕ => δ ^ t * G.eu (G.discountedRepeatedPlay σ t) who := by
  have hgeom : Summable fun t : ℕ => C * δ ^ t :=
    (summable_geometric_of_lt_one hδ0 hδ1).mul_left C
  refine Summable.of_norm_bounded hgeom ?_
  intro t
  rw [Real.norm_eq_abs]
  calc
    |δ ^ t * G.eu (G.discountedRepeatedPlay σ t) who| =
        δ ^ t * |G.eu (G.discountedRepeatedPlay σ t) who| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0 t)]
    _ ≤ δ ^ t * C :=
        mul_le_mul_of_nonneg_left (hbd (G.discountedRepeatedPlay σ t))
          (pow_nonneg hδ0 t)
    _ = C * δ ^ t := by ring

/-- Discounted continuation utilities are summable when stage utilities are
uniformly bounded and `δ ∈ [0,1)`. -/
theorem summable_discounted_continuation_stageEU_of_abs_bound
    (G : KernelGame ι) {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (play : ℕ → Profile G) (start : ℕ) (who : ι)
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C) :
    Summable fun k : ℕ => δ ^ k * G.eu (play (start + k)) who := by
  have hgeom : Summable fun k : ℕ => C * δ ^ k :=
    (summable_geometric_of_lt_one hδ0 hδ1).mul_left C
  refine Summable.of_norm_bounded hgeom ?_
  intro k
  rw [Real.norm_eq_abs]
  calc
    |δ ^ k * G.eu (play (start + k)) who| =
        δ ^ k * |G.eu (play (start + k)) who| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0 k)]
    _ ≤ δ ^ k * C :=
        mul_le_mul_of_nonneg_left (hbd (play (start + k))) (pow_nonneg hδ0 k)
    _ = C * δ ^ k := by ring

/-- If every future stage payoff is at most `b`, then the normalized
continuation payoff is at most `b`. -/
theorem discountedContinuationPayoff_le_const_of_forall_stageEU_le
    (G : KernelGame ι) {δ C b : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (play : ℕ → Profile G) (start : ℕ) (who : ι)
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C)
    (hle : ∀ k : ℕ, G.eu (play (start + k)) who ≤ b) :
    G.discountedContinuationPayoff δ play start who ≤ b := by
  have hs := G.summable_discounted_continuation_stageEU_of_abs_bound
    hδ0 hδ1 play start who hbd
  have hconst : Summable fun k : ℕ => δ ^ k * b :=
    (summable_geometric_of_lt_one hδ0 hδ1).mul_right b
  have hsum :
      (∑' k : ℕ, δ ^ k * G.eu (play (start + k)) who) ≤
        ∑' k : ℕ, δ ^ k * b := by
    exact hs.tsum_le_tsum
      (fun k => mul_le_mul_of_nonneg_left (hle k) (pow_nonneg hδ0 k)) hconst
  have hone : 1 - δ ≠ 0 := by linarith
  calc
    G.discountedContinuationPayoff δ play start who ≤
        (1 - δ) * (∑' k : ℕ, δ ^ k * b) := by
      exact mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hδ1.le)
    _ = b := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1]
      field_simp [hone]

/-- Bellman split for normalized discounted continuation payoffs. -/
theorem discountedContinuationPayoff_eq_head_add
    (G : KernelGame ι) {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (play : ℕ → Profile G) (start : ℕ) (who : ι)
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C) :
    G.discountedContinuationPayoff δ play start who =
      (1 - δ) * G.eu (play start) who +
        δ * G.discountedContinuationPayoff δ play (start + 1) who := by
  let f : ℕ → ℝ := fun k => δ ^ k * G.eu (play (start + k)) who
  have hs : Summable f := by
    simpa [f] using G.summable_discounted_continuation_stageEU_of_abs_bound
      hδ0 hδ1 play start who hbd
  have hsplit : f 0 + (∑' k : ℕ, f (k + 1)) = ∑' k : ℕ, f k := by
    simpa using hs.sum_add_tsum_nat_add 1
  have htail : (∑' k : ℕ, f (k + 1)) =
      δ * ∑' k : ℕ, δ ^ k * G.eu (play (start + 1 + k)) who := by
    calc
      (∑' k : ℕ, f (k + 1)) =
          ∑' k : ℕ, δ * (δ ^ k * G.eu (play (start + 1 + k)) who) := by
        apply tsum_congr
        intro k
        have hnat : start + (k + 1) = start + 1 + k := by omega
        dsimp [f]
        rw [pow_succ, hnat]
        ring
      _ = δ * ∑' k : ℕ, δ ^ k * G.eu (play (start + 1 + k)) who := by
        rw [tsum_mul_left]
  calc
    G.discountedContinuationPayoff δ play start who =
        (1 - δ) * ∑' k : ℕ, f k := by
      rfl
    _ = (1 - δ) * (f 0 + ∑' k : ℕ, f (k + 1)) := by
      rw [hsplit]
    _ = (1 - δ) * G.eu (play start) who +
        δ * G.discountedContinuationPayoff δ play (start + 1) who := by
      rw [htail]
      simp [discountedContinuationPayoff, f]
      ring

/-- Prefix comparison for continuation payoffs.  If two streams agree for `q`
periods from `start`, and the first stream's continuation at `start + q` is no
larger, then its continuation at `start` is no larger. -/
theorem discountedContinuationPayoff_le_of_prefix_eq_of_tail_le
    (G : KernelGame ι) {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (play₁ play₂ : ℕ → Profile G) (start q : ℕ) (who : ι)
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C)
    (hpref : ∀ k < q, play₁ (start + k) = play₂ (start + k))
    (htail : G.discountedContinuationPayoff δ play₁ (start + q) who ≤
      G.discountedContinuationPayoff δ play₂ (start + q) who) :
    G.discountedContinuationPayoff δ play₁ start who ≤
      G.discountedContinuationPayoff δ play₂ start who := by
  revert start
  induction q with
  | zero =>
      intro start _hpref htail
      simpa using htail
  | succ q ih =>
      intro start hpref htail
      have hhead : play₁ start = play₂ start := by
        simpa using hpref 0 (Nat.succ_pos q)
      have htail' :
          G.discountedContinuationPayoff δ play₁ (start + 1 + q) who ≤
            G.discountedContinuationPayoff δ play₂ (start + 1 + q) who := by
        have htail_start : start + (q + 1) = start + 1 + q := by omega
        simpa [htail_start] using htail
      have hpref' : ∀ k < q, play₁ (start + 1 + k) = play₂ (start + 1 + k) := by
        intro k hk
        have hk' : k + 1 < q + 1 := Nat.succ_lt_succ hk
        have hnat : start + (k + 1) = start + 1 + k := by omega
        simpa [hnat] using hpref (k + 1) hk'
      have htail_from_next := ih (start + 1) hpref' htail'
      rw [G.discountedContinuationPayoff_eq_head_add hδ0 hδ1 play₁ start who hbd]
      rw [G.discountedContinuationPayoff_eq_head_add hδ0 hδ1 play₂ start who hbd]
      rw [hhead]
      exact add_le_add_right (mul_le_mul_of_nonneg_left htail_from_next hδ0) _

/-- Pointwise dominance of every realized stage payoff implies dominance of
normalized discounted payoffs. -/
theorem discountedAveragePayoff_le_of_forall_stageEU_le (G : KernelGame ι)
    {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {σ τ : G.DiscountedRepeatedProfile} (who : ι)
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C)
    (hle : ∀ t : ℕ,
      G.eu (G.discountedRepeatedPlay σ t) who ≤
        G.eu (G.discountedRepeatedPlay τ t) who) :
    G.discountedAveragePayoff δ σ who ≤ G.discountedAveragePayoff δ τ who := by
  have hsσ := G.summable_discounted_stageEU_of_abs_bound hδ0 hδ1 who hbd (σ := σ)
  have hsτ := G.summable_discounted_stageEU_of_abs_bound hδ0 hδ1 who hbd (σ := τ)
  have hsum :
      (∑' t : ℕ, δ ^ t * G.eu (G.discountedRepeatedPlay σ t) who) ≤
        ∑' t : ℕ, δ ^ t * G.eu (G.discountedRepeatedPlay τ t) who := by
    exact hsσ.tsum_le_tsum
      (fun t => mul_le_mul_of_nonneg_left (hle t) (pow_nonneg hδ0 t)) hsτ
  exact mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hδ1.le)

/-- Normalized discounted payoff of a stationary repeated profile is the stage
payoff, for discount factors in `[0, 1)`. -/
theorem discountedAveragePayoff_stationaryDiscountedRepeatedProfile
    (G : KernelGame ι) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (σ : Profile G) (who : ι) :
    G.discountedAveragePayoff δ (G.stationaryDiscountedRepeatedProfile σ) who =
      G.eu σ who := by
  have hne : 1 - δ ≠ 0 := by linarith
  simp [discountedAveragePayoff, tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1,
    hne]

/-- If one player deviates from a stationary repeated profile, every realized
stage profile is the stationary profile with only that player's current action
updated. -/
theorem discountedRepeatedPlay_update_stationaryDiscountedRepeatedProfile
    (G : KernelGame ι) [DecidableEq ι] (σ : Profile G) (who : ι)
    (dev : G.DiscountedRepeatedStrategy who) (t : ℕ) :
    G.discountedRepeatedPlay
        (Function.update (G.stationaryDiscountedRepeatedProfile σ) who dev) t =
      Function.update σ who
        (dev t (fun k => G.discountedRepeatedPlay
          (Function.update (G.stationaryDiscountedRepeatedProfile σ) who dev) k)) := by
  funext i
  by_cases hi : i = who
  · subst hi
    rw [discountedRepeatedPlay]
    simp [Function.update]
  · simp [discountedRepeatedPlay, stationaryDiscountedRepeatedProfile, Function.update, hi]

/-- Nash equilibrium of the normalized discounted repeated game.

The equilibrium concept allows a unilateral deviation in the repeated-strategy
space: a player may replace their whole history-dependent repeated strategy.
Results using this predicate supply the discount-factor assumptions needed for
the payoff comparison. -/
def IsDiscountedRepeatedNash (G : KernelGame ι) [DecidableEq ι] (δ : ℝ)
    (σ : G.DiscountedRepeatedProfile) : Prop :=
  ∀ who (dev : G.DiscountedRepeatedStrategy who),
    G.discountedAveragePayoff δ σ who ≥
      G.discountedAveragePayoff δ (Function.update σ who dev) who

/-- Repeating a stage-game Nash profile stationarily is a Nash equilibrium of
the discounted repeated game. -/
theorem stationaryDiscountedRepeatedProfile_isDiscountedRepeatedNash_of_isNash
    (G : KernelGame ι) [DecidableEq ι] [Finite G.Outcome]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {σ : Profile G} (hN : G.IsNash σ) :
    G.IsDiscountedRepeatedNash δ (G.stationaryDiscountedRepeatedProfile σ) := by
  intro who dev
  obtain ⟨C, hC⟩ := G.exists_stageEU_abs_bound_of_finite_outcome who
  exact G.discountedAveragePayoff_le_of_forall_stageEU_le
    (σ := Function.update (G.stationaryDiscountedRepeatedProfile σ) who dev)
    (τ := G.stationaryDiscountedRepeatedProfile σ)
    hδ0 hδ1 who hC (fun t => by
      rw [G.discountedRepeatedPlay_update_stationaryDiscountedRepeatedProfile σ who dev t]
      rw [G.discountedRepeatedPlay_stationaryDiscountedRepeatedProfile σ t]
      exact hN who _)


end KernelGame

end GameTheory
