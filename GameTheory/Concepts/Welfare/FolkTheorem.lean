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

/-!
# Observable-Mixed-Action Discounted Folk Theorem Machinery

This file develops the payoff-set and repeated-game ingredients used for a
discounted Folk theorem over `KernelGame`s:
feasible payoffs, opponent minmax punishment values, individually-rational
payoff regions, finite-cycle approximation, periodic discounted payoffs, and
trigger strategies.

The repeated-game semantics in this file are intentionally direct.  A period
action profile is a `Profile G`, public histories record the realized sequence
of such profiles, and a repeated strategy chooses its next `G.Strategy i` from
that public profile history.  For a normal-form stage game this is the usual
perfect-public-monitoring action-history model.  For a `KernelGame` obtained by
compiling a richer language, `G.Strategy i` may already be a contingent
strategy or policy; then this construction repeats and publicly observes those
semantic stage strategies, not the source-language internal histories.

The main theorem below is stated for the repeated game over `G.mixedExtension`.
Thus each period action is a mixed stage strategy, `PMF (G.Strategy i)`, and the
mixed-action profile itself is publicly observed.  This is an observable
mixed-action formulation of the discounted Folk theorem.  It deliberately avoids
adding sampled action histories, private randomization histories, or public
correlation devices to the language layer.  Within that model, every strictly
individually-rational feasible payoff of the original stage game is approached
by Nash payoffs of sufficiently patient discounted repeated games.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- The expected-utility payoff vector induced by a pure profile. -/
def payoffVector (G : KernelGame ι) (σ : Profile G) : Payoff ι :=
  fun i => G.eu σ i

@[simp] theorem payoffVector_apply (G : KernelGame ι) (σ : Profile G) (i : ι) :
    G.payoffVector σ i = G.eu σ i :=
  rfl

/-- Payoff vectors attainable by pure strategy profiles of the stage game. -/
def purePayoffSet (G : KernelGame ι) : Set (Payoff ι) :=
  Set.range G.payoffVector

theorem mem_purePayoffSet (G : KernelGame ι) (v : Payoff ι) :
    v ∈ G.purePayoffSet ↔ ∃ σ : Profile G, G.payoffVector σ = v := by
  simp [purePayoffSet]

/-- Feasible payoffs: convex combinations of pure-profile payoff vectors. -/
def feasibleSet (G : KernelGame ι) : Set (Payoff ι) :=
  convexHull ℝ G.purePayoffSet

theorem payoffVector_mem_feasibleSet (G : KernelGame ι) (σ : Profile G) :
    G.payoffVector σ ∈ G.feasibleSet := by
  exact subset_convexHull ℝ G.purePayoffSet ⟨σ, rfl⟩

/-- Any feasible payoff has a finite convex-combination representation by
pure-profile payoff vectors. -/
theorem exists_fintype_weighted_profiles_of_mem_feasibleSet
    (G : KernelGame ι) {v : Payoff ι} (hv : v ∈ G.feasibleSet) :
    ∃ (κ : Type) (_ : Fintype κ) (w : κ → ℝ) (σ : κ → Profile G),
      (∀ k, 0 ≤ w k) ∧
      (∑ k, w k = 1) ∧
      (∑ k, w k • G.payoffVector (σ k) = v) := by
  rw [feasibleSet] at hv
  rcases (mem_convexHull_iff_exists_fintype (R := ℝ)
      (s := G.purePayoffSet) (x := v)).1 hv with
    ⟨κ, hκ, w, z, hw_nonneg, hw_sum, hz, hz_sum⟩
  letI : Fintype κ := hκ
  choose σ hσ using fun k => (G.mem_purePayoffSet (z k)).1 (hz k)
  refine ⟨κ, hκ, w, σ, hw_nonneg, hw_sum, ?_⟩
  calc
    ∑ k, w k • G.payoffVector (σ k) = ∑ k, w k • z k := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [hσ k]
    _ = v := hz_sum

/-- Coordinate form of `exists_fintype_weighted_profiles_of_mem_feasibleSet`. -/
theorem exists_fintype_weighted_profiles_apply_of_mem_feasibleSet
    (G : KernelGame ι) {v : Payoff ι} (hv : v ∈ G.feasibleSet) :
    ∃ (κ : Type) (_ : Fintype κ) (w : κ → ℝ) (σ : κ → Profile G),
      (∀ k, 0 ≤ w k) ∧
      (∑ k, w k = 1) ∧
      (∀ i, ∑ k, w k * G.eu (σ k) i = v i) := by
  rcases G.exists_fintype_weighted_profiles_of_mem_feasibleSet hv with
    ⟨κ, hκ, w, σ, hw_nonneg, hw_sum, hsum⟩
  letI : Fintype κ := hκ
  refine ⟨κ, hκ, w, σ, hw_nonneg, hw_sum, ?_⟩
  intro i
  have happly := congrArg (fun u : Payoff ι => u i) hsum
  simpa [payoffVector, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using happly

/-- Payoffs weakly above a reservation/security vector. -/
def weakReservationSet (r : Payoff ι) : Set (Payoff ι) :=
  {v | ∀ i, r i ≤ v i}

/-- Payoffs strictly above a reservation/security vector. -/
def strictReservationSet (r : Payoff ι) : Set (Payoff ι) :=
  {v | ∀ i, r i < v i}

/-- Feasible payoffs satisfying weak individual rationality. -/
def individuallyRationalPayoffSet (G : KernelGame ι) (r : Payoff ι) : Set (Payoff ι) :=
  G.feasibleSet ∩ weakReservationSet r

/-- Feasible payoffs satisfying strict individual rationality. -/
def strictIndividuallyRationalPayoffSet (G : KernelGame ι) (r : Payoff ι) : Set (Payoff ι) :=
  G.feasibleSet ∩ strictReservationSet r

/-- The finite pure-strategy security vector. -/
def pureSecurityVector (G : KernelGame ι) [Fintype (Profile G)] [Nonempty (Profile G)]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] : Payoff ι :=
  fun i => G.securityLevel i

/-- The mixed-strategy security vector, using the order-theoretic security level
of the mixed extension. -/
def mixedSecurityVector (G : KernelGame ι) [Fintype ι] : Payoff ι :=
  fun i => G.mixedExtension.securityLevelSup i

/-- Opponent profiles for punishing `who`: a strategy for every other player. -/
abbrev OpponentProfile (G : KernelGame ι) (who : ι) : Type :=
  ∀ j : {j : ι // j ≠ who}, G.Strategy j

/-- Combine player `who`'s strategy with an opponent profile. -/
def profileWithOpponent (G : KernelGame ι) [DecidableEq ι] (who : ι)
    (own : G.Strategy who) (opp : G.OpponentProfile who) : Profile G :=
  fun j =>
    if h : j = who then
      h ▸ own
    else
      opp ⟨j, h⟩

@[simp] theorem profileWithOpponent_self (G : KernelGame ι) [DecidableEq ι] (who : ι)
    (own : G.Strategy who) (opp : G.OpponentProfile who) :
    G.profileWithOpponent who own opp who = own := by
  simp [profileWithOpponent]

@[simp] theorem profileWithOpponent_ne (G : KernelGame ι) [DecidableEq ι] {who j : ι}
    (h : j ≠ who) (own : G.Strategy who) (opp : G.OpponentProfile who) :
    G.profileWithOpponent who own opp j = opp ⟨j, h⟩ := by
  simp [profileWithOpponent, h]

/-- A profile whose other coordinates match an opponent profile is exactly the
profile assembled from its own coordinate and those opponents. -/
theorem eq_profileWithOpponent_of_forall_ne (G : KernelGame ι) [DecidableEq ι]
    (who : ι) (ρ : Profile G) (opp : G.OpponentProfile who)
    (hopp : ∀ (j : ι) (h : j ≠ who), ρ j = opp ⟨j, h⟩) :
    ρ = G.profileWithOpponent who (ρ who) opp := by
  ext j
  by_cases hj : j = who
  · subst hj
    simp
  · rw [hopp j hj]
    simp [profileWithOpponent, hj]

/-- Best payoff player `who` can get against a fixed opponent profile. -/
def bestResponseValueAgainstOpponents (G : KernelGame ι) [DecidableEq ι] (who : ι)
    (opp : G.OpponentProfile who) : ℝ :=
  ⨆ own : G.Strategy who, G.eu (G.profileWithOpponent who own opp) who

/-- Opponent-enforced minmax level: the lowest best-response value the other
players can impose on `who`.

This is the punishment value used in the Folk theorem, as opposed to
`securityLevelSup`, which is `who`'s own maximin guarantee. -/
def opponentMinmaxLevel (G : KernelGame ι) [DecidableEq ι] (who : ι) : ℝ :=
  ⨅ opp : G.OpponentProfile who, G.bestResponseValueAgainstOpponents who opp

/-- The vector of opponent-enforced minmax punishment values. -/
def opponentMinmaxVector (G : KernelGame ι) [DecidableEq ι] : Payoff ι :=
  fun i => G.opponentMinmaxLevel i

/-- The opponent-enforced minmax is approximated from above by some opponent
profile. This is the order-theoretic selection step needed for approximate
punishments. -/
theorem exists_opponentProfile_bestResponseValue_lt_add (G : KernelGame ι)
    [DecidableEq ι] (who : ι) [Nonempty (G.OpponentProfile who)]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ opp : G.OpponentProfile who,
      G.bestResponseValueAgainstOpponents who opp < G.opponentMinmaxLevel who + ε := by
  have hlt : G.opponentMinmaxLevel who < G.opponentMinmaxLevel who + ε :=
    lt_add_of_pos_right _ hε
  simpa [opponentMinmaxLevel] using
    (exists_lt_of_ciInf_lt (f := fun opp : G.OpponentProfile who =>
      G.bestResponseValueAgainstOpponents who opp) hlt)

/-- A realized payoff against fixed opponents is bounded by the best-response
value against those opponents. -/
theorem eu_profileWithOpponent_le_bestResponseValueAgainstOpponents
    (G : KernelGame ι) [DecidableEq ι] (who : ι)
    (opp : G.OpponentProfile who)
    (hbdd : BddAbove (Set.range fun own : G.Strategy who =>
      G.eu (G.profileWithOpponent who own opp) who))
    (own : G.Strategy who) :
    G.eu (G.profileWithOpponent who own opp) who ≤
      G.bestResponseValueAgainstOpponents who opp := by
  exact le_ciSup hbdd own

/-- If a punishment opponent profile has low best-response value, then it caps
every one-shot action of the punished player. -/
theorem eu_profileWithOpponent_lt_of_bestResponseValue_lt
    (G : KernelGame ι) [DecidableEq ι] (who : ι)
    (opp : G.OpponentProfile who) {b : ℝ}
    (hbdd : BddAbove (Set.range fun own : G.Strategy who =>
      G.eu (G.profileWithOpponent who own opp) who))
    (hopp : G.bestResponseValueAgainstOpponents who opp < b)
    (own : G.Strategy who) :
    G.eu (G.profileWithOpponent who own opp) who < b :=
  (G.eu_profileWithOpponent_le_bestResponseValueAgainstOpponents who opp hbdd own).trans_lt hopp

/-- Choose approximate punishment opponent profiles for every player. -/
theorem exists_approx_punishmentProfiles (G : KernelGame ι) [DecidableEq ι]
    [∀ who, Nonempty (G.OpponentProfile who)]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ punish : ∀ who, G.OpponentProfile who,
      ∀ who,
        G.bestResponseValueAgainstOpponents who (punish who) <
          G.opponentMinmaxLevel who + ε := by
  choose punish hpunish using
    fun who => G.exists_opponentProfile_bestResponseValue_lt_add who hε
  exact ⟨punish, hpunish⟩

/-- Opponent profiles in the mixed extension are nonempty when every pure
strategy space is nonempty. -/
theorem nonempty_mixedExtension_opponentProfile (G : KernelGame ι) [Fintype ι]
    [∀ i, Nonempty (G.Strategy i)] (who : ι) :
    Nonempty (G.mixedExtension.OpponentProfile who) := by
  classical
  exact ⟨fun j => PMF.pure (Classical.arbitrary (G.Strategy j))⟩

/-- The mixed extension has the same outcome carrier as the original game. -/
theorem finite_mixedExtension_outcome (G : KernelGame ι) [Fintype ι]
    [Finite G.Outcome] :
    Finite G.mixedExtension.Outcome := by
  change Finite G.Outcome
  infer_instance

/-- Mixed-extension strategy spaces are nonempty when pure strategy spaces are. -/
theorem nonempty_mixedExtension_strategy (G : KernelGame ι) [Fintype ι]
    [∀ i, Nonempty (G.Strategy i)] (i : ι) :
    Nonempty (G.mixedExtension.Strategy i) := by
  classical
  exact ⟨PMF.pure (Classical.arbitrary (G.Strategy i))⟩

/-- Embed a pure stage-game profile as a mixed profile of the mixed extension. -/
def pureMixedProfile (G : KernelGame ι) [Fintype ι] (σ : Profile G) :
    Profile G.mixedExtension :=
  fun i => PMF.pure (σ i)

@[simp] theorem pureMixedProfile_apply (G : KernelGame ι) [Fintype ι]
    (σ : Profile G) (i : ι) :
    G.pureMixedProfile σ i = PMF.pure (σ i) :=
  rfl

/-- Pure profiles embedded in the mixed extension preserve expected utility. -/
theorem mixedExtension_eu_pureMixedProfile (G : KernelGame ι) [Fintype ι]
    (σ : Profile G) (who : ι) :
    G.mixedExtension.eu (G.pureMixedProfile σ) who = G.eu σ who := by
  simp only [mixedExtension, eu]
  change Math.Probability.expect
      ((Math.PMFProduct.pmfPi (fun i => (PMF.pure (σ i) : PMF (G.Strategy i)))).bind
        G.outcomeKernel) (fun ω => G.utility ω who) =
    Math.Probability.expect (G.outcomeKernel σ) (fun ω => G.utility ω who)
  rw [Math.PMFProduct.pmfPi_pure, PMF.pure_bind]

/-- Payoff vectors are preserved by embedding pure profiles into the mixed
extension as Dirac mixed profiles. -/
theorem mixedExtension_payoffVector_pureMixedProfile (G : KernelGame ι) [Fintype ι]
    (σ : Profile G) :
    G.mixedExtension.payoffVector (G.pureMixedProfile σ) = G.payoffVector σ := by
  funext who
  exact G.mixedExtension_eu_pureMixedProfile σ who

/-- Every feasible payoff of the original game is feasible in the mixed
extension. -/
theorem feasibleSet_subset_mixedExtension_feasibleSet
    (G : KernelGame ι) [Fintype ι] :
    G.feasibleSet ⊆ G.mixedExtension.feasibleSet := by
  apply convexHull_mono
  intro v hv
  rcases hv with ⟨σ, rfl⟩
  exact ⟨G.pureMixedProfile σ, G.mixedExtension_payoffVector_pureMixedProfile σ⟩

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

/-- Equivalence between residues modulo a positive natural and `Fin n`, using
the canonical representative value. -/
def zmodFinEquiv (n : ℕ) [NeZero n] : ZMod n ≃ Fin n where
  toFun j := ⟨j.val, j.val_lt⟩
  invFun k := (k.val : ZMod n)
  left_inv j := by
    apply ZMod.val_injective n
    simp
  right_inv k := by
    ext
    simp [Nat.mod_eq_of_lt k.isLt]

/-- Adding a fixed offset modulo `n` is injective on `Fin n`. -/
theorem fin_rotate_injective (n : ℕ) [NeZero n] (start : ℕ) :
    Function.Injective (fun j : Fin n => Fin.ofNat n (start + j)) := by
  intro j k h
  apply Fin.ext
  have hval : (start + (j : ℕ)) % n = (start + (k : ℕ)) % n := by
    simpa [Fin.ofNat] using congrArg Fin.val h
  have hz : ((j : ℕ) : ZMod n) = ((k : ℕ) : ZMod n) := by
    have hzk : ((start + (j : ℕ) : ℕ) : ZMod n) =
        ((start + (k : ℕ) : ℕ) : ZMod n) := by
      rw [ZMod.natCast_eq_natCast_iff']
      exact hval
    have hzk' : ((start : ZMod n) + ((j : ℕ) : ZMod n)) =
        ((start : ZMod n) + ((k : ℕ) : ZMod n)) := by
      simpa using hzk
    exact add_left_cancel hzk'
  have hmod : (j : ℕ) % n = (k : ℕ) % n := by
    rw [← ZMod.natCast_eq_natCast_iff']
    exact hz
  simpa [Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt k.isLt] using hmod

/-- The permutation of cycle phases induced by adding `start` modulo `n`. -/
def finRotateEquiv (n : ℕ) [NeZero n] (start : ℕ) : Fin n ≃ Fin n :=
  Equiv.ofBijective (fun j : Fin n => Fin.ofNat n (start + j))
    ⟨fin_rotate_injective n start,
      (Finite.injective_iff_surjective.mp (fin_rotate_injective n start))⟩

@[simp] theorem finRotateEquiv_apply (n : ℕ) [NeZero n] (start : ℕ) (j : Fin n) :
    finRotateEquiv n start j = Fin.ofNat n (start + j) :=
  rfl

/-- Rotating a finite cycle does not change its finite sum. -/
theorem sum_fin_rotate {n : ℕ} [NeZero n] (start : ℕ) (f : Fin n → ℝ) :
    (∑ j : Fin n, f (Fin.ofNat n (start + j))) = ∑ j : Fin n, f j := by
  exact Fintype.sum_equiv (finRotateEquiv n start)
    (fun j : Fin n => f (Fin.ofNat n (start + j))) f (fun j => by simp)

/-- Exact normalized discounted payoff of a periodic repeated profile.  The
discounted weights over the cycle phases are proportional to `δ ^ phase`. -/
theorem discountedAveragePayoff_periodicDiscountedRepeatedProfile_eq
    (G : KernelGame ι) [Finite G.Outcome] {n : ℕ} [NeZero n]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (cycle : Fin n → Profile G) (who : ι) :
    G.discountedAveragePayoff δ (G.periodicDiscountedRepeatedProfile cycle) who =
      (∑ j : Fin n, δ ^ (j : ℕ) * G.eu (cycle j) who) /
        (∑ j : Fin n, δ ^ (j : ℕ)) := by
  obtain ⟨C, hC⟩ := G.exists_stageEU_abs_bound_of_finite_outcome who
  let σ : G.DiscountedRepeatedProfile := G.periodicDiscountedRepeatedProfile cycle
  have hs : Summable fun t : ℕ => δ ^ t * G.eu (G.discountedRepeatedPlay σ t) who :=
    G.summable_discounted_stageEU_of_abs_bound hδ0 hδ1 who hC (σ := σ)
  have hpow : δ ^ n < 1 := pow_lt_one₀ hδ0 hδ1 (NeZero.ne n)
  have hden_pos : 0 < ∑ j : Fin n, δ ^ (j : ℕ) := by
    have hle : (1 : ℝ) ≤ ∑ j : Fin n, δ ^ (j : ℕ) := by
      have hsingle := Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin n)))
        (f := fun j : Fin n => δ ^ (j : ℕ))
        (fun j _ => pow_nonneg hδ0 (j : ℕ)) (Finset.mem_univ (0 : Fin n))
      simpa using hsingle
    exact zero_lt_one.trans_le hle
  have hden_ne : (∑ j : Fin n, δ ^ (j : ℕ)) ≠ 0 := ne_of_gt hden_pos
  have hgeom : (∑ j : Fin n, δ ^ (j : ℕ)) * (1 - δ) = 1 - δ ^ n := by
    simpa [Finset.sum_range] using (geom_sum_mul_of_le_one hδ1.le n)
  have hone : 1 - δ ≠ 0 := by linarith
  have hsplit :
      (∑' t : ℕ, δ ^ t * G.eu (G.discountedRepeatedPlay σ t) who) =
        ∑ j : ZMod n, ∑' m : ℕ,
          δ ^ (j.val + n * m) * G.eu (cycle ⟨j.val, j.val_lt⟩) who := by
    rw [Nat.sumByResidueClasses hs n]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    apply tsum_congr
    intro m
    subst σ
    rw [G.discountedRepeatedPlay_periodicDiscountedRepeatedProfile]
    congr 2
    ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt j.val_lt]
  have hinner : ∀ j : ZMod n,
      (∑' m : ℕ, δ ^ (j.val + n * m) * G.eu (cycle ⟨j.val, j.val_lt⟩) who) =
        (δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who) * (1 - δ ^ n)⁻¹ := by
    intro j
    calc
      (∑' m : ℕ, δ ^ (j.val + n * m) * G.eu (cycle ⟨j.val, j.val_lt⟩) who) =
          ∑' m : ℕ,
            (δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who) * (δ ^ n) ^ m := by
        apply tsum_congr
        intro m
        rw [pow_add, pow_mul]
        ring
      _ = (δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who) *
          (∑' m : ℕ, (δ ^ n) ^ m) := by
        rw [tsum_mul_left]
      _ = (δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who) *
          (1 - δ ^ n)⁻¹ := by
        rw [tsum_geometric_of_lt_one (pow_nonneg hδ0 n) hpow]
  have hzsum :
      (∑ j : ZMod n, δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who) =
        ∑ j : Fin n, δ ^ (j : ℕ) * G.eu (cycle j) who := by
    exact Fintype.sum_equiv (zmodFinEquiv n)
      (fun j : ZMod n => δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who)
      (fun j : Fin n => δ ^ (j : ℕ) * G.eu (cycle j) who)
      (fun j => rfl)
  calc
    G.discountedAveragePayoff δ (G.periodicDiscountedRepeatedProfile cycle) who =
        (1 - δ) * (∑ j : ZMod n,
          (δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who) * (1 - δ ^ n)⁻¹) := by
      simp only [discountedAveragePayoff]
      rw [show (G.periodicDiscountedRepeatedProfile cycle) = σ from rfl]
      rw [hsplit]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => hinner j)
    _ = (1 - δ) * ((∑ j : ZMod n,
          δ ^ j.val * G.eu (cycle ⟨j.val, j.val_lt⟩) who) * (1 - δ ^ n)⁻¹) := by
      rw [Finset.sum_mul]
    _ = (∑ j : Fin n, δ ^ (j : ℕ) * G.eu (cycle j) who) /
        (∑ j : Fin n, δ ^ (j : ℕ)) := by
      rw [hzsum]
      rw [← hgeom]
      field_simp [hden_ne, hone]

/-- Discounted continuation of a periodic path from any start period is the
discounted average of the corresponding phase-rotated cycle. -/
theorem discountedContinuationPayoff_periodicPath_eq
    (G : KernelGame ι) [Finite G.Outcome] {n : ℕ} [NeZero n]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (cycle : Fin n → Profile G) (start : ℕ) (who : ι) :
    G.discountedContinuationPayoff δ (fun t => cycle (Fin.ofNat n t)) start who =
      (∑ j : Fin n, δ ^ (j : ℕ) *
          G.eu (cycle (Fin.ofNat n (start + j))) who) /
        (∑ j : Fin n, δ ^ (j : ℕ)) := by
  let rotated : Fin n → Profile G := fun j => cycle (Fin.ofNat n (start + j))
  have hcont_avg :
      G.discountedContinuationPayoff δ (fun t => cycle (Fin.ofNat n t)) start who =
        G.discountedAveragePayoff δ (G.periodicDiscountedRepeatedProfile rotated) who := by
    simp only [discountedContinuationPayoff, discountedAveragePayoff]
    congr 1
    apply tsum_congr
    intro k
    congr 2
    unfold rotated
    ext
    simp [Fin.ofNat, Nat.add_mod]
  rw [hcont_avg]
  rw [G.discountedAveragePayoff_periodicDiscountedRepeatedProfile_eq hδ0 hδ1 rotated who]

/-- Finite discounted phase weights converge to uniform cycle weights as
`δ → 1` from below. -/
theorem exists_discountFactor_threshold_weighted_cycle_average
    {n : ℕ} [NeZero n] (a : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, δ₀ < δ → δ < 1 →
        |(∑ j : Fin n, δ ^ (j : ℕ) * a j) / (∑ j : Fin n, δ ^ (j : ℕ)) -
          (n : ℝ)⁻¹ * ∑ j : Fin n, a j| < ε := by
  let F : ℝ → ℝ := fun δ =>
    (∑ j : Fin n, δ ^ (j : ℕ) * a j) / (∑ j : Fin n, δ ^ (j : ℕ))
  have hden1 : (∑ j : Fin n, (1 : ℝ) ^ (j : ℕ)) ≠ 0 := by
    simp [NeZero.ne n]
  have hcont : ContinuousAt F 1 := by
    dsimp [F]
    apply ContinuousAt.div
    · exact (continuous_finsetSum (Finset.univ : Finset (Fin n)) (fun j _ =>
        (continuous_id.pow (j : ℕ)).mul continuous_const)).continuousAt
    · exact (continuous_finsetSum (Finset.univ : Finset (Fin n)) (fun j _ =>
        continuous_id.pow (j : ℕ))).continuousAt
    · exact hden1
  have hF1 : F 1 = (n : ℝ)⁻¹ * ∑ j : Fin n, a j := by
    dsimp [F]
    simp [Finset.sum_const, nsmul_eq_mul]
    field_simp [Nat.cast_ne_zero.mpr (NeZero.ne n)]
  rcases (Metric.tendsto_nhds_nhds.1 hcont) ε hε with ⟨d, hdpos, hd⟩
  let r : ℝ := min d 1
  have hrpos : 0 < r := lt_min hdpos zero_lt_one
  have hrle_d : r ≤ d := min_le_left d 1
  have hrle_one : r ≤ 1 := min_le_right d 1
  refine ⟨1 - r / 2, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · intro δ hδ0 hδ1
    have hdist : dist δ 1 < d := by
      rw [Real.dist_eq]
      have hδle : δ ≤ 1 := hδ1.le
      rw [abs_of_nonpos (sub_nonpos.mpr hδle)]
      nlinarith
    have hclose := hd hdist
    rw [Real.dist_eq] at hclose
    simpa [F, hF1] using hclose

/-- Combine finitely many lower-bound discount thresholds into one common
threshold. -/
theorem exists_common_discountFactor_threshold_of_finite
    {α : Type} [Finite α] {P : α → ℝ → Prop}
    (hP : ∀ a : α, ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, δ₀ < δ → δ < 1 → P a δ) :
    ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, δ₀ < δ → δ < 1 → ∀ a : α, P a δ := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  choose d hd0 hd1 hdP using hP
  by_cases hne : (Finset.univ : Finset α).Nonempty
  · let δ₀ : ℝ := (Finset.univ : Finset α).sup' hne d
    refine ⟨δ₀, ?_, ?_, ?_⟩
    · rcases hne with ⟨a0, ha0⟩
      exact (hd0 a0).trans (Finset.le_sup' d ha0)
    · rw [Finset.sup'_lt_iff]
      intro a _ha
      exact hd1 a
    · intro δ hδ hδ1 a
      exact hdP a δ ((Finset.le_sup' d (Finset.mem_univ a)).trans_lt hδ) hδ1
  · refine ⟨0, le_rfl, zero_lt_one, ?_⟩
    intro _δ _hδ _hδ1 a
    exact False.elim (hne ⟨a, Finset.mem_univ a⟩)

/-- For any fixed cycle and start phase, the discounted continuation payoff of
the periodic path is close to the cycle average when `δ` is close enough to
one from below. -/
theorem exists_discountFactor_threshold_periodic_continuation_close_cycleAverage
    (G : KernelGame ι) [Finite G.Outcome] {n : ℕ} [NeZero n]
    (cycle : Fin n → Profile G) (start : ℕ) (who : ι)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, δ₀ < δ → δ < 1 →
        |G.discountedContinuationPayoff δ (fun t => cycle (Fin.ofNat n t)) start who -
          G.cycleAveragePayoff cycle who| < ε := by
  obtain ⟨δ₀, hδ₀0, hδ₀1, hδ₀⟩ :=
    exists_discountFactor_threshold_weighted_cycle_average
      (fun j : Fin n => G.eu (cycle (Fin.ofNat n (start + j))) who) hε
  refine ⟨δ₀, hδ₀0, hδ₀1, ?_⟩
  intro δ hδgt hδlt
  have hδnonneg : 0 ≤ δ := le_of_lt (hδ₀0.trans_lt hδgt)
  have hclose := hδ₀ δ hδgt hδlt
  have hsumrot :
      (∑ j : Fin n, G.eu (cycle (Fin.ofNat n (start + j))) who) =
        ∑ j : Fin n, G.eu (cycle j) who :=
    sum_fin_rotate start (fun j : Fin n => G.eu (cycle j) who)
  rw [hsumrot] at hclose
  rw [G.discountedContinuationPayoff_periodicPath_eq hδnonneg hδlt]
  simpa [cycleAveragePayoff] using hclose

/-- The periodic continuation closeness threshold can be chosen uniformly over
all players and all start periods. -/
theorem exists_discountFactor_threshold_periodic_all_continuations_close_cycleAverage
    (G : KernelGame ι) [Finite ι] [Finite G.Outcome] {n : ℕ} [NeZero n]
    (cycle : Fin n → Profile G) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, δ₀ < δ → δ < 1 → ∀ (who : ι) (start : ℕ),
        |G.discountedContinuationPayoff δ (fun t => cycle (Fin.ofNat n t)) start who -
          G.cycleAveragePayoff cycle who| < ε := by
  let α := ι × Fin n
  have hα : ∀ a : α, ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧
      ∀ δ : ℝ, δ₀ < δ → δ < 1 →
        |G.discountedContinuationPayoff δ (fun t => cycle (Fin.ofNat n t)) (a.2 : ℕ) a.1 -
          G.cycleAveragePayoff cycle a.1| < ε := by
    intro a
    exact G.exists_discountFactor_threshold_periodic_continuation_close_cycleAverage
      cycle (a.2 : ℕ) a.1 hε
  obtain ⟨δ₀, hδ₀0, hδ₀1, hδ₀⟩ :=
    exists_common_discountFactor_threshold_of_finite hα
  refine ⟨δ₀, hδ₀0, hδ₀1, ?_⟩
  intro δ hδgt hδlt who start
  have hphase := hδ₀ δ hδgt hδlt (who, Fin.ofNat n start)
  have hstart :
      G.discountedContinuationPayoff δ (fun t => cycle (Fin.ofNat n t)) start who =
        G.discountedContinuationPayoff δ
          (fun t => cycle (Fin.ofNat n t)) ((Fin.ofNat n start).val) who := by
    simp only [discountedContinuationPayoff]
    congr 1
    apply tsum_congr
    intro k
    congr 2
    ext
    simp [Fin.ofNat, Nat.add_mod]
  rw [hstart]
  exact hphase

/-- If two profiles differ, at least one player's coordinate differs. -/
theorem exists_profile_ne_coord (G : KernelGame ι) {σ τ : Profile G}
    (h : σ ≠ τ) :
    ∃ i, σ i ≠ τ i := by
  classical
  by_contra hnone
  apply h
  funext i
  exact not_not.mp (by
    intro hne
    exact hnone ⟨i, hne⟩)

/-- A chosen coordinate at which two profiles differ.  This is the public
deviator selected when the trigger strategy first observes an off-path
profile. -/
def profileMismatchPlayer (G : KernelGame ι) {σ τ : Profile G}
    (h : σ ≠ τ) : ι :=
  Classical.choose (G.exists_profile_ne_coord h)

theorem profileMismatchPlayer_spec (G : KernelGame ι) {σ τ : Profile G}
    (h : σ ≠ τ) :
    σ (G.profileMismatchPlayer h) ≠ τ (G.profileMismatchPlayer h) :=
  Classical.choose_spec (G.exists_profile_ne_coord h)

/-- If two profiles differ only possibly at `who`, the chosen mismatch player
is `who`. -/
theorem profileMismatchPlayer_eq_of_forall_ne_eq
    (G : KernelGame ι) {σ τ : Profile G}
    (who : ι) (h : σ ≠ τ)
    (hothers : ∀ j, j ≠ who → σ j = τ j) :
    G.profileMismatchPlayer h = who := by
  classical
  by_contra hne
  exact G.profileMismatchPlayer_spec h (hothers _ hne)

/-- Drop the last observation from a public history. -/
def historyInit (G : KernelGame ι) {t : ℕ}
    (hist : G.PublicHistory (t + 1)) : G.PublicHistory t :=
  fun k => hist ⟨k.1, Nat.lt_trans k.2 (Nat.lt_succ_self t)⟩

@[simp] theorem historyInit_apply (G : KernelGame ι) {t : ℕ}
    (hist : G.PublicHistory (t + 1)) (k : Fin t) :
    G.historyInit hist k =
      hist ⟨k.1, Nat.lt_trans k.2 (Nat.lt_succ_self t)⟩ :=
  rfl

/-- Trigger-strategy automaton state computed from a public history.

`none` means no off-path profile has been observed.  `some who` means the
first off-path profile was attributed to `who`, and punishments should continue
against `who`. -/
def triggerStatus (G : KernelGame ι) (path : ℕ → Profile G) :
    (t : ℕ) → G.PublicHistory t → Option ι
  | 0, _ => none
  | t + 1, hist => by
      classical
      exact
        match G.triggerStatus path t (G.historyInit hist) with
        | some who => some who
        | none =>
            if h : hist ⟨t, Nat.lt_succ_self t⟩ = path t then none
            else some (G.profileMismatchPlayer h)

/-- The one-period profile prescribed by the trigger automaton.

In punishment state, all players other than the identified deviator play the
chosen punishment opponent profile.  The identified deviator's own coordinate is
filled by an arbitrary action, because unilateral-deviation comparisons replace
that coordinate by the deviator's strategy.  This is enough for the Nash trigger
argument below; it is not meant to encode a sequentially credible punishment
assessment for every off-path subgame. -/
def triggerProfileAt (G : KernelGame ι) [DecidableEq ι]
    [∀ i, Nonempty (G.Strategy i)] (path : ℕ → Profile G)
    (punish : ∀ who, G.OpponentProfile who) (t : ℕ)
    (status : Option ι) : Profile G :=
  fun i =>
    match status with
    | none => path t i
    | some who =>
        if h : i = who then Classical.arbitrary (G.Strategy i)
        else punish who ⟨i, h⟩

/-- The trigger repeated profile: follow `path` until the first public
mismatch, then punish the selected deviator forever. -/
def triggerDiscountedRepeatedProfile (G : KernelGame ι) [DecidableEq ι]
    [∀ i, Nonempty (G.Strategy i)] (path : ℕ → Profile G)
    (punish : ∀ who, G.OpponentProfile who) :
    G.DiscountedRepeatedProfile :=
  fun i t hist => G.triggerProfileAt path punish t (G.triggerStatus path t hist) i

theorem triggerStatus_eq_none_of_history_eq_path
    (G : KernelGame ι) (path : ℕ → Profile G) :
    ∀ {t : ℕ} (hist : G.PublicHistory t),
      (∀ k : Fin t, hist k = path k) → G.triggerStatus path t hist = none
  | 0, _hist, _hhist => by
      simp [triggerStatus]
  | t + 1, hist, hhist => by
      have hprev : G.triggerStatus path t (G.historyInit hist) = none := by
        apply G.triggerStatus_eq_none_of_history_eq_path path
        intro k
        exact hhist ⟨k.1, Nat.lt_trans k.2 (Nat.lt_succ_self t)⟩
      have hlast : hist ⟨t, Nat.lt_succ_self t⟩ = path t :=
        hhist ⟨t, Nat.lt_succ_self t⟩
      simp [triggerStatus, hprev, hlast]

/-- The trigger profile generates the intended path when nobody deviates. -/
theorem discountedRepeatedPlay_triggerDiscountedRepeatedProfile_eq_path
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who) :
    ∀ t : ℕ,
      G.discountedRepeatedPlay
          (G.triggerDiscountedRepeatedProfile path punish) t = path t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      funext i
      rw [discountedRepeatedPlay]
      have hstatus :
          G.triggerStatus path t
              (fun k =>
                G.discountedRepeatedPlay
                  (G.triggerDiscountedRepeatedProfile path punish) k) = none := by
        apply G.triggerStatus_eq_none_of_history_eq_path
        intro k
        exact ih k k.2
      simp [triggerDiscountedRepeatedProfile, triggerProfileAt, hstatus]

/-- The trigger profile's discounted payoff is the discounted payoff of its
intended path, since no deviation occurs on its own generated play. -/
theorem discountedAveragePayoff_triggerDiscountedRepeatedProfile_eq_path
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (δ : ℝ) (who : ι) :
    G.discountedAveragePayoff δ (G.triggerDiscountedRepeatedProfile path punish) who =
      (1 - δ) * ∑' t : ℕ, δ ^ t * G.eu (path t) who := by
  simp [discountedAveragePayoff,
    G.discountedRepeatedPlay_triggerDiscountedRepeatedProfile_eq_path path punish]

/-- For a periodic intended path, the trigger profile has the same discounted
payoff as the stationary periodic profile. -/
theorem discountedAveragePayoff_triggerPeriodicDiscountedRepeatedProfile_eq
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    {n : ℕ} [NeZero n] (cycle : Fin n → Profile G)
    (punish : ∀ who, G.OpponentProfile who) (δ : ℝ) (who : ι) :
    G.discountedAveragePayoff δ
        (G.triggerDiscountedRepeatedProfile (fun t => cycle (Fin.ofNat n t)) punish) who =
      G.discountedAveragePayoff δ (G.periodicDiscountedRepeatedProfile cycle) who := by
  calc
    G.discountedAveragePayoff δ
        (G.triggerDiscountedRepeatedProfile (fun t => cycle (Fin.ofNat n t)) punish) who =
        (1 - δ) * ∑' t : ℕ, δ ^ t * G.eu (cycle (Fin.ofNat n t)) who := by
      rw [G.discountedAveragePayoff_triggerDiscountedRepeatedProfile_eq_path]
    _ = G.discountedAveragePayoff δ (G.periodicDiscountedRepeatedProfile cycle) who := by
      simp [discountedAveragePayoff]

/-- Before the trigger has fired, a unilateral deviation by `who` leaves every
other player's realized action on the intended path. -/
theorem discountedRepeatedPlay_update_triggerDiscountedRepeatedProfile_ne_of_status_none
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.DiscountedRepeatedStrategy who) {t : ℕ}
    (hstatus :
      G.triggerStatus path t
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) = none)
    {j : ι} (hj : j ≠ who) :
    G.discountedRepeatedPlay
        (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) t j =
      path t j := by
  rw [discountedRepeatedPlay]
  simp [triggerDiscountedRepeatedProfile, triggerProfileAt, Function.update, hj, hstatus]

/-- If the trigger is still off both before and after period `t`, then the
realized period-`t` profile is exactly the intended path profile. -/
theorem discountedRepeatedPlay_update_trigger_eq_path_of_status_none_succ
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.DiscountedRepeatedStrategy who) {t : ℕ}
    (hstatus :
      G.triggerStatus path t
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) =
          none)
    (hstatus_succ :
      G.triggerStatus path (t + 1)
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) =
          none) :
    G.discountedRepeatedPlay
        (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) t =
      path t := by
  let σdev : G.DiscountedRepeatedProfile :=
    Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev
  let ρ : Profile G := G.discountedRepeatedPlay σdev t
  by_contra hne
  have hs_ne : ρ ≠ path t := by
    intro heq
    exact hne (by
      subst ρ
      exact heq)
  let hist : G.PublicHistory (t + 1) := fun k => G.discountedRepeatedPlay σdev k
  have hinit : G.historyInit hist =
      (fun k : Fin t => G.discountedRepeatedPlay σdev k) := by
    funext k
    rfl
  have hstatus' :
      G.triggerStatus path t (fun k : Fin t => G.discountedRepeatedPlay σdev k) =
        none := by
    simpa [σdev] using hstatus
  have hsucc_some :
      G.triggerStatus path (t + 1) hist = some (G.profileMismatchPlayer hs_ne) := by
    simp [triggerStatus, hinit, hstatus', hist, ρ, hs_ne]
  have hsucc_none' : G.triggerStatus path (t + 1) hist = none := by
    simpa [hist, σdev] using hstatus_succ
  rw [hsucc_some] at hsucc_none'
  simp at hsucc_none'

/-- If a unilateral deviation never fires the trigger, its realized play is the
intended path at every period. -/
theorem discountedRepeatedPlay_update_trigger_eq_path_of_forall_status_none
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.DiscountedRepeatedStrategy who)
    (hstatus : ∀ t : ℕ,
      G.triggerStatus path t
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) =
          none) :
    ∀ t : ℕ,
      G.discountedRepeatedPlay
          (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) t =
        path t := by
  intro t
  exact G.discountedRepeatedPlay_update_trigger_eq_path_of_status_none_succ
    path punish who dev (hstatus t) (hstatus (t + 1))

/-- If a unilateral deviation never fires the trigger, its discounted payoff is
the same as the trigger profile's on-path payoff. -/
theorem discountedAveragePayoff_update_trigger_eq_of_forall_status_none
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.DiscountedRepeatedStrategy who) (δ : ℝ)
    (hstatus : ∀ t : ℕ,
      G.triggerStatus path t
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) =
          none) :
    G.discountedAveragePayoff δ
        (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) who =
      G.discountedAveragePayoff δ (G.triggerDiscountedRepeatedProfile path punish) who := by
  rw [discountedAveragePayoff, discountedAveragePayoff]
  congr 1
  apply tsum_congr
  intro t
  rw [G.discountedRepeatedPlay_update_trigger_eq_path_of_forall_status_none
    path punish who dev hstatus t]
  rw [G.discountedRepeatedPlay_triggerDiscountedRepeatedProfile_eq_path path punish t]

/-- Along a unilateral deviation by `who`, the trigger status is either still
on-path or has identified `who` as the deviator. -/
theorem triggerStatus_update_triggerDiscountedRepeatedProfile_eq_none_or_self
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.DiscountedRepeatedStrategy who) :
    ∀ t : ℕ,
      G.triggerStatus path t
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) = none ∨
      G.triggerStatus path t
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) =
          some who := by
  intro t
  induction t with
  | zero =>
      left
      simp [triggerStatus]
  | succ t ih =>
      let σdev : G.DiscountedRepeatedProfile :=
        Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev
      let hist : G.PublicHistory (t + 1) := fun k => G.discountedRepeatedPlay σdev k
      have hinit : G.historyInit hist =
          (fun k : Fin t => G.discountedRepeatedPlay σdev k) := by
        funext k
        rfl
      change G.triggerStatus path (t + 1) hist = none ∨
        G.triggerStatus path (t + 1) hist = some who
      rcases ih with hprev | hprev
      · have hprev' :
            G.triggerStatus path t
              (fun k : Fin t => G.discountedRepeatedPlay σdev k) = none := by
          simpa [σdev] using hprev
        by_cases hlast : hist ⟨t, Nat.lt_succ_self t⟩ = path t
        · left
          simp [triggerStatus, hinit, hprev', hlast]
        · right
          have hplayer : G.profileMismatchPlayer hlast = who := by
            apply G.profileMismatchPlayer_eq_of_forall_ne_eq who
            intro j hj
            change G.discountedRepeatedPlay σdev t j = path t j
            subst σdev
            exact G.discountedRepeatedPlay_update_triggerDiscountedRepeatedProfile_ne_of_status_none
              path punish who dev hprev hj
          simp [triggerStatus, hinit, hprev', hlast, hplayer]
      · have hprev' :
            G.triggerStatus path t
              (fun k : Fin t => G.discountedRepeatedPlay σdev k) = some who := by
          simpa [σdev] using hprev
        right
        simp [triggerStatus, hinit, hprev']

/-- Every unilateral deviation either never fires the trigger, or has a least
period at which the trigger status is `some who`. -/
theorem triggerStatus_update_trigger_first_fire_or_never
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.DiscountedRepeatedStrategy who) :
    (∀ t : ℕ,
      G.triggerStatus path t
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) =
          none) ∨
    ∃ s : ℕ,
      G.triggerStatus path s
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) =
          some who ∧
      ∀ t < s,
        G.triggerStatus path t
          (fun k =>
            G.discountedRepeatedPlay
              (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) =
            none := by
  classical
  let status : ℕ → Option ι := fun t =>
    G.triggerStatus path t
      (fun k =>
        G.discountedRepeatedPlay
          (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k)
  by_cases hnever : ∀ t, status t = none
  · left
    exact hnever
  · right
    have hex : ∃ t, status t = some who := by
      push Not at hnever
      rcases hnever with ⟨t, ht⟩
      rcases G.triggerStatus_update_triggerDiscountedRepeatedProfile_eq_none_or_self
          path punish who dev t with hnone | hsome
      · exact False.elim (ht hnone)
      · exact ⟨t, hsome⟩
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    intro t ht
    have hnot : ¬ status t = some who := Nat.find_min hex ht
    rcases G.triggerStatus_update_triggerDiscountedRepeatedProfile_eq_none_or_self
        path punish who dev t with hnone | hsome
    · exact hnone
    · exact False.elim (hnot hsome)

/-- Once the trigger status is `some who` along a unilateral deviation, it
remains `some who` forever. -/
theorem triggerStatus_update_trigger_some_mono
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.DiscountedRepeatedStrategy who) {t : ℕ}
    (hstatus :
      G.triggerStatus path t
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) =
          some who) :
    ∀ k : ℕ,
      G.triggerStatus path (t + k)
        (fun m =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) m) =
        some who := by
  intro k
  induction k with
  | zero =>
      simpa using hstatus
  | succ k ih =>
      let σdev : G.DiscountedRepeatedProfile :=
        Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev
      let hist : G.PublicHistory (t + k + 1) := fun m => G.discountedRepeatedPlay σdev m
      have hinit : G.historyInit hist =
          (fun m : Fin (t + k) => G.discountedRepeatedPlay σdev m) := by
        funext m
        rfl
      have ih' :
          G.triggerStatus path (t + k)
            (fun m : Fin (t + k) => G.discountedRepeatedPlay σdev m) =
          some who := by
        simpa [σdev] using ih
      change G.triggerStatus path (t + (k + 1))
          (fun m : Fin (t + (k + 1)) => G.discountedRepeatedPlay σdev m) =
        some who
      have hnat : t + (k + 1) = t + k + 1 := by omega
      rw [hnat]
      change G.triggerStatus path (t + k + 1) hist = some who
      simp [triggerStatus, hinit, ih']

/-- After the trigger has identified `who`, every other player's realized action
is the chosen punishment action against `who`. -/
theorem discountedRepeatedPlay_update_triggerDiscountedRepeatedProfile_ne_of_status_some
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.DiscountedRepeatedStrategy who) {t : ℕ}
    (hstatus :
      G.triggerStatus path t
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) =
          some who)
    {j : ι} (hj : j ≠ who) :
    G.discountedRepeatedPlay
        (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) t j =
      punish who ⟨j, hj⟩ := by
  rw [discountedRepeatedPlay]
  simp [triggerDiscountedRepeatedProfile, triggerProfileAt, Function.update, hj, hstatus]

/-- Once the trigger has identified `who`, that player's realized stage payoff
is bounded by the best-response value against the selected punishment
opponents. -/
theorem eu_discountedRepeatedPlay_update_trigger_lt_of_status_some
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.DiscountedRepeatedStrategy who) {t : ℕ} {b : ℝ}
    (hbdd : BddAbove (Set.range fun own : G.Strategy who =>
      G.eu (G.profileWithOpponent who own (punish who)) who))
    (hpunish : G.bestResponseValueAgainstOpponents who (punish who) < b)
    (hstatus :
      G.triggerStatus path t
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) =
          some who) :
    G.eu
        (G.discountedRepeatedPlay
          (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) t) who <
      b := by
  let ρ : Profile G :=
    G.discountedRepeatedPlay
      (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) t
  have hρ : ρ = G.profileWithOpponent who (ρ who) (punish who) := by
    apply G.eq_profileWithOpponent_of_forall_ne who ρ (punish who)
    intro j hj
    exact G.discountedRepeatedPlay_update_triggerDiscountedRepeatedProfile_ne_of_status_some
      path punish who dev hstatus hj
  rw [show G.discountedRepeatedPlay
          (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) t = ρ from rfl]
  rw [hρ]
  exact G.eu_profileWithOpponent_lt_of_bestResponseValue_lt
    who (punish who) hbdd hpunish (ρ who)

/-- If a unilateral deviation is in punishment status at `start`, its whole
continuation payoff is bounded by the selected punishment cap. -/
theorem discountedContinuationPayoff_update_trigger_le_const_of_status_some
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    {δ C b : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.DiscountedRepeatedStrategy who) {start : ℕ}
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C)
    (hbdd : BddAbove (Set.range fun own : G.Strategy who =>
      G.eu (G.profileWithOpponent who own (punish who)) who))
    (hpunish : G.bestResponseValueAgainstOpponents who (punish who) < b)
    (hstatus :
      G.triggerStatus path start
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) =
          some who) :
    G.discountedContinuationPayoff δ
        (fun t =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) t)
        start who ≤ b := by
  apply G.discountedContinuationPayoff_le_const_of_forall_stageEU_le hδ0 hδ1
      (fun t =>
        G.discountedRepeatedPlay
          (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) t)
      start who hbd
  intro k
  have hkstatus := G.triggerStatus_update_trigger_some_mono path punish who dev hstatus k
  exact le_of_lt (G.eu_discountedRepeatedPlay_update_trigger_lt_of_status_some
    path punish who dev hbdd hpunish hkstatus)

/-- Incentive comparison at the firing boundary.  If the deviation first puts
the trigger into punishment status after period `q`, then the deviating
continuation from `q` is dominated by the intended-path continuation from `q`,
provided the path tail has margin over the punishment cap and the discount
factor is patient enough. -/
theorem discountedContinuationPayoff_update_trigger_le_path_of_fire
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    {δ C b η : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.DiscountedRepeatedStrategy who) {q : ℕ}
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C)
    (hbdd : BddAbove (Set.range fun own : G.Strategy who =>
      G.eu (G.profileWithOpponent who own (punish who)) who))
    (hpunish : G.bestResponseValueAgainstOpponents who (punish who) < b)
    (hfire :
      G.triggerStatus path (q + 1)
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) =
          some who)
    (hpath_tail : b + η ≤ G.discountedContinuationPayoff δ path (q + 1) who)
    (hpatient : (1 - δ) * (2 * C) ≤ δ * η) :
    G.discountedContinuationPayoff δ
        (fun t =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) t)
        q who ≤
      G.discountedContinuationPayoff δ path q who := by
  let playDev : ℕ → Profile G := fun t =>
    G.discountedRepeatedPlay
      (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) t
  have hdev_split := G.discountedContinuationPayoff_eq_head_add
    hδ0 hδ1 playDev q who hbd
  have hpath_split := G.discountedContinuationPayoff_eq_head_add
    hδ0 hδ1 path q who hbd
  have hdev_tail : G.discountedContinuationPayoff δ playDev (q + 1) who ≤ b := by
    exact G.discountedContinuationPayoff_update_trigger_le_const_of_status_some
      hδ0 hδ1 path punish who dev hbd hbdd hpunish hfire
  have hdev_head : G.eu (playDev q) who ≤ C := (abs_le.mp (hbd (playDev q))).2
  have hpath_head : -C ≤ G.eu (path q) who := (abs_le.mp (hbd (path q))).1
  have hdev_upper :
      G.discountedContinuationPayoff δ playDev q who ≤ (1 - δ) * C + δ * b := by
    rw [hdev_split]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hdev_head (sub_nonneg.mpr hδ1.le))
      (mul_le_mul_of_nonneg_left hdev_tail hδ0)
  have hpath_lower :
      (1 - δ) * (-C) + δ * (b + η) ≤
        G.discountedContinuationPayoff δ path q who := by
    rw [hpath_split]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hpath_head (sub_nonneg.mpr hδ1.le))
      (mul_le_mul_of_nonneg_left hpath_tail hδ0)
  have halg : (1 - δ) * C + δ * b ≤ (1 - δ) * (-C) + δ * (b + η) := by
    nlinarith
  exact hdev_upper.trans (halg.trans hpath_lower)

/-- Full first-fire branch of the trigger incentive proof. -/
theorem discountedContinuationPayoff_update_trigger_le_path_of_first_fire
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    {δ C b η : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.DiscountedRepeatedStrategy who) {s : ℕ}
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C)
    (hbdd : BddAbove (Set.range fun own : G.Strategy who =>
      G.eu (G.profileWithOpponent who own (punish who)) who))
    (hpunish : G.bestResponseValueAgainstOpponents who (punish who) < b)
    (hfire :
      G.triggerStatus path s
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) =
          some who)
    (hmin : ∀ t < s,
      G.triggerStatus path t
        (fun k =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) k) =
          none)
    (hpath_tail : b + η ≤ G.discountedContinuationPayoff δ path s who)
    (hpatient : (1 - δ) * (2 * C) ≤ δ * η) :
    G.discountedContinuationPayoff δ
        (fun t =>
          G.discountedRepeatedPlay
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) t)
        0 who ≤
      G.discountedContinuationPayoff δ path 0 who := by
  cases s with
  | zero =>
      simp [triggerStatus] at hfire
  | succ q =>
      let playDev : ℕ → Profile G := fun t =>
        G.discountedRepeatedPlay
          (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) t
      have htail : G.discountedContinuationPayoff δ playDev q who ≤
          G.discountedContinuationPayoff δ path q who := by
        apply G.discountedContinuationPayoff_update_trigger_le_path_of_fire
          hδ0 hδ1 path punish who dev hbd hbdd hpunish
        · simpa [playDev] using hfire
        · simpa using hpath_tail
        · exact hpatient
      have hpref : ∀ k < q, playDev (0 + k) = path (0 + k) := by
        intro k hk
        have hstat_k :
            G.triggerStatus path k
              (fun m =>
                G.discountedRepeatedPlay
                  (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) m) =
              none :=
          hmin k (lt_trans hk (Nat.lt_succ_self q))
        have hstat_ksucc :
            G.triggerStatus path (k + 1)
              (fun m =>
                G.discountedRepeatedPlay
                  (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) m) =
              none :=
          hmin (k + 1) (Nat.succ_lt_succ hk)
        have hplay := G.discountedRepeatedPlay_update_trigger_eq_path_of_status_none_succ
          path punish who dev hstat_k hstat_ksucc
        simpa [playDev] using hplay
      have hres := G.discountedContinuationPayoff_le_of_prefix_eq_of_tail_le
        hδ0 hδ1 playDev path 0 q who hbd hpref ?_
      · simpa [playDev] using hres
      · simpa using htail

/-- Trigger-strategy Nash criterion.  Once the intended path has continuation
payoff uniformly above the punishment cap and the discount factor is patient
enough to dominate a one-period gain, the trigger profile is a discounted
repeated-game Nash equilibrium. -/
theorem triggerDiscountedRepeatedProfile_isDiscountedRepeatedNash
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    {δ C η : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (b : Payoff ι)
    (hbd : ∀ (who : ι) (ρ : Profile G), |G.eu ρ who| ≤ C)
    (hbdd : ∀ who, BddAbove (Set.range fun own : G.Strategy who =>
      G.eu (G.profileWithOpponent who own (punish who)) who))
    (hpunish : ∀ who, G.bestResponseValueAgainstOpponents who (punish who) < b who)
    (hpath_tail : ∀ who s, b who + η ≤ G.discountedContinuationPayoff δ path s who)
    (hpatient : (1 - δ) * (2 * C) ≤ δ * η) :
    G.IsDiscountedRepeatedNash δ (G.triggerDiscountedRepeatedProfile path punish) := by
  intro who dev
  rcases G.triggerStatus_update_trigger_first_fire_or_never path punish who dev with
    hnever | hfirecase
  · rw [G.discountedAveragePayoff_update_trigger_eq_of_forall_status_none
      path punish who dev δ hnever]
  · rcases hfirecase with ⟨s, hs, hmin⟩
    let playDev : ℕ → Profile G := fun t =>
      G.discountedRepeatedPlay
        (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) t
    have hdev_le_path : G.discountedContinuationPayoff δ playDev 0 who ≤
        G.discountedContinuationPayoff δ path 0 who := by
      exact G.discountedContinuationPayoff_update_trigger_le_path_of_first_fire
        hδ0 hδ1 path punish who dev (hbd who) (hbdd who) (hpunish who)
        hs hmin (hpath_tail who s) hpatient
    have hleft :
        G.discountedAveragePayoff δ (G.triggerDiscountedRepeatedProfile path punish) who =
          G.discountedContinuationPayoff δ path 0 who := by
      simp [discountedAveragePayoff, discountedContinuationPayoff,
        G.discountedRepeatedPlay_triggerDiscountedRepeatedProfile_eq_path path punish]
    have hright :
        G.discountedAveragePayoff δ
            (Function.update (G.triggerDiscountedRepeatedProfile path punish) who dev) who =
          G.discountedContinuationPayoff δ playDev 0 who := by
      simp [discountedAveragePayoff, discountedContinuationPayoff, playDev]
    rw [hleft, hright]
    exact hdev_le_path

/-- Turn finite denominator-cleared weights into a cycle indexed by `Fin`. -/
def cycleOfCounts (G : KernelGame ι) {κ : Type} [Fintype κ]
    (c : κ → ℕ) (σ : κ → Profile G) :
    Fin (Fintype.card (Sigma fun k => Fin (c k))) → Profile G :=
  fun t => σ (((Fintype.equivFin (Sigma fun k => Fin (c k))).symm t).1)

/-- Summing payoffs over the denominator-cleared cycle is the same as summing
each source profile with its integer multiplicity. -/
theorem sum_eu_cycleOfCounts (G : KernelGame ι) {κ : Type} [Fintype κ]
    (c : κ → ℕ) (σ : κ → Profile G) (who : ι) :
    (∑ t : Fin (Fintype.card (Sigma fun k => Fin (c k))),
        G.eu (G.cycleOfCounts c σ t) who) =
      ∑ k, (c k : ℝ) * G.eu (σ k) who := by
  rw [show (∑ t : Fin (Fintype.card (Sigma fun k => Fin (c k))),
        G.eu (G.cycleOfCounts c σ t) who) =
      ∑ a : Sigma fun k => Fin (c k), G.eu (σ a.1) who from ?_]
  · rw [Fintype.sum_sigma]
    simp [Finset.sum_const, nsmul_eq_mul]
  · exact (Fintype.sum_equiv (Fintype.equivFin (Sigma fun k => Fin (c k)))
      (fun a : Sigma fun k => Fin (c k) => G.eu (σ a.1) who)
      (fun t : Fin (Fintype.card (Sigma fun k => Fin (c k))) =>
        G.eu (G.cycleOfCounts c σ t) who)
      (fun a => by simp [cycleOfCounts])).symm

/-- Every feasible payoff can be approximated by the uniform average payoff of
a finite pure-profile cycle. -/
theorem exists_cycleAveragePayoff_close_of_mem_feasibleSet
    (G : KernelGame ι) [Finite ι] [Finite G.Outcome]
    {v : Payoff ι} (hv : v ∈ G.feasibleSet) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : NeZero n) (cycle : Fin n → Profile G),
      ∀ who, |G.cycleAveragePayoff cycle who - v who| < ε := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  rcases G.exists_fintype_weighted_profiles_apply_of_mem_feasibleSet hv with
    ⟨κ, hκ, w, σ, hw_nonneg, hw_sum, hvsum⟩
  letI : Fintype κ := hκ
  have hκ_nonempty : Nonempty κ := by
    by_contra hne
    haveI : IsEmpty κ := not_nonempty_iff.mp hne
    simp at hw_sum
  letI : Nonempty κ := hκ_nonempty
  obtain ⟨C, hC⟩ := G.exists_uniform_stageEU_abs_bound_of_finite
  let A : ℝ := max C 0
  have hA0 : 0 ≤ A := le_max_right C 0
  have hCA : ∀ (ρ : Profile G) (who : ι), |G.eu ρ who| ≤ A := by
    intro ρ who
    exact (hC ρ who).trans (le_max_left C 0)
  let R : ℝ := (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) * A)
  have hR0 : 0 ≤ R := by
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA0)
  obtain ⟨N, hNgt⟩ := exists_nat_gt (R / ε)
  have hNpos : 0 < N := by
    by_contra hN
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
    have hRdiv0 : 0 ≤ R / ε := div_nonneg hR0 hε.le
    have : R / ε < 0 := by simpa [hN0] using hNgt
    linarith
  have hRlt : R < (N : ℝ) * ε := (div_lt_iff₀ hε).1 hNgt
  let k₀ : κ := Classical.choice hκ_nonempty
  let c : κ → ℕ := Math.SimplexApproximation.residualFloorCounts k₀ w N
  let n : ℕ := Fintype.card (Sigma fun k => Fin (c k))
  have hn_eq : n = N := by
    dsimp [n, c]
    rw [Fintype.card_sigma]
    simp [Math.SimplexApproximation.sum_residualFloorCounts k₀ hw_nonneg hw_sum N]
  have hn_ne : n ≠ 0 := by
    rw [hn_eq]
    exact Nat.ne_of_gt hNpos
  letI : NeZero n := ⟨hn_ne⟩
  let cycle : Fin n → Profile G := by
    dsimp [n]
    exact G.cycleOfCounts c σ
  refine ⟨n, inferInstance, cycle, ?_⟩
  intro who
  let u : κ → ℝ := fun k => G.eu (σ k) who
  have hNneR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNpos)
  have hcycle_sum : G.cycleAveragePayoff cycle who =
      (n : ℝ)⁻¹ * ∑ k, (c k : ℝ) * u k := by
    have hsum_cycle :
        (∑ t : Fin n, G.eu (cycle t) who) = ∑ k, (c k : ℝ) * u k := by
      dsimp [cycle, n]
      simpa [u] using G.sum_eu_cycleOfCounts c σ who
    rw [cycleAveragePayoff, hsum_cycle]
  have herror_eq : (N : ℝ)⁻¹ * (∑ k, (c k : ℝ) * u k) - ∑ k, w k * u k =
      (N : ℝ)⁻¹ * ∑ k, (((c k : ℝ) - (N : ℝ) * w k) * u k) := by
    field_simp [hNneR]
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  have hsum_abs : |∑ k, (((c k : ℝ) - (N : ℝ) * w k) * u k)| ≤ R := by
    calc
      |∑ k, (((c k : ℝ) - (N : ℝ) * w k) * u k)|
          ≤ ∑ k, |(((c k : ℝ) - (N : ℝ) * w k) * u k)| := by
            simpa using (Finset.abs_sum_le_sum_abs
              (fun k => (((c k : ℝ) - (N : ℝ) * w k) * u k)) Finset.univ)
      _ ≤ ∑ _k : κ, (Fintype.card κ : ℝ) * A := by
        apply Finset.sum_le_sum
        intro k _hk
        rw [abs_mul]
        exact mul_le_mul
          (Math.SimplexApproximation.residualFloorCounts_abs_error_le_card
            k₀ hw_nonneg hw_sum N k)
          (hCA (σ k) who)
          (abs_nonneg (u k))
          (Nat.cast_nonneg _)
      _ = R := by
        simp [R, Finset.sum_const, nsmul_eq_mul]
  have hscaled_lt :
      |(N : ℝ)⁻¹ * ∑ k, (((c k : ℝ) - (N : ℝ) * w k) * u k)| < ε := by
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
    have hle : (N : ℝ)⁻¹ *
          |∑ k, (((c k : ℝ) - (N : ℝ) * w k) * u k)| ≤
        (N : ℝ)⁻¹ * R :=
      mul_le_mul_of_nonneg_left hsum_abs (inv_nonneg.mpr (Nat.cast_nonneg N))
    have hlt : (N : ℝ)⁻¹ * R < ε := by
      have hNposR : 0 < (N : ℝ) := by exact_mod_cast hNpos
      have h := mul_lt_mul_of_pos_left hRlt (inv_pos.mpr hNposR)
      have hright : (N : ℝ)⁻¹ * ((N : ℝ) * ε) = ε := by
        field_simp [ne_of_gt hNposR]
      simpa [hright] using h
    exact hle.trans_lt hlt
  calc
    |G.cycleAveragePayoff cycle who - v who|
        = |(N : ℝ)⁻¹ * (∑ k, (c k : ℝ) * u k) - ∑ k, w k * u k| := by
          rw [hcycle_sum, hvsum who]
          rw [hn_eq]
    _ = |(N : ℝ)⁻¹ * ∑ k, (((c k : ℝ) - (N : ℝ) * w k) * u k)| := by
      rw [herror_eq]
    _ < ε := hscaled_lt

/-- A payoff vector exactly induced by a discounted repeated-game Nash
equilibrium. -/
def IsDiscountedRepeatedNashPayoff (G : KernelGame ι) [DecidableEq ι] (δ : ℝ)
    (v : Payoff ι) : Prop :=
  ∃ σ : G.DiscountedRepeatedProfile,
    G.IsDiscountedRepeatedNash δ σ ∧
      ∀ who, G.discountedAveragePayoff δ σ who = v who

/-- `v` is the limit of Nash payoff vectors as the discount factor tends to one
from below. -/
def ApproximableByDiscountedRepeatedNashPayoffs (G : KernelGame ι) [DecidableEq ι]
    (v : Payoff ι) : Prop :=
  ∀ ε > 0, ∃ δ₀ : ℝ, 0 ≤ δ₀ ∧ δ₀ < 1 ∧
    ∀ δ : ℝ, δ₀ < δ → δ < 1 →
      ∃ w : Payoff ι, G.IsDiscountedRepeatedNashPayoff δ w ∧
        ∀ who, |w who - v who| < ε

/-- Approximate discounted Folk theorem for the observable mixed-action repeated
game.

This is stated for the infinite discounted repeated game, not the existing
finite-horizon multi-round language.  The repeated game is taken over
`G.mixedExtension`, so a period action for player `i` is a mixed stage strategy
`PMF (G.Strategy i)`, and public histories observe the mixed-action profile
itself.

This is a genuine discounted Folk theorem for that public mixed-action model:
given any payoff vector `v` that is feasible in the original stage game and
strictly above the mixed-extension opponent-minmax vector, Nash payoff vectors
of the mixed-action repeated game approach `v` as `δ → 1`.

What is not modeled here is the sampled-history behavioral implementation where
players privately randomize, realized pure actions or public signals are
observed, and strategies condition on those sampled histories.  Such a layer can
refine the interface later; the payoff-set approximation and trigger-incentive
argument here are isolated from that extra sampling semantics. -/
theorem discounted_folk_theorem_approx (G : KernelGame ι) [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] [Finite G.Outcome]
    {v : Payoff ι}
    (hv : v ∈ G.strictIndividuallyRationalPayoffSet G.mixedExtension.opponentMinmaxVector) :
    G.mixedExtension.ApproximableByDiscountedRepeatedNashPayoffs v := by
  classical
  let H : KernelGame ι := G.mixedExtension
  letI : Finite H.Outcome := G.finite_mixedExtension_outcome
  letI : ∀ i, Nonempty (H.Strategy i) := fun i =>
    G.nonempty_mixedExtension_strategy i
  letI : ∀ who, Nonempty (H.OpponentProfile who) := fun who =>
    G.nonempty_mixedExtension_opponentProfile who
  intro ε hε
  obtain ⟨ηIR, hηIRpos, hηIR⟩ :=
    G.exists_pos_margin_of_mem_strictIndividuallyRationalPayoffSet hv
  let α : ℝ := min (ε / 2) (ηIR / 8)
  have hαpos : 0 < α := by
    exact lt_min (half_pos hε) (by positivity)
  have hα_le_eps : α ≤ ε / 2 := min_le_left _ _
  have hα_le_eta : α ≤ ηIR / 8 := min_le_right _ _
  obtain ⟨n, hn, cycle, hcycle_close⟩ :=
    G.exists_cycleAveragePayoff_close_of_mem_feasibleSet hv.1 hαpos
  letI : NeZero n := hn
  let cycleH : Fin n → Profile H := G.pureMixedCycle cycle
  have hcycleH_eq : H.cycleAveragePayoff cycleH = G.cycleAveragePayoff cycle := by
    simpa [H, cycleH] using G.mixedExtension_cycleAveragePayoff_pureMixedCycle cycle
  have hcycleH_close : ∀ who, |H.cycleAveragePayoff cycleH who - v who| < α := by
    intro who
    simpa [hcycleH_eq] using hcycle_close who
  let ηT : ℝ := ηIR / 4
  have hηTpos : 0 < ηT := by positivity
  let b : Payoff ι := fun who => H.opponentMinmaxVector who + ηIR / 4
  obtain ⟨punish, hpunishApprox⟩ := H.exists_approx_punishmentProfiles hηTpos
  obtain ⟨C0, hC0⟩ := H.exists_uniform_stageEU_abs_bound_of_finite
  let C : ℝ := max C0 0
  have hbd : ∀ (who : ι) (ρ : Profile H), |H.eu ρ who| ≤ C := by
    intro who ρ
    exact (hC0 ρ who).trans (le_max_left C0 0)
  have hbdd : ∀ who, BddAbove (Set.range fun own : H.Strategy who =>
      H.eu (H.profileWithOpponent who own (punish who)) who) := by
    intro who
    refine ⟨C, ?_⟩
    rintro _ ⟨own, rfl⟩
    exact (abs_le.mp (hbd who (H.profileWithOpponent who own (punish who)))).2
  have hpunish :
      ∀ who, H.bestResponseValueAgainstOpponents who (punish who) < b who := by
    intro who
    simpa [b, opponentMinmaxVector, ηT] using hpunishApprox who
  obtain ⟨δCont, hδCont0, hδCont1, hδCont⟩ :=
    H.exists_discountFactor_threshold_periodic_all_continuations_close_cycleAverage cycleH
      hαpos
  have hCnonneg : 0 ≤ C := le_max_right C0 0
  have hMnonneg : 0 ≤ 2 * C := by positivity
  obtain ⟨δPat, hδPat0, hδPat1, hδPat⟩ :=
    exists_discountFactor_threshold_one_step (M := 2 * C) (η := ηT) hMnonneg hηTpos
  let δ₀ : ℝ := max δCont δPat
  refine ⟨δ₀, ?_, ?_, ?_⟩
  · exact hδCont0.trans (le_max_left δCont δPat)
  · exact max_lt hδCont1 hδPat1
  · intro δ hδgt hδlt
    have hδCont_gt : δCont < δ := (le_max_left δCont δPat).trans_lt hδgt
    have hδPat_gt : δPat < δ := (le_max_right δCont δPat).trans_lt hδgt
    have hδnonneg : 0 ≤ δ :=
      (hδCont0.trans (le_max_left δCont δPat)).trans hδgt.le
    have hcont_close : ∀ (who : ι) (start : ℕ),
        |H.discountedContinuationPayoff δ (fun t => cycleH (Fin.ofNat n t)) start who -
          H.cycleAveragePayoff cycleH who| < α :=
      hδCont δ hδCont_gt hδlt
    have hpatient : (1 - δ) * (2 * C) ≤ δ * ηT :=
      le_of_lt (hδPat δ hδPat_gt hδlt)
    let path : ℕ → Profile H := fun t => cycleH (Fin.ofNat n t)
    have hpath_tail :
        ∀ who s, b who + ηT ≤ H.discountedContinuationPayoff δ path s who := by
      intro who s
      have htail_abs := hcont_close who s
      have hcycle_abs := hcycleH_close who
      have htail_lower : H.cycleAveragePayoff cycleH who - α <
          H.discountedContinuationPayoff δ path s who := by
        have := (abs_lt.mp htail_abs).1
        linarith
      have hcycle_lower : v who - α < H.cycleAveragePayoff cycleH who := by
        have := (abs_lt.mp hcycle_abs).1
        linarith
      have hmargin := hηIR who
      have hbdef : b who = H.opponentMinmaxVector who + ηIR / 4 := rfl
      rw [hbdef]
      nlinarith [hηIRpos, hα_le_eta, htail_lower, hcycle_lower, hmargin]
    have hNash :
        H.IsDiscountedRepeatedNash δ (H.triggerDiscountedRepeatedProfile path punish) :=
      H.triggerDiscountedRepeatedProfile_isDiscountedRepeatedNash hδnonneg hδlt path
        punish b hbd hbdd hpunish hpath_tail hpatient
    let w : Payoff ι := fun who =>
      H.discountedAveragePayoff δ (H.triggerDiscountedRepeatedProfile path punish) who
    refine ⟨w, ?_, ?_⟩
    · exact ⟨H.triggerDiscountedRepeatedProfile path punish, hNash, fun who => rfl⟩
    · intro who
      have hpay_path : w who = H.discountedContinuationPayoff δ path 0 who := by
        simp [w, path, discountedAveragePayoff, discountedContinuationPayoff,
          H.discountedRepeatedPlay_triggerDiscountedRepeatedProfile_eq_path]
      have h1 : |w who - H.cycleAveragePayoff cycleH who| < α := by
        simpa [hpay_path, path] using hcont_close who 0
      have h2 : |H.cycleAveragePayoff cycleH who - v who| < α := hcycleH_close who
      have htri := abs_sub_le (w who) (H.cycleAveragePayoff cycleH who) (v who)
      nlinarith [h1, h2, htri, hα_le_eps]

theorem finite_purePayoffSet (G : KernelGame ι) [Finite (Profile G)] :
    G.purePayoffSet.Finite := by
  exact Set.finite_range G.payoffVector

theorem nonempty_purePayoffSet (G : KernelGame ι) [Nonempty (Profile G)] :
    G.purePayoffSet.Nonempty := by
  obtain ⟨σ⟩ := ‹Nonempty (Profile G)›
  exact ⟨G.payoffVector σ, ⟨σ, rfl⟩⟩

theorem nonempty_feasibleSet (G : KernelGame ι) [Nonempty (Profile G)] :
    G.feasibleSet.Nonempty := by
  simpa [feasibleSet] using
    (Set.Nonempty.convexHull (𝕜 := ℝ) (G.nonempty_purePayoffSet))

theorem convex_feasibleSet (G : KernelGame ι) :
    Convex ℝ G.feasibleSet := by
  exact convex_convexHull ℝ G.purePayoffSet

theorem isCompact_feasibleSet (G : KernelGame ι) [Finite (Profile G)] :
    IsCompact G.feasibleSet := by
  simpa [feasibleSet] using (G.finite_purePayoffSet.isCompact_convexHull ℝ)

theorem isClosed_feasibleSet (G : KernelGame ι) [Finite (Profile G)] :
    IsClosed G.feasibleSet := by
  simpa [feasibleSet] using (G.finite_purePayoffSet.isClosed_convexHull ℝ)

theorem convex_weakReservationSet (r : Payoff ι) :
    Convex ℝ (weakReservationSet r) := by
  rw [weakReservationSet]
  intro x hx y hy a b ha hb hab i
  calc
    r i = a * r i + b * r i := by rw [← add_mul, hab, one_mul]
    _ ≤ a * x i + b * y i :=
      add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = (a • x + b • y) i := by simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul]

theorem convex_strictReservationSet (r : Payoff ι) :
    Convex ℝ (strictReservationSet r) := by
  rw [strictReservationSet]
  intro x hx y hy a b ha hb hab i
  have hxpos : 0 < x i - r i := sub_pos.mpr (hx i)
  have hypos : 0 < y i - r i := sub_pos.mpr (hy i)
  have hpos : 0 < a * (x i - r i) + b * (y i - r i) := by
    by_cases ha0 : a = 0
    · subst ha0
      have hb1 : b = 1 := by simpa using hab
      simpa [hb1] using hypos
    · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      exact add_pos_of_pos_of_nonneg (mul_pos hapos hxpos) (mul_nonneg hb hypos.le)
  have hrewrite :
      a * (x i - r i) + b * (y i - r i) = a * x i + b * y i - r i := by
    calc
      a * (x i - r i) + b * (y i - r i) =
          a * x i + b * y i - (a + b) * r i := by ring
      _ = a * x i + b * y i - r i := by rw [hab, one_mul]
  have hlt : r i < a * x i + b * y i := by
    linarith
  simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hlt

theorem isClosed_weakReservationSet (r : Payoff ι) :
    IsClosed (weakReservationSet r) := by
  have hclosed : IsClosed (⋂ i, {v : Payoff ι | r i ≤ v i}) := by
    refine isClosed_iInter ?_
    intro i
    simpa using
      (isClosed_Ici.preimage (continuous_apply i : Continuous fun v : Payoff ι => v i))
  have hset : weakReservationSet r = ⋂ i, {v : Payoff ι | r i ≤ v i} := by
    ext v
    simp [weakReservationSet]
  rw [hset]
  exact hclosed

theorem convex_individuallyRationalPayoffSet (G : KernelGame ι) (r : Payoff ι) :
    Convex ℝ (G.individuallyRationalPayoffSet r) :=
  (G.convex_feasibleSet).inter (convex_weakReservationSet r)

theorem convex_strictIndividuallyRationalPayoffSet (G : KernelGame ι) (r : Payoff ι) :
    Convex ℝ (G.strictIndividuallyRationalPayoffSet r) :=
  (G.convex_feasibleSet).inter (convex_strictReservationSet r)

theorem isClosed_individuallyRationalPayoffSet (G : KernelGame ι) [Finite (Profile G)]
    (r : Payoff ι) :
    IsClosed (G.individuallyRationalPayoffSet r) :=
  (G.isClosed_feasibleSet).inter (isClosed_weakReservationSet r)

theorem isCompact_individuallyRationalPayoffSet (G : KernelGame ι) [Finite (Profile G)]
    (r : Payoff ι) :
    IsCompact (G.individuallyRationalPayoffSet r) :=
  (G.isCompact_feasibleSet).inter_right (isClosed_weakReservationSet r)

end KernelGame

end GameTheory
