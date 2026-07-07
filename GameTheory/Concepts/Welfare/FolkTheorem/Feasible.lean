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


end KernelGame

end GameTheory
