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
import GameTheory.Concepts.Welfare.FolkTheorem.Trigger

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace KernelGame

variable {ι : Type}

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
  obtain ⟨C, hC⟩ := G.exists_uniform_eu_abs_bound_of_finite
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
  ∃ σ : G.RepeatedProfile,
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
`PMF (G.Strategy i)`, and profile histories observe the mixed-action profile
itself.

This is a discounted Folk theorem for that observable mixed-action model:
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
  obtain ⟨C0, hC0⟩ := H.exists_uniform_eu_abs_bound_of_finite
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
        H.IsDiscountedRepeatedNash δ (H.triggerRepeatedProfile path punish) :=
      H.triggerRepeatedProfile_isDiscountedRepeatedNash hδnonneg hδlt path
        punish b hbd hbdd hpunish hpath_tail hpatient
    let w : Payoff ι := fun who =>
      H.discountedAveragePayoff δ (H.triggerRepeatedProfile path punish) who
    refine ⟨w, ?_, ?_⟩
    · exact ⟨H.triggerRepeatedProfile path punish, hNash, fun who => rfl⟩
    · intro who
      have hpay_path : w who = H.discountedContinuationPayoff δ path 0 who := by
        simp [w, path, discountedAveragePayoff, discountedContinuationPayoff,
          H.repeatedPlay_triggerRepeatedProfile_eq_path]
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
    change IsClosed ((fun v : Payoff ι => v i) ⁻¹' Set.Ici (r i))
    exact isClosed_Ici.preimage (continuous_apply i : Continuous fun v : Payoff ι => v i)
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
