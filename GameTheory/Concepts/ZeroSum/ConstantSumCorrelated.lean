/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Mixed.BinaryMixed
import GameTheory.Concepts.ZeroSum.ConstantSumNash
import GameTheory.Concepts.Correlation.CorrelatedNashMixed
import Math.ProbabilityMassFunction
import Mathlib.Tactic.Linarith

/-!
# Constant-Sum Correlated Equilibria

Correlated-equilibrium value facts for two-player constant-sum games.

The main theorem says that every correlated equilibrium of a two-player
constant-sum game has the same player-0 value as any Nash equilibrium.  The
proof uses only coarse deviations: a CE is a CCE, and deviating to either
player's Nash strategy gives the usual lower/upper value bounds.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace KernelGame

/-! ## Correlated value in constant-sum games -/

theorem IsConstantSum.correlatedEu_sum_of_bounded
    {G : KernelGame (Fin 2)}
    {c : ℝ} (hcs : G.IsConstantSum c) (μ : PMF (Profile G))
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.correlatedEu μ 0 + G.correlatedEu μ 1 = c := by
  let d : PMF G.Outcome := G.correlatedOutcome μ
  have h0 : Summable (fun ω : G.Outcome => (d ω).toReal * G.utility ω 0) :=
    Math.Probability.expect_summable_of_bounded d (fun ω => G.utility ω 0) (hbd 0)
  have h1 : Summable (fun ω : G.Outcome => (d ω).toReal * G.utility ω 1) :=
    Math.Probability.expect_summable_of_bounded d (fun ω => G.utility ω 1) (hbd 1)
  have hpoint : ∀ ω : G.Outcome, G.utility ω 0 + G.utility ω 1 = c := by
    intro ω
    simpa [Fin.sum_univ_two] using hcs ω
  calc
    G.correlatedEu μ 0 + G.correlatedEu μ 1
        = (∑' ω : G.Outcome, (d ω).toReal * G.utility ω 0) +
            (∑' ω : G.Outcome, (d ω).toReal * G.utility ω 1) := by
              rfl
    _ = ∑' ω : G.Outcome,
          ((d ω).toReal * G.utility ω 0 + (d ω).toReal * G.utility ω 1) := by
          exact (Summable.tsum_add h0 h1).symm
    _ = ∑' ω : G.Outcome, (d ω).toReal * c := by
          apply tsum_congr
          intro ω
          rw [← mul_add, hpoint ω]
    _ = c := by
          rw [tsum_mul_right, Math.Probability.pmf_toReal_tsum_one, one_mul]

theorem IsConstantSum.correlatedEu_sum
    {G : KernelGame (Fin 2)} [Finite G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c) (μ : PMF (Profile G)) :
    G.correlatedEu μ 0 + G.correlatedEu μ 1 = c := by
  classical
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact hcs.correlatedEu_sum_of_bounded μ hbd

theorem IsConstantSum.coarseCorrelated_eq_eu_eq_nash_of_bounded
    {G : KernelGame (Fin 2)}
    {c : ℝ} (hcs : G.IsConstantSum c) {σ : Profile G}
    (hN : G.IsNash σ) {μ : PMF (Profile G)}
    (hCCE : G.IsCoarseCorrelatedEq μ)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.correlatedEu μ 0 = G.eu σ 0 := by
  have hsumμ := hcs.correlatedEu_sum_of_bounded μ hbd
  have hsumσ : G.eu σ 0 + G.eu σ 1 = c := by
    have hdet := hcs.eu_determined_of_bounded σ hbd
    linarith
  have h0dev :
      G.correlatedEu (G.constantDeviationDistribution μ 0 (σ 0)) 0 ≥ G.eu σ 0 := by
    rw [correlatedEu_constantDeviationDistribution_eq_expect_update_of_bounded
      (G := G) μ 0 (σ 0) (hbd 0)]
    have hgar := hcs.nash_guarantees_0_of_bounded hN hbd
    have hmono := Math.ProbabilityMassFunction.expect_mono_of_pointwise_bounded
      (d := μ)
      (f := fun _ : Profile G => G.eu σ 0)
      (g := fun τ : Profile G => G.eu (Function.update τ 0 (σ 0)) 0)
      (hfg := fun τ => by
        simpa only [ge_iff_le] using hgar τ)
      (C := C 0)
      (hf := fun _ => G.eu_abs_le_of_bounded 0 (hbd 0) σ)
      (hg := fun τ => G.eu_abs_le_of_bounded 0 (hbd 0)
        (Function.update τ 0 (σ 0)))
    simpa using hmono
  have hμ0_ge : G.correlatedEu μ 0 ≥ G.eu σ 0 :=
    le_trans h0dev (hCCE 0 (σ 0))
  have h1dev :
      G.correlatedEu (G.constantDeviationDistribution μ 1 (σ 1)) 1 ≥ G.eu σ 1 := by
    rw [correlatedEu_constantDeviationDistribution_eq_expect_update_of_bounded
      (G := G) μ 1 (σ 1) (hbd 1)]
    have hgar := hcs.nash_guarantees_1_of_bounded hN hbd
    have hmono := Math.ProbabilityMassFunction.expect_mono_of_pointwise_bounded
      (d := μ)
      (f := fun _ : Profile G => G.eu σ 1)
      (g := fun τ : Profile G => G.eu (Function.update τ 1 (σ 1)) 1)
      (hfg := fun τ => by
        simpa only [ge_iff_le] using hgar τ)
      (C := C 1)
      (hf := fun _ => G.eu_abs_le_of_bounded 1 (hbd 1) σ)
      (hg := fun τ => G.eu_abs_le_of_bounded 1 (hbd 1)
        (Function.update τ 1 (σ 1)))
    simpa using hmono
  have hμ1_ge : G.correlatedEu μ 1 ≥ G.eu σ 1 :=
    le_trans h1dev (hCCE 1 (σ 1))
  apply le_antisymm
  · linarith
  · exact hμ0_ge

theorem IsConstantSum.coarseCorrelated_eq_eu_eq_nash
    {G : KernelGame (Fin 2)} [Finite G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c) {σ : Profile G}
    (hN : G.IsNash σ) {μ : PMF (Profile G)}
    (hCCE : G.IsCoarseCorrelatedEq μ) :
    G.correlatedEu μ 0 = G.eu σ 0 := by
  classical
  choose C hbd using fun i =>
    Math.Probability.exists_abs_bound_of_finite (fun ω => G.utility ω i)
  exact hcs.coarseCorrelated_eq_eu_eq_nash_of_bounded hN hCCE hbd

theorem IsConstantSum.correlated_eq_eu_eq_nash_of_bounded
    {G : KernelGame (Fin 2)}
    {c : ℝ} (hcs : G.IsConstantSum c) {σ : Profile G}
    (hN : G.IsNash σ) {μ : PMF (Profile G)}
    (hCE : G.IsCorrelatedEq μ)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.correlatedEu μ 0 = G.eu σ 0 :=
  hcs.coarseCorrelated_eq_eu_eq_nash_of_bounded hN hCE.toCoarseCorrelatedEq hbd

theorem IsConstantSum.correlated_eq_eu_eq_nash
    {G : KernelGame (Fin 2)} [Finite G.Outcome]
    {c : ℝ} (hcs : G.IsConstantSum c) {σ : Profile G}
    (hN : G.IsNash σ) {μ : PMF (Profile G)}
    (hCE : G.IsCorrelatedEq μ) :
    G.correlatedEu μ 0 = G.eu σ 0 :=
  hcs.coarseCorrelated_eq_eu_eq_nash hN hCE.toCoarseCorrelatedEq

theorem IsZeroSum.correlated_eq_eu_eq_nash_of_bounded
    {G : KernelGame (Fin 2)}
    (hzs : G.IsZeroSum) {σ : Profile G}
    (hN : G.IsNash σ) {μ : PMF (Profile G)}
    (hCE : G.IsCorrelatedEq μ)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.correlatedEu μ 0 = G.eu σ 0 :=
  IsConstantSum.correlated_eq_eu_eq_nash_of_bounded
    (c := 0) hzs hN hCE hbd

theorem IsZeroSum.coarseCorrelated_eq_eu_eq_nash_of_bounded
    {G : KernelGame (Fin 2)}
    (hzs : G.IsZeroSum) {σ : Profile G}
    (hN : G.IsNash σ) {μ : PMF (Profile G)}
    (hCCE : G.IsCoarseCorrelatedEq μ)
    {C : Fin 2 → ℝ} (hbd : ∀ i ω, |G.utility ω i| ≤ C i) :
    G.correlatedEu μ 0 = G.eu σ 0 :=
  IsConstantSum.coarseCorrelated_eq_eu_eq_nash_of_bounded
    (c := 0) hzs hN hCCE hbd

theorem IsZeroSum.correlated_eq_eu_eq_nash
    {G : KernelGame (Fin 2)} [Finite G.Outcome]
    (hzs : G.IsZeroSum) {σ : Profile G}
    (hN : G.IsNash σ) {μ : PMF (Profile G)}
    (hCE : G.IsCorrelatedEq μ) :
    G.correlatedEu μ 0 = G.eu σ 0 :=
  IsConstantSum.correlated_eq_eu_eq_nash (c := 0) hzs hN hCE

theorem IsZeroSum.coarseCorrelated_eq_eu_eq_nash
    {G : KernelGame (Fin 2)} [Finite G.Outcome]
    (hzs : G.IsZeroSum) {σ : Profile G}
    (hN : G.IsNash σ) {μ : PMF (Profile G)}
    (hCCE : G.IsCoarseCorrelatedEq μ) :
    G.correlatedEu μ 0 = G.eu σ 0 :=
  IsConstantSum.coarseCorrelated_eq_eu_eq_nash (c := 0) hzs hN hCCE

/-! ## Binary matching-pennies correlated equilibria -/

namespace BinaryActionLabels

variable {ι : Type} {G : KernelGame ι} (L : BinaryActionLabels G)

/-- Pure profiles in a binary-labeled two-player game are equivalent to the
two Boolean action labels, ordered as `(true-player action, false-player action)`. -/
def profilePairEquiv : Profile G ≃ Bool × Bool where
  toFun σ :=
    (L.toBool (L.playerOf true) (σ (L.playerOf true)),
      L.toBool (L.playerOf false) (σ (L.playerOf false)))
  invFun p := L.profile p.1 p.2
  left_inv := by
    intro σ
    funext i
    have hwho : i = L.playerOf (L.player i) := by
      simp [playerOf]
    cases hw : L.player i
    · have hi : i = L.playerOf false := by
        simpa [hw] using hwho
      subst i
      simp [profile]
    · have hi : i = L.playerOf true := by
        simpa [hw] using hwho
      subst i
      simp [profile]
  right_inv := by
    intro p
    rcases p with ⟨a, b⟩
    simp [profile]

theorem expect_eq_sum_profilePair
    [Finite ι]
    (μ : PMF (Profile G)) (f : Profile G → ℝ) :
    expect μ f =
      ∑ p : Bool × Bool, (μ (L.profile p.1 p.2)).toReal * f (L.profile p.1 p.2) := by
  letI := Fintype.ofFinite ι
  letI : DecidableEq ι := L.decidableEqPlayer
  letI : ∀ i : ι, Fintype (G.Strategy i) := fun i => L.fintypeStrategy i
  rw [expect_eq_sum]
  exact Fintype.sum_equiv (L.profilePairEquiv)
    (fun σ : Profile G => (μ σ).toReal * f σ)
    (fun p : Bool × Bool => (μ (L.profile p.1 p.2)).toReal * f (L.profile p.1 p.2))
    (by
      intro σ
      change (μ σ).toReal * f σ =
        (μ (L.profile (L.toBool (L.playerOf true) (σ (L.playerOf true)))
          (L.toBool (L.playerOf false) (σ (L.playerOf false))))).toReal *
          f (L.profile (L.toBool (L.playerOf true) (σ (L.playerOf true)))
            (L.toBool (L.playerOf false) (σ (L.playerOf false))))
      have hσ := L.profilePairEquiv.left_inv σ
      change L.profile (L.toBool (L.playerOf true) (σ (L.playerOf true)))
        (L.toBool (L.playerOf false) (σ (L.playerOf false))) = σ at hσ
      rw [hσ])

theorem correlatedEu_eq_sum_profilePair
    [Finite ι] [Finite G.Outcome]
    (μ : PMF (Profile G)) (who : ι) :
    G.correlatedEu μ who =
      ∑ p : Bool × Bool, (μ (L.profile p.1 p.2)).toReal *
        G.eu (L.profile p.1 p.2) who := by
  letI := Fintype.ofFinite ι
  rw [G.correlatedEu_eq_expect_eu μ who]
  exact L.expect_eq_sum_profilePair μ (fun σ => G.eu σ who)

theorem update_profile_truePlayer
    [DecidableEq ι] (a b a' : Bool) :
    Function.update (L.profile a b) (L.playerOf true) (L.action (L.playerOf true) a') =
      L.profile a' b := by
  funext i
  by_cases hi : i = L.playerOf true
  · subst i
    simp [Function.update]
  · have hplayer : L.player i = false := by
      cases hw : L.player i
      · rfl
      · exact (hi (by simpa [playerOf] using congrArg L.player.symm hw)).elim
    simp [Function.update, hi, profile, hplayer]

theorem update_profile_falsePlayer
    [DecidableEq ι] (a b b' : Bool) :
    Function.update (L.profile a b) (L.playerOf false) (L.action (L.playerOf false) b') =
      L.profile a b' := by
  funext i
  by_cases hi : i = L.playerOf false
  · subst i
    simp [Function.update]
  · have hplayer : L.player i = true := by
      cases hw : L.player i
      · exact (hi (by simpa [playerOf] using congrArg L.player.symm hw)).elim
      · rfl
    simp [Function.update, hi, profile, hplayer]

end BinaryActionLabels

namespace MatchingPenniesLike

variable {ι : Type} {G : KernelGame ι} {L : BinaryActionLabels G}

private theorem ce_prob_true_true_ge_true_false
    [Finite ι] [DecidableEq ι] [Finite G.Outcome]
    (h : G.MatchingPenniesLike L) {μ : PMF (Profile G)}
    (hCE : G.IsCorrelatedEq μ) :
    (μ (L.profile true true)).toReal ≥ (μ (L.profile true false)).toReal := by
  letI := Fintype.ofFinite ι
  let p0 := L.playerOf true
  let dev : G.Strategy p0 → G.Strategy p0 := fun s =>
    if L.toBool p0 s then L.action p0 false else s
  have hineq := hCE p0 dev
  rw [L.correlatedEu_eq_sum_profilePair μ p0] at hineq
  rw [correlatedEu_unilateralDeviationDistribution_eq_expect_update
    (G := G) μ p0 dev] at hineq
  rw [L.expect_eq_sum_profilePair] at hineq
  simp [Fintype.sum_prod_type, p0, dev, h.eu_true,
    BinaryActionLabels.update_profile_truePlayer, ge_iff_le] at hineq
  nlinarith [h.scale_pos]

private theorem ce_prob_true_false_ge_false_false
    [Finite ι] [DecidableEq ι] [Finite G.Outcome]
    (h : G.MatchingPenniesLike L) {μ : PMF (Profile G)}
    (hCE : G.IsCorrelatedEq μ) :
    (μ (L.profile true false)).toReal ≥ (μ (L.profile false false)).toReal := by
  letI := Fintype.ofFinite ι
  let p1 := L.playerOf false
  let dev : G.Strategy p1 → G.Strategy p1 := fun s =>
    if L.toBool p1 s then s else L.action p1 true
  have hineq := hCE p1 dev
  rw [L.correlatedEu_eq_sum_profilePair μ p1] at hineq
  rw [correlatedEu_unilateralDeviationDistribution_eq_expect_update
    (G := G) μ p1 dev] at hineq
  rw [L.expect_eq_sum_profilePair] at hineq
  simp [Fintype.sum_prod_type, p1, dev, h.eu_false,
    BinaryActionLabels.update_profile_falsePlayer, ge_iff_le] at hineq
  nlinarith [h.scale_pos]

private theorem ce_prob_false_false_ge_false_true
    [Finite ι] [DecidableEq ι] [Finite G.Outcome]
    (h : G.MatchingPenniesLike L) {μ : PMF (Profile G)}
    (hCE : G.IsCorrelatedEq μ) :
    (μ (L.profile false false)).toReal ≥ (μ (L.profile false true)).toReal := by
  letI := Fintype.ofFinite ι
  let p0 := L.playerOf true
  let dev : G.Strategy p0 → G.Strategy p0 := fun s =>
    if L.toBool p0 s then s else L.action p0 true
  have hineq := hCE p0 dev
  rw [L.correlatedEu_eq_sum_profilePair μ p0] at hineq
  rw [correlatedEu_unilateralDeviationDistribution_eq_expect_update
    (G := G) μ p0 dev] at hineq
  rw [L.expect_eq_sum_profilePair] at hineq
  simp [Fintype.sum_prod_type, p0, dev, h.eu_true,
    BinaryActionLabels.update_profile_truePlayer, ge_iff_le] at hineq
  nlinarith [h.scale_pos]

private theorem ce_prob_false_true_ge_true_true
    [Finite ι] [DecidableEq ι] [Finite G.Outcome]
    (h : G.MatchingPenniesLike L) {μ : PMF (Profile G)}
    (hCE : G.IsCorrelatedEq μ) :
    (μ (L.profile false true)).toReal ≥ (μ (L.profile true true)).toReal := by
  letI := Fintype.ofFinite ι
  let p1 := L.playerOf false
  let dev : G.Strategy p1 → G.Strategy p1 := fun s =>
    if L.toBool p1 s then L.action p1 false else s
  have hineq := hCE p1 dev
  rw [L.correlatedEu_eq_sum_profilePair μ p1] at hineq
  rw [correlatedEu_unilateralDeviationDistribution_eq_expect_update
    (G := G) μ p1 dev] at hineq
  rw [L.expect_eq_sum_profilePair] at hineq
  simp [Fintype.sum_prod_type, p1, dev, h.eu_false,
    BinaryActionLabels.update_profile_falsePlayer, ge_iff_le] at hineq
  nlinarith [h.scale_pos]

theorem correlated_eq_profile_prob_eq_quarter
    [Finite ι] [DecidableEq ι] [Finite G.Outcome]
    (h : G.MatchingPenniesLike L) {μ : PMF (Profile G)}
    (hCE : G.IsCorrelatedEq μ) (a b : Bool) :
    (μ (L.profile a b)).toReal = (1 / 4 : ℝ) := by
  letI := Fintype.ofFinite ι
  have hHH_HT := ce_prob_true_true_ge_true_false h hCE
  have hHT_TT := ce_prob_true_false_ge_false_false h hCE
  have hTT_TH := ce_prob_false_false_ge_false_true h hCE
  have hTH_HH := ce_prob_false_true_ge_true_true h hCE
  have hall :
      (μ (L.profile true true)).toReal =
        (μ (L.profile true false)).toReal ∧
      (μ (L.profile true false)).toReal =
        (μ (L.profile false false)).toReal ∧
      (μ (L.profile false false)).toReal =
        (μ (L.profile false true)).toReal := by
    constructor
    · linarith
    constructor <;> linarith
  letI : ∀ i : ι, Fintype (G.Strategy i) := fun i => L.fintypeStrategy i
  have hsum_pairs : ∑ p : Bool × Bool, (μ (L.profile p.1 p.2)).toReal = 1 := by
    have h := L.expect_eq_sum_profilePair μ (fun _ => (1 : ℝ))
    simpa using h.symm
  simp [Fintype.sum_prod_type] at hsum_pairs
  have hquarter_HH : (μ (L.profile true true)).toReal = (1 / 4 : ℝ) := by
    linarith
  cases a <;> cases b <;> linarith [hall.1, hall.2.1, hall.2.2, hquarter_HH]

theorem correlated_eq_unique
    [Fintype ι] [DecidableEq ι] [Finite G.Outcome]
    (h : G.MatchingPenniesLike L) {μ : PMF (Profile G)}
    (hCE : G.IsCorrelatedEq μ) :
    μ = Math.PMFProduct.pmfPi L.uniformMixedProfile := by
  letI : ∀ i : ι, Fintype (G.Strategy i) := fun i => L.fintypeStrategy i
  letI : ∀ i : ι, Nonempty (G.Strategy i) := fun i => L.nonemptyStrategy i
  apply PMF.ext
  intro σ
  let p := L.profilePairEquiv σ
  have hσ : σ = L.profile p.1 p.2 := (L.profilePairEquiv.left_inv σ).symm
  rw [hσ]
  have hμ := h.correlated_eq_profile_prob_eq_quarter hCE p.1 p.2
  have hprod :
      (Math.PMFProduct.pmfPi L.uniformMixedProfile (L.profile p.1 p.2)).toReal =
        (1 / 4 : ℝ) := by
    rw [Math.PMFProduct.pmfPi_apply, ENNReal.toReal_prod]
    rw [show (∏ i : ι, ((L.uniformMixedProfile i) (L.profile p.1 p.2 i)).toReal) =
      ((L.uniformMixedProfile (L.playerOf true))
          (L.action (L.playerOf true) p.1)).toReal *
        ((L.uniformMixedProfile (L.playerOf false))
          (L.action (L.playerOf false) p.2)).toReal by
        have hprod := Fintype.prod_equiv L.player.symm
          (fun b : Bool =>
            ((L.uniformMixedProfile (L.playerOf b))
              (L.action (L.playerOf b) (if b then p.1 else p.2))).toReal)
          (fun i : ι => ((L.uniformMixedProfile i) (L.profile p.1 p.2 i)).toReal)
          (by
            intro b
            simp [BinaryActionLabels.playerOf, BinaryActionLabels.profile]
            rfl)
        rw [← hprod]
        simp [mul_comm]]
    rw [show ((L.uniformMixedProfile (L.playerOf true))
          (L.action (L.playerOf true) p.1)).toReal = (1 / 2 : ℝ) by
        cases p.1
        · rw [BinaryActionLabels.prob_false_toReal]
          rw [L.probTrue_labeledUniformMixedProfile]
          norm_num
        · exact L.probTrue_labeledUniformMixedProfile (L.playerOf true)]
    rw [show ((L.uniformMixedProfile (L.playerOf false))
          (L.action (L.playerOf false) p.2)).toReal = (1 / 2 : ℝ) by
        cases p.2
        · rw [BinaryActionLabels.prob_false_toReal]
          rw [L.probTrue_labeledUniformMixedProfile]
          norm_num
        · exact L.probTrue_labeledUniformMixedProfile (L.playerOf false)]
    norm_num
  exact (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp (hμ.trans hprod.symm)

end MatchingPenniesLike

end KernelGame

end GameTheory
