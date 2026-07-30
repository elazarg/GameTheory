/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.MovingHarmonicCorrection

/-!
# Stabilization of the analytic stage-response branch

After the analytic Fink action support freezes, feasibility of the doubled
normalized Farkas system stabilizes. A feasible certificate reconstructs a
semantic normalized Fink obstruction flow. Infeasibility excludes every
such flow, so the pointwise Fink alternative stays in its harmonic stage
adjustment branch.

Consequently, on one punctured right neighborhood either every valid slice
has a harmonic representation of its supported stage gains, or every valid
slice has a normalized pure-stage obstruction. The latter branch feeds
directly into the coherent analytic action repair.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math Math.LinearAlgebra Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace NormalizedFinkSupportTangentObstructionFlow

omit [∀ i, DecidableEq (G.Act i)] in
/-- Reconstruct a semantic normalized Fink obstruction flow from any signed
coefficient vector satisfying the finite balance and target equations. -/
def ofCoefficient
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    (coefficient : FinkObstructionColumn G → ℝ)
    (hbalance :
      Matrix.mulVec (G.finkObstructionBalance z) coefficient = 0)
    (hmass :
      (∑ column,
        G.finkObstructionMass z H K column *
          coefficient column) = 1) :
    G.NormalizedFinkSupportTangentObstructionFlow z H K where
  residualWeight s who := coefficient (Sum.inl (s, who))
  actionWeight s who d := coefficient (Sum.inr ⟨who, s, d⟩)
  operator_balance := by
    intro A
    let adjustment := G.finkAdjustmentCoefficient A
    have hdot :
        dotProduct coefficient
            (Matrix.mulVec
              (G.finkObstructionBalance z).transpose adjustment) =
          0 := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
        hbalance]
      simp
    simp only [dotProduct] at hdot
    rw [Fintype.sum_sum_type] at hdot
    have hresidual :
        (∑ residual,
          coefficient (Sum.inl residual) *
            Matrix.mulVec
              (G.finkObstructionBalance z).transpose
              adjustment (Sum.inl residual)) =
          ∑ s, ∑ who,
            coefficient (Sum.inl (s, who)) *
              G.finkContinuationResidualVector A z s who := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro who _
      rw [G.finkObstructionTranspose_mulVec_adjustment_residual]
    have haction :
        (∑ e,
          coefficient (Sum.inr e) *
            Matrix.mulVec
              (G.finkObstructionBalance z).transpose
              adjustment (Sum.inr e)) =
          ∑ s, ∑ who, ∑ d,
            coefficient (Sum.inr ⟨who, s, d⟩) *
              (if G.finkProfile z s who d ≠ 0 then
                G.finkContinuationGain A z s who d
              else 0) := by
      calc
        (∑ e,
          coefficient (Sum.inr e) *
            Matrix.mulVec
              (G.finkObstructionBalance z).transpose
              adjustment (Sum.inr e)) =
            ∑ who, ∑ s, ∑ d,
              coefficient (Sum.inr ⟨who, s, d⟩) *
                (if G.finkProfile z s who d ≠ 0 then
                  G.finkContinuationGain A z s who d
                else 0) := by
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro who _
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro s _
          apply Finset.sum_congr rfl
          intro d _
          rw [
            G.finkObstructionTranspose_mulVec_adjustment_action]
        _ = _ := Finset.sum_comm
    rw [hresidual, haction] at hdot
    exact hdot
  target_balance := by
    have hmass' := hmass
    simp only [finkObstructionMass, Fintype.sum_sum_type,
      Fintype.sum_prod_type, Fintype.sum_sigma, zero_mul,
      Finset.sum_const_zero, zero_add, ite_mul] at hmass'
    rw [Finset.sum_comm] at hmass'
    simpa [mul_comm] using hmass'

omit [∀ i, DecidableEq (G.Act i)] in
/-- Every certificate in the doubled nonnegative system reconstructs a
semantic normalized Fink obstruction flow. -/
theorem nonempty_of_orientedFarkasCertificate
    {U : ℝ} (z : G.finkDomain U)
    (H K : G.State → Payoff ι)
    {certificate :
      (FinkObstructionColumn G × Bool) → ℝ}
    (hcertificate :
      certificate ∈
        normalizedFarkasCertificateSet
          (orientedFarkasBalance
            (G.finkObstructionBalance z))
          (orientedFarkasMass
            (G.finkObstructionMass z H K))) :
    Nonempty
      (G.NormalizedFinkSupportTangentObstructionFlow z H K) := by
  obtain ⟨hbalance, hmass⟩ :=
    normalizedFarkasCertificateSet_oriented_toSigned
      (G.finkObstructionBalance z)
      (G.finkObstructionMass z H K) hcertificate
  exact ⟨ofCoefficient z H K
    (orientedFarkasToSigned certificate) hbalance hmass⟩

end NormalizedFinkSupportTangentObstructionFlow

namespace AnalyticBellmanGerm

omit [DecidableEq G.State] in
/-- The equal-continuation stage dichotomy has one eventually fixed branch.
Both branches use the exact positive-parameter Fink support. -/
theorem stageResponseBranch_eventually_stabilizes
    (germ : G.AnalyticBellmanGerm)
    (H : G.State → Payoff ι) :
    (∀ᶠ t in nhdsWithin 0 (Ioi 0),
      t ∈ Ioo (0 : ℝ) germ.radius ∧
        ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
          ∃ A : G.State → Payoff ι,
            G.finkContinuationResidualVector A
                (germ.finkPointAt ht) = 0 ∧
              ∀ s who (d : G.Act who),
                G.finkProfile
                    (germ.finkPointAt ht) s who d ≠ 0 →
                  G.finkContinuationGain A
                      (germ.finkPointAt ht) s who d =
                    G.finkStageGain
                      (germ.finkPointAt ht) s who d) ∨
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        t ∈ Ioo (0 : ℝ) germ.radius ∧
          ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
            Nonempty
              (G.NormalizedFinkSupportTangentObstructionFlow
                (germ.finkPointAt ht) H H) := by
  classical
  obtain ⟨supported, hsupport⟩ :=
    germ.exists_eventually_fixed_finkSupport
  let balance : ℝ →
      Matrix (FinkObstructionRow G)
        (FinkObstructionColumn G × Bool) ℝ :=
    fun t =>
      orientedFarkasBalance
        (germ.rawFinkObstructionBalance supported t)
  let mass : ℝ →
      (FinkObstructionColumn G × Bool) → ℝ :=
    fun t =>
      orientedFarkasMass
        (germ.rawFinkObstructionMass supported H H t)
  have hbalance :
      ∀ row column,
        AnalyticAt ℝ
          (fun t => balance t row column) 0 := by
    intro row column
    rcases column with ⟨column, positive⟩
    exact analyticAt_const.mul
      (germ.analytic_rawFinkObstructionBalance
        supported row column)
  have hmass :
      ∀ column,
        AnalyticAt ℝ (fun t => mass t column) 0 := by
    intro column
    rcases column with ⟨column, positive⟩
    exact analyticAt_const.mul
      (germ.analytic_rawFinkObstructionMass
        supported H H column)
  rcases
      analytic_normalizedFarkas_feasibility_eventually_stabilizes
        balance mass hbalance hmass with
    hcertificate | hnoCertificate
  · right
    filter_upwards [hsupport, hcertificate] with
        t hsupportAt hcertificateAt
    refine ⟨hsupportAt.1, fun ht => ?_⟩
    obtain ⟨certificate, hcertificate⟩ := hcertificateAt
    have hbalanceEq :=
      germ.rawFinkObstructionBalance_eq_finkPointAt
        supported ht (hsupportAt.2 ht)
    have hmassEq :=
      germ.rawFinkObstructionMass_eq_finkPointAt
        supported H H ht (hsupportAt.2 ht)
    have hsemantic :
        certificate ∈
          normalizedFarkasCertificateSet
            (orientedFarkasBalance
              (G.finkObstructionBalance
                (germ.finkPointAt ht)))
            (orientedFarkasMass
              (G.finkObstructionMass
                (germ.finkPointAt ht) H H)) := by
      simpa only [balance, mass, hbalanceEq, hmassEq] using
        hcertificate
    exact
      NormalizedFinkSupportTangentObstructionFlow.nonempty_of_orientedFarkasCertificate
        (germ.finkPointAt ht) H H hsemantic
  · left
    filter_upwards [hsupport, hnoCertificate] with
        t hsupportAt hnoCertificateAt
    refine ⟨hsupportAt.1, fun ht => ?_⟩
    rcases
        germ.stageHarmonicAdjustment_or_normalizedObstructionFlowAt
          ht H with hA | hF
    · exact hA
    · obtain ⟨F⟩ := hF
      have hsemanticCertificate :=
        F.orientedFarkasCertificate
          (germ.finkPointAt ht) H H
      have hbalanceEq :=
        germ.rawFinkObstructionBalance_eq_finkPointAt
          supported ht (hsupportAt.2 ht)
      have hmassEq :=
        germ.rawFinkObstructionMass_eq_finkPointAt
          supported H H ht (hsupportAt.2 ht)
      exfalso
      apply hnoCertificateAt
      refine ⟨signedFarkasToOriented F.coefficient, ?_⟩
      simpa only [balance, mass, hbalanceEq, hmassEq] using
        hsemanticCertificate

/-- Stabilized equal-continuation response: either every small valid slice
has a harmonic stage adjustment, or one coherent analytic action repair has
an exact positive aggregate pure-stage monomial. -/
theorem stageHarmonicAdjustment_or_analyticPureStageObstruction
    (germ : G.AnalyticBellmanGerm)
    (H : G.State → Payoff ι) :
    (∀ᶠ t in nhdsWithin 0 (Ioi 0),
      t ∈ Ioo (0 : ℝ) germ.radius ∧
        ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
          ∃ A : G.State → Payoff ι,
            G.finkContinuationResidualVector A
                (germ.finkPointAt ht) = 0 ∧
              ∀ s who (d : G.Act who),
                G.finkProfile
                    (germ.finkPointAt ht) s who d ≠ 0 →
                  G.finkContinuationGain A
                      (germ.finkPointAt ht) s who d =
                    G.finkStageGain
                      (germ.finkPointAt ht) s who d) ∨
      ∃ (supported :
            (Σ who : ι, G.State × G.Act who) → Bool)
          (poleOrder : ℕ)
          (repaired : ℝ → FinkObstructionColumn G → ℝ),
        AnalyticAt ℝ repaired 0 ∧
          ∀ᶠ t in nhdsWithin 0 (Ioi 0),
            t ∈ Ioo (0 : ℝ) germ.radius ∧
              (∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
                ∀ e : Σ who : ι, G.State × G.Act who,
                  supported e = true ↔
                    G.finkProfile (germ.finkPointAt ht)
                      e.2.1 e.1 e.2.2 ≠ 0) ∧
              Matrix.mulVec
                  (germ.rawFinkObstructionBalance supported t)
                  (repaired t) = 0 ∧
              (∑ e : Σ who : ι, G.State × G.Act who,
                  (if supported e then
                    germ.rawPureDeviationStageGainCurve
                      t e.2.1 e.1 e.2.2
                  else 0) * repaired t (Sum.inr e)) =
                germ.rawFinkSupportProduct supported t *
                  t ^ poleOrder ∧
              (∀ e : Σ who : ι, G.State × G.Act who,
                supported e = true →
                  0 < repaired t (Sum.inr e)) ∧
              0 <
                germ.rawFinkSupportProduct supported t *
                  t ^ poleOrder := by
  rcases germ.stageResponseBranch_eventually_stabilizes H with
    hA | hF
  · exact Or.inl hA
  · exact Or.inr
      (germ.exists_analytic_actionRepaired_eventual_pureStageObstructionFlow
          H (hF.mono fun _ ht => ht.2))

end AnalyticBellmanGerm

end StochasticGame
end GameTheory
