/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AdaptiveLocalResponseRecursion

/-!
# Adaptive certificates characterize uniform equilibrium payoffs

The adaptive-potential certificate is not merely a sufficient verification
interface.  For a payoff already known to be uniform, constant target
potentials and signed charge sequences given by the expected stage-payoff
gaps provide a certificate.  Thus the certificate is exactly equivalent to
the semantic uniform-payoff property.

The same observation also packages every certificate as a one-node completed
adaptive local-response recursion.  These results are conceptual guardrails:
they assume a particular uniform payoff and do not prove that one exists.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type}

/-- A uniform equilibrium payoff gives an adaptive-potential certificate.

At certificate accuracy `δ`, use a uniform `δ / 2`-equilibrium profile.
All three history potentials are constantly equal to the target payoff.
Their charge sequences are respectively
`v - expectedStagePayoff`, `expectedStagePayoff - v`, and the latter gap
under a unilateral deviation. -/
theorem isAdaptivePotentialEquilibriumCertificate_of_isUniformEquilibriumPayoff
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (s₀ : G.State) (v : Payoff ι)
    (hv : G.IsUniformEquilibriumPayoff s₀ v) :
    G.IsAdaptivePotentialEquilibriumCertificate s₀ v := by
  intro δ hδ
  obtain ⟨σ, Tbase, hσ⟩ := hv (δ / 2) (by linarith)
  let φ : ι → G.HistoryPotential := fun i _ _ => v i
  let elo : ι → ℕ → ℝ :=
    fun i t => v i - G.expectedStagePayoff σ s₀ t i
  let ehi : ι → ℕ → ℝ :=
    fun i t => G.expectedStagePayoff σ s₀ t i - v i
  let edv : ∀ i, G.BehaviorStrategy i → ℕ → ℝ :=
    fun i dev t =>
      G.expectedStagePayoff (Function.update σ i dev) s₀ t i - v i
  refine ⟨σ, max 2 Tbase, φ, φ, φ, elo, ehi, edv,
    le_max_left 2 Tbase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [φ, hδ.le]
  · intro i
    simp [φ, hδ.le]
  · intro i
    simp [φ, hδ.le]
  · intro i t
    simp [φ, expectedHistoryValue, expect_const]
  · intro i t
    simp [φ, elo, expectedHistoryValue, expect_const]
  · intro i t
    simp [φ, expectedHistoryValue, expect_const]
  · intro i t
    simp [φ, ehi, expectedHistoryValue, expect_const]
  · intro i dev t
    simp [φ, expectedHistoryValue, expect_const]
  · intro i dev t
    simp [φ, edv, expectedHistoryValue, expect_const]
  · intro i T hT
    have hbase : Tbase ≤ T := le_trans (le_max_right 2 Tbase) hT
    have hTpos : 0 < T := by omega
    have hcharge :
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, elo i t =
          v i - G.finiteAveragePayoff s₀ T σ i := by
      rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
      simp only [elo, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hTpos)]
    rw [hcharge]
    have hpay := (hσ T hbase).2 i
    rw [abs_le] at hpay
    linarith
  · intro i T hT
    have hbase : Tbase ≤ T := le_trans (le_max_right 2 Tbase) hT
    have hTpos : 0 < T := by omega
    have hcharge :
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, ehi i t =
          G.finiteAveragePayoff s₀ T σ i - v i := by
      rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
      simp only [ehi, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hTpos)]
    rw [hcharge]
    have hpay := (hσ T hbase).2 i
    rw [abs_le] at hpay
    linarith
  · intro i dev T hT
    have hbase : Tbase ≤ T := le_trans (le_max_right 2 Tbase) hT
    have hTpos : 0 < T := by omega
    have hcharge :
        (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, edv i dev t =
          G.finiteAveragePayoff s₀ T (Function.update σ i dev) i - v i := by
      rw [G.finiteAveragePayoff_eq_sum_expectedStagePayoff]
      simp only [edv, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
      field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hTpos)]
    rw [hcharge]
    have hNash := (hσ T hbase).1 i dev
    have hpay := (hσ T hbase).2 i
    rw [abs_le] at hpay
    linarith

/-- The adaptive-potential verification interface is exactly the semantic
uniform-equilibrium-payoff property. -/
theorem isUniformEquilibriumPayoff_iff_isAdaptivePotentialEquilibriumCertificate
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (s₀ : G.State) (v : Payoff ι) :
    G.IsUniformEquilibriumPayoff s₀ v ↔
      G.IsAdaptivePotentialEquilibriumCertificate s₀ v := by
  constructor
  · exact G.isAdaptivePotentialEquilibriumCertificate_of_isUniformEquilibriumPayoff
      s₀ v
  · exact G.isUniformEquilibriumPayoff_of_isAdaptivePotentialEquilibriumCertificate
      s₀ v

/-- Package one adaptive-potential certificate instance as a recursion with
one node and no children. -/
def oneNodeAdaptiveLocalResponseRecursionAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (s₀ : G.State) (v : Payoff ι) (δ : ℝ)
    (hcert : G.IsAdaptivePotentialCertificateAt s₀ v δ) :
    G.AdaptiveLocalResponseRecursionAt s₀ v δ where
  Rank := PUnit
  rankLt := fun _ _ => False
  rank_wellFounded := ⟨fun _ => ⟨_, fun _ h => h.elim⟩⟩
  Node := PUnit
  rank := fun _ => PUnit.unit
  root := PUnit.unit
  entry := fun _ => s₀
  target := fun _ => v
  root_entry := rfl
  root_target := rfl
  MixedPlayerContinuationCompatibility := fun _ => True
  LegalCoreHistoryEntryInterface := fun _ => True
  mixedPlayerContinuationCompatibility := fun _ => True.intro
  legalCoreHistoryEntryInterface := fun _ => True.intro
  closeLocalResponse _ _ _ _ := hcert

/-- Package an adaptive-potential equilibrium certificate as a completed
one-node adaptive local-response recursion at every accuracy. -/
def completedOneNodeAdaptiveLocalResponseRecursion
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (s₀ : G.State) (v : Payoff ι)
    (hcert : G.IsAdaptivePotentialEquilibriumCertificate s₀ v) :
    G.CompletedAdaptiveLocalResponseRecursion s₀ v where
  recursionAt δ hδ :=
    G.oneNodeAdaptiveLocalResponseRecursionAt s₀ v δ (hcert δ hδ)

/-- A completed adaptive recursion is equivalent packaging of an adaptive
potential equilibrium certificate: the reverse direction uses a one-node
recursion. -/
theorem nonempty_completedAdaptiveLocalResponseRecursion_iff
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (s₀ : G.State) (v : Payoff ι) :
    Nonempty (G.CompletedAdaptiveLocalResponseRecursion s₀ v) ↔
      G.IsAdaptivePotentialEquilibriumCertificate s₀ v := by
  constructor
  · rintro ⟨construction⟩
    exact construction.isAdaptivePotentialEquilibriumCertificate
  · intro hcert
    exact ⟨G.completedOneNodeAdaptiveLocalResponseRecursion s₀ v hcert⟩

/-- Uniform equilibrium payoffs are equivalently witnessed by a completed
adaptive local-response recursion, which may always be chosen to have one
node. -/
theorem isUniformEquilibriumPayoff_iff_nonempty_completedAdaptiveLocalResponseRecursion
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (s₀ : G.State) (v : Payoff ι) :
    G.IsUniformEquilibriumPayoff s₀ v ↔
      Nonempty (G.CompletedAdaptiveLocalResponseRecursion s₀ v) := by
  rw [G.isUniformEquilibriumPayoff_iff_isAdaptivePotentialEquilibriumCertificate,
    G.nonempty_completedAdaptiveLocalResponseRecursion_iff]

end StochasticGame
end GameTheory
