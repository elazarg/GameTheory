/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.AlgebraicSelection

/-!
# Analytic generator charge or annihilation

This file isolates the coefficient-level core of the analytic cone
dichotomy. A finite primal-dual generator expansion has nonnegative analytic
coefficients and nonnegative generator pairings.

If the total pairing is a nonzero germ, one fixed generator pair carries at
least the average charge and hence a positive power-law charge. If the total
pairing vanishes, every eventually live dual coefficient annihilates the
whole primal generator combination.

Turning the annihilation conclusion into a proper geometric face additionally
requires the semantic facts that the generators lie in a cone and its dual,
and that some live dual generator is nontrivial modulo the cone's orthogonal
complement.
-/

open Finset Set Topology

namespace Math

noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Contribution of one dual/primal generator pair. -/
def analyticGeneratorTerm
    (alpha : A → ℝ → ℝ) (beta : B → ℝ → ℝ)
    (pairing : A → B → ℝ) (ab : A × B) (t : ℝ) : ℝ :=
  alpha ab.1 t * beta ab.2 t * pairing ab.1 ab.2

/-- Total pairing of the two finite generator expansions. -/
def analyticGeneratorPairing
    (alpha : A → ℝ → ℝ) (beta : B → ℝ → ℝ)
    (pairing : A → B → ℝ) (t : ℝ) : ℝ :=
  ∑ ab : A × B, analyticGeneratorTerm alpha beta pairing ab t

/-- Pairing of one dual generator with the full primal expansion. -/
def analyticGeneratorRow
    (beta : B → ℝ → ℝ) (pairing : A → B → ℝ)
    (a : A) (t : ℝ) : ℝ :=
  ∑ b, beta b t * pairing a b

theorem analyticGeneratorPairing_eq_sum_rows
    (alpha : A → ℝ → ℝ) (beta : B → ℝ → ℝ)
    (pairing : A → B → ℝ) (t : ℝ) :
    analyticGeneratorPairing alpha beta pairing t =
      ∑ a, alpha a t * analyticGeneratorRow beta pairing a t := by
  rw [analyticGeneratorPairing, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [analyticGeneratorRow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp [analyticGeneratorTerm]
  ring

/-- If the analytic total pairing is not the zero right germ, one fixed
generator pair carries the average total and a positive power-law charge. -/
theorem exists_eventually_fixed_generator_powerCharge
    [Nonempty A] [Nonempty B]
    (alpha : A → ℝ → ℝ) (beta : B → ℝ → ℝ)
    (pairing : A → B → ℝ) {x₀ : ℝ}
    (halpha : ∀ a, AnalyticAt ℝ (alpha a) x₀)
    (hbeta : ∀ b, AnalyticAt ℝ (beta b) x₀)
    (halpha_nonneg : ∀ a,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 ≤ alpha a x)
    (hbeta_nonneg : ∀ b,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 ≤ beta b x)
    (hpairing_nonneg : ∀ a b, 0 ≤ pairing a b)
    (htotal :
      ¬∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        analyticGeneratorPairing alpha beta pairing x = 0) :
    ∃ a b n c, 0 < c ∧
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        c * (x - x₀) ^ n ≤
            (Fintype.card (A × B) : ℝ)⁻¹ *
              analyticGeneratorPairing alpha beta pairing x ∧
          (Fintype.card (A × B) : ℝ)⁻¹ *
              analyticGeneratorPairing alpha beta pairing x ≤
            analyticGeneratorTerm alpha beta pairing (a, b) x := by
  let term : A × B → ℝ → ℝ :=
    analyticGeneratorTerm alpha beta pairing
  have hterm_analytic : ∀ ab, AnalyticAt ℝ (term ab) x₀ := by
    intro ab
    exact ((halpha ab.1).mul (hbeta ab.2)).mul analyticAt_const
  have hterm_nonneg : ∀ ab,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 ≤ term ab x := by
    intro ab
    filter_upwards [halpha_nonneg ab.1, hbeta_nonneg ab.2] with x ha hb
    exact mul_nonneg (mul_nonneg ha hb) (hpairing_nonneg ab.1 ab.2)
  have htotal' :
      ¬∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∑ ab, term ab x = 0 := by
    simpa [term, analyticGeneratorPairing] using htotal
  obtain ⟨ab, n, c, hc, hcharge⟩ :=
    finite_analytic_nonnegative_family_eventually_fixed_power_charge
      term hterm_analytic hterm_nonneg htotal'
  exact ⟨ab.1, ab.2, n, c, hc, by
    simpa [term, analyticGeneratorPairing] using hcharge⟩

/-- If the total pairing vanishes, the coefficient support of the dual
expansion stabilizes and every live dual generator annihilates the full
primal expansion. -/
theorem exists_eventual_liveGenerators_annihilate_of_pairing_eq_zero
    (alpha : A → ℝ → ℝ) (beta : B → ℝ → ℝ)
    (pairing : A → B → ℝ) {x₀ : ℝ}
    (halpha : ∀ a, AnalyticAt ℝ (alpha a) x₀)
    (halpha_nonneg : ∀ a,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 ≤ alpha a x)
    (hbeta_nonneg : ∀ b,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), 0 ≤ beta b x)
    (hpairing_nonneg : ∀ a b, 0 ≤ pairing a b)
    (htotal :
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀),
        analyticGeneratorPairing alpha beta pairing x = 0) :
    ∃ live : A → Prop,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioi x₀), ∀ a,
        (0 < alpha a x ↔ live a) ∧
          (live a → analyticGeneratorRow beta pairing a x = 0) := by
  obtain ⟨zero, hzero⟩ :=
    finite_analytic_nonnegative_family_eventually_active_set
      alpha halpha halpha_nonneg
  let live : A → Prop := fun a => ¬zero a
  refine ⟨live, ?_⟩
  filter_upwards [hzero, htotal,
    Filter.eventually_all.mpr halpha_nonneg,
    Filter.eventually_all.mpr hbeta_nonneg] with x hxzero hxtotal
      hxalpha hxbeta
  intro a
  have hrow_nonneg : ∀ a, 0 ≤ analyticGeneratorRow beta pairing a x := by
    intro a'
    exact Finset.sum_nonneg fun b _ =>
      mul_nonneg (hxbeta b) (hpairing_nonneg a' b)
  have hterm_nonneg :
      ∀ a, 0 ≤ alpha a x * analyticGeneratorRow beta pairing a x :=
    fun a' => mul_nonneg (hxalpha a') (hrow_nonneg a')
  have hsum_zero :
      (∑ a, alpha a x * analyticGeneratorRow beta pairing a x) = 0 := by
    rw [← analyticGeneratorPairing_eq_sum_rows]
    exact hxtotal
  have hterm_zero :
      alpha a x * analyticGeneratorRow beta pairing a x = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun a' _ => hterm_nonneg a')).mp hsum_zero a (Finset.mem_univ a)
  constructor
  · simpa [live] using (hxzero a).2
  · intro hlive
    exact (mul_eq_zero.mp hterm_zero).resolve_left
      (ne_of_gt ((hxzero a).2.mpr hlive))

end

end Math
