/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.Bayesian.Monotonicity

/-!
# Affine maximizers are dominant-strategy truthful

The sufficiency companion to `Monotonicity`: an **affine maximizer** — choose the
alternative maximizing `∑ᵢ wᵢ · valueᵢ(θᵢ, alt) + κ(alt)` with positive weights `wᵢ`
and an alternative bias `κ`, paired with Clarke (externality) payments — is
dominant-strategy incentive compatible. Affine maximizers are, by Roberts' theorem,
essentially the *only* DSIC rules on unrestricted domains; this file proves the easy
direction (they are truthful), the canonical truthful class behind VCG. Serves
Lavi/Monderer mechanism design.

The separate `GameTheory.Auctions.VCG` API packages general Groves payments
with an arbitrary report-independent `h` term and an informational-game view.
The present module uses finite alternatives and the canonical Clarke pivot,
but additionally covers positive affine weights and alternative biases.

## Main definitions

* `affineObjective` / `affineChoice` — the weighted-welfare objective and its maximizer
* `pivotWelfare` — the others' best attainable weighted welfare (the Clarke charge)
* `affineMaximizer` — the affine-maximizer mechanism with Clarke pivot payments

## Main results

* `affineMaximizer_isDSIC` — with positive weights, the affine maximizer is DSIC
* `affineMaximizer_payment_nonneg` — the Clarke pivot charges no agent a subsidy
* `vcg_isDSIC` — VCG (efficient allocation, unit weights) is the special case
-/

open scoped BigOperators

namespace GameTheory

variable {ι Alt : Type} [Fintype ι] [DecidableEq ι] [Fintype Alt] [Nonempty Alt]
  (Θ : ι → Type) (value : (i : ι) → Θ i → Alt → ℝ) (w : ι → ℝ) (κ : Alt → ℝ)

/-- The affine objective `∑ᵢ wᵢ · valueᵢ(θᵢ, alt) + κ(alt)`. -/
def affineObjective (θ : ∀ i, Θ i) (alt : Alt) : ℝ :=
  (∑ i, w i * value i (θ i) alt) + κ alt

/-- The alternative maximizing the affine objective. -/
noncomputable def affineChoice (θ : ∀ i, Θ i) : Alt :=
  (Finset.exists_max_image Finset.univ (affineObjective Θ value w κ θ)
    Finset.univ_nonempty).choose

omit [DecidableEq ι] in
theorem affineChoice_max (θ : ∀ i, Θ i) (alt : Alt) :
    affineObjective Θ value w κ θ alt ≤
      affineObjective Θ value w κ θ (affineChoice Θ value w κ θ) :=
  (Finset.exists_max_image Finset.univ (affineObjective Θ value w κ θ)
    Finset.univ_nonempty).choose_spec.2 alt (Finset.mem_univ alt)

/-- The weighted welfare of everyone *except* `i` (plus the alternative bias) at a
given alternative. -/
def othersWelfare (θ : ∀ i, Θ i) (i : ι) (alt : Alt) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, w j * value j (θ j) alt) + κ alt

/-- The best weighted welfare the *other* agents (and the bias) can attain, ignoring
`i`'s own valuation — the quantity the Clarke pivot charges against. -/
noncomputable def pivotWelfare (θ : ∀ i, Θ i) (i : ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (othersWelfare Θ value w κ θ i)

/-- The **affine-maximizer mechanism with Clarke pivot payments**: choose
`affineChoice` and charge each agent the externality it imposes on the others —
their best attainable weighted welfare minus their welfare at the chosen
alternative, scaled by `1/wᵢ`. -/
noncomputable def affineMaximizer : SCFWithPayments ι Alt where
  Θ := Θ
  value := value
  choice := affineChoice Θ value w κ
  payment := fun θ i => (1 / w i) *
    (pivotWelfare Θ value w κ θ i
      - othersWelfare Θ value w κ θ i (affineChoice Θ value w κ θ))

omit [Fintype Alt] [Nonempty Alt] in
/-- `othersWelfare … i` is **independent of agent `i`'s own report**: it sums only
over the others. -/
theorem othersWelfare_independentOfCoordinate (i : ι) :
    Math.Probability.IndependentOfCoordinate i (fun θ => othersWelfare Θ value w κ θ i) := by
  intro θ θᵢ
  funext alt
  simp only [othersWelfare]
  congr 1
  exact Finset.sum_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

omit [Fintype Alt] [Nonempty Alt] in
/-- The Clarke charge `pivotWelfare` against agent `i` depends only on the *others'*
reports, so it is unchanged between the truthful profile and `i`'s misreport. -/
theorem othersWelfare_eq_of_agree {i : ι} {report : ∀ j, Θ j} {θ : ∀ j, Θ j}
    (hrep : ∀ j, j ≠ i → report j = θ j) :
    othersWelfare Θ value w κ report i = othersWelfare Θ value w κ θ i :=
  (othersWelfare_independentOfCoordinate Θ value w κ i).eq_of_agree hrep

/-- Scaling an agent's quasilinear utility by its (positive) weight recovers the full
affine objective at the chosen alternative *minus the report-independent Clarke
charge*, provided the others' reports match `θ` (which holds both at the truthful
profile and at a single-agent misreport). Since the charge does not depend on `i`'s
own report, it drops out of the truthfulness comparison. -/
theorem affineMaximizer_wUtil {i : ι} (hwi : w i ≠ 0) {report : ∀ j, Θ j}
    (θ : ∀ j, Θ j) (hrep : ∀ j, j ≠ i → report j = θ j) :
    w i * (affineMaximizer Θ value w κ).utility report i (θ i) =
      affineObjective Θ value w κ θ (affineChoice Θ value w κ report)
        - pivotWelfare Θ value w κ θ i := by
  have hfun := othersWelfare_eq_of_agree Θ value w κ hrep
  have hpiv : pivotWelfare Θ value w κ report i = pivotWelfare Θ value w κ θ i := by
    unfold pivotWelfare; rw [hfun]
  simp only [SCFWithPayments.utility, affineMaximizer]
  rw [hpiv, hfun]
  simp only [affineObjective, othersWelfare]
  rw [← Finset.add_sum_erase Finset.univ
    (fun j => w j * value j (θ j) (affineChoice Θ value w κ report)) (Finset.mem_univ i)]
  field_simp
  ring

/-- **The Clarke pivot payment is nonnegative.** Each agent pays the (nonnegative)
externality it imposes on the others, never receiving a subsidy. Only the
weight of player `i` need be positive. -/
theorem affineMaximizer_payment_nonneg (θ : ∀ j, Θ j) (i : ι) (hwi : 0 < w i) :
    0 ≤ (affineMaximizer Θ value w κ).payment θ i := by
  simp only [affineMaximizer]
  refine mul_nonneg (le_of_lt (div_pos one_pos hwi)) ?_
  rw [sub_nonneg]
  exact Finset.le_sup' (othersWelfare Θ value w κ θ i) (Finset.mem_univ _)

/-- **Affine maximizers are truthful.** With positive weights, the affine-maximizer
mechanism (with Clarke pivot payments) is dominant-strategy incentive compatible. -/
theorem affineMaximizer_isDSIC (hw : ∀ i, 0 < w i) :
    (affineMaximizer Θ value w κ).IsDSIC := by
  intro i θ θ'ᵢ
  have ht := affineMaximizer_wUtil Θ value w κ (ne_of_gt (hw i)) θ (fun _ _ => rfl)
  have hm := affineMaximizer_wUtil Θ value w κ (ne_of_gt (hw i)) (report := Function.update θ i θ'ᵢ)
    θ (fun j hj => Function.update_of_ne hj _ _)
  have hmax := affineChoice_max Θ value w κ θ (affineChoice Θ value w κ (Function.update θ i θ'ᵢ))
  exact le_of_mul_le_mul_left
    (le_trans (le_of_eq hm)
      (le_trans (sub_le_sub_right hmax (pivotWelfare Θ value w κ θ i)) (le_of_eq ht.symm)))
    (hw i)

/-- The **VCG (efficient) mechanism**: the affine maximizer with unit weights and no
bias, i.e. it maximizes utilitarian welfare `∑ᵢ valueᵢ(θᵢ, ·)` and charges Clarke
pivot payments. -/
noncomputable def vcg : SCFWithPayments ι Alt :=
  affineMaximizer Θ value (fun _ => 1) (fun _ => 0)

/-- **Vickrey–Clarke–Groves is truthful.** The efficient (utilitarian-welfare-
maximizing) allocation with Clarke payments is dominant-strategy incentive
compatible — the special case of `affineMaximizer_isDSIC` with unit weights. -/
theorem vcg_isDSIC : (vcg Θ value).IsDSIC :=
  affineMaximizer_isDSIC Θ value (fun _ => 1) (fun _ => 0) (fun _ => one_pos)

end GameTheory
