/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.Monotonicity

/-!
# Affine maximizers are dominant-strategy truthful

The sufficiency companion to `Monotonicity`: an **affine maximizer** — choose the
alternative maximizing `∑ᵢ wᵢ · valueᵢ(θᵢ, alt) + κ(alt)` with positive weights `wᵢ`
and an alternative bias `κ`, paired with Clarke (externality) payments — is
dominant-strategy incentive compatible. Affine maximizers are, by Roberts' theorem,
essentially the *only* DSIC rules on unrestricted domains; this file proves the easy
direction (they are truthful), the canonical truthful class behind VCG. Serves
Lavi/Monderer mechanism design.

## Main definitions

* `affineObjective` / `affineChoice` — the weighted-welfare objective and its maximizer
* `affineMaximizer` — the affine-maximizer mechanism with Clarke payments

## Main result

* `affineMaximizer_isDSIC` — with positive weights, the affine maximizer is DSIC
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

/-- The **affine-maximizer mechanism**: choose `affineChoice` and charge each agent
the Clarke externality payment (the negated affine welfare of the others). -/
noncomputable def affineMaximizer : SCFWithPayments ι Alt where
  Θ := Θ
  value := value
  choice := affineChoice Θ value w κ
  payment := fun θ i => -(1 / w i) *
    ((∑ j ∈ Finset.univ.erase i, w j * value j (θ j) (affineChoice Θ value w κ θ))
      + κ (affineChoice Θ value w κ θ))

/-- Scaling an agent's quasilinear utility by its (positive) weight recovers the full
affine objective evaluated at the chosen alternative, provided the others' reports
match `θ` (which holds both at the truthful profile and at a single-agent misreport). -/
theorem affineMaximizer_wUtil {i : ι} (hwi : w i ≠ 0) {report : ∀ j, Θ j}
    (θ : ∀ j, Θ j) (hrep : ∀ j, j ≠ i → report j = θ j) :
    w i * (affineMaximizer Θ value w κ).utility report i (θ i) =
      affineObjective Θ value w κ θ (affineChoice Θ value w κ report) := by
  simp only [SCFWithPayments.utility, affineMaximizer, affineObjective]
  rw [show (∑ j ∈ Finset.univ.erase i,
        w j * value j (report j) (affineChoice Θ value w κ report)) =
      ∑ j ∈ Finset.univ.erase i, w j * value j (θ j) (affineChoice Θ value w κ report) from
    Finset.sum_congr rfl fun j hj => by rw [hrep j (Finset.ne_of_mem_erase hj)]]
  rw [← Finset.add_sum_erase Finset.univ
    (fun j => w j * value j (θ j) (affineChoice Θ value w κ report)) (Finset.mem_univ i)]
  field_simp
  ring

/-- **Affine maximizers are truthful.** With positive weights, the affine-maximizer
mechanism is dominant-strategy incentive compatible. -/
theorem affineMaximizer_isDSIC (hw : ∀ i, 0 < w i) :
    (affineMaximizer Θ value w κ).IsDSIC := by
  intro i θ θ'ᵢ
  have ht := affineMaximizer_wUtil Θ value w κ (ne_of_gt (hw i)) θ (fun _ _ => rfl)
  have hm := affineMaximizer_wUtil Θ value w κ (ne_of_gt (hw i)) (report := Function.update θ i θ'ᵢ)
    θ (fun j hj => Function.update_of_ne hj _ _)
  have hmax := affineChoice_max Θ value w κ θ (affineChoice Θ value w κ (Function.update θ i θ'ᵢ))
  exact le_of_mul_le_mul_left
    (le_trans (le_of_eq hm) (le_trans hmax (le_of_eq ht.symm))) (hw i)

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
