/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.FourierMotzkin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic

/-!
# Owner-labeled flow systems and the zero-holonomy gluing condition

**Provenance.**  This is the "Layer A" routing interface for strategic
routing under a full-support mixed-context certificate: the typed incidence
and circulation notation, the two-row account obstruction, and the global
gluing invariant.  It is consumed later by the mixed-owner routing no-go,
which needs the gluing condition `ZeroHolonomy` as a *separate* hypothesis
rather than as a consequence of ownerwise Bellman provenance.

**This file is deliberately game-free.**  Everything below is finite
linear algebra over `ℝ`: no games, no strategies, no payoffs, no
probability measures, no dynamics.  Rows `R` and vertices `V` are bare
finite types, `P` is a bare row-stochastic matrix, and `ownerOf` is a bare
map into a label type.  The game-theoretic reading (rows = tagged Bellman
rows, `src` = public source configuration, `P` = lifted transition law,
`c` = row-charge cochain, `ownerOf` = owning player) belongs to the
consumers of this interface, not here.

## Main definitions

* `incidence src P x`: the incidence operator `B`,
  `(B x)(v) = ∑_{src r = v} x r - ∑_r x r * P r v`.
* `IsCirculation` / `IsNormalizedCirculation`: a nonnegative flow balanced
  at every vertex, resp. one whose total row mass is also normalized to `1`.
* `IsOwnerPure ownerOf i x`: the flow `x` is supported on owner `i`'s rows.
* `holonomy c x`: the account pairing `∑_r x r * c r`.
* `ZeroHolonomy src P c`: the gluing condition — every circulation pairs
  nonpositively with the charge cochain `c`.
* `IsAccountPotential src P c H`: the pointwise
  superharmonicity `c r + ∑_v P r v * H v - H (src r) ≤ 0`.

## Main results

* `zeroHolonomy_iff_exists_accountPotential`: the Farkas duality between the
  gluing condition and existence of an account potential.  Zero holonomy
  holds exactly when a single scalar account potential discharges every row
  charge.
* `TwoCycle.not_zeroHolonomy` together with
  `TwoCycle.ownerPure_circulation_eq_zero`: the abstract skeleton of the
  owner-switching falsifier.  On the two-row two-vertex owner-switching
  cycle every owner-pure circulation vanishes (so each owner is separately harmless)
  while the mixed uniform circulation has holonomy `(α₁ + α₂) / 2 > 0`.
  Owner-pure harmlessness therefore does **not** imply zero holonomy.
-/

open Finset BigOperators

namespace Math
namespace LinearAlgebra
namespace OwnerLabeledFlowHolonomy

noncomputable section

set_option autoImplicit false

section General

variable {R V ι : Type*} [Fintype R] [Fintype V] [DecidableEq V]

/-! ### The finite flow system -/

/-- The transition weights of a finite flow system form a row-stochastic
matrix: nonnegative entries, each row summing to `1`. -/
structure IsStochastic (P : R → V → ℝ) : Prop where
  /-- Every transition weight is nonnegative. -/
  nonneg : ∀ r v, 0 ≤ P r v
  /-- Every row is a probability vector. -/
  row_sum : ∀ r, ∑ v, P r v = 1

/-- The incidence operator `B`:
`(B x)(v) = ∑_{src r = v} x r - ∑_r x r * P r v`.  The first term collects
the mass leaving `v`, the second the mass arriving at `v`. -/
def incidence (src : R → V) (P : R → V → ℝ) (x : R → ℝ) (v : V) : ℝ :=
  (∑ r, if src r = v then x r else 0) - ∑ r, x r * P r v

/-- The `(r, v)` entry of the incidence matrix: `1` at the source vertex of
row `r`, minus the transition weight of `r` into `v`. -/
def incidenceEntry (src : R → V) (P : R → V → ℝ) (r : R) (v : V) : ℝ :=
  (if src r = v then 1 else 0) - P r v

omit [Fintype V] in
/-- `incidence` written with the fibre sum literally. -/
theorem incidence_eq_sum_filter (src : R → V) (P : R → V → ℝ) (x : R → ℝ)
    (v : V) :
    incidence src P x v
      = (∑ r ∈ Finset.univ.filter fun r => src r = v, x r)
        - ∑ r, x r * P r v := by
  rw [incidence, Finset.sum_filter]

omit [Fintype V] in
/-- `incidence` as a matrix-vector product against `incidenceEntry`. -/
theorem incidence_eq_sum_mul (src : R → V) (P : R → V → ℝ) (x : R → ℝ)
    (v : V) :
    incidence src P x v = ∑ r, x r * incidenceEntry src P r v := by
  rw [incidence, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [incidenceEntry]
  by_cases hr : src r = v
  · rw [if_pos hr, if_pos hr]; ring
  · rw [if_neg hr, if_neg hr]; ring

omit [Fintype R] in
/-- Pairing a potential against a row of the incidence matrix returns the
one-step drift of the potential along that row. -/
theorem sum_incidenceEntry_mul (src : R → V) (P : R → V → ℝ) (r : R)
    (H : V → ℝ) :
    ∑ v, incidenceEntry src P r v * H v = H (src r) - ∑ v, P r v * H v := by
  have hsplit : ∀ v : V, incidenceEntry src P r v * H v
      = (if src r = v then H v else 0) - P r v * H v := by
    intro v
    rw [incidenceEntry]
    by_cases hv : src r = v
    · rw [if_pos hv, if_pos hv]; ring
    · rw [if_neg hv, if_neg hv]; ring
  simp only [hsplit]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp

/-- A stochastic flow system conserves total mass: the image of `incidence`
lies in the sum-zero hyperplane. -/
theorem sum_incidence_eq_zero {P : R → V → ℝ} (hP : IsStochastic P)
    (src : R → V) (x : R → ℝ) : ∑ v, incidence src P x v = 0 := by
  have h1 : (∑ v, ∑ r, if src r = v then x r else 0) = ∑ r, x r := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp
  have h2 : (∑ v, ∑ r, x r * P r v) = ∑ r, x r := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.mul_sum, hP.row_sum r, mul_one]
  simp only [incidence]
  rw [Finset.sum_sub_distrib, h1, h2, sub_self]

/-! ### Circulations -/

/-- A circulation: a nonnegative flow in the kernel of the incidence
operator (without the total-mass normalization). -/
structure IsCirculation (src : R → V) (P : R → V → ℝ) (x : R → ℝ) : Prop where
  /-- Row masses are nonnegative. -/
  nonneg : ∀ r, 0 ≤ x r
  /-- Every vertex balances: `B x = 0`. -/
  balanced : ∀ v, incidence src P x v = 0

/-- A normalized circulation: a circulation with unit total mass,
`x ≥ 0`, `1ᵀx = 1`, `B x = 0`. -/
structure IsNormalizedCirculation (src : R → V) (P : R → V → ℝ)
    (x : R → ℝ) : Prop extends IsCirculation src P x where
  /-- The total row mass is one. -/
  total : ∑ r, x r = 1

/-! ### Owner labels and charges -/

/-- The flow `x` is *owner-pure* for the label `i`: it is supported inside
the rows owned by `i`. -/
def IsOwnerPure (ownerOf : R → ι) (i : ι) (x : R → ℝ) : Prop :=
  ∀ r, ownerOf r ≠ i → x r = 0

/-- The account pairing (holonomy) of a flow against a row-charge cochain,
`∑_r x r * c r`. -/
def holonomy (c : R → ℝ) (x : R → ℝ) : ℝ := ∑ r, x r * c r

/-- The gluing condition: every global oriented
circulation pairs nonpositively with the charge cochain. -/
def ZeroHolonomy (src : R → V) (P : R → V → ℝ) (c : R → ℝ) : Prop :=
  ∀ η : R → ℝ, IsCirculation src P η → holonomy c η ≤ 0

/-- A scalar *account potential* discharging the charges: the pointwise
superharmonicity inequality below.  This is the primal side of the Farkas
dual pair, `c ∈ -im B - ℝ₊`. -/
def IsAccountPotential (src : R → V) (P : R → V → ℝ) (c : R → ℝ)
    (H : V → ℝ) : Prop :=
  ∀ r, c r + (∑ v, P r v * H v) - H (src r) ≤ 0

omit [Fintype R] in
/-- Being an account potential is exactly solving the weak-inequality
system `B H ≥ c` whose matrix is `incidenceEntry`. -/
theorem isAccountPotential_iff (src : R → V) (P : R → V → ℝ) (c : R → ℝ)
    (H : V → ℝ) :
    IsAccountPotential src P c H
      ↔ ∀ r, c r ≤ ∑ v, incidenceEntry src P r v * H v := by
  constructor
  · intro h r
    have hr := h r
    rw [sum_incidenceEntry_mul]
    linarith
  · intro h r
    have hr := h r
    rw [sum_incidenceEntry_mul] at hr
    linarith

/-- The adjunction between the incidence operator and the one-step drift:
`⟨H, B x⟩ = ⟨x, drift H⟩`. -/
theorem sum_mul_incidence (src : R → V) (P : R → V → ℝ) (x : R → ℝ)
    (H : V → ℝ) :
    (∑ v, H v * incidence src P x v)
      = ∑ r, x r * (H (src r) - ∑ v, P r v * H v) := by
  calc (∑ v, H v * incidence src P x v)
      = ∑ v, ∑ r, x r * (incidenceEntry src P r v * H v) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [incidence_eq_sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
    _ = ∑ r, ∑ v, x r * (incidenceEntry src P r v * H v) := Finset.sum_comm
    _ = ∑ r, x r * (H (src r) - ∑ v, P r v * H v) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← Finset.mul_sum, sum_incidenceEntry_mul]

/-! ### The gluing/potential duality -/

/-- **Easy direction.**  An account potential forces every circulation to
have nonpositive holonomy: multiply the row inequality by the row mass,
sum, and use the balance equations. -/
theorem holonomy_nonpos_of_accountPotential {src : R → V} {P : R → V → ℝ}
    {c : R → ℝ} {H : V → ℝ} (hH : IsAccountPotential src P c H)
    {η : R → ℝ} (hη : IsCirculation src P η) : holonomy c η ≤ 0 := by
  have hbal : (∑ v, H v * incidence src P η v) = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [hη.balanced v, mul_zero]
  rw [sum_mul_incidence] at hbal
  have hterm : ∀ r ∈ (Finset.univ : Finset R),
      η r * c r ≤ η r * (H (src r) - ∑ v, P r v * H v) := by
    intro r _
    have hr := hH r
    exact mul_le_mul_of_nonneg_left (by linarith) (hη.nonneg r)
  calc holonomy c η = ∑ r, η r * c r := rfl
    _ ≤ ∑ r, η r * (H (src r) - ∑ v, P r v * H v) := Finset.sum_le_sum hterm
    _ = 0 := hbal

/-- **Easy direction, packaged.**  Existence of an account potential
implies the gluing condition. -/
theorem zeroHolonomy_of_exists_accountPotential {src : R → V}
    {P : R → V → ℝ} {c : R → ℝ}
    (h : ∃ H : V → ℝ, IsAccountPotential src P c H) :
    ZeroHolonomy src P c := by
  obtain ⟨H, hH⟩ := h
  exact fun _ hη => holonomy_nonpos_of_accountPotential hH hη

/-- **Hard direction (Farkas).**  If every circulation has nonpositive
holonomy then a single scalar account potential discharges every row
charge.  The proof is the theorem of the alternative applied to the system
`B H ≥ c`: a Farkas certificate of its infeasibility is literally a
circulation with positive holonomy. -/
theorem exists_accountPotential_of_zeroHolonomy {src : R → V}
    {P : R → V → ℝ} {c : R → ℝ} (hzero : ZeroHolonomy src P c) :
    ∃ H : V → ℝ, IsAccountPotential src P c H := by
  by_contra hcon
  set e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V with he
  set A : R → Fin (Fintype.card V) → ℝ :=
    fun r k => incidenceEntry src P r (e.symm k) with hA
  -- Rows of `A` evaluate to the drift of the transported potential.
  have hrow : ∀ (r : R) (y : Fin (Fintype.card V) → ℝ),
      rowEval A r y = ∑ v, incidenceEntry src P r v * y (e v) := by
    intro r y
    rw [rowEval,
      ← Equiv.sum_comp e.symm fun v => incidenceEntry src P r v * y (e v)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hA]
    simp
  -- Columns of `A` evaluate to the incidence operator.
  have hcol : ∀ (u : R → ℝ) (v : V),
      (∑ r, u r * A r (e v)) = incidence src P u v := by
    intro u v
    rw [incidence_eq_sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hA]
    simp
  have hinfeas : ¬ IsFeasible A c := by
    rintro ⟨y, hy⟩
    refine hcon ⟨fun v => y (e v), ?_⟩
    rw [isAccountPotential_iff]
    intro r
    have hyr := hy r
    rw [hrow r y] at hyr
    exact hyr
  obtain ⟨u, hu_nonneg, hu_zero, hu_pos⟩ :=
    (theorem_of_alternative A c).mp hinfeas
  have hcirc : IsCirculation src P u :=
    { nonneg := hu_nonneg
      balanced := fun v => by rw [← hcol u v]; exact hu_zero (e v) }
  have hle : holonomy c u ≤ 0 := hzero u hcirc
  rw [holonomy] at hle
  linarith

/-- **Main theorem (the gluing/potential duality).**  The gluing condition
holds exactly when the charge cochain is discharged by a scalar account
potential. -/
theorem zeroHolonomy_iff_exists_accountPotential (src : R → V)
    (P : R → V → ℝ) (c : R → ℝ) :
    ZeroHolonomy src P c ↔ ∃ H : V → ℝ, IsAccountPotential src P c H :=
  ⟨exists_accountPotential_of_zeroHolonomy,
    zeroHolonomy_of_exists_accountPotential⟩

omit [Fintype V] in
/-- Vacuity probe: a nonpositive charge cochain always glues (the constant
zero potential works, but the direct argument is shorter). -/
theorem zeroHolonomy_of_charge_nonpos {src : R → V} {P : R → V → ℝ}
    {c : R → ℝ} (hc : ∀ r, c r ≤ 0) : ZeroHolonomy src P c := by
  intro η hη
  rw [holonomy]
  refine Finset.sum_nonpos fun r _ => ?_
  exact mul_nonpos_of_nonneg_of_nonpos (hη.nonneg r) (hc r)

end General

/-! ### The two-row owner-switching falsifier

The abstract skeleton: two vertices `false`,
`true`; two rows, row `b` sourced at `b` and moving deterministically to
`!b`; the two rows are owned by two different owners, and carry charges
`α₁`, `α₂` with `α₁ + α₂ > 0`.

The uniform occupation `(1/2, 1/2)` is a normalized circulation with
holonomy `(α₁ + α₂) / 2 > 0`, so the gluing condition fails and (by the
main theorem) no account potential exists.  Yet
every owner-pure circulation is identically zero (every one-owner
subsystem is harmless).  Owner-pure harmlessness therefore does not imply
zero holonomy. -/

namespace TwoCycle

/-- Row `b` is sourced at vertex `b`. -/
def src : Bool → Bool := id

/-- Row `b` is owned by owner `b`; the two rows have distinct owners. -/
def ownerOf : Bool → Bool := id

/-- Row `b` moves deterministically to the other vertex `!b`. -/
def transition : Bool → Bool → ℝ := fun b v => if v = !b then 1 else 0

/-- The uniform occupation `(1/2, 1/2)`. -/
def uniform : Bool → ℝ := fun _ => 1 / 2

/-- The two row charges `α₁` (row `false`) and `α₂` (row `true`). -/
def charge (a₁ a₂ : ℝ) : Bool → ℝ := fun b => if b then a₂ else a₁

theorem isStochastic_transition : IsStochastic transition := by
  refine ⟨fun r v => ?_, fun r => ?_⟩
  · rw [transition]
    positivity
  · cases r with
    | false => norm_num [transition, Fintype.sum_bool]
    | true => norm_num [transition, Fintype.sum_bool]

/-- **(a)** The uniform occupation is a normalized circulation. -/
theorem isNormalizedCirculation_uniform :
    IsNormalizedCirculation src transition uniform := by
  refine ⟨⟨fun r => ?_, fun v => ?_⟩, ?_⟩
  · norm_num [uniform]
  · cases v with
    | false => norm_num [incidence, src, transition, uniform, Fintype.sum_bool]
    | true => norm_num [incidence, src, transition, uniform, Fintype.sum_bool]
  · norm_num [uniform, Fintype.sum_bool]

/-- The holonomy of the uniform occupation is the average charge. -/
theorem holonomy_uniform (a₁ a₂ : ℝ) :
    holonomy (charge a₁ a₂) uniform = (a₁ + a₂) / 2 := by
  rw [holonomy]
  norm_num [uniform, charge, Fintype.sum_bool]
  ring

/-- **(b)** The gluing condition fails whenever the two charges have
positive sum: the uniform circulation is the exact Farkas witness of
that failure. -/
theorem not_zeroHolonomy {a₁ a₂ : ℝ} (h : 0 < a₁ + a₂) :
    ¬ ZeroHolonomy src transition (charge a₁ a₂) := by
  intro hzero
  have hle := hzero uniform isNormalizedCirculation_uniform.toIsCirculation
  rw [holonomy_uniform] at hle
  linarith

/-- No common scalar account potential exists,
because adding the two row inequalities gives `α₁ + α₂ ≤ 0`. -/
theorem not_exists_accountPotential {a₁ a₂ : ℝ} (h : 0 < a₁ + a₂) :
    ¬ ∃ H : Bool → ℝ, IsAccountPotential src transition (charge a₁ a₂) H :=
  fun hH => not_zeroHolonomy h (zeroHolonomy_of_exists_accountPotential hH)

/-- **(c)** Every owner-pure circulation vanishes: neither owner has any
nonzero circulation on the active two-row cone. -/
theorem ownerPure_circulation_eq_zero {i : Bool} {x : Bool → ℝ}
    (hcirc : IsCirculation src transition x) (hpure : IsOwnerPure ownerOf i x) :
    x = 0 := by
  have hother : x (!i) = 0 := hpure (!i) (by cases i <;> decide)
  have hbal := hcirc.balanced (!i)
  have hself : x i = 0 := by
    cases i with
    | false =>
      norm_num [incidence, src, transition, Fintype.sum_bool] at hbal hother
      linarith
    | true =>
      norm_num [incidence, src, transition, Fintype.sum_bool] at hbal hother
      linarith
  funext r
  simp only [Pi.zero_apply]
  by_cases hr : r = i
  · rw [hr]
    exact hself
  · exact hpure r (by simpa [ownerOf] using hr)

end TwoCycle

end

end OwnerLabeledFlowHolonomy
end LinearAlgebra
end Math
