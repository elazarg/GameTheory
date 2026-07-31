/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.Farkas
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic

/-!
# Owner-typed dual lifting and the owner-custody obstruction

**Provenance.**  This is the second "Layer A" routing interface, distilled
from Question 72 (*Owner-Correct Routing of a Complete-Target
Separator*): the typed finite cell presentation of its Answer §A.1
(eq. 2-4), the typed dual cone of §A.2 (eq. 5-9), the cross-owner
incidence-cancellation counterexample of §A.5, and the custody map
`J` together with the owner-invisible target coordinates of Part E
(eq. 23, 26-27).  The game-level tagging layer -- which rows are genuine
unilateral Bellman rows of which player, in which legal public response
context, under which common behavioral realization -- is future work and
lives in the consumers of this interface, not here.

**This file is deliberately game-free.**  Everything below is finite
linear algebra over `ℝ`: no games, no strategies, no payoffs, no
probability measures, no dynamics.  `Ω` is a bare label type, `E`, `N`,
`U` are bare finite row index types, `Y` and `T` are bare finite column
index types, and the coefficient data is a bare record of functions.  The
intended reading (`Y` = internal public-history/owner-history/account
variables, `T` = the complete boundary target, `E` = public flow and
suffix-rebasing equations, `N` = owner-neutral structural inequalities,
`U` = unilateral Bellman rows tagged by their owner) belongs to the
consumers.

## Main definitions

* `TypedCell`: the affine data of one owner-context pair, Question 72
  eq. (2)-(4): `A y + R t = b`, `C y + Q t ≤ c`, and the owner-tagged
  rows `B y + S t ≤ d`.
* `MemVisible P i y t` / `MemFull P y t`: the owner-`i`-visible relaxation
  (keep (2), (3) and only owner `i`'s rows of (4)) and the full system.
* `IsTypedLift` / `HasTypedLift`: eq. (6)-(8).  Free multipliers `η` on
  (2), nonnegative `ν` on (3), nonnegative `μ` supported on owner `i`'s
  rows of (4), with the internal coefficients cancelling and the residual
  boundary load equal to `α`.
* `custody P i`: the owner-`i` custody map `J_{i,κ}` of eq. (23)/(26) --
  the boundary-target information owner `i`'s own rows can see.
* `IsVisibleRecession`: a recession direction of the owner-`i`-visible
  relaxation.

## Main results

* `validOnVisible_of_hasTypedLift`: soundness of eq. (6)-(8).  A typed
  lift is a valid inequality for the owner-`i`-visible polyhedron.  No
  feasibility hypothesis.
* `hasTypedLift_iff_validOnVisible`: the Farkas characterization.  When
  the owner-`i`-visible relaxation is nonempty, `α · t ≤ β` has an
  `i`-typed Bellman lift **iff** it is valid on that relaxation.  Typed
  liftability is exactly validity over the owner-`i`-visible polyhedron;
  it never sees the other owners' rows.
* `not_hasTypedLift_of_visibleRecession`: the custody obstruction.  A
  charged recession direction of the visible relaxation kills every typed
  lift, for every bound `β`.
* `CrossOwnerCancellation.not_hasTypedLift`: the mandatory falsifier, the
  abstract skeleton of Question 72 §A.5 and Part E.  On a two-owner
  system where owner `i`'s rows touch only target coordinate `i`, the
  inequality `t₀ + t₁ ≤ 0` is valid on the **full** system
  (`CrossOwnerCancellation.validOnFull`) but has **no** typed lift for
  **either** owner and **any** bound, because each owner's escape
  direction is invisible to that owner's custody map
  (`CrossOwnerCancellation.custody_escape`).  The cancellation of the
  internal variable is intrinsically cross-owner.
* `CrossOwnerCancellation.hasTypedLift_ownNormal`: the positive vacuity
  probe.  An inequality supported on owner `false`'s visible coordinate
  and implied by owner `false`'s relaxation does have a typed lift.
-/

open Finset BigOperators

namespace Math
namespace LinearAlgebra
namespace OwnerTypedDualLifting

noncomputable section

set_option autoImplicit false

/-! ### The coefficient pairing -/

/-- The pairing `∑ j, a j * z j` of a coefficient row `a` with a variable
vector `z`.  All rows of Question 72 eq. (2)-(4) are evaluated with it. -/
def dot {J : Type*} [Fintype J] (a z : J → ℝ) : ℝ := ∑ j, a j * z j

variable {J : Type*} [Fintype J]

/-- Pairing against an affinely shifted vector. -/
theorem dot_shift (a y y₀ : J → ℝ) (s : ℝ) :
    dot a (fun j => y j + s * y₀ j) = dot a y + s * dot a y₀ := by
  simp only [dot, mul_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Transposition: a multiplier-weighted sum of rows is the column-weighted
sum of the variables. -/
theorem sum_mul_dot {I : Type*} [Fintype I] (m : I → ℝ) (M : I → J → ℝ)
    (z : J → ℝ) : (∑ i, m i * dot (M i) z) = ∑ j, (∑ i, m i * M i j) * z j := by
  simp only [dot, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => by ring

private theorem sum_neg_mul (f z : J → ℝ) : (∑ j, -f j * z j) = -dot f z := by
  rw [dot, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem sum_neg_smul_mul (s : ℝ) (f z : J → ℝ) :
    (∑ j, -(s * f j) * z j) = -(s * dot f z) := by
  rw [dot, Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem sum_mul_neg (u f : J → ℝ) : (∑ j, u j * -f j) = -∑ j, u j * f j := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem sum_mul_neg_smul (u m f : J → ℝ) :
    (∑ j, u j * -(m j * f j)) = -∑ j, u j * m j * f j := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem sum_sub_mul (u u' f : J → ℝ) :
    (∑ j, (u j - u' j) * f j) = (∑ j, u j * f j) - ∑ j, u' j * f j := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

section General

variable {Ω E N U Y T : Type*}

/-! ### The typed finite cell presentation (Question 72, §A.1) -/

/-- The affine data of one owner-context pair `p = (i, κ)`, Question 72
eq. (2)-(4).  The internal variables are indexed by `Y`, the complete
boundary target by `T`.

* `E` indexes the structural equations `A y + R t = b` of eq. (2): public
  flow, owner-history incidence, suffix rebasing, account conservation.
* `N` indexes the owner-neutral inequalities `C y + Q t ≤ c` of eq. (3).
* `U` indexes the unilateral rows `B y + S t ≤ d` of eq. (4), each tagged
  by its owner via `ownerOf`.  Discipline: no unilateral row of any owner
  may be hidden in the `N` block.

Everything is a bare function; the polynomial dependence of the matrices
on the common realization parameters is suppressed, exactly as in the
source. -/
structure TypedCell (Ω E N U Y T : Type*) where
  /-- The owner label carried by each unilateral row. -/
  ownerOf : U → Ω
  /-- Internal coefficients of the structural equations (2). -/
  A : E → Y → ℝ
  /-- Boundary-target coefficients of the structural equations (2). -/
  R : E → T → ℝ
  /-- Right-hand side of the structural equations (2). -/
  b : E → ℝ
  /-- Internal coefficients of the owner-neutral inequalities (3). -/
  C : N → Y → ℝ
  /-- Boundary-target coefficients of the owner-neutral inequalities (3). -/
  Q : N → T → ℝ
  /-- Right-hand side of the owner-neutral inequalities (3). -/
  c : N → ℝ
  /-- Internal coefficients of the unilateral rows (4). -/
  B : U → Y → ℝ
  /-- Boundary-target coefficients of the unilateral rows (4). -/
  S : U → T → ℝ
  /-- Right-hand side of the unilateral rows (4). -/
  d : U → ℝ

variable [Fintype Y] [Fintype T]

/-- Question 72, eq. (2): the structural equations hold at `(y, t)`. -/
def SatEq (P : TypedCell Ω E N U Y T) (y : Y → ℝ) (t : T → ℝ) : Prop :=
  ∀ e, dot (P.A e) y + dot (P.R e) t = P.b e

/-- Question 72, eq. (3): the owner-neutral inequalities hold at `(y, t)`. -/
def SatNeutral (P : TypedCell Ω E N U Y T) (y : Y → ℝ) (t : T → ℝ) : Prop :=
  ∀ n, dot (P.C n) y + dot (P.Q n) t ≤ P.c n

/-- Question 72, eq. (4) restricted to the rows owned by `i`. -/
def SatOwner (P : TypedCell Ω E N U Y T) (i : Ω) (y : Y → ℝ) (t : T → ℝ) : Prop :=
  ∀ u, P.ownerOf u = i → dot (P.B u) y + dot (P.S u) t ≤ P.d u

/-- Question 72, eq. (4) for every owner at once. -/
def SatAll (P : TypedCell Ω E N U Y T) (y : Y → ℝ) (t : T → ℝ) : Prop :=
  ∀ u, dot (P.B u) y + dot (P.S u) t ≤ P.d u

/-- The **owner-`i`-visible relaxation**: the structural equations, the
owner-neutral inequalities, and only owner `i`'s unilateral rows.  Every
other owner's rows are dropped. -/
structure MemVisible (P : TypedCell Ω E N U Y T) (i : Ω) (y : Y → ℝ)
    (t : T → ℝ) : Prop where
  /-- The structural equations (2). -/
  structural : SatEq P y t
  /-- The owner-neutral inequalities (3). -/
  neutral : SatNeutral P y t
  /-- Owner `i`'s unilateral rows of (4). -/
  unilateral : SatOwner P i y t

/-- The full system: (2), (3) and *all* unilateral rows of (4). -/
structure MemFull (P : TypedCell Ω E N U Y T) (y : Y → ℝ) (t : T → ℝ) : Prop where
  /-- The structural equations (2). -/
  structural : SatEq P y t
  /-- The owner-neutral inequalities (3). -/
  neutral : SatNeutral P y t
  /-- Every owner's unilateral rows of (4). -/
  unilateral : SatAll P y t

/-- The full system is contained in every owner's relaxation. -/
theorem memVisible_of_memFull {P : TypedCell Ω E N U Y T} {y : Y → ℝ}
    {t : T → ℝ} (h : MemFull P y t) (i : Ω) : MemVisible P i y t :=
  ⟨h.structural, h.neutral, fun u _ => h.unilateral u⟩

/-- `α · t ≤ β` is valid on the owner-`i`-visible relaxation. -/
def ValidOnVisible (P : TypedCell Ω E N U Y T) (i : Ω) (α : T → ℝ) (β : ℝ) : Prop :=
  ∀ y t, MemVisible P i y t → dot α t ≤ β

/-- `α · t ≤ β` is valid on the full system. -/
def ValidOnFull (P : TypedCell Ω E N U Y T) (α : T → ℝ) (β : ℝ) : Prop :=
  ∀ y t, MemFull P y t → dot α t ≤ β

/-- Validity on any single owner's relaxation is stronger than validity on
the full system. -/
theorem validOnFull_of_validOnVisible {P : TypedCell Ω E N U Y T} {i : Ω}
    {α : T → ℝ} {β : ℝ} (h : ValidOnVisible P i α β) : ValidOnFull P α β :=
  fun y t hmem => h y t (memVisible_of_memFull hmem i)

/-! ### The typed dual cone (Question 72, §A.2) -/

variable [Fintype E] [Fintype N] [Fintype U]

/-- Question 72, eq. (6)-(8).  `(η, ν, μ)` is an `i`-typed Bellman lift of
the inequality `α · t ≤ β`:

* `ν ≥ 0` on the owner-neutral rows (3) and `μ ≥ 0` on the unilateral rows
  (4), with `μ` supported on owner `i`'s rows only; `η` is free on the
  equations (2);
* eq. (6), `Aᵀη + Cᵀν + Bᵢᵀμ = 0`: the internal coefficients cancel;
* eq. (7), `Rᵀη + Qᵀν + Sᵢᵀμ = α`: the residual boundary load is exactly
  `α`;
* eq. (8), `bᵀη + cᵀν + dᵢᵀμ ≤ β`.

The support condition on `μ` is what makes the certificate *typed*: only
owner `i`'s genuine unilateral rows may carry strategic weight. -/
structure IsTypedLift (P : TypedCell Ω E N U Y T) (i : Ω) (α : T → ℝ) (β : ℝ)
    (η : E → ℝ) (ν : N → ℝ) (μ : U → ℝ) : Prop where
  /-- The multipliers on the owner-neutral inequalities are nonnegative. -/
  neutral_nonneg : ∀ n, 0 ≤ ν n
  /-- The multipliers on the unilateral rows are nonnegative. -/
  owner_nonneg : ∀ u, 0 ≤ μ u
  /-- Only owner `i`'s unilateral rows may carry weight. -/
  owner_pure : ∀ u, P.ownerOf u ≠ i → μ u = 0
  /-- Eq. (6): the incidence-cancellation requirement. -/
  internal_cancel : ∀ v : Y,
    (∑ e, η e * P.A e v) + (∑ n, ν n * P.C n v) + (∑ u, μ u * P.B u v) = 0
  /-- Eq. (7): the residual boundary load is exactly `α`. -/
  boundary_load : ∀ w : T,
    (∑ e, η e * P.R e w) + (∑ n, ν n * P.Q n w) + (∑ u, μ u * P.S u w) = α w
  /-- Eq. (8): the constant term is dominated by `β`. -/
  rhs_bound :
    (∑ e, η e * P.b e) + (∑ n, ν n * P.c n) + (∑ u, μ u * P.d u) ≤ β

/-- Question 72, eq. (9): the inequality `α · t ≤ β` admits an `i`-typed
Bellman lift. -/
def HasTypedLift (P : TypedCell Ω E N U Y T) (i : Ω) (α : T → ℝ) (β : ℝ) : Prop :=
  ∃ (η : E → ℝ) (ν : N → ℝ) (μ : U → ℝ), IsTypedLift P i α β η ν μ

/-! ### Soundness of a typed lift -/

/-- The weighted-sum computation of Question 72, §A.2: summing the rows
against `(η, ν, μ)` and using eq. (6)-(7) gives
`α · t ≤ bᵀη + cᵀν + dᵢᵀμ` at every point of the owner-`i`-visible
relaxation.  No feasibility hypothesis is needed. -/
theorem dot_le_rhs_of_isTypedLift {P : TypedCell Ω E N U Y T} {i : Ω}
    {α : T → ℝ} {β : ℝ} {η : E → ℝ} {ν : N → ℝ} {μ : U → ℝ}
    (hlift : IsTypedLift P i α β η ν μ) {y : Y → ℝ} {t : T → ℝ}
    (hmem : MemVisible P i y t) :
    dot α t ≤ (∑ e, η e * P.b e) + (∑ n, ν n * P.c n) + (∑ u, μ u * P.d u) := by
  have hEy : (∑ e, η e * dot (P.A e) y) = ∑ v, (∑ e, η e * P.A e v) * y v :=
    sum_mul_dot _ _ _
  have hEt : (∑ e, η e * dot (P.R e) t) = ∑ w, (∑ e, η e * P.R e w) * t w :=
    sum_mul_dot _ _ _
  have hNy : (∑ n, ν n * dot (P.C n) y) = ∑ v, (∑ n, ν n * P.C n v) * y v :=
    sum_mul_dot _ _ _
  have hNt : (∑ n, ν n * dot (P.Q n) t) = ∑ w, (∑ n, ν n * P.Q n w) * t w :=
    sum_mul_dot _ _ _
  have hUy : (∑ u, μ u * dot (P.B u) y) = ∑ v, (∑ u, μ u * P.B u v) * y v :=
    sum_mul_dot _ _ _
  have hUt : (∑ u, μ u * dot (P.S u) t) = ∑ w, (∑ u, μ u * P.S u w) * t w :=
    sum_mul_dot _ _ _
  -- The three row blocks, weighted.
  have hE : (∑ e, η e * dot (P.A e) y) + (∑ e, η e * dot (P.R e) t)
      = ∑ e, η e * P.b e := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← mul_add, hmem.structural e]
  have hN : (∑ n, ν n * dot (P.C n) y) + (∑ n, ν n * dot (P.Q n) t)
      ≤ ∑ n, ν n * P.c n := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hmem.neutral n) (hlift.neutral_nonneg n)
  have hU : (∑ u, μ u * dot (P.B u) y) + (∑ u, μ u * dot (P.S u) t)
      ≤ ∑ u, μ u * P.d u := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [← mul_add]
    by_cases hu : P.ownerOf u = i
    · exact mul_le_mul_of_nonneg_left (hmem.unilateral u hu) (hlift.owner_nonneg u)
    · rw [hlift.owner_pure u hu, zero_mul, zero_mul]
  -- Eq. (6): the internal coefficients cancel.
  have hYzero : (∑ v, (∑ e, η e * P.A e v) * y v)
      + (∑ v, (∑ n, ν n * P.C n v) * y v)
      + (∑ v, (∑ u, μ u * P.B u v) * y v) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [← add_mul, ← add_mul, hlift.internal_cancel v, zero_mul]
  -- Eq. (7): the residual boundary load is `α`.
  have hTalpha : (∑ w, (∑ e, η e * P.R e w) * t w)
      + (∑ w, (∑ n, ν n * P.Q n w) * t w)
      + (∑ w, (∑ u, μ u * P.S u w) * t w) = dot α t := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp only [dot]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← add_mul, ← add_mul, hlift.boundary_load w]
  rw [hEy, hEt] at hE
  rw [hNy, hNt] at hN
  rw [hUy, hUt] at hU
  linarith

/-- **Soundness of eq. (6)-(8).**  An `i`-typed Bellman lift certifies the
inequality on the owner-`i`-visible relaxation. -/
theorem validOnVisible_of_hasTypedLift {P : TypedCell Ω E N U Y T} {i : Ω}
    {α : T → ℝ} {β : ℝ} (h : HasTypedLift P i α β) : ValidOnVisible P i α β := by
  obtain ⟨η, ν, μ, hlift⟩ := h
  exact fun y t hmem =>
    le_trans (dot_le_rhs_of_isTypedLift hlift hmem) hlift.rhs_bound

/-- A typed lift is in particular a valid inequality for the full system. -/
theorem validOnFull_of_hasTypedLift {P : TypedCell Ω E N U Y T} {i : Ω}
    {α : T → ℝ} {β : ℝ} (h : HasTypedLift P i α β) : ValidOnFull P α β :=
  validOnFull_of_validOnVisible (validOnVisible_of_hasTypedLift h)

/-! ### The Farkas characterization -/

section Farkas

variable [DecidableEq Ω]

/-- The indicator of the rows owned by `i`. -/
def ownerMask (P : TypedCell Ω E N U Y T) (i : Ω) (u : U) : ℝ :=
  if P.ownerOf u = i then 1 else 0

omit [Fintype Y] [Fintype T] [Fintype E] [Fintype N] [Fintype U] in
theorem ownerMask_nonneg (P : TypedCell Ω E N U Y T) (i : Ω) (u : U) :
    0 ≤ ownerMask P i u := by
  rw [ownerMask]; split_ifs <;> norm_num

omit [Fintype Y] [Fintype T] [Fintype E] [Fintype N] [Fintype U] in
theorem ownerMask_of_eq (P : TypedCell Ω E N U Y T) (i : Ω) {u : U}
    (h : P.ownerOf u = i) : ownerMask P i u = 1 := if_pos h

omit [Fintype Y] [Fintype T] [Fintype E] [Fintype N] [Fintype U] in
theorem ownerMask_of_ne (P : TypedCell Ω E N U Y T) (i : Ω) {u : U}
    (h : P.ownerOf u ≠ i) : ownerMask P i u = 0 := if_neg h

/-- Row index of the owner-`i`-visible relaxation, written as a weak
inequality system: the two orientations of each structural equation, the
owner-neutral inequalities, and the unilateral rows (the rows of the other
owners are masked to the trivial row `0 ≥ 0`). -/
abbrev VisibleRow (E N U : Type*) : Type _ := E ⊕ E ⊕ N ⊕ U

/-- Column index of the relaxation: internal variables, then boundary
target coordinates. -/
abbrev VisibleCol (Y T : Type*) : Type _ := Y ⊕ T

/-- The coefficient matrix of the owner-`i`-visible relaxation, in the
`≥` normal form consumed by `Math.LinearAlgebra.farkas_lemma_fintype`. -/
def visibleMatrix (P : TypedCell Ω E N U Y T) (i : Ω) :
    VisibleRow E N U → VisibleCol Y T → ℝ
  | Sum.inl e, Sum.inl v => P.A e v
  | Sum.inl e, Sum.inr w => P.R e w
  | Sum.inr (Sum.inl e), Sum.inl v => -P.A e v
  | Sum.inr (Sum.inl e), Sum.inr w => -P.R e w
  | Sum.inr (Sum.inr (Sum.inl n)), Sum.inl v => -P.C n v
  | Sum.inr (Sum.inr (Sum.inl n)), Sum.inr w => -P.Q n w
  | Sum.inr (Sum.inr (Sum.inr u)), Sum.inl v => -(ownerMask P i u * P.B u v)
  | Sum.inr (Sum.inr (Sum.inr u)), Sum.inr w => -(ownerMask P i u * P.S u w)

/-- The right-hand side paired with `visibleMatrix`. -/
def visibleRhs (P : TypedCell Ω E N U Y T) (i : Ω) : VisibleRow E N U → ℝ
  | Sum.inl e => P.b e
  | Sum.inr (Sum.inl e) => -P.b e
  | Sum.inr (Sum.inr (Sum.inl n)) => -P.c n
  | Sum.inr (Sum.inr (Sum.inr u)) => -(ownerMask P i u * P.d u)

/-- The linear objective encoding `α · t ≤ β` as the lower bound
`-β ≤ (-α) · t`. -/
def targetObjective (α : T → ℝ) : VisibleCol Y T → ℝ
  | Sum.inl _ => 0
  | Sum.inr w => -α w

theorem sum_targetObjective (α : T → ℝ) (y : Y → ℝ) (t : T → ℝ) :
    (∑ j, targetObjective (Y := Y) α j * Sum.elim y t j) = -dot α t := by
  rw [Fintype.sum_sum_type]
  simp only [targetObjective, Sum.elim_inl, Sum.elim_inr, zero_mul,
    Finset.sum_const_zero, zero_add]
  exact sum_neg_mul _ _

omit [Fintype Y] [Fintype T] [Fintype E] [Fintype N] [Fintype U] in
theorem sum_elim_self (x : VisibleCol Y T → ℝ) :
    Sum.elim (fun v => x (Sum.inl v)) (fun w => x (Sum.inr w)) = x := by
  funext j; cases j <;> rfl

omit [Fintype E] [Fintype N] [Fintype U] in
/-- Feasibility of the encoded weak-inequality system is exactly membership
in the owner-`i`-visible relaxation. -/
theorem visibleFeasible_iff (P : TypedCell Ω E N U Y T) (i : Ω) (y : Y → ℝ)
    (t : T → ℝ) :
    (∀ r, visibleRhs P i r ≤ ∑ j, visibleMatrix P i r j * Sum.elim y t j)
      ↔ MemVisible P i y t := by
  have hrow : ∀ r : VisibleRow E N U,
      (∑ j, visibleMatrix P i r j * Sum.elim y t j)
        = match r with
          | Sum.inl e => dot (P.A e) y + dot (P.R e) t
          | Sum.inr (Sum.inl e) => -(dot (P.A e) y + dot (P.R e) t)
          | Sum.inr (Sum.inr (Sum.inl n)) => -(dot (P.C n) y + dot (P.Q n) t)
          | Sum.inr (Sum.inr (Sum.inr u)) =>
              -(ownerMask P i u * (dot (P.B u) y + dot (P.S u) t)) := by
    intro r
    rw [Fintype.sum_sum_type]
    match r with
    | Sum.inl e =>
      simp only [visibleMatrix, Sum.elim_inl, Sum.elim_inr, dot]
    | Sum.inr (Sum.inl e) =>
      simp only [visibleMatrix, Sum.elim_inl, Sum.elim_inr]
      rw [sum_neg_mul, sum_neg_mul]; ring
    | Sum.inr (Sum.inr (Sum.inl n)) =>
      simp only [visibleMatrix, Sum.elim_inl, Sum.elim_inr]
      rw [sum_neg_mul, sum_neg_mul]; ring
    | Sum.inr (Sum.inr (Sum.inr u)) =>
      simp only [visibleMatrix, Sum.elim_inl, Sum.elim_inr]
      rw [sum_neg_smul_mul, sum_neg_smul_mul]; ring
  constructor
  · intro hx
    refine ⟨fun e => ?_, fun n => ?_, fun u hu => ?_⟩
    · have h1 := hx (Sum.inl e)
      have h2 := hx (Sum.inr (Sum.inl e))
      rw [hrow] at h1 h2
      simp only [visibleRhs] at h1 h2
      linarith
    · have h := hx (Sum.inr (Sum.inr (Sum.inl n)))
      rw [hrow] at h
      simp only [visibleRhs] at h
      linarith
    · have h := hx (Sum.inr (Sum.inr (Sum.inr u)))
      rw [hrow] at h
      simp only [visibleRhs] at h
      rw [ownerMask_of_eq P i hu] at h
      linarith
  · intro hmem r
    rw [hrow]
    match r with
    | Sum.inl e =>
      simp only [visibleRhs]
      exact le_of_eq (hmem.structural e).symm
    | Sum.inr (Sum.inl e) =>
      simp only [visibleRhs]
      rw [hmem.structural e]
    | Sum.inr (Sum.inr (Sum.inl n)) =>
      simp only [visibleRhs]
      have := hmem.neutral n
      linarith
    | Sum.inr (Sum.inr (Sum.inr u)) =>
      simp only [visibleRhs]
      by_cases hu : P.ownerOf u = i
      · rw [ownerMask_of_eq P i hu, one_mul, one_mul]
        have := hmem.unilateral u hu
        linarith
      · rw [ownerMask_of_ne P i hu, zero_mul, zero_mul]

omit [DecidableEq Ω] in
/-- **The Farkas characterization (Question 72, eq. (6)-(9)).**  When the
owner-`i`-visible relaxation is nonempty, `α · t ≤ β` has an `i`-typed
Bellman lift exactly when it is valid on that relaxation.  Typed
liftability is therefore *nothing but* validity over the owner-`i`-visible
polyhedron: the certificate can never use another owner's rows, so it can
never see the target coordinates only those rows constrain. -/
theorem hasTypedLift_iff_validOnVisible (P : TypedCell Ω E N U Y T) (i : Ω)
    (α : T → ℝ) (β : ℝ) (hfeas : ∃ y t, MemVisible P i y t) :
    HasTypedLift P i α β ↔ ValidOnVisible P i α β := by
  classical
  refine ⟨validOnVisible_of_hasTypedLift, fun hvalid => ?_⟩
  obtain ⟨y₀, t₀, hy₀⟩ := hfeas
  have hfeas' : ∃ x : VisibleCol Y T → ℝ,
      ∀ r, visibleRhs P i r ≤ ∑ j, visibleMatrix P i r j * x j :=
    ⟨Sum.elim y₀ t₀, (visibleFeasible_iff P i y₀ t₀).mpr hy₀⟩
  have hbound : ∀ x : VisibleCol Y T → ℝ,
      (∀ r, visibleRhs P i r ≤ ∑ j, visibleMatrix P i r j * x j) →
      -β ≤ ∑ j, targetObjective (Y := Y) α j * x j := by
    intro x hx
    have hxe := sum_elim_self x
    have hmem : MemVisible P i (fun v => x (Sum.inl v)) (fun w => x (Sum.inr w)) :=
      (visibleFeasible_iff P i _ _).mp (by rw [hxe]; exact hx)
    have hv := hvalid _ _ hmem
    have hobj := sum_targetObjective (Y := Y) α (fun v => x (Sum.inl v))
      (fun w => x (Sum.inr w))
    rw [hxe] at hobj
    rw [hobj]
    linarith
  obtain ⟨u, hu_nonneg, hu_col, hu_rhs⟩ :=
    (farkas_lemma_fintype (visibleMatrix P i) (visibleRhs P i)
      (targetObjective (Y := Y) α) (-β) hfeas').mp hbound
  refine ⟨fun e => u (Sum.inr (Sum.inl e)) - u (Sum.inl e),
    fun n => u (Sum.inr (Sum.inr (Sum.inl n))),
    fun r => u (Sum.inr (Sum.inr (Sum.inr r))) * ownerMask P i r, ?_⟩
  refine ⟨fun n => hu_nonneg _, fun r => mul_nonneg (hu_nonneg _)
    (ownerMask_nonneg P i r), fun r hr => ?_, fun v => ?_, fun w => ?_, ?_⟩
  · rw [ownerMask_of_ne P i hr, mul_zero]
  · have h := hu_col (Sum.inl v)
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at h
    simp only [visibleMatrix, targetObjective] at h
    rw [sum_mul_neg, sum_mul_neg, sum_mul_neg_smul] at h
    rw [sum_sub_mul]
    linarith
  · have h := hu_col (Sum.inr w)
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at h
    simp only [visibleMatrix, targetObjective] at h
    rw [sum_mul_neg, sum_mul_neg, sum_mul_neg_smul] at h
    rw [sum_sub_mul]
    linarith
  · rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hu_rhs
    simp only [visibleRhs] at hu_rhs
    rw [sum_mul_neg, sum_mul_neg, sum_mul_neg_smul] at hu_rhs
    rw [sum_sub_mul]
    linarith

omit [DecidableEq Ω] in
/-- The Farkas characterization under the more familiar hypothesis that the
*full* system is feasible; the relaxation is then feasible a fortiori. -/
theorem hasTypedLift_iff_validOnVisible_of_full (P : TypedCell Ω E N U Y T)
    (i : Ω) (α : T → ℝ) (β : ℝ) (hfeas : ∃ y t, MemFull P y t) :
    HasTypedLift P i α β ↔ ValidOnVisible P i α β := by
  obtain ⟨y, t, ht⟩ := hfeas
  exact hasTypedLift_iff_validOnVisible P i α β
    ⟨y, t, memVisible_of_memFull ht i⟩

/-! ### The custody map and the owner-invisible obstruction -/

/-- Question 72, eq. (23)/(26): the owner-`i` **custody map** `J_{i,κ}`.
It records exactly the boundary-target information that owner `i`'s own
unilateral rows can see, namely the load `Sᵢ t` those rows place on the
target; every other owner's row returns `0`.  A target discrepancy in the
kernel of `J_{i,κ}` is *owner-`i`-invisible*: no `i`-typed certificate can
charge it, so it needs a different custodian (terminal, account, child, or
analytic route). -/
def custody (P : TypedCell Ω E N U Y T) (i : Ω) (t : T → ℝ) : U → ℝ :=
  fun u => ownerMask P i u * dot (P.S u) t

omit [Fintype Y] [Fintype E] [Fintype N] [Fintype U] in
/-- On owner `i`'s own rows the custody map is the plain row load. -/
theorem custody_apply_of_eq (P : TypedCell Ω E N U Y T) {i : Ω} {u : U}
    (h : P.ownerOf u = i) (t : T → ℝ) : custody P i t u = dot (P.S u) t := by
  rw [custody, ownerMask_of_eq P i h, one_mul]

omit [Fintype Y] [Fintype E] [Fintype N] [Fintype U] in
/-- An owner-`i`-invisible target direction puts no load on any of owner
`i`'s own rows. -/
theorem dot_S_eq_zero_of_custody_eq_zero {P : TypedCell Ω E N U Y T} {i : Ω}
    {t₀ : T → ℝ} (h : custody P i t₀ = 0) {u : U} (hu : P.ownerOf u = i) :
    dot (P.S u) t₀ = 0 := by
  have := congrFun h u
  rwa [custody_apply_of_eq P hu, Pi.zero_apply] at this

end Farkas

/-- A recession direction of the owner-`i`-visible relaxation: it satisfies
the homogeneous form of (2), (3) and owner `i`'s rows of (4). -/
structure IsVisibleRecession (P : TypedCell Ω E N U Y T) (i : Ω) (y₀ : Y → ℝ)
    (t₀ : T → ℝ) : Prop where
  /-- Homogeneous form of the structural equations (2). -/
  structural : ∀ e, dot (P.A e) y₀ + dot (P.R e) t₀ = 0
  /-- Homogeneous form of the owner-neutral inequalities (3). -/
  neutral : ∀ n, dot (P.C n) y₀ + dot (P.Q n) t₀ ≤ 0
  /-- Homogeneous form of owner `i`'s unilateral rows (4). -/
  unilateral : ∀ u, P.ownerOf u = i → dot (P.B u) y₀ + dot (P.S u) t₀ ≤ 0

omit [Fintype E] [Fintype N] [Fintype U] in
/-- Owner `i`'s block of the recession condition only constrains the
*internal* direction as soon as the target direction is owner-`i`-invisible:
this is exactly the custody failure of Question 72, Part E. -/
theorem recession_unilateral_of_custody_eq_zero [DecidableEq Ω]
    {P : TypedCell Ω E N U Y T} {i : Ω} {y₀ : Y → ℝ} {t₀ : T → ℝ}
    (hinv : custody P i t₀ = 0)
    (hy : ∀ u, P.ownerOf u = i → dot (P.B u) y₀ ≤ 0) :
    ∀ u, P.ownerOf u = i → dot (P.B u) y₀ + dot (P.S u) t₀ ≤ 0 := by
  intro u hu
  rw [dot_S_eq_zero_of_custody_eq_zero hinv hu, add_zero]
  exact hy u hu

omit [Fintype E] [Fintype N] [Fintype U] in
/-- The owner-`i`-visible relaxation is closed under adding a nonnegative
multiple of one of its recession directions. -/
theorem memVisible_shift {P : TypedCell Ω E N U Y T} {i : Ω} {y : Y → ℝ}
    {t : T → ℝ} (hmem : MemVisible P i y t) {y₀ : Y → ℝ} {t₀ : T → ℝ}
    (hrec : IsVisibleRecession P i y₀ t₀) {s : ℝ} (hs : 0 ≤ s) :
    MemVisible P i (fun v => y v + s * y₀ v) (fun w => t w + s * t₀ w) := by
  refine ⟨fun e => ?_, fun n => ?_, fun u hu => ?_⟩
  · rw [dot_shift, dot_shift]
    have h1 := hmem.structural e
    have h2 := hrec.structural e
    nlinarith [h1, h2]
  · rw [dot_shift, dot_shift]
    have h1 := hmem.neutral n
    have h2 := hrec.neutral n
    nlinarith [mul_nonneg hs (neg_nonneg.mpr h2)]
  · rw [dot_shift, dot_shift]
    have h1 := hmem.unilateral u hu
    have h2 := hrec.unilateral u hu
    nlinarith [mul_nonneg hs (neg_nonneg.mpr h2)]

/-- **The custody obstruction.**  If the owner-`i`-visible relaxation is
nonempty and has a recession direction that `α` charges positively, then
`α · t ≤ β` has no `i`-typed Bellman lift, *for any* bound `β`.  In the
falsifier below the charged direction is exactly a target direction the
owner-`i` custody map cannot see. -/
theorem not_hasTypedLift_of_visibleRecession {P : TypedCell Ω E N U Y T}
    {i : Ω} {α : T → ℝ} {y : Y → ℝ} {t : T → ℝ} (hmem : MemVisible P i y t)
    {y₀ : Y → ℝ} {t₀ : T → ℝ} (hrec : IsVisibleRecession P i y₀ t₀)
    (hcharge : 0 < dot α t₀) (β : ℝ) : ¬ HasTypedLift P i α β := by
  intro hlift
  have hvalid := validOnVisible_of_hasTypedLift hlift
  set s : ℝ := (|β - dot α t| + 1) / dot α t₀ with hs_def
  have hs_nonneg : 0 ≤ s := by
    rw [hs_def]
    positivity
  have hs_mul : s * dot α t₀ = |β - dot α t| + 1 := by
    rw [hs_def, div_mul_cancel₀ _ (ne_of_gt hcharge)]
  have hshift := hvalid _ _ (memVisible_shift hmem hrec hs_nonneg)
  rw [dot_shift, hs_mul] at hshift
  have habs : β - dot α t ≤ |β - dot α t| := le_abs_self _
  linarith

end General

/-! ### The cross-owner cancellation falsifier

The abstract skeleton of Question 72, §A.5 (*cross-owner incidence
cancellation*) and Part E (*owner-invisible target coordinates*).

Two owners `false`, `true`; one internal variable `y`; two boundary target
coordinates `t false`, `t true`; one owner-neutral row `y ≤ 0`; and two
unilateral rows

  `t false - y ≤ 0`  owned by `false`,
  `t true  + y ≤ 0`  owned by `true`.

Adding the two unilateral rows cancels `y` and gives the valid inequality

  `t false + t true ≤ 0`,

but that cancellation is intrinsically cross-owner.  Owner `i`'s rows
constrain only the target coordinate `i`; the other coordinate is
invisible to owner `i`'s custody map and escapes to `+∞` inside owner
`i`'s relaxation.  Hence *neither* owner has a typed lift, for *any*
bound.  This is exactly Question 72's missing invariant: coordinate
`!i` has no custodian in owner `i`'s Bellman system. -/

namespace CrossOwnerCancellation

/-- The cross-owner normal `α = (1, 1)` of Question 72, §A.5. -/
def crossNormal : Bool → ℝ := fun _ => 1

/-- The indicator of owner `i`'s own visible target coordinate. -/
def ownNormal (i : Bool) : Bool → ℝ := fun w => if w = i then 1 else 0

/-- The owner-`i`-invisible escape direction: the indicator of the *other*
target coordinate, the one owner `i`'s rows never mention. -/
def escape (i : Bool) : Bool → ℝ := fun w => if w = i then 0 else 1

/-- The two-owner system.  `Ω = Bool` (owners), `E = Empty` (no structural
equations), `N = Unit` (the single owner-neutral row `y ≤ 0`), `U = Bool`
(one unilateral row per owner), `Y = Unit` (one internal variable),
`T = Bool` (two boundary target coordinates). -/
def system : TypedCell Bool Empty Unit Bool Unit Bool where
  ownerOf := id
  A := fun e => e.elim
  R := fun e => e.elim
  b := fun e => e.elim
  C := fun _ _ => 1
  Q := fun _ _ => 0
  c := fun _ => 0
  B := fun u _ => if u then 1 else -1
  S := ownNormal
  d := fun _ => 0

theorem dot_ownNormal (i : Bool) (t : Bool → ℝ) : dot (ownNormal i) t = t i := by
  simp [dot, ownNormal, Finset.sum_ite_eq']

theorem dot_crossNormal (t : Bool → ℝ) :
    dot crossNormal t = t true + t false := by
  simp [dot, crossNormal]

theorem dot_crossNormal_escape (i : Bool) : dot crossNormal (escape i) = 1 := by
  cases i <;> simp [dot_crossNormal, escape]

theorem dot_S (u : Bool) (t : Bool → ℝ) : dot (system.S u) t = t u :=
  dot_ownNormal u t

theorem dot_B (u : Bool) (y : Unit → ℝ) :
    dot (system.B u) y = (if u then 1 else -1) * y () := by
  simp [dot, system]

theorem dot_C (y : Unit → ℝ) : dot (system.C ()) y = y () := by
  simp [dot, system]

theorem dot_Q (t : Bool → ℝ) : dot (system.Q ()) t = 0 := by
  simp [dot, system]

/-! #### Validity over the full system -/

/-- Question 72, §A.5: adding the two unilateral rows cancels the internal
variable and yields `t false + t true ≤ 0` on the full system. -/
theorem validOnFull : ValidOnFull system crossNormal 0 := by
  intro y t hmem
  have h0 := hmem.unilateral false
  have h1 := hmem.unilateral true
  rw [dot_B, dot_S] at h0 h1
  simp only [system] at h0 h1
  rw [dot_crossNormal]
  norm_num at h0 h1
  linarith

/-- The origin is feasible for the full system, so the falsifier is not
vacuous. -/
theorem memFull_zero : MemFull system (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun e => e.elim, fun n => ?_, fun u => ?_⟩
  · rw [show n = () from rfl, dot_C, dot_Q]
    norm_num [system]
  · rw [dot_B, dot_S]
    norm_num [system]

theorem memVisible_zero (i : Bool) :
    MemVisible system i (fun _ => 0) (fun _ => 0) :=
  memVisible_of_memFull memFull_zero i

/-! #### The escape direction is owner-invisible -/

/-- Question 72, Part E: the escape direction lies in the kernel of the
owner-`i` custody map.  Owner `i` literally cannot see it. -/
theorem custody_escape (i : Bool) : custody system i (escape i) = 0 := by
  funext u
  rw [custody, dot_S]
  simp [escape, ownerMask, system]

/-- The escape direction is a recession direction of owner `i`'s
relaxation, with the internal direction taken to be `0`. -/
theorem isVisibleRecession_escape (i : Bool) :
    IsVisibleRecession system i (fun _ => 0) (escape i) := by
  refine ⟨fun e => e.elim, fun n => ?_, ?_⟩
  · rw [show n = () from rfl, dot_C, dot_Q]
    norm_num
  · refine recession_unilateral_of_custody_eq_zero (custody_escape i) ?_
    intro u _
    rw [dot_B]
    norm_num

/-! #### The falsifier -/

/-- **The falsifier (Question 72, §A.5 and Part E).**  The inequality
`t false + t true ≤ 0` is valid on the full system, yet it has *no*
typed Bellman lift for *either* owner and *any* bound `β`.  The obstruction
is custody: owner `i`'s rows constrain only coordinate `i`, so the
coordinate `!i` escapes to `+∞` inside owner `i`'s relaxation while
staying invisible to owner `i`'s custody map. -/
theorem not_hasTypedLift (i : Bool) (β : ℝ) :
    ¬ HasTypedLift system i crossNormal β :=
  not_hasTypedLift_of_visibleRecession (memVisible_zero i)
    (isVisibleRecession_escape i)
    (by rw [dot_crossNormal_escape]; norm_num) β

/-- The same failure read through the Farkas characterization: the
cross-owner inequality is not even valid on either owner's relaxation, at
any bound.  Owner `i` simply does not constrain coordinate `!i`. -/
theorem not_validOnVisible (i : Bool) (β : ℝ) :
    ¬ ValidOnVisible system i crossNormal β := fun hvalid =>
  not_hasTypedLift i β
    ((hasTypedLift_iff_validOnVisible system i crossNormal β
      ⟨_, _, memVisible_zero i⟩).mpr hvalid)

/-- The falsifier at the natural bound `β = 0`, contrasted with
`validOnFull`: a valid inequality of the full system owned by nobody. -/
theorem no_owner_lifts_crossNormal :
    ValidOnFull system crossNormal 0 ∧ ∀ i : Bool,
      ¬ HasTypedLift system i crossNormal 0 :=
  ⟨validOnFull, fun i => not_hasTypedLift i 0⟩

/-! #### The positive vacuity probe -/

/-- **Positive probe.**  The inequality `t false ≤ 0` is supported on owner
`false`'s own visible coordinate -- indeed `ownNormal false` is literally
owner `false`'s own target row `system.S false` -- and it is implied by
owner `false`'s relaxation (`y ≤ 0` and `t false ≤ y`).  It does have a
`false`-typed lift: put weight `1` on the owner-neutral row and weight `1`
on owner `false`'s own row, and the internal coefficient cancels
*within one owner*. -/
theorem hasTypedLift_ownNormal : HasTypedLift system false (ownNormal false) 0 := by
  refine ⟨fun e => e.elim, fun _ => 1, fun u => if u then 0 else 1, ?_⟩
  refine ⟨fun n => by norm_num, fun u => ?_, fun u hu => ?_, fun v => ?_,
    fun w => ?_, ?_⟩
  · cases u <;> norm_num
  · cases u
    · exact absurd rfl hu
    · norm_num
  · simp [system]
  · cases w <;> simp [system, ownNormal]
  · simp [system]

/-- The probe functional is exactly owner `false`'s own target row: it is
supported on the coordinates owner `false` has custody of. -/
theorem ownNormal_eq_row : system.S false = ownNormal false := rfl

/-- Soundness applied to the probe: `t false ≤ 0` really is valid on owner
`false`'s relaxation. -/
theorem validOnVisible_ownNormal :
    ValidOnVisible system false (ownNormal false) 0 :=
  validOnVisible_of_hasTypedLift hasTypedLift_ownNormal

end CrossOwnerCancellation

end

end OwnerTypedDualLifting
end LinearAlgebra
end Math


