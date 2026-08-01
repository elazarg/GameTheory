/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.OrientedAccountBridge
import Math.LinearAlgebra.OwnerTypedDualLifting
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The owner-obstruction cokernel

**Provenance.**  This file glues the two "Layer A" routing interfaces
`Math.LinearAlgebra.OwnerTypedDualLifting` (Question 72: owner-typed dual
lifting, custody) and `Math.LinearAlgebra.OwnerLabeledFlowHolonomy`
(Question 71: account potentials, circulations, holonomy) into a single
finite-dimensional invariant: the quotient of the target-normal space by
everything a *single owner* can certify, either through its own unilateral
Bellman rows or through a global scalar account potential.

**This file is deliberately game-free.**  Everything below is finite linear
algebra over `ℝ`.  `Ω` is a bare owner-label type, `E`, `N`, `U` are bare
finite row index types, `Y`, `T` bare finite column index types, `V` a bare
finite vertex type, and `src`/`trans` a bare source map and a bare weight
matrix.  No games, strategies, payoffs, probability measures or dynamics
occur.

## The mandatory caveat: a nonzero class is algebra, not strategy

A nonzero obstruction class is a statement about **linear algebra only**: it
says that a target normal is not the sum of an owner-`i`-typed signed
multiplier combination and an account coboundary.  It is **not**, by itself,
a strategic obstruction.  The surrounding project contains a machine-checked
pure-externality example in which strictly positive holonomy coexists with a
genuine uniform equilibrium; positive holonomy — and a fortiori a nonzero
class, which is weaker in one direction and stronger in another — therefore
does **not** entail that any strategic construction fails.  The cokernel
*classifies gluing failure of certificates*.  Consuming a nonzero class as a
statement about players, strategies or equilibria requires a separate,
separately proved theorem, and none is offered here.  (No game file is
imported, on purpose.)

## Main definitions

* `rowLoad`: the multiplier-weighted combination of the three row blocks of a
  typed cell, with the unilateral multipliers pre-multiplied by a mask.  The
  mask replaces the support condition `IsTypedLift.owner_pure`.
* `signedNormals P m`: the submodule of target normals reachable by *signed*
  `m`-masked multipliers whose internal coefficients cancel.  This is the
  linearization of `OwnerTypedDualLifting.HasTypedLift` (signs and the bound
  `β` dropped, so that the object is a subspace and not merely a cone).
* `IsDualDirection P m lam x`: the dual test data — the lineality-space form
  of `OwnerTypedDualLifting.IsVisibleRecession`.
* `OwnerSystem`: a typed cell together with a finite flow structure
  `src : T → V`, `trans : T → V → ℝ` on the boundary target index.  The
  target coordinates double as the rows of the flow system, so a target
  normal is simultaneously a charge cochain in the sense of
  `OwnerLabeledFlowHolonomy`.
* `accountCell`: the typed cell obtained by appending the account block, i.e.
  the columns `incidenceEntry src trans` of the incidence matrix, to the
  structural equations.  Account potentials become free multipliers.
* `ownerNormals sys i` and `globalNormals sys`: what owner `i` alone, resp.
  all owners together, can certify.
* `Obstruction sys i := (T → ℝ) ⧸ ownerNormals sys i` and
  `obstructionClass`: the cokernel and the class map.
* `IsObstructionTest sys i lam x`: the dual test vectors — signed
  circulations of the flow system that additionally lie in the lineality
  space of owner `i`'s visible relaxation.

## Main results

* `mem_signedNormals_iff`: **the Farkas duality.**  A target normal is a
  signed masked lift **iff** it annihilates every dual direction.  Proved
  with the in-tree `Math.LinearAlgebra.theorem_of_alternative` (the
  infeasibility ⇔ certificate form; the objective-bound
  `farkas_lemma_fintype` is unusable here because it presupposes primal
  feasibility, which is exactly what is in question).
* `mem_ownerNormals_iff`: the primal, gluing form — `α` is certifiable by
  owner `i` exactly when it decomposes as an owner-`i`-pure signed Bellman
  combination plus a scalar account coboundary.
* `obstructionClass_eq_zero_iff_forall_test`: the class of `α` vanishes iff
  the ownerwise witnesses glue iff every obstruction test pairs to `0`.
* `obstruction_alternative` / `not_and_of_obstruction_alternative`: the
  computability statement.  Either the decomposition exists, or an explicit
  separating signed circulation certifies the nonzero class; never both.
* `mem_ownerNormals_of_hasTypedLift` /
  `not_hasTypedLift_of_obstructionClass_ne_zero`: the lifting presentation.
  A nonzero class kills every `OwnerTypedDualLifting.HasTypedLift` at every
  bound (the converse is false — a typed lift also needs signs and a bound).
* `finrank_obstruction_add_finrank`: the object is finite dimensional, of
  corank the dimension of the certifiable subspace.
* `ownerNormals_eq_globalNormals_of_subsingleton`,
  `obstructionClass_eq_zero_of_subsingleton` and
  `subsingleton_obstruction_of_subsingleton`: the required sanity theorem.
  With a single owner, ownerwise = global, so every globally certifiable
  normal has zero class, and the cokernel is literally the zero space as soon
  as every normal is certifiable.  Honest scope: the ambient is *all* target
  normals, so a single-owner cokernel need not vanish outright — see
  `ParallelRowsCounterexample`, where it does not.
* `TrivialSystem.ownerNormals_eq_bot`: the zero-system vacuity probe.  On the
  zero system the certifiable subspace is `⊥`, so the class map is injective
  and nothing below is vacuously true.
* `obstructionClass_eq_zero_iff_exists_isExactBridge`: with no typed rows the
  object is exactly the coboundary cokernel — a class vanishes iff the charge
  cochain is an exact account bridge in the sense of `OrientedAccountBridge`.
* `zeroHolonomy_of_obstructionClass_eq_zero`: **one direction of the duality
  with `ZeroHolonomy`**, under the hypothesis that every circulation extends
  to an obstruction test (automatic when the typed blocks are absent).
* `ParallelRowsCounterexample`: **the converse fails.**  On the parallel-rows
  system of `OrientedAccountBridge` every circulation is zero — so
  `ZeroHolonomy` holds for every charge — yet the class of `charge` is
  nonzero, separated by the *signed* cycle `(1, -1)`.  The obstruction space
  sees the whole signed cycle space; `ZeroHolonomy` sees only its
  nonnegative cone.
* `TwoCycleObstruction.obstructionClass_ne_zero` and
  `CrossOwnerObstruction.obstructionClass_ne_zero`: the two mandatory
  falsifiers recomputed as class computations, each exhibited by an explicit
  nonnegative circulation.
-/

open Finset BigOperators
open Math.LinearAlgebra.OwnerLabeledFlowHolonomy
open Math.LinearAlgebra.OwnerTypedDualLifting

namespace Math
namespace LinearAlgebra
namespace OwnerObstructionCokernel

noncomputable section

set_option autoImplicit false

/-! ### Weighted row sums -/

section RowSums

variable {I J : Type*} [Fintype I]

/-- The weighted row sum `∑ i, m i * M i j`: the `j`-th coordinate of the
multiplier-weighted combination of the rows of `M`. -/
def wsum (m : I → ℝ) (M : I → J → ℝ) (j : J) : ℝ := ∑ i, m i * M i j

theorem wsum_zero (M : I → J → ℝ) (j : J) : wsum (fun _ => (0 : ℝ)) M j = 0 := by
  simp [wsum]

theorem wsum_add (a b : I → ℝ) (M : I → J → ℝ) (j : J) :
    wsum (fun i => a i + b i) M j = wsum a M j + wsum b M j := by
  simp only [wsum, add_mul]
  exact Finset.sum_add_distrib

theorem wsum_smul (s : ℝ) (a : I → ℝ) (M : I → J → ℝ) (j : J) :
    wsum (fun i => s * a i) M j = s * wsum a M j := by
  simp only [wsum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end RowSums

/-! ### The three-block multiplier load -/

section Blocks

variable {E N U K : Type*} [Fintype E] [Fintype N] [Fintype U]

/-- The multiplier-weighted combination of the three row blocks of a typed
cell, evaluated on the column block `K`.  The unilateral multipliers are
pre-multiplied by the mask `m`; masking by `ownerMask` is what replaces the
support condition `OwnerTypedDualLifting.IsTypedLift.owner_pure`. -/
def rowLoad (m : U → ℝ) (η : E → ℝ) (ν : N → ℝ) (μ : U → ℝ) (MA : E → K → ℝ)
    (MC : N → K → ℝ) (MB : U → K → ℝ) (k : K) : ℝ :=
  wsum η MA k + wsum ν MC k + wsum (fun u => m u * μ u) MB k

theorem rowLoad_zero (m : U → ℝ) (MA : E → K → ℝ) (MC : N → K → ℝ)
    (MB : U → K → ℝ) (k : K) :
    rowLoad m (fun _ => 0) (fun _ => 0) (fun _ => 0) MA MC MB k = 0 := by
  have h : (fun u => m u * (0 : ℝ)) = fun _ : U => (0 : ℝ) := by
    funext u; ring
  rw [rowLoad, h, wsum_zero, wsum_zero, wsum_zero]
  ring

theorem rowLoad_add (m : U → ℝ) (η η' : E → ℝ) (ν ν' : N → ℝ) (μ μ' : U → ℝ)
    (MA : E → K → ℝ) (MC : N → K → ℝ) (MB : U → K → ℝ) (k : K) :
    rowLoad m (fun e => η e + η' e) (fun n => ν n + ν' n) (fun u => μ u + μ' u)
        MA MC MB k
      = rowLoad m η ν μ MA MC MB k + rowLoad m η' ν' μ' MA MC MB k := by
  have h : (fun u => m u * (μ u + μ' u)) = fun u => m u * μ u + m u * μ' u := by
    funext u; ring
  rw [rowLoad, rowLoad, rowLoad, h, wsum_add, wsum_add, wsum_add]
  ring

theorem rowLoad_smul (s : ℝ) (m : U → ℝ) (η : E → ℝ) (ν : N → ℝ) (μ : U → ℝ)
    (MA : E → K → ℝ) (MC : N → K → ℝ) (MB : U → K → ℝ) (k : K) :
    rowLoad m (fun e => s * η e) (fun n => s * ν n) (fun u => s * μ u) MA MC MB k
      = s * rowLoad m η ν μ MA MC MB k := by
  have h : (fun u => m u * (s * μ u)) = fun u => s * (m u * μ u) := by
    funext u; ring
  rw [rowLoad, rowLoad, h, wsum_smul, wsum_smul, wsum_smul]
  ring

/-- Pairing the multiplier load against a column vector transposes it back
onto the rows. -/
theorem sum_rowLoad_mul [Fintype K] (m : U → ℝ) (η : E → ℝ) (ν : N → ℝ)
    (μ : U → ℝ) (MA : E → K → ℝ) (MC : N → K → ℝ) (MB : U → K → ℝ)
    (z : K → ℝ) :
    (∑ k, rowLoad m η ν μ MA MC MB k * z k)
      = (∑ e, η e * dot (MA e) z) + (∑ n, ν n * dot (MC n) z)
        + ∑ u, m u * μ u * dot (MB u) z := by
  rw [sum_mul_dot, sum_mul_dot, sum_mul_dot]
  simp only [rowLoad, wsum, add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

end Blocks

/-! ### Signed masked lifts and the submodule of certifiable normals -/

section SignedNormals

variable {Ω E N U Y T : Type*} [Fintype E] [Fintype N] [Fintype U]

/-- The internal (`Y`-block) load of a masked multiplier triple: the left
side of `OwnerTypedDualLifting.IsTypedLift.internal_cancel`. -/
def internalLoad (P : TypedCell Ω E N U Y T) (m : U → ℝ) (η : E → ℝ) (ν : N → ℝ)
    (μ : U → ℝ) : Y → ℝ :=
  rowLoad m η ν μ P.A P.C P.B

/-- The boundary (`T`-block) load of a masked multiplier triple: the left
side of `OwnerTypedDualLifting.IsTypedLift.boundary_load`. -/
def boundaryLoad (P : TypedCell Ω E N U Y T) (m : U → ℝ) (η : E → ℝ)
    (ν : N → ℝ) (μ : U → ℝ) : T → ℝ :=
  rowLoad m η ν μ P.R P.Q P.S

/-- `(η, ν, μ)` is a **signed `m`-masked lift** of the target normal `α`: the
internal coefficients cancel and the residual boundary load is exactly `α`.
This is `OwnerTypedDualLifting.IsTypedLift` with the sign constraints and the
bound `β` dropped, so that the set of such `α` is a subspace rather than a
cone. -/
structure IsSignedLift (P : TypedCell Ω E N U Y T) (m : U → ℝ) (α : T → ℝ)
    (η : E → ℝ) (ν : N → ℝ) (μ : U → ℝ) : Prop where
  /-- The internal coefficients cancel. -/
  internal_cancel : ∀ v, internalLoad P m η ν μ v = 0
  /-- The residual boundary load is exactly `α`. -/
  boundary_load : ∀ w, boundaryLoad P m η ν μ w = α w

/-- The subspace of target normals carrying a signed `m`-masked lift. -/
def signedNormals (P : TypedCell Ω E N U Y T) (m : U → ℝ) :
    Submodule ℝ (T → ℝ) where
  carrier := {α | ∃ (η : E → ℝ) (ν : N → ℝ) (μ : U → ℝ), IsSignedLift P m α η ν μ}
  zero_mem' :=
    ⟨fun _ => 0, fun _ => 0, fun _ => 0,
      ⟨fun v => rowLoad_zero m P.A P.C P.B v,
        fun w => rowLoad_zero m P.R P.Q P.S w⟩⟩
  add_mem' := by
    rintro a b ⟨η, ν, μ, ha⟩ ⟨η', ν', μ', hb⟩
    refine ⟨fun e => η e + η' e, fun n => ν n + ν' n, fun u => μ u + μ' u,
      ⟨fun v => ?_, fun w => ?_⟩⟩
    · have h1 := ha.internal_cancel v
      have h2 := hb.internal_cancel v
      simp only [internalLoad] at h1 h2 ⊢
      rw [rowLoad_add, h1, h2, add_zero]
    · have h1 := ha.boundary_load w
      have h2 := hb.boundary_load w
      simp only [boundaryLoad] at h1 h2 ⊢
      rw [rowLoad_add, h1, h2]
      rfl
  smul_mem' := by
    rintro s a ⟨η, ν, μ, ha⟩
    refine ⟨fun e => s * η e, fun n => s * ν n, fun u => s * μ u,
      ⟨fun v => ?_, fun w => ?_⟩⟩
    · have h1 := ha.internal_cancel v
      simp only [internalLoad] at h1 ⊢
      rw [rowLoad_smul, h1, mul_zero]
    · have h1 := ha.boundary_load w
      simp only [boundaryLoad] at h1 ⊢
      rw [rowLoad_smul, h1]
      rfl

theorem mem_signedNormals {P : TypedCell Ω E N U Y T} {m : U → ℝ} {α : T → ℝ} :
    α ∈ signedNormals P m ↔ ∃ η ν μ, IsSignedLift P m α η ν μ := Iff.rfl

end SignedNormals

/-! ### Dual directions and soundness -/

section DualDirections

variable {Ω E N U Y T : Type*} [Fintype E] [Fintype N] [Fintype U] [Fintype Y]
  [Fintype T]

omit [Fintype E] [Fintype N] [Fintype U] in
theorem dot_neg {J : Type*} [Fintype J] (a z : J → ℝ) :
    dot a (fun j => -z j) = -dot a z := by
  rw [dot, dot, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- A **dual direction** for the masked system: the lineality-space form of
`OwnerTypedDualLifting.IsVisibleRecession`, i.e. the homogeneous *equality*
version of the owner-visible relaxation, with the mask `m` selecting which
unilateral rows are constraining. -/
structure IsDualDirection (P : TypedCell Ω E N U Y T) (m : U → ℝ) (lam : Y → ℝ)
    (x : T → ℝ) : Prop where
  /-- The structural equations, homogeneously and with equality. -/
  structural : ∀ e, dot (P.A e) lam + dot (P.R e) x = 0
  /-- The owner-neutral rows, homogeneously and with equality. -/
  neutral : ∀ n, dot (P.C n) lam + dot (P.Q n) x = 0
  /-- The masked unilateral rows, homogeneously and with equality. -/
  unilateral : ∀ u, m u * (dot (P.B u) lam + dot (P.S u) x) = 0

omit [Fintype E] [Fintype N] [Fintype U] in
/-- Dual directions form a cone symmetric under negation, so a separating
direction can always be normalized to pair positively. -/
theorem IsDualDirection.neg {P : TypedCell Ω E N U Y T} {m : U → ℝ}
    {lam : Y → ℝ} {x : T → ℝ} (h : IsDualDirection P m lam x) :
    IsDualDirection P m (fun v => -lam v) fun w => -x w := by
  refine ⟨fun e => ?_, fun n => ?_, fun u => ?_⟩
  · rw [dot_neg, dot_neg]
    have := h.structural e
    linarith
  · rw [dot_neg, dot_neg]
    have := h.neutral n
    linarith
  · rw [dot_neg, dot_neg]
    have := h.unilateral u
    nlinarith [this]

/-- **Soundness.**  A signed masked lift of `α` forces `α` to annihilate
every dual direction.  This is the transposed form of
`OwnerTypedDualLifting.dot_le_rhs_of_isTypedLift`. -/
theorem dot_eq_zero_of_isSignedLift {P : TypedCell Ω E N U Y T} {m : U → ℝ}
    {α : T → ℝ} {η : E → ℝ} {ν : N → ℝ} {μ : U → ℝ} {lam : Y → ℝ} {x : T → ℝ}
    (hlift : IsSignedLift P m α η ν μ) (hdual : IsDualDirection P m lam x) :
    dot α x = 0 := by
  have hb : (∑ w, boundaryLoad P m η ν μ w * x w) = dot α x := by
    rw [dot]
    exact Finset.sum_congr rfl fun w _ => by rw [hlift.boundary_load w]
  have hi : (∑ v, internalLoad P m η ν μ v * lam v) = 0 :=
    Finset.sum_eq_zero fun v _ => by rw [hlift.internal_cancel v, zero_mul]
  rw [boundaryLoad, sum_rowLoad_mul] at hb
  rw [internalLoad, sum_rowLoad_mul] at hi
  have hE : (∑ e, η e * dot (P.A e) lam) + ∑ e, η e * dot (P.R e) x = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [← mul_add, hdual.structural e, mul_zero]
  have hN : (∑ n, ν n * dot (P.C n) lam) + ∑ n, ν n * dot (P.Q n) x = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [← mul_add, hdual.neutral n, mul_zero]
  have hU : (∑ u, m u * μ u * dot (P.B u) lam)
      + ∑ u, m u * μ u * dot (P.S u) x = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun u _ => ?_
    calc m u * μ u * dot (P.B u) lam + m u * μ u * dot (P.S u) x
        = μ u * (m u * (dot (P.B u) lam + dot (P.S u) x)) := by ring
      _ = μ u * 0 := by rw [hdual.unilateral u]
      _ = 0 := mul_zero _
  linarith

end DualDirections

/-! ### The Farkas duality

The decomposition question "is `α` a signed `m`-masked lift?" is a finite
system of linear *equations* in free multipliers.  Written as two weak
inequalities per equation it becomes the normal form `A z ≥ b` consumed by
`Math.LinearAlgebra.theorem_of_alternative`, whose Farkas certificate is
literally a dual direction pairing positively with `α`.  Note that the
objective-bound form `Math.LinearAlgebra.farkas_lemma_fintype` cannot be used
here: it presupposes primal feasibility, which is exactly the question. -/

section FarkasDuality

variable {Ω E N U Y T : Type*}

/-- Row index of the decomposition system: the internal cancellation
equations in both orientations, then the boundary load equations in both
orientations. -/
abbrev LiftRow (Y T : Type*) : Type _ := Y ⊕ Y ⊕ T ⊕ T

/-- Column index of the decomposition system: the three multiplier blocks. -/
abbrev LiftCol (E N U : Type*) : Type _ := E ⊕ N ⊕ U

/-- The internal-block coefficients of one column of the decomposition
system. -/
def liftInternal (P : TypedCell Ω E N U Y T) (m : U → ℝ) :
    LiftCol E N U → Y → ℝ
  | Sum.inl e => P.A e
  | Sum.inr (Sum.inl n) => P.C n
  | Sum.inr (Sum.inr u) => fun v => m u * P.B u v

/-- The boundary-block coefficients of one column of the decomposition
system. -/
def liftBoundary (P : TypedCell Ω E N U Y T) (m : U → ℝ) :
    LiftCol E N U → T → ℝ
  | Sum.inl e => P.R e
  | Sum.inr (Sum.inl n) => P.Q n
  | Sum.inr (Sum.inr u) => fun w => m u * P.S u w

/-- The coefficient matrix of the decomposition system, in the `≥` normal
form consumed by `Math.LinearAlgebra.theorem_of_alternative`. -/
def liftMatrix (P : TypedCell Ω E N U Y T) (m : U → ℝ) :
    LiftRow Y T → LiftCol E N U → ℝ
  | Sum.inl v, c => liftInternal P m c v
  | Sum.inr (Sum.inl v), c => -liftInternal P m c v
  | Sum.inr (Sum.inr (Sum.inl w)), c => liftBoundary P m c w
  | Sum.inr (Sum.inr (Sum.inr w)), c => -liftBoundary P m c w

/-- The right-hand side of the decomposition system: the internal equations
are homogeneous, the boundary equations demand exactly `α`. -/
def liftRhs (α : T → ℝ) : LiftRow Y T → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr (Sum.inl w)) => α w
  | Sum.inr (Sum.inr (Sum.inr w)) => -α w

variable [Fintype E] [Fintype N] [Fintype U] [Fintype Y] [Fintype T]

omit [Fintype E] [Fintype N] [Fintype U] [Fintype Y] [Fintype T] in
theorem dot_const_mul {J : Type*} [Fintype J] (s : ℝ) (a z : J → ℝ) :
    dot (fun j => s * a j) z = s * dot a z := by
  rw [dot, dot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [Fintype Y] [Fintype T] in
theorem sum_liftMatrix_internal (P : TypedCell Ω E N U Y T) (m : U → ℝ)
    (z : LiftCol E N U → ℝ) (v : Y) :
    (∑ c, liftMatrix P m (Sum.inl v) c * z c)
      = internalLoad P m (fun e => z (Sum.inl e))
          (fun n => z (Sum.inr (Sum.inl n)))
          (fun u => z (Sum.inr (Sum.inr u))) v := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : (∑ e, liftMatrix P m (Sum.inl v) (Sum.inl e) * z (Sum.inl e))
      = wsum (fun e => z (Sum.inl e)) P.A v := by
    rw [wsum]
    refine Finset.sum_congr rfl fun e _ => ?_
    change P.A e v * z (Sum.inl e) = z (Sum.inl e) * P.A e v
    ring
  have h2 : (∑ n, liftMatrix P m (Sum.inl v) (Sum.inr (Sum.inl n))
        * z (Sum.inr (Sum.inl n)))
      = wsum (fun n => z (Sum.inr (Sum.inl n))) P.C v := by
    rw [wsum]
    refine Finset.sum_congr rfl fun n _ => ?_
    change P.C n v * z (Sum.inr (Sum.inl n)) = z (Sum.inr (Sum.inl n)) * P.C n v
    ring
  have h3 : (∑ u, liftMatrix P m (Sum.inl v) (Sum.inr (Sum.inr u))
        * z (Sum.inr (Sum.inr u)))
      = wsum (fun u => m u * z (Sum.inr (Sum.inr u))) P.B v := by
    rw [wsum]
    refine Finset.sum_congr rfl fun u _ => ?_
    change m u * P.B u v * z (Sum.inr (Sum.inr u))
      = m u * z (Sum.inr (Sum.inr u)) * P.B u v
    ring
  rw [h1, h2, h3, internalLoad, rowLoad]
  ring

omit [Fintype Y] [Fintype T] in
theorem sum_liftMatrix_internal_neg (P : TypedCell Ω E N U Y T) (m : U → ℝ)
    (z : LiftCol E N U → ℝ) (v : Y) :
    (∑ c, liftMatrix P m (Sum.inr (Sum.inl v)) c * z c)
      = -internalLoad P m (fun e => z (Sum.inl e))
          (fun n => z (Sum.inr (Sum.inl n)))
          (fun u => z (Sum.inr (Sum.inr u))) v := by
  rw [← sum_liftMatrix_internal P m z v, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  change -liftInternal P m c v * z c = -(liftInternal P m c v * z c)
  ring

omit [Fintype Y] [Fintype T] in
theorem sum_liftMatrix_boundary (P : TypedCell Ω E N U Y T) (m : U → ℝ)
    (z : LiftCol E N U → ℝ) (w : T) :
    (∑ c, liftMatrix P m (Sum.inr (Sum.inr (Sum.inl w))) c * z c)
      = boundaryLoad P m (fun e => z (Sum.inl e))
          (fun n => z (Sum.inr (Sum.inl n)))
          (fun u => z (Sum.inr (Sum.inr u))) w := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h1 : (∑ e, liftMatrix P m (Sum.inr (Sum.inr (Sum.inl w))) (Sum.inl e)
        * z (Sum.inl e))
      = wsum (fun e => z (Sum.inl e)) P.R w := by
    rw [wsum]
    refine Finset.sum_congr rfl fun e _ => ?_
    change P.R e w * z (Sum.inl e) = z (Sum.inl e) * P.R e w
    ring
  have h2 : (∑ n, liftMatrix P m (Sum.inr (Sum.inr (Sum.inl w)))
        (Sum.inr (Sum.inl n)) * z (Sum.inr (Sum.inl n)))
      = wsum (fun n => z (Sum.inr (Sum.inl n))) P.Q w := by
    rw [wsum]
    refine Finset.sum_congr rfl fun n _ => ?_
    change P.Q n w * z (Sum.inr (Sum.inl n)) = z (Sum.inr (Sum.inl n)) * P.Q n w
    ring
  have h3 : (∑ u, liftMatrix P m (Sum.inr (Sum.inr (Sum.inl w)))
        (Sum.inr (Sum.inr u)) * z (Sum.inr (Sum.inr u)))
      = wsum (fun u => m u * z (Sum.inr (Sum.inr u))) P.S w := by
    rw [wsum]
    refine Finset.sum_congr rfl fun u _ => ?_
    change m u * P.S u w * z (Sum.inr (Sum.inr u))
      = m u * z (Sum.inr (Sum.inr u)) * P.S u w
    ring
  rw [h1, h2, h3, boundaryLoad, rowLoad]
  ring

omit [Fintype Y] [Fintype T] in
theorem sum_liftMatrix_boundary_neg (P : TypedCell Ω E N U Y T) (m : U → ℝ)
    (z : LiftCol E N U → ℝ) (w : T) :
    (∑ c, liftMatrix P m (Sum.inr (Sum.inr (Sum.inr w))) c * z c)
      = -boundaryLoad P m (fun e => z (Sum.inl e))
          (fun n => z (Sum.inr (Sum.inl n)))
          (fun u => z (Sum.inr (Sum.inr u))) w := by
  rw [← sum_liftMatrix_boundary P m z w, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  change -liftBoundary P m c w * z c = -(liftBoundary P m c w * z c)
  ring

omit [Fintype Y] [Fintype T] in
/-- Feasibility of the encoded weak-inequality system is exactly the
existence of a signed masked lift. -/
theorem liftFeasible_iff (P : TypedCell Ω E N U Y T) (m : U → ℝ) (α : T → ℝ)
    (z : LiftCol E N U → ℝ) :
    (∀ r, liftRhs α r ≤ ∑ c, liftMatrix P m r c * z c)
      ↔ IsSignedLift P m α (fun e => z (Sum.inl e))
          (fun n => z (Sum.inr (Sum.inl n)))
          (fun u => z (Sum.inr (Sum.inr u))) := by
  constructor
  · intro h
    refine ⟨fun v => ?_, fun w => ?_⟩
    · have h1 := h (Sum.inl v)
      have h2 := h (Sum.inr (Sum.inl v))
      rw [sum_liftMatrix_internal] at h1
      rw [sum_liftMatrix_internal_neg] at h2
      simp only [liftRhs] at h1 h2
      linarith
    · have h1 := h (Sum.inr (Sum.inr (Sum.inl w)))
      have h2 := h (Sum.inr (Sum.inr (Sum.inr w)))
      rw [sum_liftMatrix_boundary] at h1
      rw [sum_liftMatrix_boundary_neg] at h2
      simp only [liftRhs] at h1 h2
      linarith
  · intro hlift r
    match r with
    | Sum.inl v =>
      rw [sum_liftMatrix_internal, hlift.internal_cancel v]
      simp [liftRhs]
    | Sum.inr (Sum.inl v) =>
      rw [sum_liftMatrix_internal_neg, hlift.internal_cancel v]
      simp [liftRhs]
    | Sum.inr (Sum.inr (Sum.inl w)) =>
      rw [sum_liftMatrix_boundary, hlift.boundary_load w]
      simp [liftRhs]
    | Sum.inr (Sum.inr (Sum.inr w)) =>
      rw [sum_liftMatrix_boundary_neg, hlift.boundary_load w]
      simp [liftRhs]

omit [Fintype E] [Fintype N] [Fintype U] in
/-- A column of the transposed system: the multiplier attached to the two
orientations of each equation reassembles into one signed dual variable. -/
theorem sum_liftMatrix_col (P : TypedCell Ω E N U Y T) (m : U → ℝ)
    (q : LiftRow Y T → ℝ) (c : LiftCol E N U) :
    (∑ r, q r * liftMatrix P m r c)
      = dot (liftInternal P m c)
            (fun v => q (Sum.inl v) - q (Sum.inr (Sum.inl v)))
        + dot (liftBoundary P m c)
            (fun w => q (Sum.inr (Sum.inr (Sum.inl w)))
              - q (Sum.inr (Sum.inr (Sum.inr w)))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, dot,
    dot]
  have hA : (∑ v, liftInternal P m c v
        * (q (Sum.inl v) - q (Sum.inr (Sum.inl v))))
      = (∑ v, q (Sum.inl v) * liftMatrix P m (Sum.inl v) c)
        + ∑ v, q (Sum.inr (Sum.inl v))
            * liftMatrix P m (Sum.inr (Sum.inl v)) c := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    change liftInternal P m c v * (q (Sum.inl v) - q (Sum.inr (Sum.inl v)))
      = q (Sum.inl v) * liftInternal P m c v
        + q (Sum.inr (Sum.inl v)) * -liftInternal P m c v
    ring
  have hB : (∑ w, liftBoundary P m c w
        * (q (Sum.inr (Sum.inr (Sum.inl w)))
          - q (Sum.inr (Sum.inr (Sum.inr w)))))
      = (∑ w, q (Sum.inr (Sum.inr (Sum.inl w)))
            * liftMatrix P m (Sum.inr (Sum.inr (Sum.inl w))) c)
        + ∑ w, q (Sum.inr (Sum.inr (Sum.inr w)))
            * liftMatrix P m (Sum.inr (Sum.inr (Sum.inr w))) c := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    change liftBoundary P m c w * (q (Sum.inr (Sum.inr (Sum.inl w)))
          - q (Sum.inr (Sum.inr (Sum.inr w))))
      = q (Sum.inr (Sum.inr (Sum.inl w))) * liftBoundary P m c w
        + q (Sum.inr (Sum.inr (Sum.inr w))) * -liftBoundary P m c w
    ring
  rw [hA, hB]
  ring

omit [Fintype E] [Fintype N] [Fintype U] in
/-- The transposed right-hand side is the holonomy pairing of `α` with the
reassembled boundary dual variable. -/
theorem sum_liftRhs (α : T → ℝ) (q : LiftRow Y T → ℝ) :
    (∑ r, q r * liftRhs α r)
      = dot α (fun w => q (Sum.inr (Sum.inr (Sum.inl w)))
          - q (Sum.inr (Sum.inr (Sum.inr w)))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, dot]
  have h0 : (∑ v, q (Sum.inl v) * liftRhs (Y := Y) α (Sum.inl v)) = 0 :=
    Finset.sum_eq_zero fun v _ => by simp [liftRhs]
  have h0' : (∑ v, q (Sum.inr (Sum.inl v))
      * liftRhs (Y := Y) α (Sum.inr (Sum.inl v))) = 0 :=
    Finset.sum_eq_zero fun v _ => by simp [liftRhs]
  have h : (∑ w, α w * (q (Sum.inr (Sum.inr (Sum.inl w)))
        - q (Sum.inr (Sum.inr (Sum.inr w)))))
      = (∑ w, q (Sum.inr (Sum.inr (Sum.inl w)))
            * liftRhs (Y := Y) α (Sum.inr (Sum.inr (Sum.inl w))))
        + ∑ w, q (Sum.inr (Sum.inr (Sum.inr w)))
            * liftRhs (Y := Y) α (Sum.inr (Sum.inr (Sum.inr w))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    change α w * (q (Sum.inr (Sum.inr (Sum.inl w)))
          - q (Sum.inr (Sum.inr (Sum.inr w))))
      = q (Sum.inr (Sum.inr (Sum.inl w))) * α w
        + q (Sum.inr (Sum.inr (Sum.inr w))) * -α w
    ring
  rw [h, h0, h0']
  ring

/-- **The Farkas duality for signed masked lifts.**  A target normal carries
a signed `m`-masked lift **iff** it annihilates every dual direction.  The
`←` direction is the theorem of the alternative applied to the decomposition
system: a Farkas certificate of its infeasibility is literally a dual
direction pairing positively with `α`. -/
theorem mem_signedNormals_iff (P : TypedCell Ω E N U Y T) (m : U → ℝ)
    (α : T → ℝ) :
    α ∈ signedNormals P m ↔ ∀ lam x, IsDualDirection P m lam x → dot α x = 0 := by
  classical
  refine ⟨fun hmem lam x hdual => ?_, fun hforall => ?_⟩
  · obtain ⟨η, ν, μ, hlift⟩ := hmem
    exact dot_eq_zero_of_isSignedLift hlift hdual
  · by_contra hmem
    set ec : LiftCol E N U ≃ Fin (Fintype.card (LiftCol E N U)) :=
      Fintype.equivFin (LiftCol E N U) with hec
    set Amat : LiftRow Y T → Fin (Fintype.card (LiftCol E N U)) → ℝ :=
      fun r k => liftMatrix P m r (ec.symm k) with hAmat
    have hrow : ∀ (r : LiftRow Y T)
        (z : Fin (Fintype.card (LiftCol E N U)) → ℝ),
        rowEval Amat r z = ∑ c, liftMatrix P m r c * z (ec c) := by
      intro r z
      rw [rowEval,
        ← Equiv.sum_comp ec.symm fun c => liftMatrix P m r c * z (ec c)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hAmat]
      simp
    have hcol : ∀ (q : LiftRow Y T → ℝ) (c : LiftCol E N U),
        (∑ r, q r * Amat r (ec c)) = ∑ r, q r * liftMatrix P m r c := by
      intro q c
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hAmat]
      simp
    have hinfeas : ¬ IsFeasible Amat (liftRhs α) := by
      rintro ⟨z, hz⟩
      refine hmem ⟨_, _, _,
        (liftFeasible_iff P m α fun c => z (ec c)).mp fun r => ?_⟩
      have hr := hz r
      rw [hrow] at hr
      exact hr
    obtain ⟨q, hq_nonneg, hq_zero, hq_pos⟩ :=
      (theorem_of_alternative Amat (liftRhs α)).mp hinfeas
    have hdual : IsDualDirection P m
        (fun v => q (Sum.inl v) - q (Sum.inr (Sum.inl v)))
        (fun w => q (Sum.inr (Sum.inr (Sum.inl w)))
          - q (Sum.inr (Sum.inr (Sum.inr w)))) := by
      refine ⟨fun e => ?_, fun n => ?_, fun u => ?_⟩
      · have h := hq_zero (ec (Sum.inl e))
        rw [hcol, sum_liftMatrix_col] at h
        exact h
      · have h := hq_zero (ec (Sum.inr (Sum.inl n)))
        rw [hcol, sum_liftMatrix_col] at h
        exact h
      · have h := hq_zero (ec (Sum.inr (Sum.inr u)))
        rw [hcol, sum_liftMatrix_col] at h
        simp only [liftInternal, liftBoundary] at h
        rw [dot_const_mul, dot_const_mul] at h
        linarith
    have hzero := hforall _ _ hdual
    rw [sum_liftRhs] at hq_pos
    linarith

end FarkasDuality

/-! ### Owner-labeled systems and the obstruction cokernel -/

section OwnerLayer

variable {Ω E N U Y T V : Type*}

/-- An **owner-labeled system**: a typed finite cell of
`OwnerTypedDualLifting` together with a finite flow structure on the boundary
target index.  The target coordinates do double duty: they are the boundary
columns of the typed cell *and* the rows of the flow system, so a target
normal `α : T → ℝ` is simultaneously a charge cochain in the sense of
`OwnerLabeledFlowHolonomy`. -/
structure OwnerSystem (Ω E N U Y T V : Type*) where
  /-- The typed finite cell: structural equations, owner-neutral rows and
  owner-tagged unilateral rows. -/
  cell : TypedCell Ω E N U Y T
  /-- The source vertex of each target coordinate read as a Bellman row. -/
  src : T → V
  /-- The one-step transition weights out of each target coordinate. -/
  trans : T → V → ℝ

variable [Fintype E] [Fintype N] [Fintype U] [Fintype Y] [Fintype T]
  [Fintype V] [DecidableEq V]

/-- The **account cell**: the typed cell obtained by appending one free
multiplier per vertex, whose boundary coefficients are the columns of the
incidence matrix `OwnerLabeledFlowHolonomy.incidenceEntry` and whose internal
coefficients vanish.  A scalar account potential is exactly such a multiplier
vector, so account coboundaries become an extra structural block. -/
def accountCell (sys : OwnerSystem Ω E N U Y T V) : TypedCell Ω (E ⊕ V) N U Y T where
  ownerOf := sys.cell.ownerOf
  A := Sum.elim sys.cell.A fun _ _ => 0
  R := Sum.elim sys.cell.R fun v w => incidenceEntry sys.src sys.trans w v
  b := Sum.elim sys.cell.b fun _ => 0
  C := sys.cell.C
  Q := sys.cell.Q
  c := sys.cell.c
  B := sys.cell.B
  S := sys.cell.S
  d := sys.cell.d

omit [Fintype E] [Fintype N] [Fintype U] [Fintype Y] [Fintype T] [Fintype V]
  [DecidableEq V] in
theorem sum_elim_inl_inr {A B C : Type*} (f : A ⊕ B → C) :
    Sum.elim (fun a => f (Sum.inl a)) (fun b => f (Sum.inr b)) = f := by
  funext c
  cases c <;> rfl

omit [Fintype N] [Fintype U] [Fintype Y] [Fintype T] in
/-- The internal load of the account cell ignores the account multipliers. -/
theorem wsum_accountCell_A (sys : OwnerSystem Ω E N U Y T V) (η : E → ℝ)
    (H : V → ℝ) (v : Y) :
    wsum (Sum.elim η H) (accountCell sys).A v = ∑ e, η e * sys.cell.A e v := by
  rw [wsum, Fintype.sum_sum_type]
  have h2 : (∑ v', Sum.elim η H (Sum.inr v')
      * (accountCell sys).A (Sum.inr v') v) = 0 :=
    Finset.sum_eq_zero fun v' _ => by simp [accountCell]
  rw [h2, add_zero]
  rfl

omit [Fintype N] [Fintype U] [Fintype Y] [Fintype T] in
/-- The boundary load of the account cell adds exactly the account drift
`H (src w) - ∑ v, trans w v * H v` of `OrientedAccountBridge.IsExactBridge`. -/
theorem wsum_accountCell_R (sys : OwnerSystem Ω E N U Y T V) (η : E → ℝ)
    (H : V → ℝ) (w : T) :
    wsum (Sum.elim η H) (accountCell sys).R w
      = (∑ e, η e * sys.cell.R e w)
        + (H (sys.src w) - ∑ v, sys.trans w v * H v) := by
  rw [wsum, Fintype.sum_sum_type]
  have h1 : (∑ e, Sum.elim η H (Sum.inl e) * (accountCell sys).R (Sum.inl e) w)
      = ∑ e, η e * sys.cell.R e w := rfl
  have h2 : (∑ v, Sum.elim η H (Sum.inr v) * (accountCell sys).R (Sum.inr v) w)
      = H (sys.src w) - ∑ v, sys.trans w v * H v := by
    rw [← sum_incidenceEntry_mul sys.src sys.trans w H]
    refine Finset.sum_congr rfl fun v _ => ?_
    change H v * incidenceEntry sys.src sys.trans w v
      = incidenceEntry sys.src sys.trans w v * H v
    ring
  rw [h1, h2]

/-- The subspace of target normals owner `i` alone can certify: an
`i`-typed signed multiplier combination plus a scalar account coboundary. -/
def ownerNormals [DecidableEq Ω] (sys : OwnerSystem Ω E N U Y T V) (i : Ω) :
    Submodule ℝ (T → ℝ) :=
  signedNormals (accountCell sys) (ownerMask sys.cell i)

/-- The subspace of target normals *all* owners together can certify: the
same construction with every unilateral row available. -/
def globalNormals (sys : OwnerSystem Ω E N U Y T V) : Submodule ℝ (T → ℝ) :=
  signedNormals (accountCell sys) fun _ => 1

/-- **The owner-obstruction cokernel of owner `i`.**  A finite-dimensional
quotient: target normals modulo everything owner `i` can certify on its own.
Read `Obstruction sys i = 0` as "owner `i`'s local certificates glue". -/
abbrev Obstruction [DecidableEq Ω] (sys : OwnerSystem Ω E N U Y T V) (i : Ω) :
    Type _ :=
  (T → ℝ) ⧸ ownerNormals sys i

/-- The class of a target normal in the owner-obstruction cokernel. -/
def obstructionClass [DecidableEq Ω] (sys : OwnerSystem Ω E N U Y T V) (i : Ω)
    (α : T → ℝ) : Obstruction sys i :=
  Submodule.Quotient.mk α

omit [Fintype Y] [Fintype T] in
theorem obstructionClass_eq_zero_iff [DecidableEq Ω]
    (sys : OwnerSystem Ω E N U Y T V) (i : Ω) (α : T → ℝ) :
    obstructionClass sys i α = 0 ↔ α ∈ ownerNormals sys i :=
  Submodule.Quotient.mk_eq_zero _

/-! #### Finite dimensionality -/

omit [Fintype Y] [Fintype T] in
/-- The cokernel is a finite-dimensional real vector space. -/
theorem finiteDimensional_obstruction [Finite T] [DecidableEq Ω]
    (sys : OwnerSystem Ω E N U Y T V) (i : Ω) :
    FiniteDimensional ℝ (Obstruction sys i) :=
  Module.Finite.of_surjective (ownerNormals sys i).mkQ
    (Submodule.mkQ_surjective _)

omit [Fintype Y] in
/-- The cokernel is finite dimensional, of corank the dimension of the
certifiable subspace. -/
theorem finrank_obstruction_add_finrank [DecidableEq Ω]
    (sys : OwnerSystem Ω E N U Y T V) (i : Ω) :
    Module.finrank ℝ (Obstruction sys i)
        + Module.finrank ℝ (ownerNormals sys i) = Fintype.card T := by
  rw [Submodule.finrank_quotient_add_finrank (ownerNormals sys i),
    Module.finrank_fintype_fun_eq_card]

/-! #### Gluing: the primal description of a vanishing class -/

omit [Fintype Y] [Fintype T] in
/-- **The gluing statement.**  A target normal is certifiable by owner `i`
exactly when it decomposes as an owner-`i`-pure signed Bellman combination
plus a scalar account coboundary. -/
theorem mem_ownerNormals_iff [DecidableEq Ω] (sys : OwnerSystem Ω E N U Y T V)
    (i : Ω) (α : T → ℝ) :
    α ∈ ownerNormals sys i
      ↔ ∃ (η : E → ℝ) (ν : N → ℝ) (μ : U → ℝ) (H : V → ℝ),
          (∀ u, sys.cell.ownerOf u ≠ i → μ u = 0)
            ∧ (∀ v : Y, (∑ e, η e * sys.cell.A e v)
                + (∑ n, ν n * sys.cell.C n v)
                + (∑ u, μ u * sys.cell.B u v) = 0)
            ∧ ∀ w : T, (∑ e, η e * sys.cell.R e w)
                + (∑ n, ν n * sys.cell.Q n w)
                + (∑ u, μ u * sys.cell.S u w)
                + (H (sys.src w) - ∑ v, sys.trans w v * H v) = α w := by
  constructor
  · rintro ⟨ηv, ν, μ, hlift⟩
    have hηv := sum_elim_inl_inr ηv
    refine ⟨fun e => ηv (Sum.inl e), ν, fun u => ownerMask sys.cell i u * μ u,
      fun v => ηv (Sum.inr v), fun u hu => ?_, fun v => ?_, fun w => ?_⟩
    · change ownerMask sys.cell i u * μ u = 0
      rw [ownerMask_of_ne sys.cell i hu, zero_mul]
    · have h := hlift.internal_cancel v
      simp only [internalLoad, rowLoad] at h
      rw [← hηv, wsum_accountCell_A] at h
      exact h
    · have h := hlift.boundary_load w
      simp only [boundaryLoad, rowLoad] at h
      rw [← hηv, wsum_accountCell_R] at h
      have hQ : wsum ν (accountCell sys).Q w = ∑ n, ν n * sys.cell.Q n w := rfl
      have hS : wsum (fun u => ownerMask sys.cell i u * μ u)
          (accountCell sys).S w
          = ∑ u, ownerMask sys.cell i u * μ u * sys.cell.S u w := rfl
      rw [hQ, hS] at h
      linarith
  · rintro ⟨η, ν, μ, H, hpure, hint, hbnd⟩
    have hmask : (fun u => ownerMask sys.cell i u * μ u) = μ := by
      funext u
      by_cases hu : sys.cell.ownerOf u = i
      · rw [ownerMask_of_eq sys.cell i hu, one_mul]
      · rw [ownerMask_of_ne sys.cell i hu, zero_mul, hpure u hu]
    refine ⟨Sum.elim η H, ν, μ, ⟨fun v => ?_, fun w => ?_⟩⟩
    · simp only [internalLoad, rowLoad]
      rw [wsum_accountCell_A, hmask]
      exact hint v
    · simp only [boundaryLoad, rowLoad]
      rw [wsum_accountCell_R, hmask]
      have hQ : wsum ν (accountCell sys).Q w = ∑ n, ν n * sys.cell.Q n w := rfl
      have hS : wsum μ (accountCell sys).S w
          = ∑ u, μ u * sys.cell.S u w := rfl
      rw [hQ, hS]
      have := hbnd w
      linarith

/-! #### The dual test vectors -/

/-- **An obstruction test for owner `i`**: a signed circulation of the flow
system that additionally lies in the *lineality space* of owner `i`'s visible
relaxation, i.e. satisfies the homogeneous equality form of
`OwnerTypedDualLifting.IsVisibleRecession`.  The `unilateral` clause is
exactly the statement that `x` is invisible to owner `i`'s custody map
modulo the internal direction `lam`. -/
structure IsObstructionTest (sys : OwnerSystem Ω E N U Y T V) (i : Ω)
    (lam : Y → ℝ) (x : T → ℝ) : Prop where
  /-- `x` is a signed circulation of the flow system. -/
  circulation : ∀ v : V, incidence sys.src sys.trans x v = 0
  /-- The structural equations, homogeneously and with equality. -/
  structural : ∀ e, dot (sys.cell.A e) lam + dot (sys.cell.R e) x = 0
  /-- The owner-neutral rows, homogeneously and with equality. -/
  neutral : ∀ n, dot (sys.cell.C n) lam + dot (sys.cell.Q n) x = 0
  /-- Owner `i`'s unilateral rows, homogeneously and with equality. -/
  unilateral : ∀ u, sys.cell.ownerOf u = i →
    dot (sys.cell.B u) lam + dot (sys.cell.S u) x = 0

omit [Fintype E] [Fintype N] [Fintype U] [Fintype Y] [Fintype V] in
theorem incidence_neg (src : T → V) (Pm : T → V → ℝ) (x : T → ℝ) (v : V) :
    incidence src Pm (fun w => -x w) v = -incidence src Pm x v := by
  simp only [incidence]
  have h1 : (∑ r, if src r = v then -x r else 0)
      = -∑ r, if src r = v then x r else 0 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun r _ => by split_ifs <;> ring
  have h2 : (∑ r, -x r * Pm r v) = -∑ r, x r * Pm r v := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [h1, h2]
  ring

omit [Fintype E] [Fintype N] [Fintype U] [Fintype V] in
/-- Obstruction tests are closed under negation, so a separating test can
always be normalized to pair positively. -/
theorem IsObstructionTest.neg {sys : OwnerSystem Ω E N U Y T V} {i : Ω}
    {lam : Y → ℝ} {x : T → ℝ} (h : IsObstructionTest sys i lam x) :
    IsObstructionTest sys i (fun v => -lam v) fun w => -x w := by
  refine ⟨fun v => ?_, fun e => ?_, fun n => ?_, fun u hu => ?_⟩
  · rw [incidence_neg, h.circulation v, neg_zero]
  · rw [dot_neg, dot_neg]
    have := h.structural e
    linarith
  · rw [dot_neg, dot_neg]
    have := h.neutral n
    linarith
  · rw [dot_neg, dot_neg]
    have := h.unilateral u hu
    linarith

omit [Fintype E] [Fintype N] [Fintype U] [Fintype Y] [Fintype V] in
theorem dot_incidenceEntry (sys : OwnerSystem Ω E N U Y T V) (x : T → ℝ)
    (v : V) :
    dot (fun w => incidenceEntry sys.src sys.trans w v) x
      = incidence sys.src sys.trans x v := by
  rw [incidence_eq_sum_mul, dot]
  exact Finset.sum_congr rfl fun w _ => mul_comm _ _

omit [Fintype E] [Fintype N] [Fintype U] [Fintype T] in
theorem dot_zero_left {J : Type*} [Fintype J] (z : J → ℝ) :
    dot (fun _ => (0 : ℝ)) z = 0 := by
  simp [dot]

omit [Fintype E] [Fintype N] [Fintype U] [Fintype V] in
/-- The dual directions of the account cell, masked to owner `i`, are exactly
the obstruction tests: the account block contributes the circulation
equations, the typed blocks the visible lineality equations. -/
theorem isDualDirection_accountCell_iff [DecidableEq Ω]
    (sys : OwnerSystem Ω E N U Y T V) (i : Ω) (lam : Y → ℝ) (x : T → ℝ) :
    IsDualDirection (accountCell sys) (ownerMask sys.cell i) lam x
      ↔ IsObstructionTest sys i lam x := by
  constructor
  · intro h
    refine ⟨fun v => ?_, fun e => h.structural (Sum.inl e), h.neutral,
      fun u hu => ?_⟩
    · have hv := h.structural (Sum.inr v)
      rw [show (accountCell sys).A (Sum.inr v) = fun _ => (0 : ℝ) from rfl,
        dot_zero_left, zero_add] at hv
      rw [show (accountCell sys).R (Sum.inr v)
          = fun w => incidenceEntry sys.src sys.trans w v from rfl,
        dot_incidenceEntry] at hv
      exact hv
    · have hu' := h.unilateral u
      rw [ownerMask_of_eq sys.cell i hu, one_mul] at hu'
      exact hu'
  · intro h
    refine ⟨fun e => ?_, h.neutral, fun u => ?_⟩
    · match e with
      | Sum.inl e => exact h.structural e
      | Sum.inr v =>
        rw [show (accountCell sys).A (Sum.inr v) = fun _ => (0 : ℝ) from rfl,
          dot_zero_left, zero_add,
          show (accountCell sys).R (Sum.inr v)
            = fun w => incidenceEntry sys.src sys.trans w v from rfl,
          dot_incidenceEntry]
        exact h.circulation v
    · by_cases hu : sys.cell.ownerOf u = i
      · rw [ownerMask_of_eq sys.cell i hu, one_mul]
        exact h.unilateral u hu
      · rw [ownerMask_of_ne sys.cell i hu, zero_mul]

omit [Fintype E] [Fintype N] [Fintype U] [Fintype Y] [Fintype V] in
/-- The typed-cell pairing and the flow-module holonomy pairing agree. -/
theorem dot_eq_holonomy (α x : T → ℝ) : dot α x = holonomy α x := by
  rw [dot, holonomy]
  exact Finset.sum_congr rfl fun w _ => mul_comm _ _

/-! #### The duality -/

/-- **The main duality.**  Owner `i` can certify `α` exactly when `α` has
zero holonomy against every obstruction test.  The `←` direction is the
Farkas alternative `mem_signedNormals_iff`. -/
theorem mem_ownerNormals_iff_forall_test [DecidableEq Ω]
    (sys : OwnerSystem Ω E N U Y T V) (i : Ω) (α : T → ℝ) :
    α ∈ ownerNormals sys i
      ↔ ∀ lam x, IsObstructionTest sys i lam x → holonomy α x = 0 := by
  rw [ownerNormals, mem_signedNormals_iff]
  constructor
  · intro h lam x ht
    rw [← dot_eq_holonomy]
    exact h lam x ((isDualDirection_accountCell_iff sys i lam x).mpr ht)
  · intro h lam x hd
    rw [dot_eq_holonomy]
    exact h lam x ((isDualDirection_accountCell_iff sys i lam x).mp hd)

/-- **Zero-class characterization.**  The class of `α` vanishes iff the
ownerwise witnesses glue iff every obstruction test pairs to zero. -/
theorem obstructionClass_eq_zero_iff_forall_test [DecidableEq Ω]
    (sys : OwnerSystem Ω E N U Y T V) (i : Ω) (α : T → ℝ) :
    obstructionClass sys i α = 0
      ↔ ∀ lam x, IsObstructionTest sys i lam x → holonomy α x = 0 := by
  rw [obstructionClass_eq_zero_iff, mem_ownerNormals_iff_forall_test]

/-- A separating obstruction test certifies a nonzero class. -/
theorem obstructionClass_ne_zero_of_test [DecidableEq Ω]
    (sys : OwnerSystem Ω E N U Y T V) (i : Ω) (α : T → ℝ) {lam : Y → ℝ}
    {x : T → ℝ} (ht : IsObstructionTest sys i lam x)
    (hne : holonomy α x ≠ 0) : obstructionClass sys i α ≠ 0 := by
  intro hzero
  exact hne ((obstructionClass_eq_zero_iff_forall_test sys i α).mp hzero lam x ht)

omit [Fintype Y] [Fintype T] in
/-- **The lifting presentation.**  An `i`-typed Bellman lift of
`OwnerTypedDualLifting`, at *any* bound `β`, is in particular a signed
`ownerMask`-masked lift with zero account potential.  Dropping the sign
constraints and the bound is exactly the linearization that turns the typed
dual cone into a subspace. -/
theorem mem_ownerNormals_of_hasTypedLift [DecidableEq Ω]
    (sys : OwnerSystem Ω E N U Y T V) (i : Ω) (α : T → ℝ) (β : ℝ)
    (h : HasTypedLift sys.cell i α β) : α ∈ ownerNormals sys i := by
  obtain ⟨η, ν, μ, hlift⟩ := h
  rw [mem_ownerNormals_iff]
  refine ⟨η, ν, μ, 0, hlift.owner_pure, hlift.internal_cancel, fun w => ?_⟩
  have hw := hlift.boundary_load w
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]
  exact hw

omit [Fintype Y] [Fintype T] in
/-- **Nonzero class kills every typed lift.**  Contrapositive of
`mem_ownerNormals_of_hasTypedLift`: if the class of `α` is nonzero then owner
`i` has no typed Bellman lift of `α`, for any bound.  (The converse is false:
a typed lift also requires sign feasibility and a bound.) -/
theorem not_hasTypedLift_of_obstructionClass_ne_zero [DecidableEq Ω]
    (sys : OwnerSystem Ω E N U Y T V) (i : Ω) (α : T → ℝ)
    (h : obstructionClass sys i α ≠ 0) (β : ℝ) :
    ¬ HasTypedLift sys.cell i α β := fun hlift =>
  h ((obstructionClass_eq_zero_iff sys i α).mpr
    (mem_ownerNormals_of_hasTypedLift sys i α β hlift))

/-- **The computable alternative.**  Either `α` decomposes, or an explicit
obstruction test — a signed circulation lying in owner `i`'s visible
lineality space — separates it with strictly positive holonomy.  Never
both. -/
theorem obstruction_alternative [DecidableEq Ω]
    (sys : OwnerSystem Ω E N U Y T V) (i : Ω) (α : T → ℝ) :
    α ∈ ownerNormals sys i
      ∨ ∃ lam x, IsObstructionTest sys i lam x ∧ 0 < holonomy α x := by
  by_cases hmem : α ∈ ownerNormals sys i
  · exact Or.inl hmem
  · refine Or.inr ?_
    rw [mem_ownerNormals_iff_forall_test] at hmem
    push Not at hmem
    obtain ⟨lam, x, ht, hne⟩ := hmem
    rcases lt_trichotomy (holonomy α x) 0 with hlt | heq | hgt
    · refine ⟨fun v => -lam v, fun w => -x w, ht.neg, ?_⟩
      rw [← dot_eq_holonomy, dot_neg, dot_eq_holonomy]
      linarith
    · exact absurd heq hne
    · exact ⟨lam, x, ht, hgt⟩

/-- The two branches of `obstruction_alternative` are exclusive. -/
theorem not_and_of_obstruction_alternative [DecidableEq Ω]
    (sys : OwnerSystem Ω E N U Y T V) (i : Ω) (α : T → ℝ) :
    ¬ (α ∈ ownerNormals sys i
      ∧ ∃ lam x, IsObstructionTest sys i lam x ∧ 0 < holonomy α x) := by
  rintro ⟨hmem, lam, x, ht, hpos⟩
  have := (mem_ownerNormals_iff_forall_test sys i α).mp hmem lam x ht
  linarith

/-! #### The link with `ZeroHolonomy`, in the direction that holds -/

omit [Fintype E] [Fintype N] [Fintype U] [Fintype V] in
/-- With no typed rows at all, every signed circulation is an obstruction
test: the obstruction space is then the plain coboundary cokernel. -/
theorem isObstructionTest_of_circulation [IsEmpty E]
    [IsEmpty N] [IsEmpty U] (sys : OwnerSystem Ω E N U Y T V) (i : Ω)
    (lam : Y → ℝ) {x : T → ℝ}
    (hx : ∀ v : V, incidence sys.src sys.trans x v = 0) :
    IsObstructionTest sys i lam x :=
  ⟨hx, fun e => isEmptyElim e, fun n => isEmptyElim n, fun u => isEmptyElim u⟩

omit [Fintype Y] [Fintype T] in
/-- With no typed rows the certifiable subspace is exactly the space of exact
account bridges of `OrientedAccountBridge`: the class of a charge cochain
vanishes iff that cochain is an exact coboundary of the flow system.  This
pins the object down as the coboundary cokernel, whose dual is the full
*signed* cycle space — strictly larger than the nonnegative circulation cone
tested by `ZeroHolonomy`. -/
theorem obstructionClass_eq_zero_iff_exists_isExactBridge [DecidableEq Ω]
    [IsEmpty E] [IsEmpty N] [IsEmpty U] (sys : OwnerSystem Ω E N U Y T V)
    (i : Ω) (α : T → ℝ) :
    obstructionClass sys i α = 0
      ↔ ∃ H : V → ℝ,
          OrientedAccountBridge.IsExactBridge sys.src sys.trans α H := by
  rw [obstructionClass_eq_zero_iff, mem_ownerNormals_iff]
  constructor
  · rintro ⟨η, ν, μ, H, -, -, hbnd⟩
    refine ⟨H, fun w => ?_⟩
    have h := hbnd w
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at h
    linarith
  · rintro ⟨H, hH⟩
    refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, H, fun u _ => rfl, fun v => ?_,
      fun w => ?_⟩
    · simp
    · have h := hH w
      simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add]
      linarith

/-- **The inclusion that holds.**  A vanishing class forces the gluing
condition `OwnerLabeledFlowHolonomy.ZeroHolonomy`, provided every circulation
extends to an obstruction test (automatic when there are no typed rows, by
`isObstructionTest_of_circulation`).  The converse fails; see
`ParallelRowsCounterexample`. -/
theorem zeroHolonomy_of_obstructionClass_eq_zero [DecidableEq Ω]
    (sys : OwnerSystem Ω E N U Y T V) (i : Ω) (α : T → ℝ)
    (hclass : obstructionClass sys i α = 0)
    (hext : ∀ x, IsCirculation sys.src sys.trans x
      → ∃ lam, IsObstructionTest sys i lam x) :
    ZeroHolonomy sys.src sys.trans α := by
  intro x hx
  obtain ⟨lam, ht⟩ := hext x hx
  exact le_of_eq
    ((obstructionClass_eq_zero_iff_forall_test sys i α).mp hclass lam x ht)

/-! #### The single-owner sanity theorem -/

omit [Fintype E] [Fintype N] [Fintype U] [Fintype Y] [Fintype T] [Fintype V]
  [DecidableEq V] in
theorem ownerMask_eq_one_of_subsingleton [DecidableEq Ω] [Subsingleton Ω]
    (P : TypedCell Ω E N U Y T) (i : Ω) : ownerMask P i = fun _ => 1 := by
  funext u
  exact ownerMask_of_eq P i (Subsingleton.elim _ _)

omit [Fintype Y] [Fintype T] in
/-- **Required sanity theorem.**  With a single owner, ownerwise certification
*is* global certification: the owner-`i` subspace and the global subspace
coincide, so the owner-obstruction cokernel carries no owner-splitting
information at all. -/
theorem ownerNormals_eq_globalNormals_of_subsingleton [DecidableEq Ω]
    [Subsingleton Ω] (sys : OwnerSystem Ω E N U Y T V) (i : Ω) :
    ownerNormals sys i = globalNormals sys := by
  rw [ownerNormals, globalNormals, ownerMask_eq_one_of_subsingleton]

omit [Fintype Y] [Fintype T] in
/-- **Required sanity theorem, class form.**  With a single owner every
globally certifiable normal has zero class: there is nothing left to glue. -/
theorem obstructionClass_eq_zero_of_subsingleton [DecidableEq Ω]
    [Subsingleton Ω] (sys : OwnerSystem Ω E N U Y T V) (i : Ω) {α : T → ℝ}
    (h : α ∈ globalNormals sys) : obstructionClass sys i α = 0 := by
  rw [obstructionClass_eq_zero_iff, ownerNormals_eq_globalNormals_of_subsingleton]
  exact h

omit [Fintype Y] [Fintype T] in
/-- Owner-`i` certification is always at most global certification. -/
theorem ownerNormals_le_globalNormals [DecidableEq Ω]
    (sys : OwnerSystem Ω E N U Y T V) (i : Ω) :
    ownerNormals sys i ≤ globalNormals sys := by
  rintro α ⟨η, ν, μ, hlift⟩
  refine ⟨η, ν, fun u => ownerMask sys.cell i u * μ u, ⟨fun v => ?_, fun w => ?_⟩⟩
  · have h := hlift.internal_cancel v
    simp only [internalLoad, rowLoad] at h ⊢
    have hm : (fun u => (1 : ℝ) * (ownerMask sys.cell i u * μ u))
        = fun u => ownerMask sys.cell i u * μ u := by
      funext u; ring
    rw [hm]
    exact h
  · have h := hlift.boundary_load w
    simp only [boundaryLoad, rowLoad] at h ⊢
    have hm : (fun u => (1 : ℝ) * (ownerMask sys.cell i u * μ u))
        = fun u => ownerMask sys.cell i u * μ u := by
      funext u; ring
    rw [hm]
    exact h

omit [Fintype Y] [Fintype T] in
/-- If everything is globally certifiable and there is a single owner, the
obstruction cokernel is literally the zero space. -/
theorem subsingleton_obstruction_of_subsingleton [DecidableEq Ω]
    [Subsingleton Ω] (sys : OwnerSystem Ω E N U Y T V) (i : Ω)
    (h : globalNormals sys = ⊤) : Subsingleton (Obstruction sys i) := by
  have hi : ownerNormals sys i = ⊤ := by
    rw [ownerNormals_eq_globalNormals_of_subsingleton, h]
  rw [show Obstruction sys i = ((T → ℝ) ⧸ ownerNormals sys i) from rfl, hi]
  infer_instance

end OwnerLayer

/-! ### The typed cell with no rows

Instantiating the typed blocks by `Empty` leaves only the account block, so
`ownerNormals` becomes the plain coboundary space of the flow system and
`IsObstructionTest` becomes the plain signed cycle space.  This is the
setting in which the obstruction cokernel is directly comparable with
`OwnerLabeledFlowHolonomy.ZeroHolonomy`. -/

/-- The typed cell with no structural, neutral or unilateral rows. -/
def emptyCell (Ω Y T : Type*) : TypedCell Ω Empty Empty Empty Y T where
  ownerOf := fun u => u.elim
  A := fun e => e.elim
  R := fun e => e.elim
  b := fun e => e.elim
  C := fun n => n.elim
  Q := fun n => n.elim
  c := fun n => n.elim
  B := fun u => u.elim
  S := fun u => u.elim
  d := fun u => u.elim

/-! ### Vacuity probe: the zero system

One owner, no typed rows, one vertex, one target coordinate and a transition
that returns to the unique vertex.  Every account coboundary vanishes, so the
certifiable subspace is `⊥` and the class map is injective: the definitions
are not vacuously trivial. -/

namespace TrivialSystem

/-- The zero system. -/
def system : OwnerSystem Unit Empty Empty Empty Unit Unit Unit where
  cell := emptyCell Unit Unit Unit
  src := fun _ => ()
  trans := fun _ _ => 1

/-- The account drift of the zero system is identically zero. -/
theorem drift_eq_zero (H : Unit → ℝ) (w : Unit) :
    H (system.src w) - ∑ v, system.trans w v * H v = 0 := by
  simp [system]

/-- **Vacuity probe.**  The certifiable subspace of the zero system is `⊥`. -/
theorem ownerNormals_eq_bot : ownerNormals system () = ⊥ := by
  refine le_antisymm (fun α hα => ?_) bot_le
  rw [Submodule.mem_bot]
  rw [mem_ownerNormals_iff] at hα
  obtain ⟨η, ν, μ, H, -, -, hbnd⟩ := hα
  funext w
  have h := hbnd w
  have h1 : (∑ e, η e * system.cell.R e w) = 0 := by simp
  have h2 : (∑ n, ν n * system.cell.Q n w) = 0 := by simp
  have h3 : (∑ u, μ u * system.cell.S u w) = 0 := by simp
  rw [h1, h2, h3, drift_eq_zero] at h
  simpa using h.symm

/-- **Vacuity probe, class form.**  On the zero system a class vanishes only
for the zero normal, so the cokernel is the whole normal space. -/
theorem obstructionClass_eq_zero_iff_eq_zero (α : Unit → ℝ) :
    obstructionClass system () α = 0 ↔ α = 0 := by
  rw [obstructionClass_eq_zero_iff, ownerNormals_eq_bot, Submodule.mem_bot]

end TrivialSystem

/-! ### Falsifier (a): the two-row owner-switching cycle

The Question 71 falsifier of `OwnerLabeledFlowHolonomy.TwoCycle`, recomputed
as a class computation.  Every owner-pure circulation vanishes there
(`TwoCycle.ownerPure_circulation_eq_zero`), yet the mixed uniform circulation
is a legitimate obstruction test and separates the charge cochain. -/

namespace TwoCycleObstruction

/-- The two-row owner-switching cycle as an owner-labeled system, with no
typed rows: the obstruction space is the cokernel of the account coboundary
map. -/
def system : OwnerSystem Bool Empty Empty Empty Unit Bool Bool where
  cell := emptyCell Bool Unit Bool
  src := TwoCycle.src
  trans := TwoCycle.transition

/-- The uniform occupation `(1/2, 1/2)` is a genuine circulation. -/
theorem isCirculation_uniform :
    IsCirculation system.src system.trans TwoCycle.uniform :=
  TwoCycle.isNormalizedCirculation_uniform.toIsCirculation

/-- The uniform occupation is an obstruction test for either owner. -/
theorem isObstructionTest_uniform (i : Bool) :
    IsObstructionTest system i 0 TwoCycle.uniform :=
  isObstructionTest_of_circulation system i 0 isCirculation_uniform.balanced

/-- **Falsifier (a), acceptance test.**  As soon as the two row charges have
positive sum, the class of the charge cochain is nonzero, and the explicit
separating vector is the uniform circulation. -/
theorem obstructionClass_ne_zero (i : Bool) {a₁ a₂ : ℝ} (h : 0 < a₁ + a₂) :
    obstructionClass system i (TwoCycle.charge a₁ a₂) ≠ 0 := by
  refine obstructionClass_ne_zero_of_test system i _
    (isObstructionTest_uniform i) ?_
  rw [TwoCycle.holonomy_uniform]
  linarith

/-- The same failure in the flow module's language: the gluing condition
fails too, consistently with `zeroHolonomy_of_obstructionClass_eq_zero`. -/
theorem not_zeroHolonomy {a₁ a₂ : ℝ} (h : 0 < a₁ + a₂) :
    ¬ ZeroHolonomy system.src system.trans (TwoCycle.charge a₁ a₂) :=
  TwoCycle.not_zeroHolonomy h

/-- Positive probe: a charge cochain that *is* an account coboundary has zero
class.  Here `(1, -1)` is the drift of the potential `(1, 0)`. -/
theorem obstructionClass_coboundary_eq_zero (i : Bool) :
    obstructionClass system i (fun r => if r then -1 else 1) = 0 := by
  rw [obstructionClass_eq_zero_iff, mem_ownerNormals_iff]
  refine ⟨fun e => e.elim, fun n => n.elim, fun u => u.elim,
    (fun v => if v then 0 else 1), fun u => u.elim, fun v => ?_, fun w => ?_⟩
  · simp
  · cases w <;>
      norm_num [system, TwoCycle.src, TwoCycle.transition, Fintype.sum_bool]

end TwoCycleObstruction

/-! ### Falsifier (b): cross-owner incidence cancellation

The Question 72 falsifier of `OwnerTypedDualLifting.CrossOwnerCancellation`,
recomputed as a class computation.  The flow structure is the one-vertex
self-loop, so every account coboundary vanishes and the obstruction is purely
one of typed liftability: the escape direction, which owner `i`'s custody map
cannot see, is a nonnegative circulation separating the cross-owner
normal. -/

namespace CrossOwnerObstruction

/-- The cross-owner cancellation cell with the trivial one-vertex flow. -/
def system : OwnerSystem Bool Empty Unit Bool Unit Bool Unit where
  cell := CrossOwnerCancellation.system
  src := fun _ => ()
  trans := fun _ _ => 1

theorem incidence_escape (i : Bool) (v : Unit) :
    incidence system.src system.trans (CrossOwnerCancellation.escape i) v
      = 0 := by
  simp [incidence, system]

/-- The escape direction is a genuine nonnegative circulation. -/
theorem isCirculation_escape (i : Bool) :
    IsCirculation system.src system.trans (CrossOwnerCancellation.escape i) :=
  ⟨fun r => by
      simp only [CrossOwnerCancellation.escape]
      split_ifs <;> norm_num,
    incidence_escape i⟩

/-- The escape direction is an obstruction test for owner `i`: it is a
circulation, it satisfies the owner-neutral row homogeneously, and it is
invisible to owner `i`'s own unilateral row — exactly
`CrossOwnerCancellation.custody_escape`. -/
theorem isObstructionTest_escape (i : Bool) :
    IsObstructionTest system i 0 (CrossOwnerCancellation.escape i) := by
  have hc : system.cell = CrossOwnerCancellation.system := rfl
  refine ⟨incidence_escape i, fun e => e.elim, fun n => ?_, fun u hu => ?_⟩
  · rw [show n = () from rfl, hc, CrossOwnerCancellation.dot_C,
      CrossOwnerCancellation.dot_Q]
    simp
  · have hui : u = i := hu
    subst hui
    rw [hc, CrossOwnerCancellation.dot_B, CrossOwnerCancellation.dot_S]
    simp [CrossOwnerCancellation.escape]

/-- **Falsifier (b), acceptance test.**  The cross-owner normal
`t false + t true` has a nonzero class for *either* owner, separated by the
explicit owner-invisible escape circulation. -/
theorem obstructionClass_ne_zero (i : Bool) :
    obstructionClass system i CrossOwnerCancellation.crossNormal ≠ 0 := by
  refine obstructionClass_ne_zero_of_test system i _
    (isObstructionTest_escape i) ?_
  rw [← dot_eq_holonomy, CrossOwnerCancellation.dot_crossNormal_escape]
  norm_num

/-- **The class computation recovers the Question 72 falsifier.**  The
no-typed-lift statement is *derived* here from the nonzero class, rather than
quoted: a nonzero class kills every typed lift at every bound. -/
theorem not_hasTypedLift_of_class (i : Bool) (β : ℝ) :
    ¬ HasTypedLift CrossOwnerCancellation.system i
      CrossOwnerCancellation.crossNormal β :=
  not_hasTypedLift_of_obstructionClass_ne_zero system i _
    (obstructionClass_ne_zero i) β

/-- The class computation and the lifting presentation agree: the cross-owner
normal is valid on the full typed system, has no typed lift for any owner and
any bound, and has a nonzero owner-obstruction class for every owner. -/
theorem validOnFull_and_no_lift_and_nonzero_class :
    ValidOnFull CrossOwnerCancellation.system
        CrossOwnerCancellation.crossNormal 0
      ∧ ∀ i : Bool, (∀ β : ℝ, ¬ HasTypedLift CrossOwnerCancellation.system i
          CrossOwnerCancellation.crossNormal β)
        ∧ obstructionClass system i CrossOwnerCancellation.crossNormal ≠ 0 :=
  ⟨CrossOwnerCancellation.validOnFull, fun i =>
    ⟨fun β => CrossOwnerCancellation.not_hasTypedLift i β,
      obstructionClass_ne_zero i⟩⟩

/-- Positive probe: owner `false`'s own visible coordinate does have a typed
lift (`CrossOwnerCancellation.hasTypedLift_ownNormal`), and correspondingly
its class vanishes — weight `1` on the owner-neutral row and `1` on owner
`false`'s own row cancels the internal variable within one owner. -/
theorem obstructionClass_ownNormal_eq_zero :
    obstructionClass system false (CrossOwnerCancellation.ownNormal false)
      = 0 := by
  rw [obstructionClass_eq_zero_iff, mem_ownerNormals_iff]
  refine ⟨fun e => e.elim, fun _ => 1, (fun u => if u then 0 else 1),
    fun _ => 0, fun u hu => ?_, fun v => ?_, fun w => ?_⟩
  · cases u
    · exact absurd rfl hu
    · norm_num
  · simp [system, CrossOwnerCancellation.system]
  · cases w <;>
      simp [system, CrossOwnerCancellation.system,
        CrossOwnerCancellation.ownNormal]

end CrossOwnerObstruction

/-! ### The converse of the `ZeroHolonomy` comparison fails

The parallel-rows system of `OrientedAccountBridge`: two rows leaving the
same vertex, nothing ever returning.  The *only* circulation is `0`, so
`ZeroHolonomy` holds for every charge; but the signed cycle space is a line,
and the charge cochain pairs nontrivially with it, so its class is nonzero.
The obstruction cokernel is dual to the whole *signed* cycle space, while
`ZeroHolonomy` only tests the nonnegative cone.  There is a single owner
here, so this is not an owner-splitting failure. -/

namespace ParallelRowsCounterexample

open Math.LinearAlgebra.OrientedAccountBridge

/-- The parallel-rows system with one owner and no typed rows. -/
def system : OwnerSystem Unit Empty Empty Empty Unit Bool Bool where
  cell := emptyCell Unit Unit Bool
  src := ParallelRows.src
  trans := ParallelRows.transition

/-- The signed cycle `(1, -1)`.  It is *not* nonnegative, hence not a
circulation, but it is a perfectly good obstruction test. -/
def signedCycle : Bool → ℝ := fun r => if r then -1 else 1

theorem incidence_signedCycle (v : Bool) :
    incidence system.src system.trans signedCycle v = 0 := by
  cases v <;>
    norm_num [incidence, system, ParallelRows.src, ParallelRows.transition,
      signedCycle, Fintype.sum_bool]

theorem isObstructionTest_signedCycle :
    IsObstructionTest system () 0 signedCycle :=
  isObstructionTest_of_circulation system () 0 incidence_signedCycle

/-- **The counterexample.**  `ZeroHolonomy` holds for the charge cochain — the
only circulation is `0` — yet its obstruction class is nonzero, separated by
the signed cycle `(1, -1)`.  So `ZeroHolonomy` does **not** imply a vanishing
class; only the converse implication
`zeroHolonomy_of_obstructionClass_eq_zero` holds. -/
theorem zeroHolonomy_and_obstructionClass_ne_zero :
    ZeroHolonomy system.src system.trans ParallelRows.charge
      ∧ obstructionClass system () ParallelRows.charge ≠ 0 := by
  refine ⟨ParallelRows.zeroHolonomy_any _, ?_⟩
  refine obstructionClass_ne_zero_of_test system () _
    isObstructionTest_signedCycle ?_
  rw [holonomy]
  norm_num [signedCycle, ParallelRows.charge, Fintype.sum_bool]

/-- Sharper reading of the counterexample: with a single owner the owner-`i`
subspace *is* the global subspace, so the charge is missed even by the global
certificate space.  The gap is between signed and nonnegative cycles, not
between owners. -/
theorem not_mem_globalNormals : ParallelRows.charge ∉ globalNormals system := by
  rw [← ownerNormals_eq_globalNormals_of_subsingleton system ()]
  intro h
  exact zeroHolonomy_and_obstructionClass_ne_zero.2
    ((obstructionClass_eq_zero_iff system () _).mpr h)

/-- Positive probe: the constant normal is the account coboundary of the
potential `(1, 0)`, so its class does vanish.  The cokernel is not the whole
space. -/
theorem obstructionClass_const_eq_zero :
    obstructionClass system () (fun _ => 1) = 0 := by
  rw [obstructionClass_eq_zero_iff, mem_ownerNormals_iff]
  refine ⟨fun e => e.elim, fun n => n.elim, fun u => u.elim,
    (fun v => if v then 0 else 1), fun u => u.elim, fun v => ?_, fun w => ?_⟩
  · simp
  · norm_num [system, ParallelRows.src, ParallelRows.transition,
      Fintype.sum_bool]

end ParallelRowsCounterexample

end

end OwnerObstructionCokernel
end LinearAlgebra
end Math
