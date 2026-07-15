/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic

/-!
# Weighted incidence and the degree-one cut/cycle decomposition

The **degree-one fragment of combinatorial Hodge theory** over an abstract
finite weighted incidence structure (a directed multigraph with positive edge
weights). Searchable vocabulary: *Helmholtz decomposition*, *graph Laplacian*,
*cut space* / *cycle space*.

Given finite node and edge types `A`, `E` with `src tgt : E → A` and positive
weights `wt : E → ℝ`, this file builds the two degree-one maps
`grad : (A → ℝ) →ₗ (E → ℝ)` and its `wt`-adjoint `div : (E → ℝ) →ₗ (A → ℝ)`,
and proves the orthogonal splitting
`(E → ℝ) = range grad ⊕ ker div` (`range_grad_isCompl_ker_div`): the cut space
`range grad` and the cycle (divergence-free) space `ker div` are complementary.
A **reversal section** adds an edge-reversing involution and the alternating
subspace it cuts out, showing the split restricts to alternating flows — this
is the shape the game-theoretic flow decomposition consumes.

A cochain-complex development — orientations, the next coboundary `d₁`,
`d ∘ d = 0`, curl adjoints over higher cells — is deliberately **out of scope**;
this module is degree-one by declaration and a higher-degree Hodge theory would
extend it rather than reuse it as-is.
-/

open Finset BigOperators

namespace Math.LinearAlgebra.WeightedIncidence

variable {A E : Type} [Fintype A] [Fintype E] [DecidableEq A]
  (src tgt : E → A) (wt : E → ℝ)

/-! ### The incidence coefficient, gradient and divergence -/

/-- Signed incidence coefficient of edge `e` at node `a`: `+1` when `a` is the
target of `e`, `-1` when `a` is its source, `0` otherwise. -/
def incidence (e : E) (a : A) : ℝ :=
  (if a = tgt e then 1 else 0) - (if a = src e then 1 else 0)

/-- The gradient (degree-zero coboundary) `C⁰ → C¹`:
`(grad φ) e = φ (tgt e) − φ (src e)`. -/
def grad : (A → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun φ := fun e => φ (tgt e) - φ (src e)
  map_add' φ ψ := by funext e; simp only [Pi.add_apply]; ring
  map_smul' c φ := by funext e; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

omit [Fintype A] [Fintype E] [DecidableEq A] in
@[simp] lemma grad_apply (φ : A → ℝ) (e : E) :
    grad src tgt φ e = φ (tgt e) - φ (src e) := rfl

/-- The weighted divergence (the `wt`-adjoint of `grad`) `C¹ → C⁰`:
`(div X) a = ∑ e, incidence e a * wt e * X e`, a signed weighted incidence sum
at each node (inflow minus outflow). -/
def div : (E → ℝ) →ₗ[ℝ] (A → ℝ) where
  toFun X := fun a => ∑ e, incidence src tgt e a * (wt e * X e)
  map_add' X Y := by
    funext a
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring

omit [Fintype A] in
@[simp] lemma div_apply (X : E → ℝ) (a : A) :
    div src tgt wt X a = ∑ e, incidence src tgt e a * (wt e * X e) := rfl

/-! ### Inner products and the adjointness specification -/

/-- The `wt`-weighted inner product on edge functions `⟪X, Y⟫_wt = ∑ e, wt e * X e * Y e`. -/
def edgeInner (X Y : E → ℝ) : ℝ := ∑ e, wt e * X e * Y e

/-- The plain inner product on node functions `⟪φ, ψ⟫ = ∑ a, φ a * ψ a`. -/
def nodeInner (φ ψ : A → ℝ) : ℝ := ∑ a, φ a * ψ a

omit [Fintype E] in
/-- The gradient as a weighted incidence sum: `(grad φ) e = ∑ a, incidence e a * φ a`. -/
lemma grad_eq_sum_incidence (φ : A → ℝ) (e : E) :
    grad src tgt φ e = ∑ a, incidence src tgt e a * φ a := by
  simp only [grad_apply, incidence, sub_mul, one_mul, ite_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Divergence is the `wt`-adjoint of the gradient**: the specification lemma
`⟪grad φ, X⟫_wt = ⟪φ, div X⟫`. Every property of `div` used below flows from this. -/
theorem div_isAdjoint_grad (φ : A → ℝ) (X : E → ℝ) :
    edgeInner wt (grad src tgt φ) X = nodeInner φ (div src tgt wt X) := by
  simp only [edgeInner, nodeInner, div_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [grad_eq_sum_incidence, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-! ### The edge form is positive definite -/

/-- The `wt`-weighted inner product packaged as a bilinear form on `E → ℝ`. -/
def edgeBilin : LinearMap.BilinForm ℝ (E → ℝ) :=
  LinearMap.mk₂ ℝ (fun X Y => ∑ e, wt e * X e * Y e)
    (fun X X' Y => by
      simp only [Pi.add_apply]; rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun e _ => by ring)
    (fun c X Y => by
      simp only [Pi.smul_apply, smul_eq_mul]; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring)
    (fun X Y Y' => by
      simp only [Pi.add_apply]; rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun e _ => by ring)
    (fun c X Y => by
      simp only [Pi.smul_apply, smul_eq_mul]; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring)

@[simp] lemma edgeBilin_apply (X Y : E → ℝ) :
    edgeBilin wt X Y = edgeInner wt X Y := rfl

omit [Fintype A] [DecidableEq A] in
/-- The edge form is reflexive (indeed symmetric). -/
lemma edgeBilin_isRefl : (edgeBilin wt).IsRefl := by
  intro X Y h
  rw [edgeBilin_apply, edgeInner] at h ⊢
  rw [← h]
  exact Finset.sum_congr rfl fun e _ => by ring

omit [Fintype A] [DecidableEq A] in
/-- Positive definiteness: a nonzero edge function has positive self-inner-product,
so `⟪X, X⟫_wt = 0` forces `X = 0`. -/
lemma eq_zero_of_edgeInner_self_eq_zero (hwt : ∀ e, 0 < wt e) {X : E → ℝ}
    (h : edgeInner wt X X = 0) : X = 0 := by
  rw [edgeInner] at h
  have hnn : ∀ e ∈ (Finset.univ : Finset E), 0 ≤ wt e * X e * X e := fun e _ => by
    rw [mul_assoc]; exact mul_nonneg (hwt e).le (mul_self_nonneg _)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
  funext e
  have he := hz e (Finset.mem_univ e)
  rw [mul_assoc] at he
  exact mul_self_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (ne_of_gt (hwt e)))

omit [Fintype E] [DecidableEq A] in
/-- The node inner product is positive definite too. -/
lemma eq_zero_of_nodeInner_self_eq_zero {ψ : A → ℝ} (h : nodeInner ψ ψ = 0) : ψ = 0 := by
  rw [nodeInner] at h
  have hnn : ∀ a ∈ (Finset.univ : Finset A), 0 ≤ ψ a * ψ a := fun a _ => mul_self_nonneg _
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
  funext a
  exact mul_self_eq_zero.mp (hz a (Finset.mem_univ a))

/-! ### The cut/cycle orthogonal splitting -/

omit [Fintype A] in
/-- The divergence-free (cycle) space is exactly the `wt`-orthogonal complement of
the cut space `range grad`. The adjointness `div_isAdjoint_grad` and the
nondegeneracy of the node inner product are all that is used. -/
theorem ker_div_eq_orthogonal [Finite A] :
    LinearMap.ker (div src tgt wt)
      = (edgeBilin wt).orthogonal (LinearMap.range (grad src tgt)) := by
  letI : Fintype A := Fintype.ofFinite A
  ext Y
  rw [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hY X hX
    obtain ⟨φ, rfl⟩ := hX
    rw [edgeBilin_apply, div_isAdjoint_grad, hY]
    simp [nodeInner]
  · intro h
    have hkey : ∀ φ, nodeInner φ (div src tgt wt Y) = 0 := fun φ => by
      have hφ := h (grad src tgt φ) (LinearMap.mem_range_self _ φ)
      rwa [edgeBilin_apply, div_isAdjoint_grad] at hφ
    exact eq_zero_of_nodeInner_self_eq_zero (hkey (div src tgt wt Y))

omit [Fintype A] in
/-- Disjointness of the cut and cycle spaces: a divergence-free gradient flow has
zero self-inner-product, hence vanishes. -/
theorem disjoint_range_grad_ker_div [Finite A] (hwt : ∀ e, 0 < wt e) :
    Disjoint (LinearMap.range (grad src tgt)) (LinearMap.ker (div src tgt wt)) := by
  letI : Fintype A := Fintype.ofFinite A
  rw [Submodule.disjoint_def]
  intro X hX hXk
  obtain ⟨φ, rfl⟩ := hX
  rw [LinearMap.mem_ker] at hXk
  refine eq_zero_of_edgeInner_self_eq_zero wt hwt ?_
  rw [div_isAdjoint_grad, hXk]
  simp [nodeInner]

omit [Fintype A] in
/-- **Cut/cycle decomposition** (degree-one Helmholtz/Hodge split): the cut space
`range grad` and the cycle space `ker div` are `wt`-orthogonal complements, so
`(E → ℝ) = range grad ⊕ ker div`. -/
theorem range_grad_isCompl_ker_div [Finite A] (hwt : ∀ e, 0 < wt e) :
    IsCompl (LinearMap.range (grad src tgt)) (LinearMap.ker (div src tgt wt)) := by
  rw [ker_div_eq_orthogonal src tgt wt]
  refine LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (edgeBilin_isRefl wt) ?_
  refine LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal (edgeBilin wt)
    (edgeBilin_isRefl wt) ?_
  rw [← ker_div_eq_orthogonal src tgt wt]
  exact disjoint_range_grad_ker_div src tgt wt hwt

omit [Fintype A] in
/-- The unique cut/cycle decomposition of any edge function: every `X` is uniquely
a cut component `p ∈ range grad` plus a divergence-free residual `X - p ∈ ker div`. -/
theorem exists_unique_grad_add_ker_div [Finite A] (hwt : ∀ e, 0 < wt e) (X : E → ℝ) :
    ∃! p : E → ℝ,
      p ∈ LinearMap.range (grad src tgt) ∧ X - p ∈ LinearMap.ker (div src tgt wt) := by
  obtain ⟨u, v, huv, huniq⟩ :=
    Submodule.existsUnique_add_of_isCompl (range_grad_isCompl_ker_div src tgt wt hwt) X
  refine ⟨(u : E → ℝ), ⟨u.2, ?_⟩, ?_⟩
  · have hxu : X - (u : E → ℝ) = (v : E → ℝ) := by rw [← huv]; abel
    rw [hxu]; exact v.2
  · rintro p ⟨hp, hpk⟩
    obtain ⟨h1, -⟩ := huniq ⟨p, hp⟩ ⟨X - p, hpk⟩ (by simp)
    exact congrArg Subtype.val h1

/-! ### Reversal and alternating flows

An edge-reversing involution `rev` (with `src`, `tgt`, `wt` reversal-symmetric)
carves out the **alternating** flows `X (rev e) = − X e`. Gradients are
alternating and the cut/cycle split restricts to this subspace — the shape the
game-theoretic flow decomposition consumes (one directed edge per unilateral
deviation, its reversal the opposite deviation). -/

variable (rev : E → E) (hrev : Function.Involutive rev)
  (hsrc : ∀ e, src (rev e) = tgt e) (htgt : ∀ e, tgt (rev e) = src e)
  (hwt_rev : ∀ e, wt (rev e) = wt e)

/-- The submodule of flows that negate under edge reversal: `X (rev e) = − X e`. -/
def AlternatingFlow : Submodule ℝ (E → ℝ) where
  carrier := {X | ∀ e, X (rev e) = - X e}
  add_mem' {X Y} hX hY e := by simp only [Pi.add_apply, hX e, hY e]; ring
  zero_mem' e := by simp
  smul_mem' c X hX e := by simp only [Pi.smul_apply, smul_eq_mul, hX e]; ring

omit [Fintype A] [Fintype E] [DecidableEq A] in
@[simp] lemma mem_alternatingFlow {X : E → ℝ} :
    X ∈ AlternatingFlow rev ↔ ∀ e, X (rev e) = - X e := Iff.rfl

omit [Fintype A] [Fintype E] [DecidableEq A] in
include hsrc htgt in
/-- Every gradient flow is alternating. -/
lemma grad_mem_alternatingFlow (φ : A → ℝ) : grad src tgt φ ∈ AlternatingFlow rev := by
  intro e
  simp only [grad_apply, hsrc e, htgt e]
  ring

omit [Fintype A] [Fintype E] [DecidableEq A] in
include hsrc htgt in
/-- The cut space sits inside the alternating flows. -/
lemma range_grad_le_alternatingFlow :
    LinearMap.range (grad src tgt) ≤ AlternatingFlow rev := by
  rintro X ⟨φ, rfl⟩
  exact grad_mem_alternatingFlow src tgt rev hsrc htgt φ

omit [Fintype A] in
include hrev hsrc hwt_rev in
/-- **Divergence on an alternating flow** collapses to a single orientation:
`(div X) a = 2 · ∑ e, [tgt e = a] · wt e · X e`, twice the weighted inflow. The
outflow term equals the negated inflow after reindexing by the reversal. -/
lemma div_apply_of_mem_alternatingFlow {X : E → ℝ} (hX : X ∈ AlternatingFlow rev) (a : A) :
    div src tgt wt X a = 2 * ∑ e, (if a = tgt e then wt e * X e else 0) := by
  have hXe : ∀ e, X (rev e) = - X e := hX
  rw [div_apply]
  have hsplit : ∀ e, incidence src tgt e a * (wt e * X e)
      = (if a = tgt e then wt e * X e else 0) - (if a = src e then wt e * X e else 0) :=
    fun e => by simp only [incidence, sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_congr rfl (fun e _ => hsplit e), Finset.sum_sub_distrib]
  have hout : (∑ e, if a = src e then wt e * X e else 0)
      = -(∑ e, if a = tgt e then wt e * X e else 0) := by
    rw [← Equiv.sum_comp hrev.toPerm (fun e => if a = src e then wt e * X e else 0),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Function.Involutive.coe_toPerm, hsrc e, hwt_rev e, hXe e]
    split_ifs <;> ring
  rw [hout]; ring

omit [Fintype A] in
/-- Disjointness restricts to the alternating flows. -/
theorem alternatingFlow_disjoint [Finite A] (hwt : ∀ e, 0 < wt e) :
    Disjoint (LinearMap.range (grad src tgt))
      (LinearMap.ker (div src tgt wt) ⊓ AlternatingFlow rev) :=
  (disjoint_range_grad_ker_div src tgt wt hwt).mono_right inf_le_left

omit [Fintype A] in
include hsrc htgt in
/-- **The cut/cycle split restricts to the alternating flows**: within
`AlternatingFlow`, the cut space `range grad` and the alternating divergence-free
flows `ker div ⊓ AlternatingFlow` sum to the whole alternating subspace. Together
with `alternatingFlow_disjoint` this is the unique decomposition on `AlternatingFlow`. -/
theorem alternatingFlow_sup [Finite A] (hwt : ∀ e, 0 < wt e) :
    LinearMap.range (grad src tgt) ⊔ (LinearMap.ker (div src tgt wt) ⊓ AlternatingFlow rev)
      = AlternatingFlow rev := by
  rw [← sup_inf_assoc_of_le _ (range_grad_le_alternatingFlow src tgt rev hsrc htgt),
    (range_grad_isCompl_ker_div src tgt wt hwt).sup_eq_top, top_inf_eq]

/-! ### Sanity example: the directed 3-cycle

Nodes `Fin 3`, six directed edges `Fin 3 × Bool` (`b = false`: forward `k → k+1`;
`b = true`: its reversal `k+1 → k`), uniform weights. A compile-time certificate
of the sign conventions: a gradient flow is nonzero, the cyclic rotation flow is
divergence-free (a nonzero cycle), and the two are `wt`-orthogonal — as the
decomposition demands. -/

namespace TriangleExample

/-- Source map: forward edge `k → k+1`, reverse edge `k+1 → k`. -/
def triSrc : Fin 3 × Bool → Fin 3 := fun p => if p.2 then p.1 + 1 else p.1
/-- Target map. -/
def triTgt : Fin 3 × Bool → Fin 3 := fun p => if p.2 then p.1 else p.1 + 1
/-- Edge reversal: flip the orientation bit. -/
def triRev : Fin 3 × Bool → Fin 3 × Bool := fun p => (p.1, !p.2)
/-- Uniform edge weights. -/
def triWt : Fin 3 × Bool → ℝ := fun _ => 1
/-- A potential `0, 1, 2` on the three nodes; its gradient is a nonzero cut flow. -/
def triPot : Fin 3 → ℝ := fun i => (i.val : ℝ)
/-- The cyclic rotation flow: `+1` on forward edges, `−1` on reverse edges. -/
def triRot : Fin 3 × Bool → ℝ := fun p => if p.2 then -1 else 1

example : Function.Involutive triRev := fun p => by simp [triRev]

example : ∀ e, 0 < triWt e := fun _ => one_pos

/-- The gradient of `triPot` is a nonzero cut flow. -/
example : grad triSrc triTgt triPot ≠ 0 := by
  intro h
  have hval := congrFun h (0, false)
  simp [grad_apply, triSrc, triTgt, triPot] at hval

/-- The cyclic rotation is divergence-free: a genuine cycle flow. -/
example : div triSrc triTgt triWt triRot = 0 := by
  funext a
  fin_cases a <;>
    simp [div_apply, incidence, triSrc, triTgt, triWt, triRot,
      Fintype.sum_prod_type, Fin.sum_univ_three]

/-- The cut flow and the cycle flow are `wt`-orthogonal — the decomposition is
orthogonal, and the signs are consistent. -/
example : edgeInner triWt (grad triSrc triTgt triPot) triRot = 0 := by
  simp [edgeInner, grad_apply, triSrc, triTgt, triWt, triRot, triPot,
    Fintype.sum_prod_type, Fin.sum_univ_three]
  norm_num

end TriangleExample

end Math.LinearAlgebra.WeightedIncidence
