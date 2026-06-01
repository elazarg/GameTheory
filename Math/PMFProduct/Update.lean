/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Math.ProbabilityMassFunction
import Math.Reindex
import Math.PMFProduct.Conditioning

namespace Math
namespace PMFProduct

open scoped BigOperators
open Math.ProbabilityMassFunction

universe uι uA uα uβ uγ

set_option autoImplicit false


-- ============================================================================
-- Family Update Lemmas
-- ============================================================================

section UpdateLemmas

variable {ι : Type uι} [DecidableEq ι]
variable {A : ι → Type uA}
variable {β : Type uβ}

open Classical in
/-- Folding coordinate updates along a nodup list rewrites exactly those
    coordinates (and leaves all others unchanged). -/
lemma foldl_update_family_eq_of_nodup
    (l : List ι) (hNodup : l.Nodup)
    (σ τ : ∀ i, PMF (A i)) :
    l.foldl (fun fam j => Function.update fam j (τ j)) σ
      = fun i => if i ∈ l then τ i else σ i := by
  induction l generalizing σ with
  | nil =>
      simp
  | cons j rest ih =>
      have hNodupRest : rest.Nodup := List.Nodup.of_cons hNodup
      simp only [List.foldl]
      -- rewrite fold over `rest` with updated base family
      rw [ih (σ := Function.update σ j (τ j)) hNodupRest]
      funext i
      by_cases hi : i = j
      · subst hi
        simp
      · simp [List.mem_cons, hi]

open Classical in
@[simp] lemma update_family_same (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j)) :
    (Function.update σ j τ) j = τ := by
  simp [Function.update]

open Classical in
@[simp] lemma update_family_other (σ : ∀ i, PMF (A i)) {i j : ι}
    (τ : PMF (A j)) (h : i ≠ j) :
    (Function.update σ j τ) i = σ i := by
  simp [Function.update, h]

variable [Fintype ι]

open Classical in
/-- Pointwise: updating the *factor family* at `j` only changes that coordinate's factor. -/
@[simp] lemma pmfPi_apply_update_family (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j))
    (s : ∀ i, A i) :
    pmfPi (A := A) (Function.update σ j τ) s
      =
    (τ (s j)) * (∏ i ∈ Finset.univ.erase j, σ i (s i)) := by
  classical
  simp only [pmfPi_apply]
  rw [prod_factor_erase (fun i x => (Function.update σ j τ) i x) j s]
  congr 1
  · simp [Function.update]
  · apply Finset.prod_congr rfl; intro i hi
    simp [Function.update, Finset.ne_of_mem_erase hi]

open Classical in
/-- A robust, division-free form: cross-multiplication of the updated and original products. -/
lemma pmfPi_update_family_mul (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j))
    (s : ∀ i, A i) :
    pmfPi (A := A) (Function.update σ j τ) s * σ j (s j)
      =
    pmfPi (A := A) σ s * τ (s j) := by
  rw [pmfPi_apply_update_family, pmfPi_apply, prod_factor_erase (fun i x => σ i x) j s]
  -- LHS: (τ (s j) * rest) * σ j (s j)
  -- RHS: (σ j (s j) * rest) * τ (s j)
  simp [mul_comm, mul_left_comm]

open Classical in
/-- The product PMF with one component replaced by a mixture `d` equals the mixture of
    products with that component set to pure values. This is the "Fubini" identity for `pmfPi`. -/
theorem pmfPi_update_bind (σ : ∀ i, PMF (A i)) (j : ι) (d : PMF (A j)) :
    pmfPi (A := A) (Function.update σ j d) =
      d.bind (fun a => pmfPi (A := A) (Function.update σ j (PMF.pure a))) := by
  ext s
  simp only [PMF.bind_apply, pmfPi_apply_update_family, PMF.pure_apply]
  rw [tsum_eq_single (s j)]
  · simp
  · intro b hb; simp [Ne.symm hb]

variable [∀ i, Fintype (A i)]

omit [∀ i, Fintype (A i)] in
/-- When `f` ignores coordinate `j`, the bind of a deterministic
    product (with `pure a` at `j`) through `f` is independent of `a`.
    This is the core step for marginalizing an irrelevant coordinate. -/
theorem pmfPi_bind_update_pure_eq_of_ignores [∀ i, Finite (A i)]
    (σ : ∀ i, PMF (A i)) (j : ι) (a a' : A j)
    {β : Type*}
    (f : (∀ i, A i) → PMF β)
    (hf : Ignores j f) :
    (pmfPi (Function.update σ j (PMF.pure a))).bind f =
      (pmfPi (Function.update σ j (PMF.pure a'))).bind f := by
  classical
  letI : DecidableEq (A j) := Classical.decEq (A j)
  ext t
  simp only [PMF.bind_apply, pmfPi_apply_update_family, PMF.pure_apply]
  -- Swap at coordinate `j` and identity elsewhere; involutive since `Equiv.swap` is.
  let e : (∀ i, A i) → (∀ i, A i) := fun acts i =>
    if h : i = j then h ▸ Equiv.swap a a' (acts j) else acts i
  have he : Function.Involutive e := by
    intro acts; ext i
    by_cases hi : i = j
    · subst hi; simp [e]
    · simp [e, hi]
  rw [← Math.Reindex.tsum_eq_tsum_of_involutive e he]
  -- Show the summands match pointwise after the swap.
  refine tsum_congr fun acts => ?_
  have hej : e acts j = Equiv.swap a a' (acts j) := by simp [e]
  have hene : ∀ i, i ≠ j → e acts i = acts i := fun i hi => by simp [e, hi]
  have heupd : e acts = Function.update acts j (Equiv.swap a a' (acts j)) := by
    ext i; by_cases hi : i = j
    · subst hi; simp [hej]
    · rw [hene i hi]; simp [hi]
  have hfeq : f (e acts) = f acts := by rw [heupd]; exact hf acts _
  have hprod : (∏ i ∈ Finset.univ.erase j, (σ i) (e acts i)) =
      ∏ i ∈ Finset.univ.erase j, (σ i) (acts i) :=
    Finset.prod_congr rfl fun i hi => by rw [hene i (Finset.ne_of_mem_erase hi)]
  rw [hej, hprod, hfeq]
  -- Final: ite (swap(acts j) = a) * ... = ite (acts j = a') * ...
  congr 1; congr 1
  by_cases h : acts j = a
  · simp [h, Equiv.swap_apply_left, eq_comm]
  · by_cases h' : acts j = a'
    · simp [h', Equiv.swap_apply_right]
    · simp [h, h', Equiv.swap_apply_of_ne_of_ne h h']

omit [∀ i, Fintype (A i)] in
/-- If `f` ignores coordinate `j`, then `(pmfPi σ).bind f` is
    independent of `σ j`. That is, updating `σ j` does not change
    the expected value of `f` under the product. -/
theorem pmfPi_bind_ignores_coord [∀ i, Finite (A i)]
    (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j))
    {β : Type*}
    (f : (∀ i, A i) → PMF β)
    (hf : Ignores j f) :
    (pmfPi (Function.update σ j τ)).bind f =
      (pmfPi σ).bind f := by
  -- Decompose both sides via pmfPi_update_bind
  rw [pmfPi_update_bind, PMF.bind_bind]
  conv_rhs =>
    rw [show σ = Function.update σ j (σ j) from by
      ext i x; by_cases h : i = j
      · subst h; simp
      · simp [Function.update_of_ne h]]
    rw [pmfPi_update_bind, PMF.bind_bind]
  -- Both: d.bind g where g a = pmfPi(update σ j (pure a)).bind f
  -- g is constant by `pmfPi_bind_update_pure_eq_of_ignores`, so d doesn't matter.
  -- Pick a₀ from τ's support (PMF is nonempty).
  obtain ⟨a₀, _⟩ := τ.support_nonempty
  have hconst : ∀ a,
      (pmfPi (Function.update σ j (PMF.pure a))).bind f =
      (pmfPi (Function.update σ j (PMF.pure a₀))).bind f :=
    fun a => pmfPi_bind_update_pure_eq_of_ignores σ j a a₀ f hf
  simp_rw [hconst]; simp [PMF.bind_const]

omit [∀ i, Fintype (A i)] in
/-- Repeated coordinate updates do not change `pmfPi.bind f` when `f`
    ignores every updated coordinate.

    This is a list-iterated form of `pmfPi_bind_ignores_coord`, useful when
    many coordinates are rewritten one-by-one. -/
theorem pmfPi_bind_ignores_coord_list [∀ i, Finite (A i)]
    (σ τ : ∀ i, PMF (A i))
    {β : Type*}
    (f : (∀ i, A i) → PMF β)
    (l : List ι)
    (hNodup : l.Nodup)
    (hf : ∀ j, j ∈ l → Ignores j f) :
    (pmfPi (l.foldl (fun fam j => Function.update fam j (τ j)) σ)).bind f =
      (pmfPi σ).bind f := by
  induction l generalizing σ with
  | nil =>
      simp
  | cons j rest ih =>
      have hNodupRest : rest.Nodup := List.Nodup.of_cons hNodup
      have hfj : Ignores j f := hf j (by simp)
      have hfRest : ∀ k, k ∈ rest → Ignores k f := by
        intro k hk
        exact hf k (by simp [hk])
      simp only [List.foldl]
      calc
        (pmfPi (rest.foldl (fun fam j => Function.update fam j (τ j))
            (Function.update σ j (τ j)))).bind f
            =
          (pmfPi (Function.update σ j (τ j))).bind f := by
              exact ih (σ := Function.update σ j (τ j)) hNodupRest hfRest
        _ = (pmfPi σ).bind f := pmfPi_bind_ignores_coord σ j (τ j) f hfj

omit [∀ i, Fintype (A i)] in
/-- Finset wrapper for `pmfPi_bind_ignores_coord_list`. -/
theorem pmfPi_bind_ignores_coord_finset [∀ i, Finite (A i)]
    (σ τ : ∀ i, PMF (A i))
    {β : Type*}
    (f : (∀ i, A i) → PMF β)
    (J : Finset ι)
    (hf : ∀ j, j ∈ J → Ignores j f) :
    (pmfPi ((J.toList).foldl (fun fam j => Function.update fam j (τ j)) σ)).bind f =
      (pmfPi σ).bind f := by
  refine pmfPi_bind_ignores_coord_list σ τ f J.toList J.nodup_toList ?_
  intro j hj
  exact hf j ((Finset.mem_toList.mp hj))

omit [∀ i, Fintype (A i)] in
/-- If a continuation ignores every coordinate, binding it under any product PMF
    collapses to the same constant PMF value. -/
theorem pmfPi_bind_eq_of_forall_ignores [∀ i, Finite (A i)]
    (σ : ∀ i, PMF (A i))
    {β : Type*}
    (g : (∀ i, A i) → PMF β)
    (hg : ∀ j, Ignores j g)
    (s0 : ∀ i, A i) :
    (pmfPi σ).bind g = g s0 := by
  let τ : ∀ i, PMF (A i) := fun i => PMF.pure (s0 i)
  have hfold :
      (Finset.univ.toList.foldl
          (fun fam j => Function.update fam j (τ j)) σ) = τ := by
    have htmp := foldl_update_family_eq_of_nodup
      (l := Finset.univ.toList) (σ := σ) (τ := τ) (Finset.univ.nodup_toList)
    calc
      (Finset.univ.toList.foldl (fun fam j => Function.update fam j (τ j)) σ)
          = (fun i => if i ∈ Finset.univ.toList then τ i else σ i) := htmp
      _ = τ := by
          funext i
          simp
  have hbind :
      (pmfPi τ).bind g = (pmfPi σ).bind g := by
    have h := pmfPi_bind_ignores_coord_finset (σ := σ) (τ := τ)
      (f := g) (J := Finset.univ) (hf := fun j _ => hg j)
    simpa [hfold] using h
  calc
    (pmfPi σ).bind g = (pmfPi τ).bind g := hbind.symm
    _ = g s0 := by simp [τ, pmfPi_pure]

omit [∀ i, Fintype (A i)] in
/-- "Fresh bind" corollary: if `g` ignores every coordinate, then
    integrating `g` against any product PMF equals evaluating `g` at an
    assignment chosen from each factor's support. -/
theorem pmfPi_bind_comm_fresh_support [∀ i, Finite (A i)]
    (σ : ∀ i, PMF (A i))
    {β : Type*}
    (g : (∀ i, A i) → PMF β)
    (hg : ∀ j, Ignores j g) :
    (pmfPi σ).bind g = g (fun i => (σ i).support_nonempty.choose) :=
  pmfPi_bind_eq_of_forall_ignores (σ := σ) (g := g) hg
    (fun i => (σ i).support_nonempty.choose)

omit [∀ i, Fintype (A i)] in
/-- Arbitrary-point variant of `pmfPi_bind_comm_fresh_support`. -/
theorem pmfPi_bind_comm_fresh [∀ i, Finite (A i)]
    (σ : ∀ i, PMF (A i))
    {β : Type*}
    (g : (∀ i, A i) → PMF β)
    (hg : ∀ j, Ignores j g)
    [∀ i, Nonempty (A i)] :
    (pmfPi σ).bind g = g (fun i => Classical.arbitrary (A i)) :=
  pmfPi_bind_eq_of_forall_ignores (σ := σ) (g := g) hg
    (fun i => Classical.arbitrary (A i))

omit [∀ i, Fintype (A i)] in
/-- Binding a product PMF with a function-dependent coordinate update equals the
    product with that component replaced by the pushforward. -/
theorem pmfPi_bind_update_map
    (σ : ∀ i, PMF (A i)) (j : ι) (f : A j → A j) :
    (pmfPi σ).bind (fun s => PMF.pure (Function.update s j (f (s j)))) =
      pmfPi (Function.update σ j (PMF.map f (σ j))) := by
  classical
  let g : ∀ i, A i → A i := fun i =>
    if h : i = j then h ▸ f else id
  have hpush := pmfPi_push_coordwise (A := A) (B := A) σ g
  have hmap :
      (fun s : ∀ i, A i => (fun i => g i (s i))) =
        fun s => Function.update s j (f (s j)) := by
    funext s i
    by_cases hi : i = j
    · subst hi
      simp [g]
    · rw [Function.update_of_ne hi]
      simp [g, hi]
  have hfamily :
      (fun i => pushforward (σ i) (g i)) =
        Function.update σ j (PMF.map f (σ j)) := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp [g, pushforward]
    · have hg : g i = id := by
        simp [g, hi]
      rw [Function.update_of_ne hi, hg, pushforward, PMF.map_id]
  rw [show (pmfPi σ).bind (fun s => PMF.pure (Function.update s j (f (s j)))) =
      PMF.map (fun s => Function.update s j (f (s j))) (pmfPi σ) from
        PMF.bind_pure_comp (fun s => Function.update s j (f (s j))) (pmfPi σ)]
  simpa [hmap, hfamily] using hpush

omit [∀ i, Fintype (A i)] in
/-- Binding a product PMF with a constant coordinate update equals the product
    with that component replaced by a point mass. Special case of
    `pmfPi_bind_update_map` with `f = fun _ => x`. -/
theorem pmfPi_bind_update_pure
    (σ : ∀ i, PMF (A i)) (j : ι) (x : A j) :
    (pmfPi σ).bind (fun s => PMF.pure (Function.update s j x)) =
      pmfPi (Function.update σ j (PMF.pure x)) := by
  have h := pmfPi_bind_update_map σ j (Function.const _ x)
  simp only [PMF.map_const] at h; exact h

end UpdateLemmas

-- ============================================================================
-- Conditioning on Coordinates & Mass Invariance
-- ============================================================================

section ConditioningCoord

variable {ι : Type uι} [Fintype ι]
variable {A : ι → Type uA} [∀ i, Fintype (A i)]

open Classical in
omit [∀ i, Fintype (A i)] in
/-- Other marginals are unchanged after conditioning on a coordinate. -/
theorem pmfPi_cond_coord_other_marginal
    [∀ i, Finite (A i)]
    (σ : ∀ i, PMF (A i)) {j q : ι} (hq : q ≠ j)
    (E : A j → Prop)
    (hE : pmfMass (μ := σ j) E ≠ 0) :
    pushforward
      (pmfCond (μ := pmfPi (A := A) σ) (fun s => E (s j))
        (by simpa [pmfMass_pmfPi_coord (A := A) (σ := σ) (j := j) (E := E)] using hE))
      (fun s => s q)
      =
    σ q := by
  exact pmfPi_cond_coord_push_other σ hq E hE

-- ---- Cross-multiplication & mass invariance ------------------------------

open Classical in
/-- The ratio of an event's mass is invariant under updating coordinate `j`,
    provided the event ignores coordinate `j`. -/
theorem pmfPi_event_ratio_invariant_of_ignores
    (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j))
    (Num Denom : (∀ i, A i) → Prop)
    (hNum_ign : Ignores (A := A) j Num)
    (hDenom_ign : Ignores (A := A) j Denom) :
    (∑ s, if Num s then pmfPi (A := A) (Function.update σ j τ) s else 0)
      * (∑ s, if Denom s then pmfPi (A := A) σ s else 0)
      =
    (∑ s, if Num s then pmfPi (A := A) σ s else 0)
      * (∑ s, if Denom s then pmfPi (A := A) (Function.update σ j τ) s else 0) := by
  let W : (∀ i, A i) × (∀ i, A i) → ENNReal := fun p =>
    (if Num p.1 then pmfPi (A := A) (Function.update σ j τ) p.1 else 0) *
    (if Denom p.2 then pmfPi (A := A) σ p.2 else 0)
  let W_CD : (∀ i, A i) × (∀ i, A i) → ENNReal := fun p =>
    (if Num p.1 then pmfPi (A := A) σ p.1 else 0) *
    (if Denom p.2 then pmfPi (A := A) (Function.update σ j τ) p.2 else 0)
  -- The swap bijection
  let e : (∀ i, A i) × (∀ i, A i) → (∀ i, A i) × (∀ i, A i) :=
    fun p => (update (A := A) p.1 j (p.2 j), update (A := A) p.2 j (p.1 j))
  have he : Function.Involutive e := by
    intro ⟨s1, s2⟩
    dsimp [e]
    congr 1
    · ext i; by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
    · ext i; by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
  have hW : ∀ p, W (e p) = W_CD p := by
    intro ⟨s1, s2⟩
    dsimp only [W, W_CD, e]
    -- The events ignore j, so the conditions match.
    have hNum_eq : Num (update (A := A) s1 j (s2 j)) = Num s1 := by
      simpa [update] using (hNum_ign s1 (s2 j))
    have hDen_eq : Denom (update (A := A) s2 j (s1 j)) = Denom s2 := by
      simpa [update] using (hDenom_ign s2 (s1 j))
    simp_rw [hNum_eq, hDen_eq]
    have h1 : pmfPi (A := A) (Function.update σ j τ) (update (A := A) s1 j (s2 j))
              = τ (s2 j) * ∏ i ∈ Finset.univ.erase j, σ i (s1 i) := by
      rw [pmfPi_apply_update_family]
      congr 1
      · simp
      · apply Finset.prod_congr rfl; intro i hi
        simp [Finset.ne_of_mem_erase hi]
    have h2 : pmfPi (A := A) σ (update (A := A) s2 j (s1 j)) = σ j (s1 j)
              * ∏ i ∈ Finset.univ.erase j, σ i (s2 i) := by
      rw [pmfPi_apply, prod_factor_erase (fun i x => σ i x) j
        (update (A := A) s2 j (s1 j))]
      congr 1
      · simp
      · apply Finset.prod_congr rfl; intro i hi
        simp [Finset.ne_of_mem_erase hi]
    have h3 : pmfPi (A := A) σ s1 = σ j (s1 j) * ∏ i ∈ Finset.univ.erase j, σ i (s1 i) := by
      rw [pmfPi_apply, prod_factor_erase (fun i x => σ i x) j s1]
    have h4 : pmfPi (A := A) (Function.update σ j τ) s2 = τ (s2 j)
              * ∏ i ∈ Finset.univ.erase j, σ i (s2 i) := by
      rw [pmfPi_apply_update_family]
    -- Substitute all evaluations back into the equality
    rw [h1, h2, h3, h4]
    -- Push the if-statements and sort the commutative factors
    by_cases hN : Num s1 <;> by_cases hD : Denom s2
    · simp only [hN, hD, ↓reduceIte]
      simp only [mul_comm, mul_left_comm]
    · simp [hN, hD]
    · simp [hN, hD]
    · simp [hN, hD]
  -- Finally, thread the double sum through the bijection
  calc (∑ s, if Num s then pmfPi (A := A) (Function.update σ j τ) s else 0)
     * (∑ s, if Denom s then pmfPi (A := A) σ s else 0)
    _ = ∑ s1, ∑ s2, (if Num s1 then pmfPi (A := A) (Function.update σ j τ) s1 else 0)
      * (if Denom s2 then pmfPi (A := A) σ s2 else 0) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro s1 _
        rw [Finset.mul_sum]
    _ = ∑ p : (∀ i, A i) × (∀ i, A i), W p := (Fintype.sum_prod_type W).symm
    _ = ∑ p : (∀ i, A i) × (∀ i, A i), W (e p) :=
        (Math.Reindex.sum_univ_eq_sum_univ_of_involutive e he W).symm
    _ = ∑ p : (∀ i, A i) × (∀ i, A i), W_CD p := by
        apply Finset.sum_congr rfl; intro p _
        exact hW p
    _ = ∑ s1, ∑ s2, W_CD (s1, s2) := Fintype.sum_prod_type W_CD
    _ = (∑ s, if Num s then pmfPi (A := A) σ s else 0)
      * (∑ s, if Denom s then pmfPi (A := A) (Function.update σ j τ) s else 0) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro s1 _
        rw [Finset.mul_sum]

omit [∀ i, Fintype (A i)] in
open Classical in
/-- Mass is invariant under updating coordinate `j`, if the event ignores `j`. -/
theorem pmfPi_mass_invariant_of_ignores [∀ i, Finite (A i)]
    (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j))
    (P : (∀ i, A i) → Prop)
    (hP : Ignores (A := A) j P) :
    pmfMass (μ := pmfPi (A := A) (Function.update σ j τ)) P
      =
    pmfMass (μ := pmfPi (A := A) σ) P := by
  classical
  letI (i : ι) : Fintype (A i) := Fintype.ofFinite (A i)
  have h :=
    pmfPi_event_ratio_invariant_of_ignores
      (A := A) (σ := σ) (j := j) (τ := τ)
      (Num := P) (Denom := (fun _ : (∀ i, A i) => True))
      (hNum_ign := hP)
      (hDenom_ign := (by intro s a; rfl))
  -- h : mU * mass(True under old) = mO * mass(True under updated)
  -- rewrite both True-masses to 1, then simp
  have h' :
      pmfMass (μ := pmfPi (A := A) (Function.update σ j τ)) P * 1
        =
      pmfMass (μ := pmfPi (A := A) σ) P * 1 := by
    -- first rewrite the two True-masses in `h` to `1`
    have hT_old :
        (∑ s : (∀ i, A i), if (fun _ => True) s then (pmfPi (A := A) σ) s else 0) = 1 := by
      simpa using (sum_coe_fintype (pmfPi (A := A) σ))
    have hT_upd :
        (∑ s : (∀ i, A i),
          if (fun _ => True) s
          then (pmfPi (A := A) (Function.update σ j τ)) s else 0) = 1 := by
      simpa using (sum_coe_fintype (pmfPi (A := A) (Function.update σ j τ)))
    -- now `simp` actually has concrete rewrite rules for those factors
    simp_all only [pmfMass, pmfMask, tsum_fintype, pmfPi_apply, ↓reduceIte, mul_one]
  simpa [mul_one] using h'

omit [∀ i, Fintype (A i)] in
open Classical in
/-- Conditional probability (ratio of masses) is invariant under updating coordinate `j`,
    provided both events ignore `j` and the denominator has nonzero mass. -/
theorem pmfPi_cond_prob_invariant_of_ignores [∀ i, Finite (A i)]
    (σ : ∀ i, PMF (A i)) (j : ι) (τ : PMF (A j))
    (Num Denom : (∀ i, A i) → Prop)
    (hNum : Ignores (A := A) j Num)
    (hDen : Ignores (A := A) j Denom)
    (hDO : pmfMass (μ := pmfPi (A := A) σ) Denom ≠ 0) :
    (pmfMass (μ := pmfPi (A := A) (Function.update σ j τ)) Num)
     / (pmfMass (μ := pmfPi (A := A) (Function.update σ j τ)) Denom)
      =
    (pmfMass (μ := pmfPi (A := A) σ) Num) /
      (pmfMass (μ := pmfPi (A := A) σ) Denom) := by
  classical
  letI (i : ι) : Fintype (A i) := Fintype.ofFinite (A i)
  -- abbreviate the four masses
  set mNU : ENNReal := pmfMass (μ := pmfPi (A := A) (Function.update σ j τ)) Num
  set mDU : ENNReal := pmfMass (μ := pmfPi (A := A) (Function.update σ j τ)) Denom
  set mNO : ENNReal := pmfMass (μ := pmfPi (A := A) σ) Num
  set mDO : ENNReal := pmfMass (μ := pmfPi (A := A) σ) Denom
  have hDU : mDU ≠ 0 := by
    have hm := pmfPi_mass_invariant_of_ignores
      (A := A) (σ := σ) (j := j) (τ := τ) (P := Denom) hDen
    simpa [mDU, hm] using hDO
  have hcross :
      mNU * mDO = mNO * mDU := by
    -- your cross-multiplication lemma, just unfolded
    simpa [mNU, mDU, mNO, mDO, pmfMass, pmfMask, tsum_fintype]
      using
        (pmfPi_event_ratio_invariant_of_ignores
          (A := A) (σ := σ) (j := j) (τ := τ)
          (Num := Num) (Denom := Denom) hNum hDen)
  -- non-top facts (needed for ENNReal.mul_inv_cancel)
  have hDO_top : mDO ≠ (⊤ : ENNReal) := by
    simpa [mDO] using pmfMass_ne_top (μ := pmfPi (A := A) σ) Denom
  have hDU_top : mDU ≠ (⊤ : ENNReal) := by
    simpa [mDU] using
      pmfMass_ne_top (μ := pmfPi (A := A) (Function.update σ j τ)) Denom
  have : mNU * mDU⁻¹ = mNO * mDO⁻¹ := by
    -- Step 1: cancel mDU on the RHS of hcross
    have h1 : (mNU * mDO) * mDU⁻¹ = mNO := by
      have := congrArg (fun x => x * mDU⁻¹) hcross
      -- RHS: (mNO * mDU) * mDU⁻¹ = mNO * (mDU * mDU⁻¹) = mNO
      -- LHS stays as (mNU * mDO) * mDU⁻¹
      simpa [mul_assoc, mul_left_comm, mul_comm,
        ENNReal.mul_inv_cancel hDU hDU_top] using this
    -- Step 2: multiply by mDO⁻¹ and cancel mDO on the LHS
    have h2 : ((mNU * mDO) * mDU⁻¹) * mDO⁻¹ = mNO * mDO⁻¹ := by
      exact congrArg (fun x => x * mDO⁻¹) h1
    -- Reassociate/commute: ((mNU*mDO)*mDU⁻¹)*mDO⁻¹ = (mNU*mDU⁻¹)*(mDO*mDO⁻¹) = mNU*mDU⁻¹
    have : mNU * mDU⁻¹ = mNO * mDO⁻¹ := by
      have h3 :
          ((mNU * mDO) * mDU⁻¹) * mDO⁻¹ = mNU * mDU⁻¹ := by
        calc
          ((mNU * mDO) * mDU⁻¹) * mDO⁻¹
              = (mNU * mDU⁻¹) * (mDO * mDO⁻¹) := by
                  ac_rfl
          _ = (mNU * mDU⁻¹) * 1 := by
                  simp [ENNReal.mul_inv_cancel hDO hDO_top]
          _ = mNU * mDU⁻¹ := by simp
      -- now rewrite h2 using h3
      simpa [h3] using h2
    exact this
  -- rewrite / as * inv
  simpa [div_eq_mul_inv, mNU, mDU, mNO, mDO] using this

end ConditioningCoord

end PMFProduct

end Math
