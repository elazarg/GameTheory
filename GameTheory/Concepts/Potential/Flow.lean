/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.WeightedIncidence
import GameTheory.Basic

/-!
# The unilateral flow of a finite game

The **flow layer** of the Candogan–Menache–Ozdaglar–Parrilo decomposition
(*Flows and Decompositions of Games: Harmonic and Potential Games*,
Math. Oper. Res. 2011). A finite game with fixed strategy sets is a utility
vector `u : (∀ i, S i) → Payoff ι`; its **unilateral flow** records, along each
edge of the **game graph** (nodes are strategy profiles, edges single-player
deviations), the deviating player's own utility difference.

This file:

- `flow` — the ambient triple-indexed flow, `u (update σ i s') i − u σ i`;
- `GameEdge` — directed unilateral edges excluding self-deviations, with the
  reversal involution `edgeRev` (the opposite deviation), a `Fintype` instance,
  and reversal-symmetric endpoints;
- `flowLinear` — the flow as a linear map into edge functions, landing in the
  `AlternatingFlow` subspace of the weighted-incidence spine;
- `NonstrategicSpace` — the kernel of `flowLinear` (utilities unmoved by a
  player's own unilateral deviation, equivalently depending only on opponents);
- `NormalizedSpace` and `normalize` — the per-context zero-mean condition and
  the projection onto it, giving `IsCompl NormalizedSpace NonstrategicSpace` and
  the linear equivalence `flowNormalizedEquiv` with the range of `flowLinear`;
- `flow_curl_free` — within any fiber the flow telescopes around triangles.

Coalition data, divergence/harmonicity, the component spaces, and the bridge to
equilibrium concepts live in later files; this one imports only the incidence
spine and the shared payoff vocabulary.
-/

open Finset BigOperators
open Math.LinearAlgebra.WeightedIncidence

namespace GameTheory.FlowDecomposition

variable {ι : Type} [DecidableEq ι] {S : ι → Type}

/-! ### The ambient flow -/

/-- The **unilateral flow**: what player `i` gains at profile `σ` by unilaterally
switching to `s'`. This is the edge value on the game graph of Candogan et al. -/
def flow (u : (∀ i, S i) → Payoff ι) (σ : ∀ i, S i) (i : ι) (s' : S i) : ℝ :=
  u (Function.update σ i s') i - u σ i

/-! ### The game edge space -/

/-- A directed **unilateral edge** of the game graph: a base profile `base`, a
deviating `player`, and a new strategy `dev` for that player, distinct from the
one played at `base` (self-deviations are excluded). -/
structure GameEdge (S : ι → Type) where
  /-- The source profile. -/
  base : ∀ i, S i
  /-- The deviating player. -/
  player : ι
  /-- The deviating player's new strategy. -/
  dev : S player
  /-- Self-deviations are excluded. -/
  dev_ne : dev ≠ base player

/-- The source profile of an edge. -/
def edgeSrc (e : GameEdge S) : ∀ i, S i := e.base

/-- The target profile of an edge: the base with the deviating player's strategy
replaced by `dev`. -/
def edgeTgt (e : GameEdge S) : ∀ i, S i := Function.update e.base e.player e.dev

/-- Edge reversal: the opposite deviation, from `edgeTgt e` back to `e.base` by
the same player. -/
def edgeRev (e : GameEdge S) : GameEdge S where
  base := Function.update e.base e.player e.dev
  player := e.player
  dev := e.base e.player
  dev_ne := by rw [Function.update_self]; exact e.dev_ne.symm

/-- The underlying equivalence to the nested-sigma form, used only to transport
the `Fintype` instance. -/
def edgeEquivSigma :
    GameEdge S ≃ Σ (σ : ∀ i, S i) (i : ι), {s' : S i // s' ≠ σ i} where
  toFun e := ⟨e.base, e.player, e.dev, e.dev_ne⟩
  invFun e := ⟨e.1, e.2.1, e.2.2.1, e.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype ι] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] :
    Fintype (GameEdge S) :=
  Fintype.ofEquiv _ edgeEquivSigma.symm

@[simp] lemma edgeSrc_edgeRev (e : GameEdge S) : edgeSrc (edgeRev e) = edgeTgt e := rfl

@[simp] lemma edgeTgt_edgeRev (e : GameEdge S) : edgeTgt (edgeRev e) = edgeSrc e := by
  simp only [edgeTgt, edgeRev, edgeSrc, Function.update_idem, Function.update_eq_self]

theorem edgeRev_involutive : Function.Involutive (edgeRev (S := S)) := by
  intro e
  obtain ⟨base, player, dev, dev_ne⟩ := e
  simp only [edgeRev, Function.update_idem, Function.update_eq_self, Function.update_self]

/-! ### The flow as an edge function -/

/-- The unilateral flow as a linear map from games to edge functions:
`flowLinear u e` is the deviating player's gain along `e`. -/
def flowLinear : ((∀ i, S i) → Payoff ι) →ₗ[ℝ] (GameEdge S → ℝ) where
  toFun u := fun e => flow u e.base e.player e.dev
  map_add' u v := by funext e; simp only [flow, Pi.add_apply]; ring
  map_smul' c u := by
    funext e; simp only [flow, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] lemma flowLinear_apply (u : (∀ i, S i) → Payoff ι) (e : GameEdge S) :
    flowLinear u e = flow u e.base e.player e.dev := rfl

/-- The flow of a game is an **alternating** edge function: reversing an edge
negates the flow, because the deviating player is preserved by reversal. -/
theorem flowLinear_mem_alternatingFlow (u : (∀ i, S i) → Payoff ι) :
    flowLinear u ∈ AlternatingFlow (edgeRev (S := S)) := by
  rw [mem_alternatingFlow]
  rintro ⟨σ, i, s', hs'⟩
  simp only [flowLinear_apply, edgeRev, flow, Function.update_idem, Function.update_eq_self]
  ring

/-! ### The nonstrategic subspace -/

/-- The **nonstrategic subspace**: games whose each player's utility is unchanged
by that player's own unilateral deviation (equivalently, depends only on the
opponents' strategies). It is the kernel of `flowLinear`. -/
def NonstrategicSpace : Submodule ℝ ((∀ i, S i) → Payoff ι) where
  carrier := {u | ∀ (σ : ∀ i, S i) (i : ι) (s' : S i), u (Function.update σ i s') i = u σ i}
  add_mem' {u v} hu hv σ i s' := by simp only [Pi.add_apply, hu σ i s', hv σ i s']
  zero_mem' σ i s' := rfl
  smul_mem' c u hu σ i s' := by simp only [Pi.smul_apply, smul_eq_mul, hu σ i s']

theorem mem_nonstrategicSpace_iff_flowLinear_eq_zero (u : (∀ i, S i) → Payoff ι) :
    u ∈ NonstrategicSpace ↔ flowLinear u = 0 := by
  constructor
  · intro hu
    funext e
    obtain ⟨σ, i, s', hs'⟩ := e
    simp only [flowLinear_apply, flow, Pi.zero_apply, hu σ i s', sub_self]
  · intro hu σ i s'
    rcases eq_or_ne s' (σ i) with h | h
    · rw [h, Function.update_eq_self]
    · have hz := congrFun hu ⟨σ, i, s', h⟩
      simp only [flowLinear_apply, flow, Pi.zero_apply] at hz
      linarith

/-! ### Curl-freeness -/

/-- Two profiles are **unilaterally adjacent** when they differ in exactly one
coordinate: they disagree, but agree off a single player. These are the edges of
the game graph. -/
def Adjacent (σ τ : ∀ i, S i) : Prop := σ ≠ τ ∧ ∃ i, ∀ j, j ≠ i → σ j = τ j

omit [DecidableEq ι] in
/-- **All triangles of the game graph lie within one player's fiber.** Three
pairwise unilaterally-adjacent profiles differ only in one common coordinate `i`;
in particular the middle profile is another strategy of player `i` at the same
context. This is why the flow's curl is entirely within-fiber (`flow_curl_free`). -/
theorem adjacent_triangle_same_player {σ τ ρ : ∀ i, S i}
    (hστ : Adjacent σ τ) (hτρ : Adjacent τ ρ) (hσρ : Adjacent σ ρ) :
    ∃ i, (∀ j, j ≠ i → σ j = τ j) ∧ (∀ j, j ≠ i → τ j = ρ j) ∧
      (∀ j, j ≠ i → σ j = ρ j) := by
  obtain ⟨hστ_ne, a, ha⟩ := hστ
  obtain ⟨hτρ_ne, b, hb⟩ := hτρ
  obtain ⟨_, c, hc⟩ := hσρ
  have diff : ∀ {μ ν : ∀ i, S i} {x : ι}, μ ≠ ν → (∀ j, j ≠ x → μ j = ν j) → μ x ≠ ν x := by
    intro μ ν x hne hoff h
    exact hne (funext fun j => by rcases eq_or_ne j x with rfl | hj; exacts [h, hoff j hj])
  have hab : a = b := by
    by_contra hne
    have h1 : σ a ≠ ρ a := (hb a hne) ▸ diff hστ_ne ha
    have h2 : σ b ≠ ρ b := by
      have hd := diff hτρ_ne hb
      rwa [← ha b (Ne.symm hne)] at hd
    have hac : a = c := not_ne_iff.mp fun h => h1 (hc a h)
    have hbc : b = c := not_ne_iff.mp fun h => h2 (hc b h)
    exact hne (hac.trans hbc.symm)
  exact ⟨a, ha, fun j hj => hb j (hab ▸ hj), fun j hj => (ha j hj).trans (hb j (hab ▸ hj))⟩

/-- **Curl-freeness (within-fiber telescoping).** All triangles of the game graph
lie within a single player's fiber, and there the flow telescopes: the gain from
`s'` equals the gain to `t'` plus the gain from `t'` to `s'`. Summed around the
triangle `σ → t' → s' → σ` the flow is zero. -/
theorem flow_curl_free (u : (∀ i, S i) → Payoff ι) (σ : ∀ i, S i) (i : ι) (s' t' : S i) :
    flow u σ i s' = flow u σ i t' + flow u (Function.update σ i t') i s' := by
  simp only [flow, Function.update_idem]
  ring

/-! ### The normalized subspace and its representative -/

section Normalized

variable [∀ i, Fintype (S i)]

/-- The **normalized subspace**: games with per-context zero mean — for every
player `i` and context, the utilities `i` obtains across its own strategies sum
to zero. This is the unique representative of a flow with no nonstrategic part. -/
def NormalizedSpace : Submodule ℝ ((∀ i, S i) → Payoff ι) where
  carrier := {u | ∀ (i : ι) (σ : ∀ j, S j), ∑ s : S i, u (Function.update σ i s) i = 0}
  add_mem' {u v} hu hv i σ := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, hu i σ, hv i σ, add_zero]
  zero_mem' i σ := by simp
  smul_mem' c u hu i σ := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hu i σ, mul_zero]

/-- The **normalization** projection: subtract each player's per-context mean
utility. Its image lies in `NormalizedSpace` and it fixes the flow. -/
noncomputable def normalize : ((∀ i, S i) → Payoff ι) →ₗ[ℝ] ((∀ i, S i) → Payoff ι) where
  toFun u := fun σ i => u σ i - (∑ s : S i, u (Function.update σ i s) i) / (Fintype.card (S i))
  map_add' u v := by
    funext σ i; simp only [Pi.add_apply, Finset.sum_add_distrib, add_div]; ring
  map_smul' c u := by
    funext σ i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum, mul_div_assoc]
    ring

@[simp] lemma normalize_apply (u : (∀ i, S i) → Payoff ι) (σ : ∀ i, S i) (i : ι) :
    normalize u σ i = u σ i - (∑ s : S i, u (Function.update σ i s) i) / (Fintype.card (S i)) :=
  rfl

theorem normalize_mem_normalizedSpace [∀ i, Nonempty (S i)] (u : (∀ i, S i) → Payoff ι) :
    normalize u ∈ NormalizedSpace := by
  intro i σ
  have hcard : (Fintype.card (S i) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [normalize_apply, Function.update_idem]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem sub_normalize_mem_nonstrategicSpace (u : (∀ i, S i) → Payoff ι) :
    u - normalize u ∈ NonstrategicSpace := by
  intro σ i s'
  simp only [Pi.sub_apply, normalize_apply, Function.update_idem, sub_sub_cancel]

theorem flowLinear_normalize (u : (∀ i, S i) → Payoff ι) :
    flowLinear (normalize u) = flowLinear u := by
  funext e
  obtain ⟨σ, i, s', hs'⟩ := e
  simp only [flowLinear_apply, flow, normalize_apply, Function.update_idem]
  ring

theorem normalizedSpace_isCompl_nonstrategicSpace [∀ i, Nonempty (S i)] :
    IsCompl (NormalizedSpace (S := S)) (NonstrategicSpace (S := S)) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro u hN hNs
    funext σ i
    have hcard : (Fintype.card (S i) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have h1 : ∑ s : S i, u (Function.update σ i s) i = 0 := hN i σ
    rw [Finset.sum_congr rfl (fun s _ => hNs σ i s), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at h1
    have := (mul_eq_zero.mp h1).resolve_left hcard
    simpa using this
  · rw [codisjoint_iff, eq_top_iff]
    intro u _
    rw [show u = normalize u + (u - normalize u) by abel]
    exact Submodule.add_mem_sup (normalize_mem_normalizedSpace u)
      (sub_normalize_mem_nonstrategicSpace u)

/-- The **flow equivalence**: `flowLinear` restricts to a linear isomorphism from
the normalized games onto its range. Injectivity is disjointness of the
normalized and nonstrategic subspaces; surjectivity is `flowLinear_normalize`. -/
noncomputable def flowNormalizedEquiv [∀ i, Nonempty (S i)] :
    NormalizedSpace (S := S) ≃ₗ[ℝ] LinearMap.range (flowLinear (ι := ι) (S := S)) :=
  LinearEquiv.ofBijective
    ((flowLinear.domRestrict NormalizedSpace).codRestrict (LinearMap.range flowLinear)
      (fun _ => LinearMap.mem_range_self _ _))
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro u hu
      have h0 : flowLinear (u : (∀ i, S i) → Payoff ι) = 0 := Subtype.ext_iff.mp hu
      have hns := (mem_nonstrategicSpace_iff_flowLinear_eq_zero
          (u : (∀ i, S i) → Payoff ι)).mpr h0
      exact Subtype.ext
        ((Submodule.disjoint_def.mp normalizedSpace_isCompl_nonstrategicSpace.disjoint)
          (u : (∀ i, S i) → Payoff ι) u.2 hns),
     by
      rintro ⟨y, u, rfl⟩
      exact ⟨⟨normalize u, normalize_mem_normalizedSpace u⟩,
        Subtype.ext (flowLinear_normalize u)⟩⟩

end Normalized

/-! ### Sanity example: a `2 × 2` game -/

section Example

/-- A concrete two-player game on `Bool` strategies: each player scores `1`
exactly when they play `true`. -/
def exGame : (∀ _ : Fin 2, Bool) → Payoff (Fin 2) := fun σ i => if σ i then 1 else 0

/-- The flow of `exGame` for player `0` switching to `true` from the all-`false`
profile is `1`. -/
example : flow exGame (fun _ => false) 0 true = 1 := by
  simp [flow, exGame, Function.update_self]

/-- `normalize exGame` has the per-context mean `1/2` removed, so it is normalized:
each player's two utilities sum to zero. -/
example : normalize exGame ∈ NormalizedSpace := normalize_mem_normalizedSpace exGame

end Example

end GameTheory.FlowDecomposition
