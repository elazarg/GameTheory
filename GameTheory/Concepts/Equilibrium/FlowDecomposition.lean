/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Potential.Decomposition
import GameTheory.Concepts.Equilibrium.FlowInvariance

/-!
# The equilibrium meaning of the flow decomposition

The equilibrium-facing layer of the Candogan–Menache–Ozdaglar–Parrilo development
(*Flows and Decompositions of Games: Harmonic and Potential Games*,
Math. Oper. Res. 2011). The flow layer (`Concepts/Potential/`) is deliberately
ignorant of solution concepts; this file supplies the bridge back to Nash,
correlated, and coarse-correlated equilibria.

This file:

- `mem_nonstrategicSpace_iff_dependsOnlyOnOthers` — the flow-kernel subspace of the
  decomposition is exactly the `wᵢ(σ₋ᵢ)` shape that flow invariance cancels;
- `isNash_of_flowEquiv`, `isCorrelatedEq_of_flowEquiv`,
  `isCoarseCorrelatedEq_of_flowEquiv` — two games with the same unilateral flow
  share their Nash / correlated / coarse-correlated equilibria (the equilibrium
  face of `flowEquiv_iff_sub_nonstrategic`, glued to flow invariance);
- `isNash_ofPureEU_dropNonstrategic` and its CE/CCE twins — a game and its
  potential-plus-harmonic part (dropping the nonstrategic component of the flow
  decomposition) share the unilateral solution concepts;
- `coalitionGain` — the per-member endpoint payoff differences of a coalition's
  joint move, with `coalitionGain_singleton` recovering the unilateral flow;
- `unilateralFlow_ne_determines_coalitionGain` — a checked separation: same
  unilateral flow does not determine the coalitional gain data.

## Coalition endpoint data, honestly

`coalitionGain` is endpoint payoff data on a diagonal of a product cell of the
profile space. It is vector-valued (one component per coalition member), carries
no orientation, and interacts with no boundary operator: it is **not** a cochain.
The cochain refinement — orientations, a coboundary `d₁`, `d ∘ d = 0`, and curl
adjoints over the cubical (product) cell structure whose 1-skeleton is the
unilateral game graph — belongs to a successor theory and is not developed here.
`unilateralFlow_ne_determines_coalitionGain` records only that the 1-skeleton flow
does not determine this endpoint data; it makes no claim to detect a higher Hodge
component. It is the decomposition-side face of the strong-Nash boundary already
checked in `FlowInvariance.lean` (`FlowInvarianceExample.g0_isStrongNash` versus
`FlowInvarianceExample.g1_not_isStrongNash`).
-/

open Finset BigOperators
open Math.LinearAlgebra.WeightedIncidence

namespace GameTheory.FlowDecomposition

open KernelGame

variable {ι : Type} [DecidableEq ι] {S : ι → Type}

/-! ### The nonstrategic subspace is the flow-invariance kernel -/

/-- **The flow-kernel subspace is the flow-invariance predicate.** A utility vector
lies in `NonstrategicSpace` — its flow vanishes — exactly when each player's payoff
depends only on the opponents' strategies (`KernelGame.DependsOnlyOnOthers`, the
`wᵢ(σ₋ᵢ)` shape that flow invariance cancels). This is the bridge from the flow
layer's kernel to the equilibrium layer's nonstrategic components. -/
theorem mem_nonstrategicSpace_iff_dependsOnlyOnOthers (u : (∀ i, S i) → Payoff ι) :
    u ∈ NonstrategicSpace ↔ KernelGame.DependsOnlyOnOthers u := by
  constructor
  · intro hu i σ σ' hagree
    have hσ' : Function.update σ i (σ' i) = σ' := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj]; exact hagree j hj
    rw [← hσ']
    exact (hu σ i (σ' i)).symm
  · intro h σ i s'
    exact h i (Function.update σ i s') σ (fun j hj => Function.update_of_ne hj s' σ)

omit [DecidableEq ι] in
/-- Adding a nonstrategic component to a strategic-form game is the same as adding
it to the utility vector: `(ofPureEU S u).addNonstrategic w = ofPureEU S (u + w)`.
The two games agree in every field (utilities pointwise). -/
theorem ofPureEU_addNonstrategic (u w : (∀ i, S i) → Payoff ι) :
    (KernelGame.ofPureEU S u).addNonstrategic w = KernelGame.ofPureEU S (u + w) := rfl

/-! ### Equal flow ⇒ shared unilateral equilibria -/

/-- Transport a Nash equilibrium along a game equality. Needed because `IsNash` is
dependent in its game argument, so `rw` cannot rewrite the game underneath a fixed
profile; the profile is carried across by `HEq`. -/
private theorem isNash_iff_of_game_eq {G G' : KernelGame ι} (h : G = G')
    {σ : G.Profile} {σ' : G'.Profile} (hσ : HEq σ σ') : G.IsNash σ ↔ G'.IsNash σ' := by
  subst h; cases hσ; rfl

/-- Transport a correlated equilibrium along a game equality. -/
private theorem isCorrelatedEq_iff_of_game_eq {G G' : KernelGame ι} (h : G = G')
    {μ : PMF G.Profile} {μ' : PMF G'.Profile} (hμ : HEq μ μ') :
    G.IsCorrelatedEq μ ↔ G'.IsCorrelatedEq μ' := by subst h; cases hμ; rfl

/-- Transport a coarse-correlated equilibrium along a game equality. -/
private theorem isCoarseCorrelatedEq_iff_of_game_eq {G G' : KernelGame ι} (h : G = G')
    {μ : PMF G.Profile} {μ' : PMF G'.Profile} (hμ : HEq μ μ') :
    G.IsCoarseCorrelatedEq μ ↔ G'.IsCoarseCorrelatedEq μ' := by subst h; cases hμ; rfl

section Equilibrium

variable [Finite ι] [∀ i, Finite (S i)]

/-- **Same flow ⇒ same Nash.** Two strategic-form games with equal unilateral flow
have exactly the same Nash equilibria: they differ by a nonstrategic component,
which cancels in every player's unilateral incentive comparison. This is the
equilibrium face of `flowEquiv_iff_sub_nonstrategic`. -/
theorem isNash_of_flowEquiv (u u' : (∀ i, S i) → Payoff ι)
    (h : flowLinear u = flowLinear u') (σ : (KernelGame.ofPureEU S u).Profile) :
    (KernelGame.ofPureEU S u).IsNash σ ↔ (KernelGame.ofPureEU S u').IsNash σ := by
  haveI : Finite (KernelGame.ofPureEU S u).Outcome := inferInstanceAs (Finite (∀ i, S i))
  have hdoo : KernelGame.DependsOnlyOnOthers (u' - u) :=
    (mem_nonstrategicSpace_iff_dependsOnlyOnOthers _).mp
      ((flowEquiv_iff_sub_nonstrategic u' u).mp h.symm)
  have hgame : KernelGame.ofPureEU S u' = (KernelGame.ofPureEU S u).addNonstrategic (u' - u) := by
    rw [ofPureEU_addNonstrategic]; congr 1; abel
  refine (KernelGame.isNash_addNonstrategic_iff (KernelGame.ofPureEU S u) (u' - u)
    (KernelGame.ofPureEU_nonstrategic_constant S u (u' - u) hdoo)
    (KernelGame.ExpectSummable.of_finite _ _)
    (KernelGame.ExpectSummable.of_finite _ _) σ).symm.trans ?_
  exact (isNash_iff_of_game_eq hgame (σ := σ) (σ' := σ) HEq.rfl).symm

/-- **Same flow ⇒ same correlated equilibria.** Equal unilateral flow leaves the
correlated equilibria of every correlation device unchanged. -/
theorem isCorrelatedEq_of_flowEquiv (u u' : (∀ i, S i) → Payoff ι)
    (h : flowLinear u = flowLinear u') (μ : PMF (KernelGame.ofPureEU S u).Profile) :
    (KernelGame.ofPureEU S u).IsCorrelatedEq μ ↔ (KernelGame.ofPureEU S u').IsCorrelatedEq μ := by
  haveI : Finite (KernelGame.ofPureEU S u).Outcome := inferInstanceAs (Finite (∀ i, S i))
  have hdoo : KernelGame.DependsOnlyOnOthers (u' - u) :=
    (mem_nonstrategicSpace_iff_dependsOnlyOnOthers _).mp
      ((flowEquiv_iff_sub_nonstrategic u' u).mp h.symm)
  have hgame : KernelGame.ofPureEU S u' = (KernelGame.ofPureEU S u).addNonstrategic (u' - u) := by
    rw [ofPureEU_addNonstrategic]; congr 1; abel
  refine (KernelGame.isCorrelatedEq_addNonstrategic_iff (KernelGame.ofPureEU S u) (u' - u)
    (KernelGame.ofPureEU_nonstrategic_recommendation S u (u' - u) hdoo)
    (KernelGame.ExpectSummable.of_finite _ _)
    (KernelGame.ExpectSummable.of_finite _ _) μ).symm.trans ?_
  exact (isCorrelatedEq_iff_of_game_eq hgame (μ := μ) (μ' := μ) HEq.rfl).symm

/-- **Same flow ⇒ same coarse-correlated equilibria.** Equal unilateral flow leaves
the coarse correlated equilibria of every correlation device unchanged. -/
theorem isCoarseCorrelatedEq_of_flowEquiv (u u' : (∀ i, S i) → Payoff ι)
    (h : flowLinear u = flowLinear u') (μ : PMF (KernelGame.ofPureEU S u).Profile) :
    (KernelGame.ofPureEU S u).IsCoarseCorrelatedEq μ ↔
      (KernelGame.ofPureEU S u').IsCoarseCorrelatedEq μ := by
  haveI : Finite (KernelGame.ofPureEU S u).Outcome := inferInstanceAs (Finite (∀ i, S i))
  have hdoo : KernelGame.DependsOnlyOnOthers (u' - u) :=
    (mem_nonstrategicSpace_iff_dependsOnlyOnOthers _).mp
      ((flowEquiv_iff_sub_nonstrategic u' u).mp h.symm)
  have hgame : KernelGame.ofPureEU S u' = (KernelGame.ofPureEU S u).addNonstrategic (u' - u) := by
    rw [ofPureEU_addNonstrategic]; congr 1; abel
  refine (KernelGame.isCoarseCorrelatedEq_addNonstrategic_iff (KernelGame.ofPureEU S u) (u' - u)
    (KernelGame.ofPureEU_nonstrategic_constant S u (u' - u) hdoo)
    (KernelGame.ExpectSummable.of_finite _ _)
    (KernelGame.ExpectSummable.of_finite _ _) μ).symm.trans ?_
  exact (isCoarseCorrelatedEq_iff_of_game_eq hgame (μ := μ) (μ' := μ) HEq.rfl).symm

/-! ### Dropping the nonstrategic component of the decomposition

When `u = p + h + n` is the flow decomposition of a game (`p` its potential
component, `h` its harmonic component, `n` its nonstrategic component), the game
and its **potential-plus-harmonic part** `p + h` have the same unilateral flow —
`n` is nonstrategic, so its flow vanishes — hence the same Nash, correlated, and
coarse-correlated equilibria. Dropping the nonstrategic component of the
decomposition preserves the unilateral solution concepts. -/

/-- The potential-plus-harmonic part `p + h` preserves Nash: dropping the
nonstrategic component `n` of the decomposition `u = p + h + n` does not change the
Nash equilibria. -/
theorem isNash_ofPureEU_dropNonstrategic (p h n : (∀ i, S i) → Payoff ι)
    (hn : n ∈ NonstrategicSpace) (σ : (KernelGame.ofPureEU S (p + h + n)).Profile) :
    (KernelGame.ofPureEU S (p + h + n)).IsNash σ ↔ (KernelGame.ofPureEU S (p + h)).IsNash σ := by
  apply isNash_of_flowEquiv
  rw [map_add, (mem_nonstrategicSpace_iff_flowLinear_eq_zero n).mp hn, add_zero]

/-- The potential-plus-harmonic part `p + h` preserves correlated equilibria. -/
theorem isCorrelatedEq_ofPureEU_dropNonstrategic (p h n : (∀ i, S i) → Payoff ι)
    (hn : n ∈ NonstrategicSpace) (μ : PMF (KernelGame.ofPureEU S (p + h + n)).Profile) :
    (KernelGame.ofPureEU S (p + h + n)).IsCorrelatedEq μ ↔
      (KernelGame.ofPureEU S (p + h)).IsCorrelatedEq μ := by
  apply isCorrelatedEq_of_flowEquiv
  rw [map_add, (mem_nonstrategicSpace_iff_flowLinear_eq_zero n).mp hn, add_zero]

/-- The potential-plus-harmonic part `p + h` preserves coarse-correlated
equilibria. -/
theorem isCoarseCorrelatedEq_ofPureEU_dropNonstrategic (p h n : (∀ i, S i) → Payoff ι)
    (hn : n ∈ NonstrategicSpace) (μ : PMF (KernelGame.ofPureEU S (p + h + n)).Profile) :
    (KernelGame.ofPureEU S (p + h + n)).IsCoarseCorrelatedEq μ ↔
      (KernelGame.ofPureEU S (p + h)).IsCoarseCorrelatedEq μ := by
  apply isCoarseCorrelatedEq_of_flowEquiv
  rw [map_add, (mem_nonstrategicSpace_iff_flowLinear_eq_zero n).mp hn, add_zero]

end Equilibrium

/-! ### Coalition endpoint data -/

/-- The **coalition gain**: for a coalition `C` making the joint move from `σ` to
its members' choices in `τ` (non-members keeping `σ`), the vector of per-member
utility differences at the two endpoints. Component `i ∈ C` is member `i`'s payoff
change.

This is endpoint payoff data on a diagonal of a product cell of the profile space:
it is vector-valued, carries no orientation, and interacts with no boundary
operator. It is **not** a cochain, and the cochain refinement over the cubical cell
structure is a successor theory (see the module docstring). -/
def coalitionGain (u : (∀ i, S i) → Payoff ι) (σ : ∀ i, S i) (C : Coalition ι)
    (τ : ∀ i, S i) : {i // i ∈ C.val} → ℝ :=
  fun i => u (fun j => if j ∈ C.val then τ j else σ j) i.val - u σ i.val

/-- **Singletons recover the unilateral flow.** At a singleton coalition the
coalition gain of its one member is exactly the unilateral flow of that player's
move. This is the degree-one face of the endpoint data. -/
theorem coalitionGain_singleton (u : (∀ i, S i) → Payoff ι) (σ : ∀ i, S i) (i : ι)
    (τ : ∀ i, S i) (hi : i ∈ (Coalition.singleton i).val) :
    coalitionGain u σ (Coalition.singleton i) τ ⟨i, hi⟩ = flow u σ i (τ i) := by
  have hp : (fun j => if j ∈ (Coalition.singleton i).val then τ j else σ j)
      = Function.update σ i (τ i) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [Coalition.singleton]
    · simp [Coalition.singleton, hj]
  simp only [coalitionGain, flow, hp]

/-! ### Separation: the flow does not determine the coalition gain -/

open FlowInvarianceExample in
/-- **Unilateral flow does not determine the coalitional gain.** The two games of
`FlowInvarianceExample` — the zero game and its nonstrategic shift by `w` — have the
same (identically zero) unilateral flow, yet their `coalitionGain` at the grand
coalition, moving from all-`false` to all-`true`, differs (each member's gain is `0`
versus `1`). Unilateral payoff-difference data does not determine coalitional
payoff-difference data.

This is the decomposition-side face of the strong-Nash boundary checked in
`FlowInvariance.lean` (`FlowInvarianceExample.g0_isStrongNash` versus
`FlowInvarianceExample.g1_not_isStrongNash`). It records only that the 1-skeleton
flow underdetermines this endpoint data; it makes no claim to detect a higher Hodge
component. -/
theorem unilateralFlow_ne_determines_coalitionGain :
    flowLinear (ι := Bool) (S := fun _ => Bool) (fun _ _ => 0) = flowLinear w ∧
      coalitionGain (fun _ _ => (0 : ℝ)) (fun _ => false)
          ⟨Finset.univ, Finset.univ_nonempty⟩ (fun _ => true) ≠
        coalitionGain w (fun _ => false) ⟨Finset.univ, Finset.univ_nonempty⟩ (fun _ => true) := by
  refine ⟨?_, ?_⟩
  · have h1 : flowLinear (ι := Bool) (S := fun _ => Bool) (fun _ _ => 0) = 0 := by
      funext e; simp [flowLinear_apply, flow]
    have h2 : flowLinear w = 0 :=
      (mem_nonstrategicSpace_iff_flowLinear_eq_zero w).mp
        ((mem_nonstrategicSpace_iff_dependsOnlyOnOthers w).mpr w_dependsOnlyOnOthers)
    rw [h1, h2]
  · intro heq
    have hval := congrFun heq ⟨true, Finset.mem_univ true⟩
    simp [coalitionGain, w] at hval

end GameTheory.FlowDecomposition
