/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Potential.Harmonic
import GameTheory.Core.GameProperties

/-!
# The flow decomposition of finite games (Hodge decomposition of games)

The decomposition layer of the Candogan–Menache–Ozdaglar–Parrilo development
(*Flows and Decompositions of Games: Harmonic and Potential Games*,
Math. Oper. Res. 2011). Every finite game with fixed strategy sets splits
**uniquely** into a **potential component**, a **harmonic component**, and a
**nonstrategic component**. On the flow (edge) level this is the degree-one
Helmholtz/Hodge split of the game graph provided by the weighted-incidence
spine; on the game level it is glued to the normalized representative.

This file:

- `PotentialComponentSpace`, `HarmonicComponentSpace` — the two normalized
  component subspaces (paper's `P` and `H`), and the larger game classes
  `PotentialGameSpace`, `HarmonicGameSpace` that also absorb nonstrategic
  shifts;
- `gamifyPotential` — the game whose every player's utility *is* a fixed node
  potential; its flow is exactly the gradient, so gradients of the game graph
  are realized as flows (`grad_mem_range_flowLinear`);
- `decomposition` — the unique splitting `u = p + h + n` into potential,
  harmonic, and nonstrategic parts, together with the submodule-lattice facts
  (`potentialComponent_sup_harmonicComponent`, its disjointness twin, and the
  three-way span of the whole game space);
- `isHarmonic_iff_mem_harmonicGameSpace`,
  `mem_potentialGameSpace_iff_isExactPotential` — the identifications of the two
  game classes with the divergence-free and exact-potential notions;
- `potentialGameSpace_inf_harmonicGameSpace` — a game that is both potential and
  harmonic is nonstrategic.
-/

open Finset BigOperators
open Math.LinearAlgebra.WeightedIncidence

namespace GameTheory.FlowDecomposition

variable {ι : Type} [DecidableEq ι] {S : ι → Type}

/-! ### Gradient games: realizing node potentials as flows -/

/-- The **gradient game** of a node potential `φ`: every player's utility is `φ`
itself. Its unilateral flow along each edge is the gradient of `φ`, so the
gradients of the game graph are exactly the flows of these games. -/
def gamifyPotential (φ : (∀ i, S i) → ℝ) : (∀ i, S i) → Payoff ι := fun σ _ => φ σ

omit [DecidableEq ι] in
@[simp] lemma gamifyPotential_apply (φ : (∀ i, S i) → ℝ) (σ : ∀ i, S i) (i : ι) :
    gamifyPotential φ σ i = φ σ := rfl

lemma flow_gamifyPotential (φ : (∀ i, S i) → ℝ) (σ : ∀ i, S i) (i : ι) (s' : S i) :
    flow (gamifyPotential φ) σ i s' = φ (Function.update σ i s') - φ σ := rfl

/-- The flow of a gradient game is the gradient of its potential (on the edge
space of the game graph). -/
lemma flowLinear_gamifyPotential (φ : (∀ i, S i) → ℝ) :
    flowLinear (gamifyPotential φ) = grad edgeSrc edgeTgt φ := by
  funext e
  simp only [flowLinear_apply, flow_gamifyPotential, grad_apply, edgeTgt, edgeSrc]

/-- **Gradients are realized as flows**: every gradient of the game graph is the
flow of some game (the gradient game of its potential). This is the step that
makes `range flowLinear` closed under the cut/cycle split. -/
lemma grad_mem_range_flowLinear (φ : (∀ i, S i) → ℝ) :
    grad edgeSrc edgeTgt φ ∈ LinearMap.range (flowLinear (ι := ι) (S := S)) :=
  ⟨gamifyPotential φ, flowLinear_gamifyPotential φ⟩

/-- Two decompositions `a + b = a' + b'` with `a, a'` in `p` and `b, b'` in a
subspace `q` disjoint from `p` must agree componentwise. -/
theorem eq_of_add_eq_of_disjoint {V : Type*} [AddCommGroup V] [Module ℝ V]
    {p q : Submodule ℝ V} (h : Disjoint p q) {a a' b b' : V}
    (ha : a ∈ p) (ha' : a' ∈ p) (hb : b ∈ q) (hb' : b' ∈ q)
    (hadd : a + b = a' + b') : a = a' ∧ b = b' := by
  have hmem : a - a' ∈ q := by
    have hswap : a - a' = b' - b := by
      rw [sub_eq_sub_iff_add_eq_add, hadd]; exact add_comm a' b'
    rw [hswap]; exact q.sub_mem hb' hb
  have h0 : a - a' = 0 :=
    (Submodule.disjoint_def.mp h) (a - a') (p.sub_mem ha ha') hmem
  have haa : a = a' := sub_eq_zero.mp h0
  exact ⟨haa, by rw [haa] at hadd; exact add_left_cancel hadd⟩

/-- **The flow determines the game up to a nonstrategic shift**: two games have the
same unilateral flow exactly when they differ by a nonstrategic game. This is the
linear-algebra face of flow invariance. -/
theorem flowEquiv_iff_sub_nonstrategic (u u' : (∀ i, S i) → Payoff ι) :
    flowLinear u = flowLinear u' ↔ u - u' ∈ NonstrategicSpace := by
  rw [mem_nonstrategicSpace_iff_flowLinear_eq_zero, map_sub, sub_eq_zero]

/-- Exact-potentiality of `ofPureEU S u` is the flow-level gradient identity: the
unilateral flow of `u` is the potential difference along every deviation. -/
theorem isExactPotential_ofPureEU_iff (u : (∀ i, S i) → Payoff ι) (φ : (∀ i, S i) → ℝ) :
    (KernelGame.ofPureEU S u).IsExactPotential φ ↔
      ∀ (who : ι) (σ : ∀ i, S i) (s' : S who),
        flow u σ who s' = φ (Function.update σ who s') - φ σ := by
  refine ⟨fun h who σ s' => ?_, fun h who σ s' => ?_⟩
  · have hval := h who σ s'
    rw [KernelGame.eu_ofPureEU, KernelGame.eu_ofPureEU] at hval
    exact hval
  · rw [KernelGame.eu_ofPureEU, KernelGame.eu_ofPureEU]
    exact h who σ s'

/-- **Gradient games are exact-potential games**: the game whose every player's
utility is `φ` has `φ` itself as an exact potential. -/
theorem gamifyPotential_isExactPotential (φ : (∀ i, S i) → ℝ) :
    (KernelGame.ofPureEU S (gamifyPotential φ)).IsExactPotential φ := by
  rw [isExactPotential_ofPureEU_iff]
  intro who σ s'
  rw [flow_gamifyPotential]

/-- The flow of `u` is the gradient of `φ` exactly when `φ` is a potential for the
deviation gains of `u` at every profile (self-deviations are the trivial case). -/
theorem flowLinear_eq_grad_iff (u : (∀ i, S i) → Payoff ι) (φ : (∀ i, S i) → ℝ) :
    flowLinear u = grad edgeSrc edgeTgt φ ↔
      ∀ (who : ι) (σ : ∀ i, S i) (s' : S who),
        flow u σ who s' = φ (Function.update σ who s') - φ σ := by
  constructor
  · intro h who σ s'
    rcases eq_or_ne s' (σ who) with hs | hs
    · subst hs; simp [flow_self, Function.update_eq_self]
    · have hc := congrFun h ⟨σ, who, s', hs⟩
      simpa only [flowLinear_apply, grad_apply, edgeTgt, edgeSrc] using hc
  · intro h
    funext e
    obtain ⟨σ, who, s', hs⟩ := e
    rw [flowLinear_apply, grad_apply]
    simpa only [edgeTgt, edgeSrc] using h who σ s'

/-! ### The potential component and games -/

section PotentialSide

variable [∀ i, Fintype (S i)]

/-- The **potential component** subspace (paper's `P`): the normalized games whose
flow is a gradient of the game graph. -/
def PotentialComponentSpace : Submodule ℝ ((∀ i, S i) → Payoff ι) :=
  NormalizedSpace ⊓ Submodule.comap flowLinear (LinearMap.range (grad edgeSrc edgeTgt))

/-- The **potential games**: the potential component plus arbitrary nonstrategic
shifts. -/
def PotentialGameSpace : Submodule ℝ ((∀ i, S i) → Payoff ι) :=
  PotentialComponentSpace ⊔ NonstrategicSpace

theorem mem_potentialComponentSpace_iff (u : (∀ i, S i) → Payoff ι) :
    u ∈ PotentialComponentSpace ↔
      u ∈ NormalizedSpace ∧ ∃ φ, flowLinear u = grad edgeSrc edgeTgt φ := by
  simp only [PotentialComponentSpace, Submodule.mem_inf, Submodule.mem_comap, LinearMap.mem_range,
    eq_comm]

/-- Normalization fixes an already-normalized game. -/
theorem normalize_of_mem_normalizedSpace {u : (∀ i, S i) → Payoff ι}
    (hu : u ∈ NormalizedSpace) : normalize u = u := by
  funext σ i
  rw [normalize_apply, hu i σ, zero_div, sub_zero]

/-- Normalization annihilates a nonstrategic game. -/
theorem normalize_of_mem_nonstrategicSpace [∀ i, Nonempty (S i)]
    {w : (∀ i, S i) → Payoff ι} (hw : w ∈ NonstrategicSpace) : normalize w = 0 := by
  funext σ i
  simp only [Pi.zero_apply]
  have hcard : (Fintype.card (S i) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [normalize_apply, Finset.sum_congr rfl (fun s _ => hw σ i s),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, mul_div_assoc,
    div_self hcard, mul_one, sub_self]

end PotentialSide

/-! ### The harmonic component and games -/

section Full

variable [Fintype ι] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The **harmonic component** subspace (paper's `H`): the normalized games whose
flow is divergence-free. -/
noncomputable def HarmonicComponentSpace : Submodule ℝ ((∀ i, S i) → Payoff ι) :=
  NormalizedSpace ⊓ LinearMap.ker gameDivLinear

/-- The **harmonic games**: the harmonic component plus arbitrary nonstrategic
shifts. -/
noncomputable def HarmonicGameSpace : Submodule ℝ ((∀ i, S i) → Payoff ι) :=
  HarmonicComponentSpace ⊔ NonstrategicSpace

theorem mem_harmonicComponentSpace_iff (u : (∀ i, S i) → Payoff ι) :
    u ∈ HarmonicComponentSpace ↔ u ∈ NormalizedSpace ∧ IsHarmonic u := by
  simp only [HarmonicComponentSpace, Submodule.mem_inf, LinearMap.mem_ker, gameDivLinear_apply,
    IsHarmonic]

omit [Fintype ι] [∀ i, DecidableEq (S i)] in
/-- Two normalized games with the same flow are equal: `flowLinear` is injective on
`NormalizedSpace` (the normalized representative is unique for its flow). -/
theorem normalizedSpace_flowLinear_inj [∀ i, Nonempty (S i)]
    {a b : (∀ i, S i) → Payoff ι} (ha : a ∈ NormalizedSpace) (hb : b ∈ NormalizedSpace)
    (h : flowLinear a = flowLinear b) : a = b := by
  have hab : a - b ∈ NonstrategicSpace := by
    rw [mem_nonstrategicSpace_iff_flowLinear_eq_zero, map_sub, h, sub_self]
  have h0 := (Submodule.disjoint_def.mp normalizedSpace_isCompl_nonstrategicSpace.disjoint)
    (a - b) (NormalizedSpace.sub_mem ha hb) hab
  exact sub_eq_zero.mp h0

/-! ### The decomposition -/

/-- **The potential and harmonic components split the normalized games.** Inside
`NormalizedSpace`, the flow-level cut/cycle (Helmholtz) decomposition pulls back to
the two component subspaces. -/
theorem potentialComponent_sup_harmonicComponent [∀ i, Nonempty (S i)] :
    PotentialComponentSpace ⊔ HarmonicComponentSpace = NormalizedSpace (S := S) := by
  apply le_antisymm
  · exact sup_le inf_le_left inf_le_left
  · intro u hu
    obtain ⟨p, ⟨hp_range, hp_ker⟩, -⟩ :=
      exists_unique_grad_add_ker_div edgeSrc edgeTgt (fun _ => 1) (fun _ => one_pos) (flowLinear u)
    obtain ⟨φ, hφ⟩ := hp_range
    -- potential component: the normalized gradient game
    have hflow_pc : flowLinear (normalize (gamifyPotential φ)) = p := by
      rw [flowLinear_normalize, flowLinear_gamifyPotential, hφ]
    have hpc_mem : normalize (gamifyPotential φ) ∈ PotentialComponentSpace := by
      rw [mem_potentialComponentSpace_iff]
      exact ⟨normalize_mem_normalizedSpace _, φ, by rw [hflow_pc, hφ]⟩
    -- harmonic component: pull back the divergence-free residual
    have hXp : flowLinear u - p ∈ LinearMap.range (flowLinear (ι := ι) (S := S)) :=
      Submodule.sub_mem _ (LinearMap.mem_range_self _ u) (hφ ▸ grad_mem_range_flowLinear φ)
    obtain ⟨w, hw⟩ := hXp
    have hflow_hc : flowLinear (normalize w) = flowLinear u - p := by
      rw [flowLinear_normalize, hw]
    have hhc_mem : normalize w ∈ HarmonicComponentSpace := by
      rw [mem_harmonicComponentSpace_iff]
      refine ⟨normalize_mem_normalizedSpace _, ?_⟩
      rw [IsHarmonic, ← gameDivLinear_apply, gameDivLinear, LinearMap.comp_apply, hflow_hc]
      exact LinearMap.mem_ker.mp hp_ker
    -- assemble: the two normalized components have combined flow `flowLinear u`
    have hsum : flowLinear (normalize (gamifyPotential φ) + normalize w) = flowLinear u := by
      rw [map_add, hflow_pc, hflow_hc]; abel
    have hnorm_sum : normalize (gamifyPotential φ) + normalize w ∈ NormalizedSpace :=
      NormalizedSpace.add_mem (normalize_mem_normalizedSpace _) (normalize_mem_normalizedSpace _)
    have hu_eq : u = normalize (gamifyPotential φ) + normalize w :=
      normalizedSpace_flowLinear_inj hu hnorm_sum hsum.symm
    rw [hu_eq]
    exact Submodule.add_mem_sup hpc_mem hhc_mem

/-- **The potential and harmonic components are disjoint.** A normalized game whose
flow is both a gradient and divergence-free has zero flow, hence is nonstrategic and
normalized, hence zero. -/
theorem potentialComponent_disjoint_harmonicComponent [∀ i, Nonempty (S i)] :
    Disjoint (PotentialComponentSpace (S := S)) HarmonicComponentSpace := by
  rw [Submodule.disjoint_def]
  intro u hp hh
  obtain ⟨hu_norm, φ, hφ⟩ := (mem_potentialComponentSpace_iff u).mp hp
  obtain ⟨-, hharm⟩ := (mem_harmonicComponentSpace_iff u).mp hh
  have h1 : flowLinear u ∈ LinearMap.range (grad edgeSrc edgeTgt) :=
    hφ ▸ LinearMap.mem_range_self _ _
  have h2 : flowLinear u ∈ LinearMap.ker (div edgeSrc edgeTgt (fun _ => 1)) := by
    rw [LinearMap.mem_ker]
    have hgd : gameDiv u = 0 := hharm
    rwa [← gameDivLinear_apply, gameDivLinear, LinearMap.comp_apply] at hgd
  have hflow0 : flowLinear u = 0 :=
    (Submodule.disjoint_def.mp
      (disjoint_range_grad_ker_div edgeSrc edgeTgt (fun _ => 1) (fun _ => one_pos)))
      (flowLinear u) h1 h2
  have hns : u ∈ NonstrategicSpace := (mem_nonstrategicSpace_iff_flowLinear_eq_zero u).mpr hflow0
  exact (Submodule.disjoint_def.mp normalizedSpace_isCompl_nonstrategicSpace.disjoint) u hu_norm hns

/-- **The three component subspaces are complementary** — they span the whole space
of games. -/
theorem potentialComponent_sup_harmonicComponent_sup_nonstrategic [∀ i, Nonempty (S i)] :
    PotentialComponentSpace ⊔ HarmonicComponentSpace ⊔ NonstrategicSpace
      = (⊤ : Submodule ℝ ((∀ i, S i) → Payoff ι)) := by
  rw [potentialComponent_sup_harmonicComponent,
    normalizedSpace_isCompl_nonstrategicSpace.sup_eq_top]

/-- **The Hodge decomposition of a finite game.** Every game splits *uniquely* as
`u = p + h + n` with `p` a potential component, `h` a harmonic component, and `n`
nonstrategic. Uniqueness is stated on the packaged triple. -/
theorem decomposition [∀ i, Nonempty (S i)] (u : (∀ i, S i) → Payoff ι) :
    ∃! t : ((∀ i, S i) → Payoff ι) × ((∀ i, S i) → Payoff ι) × ((∀ i, S i) → Payoff ι),
      t.1 ∈ PotentialComponentSpace ∧ t.2.1 ∈ HarmonicComponentSpace ∧
        t.2.2 ∈ NonstrategicSpace ∧ u = t.1 + t.2.1 + t.2.2 := by
  have hu0 : normalize u ∈ PotentialComponentSpace ⊔ HarmonicComponentSpace := by
    rw [potentialComponent_sup_harmonicComponent]; exact normalize_mem_normalizedSpace u
  rw [Submodule.mem_sup] at hu0
  obtain ⟨p, hp, h, hh, hph⟩ := hu0
  refine ⟨(p, h, u - normalize u),
    ⟨hp, hh, sub_normalize_mem_nonstrategicSpace u, by rw [hph, add_comm, sub_add_cancel]⟩, ?_⟩
  rintro ⟨p', h', n'⟩ ⟨hp', hh', hn', heq⟩
  have hP_le : PotentialComponentSpace ≤ NormalizedSpace (S := S) := inf_le_left
  have hH_le : HarmonicComponentSpace ≤ NormalizedSpace (S := S) := inf_le_left
  -- outer split: normalized part vs nonstrategic part
  have hwit_eq : u = (p + h) + (u - normalize u) := by rw [hph, add_comm, sub_add_cancel]
  have key : (p + h) + (u - normalize u) = (p' + h') + n' := hwit_eq.symm.trans heq
  obtain ⟨hnorm_eq, hn_eq⟩ := eq_of_add_eq_of_disjoint
    normalizedSpace_isCompl_nonstrategicSpace.disjoint
    (NormalizedSpace.add_mem (hP_le hp) (hH_le hh))
    (NormalizedSpace.add_mem (hP_le hp') (hH_le hh'))
    (sub_normalize_mem_nonstrategicSpace u) hn' key
  -- inner split: potential part vs harmonic part
  obtain ⟨hp_eq, hh_eq⟩ := eq_of_add_eq_of_disjoint
    potentialComponent_disjoint_harmonicComponent hp hp' hh hh' hnorm_eq
  simp only [Prod.mk.injEq]
  exact ⟨hp_eq.symm, hh_eq.symm, hn_eq.symm⟩

/-! ### The game classes -/

/-- **A game is harmonic exactly when it lies in `HarmonicGameSpace`** — the
divergence-free games, modulo nonstrategic shifts. -/
theorem isHarmonic_iff_mem_harmonicGameSpace [∀ i, Nonempty (S i)]
    (u : (∀ i, S i) → Payoff ι) : IsHarmonic u ↔ u ∈ HarmonicGameSpace := by
  constructor
  · intro hu
    rw [HarmonicGameSpace, show u = normalize u + (u - normalize u) by abel]
    refine Submodule.add_mem_sup ?_ (sub_normalize_mem_nonstrategicSpace u)
    rw [mem_harmonicComponentSpace_iff]
    exact ⟨normalize_mem_normalizedSpace u, (isHarmonic_normalize_iff u).mpr hu⟩
  · intro hu
    rw [HarmonicGameSpace, Submodule.mem_sup] at hu
    obtain ⟨h, hh, w, hw, rfl⟩ := hu
    exact ((mem_harmonicComponentSpace_iff h).mp hh).2.add_nonstrategic hw

omit [Fintype ι] [∀ i, DecidableEq (S i)] in
/-- Membership in `PotentialGameSpace` is a flow-level condition: the flow is a
gradient of the game graph. -/
theorem mem_potentialGameSpace_iff_flowLinear_mem_range_grad [∀ i, Nonempty (S i)]
    (u : (∀ i, S i) → Payoff ι) :
    u ∈ PotentialGameSpace ↔ flowLinear u ∈ LinearMap.range (grad edgeSrc edgeTgt) := by
  constructor
  · intro hu
    rw [PotentialGameSpace, Submodule.mem_sup] at hu
    obtain ⟨p, hp, w, hw, rfl⟩ := hu
    obtain ⟨φ, hφ⟩ := ((mem_potentialComponentSpace_iff p).mp hp).2
    rw [map_add, (mem_nonstrategicSpace_iff_flowLinear_eq_zero w).mp hw, add_zero, hφ]
    exact LinearMap.mem_range_self _ _
  · intro hu
    rw [PotentialGameSpace, Submodule.mem_sup]
    refine ⟨normalize u, ?_, u - normalize u, sub_normalize_mem_nonstrategicSpace u, by abel⟩
    rw [mem_potentialComponentSpace_iff, flowLinear_normalize]
    obtain ⟨φ, hφ⟩ := hu
    exact ⟨normalize_mem_normalizedSpace u, φ, hφ.symm⟩

omit [Fintype ι] [∀ i, DecidableEq (S i)] in
/-- **A game is a potential game exactly when it has an exact potential** — the
Potential-cluster notion, at the `ofPureEU` corner. -/
theorem mem_potentialGameSpace_iff_isExactPotential [∀ i, Nonempty (S i)]
    (u : (∀ i, S i) → Payoff ι) :
    u ∈ PotentialGameSpace ↔ ∃ φ, (KernelGame.ofPureEU S u).IsExactPotential φ := by
  rw [mem_potentialGameSpace_iff_flowLinear_mem_range_grad]
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, (isExactPotential_ofPureEU_iff u φ).mpr ((flowLinear_eq_grad_iff u φ).mp hφ.symm)⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨φ, ((flowLinear_eq_grad_iff u φ).mpr ((isExactPotential_ofPureEU_iff u φ).mp hφ)).symm⟩

/-- **A game that is both a potential game and a harmonic game is nonstrategic.**
The two game classes meet exactly in the nonstrategic subspace. -/
theorem potentialGameSpace_inf_harmonicGameSpace [∀ i, Nonempty (S i)] :
    PotentialGameSpace ⊓ HarmonicGameSpace = NonstrategicSpace (S := S) := by
  apply le_antisymm
  · intro u hu
    obtain ⟨hup, huh⟩ := Submodule.mem_inf.mp hu
    rw [PotentialGameSpace, Submodule.mem_sup] at hup
    obtain ⟨p, hp, w1, hw1, hpw1⟩ := hup
    rw [HarmonicGameSpace, Submodule.mem_sup] at huh
    obtain ⟨h, hh, w2, hw2, hhw2⟩ := huh
    have hp_norm : p ∈ NormalizedSpace := ((mem_potentialComponentSpace_iff p).mp hp).1
    have hh_norm : h ∈ NormalizedSpace := ((mem_harmonicComponentSpace_iff h).mp hh).1
    have hnp : normalize u = p := by
      rw [← hpw1, map_add, normalize_of_mem_normalizedSpace hp_norm,
        normalize_of_mem_nonstrategicSpace hw1, add_zero]
    have hnh : normalize u = h := by
      rw [← hhw2, map_add, normalize_of_mem_normalizedSpace hh_norm,
        normalize_of_mem_nonstrategicSpace hw2, add_zero]
    have hp0 : p = 0 :=
      (Submodule.disjoint_def.mp potentialComponent_disjoint_harmonicComponent) p hp
        ((hnp.symm.trans hnh) ▸ hh)
    have husub : u = u - normalize u := by rw [hnp, hp0, sub_zero]
    rw [husub]; exact sub_normalize_mem_nonstrategicSpace u
  · exact le_inf le_sup_right le_sup_right

end Full

/-! ### Sanity examples

`rockPaperScissors` is a harmonic game and the coordination game is a potential
game, each certified through its component-space membership. A fully explicit
`decomposition` triple for a concrete game is not exhibited here: the two class
memberships already pin the two nontrivial components, and RPS is normalized with
no nonstrategic part so its harmonic component is itself. -/

/-- Rock–paper–scissors is a harmonic game. -/
example : rpsGame ∈ HarmonicGameSpace :=
  (isHarmonic_iff_mem_harmonicGameSpace rpsGame).mp rps_isHarmonic

/-- The two-player coordination potential: both players score `1` when they agree. -/
def coordPot : (∀ _ : Fin 2, Bool) → ℝ := fun σ => if σ 0 = σ 1 then 1 else 0

/-- The coordination game — every player's utility is the agreement indicator
`coordPot` — is a potential game, via the exact-potential bridge with potential
`coordPot`. -/
example : gamifyPotential coordPot ∈ PotentialGameSpace :=
  (mem_potentialGameSpace_iff_isExactPotential (gamifyPotential coordPot)).mpr
    ⟨coordPot, gamifyPotential_isExactPotential coordPot⟩

end GameTheory.FlowDecomposition
