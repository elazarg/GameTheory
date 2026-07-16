/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Potential.Flow
import GameTheory.Concepts.Mixed.MixedExtension

/-!
# Harmonic games

The **harmonic layer** of the Candogan–Menache–Ozdaglar–Parrilo decomposition
(*Flows and Decompositions of Games: Harmonic and Potential Games*,
Math. Oper. Res. 2011). A finite game `u : (∀ i, S i) → Payoff ι` is **harmonic**
when its unilateral flow is **divergence-free** on the game graph.

Instantiating the weighted-incidence spine (`Math/LinearAlgebra/WeightedIncidence`)
at the game edge space with **uniform** edge weights, this file defines:

- `gameDiv` — the graph divergence of the flow, and `IsHarmonic` — its vanishing;
- `isHarmonic_iff_sum_flow` — the paper's characterization: at every profile the
  total flow out of each player, summed over players, vanishes;
- `isHarmonic_iff_of_normalized` — for normalized games the divergence-free
  condition is the weighted identity `∑ₘ (card (S m)) · uₘ = 0`;
- `rockPaperScissors` — generalized rock–paper–scissors, harmonic with no pure
  Nash equilibrium, and its uniformly mixed Nash equilibrium;
- `asymHarmonic` — an unequal-size (`2 × 3`) normalized harmonic game, the
  discriminating witness for the strategy-count weights;
- `uniformlyMixed_nash_of_harmonic` — the uniformly mixed profile is a mixed Nash
  equilibrium of any harmonic game.

The strategy-count factors `hₘ = card (S m)` are **not** edge weights (the graph
divergence is unweighted); they emerge in the utility-space identity above.
-/

open Finset BigOperators
open Math.LinearAlgebra.WeightedIncidence

namespace GameTheory.FlowDecomposition

variable {ι : Type} [DecidableEq ι] {S : ι → Type}

/-! ### Divergence and harmonicity -/

/-- The flow of a self-deviation vanishes. -/
theorem flow_self (u : (∀ i, S i) → Payoff ι) (σ : ∀ i, S i) (i : ι) :
    flow u σ i (σ i) = 0 := by
  simp [flow, Function.update_eq_self]

section Divergence

variable [Fintype ι] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The **graph divergence** of a game's flow: the weighted-incidence divergence of
`flowLinear u` on the game graph with **uniform** edge weights. -/
noncomputable def gameDiv (u : (∀ i, S i) → Payoff ι) : (∀ i, S i) → ℝ :=
  div edgeSrc edgeTgt (fun _ => 1) (flowLinear u)

/-- A game is **harmonic** when its unilateral flow is divergence-free. -/
def IsHarmonic (u : (∀ i, S i) → Payoff ι) : Prop := gameDiv u = 0

/-- **Outflow reindex.** The flow out of profile `a` — over edges whose source is
`a`, hence with base `a` and summand `flow u a i s'` directly — is the total
unilateral flow of every player at `a`. -/
theorem sum_edgeSrc_flowLinear (u : (∀ i, S i) → Payoff ι) (a : ∀ i, S i) :
    ∑ e : GameEdge S, (if a = edgeSrc e then flowLinear u e else 0)
      = ∑ i, ∑ s' : S i, flow u a i s' := by
  rw [← Finset.sum_filter]
  have hrhs : (∑ i, ∑ s' : S i, flow u a i s')
      = ∑ x ∈ Finset.univ.sigma (fun i => (Finset.univ.erase (a i))),
          flow u a x.1 x.2 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Finset.sum_erase _ (flow_self u a i)).symm
  rw [hrhs]
  refine Finset.sum_bij'
    (fun e _ => (⟨e.player, e.dev⟩ : Σ i, S i))
    (fun x hx => (⟨a, x.1, x.2, (Finset.mem_erase.mp (Finset.mem_sigma.mp hx).2).1⟩ : GameEdge S))
    (fun e he => ?_) (fun x hx => ?_) (fun e he => ?_) (fun x hx => ?_) (fun e he => ?_)
  · -- i maps into the sigma set
    have hbase : a = e.base := (Finset.mem_filter.mp he).2
    refine Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
    rw [hbase]; exact e.dev_ne
  · -- j maps into the filter set
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · -- left inverse
    have hbase : a = e.base := (Finset.mem_filter.mp he).2
    obtain ⟨base, player, dev, dev_ne⟩ := e
    simp only at hbase
    subst hbase
    rfl
  · -- right inverse
    rfl
  · -- values agree
    have hbase : a = e.base := (Finset.mem_filter.mp he).2
    simp only [flowLinear_apply, ← hbase]

/-- **Inflow reindex.** On the alternating game flow the inflow into `a` is the
negated outflow (reverse each edge), hence minus the total unilateral flow at `a`. -/
theorem sum_edgeTgt_flowLinear (u : (∀ i, S i) → Payoff ι) (a : ∀ i, S i) :
    ∑ e : GameEdge S, (if a = edgeTgt e then flowLinear u e else 0)
      = -∑ i, ∑ s' : S i, flow u a i s' := by
  rw [← sum_edgeSrc_flowLinear u a, ← Finset.sum_neg_distrib,
    ← Equiv.sum_comp edgeRev_involutive.toPerm
      (fun e => if a = edgeTgt e then flowLinear u e else 0)]
  refine Finset.sum_congr rfl fun e _ => ?_
  have halt : flowLinear u (edgeRev e) = - flowLinear u e :=
    flowLinear_mem_alternatingFlow u e
  simp only [Function.Involutive.coe_toPerm, edgeTgt_edgeRev, halt]
  split_ifs <;> ring

/-- **The graph divergence of the flow**, in closed form: `−2` times the total
unilateral flow of every player at the profile. Uniform edge weights; the factor
`−2` is the doubling of the cut/cycle split on alternating flows. -/
theorem gameDiv_apply (u : (∀ i, S i) → Payoff ι) (a : ∀ i, S i) :
    gameDiv u a = -2 * ∑ i, ∑ s' : S i, flow u a i s' := by
  rw [gameDiv, div_apply_of_mem_alternatingFlow edgeSrc edgeTgt (fun _ => 1) edgeRev
    edgeRev_involutive edgeSrc_edgeRev (fun _ => rfl) (flowLinear_mem_alternatingFlow u)]
  simp only [one_mul]
  rw [sum_edgeTgt_flowLinear]
  ring

/-- **The paper's characterization of harmonicity.** A game is harmonic exactly
when at every profile the total unilateral flow, summed over all players and all
of each player's strategies, vanishes. (Self-deviation terms are zero, so summing
over all strategies is the same as over the deviations.) -/
theorem isHarmonic_iff_sum_flow (u : (∀ i, S i) → Payoff ι) :
    IsHarmonic u ↔ ∀ σ : ∀ i, S i, ∑ i, ∑ s' : S i, flow u σ i s' = 0 := by
  rw [IsHarmonic, funext_iff]
  refine forall_congr' fun a => ?_
  rw [gameDiv_apply, Pi.zero_apply, mul_eq_zero]
  constructor
  · rintro (h | h)
    · norm_num at h
    · exact h
  · intro h; exact Or.inr h

/-- **The normalized-harmonic identity** (the paper's `∑ₘ hₘ uₘ = 0`). For a
normalized game — every player's per-context utilities summing to zero —
harmonicity is exactly the pointwise vanishing of the strategy-count-weighted
sum of payoffs, where the weight of player `m` is `hₘ = card (S m)`. This is where
the strategy-count factors enter; they are *not* the (uniform) graph edge weights. -/
theorem isHarmonic_iff_of_normalized (u : (∀ i, S i) → Payoff ι)
    (hu : u ∈ NormalizedSpace) :
    IsHarmonic u ↔ ∀ σ : ∀ i, S i, ∑ i, (Fintype.card (S i) : ℝ) * u σ i = 0 := by
  rw [isHarmonic_iff_sum_flow]
  refine forall_congr' fun σ => ?_
  have key : ∀ i, ∑ s' : S i, flow u σ i s' = -((Fintype.card (S i) : ℝ) * u σ i) := by
    intro i
    have hz : ∑ s' : S i, u (Function.update σ i s') i = 0 := hu i σ
    simp only [flow, Finset.sum_sub_distrib, hz, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  simp only [key, Finset.sum_neg_distrib, neg_eq_zero]

/-! ### Harmonicity is a linear, nonstrategic-blind predicate -/

/-- The graph divergence as a linear map: `div` of the flow. Its kernel is the
space of harmonic games. -/
noncomputable def gameDivLinear : ((∀ i, S i) → Payoff ι) →ₗ[ℝ] ((∀ i, S i) → ℝ) :=
  (div edgeSrc edgeTgt (fun _ => 1)).comp flowLinear

@[simp] lemma gameDivLinear_apply (u : (∀ i, S i) → Payoff ι) :
    gameDivLinear u = gameDiv u := rfl

theorem gameDiv_add (u v : (∀ i, S i) → Payoff ι) :
    gameDiv (u + v) = gameDiv u + gameDiv v := by
  simp only [← gameDivLinear_apply, map_add]

theorem gameDiv_smul (c : ℝ) (u : (∀ i, S i) → Payoff ι) :
    gameDiv (c • u) = c • gameDiv u := by
  simp only [← gameDivLinear_apply, map_smul]

/-- A nonstrategic game has zero flow, hence zero divergence. -/
theorem gameDiv_of_mem_nonstrategic {w : (∀ i, S i) → Payoff ι}
    (hw : w ∈ NonstrategicSpace) : gameDiv w = 0 := by
  rw [← gameDivLinear_apply, gameDivLinear, LinearMap.comp_apply,
    (mem_nonstrategicSpace_iff_flowLinear_eq_zero w).mp hw, map_zero]

theorem IsHarmonic.add {u v : (∀ i, S i) → Payoff ι}
    (hu : IsHarmonic u) (hv : IsHarmonic v) : IsHarmonic (u + v) := by
  rw [IsHarmonic, gameDiv_add, hu, hv, add_zero]

theorem IsHarmonic.smul {u : (∀ i, S i) → Payoff ι} (c : ℝ)
    (hu : IsHarmonic u) : IsHarmonic (c • u) := by
  rw [IsHarmonic, gameDiv_smul, hu, smul_zero]

/-- **Harmonicity is nonstrategic-blind**: adding a nonstrategic component (one
with vanishing flow) preserves harmonicity, because it does not move the flow. -/
theorem IsHarmonic.add_nonstrategic {u w : (∀ i, S i) → Payoff ι}
    (hu : IsHarmonic u) (hw : w ∈ NonstrategicSpace) : IsHarmonic (u + w) := by
  rw [IsHarmonic, gameDiv_add, hu, gameDiv_of_mem_nonstrategic hw, add_zero]

/-- The divergence is invariant under normalization: normalizing does not move the
flow. -/
theorem gameDiv_normalize (u : (∀ i, S i) → Payoff ι) :
    gameDiv (normalize u) = gameDiv u := by
  rw [← gameDivLinear_apply, ← gameDivLinear_apply, gameDivLinear,
    LinearMap.comp_apply, LinearMap.comp_apply, flowLinear_normalize]

/-- Harmonicity is invariant under normalization (both directions): the normalized
representative is harmonic iff the game is. -/
theorem isHarmonic_normalize_iff (u : (∀ i, S i) → Payoff ι) :
    IsHarmonic (normalize u) ↔ IsHarmonic u := by
  rw [IsHarmonic, IsHarmonic, gameDiv_normalize]

end Divergence

/-! ### Acceptance example A: rock–paper–scissors -/

section RockPaperScissors

/-- Rock–paper–scissors payoff to the row player: `+1` for a win (`a = b + 1` on
`Fin 3`: rock beats scissors, paper beats rock, scissors beats paper), `-1` for a
loss, `0` for a tie. -/
def rpsPayoff (a b : Fin 3) : ℝ := if a = b then 0 else if a = b + 1 then 1 else -1

/-- **Generalized rock–paper–scissors**: two players, three strategies each,
zero-sum (the column player receives the negated row payoff). -/
def rpsGame : (Fin 2 → Fin 3) → Payoff (Fin 2) :=
  fun σ i => if i = 0 then rpsPayoff (σ 0) (σ 1) else - rpsPayoff (σ 0) (σ 1)

/-- Every column of the rock–paper–scissors payoff sums to zero (win, loss, tie). -/
lemma rpsPayoff_col_sum (b : Fin 3) : ∑ a : Fin 3, rpsPayoff a b = 0 := by
  fin_cases b <;> simp [rpsPayoff, Fin.sum_univ_three]

/-- Every row of the rock–paper–scissors payoff sums to zero. -/
lemma rpsPayoff_row_sum (a : Fin 3) : ∑ b : Fin 3, rpsPayoff a b = 0 := by
  fin_cases a <;> simp [rpsPayoff, Fin.sum_univ_three]

/-- Player 0's payoff when unilaterally deviating to `s` is the row payoff `s`
against the opponent. -/
lemma rpsGame_update_zero (σ : Fin 2 → Fin 3) (s : Fin 3) :
    rpsGame (Function.update σ 0 s) 0 = rpsPayoff s (σ 1) := by
  simp [rpsGame]

/-- Player 1's payoff when unilaterally deviating to `s` is the negated column
payoff of the opponent against `s`. -/
lemma rpsGame_update_one (σ : Fin 2 → Fin 3) (s : Fin 3) :
    rpsGame (Function.update σ 1 s) 1 = - rpsPayoff (σ 0) s := by
  simp [rpsGame]

/-- Rock–paper–scissors is normalized: each player's payoffs sum to zero across
their own strategies in every context. -/
theorem rps_mem_normalizedSpace : rpsGame ∈ NormalizedSpace := by
  intro i σ
  fin_cases i
  · change ∑ s : Fin 3, rpsGame (Function.update σ 0 s) 0 = 0
    simp only [rpsGame_update_zero]
    exact rpsPayoff_col_sum (σ 1)
  · change ∑ s : Fin 3, rpsGame (Function.update σ 1 s) 1 = 0
    simp only [rpsGame_update_one, Finset.sum_neg_distrib, rpsPayoff_row_sum, neg_zero]

/-- Beating the opponent (playing one above their strategy) scores `1`. -/
lemma rpsPayoff_beat (b : Fin 3) : rpsPayoff (b + 1) b = 1 := by
  fin_cases b <;> simp [rpsPayoff]

/-- Being beaten (the opponent plays one above) scores `-1`. -/
lemma rpsPayoff_lose (a : Fin 3) : rpsPayoff a (a + 1) = -1 := by
  fin_cases a <;> simp [rpsPayoff]

/-- **Rock–paper–scissors is harmonic.** -/
theorem rps_isHarmonic : IsHarmonic rpsGame := by
  rw [isHarmonic_iff_of_normalized rpsGame rps_mem_normalizedSpace]
  intro σ
  simp only [Fin.sum_univ_two, Fintype.card_fin, rpsGame, Fin.isValue, if_true,
    one_ne_zero, if_false]
  ring

/-- **Rock–paper–scissors has no pure Nash equilibrium.** Against any pure profile,
playing one strategy above the opponent forces the row payoff to be at least `1`,
while the column player symmetrically forces it to be at most `-1`: no profile can
satisfy both. -/
theorem rps_no_pure_nash (σ : Fin 2 → Fin 3) :
    ¬ (KernelGame.ofPureEU (fun _ : Fin 2 => Fin 3) rpsGame).IsNash σ := by
  intro hN
  have h0 := hN 0 ((σ 1 + 1 : Fin 3))
  have h1 := hN 1 ((σ 0 + 1 : Fin 3))
  simp only [KernelGame.eu_ofPureEU, rpsGame, Fin.isValue, Function.update_self,
    Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide),
    Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), one_ne_zero, if_true, if_false]
    at h0 h1
  rw [rpsPayoff_beat] at h0
  rw [rpsPayoff_lose] at h1
  linarith

end RockPaperScissors

/-! ### Acceptance example B: an unequal-size (`2 × 3`) harmonic game

The discriminating witness for the strategy-count weights: `card (S true) = 2` and
`card (S false) = 3`, so the normalized-harmonic identity `∑ₘ hₘ uₘ = 0` reads
`2 · u_true + 3 · u_false = 0` — which pins the factor placement RPS (with equal
sizes) cannot. -/

section AsymmetricHarmonic

/-- Heterogeneous strategy space: the row player has two strategies, the column
player three. -/
abbrev asymS : Bool → Type
  | true => Fin 2
  | false => Fin 3

instance (b : Bool) : Fintype (asymS b) := by cases b <;> exact inferInstance
instance (b : Bool) : DecidableEq (asymS b) := by cases b <;> exact inferInstance
instance (b : Bool) : Nonempty (asymS b) := by cases b <;> exact inferInstance

/-- Row player's payoff table (player `true`). Per-column zero-mean over the two
rows; the column weight `-6` at `b = 2` balances the two `3`s. -/
def asymRow (a : Fin 2) (b : Fin 3) : ℝ := (if a = 0 then 1 else -1) * (if b = 2 then -6 else 3)

/-- Column player's payoff table (player `false`), chosen so `2·row + 3·col = 0`
pointwise: it is `-(2/3)` times the row table. Per-row zero-mean over the three
columns. -/
def asymCol (a : Fin 2) (b : Fin 3) : ℝ := (if a = 0 then 1 else -1) * (if b = 2 then 4 else -2)

/-- The `2 × 3` harmonic game: zero-sum-like balance `2·u_true + 3·u_false = 0`. -/
def asymGame : (∀ b : Bool, asymS b) → Payoff Bool :=
  fun σ p => if p then asymRow (σ true) (σ false) else asymCol (σ true) (σ false)

/-- The strategy-count-weighted balance identity, pointwise: `2·row + 3·col = 0`.
This is the exact convention the design predicts (`hₘ = card (S m)` multiplying the
payoff), verified numerically. -/
lemma asym_balance (a : Fin 2) (b : Fin 3) : 2 * asymRow a b + 3 * asymCol a b = 0 := by
  fin_cases a <;> fin_cases b <;> simp [asymRow, asymCol] <;> norm_num

/-- Each column of the row table sums to zero over the two rows. -/
lemma asymRow_col_sum (b : Fin 3) : ∑ a : Fin 2, asymRow a b = 0 := by
  simp [asymRow, Fin.sum_univ_two]

/-- Each row of the column table sums to zero over the three columns. -/
lemma asymCol_row_sum (a : Fin 2) : ∑ b : Fin 3, asymCol a b = 0 := by
  fin_cases a <;> simp [asymCol, Fin.sum_univ_three] <;> norm_num

lemma asym_card_true : Fintype.card (asymS true) = 2 := rfl
lemma asym_card_false : Fintype.card (asymS false) = 3 := rfl

/-- Row player's payoff under a unilateral deviation to `s`. -/
lemma asymGame_update_true (σ : ∀ b, asymS b) (s : Fin 2) :
    asymGame (Function.update σ true s) true = asymRow s (σ false) := by
  simp [asymGame]

/-- Column player's payoff under a unilateral deviation to `s`. -/
lemma asymGame_update_false (σ : ∀ b, asymS b) (s : Fin 3) :
    asymGame (Function.update σ false s) false = asymCol (σ true) s := by
  simp [asymGame]

/-- The `2 × 3` game is normalized: each player's payoffs sum to zero across their
own strategies in every context. -/
theorem asym_mem_normalizedSpace : asymGame ∈ NormalizedSpace := by
  intro i σ
  cases i
  · change ∑ s : Fin 3, asymGame (Function.update σ false s) false = 0
    simp only [asymGame_update_false]
    exact asymCol_row_sum (σ true)
  · change ∑ s : Fin 2, asymGame (Function.update σ true s) true = 0
    simp only [asymGame_update_true]
    exact asymRow_col_sum (σ false)

/-- **The `2 × 3` game is harmonic.** Via the normalized characterization, this is
exactly the balance `2·row + 3·col = 0` with weights `card (S true) = 2`,
`card (S false) = 3`. -/
theorem asym_isHarmonic : IsHarmonic asymGame := by
  rw [isHarmonic_iff_of_normalized asymGame asym_mem_normalizedSpace]
  intro σ
  rw [Fintype.sum_bool, asym_card_true, asym_card_false]
  simp only [asymGame, Bool.false_eq_true, if_false, if_true]
  push_cast
  linarith [asym_balance (σ true) (σ false)]

end AsymmetricHarmonic

/-! ### The uniformly mixed equilibrium of a harmonic game -/

section UniformNash

variable [Fintype ι] [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- Total payoff of player `who` summed over all profiles whose own coordinate is
`a` (the "column sum" for `who` at `a`). -/
def colSum (u : (∀ i, S i) → Payoff ι) (who : ι) (a : S who) : ℝ :=
  ∑ s : (∀ i, S i), if s who = a then u s who else 0

/-- The involution on `(profile, spare strategy)` pairs that swaps player `i`'s
played strategy with the spare one: `(σ, s') ↦ (update σ i s', σ i)`. It reindexes
the fiber sums driving the harmonic balance identity. -/
def updateSwap (i : ι) : ((∀ j, S j) × S i) ≃ ((∀ j, S j) × S i) where
  toFun p := (Function.update p.1 i p.2, p.1 i)
  invFun p := (Function.update p.1 i p.2, p.1 i)
  left_inv p := by
    obtain ⟨σ, s'⟩ := p
    simp only [Function.update_idem, Function.update_self, Function.update_eq_self]
  right_inv p := by
    obtain ⟨σ, s'⟩ := p
    simp only [Function.update_idem, Function.update_self, Function.update_eq_self]

/-- The fiber reindex driven by `updateSwap`: summing over `(σ, s')` pairs, moving
player `i`'s deviation target `s'` into the played coordinate leaves the total
unchanged. -/
lemma updateSwap_reindex (u : (∀ i, S i) → Payoff ι) (who : ι) (a : S who) (i : ι) :
    ∑ p : (∀ j, S j) × S i,
        (if (Function.update p.1 i p.2) who = a then u (Function.update p.1 i p.2) i else 0)
      = ∑ p : (∀ j, S j) × S i, (if p.1 who = a then u p.1 i else 0) :=
  Equiv.sum_comp (updateSwap i) (fun p => if p.1 who = a then u p.1 i else 0)

/-- **The harmonic balance identity.** In a harmonic game the column sum for any
player is proportional to the same total (independent of the chosen own strategy),
with the strategy count as the proportionality constant. This is the algebraic
heart of the uniformly-mixed equilibrium: summing the divergence-free condition
over all profiles with `who`'s coordinate fixed to `a`, the cross-player terms
telescope away and leave `hₐ · colSum = ∑ u`. -/
theorem card_mul_colSum (u : (∀ i, S i) → Payoff ι) (hu : IsHarmonic u)
    (who : ι) (a : S who) :
    (Fintype.card (S who) : ℝ) * colSum u who a = ∑ s : (∀ i, S i), u s who := by
  classical
  -- `A i` is the total, over profiles with `who`-coordinate `a`, of player `i`'s
  -- outgoing flow; harmonicity makes these sum to zero over players.
  set A : ι → ℝ :=
    fun i => ∑ σ : (∀ j, S j), if σ who = a then ∑ s' : S i, flow u σ i s' else 0 with hA_def
  have hsum0 : ∑ i, A i = 0 := by
    simp only [hA_def]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun σ _ => ?_
    by_cases h : σ who = a
    · simp only [if_pos h]; exact (isHarmonic_iff_sum_flow u).mp hu σ
    · simp only [if_neg h, Finset.sum_const_zero]
  -- `A i` splits into a "deviation" pair-sum minus a "played" pair-sum.
  have hAsplit : ∀ i, A i =
      (∑ p : (∀ j, S j) × S i, if p.1 who = a then u (Function.update p.1 i p.2) i else 0)
      - (∑ p : (∀ j, S j) × S i, if p.1 who = a then u p.1 i else 0) := by
    intro i
    have e1 : A i = ∑ p : (∀ j, S j) × S i, if p.1 who = a then flow u p.1 i p.2 else 0 := by
      simp only [hA_def]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases h : σ who = a <;> simp [h]
    rw [e1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : p.1 who = a <;> simp [h, flow]
  -- The "played" pair-sum is `card (S i)` times the profile-indicator sum.
  have hST : ∀ i, (∑ p : (∀ j, S j) × S i, if p.1 who = a then u p.1 i else 0)
      = (Fintype.card (S i) : ℝ) * ∑ σ : (∀ j, S j), if σ who = a then u σ i else 0 := by
    intro i
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  -- Off `who`, the deviation pair-sum equals the played one (reversal reindex).
  have hAi_zero : ∀ i, i ≠ who → A i = 0 := by
    intro i hi
    rw [hAsplit i]
    have hFT :
        (∑ p : (∀ j, S j) × S i, if p.1 who = a then u (Function.update p.1 i p.2) i else 0)
          = ∑ p : (∀ j, S j) × S i, if p.1 who = a then u p.1 i else 0 := by
      rw [← updateSwap_reindex u who a i]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Function.update_of_ne (Ne.symm hi) p.2 p.1]
    rw [hFT, sub_self]
  -- At `who`, the deviation pair-sum collapses to the grand total.
  have hFTwho :
      (∑ p : (∀ j, S j) × S who, if p.1 who = a then u (Function.update p.1 who p.2) who else 0)
        = ∑ s : (∀ i, S i), u s who := by
    rw [← Equiv.sum_comp (updateSwap who)
      (fun p : (∀ j, S j) × S who =>
        if p.1 who = a then u (Function.update p.1 who p.2) who else 0)]
    simp only [updateSwap, Equiv.coe_fn_mk, Function.update_self, Function.update_idem,
      Function.update_eq_self]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_ite_eq']
    simp
  -- Assemble: `∑ i, A i = A who`, and `A who = total - card·colSum`.
  have hAwho : A who
      = (∑ s : (∀ i, S i), u s who) - (Fintype.card (S who) : ℝ) * colSum u who a := by
    rw [hAsplit who, hFTwho, hST who, colSum]
  rw [Finset.sum_eq_single who (fun i _ hi => hAi_zero i hi)
    (fun h => absurd (Finset.mem_univ who) h), hAwho] at hsum0
  linarith

variable [∀ i, Nonempty (S i)]

/-- The product of the opponents' uniform weights `∏_{j ≠ who} (card (S j))⁻¹`. This
is the constant relating the uniform-opponents mixed expected utility of a pure
own strategy to its combinatorial column sum. -/
noncomputable def uniformWeight (S : ι → Type) [∀ i, Fintype (S i)] (who : ι) : ℝ :=
  ∏ i ∈ Finset.univ.erase who, (Fintype.card (S i) : ℝ)⁻¹

/-- The expected utility of player `who` playing pure `a` against uniform opponents
is `uniformWeight who` times the column sum for `who` at `a`. -/
theorem mixedEu_update_pure_eq (u : (∀ i, S i) → Payoff ι) (who : ι) (a : S who) :
    (KernelGame.ofPureEU S u).mixedExtension.eu
        (Function.update (fun i => PMF.uniformOfFintype (S i)) who (PMF.pure a)) who
      = uniformWeight S who * colSum u who a := by
  haveI : Finite ((KernelGame.ofPureEU S u).Outcome) := inferInstanceAs (Finite (∀ i, S i))
  letI : Fintype (∀ i, (KernelGame.ofPureEU S u).Strategy i) :=
    inferInstanceAs (Fintype (∀ i, S i))
  rw [KernelGame.mixedExtension_eu, Math.Probability.expect_eq_sum]
  have key :
      (∑ x, ((Math.PMFProduct.pmfPi
          (Function.update (fun i => PMF.uniformOfFintype (S i)) who (PMF.pure a))) x).toReal
            * (KernelGame.ofPureEU S u).eu x who)
        = uniformWeight S who * ∑ x, (if x who = a then u x who else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [KernelGame.eu_ofPureEU, Math.PMFProduct.pmfPi_apply_update_family, ENNReal.toReal_mul,
      ENNReal.toReal_prod, PMF.pure_apply, uniformWeight]
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    by_cases h : x who = a <;> simp [h]
  rw [colSum]
  exact key

/-- The column sum is independent of the chosen own strategy in a harmonic game
(both are proportional to the same total). -/
theorem colSum_const (u : (∀ i, S i) → Payoff ι) (hu : IsHarmonic u)
    (who : ι) (a b : S who) : colSum u who a = colSum u who b := by
  have hcard : (Fintype.card (S who) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact mul_left_cancel₀ hcard
    ((card_mul_colSum u hu who a).trans (card_mul_colSum u hu who b).symm)

/-- **The uniformly mixed profile is a mixed Nash equilibrium of any harmonic game.**
Against uniform opponents every pure strategy of a player yields the same expected
payoff (the harmonic balance identity), so no player can gain by deviating. The
hypothesis is purely flow-level, so this holds for arbitrary nonstrategic
components as well. -/
theorem uniformlyMixed_nash_of_harmonic (u : (∀ i, S i) → Payoff ι) (hu : IsHarmonic u) :
    (KernelGame.ofPureEU S u).mixedExtension.IsNash
      (fun i => PMF.uniformOfFintype (S i)) := by
  haveI : Finite ((KernelGame.ofPureEU S u).Outcome) := inferInstanceAs (Finite (∀ i, S i))
  set G := KernelGame.ofPureEU S u with hG
  have hgain : ∀ (who : ι) (a : S who),
      G.mixedGain (fun i => PMF.uniformOfFintype (S i)) who a = 0 := by
    intro who a
    have hDconst : ∀ b : S who,
        G.mixedGain (fun i => PMF.uniformOfFintype (S i)) who b
          = G.mixedGain (fun i => PMF.uniformOfFintype (S i)) who a := by
      intro b
      unfold KernelGame.mixedGain
      rw [mixedEu_update_pure_eq u who b, mixedEu_update_pure_eq u who a, colSum_const u hu who b a]
    have hz := G.weighted_gain_sum_zero (fun i => PMF.uniformOfFintype (S i)) who
    rw [show (fun b => G.mixedGain (fun i => PMF.uniformOfFintype (S i)) who b)
          = (fun _ => G.mixedGain (fun i => PMF.uniformOfFintype (S i)) who a)
        from funext hDconst, Math.Probability.expect_const] at hz
    exact hz
  rw [G.isNash_iff_gains_nonpos (fun i => PMF.uniformOfFintype (S i))]
  intro who a
  rw [hgain who a]

end UniformNash

/-- **The uniform profile is a Nash equilibrium of rock–paper–scissors** — the mixed
equilibrium that its lack of a pure one forces. An instance of the general theorem. -/
theorem rps_uniform_nash :
    (KernelGame.ofPureEU (fun _ : Fin 2 => Fin 3) rpsGame).mixedExtension.IsNash
      (fun i => PMF.uniformOfFintype ((fun _ : Fin 2 => Fin 3) i)) :=
  uniformlyMixed_nash_of_harmonic rpsGame rps_isHarmonic

/-- **The uniform profile is a Nash equilibrium of the `2 × 3` harmonic game.** An
instance of the general theorem, with unequal strategy-set sizes. -/
theorem asym_uniform_nash :
    (KernelGame.ofPureEU asymS asymGame).mixedExtension.IsNash
      (fun i => PMF.uniformOfFintype (asymS i)) :=
  uniformlyMixed_nash_of_harmonic asymGame asym_isHarmonic

/-! ### Zero-sum does not imply harmonic

Matching pennies is both zero-sum and harmonic, but this is a special feature of
its payoff table (each player's payoff depends only on whether the two actions
agree), not a consequence of zero-sum alone. A generic zero-sum `2 × 2` table is
a machine-checked counterexample to "zero-sum ⇒ harmonic". -/

section ZeroSumNotHarmonic

/-- An arbitrary payoff table on `Fin 2 × Fin 2`, with no special structure. -/
def zsWitness : Fin 2 → Fin 2 → ℝ
  | 0, 0 => 1
  | 1, 0 => 2
  | 0, 1 => 3
  | 1, 1 => 4

/-- The zero-sum game built from `zsWitness`: player `1`'s payoff is the negation
of player `0`'s. -/
def zsGame : (Fin 2 → Fin 2) → Payoff (Fin 2) :=
  fun σ i => if i = 0 then zsWitness (σ 0) (σ 1) else - zsWitness (σ 0) (σ 1)

/-- `zsGame` is zero-sum at every profile. -/
theorem zsGame_isZeroSum (σ : Fin 2 → Fin 2) : zsGame σ 0 + zsGame σ 1 = 0 := by
  simp [zsGame]

theorem zsGame_update_zero (σ : Fin 2 → Fin 2) (s : Fin 2) :
    zsGame (Function.update σ 0 s) 0 = zsWitness s (σ 1) := by
  simp [zsGame]

theorem zsGame_update_one (σ : Fin 2 → Fin 2) (s : Fin 2) :
    zsGame (Function.update σ 1 s) 1 = - zsWitness (σ 0) s := by
  simp [zsGame]

/-- **Zero-sum does not imply harmonic.** A generic `2 × 2` zero-sum game need not
be divergence-free: `zsGame` violates the harmonic balance at `σ = (0, 0)`, where
player `0`'s outgoing flow is `1` and player `1`'s is `-2`, summing to `-1 ≠ 0`. -/
theorem zsGame_not_isHarmonic : ¬ IsHarmonic zsGame := by
  rw [isHarmonic_iff_sum_flow]
  push Not
  refine ⟨![0, 0], ?_⟩
  have h0 : ∑ s' : Fin 2, flow zsGame ![0, 0] 0 s' = 1 := by
    rw [Fin.sum_univ_two]
    simp only [flow, zsGame, zsWitness]
    norm_num
  have h1 : ∑ s' : Fin 2, flow zsGame ![0, 0] 1 s' = -2 := by
    rw [Fin.sum_univ_two]
    simp only [flow, zsGame, zsWitness]
    norm_num
  rw [Fin.sum_univ_two, h0, h1]
  norm_num

end ZeroSumNotHarmonic

end GameTheory.FlowDecomposition
