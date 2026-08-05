/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ChargedPathBudget
import Math.PMFProduct.CoalitionMass
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Fin.VecNotation

/-!
# Sharpness of the path-budget / bounded-potential duality

Three explicit charged relations delimiting `Math.ChargedPathBudget`.

## Towers

`Towers.relation` is a countable charged relation whose `k`-th component is a
finite chain of `k` unit-charge edges.  Every finite path has finite charge, every
path has length at most its component index (so there is no infinite path at all),
and from each state the reachable charges are bounded.  The budget is nevertheless
infinite, so no bounded potential exists.  Pointwise finiteness of the budget-to-go
is therefore strictly weaker than a uniform budget.

## Continuous incompleteness

`Interpolation.relation` is a charged relation on the plane whose edges all live in
the compact unit square.  Its budget is exactly one, witnessed by an exact bounded
potential; but every potential for it — bounded or not — fails to be continuous at
the origin.  So exact potentials cannot in general be chosen continuous, even for a
relation supported on a compact set and of small budget.

## Quit-bonus calibration

`QuitBonus` is an arithmetic calibration for two-player quitting-style value
updates.  For the table `w {1} = (a, 0)`, `w {2} = (1, -1)`, `w {1,2} = (0, 1)`,
the value vector `v = (a, 0)` and the row `x = (1/2, 0)` (the first player quits
with probability one half, the second continues surely), the one-stage update fixes
`v` exactly, with continuation mass `1/2` and hence quitting charge `1/2 > 0`.  This
is an exact positive-charge self-loop, so the corresponding charged relation admits
no bounded potential of any kind.
-/

namespace Math
namespace ChargedPathBudget

open ChargedRelation

-- ============================================================================
-- Towers: every path is finite, yet the budget is infinite
-- ============================================================================

namespace Towers

/-- Edges of the towers relation.  The edge indexed by `(k, i)` with `i < k` is the
`i`-th step of the `k`-th tower. -/
abbrev Edge : Type := {p : ℕ × ℕ // p.2 < p.1}

/-- The towers relation: the `k`-th component is a chain of `k` unit-charge edges
`(k, 0) → (k, 1) → ⋯ → (k, k)`. -/
def relation : ChargedRelation (ℕ × ℕ) Towers.Edge where
  src e := e.1
  tgt e := (e.1.1, e.1.2 + 1)
  charge _ := 1
  charge_nonneg _ := zero_le_one

@[simp] theorem relation_src_fst (e : Edge) : (relation.src e).1 = e.1.1 := rfl

@[simp] theorem relation_src_snd (e : Edge) : (relation.src e).2 = e.1.2 := rfl

@[simp] theorem relation_tgt_fst (e : Edge) : (relation.tgt e).1 = e.1.1 := rfl

@[simp] theorem relation_tgt_snd (e : Edge) : (relation.tgt e).2 = e.1.2 + 1 := rfl

@[simp] theorem relation_charge (e : Edge) : relation.charge e = 1 := rfl

/-- Every path stays inside one tower, its endpoint stays below the tower height,
and its charge is the height gained. -/
theorem path_invariant {s t : ℕ × ℕ} (p : relation.Path s t) :
    t.1 = s.1 ∧ t.2 ≤ max s.2 s.1 ∧ p.chargeSum = (t.2 : ℝ) - s.2 := by
  induction p with
  | nil s => simp
  | cons e rest ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have he : e.1.2 < e.1.1 := e.2
      simp only [relation_tgt_fst, relation_tgt_snd] at h1 h2 h3
      refine ⟨by simpa using h1, ?_, ?_⟩
      · simp only [relation_src_fst, relation_src_snd]
        omega
      · rw [Path.chargeSum_cons, relation_charge, h3]
        simp only [relation_src_snd]
        push_cast
        ring

/-- Every path has length equal to its charge. -/
theorem length_eq_chargeSum {s t : ℕ × ℕ} (p : relation.Path s t) :
    (p.length : ℝ) = p.chargeSum := by
  induction p with
  | nil s => simp
  | cons e rest ih =>
      rw [Path.length_cons, Path.chargeSum_cons, relation_charge, ← ih]
      push_cast
      ring

/-- Path lengths from a fixed state are uniformly bounded: the towers relation has
no infinite path. -/
theorem length_le {s t : ℕ × ℕ} (p : relation.Path s t) : p.length ≤ max s.2 s.1 := by
  obtain ⟨_, h2, h3⟩ := path_invariant p
  have hlen : (p.length : ℝ) = (t.2 : ℝ) - s.2 := by rw [length_eq_chargeSum, h3]
  have hcast : (p.length : ℝ) ≤ (max s.2 s.1 : ℝ) := by
    have h4 : (t.2 : ℝ) ≤ (max s.2 s.1 : ℝ) := by exact_mod_cast h2
    have h5 : (0 : ℝ) ≤ (s.2 : ℝ) := Nat.cast_nonneg _
    rw [hlen]
    linarith
  exact_mod_cast hcast

/-- From each individual state the reachable charges are bounded: the budget-to-go
is finite at every state. -/
theorem bddAbove_chargesFrom (s : ℕ × ℕ) : BddAbove (relation.chargesFrom s) := by
  refine ⟨(max s.2 s.1 : ℝ) - s.2, ?_⟩
  rintro x ⟨t, p, rfl⟩
  obtain ⟨_, h2, h3⟩ := path_invariant p
  have h4 : (t.2 : ℝ) ≤ (max s.2 s.1 : ℝ) := by exact_mod_cast h2
  rw [h3]
  linarith

/-- The `k`-th tower carries a path of charge `k`. -/
theorem exists_chain (k : ℕ) :
    ∀ i, i ≤ k → ∃ p : relation.Path (k, 0) (k, i), p.chargeSum = (i : ℝ) := by
  intro i
  induction i with
  | zero => exact fun _ => ⟨Path.nil _, by simp⟩
  | succ i ih =>
      intro h
      obtain ⟨p, hp⟩ := ih (by omega)
      refine ⟨p.append (Path.edge (R := relation) ⟨(k, i), by omega⟩ rfl rfl), ?_⟩
      rw [Path.chargeSum_append, hp, Path.chargeSum_edge, relation_charge]
      push_cast
      ring

/-- **Towers counterexample.**  Every path is finite and every state has a finite
budget-to-go, yet the budget is infinite. -/
theorem not_hasFiniteBudget : ¬ relation.HasFiniteBudget := by
  rintro ⟨M, hM⟩
  obtain ⟨k, hk⟩ := exists_nat_gt M
  obtain ⟨p, hp⟩ := exists_chain k k le_rfl
  have hle : p.chargeSum ≤ M := hM (relation.mem_pathCharges p)
  rw [hp] at hle
  linarith

/-- Consequently the towers relation has no bounded potential. -/
theorem no_boundedPotential :
    ¬ ∃ Φ : ℕ × ℕ → ℝ, relation.IsBoundedPotential Φ := by
  rw [← relation.hasFiniteBudget_iff_exists_boundedPotential]
  exact not_hasFiniteBudget

end Towers

-- ============================================================================
-- Continuous incompleteness: budget one, but no continuous potential
-- ============================================================================

namespace Interpolation

/-- Edges of the interpolation relation: from `(t, y)` with `0 < t ≤ 1` and
`t ^ 2 ≤ y ≤ t`, a step of charge `t` down to `(t, y - t ^ 2)`. -/
abbrev Edge : Type :=
  {p : ℝ × ℝ // 0 < p.1 ∧ p.1 ≤ 1 ∧ p.1 ^ 2 ≤ p.2 ∧ p.2 ≤ p.1}

/-- The interpolation relation: `(t, y) → (t, y - t ^ 2)` with charge `t`. -/
def relation : ChargedRelation (ℝ × ℝ) Interpolation.Edge where
  src e := e.1
  tgt e := (e.1.1, e.1.2 - e.1.1 ^ 2)
  charge e := e.1.1
  charge_nonneg e := le_of_lt e.2.1

@[simp] theorem relation_src (e : Edge) : relation.src e = e.1 := rfl

@[simp] theorem relation_tgt (e : Edge) :
    relation.tgt e = (e.1.1, e.1.2 - e.1.1 ^ 2) := rfl

@[simp] theorem relation_charge (e : Edge) : relation.charge e = e.1.1 := rfl

/-- The exact potential: on the region carrying edges it is `y / t`, clamped to
`[0, 1]` elsewhere so that it is globally bounded. -/
noncomputable def exactPotential (q : ℝ × ℝ) : ℝ := max 0 (min 1 (q.2 / q.1))

theorem exactPotential_mem_Icc (q : ℝ × ℝ) : exactPotential q ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- On an edge source the clamped potential is exactly `y / t`. -/
theorem exactPotential_src (e : Edge) : exactPotential (relation.src e) = e.1.2 / e.1.1 := by
  obtain ⟨ht0, ht1, hsq, hle⟩ := e.2
  have hratio : e.1.2 / e.1.1 ≤ 1 := (div_le_one ht0).2 hle
  have hnn : 0 ≤ e.1.2 / e.1.1 := div_nonneg (le_trans (sq_nonneg _) hsq) ht0.le
  simp only [relation_src, exactPotential, min_eq_right hratio, max_eq_right hnn]

/-- On an edge target the clamped potential is exactly `y / t - t`. -/
theorem exactPotential_tgt (e : Edge) :
    exactPotential (relation.tgt e) = e.1.2 / e.1.1 - e.1.1 := by
  obtain ⟨ht0, ht1, hsq, hle⟩ := e.2
  have htne : e.1.1 ≠ 0 := ne_of_gt ht0
  have hsqnn : (0 : ℝ) ≤ e.1.1 ^ 2 := sq_nonneg _
  have hkey : (e.1.2 - e.1.1 ^ 2) / e.1.1 = e.1.2 / e.1.1 - e.1.1 := by
    field_simp
  have hlow : 0 ≤ e.1.2 / e.1.1 - e.1.1 := by
    rw [← hkey]
    exact div_nonneg (by linarith) ht0.le
  have hhigh : e.1.2 / e.1.1 - e.1.1 ≤ 1 := by
    rw [← hkey, div_le_one ht0]
    linarith
  simp only [relation_tgt, exactPotential]
  rw [hkey, min_eq_right hhigh, max_eq_right hlow]

theorem exactPotential_isBoundedPotential :
    relation.IsBoundedPotential exactPotential where
  bddAbove := ⟨1, by
    rintro x ⟨q, rfl⟩
    exact (exactPotential_mem_Icc q).2⟩
  bddBelow := ⟨0, by
    rintro x ⟨q, rfl⟩
    exact (exactPotential_mem_Icc q).1⟩
  isPotential := by
    intro e
    rw [exactPotential_src e, exactPotential_tgt e, relation_charge]
    ring_nf
    exact le_rfl

theorem hasFiniteBudget : relation.HasFiniteBudget :=
  exactPotential_isBoundedPotential.hasFiniteBudget

/-- The budget of the interpolation relation is at most one. -/
theorem budget_le_one : relation.budget ≤ 1 := by
  refine le_trans (relation.budget_le_oscillation exactPotential_isBoundedPotential) ?_
  have hA : sSup (Set.range exactPotential) ≤ 1 :=
    Real.sSup_le (by
      rintro x ⟨q, rfl⟩
      exact (exactPotential_mem_Icc q).2) zero_le_one
  have hB : (0 : ℝ) ≤ sInf (Set.range exactPotential) :=
    Real.le_sInf (by
      rintro x ⟨q, rfl⟩
      exact (exactPotential_mem_Icc q).1) le_rfl
  simp only [oscillation]
  linarith

/-- Every edge endpoint lies in the unit square. -/
theorem src_mem_square (e : Edge) :
    relation.src e ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨ht0, ht1, hsq, hle⟩ := e.2
  have h0 : (0 : ℝ) ≤ e.1.1 ^ 2 := sq_nonneg _
  simp only [Set.mem_prod, relation_src, Set.mem_Icc]
  exact ⟨⟨ht0.le, ht1⟩, by linarith, by linarith⟩

theorem tgt_mem_square (e : Edge) :
    relation.tgt e ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨ht0, ht1, hsq, hle⟩ := e.2
  have h0 : (0 : ℝ) ≤ e.1.1 ^ 2 := sq_nonneg _
  simp only [Set.mem_prod, relation_tgt, Set.mem_Icc]
  exact ⟨⟨ht0.le, ht1⟩, by linarith, by linarith⟩

/-- The region carrying the edges is compact. -/
theorem isCompact_square :
    IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
  isCompact_Icc.prod isCompact_Icc

/-- Descending inside the tower over `t = 1 / m`: after `k` steps the height is
`(m - k) / m ^ 2` and any potential has dropped by at least `k / m`. -/
theorem potential_drop {Ψ : ℝ × ℝ → ℝ} (hΨ : relation.IsPotential Ψ) (m : ℕ) (hm : 1 ≤ m) :
    ∀ k : ℕ, k ≤ m →
      Ψ (1 / (m : ℝ), ((m : ℝ) - k) / (m : ℝ) ^ 2) + k / (m : ℝ)
        ≤ Ψ (1 / (m : ℝ), 1 / (m : ℝ)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm0
  intro k
  induction k with
  | zero =>
      intro _
      have h1 : ((m : ℝ) - ((0 : ℕ) : ℝ)) / (m : ℝ) ^ 2 = 1 / (m : ℝ) := by
        push_cast
        field_simp
        ring
      rw [h1]
      simp
  | succ k ih =>
      intro hk
      have hkm : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hk
      have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      have hpos : (0 : ℝ) < 1 / (m : ℝ) := by positivity
      have hone : (1 : ℝ) / (m : ℝ) ≤ 1 := by
        rw [div_le_one hm0]
        exact_mod_cast hm
      have hsqdiff : ((m : ℝ) - (k : ℝ)) / (m : ℝ) ^ 2 - (1 / (m : ℝ)) ^ 2
          = ((m : ℝ) - ((k : ℝ) + 1)) / (m : ℝ) ^ 2 := by
        field_simp
        ring
      have hsqnn : (0 : ℝ) ≤ ((m : ℝ) - ((k : ℝ) + 1)) / (m : ℝ) ^ 2 :=
        div_nonneg (by linarith) (by positivity)
      have hsq : (1 / (m : ℝ)) ^ 2 ≤ ((m : ℝ) - (k : ℝ)) / (m : ℝ) ^ 2 := by linarith
      have hlediff : 1 / (m : ℝ) - ((m : ℝ) - (k : ℝ)) / (m : ℝ) ^ 2
          = (k : ℝ) / (m : ℝ) ^ 2 := by
        field_simp
        ring
      have hlenn : (0 : ℝ) ≤ (k : ℝ) / (m : ℝ) ^ 2 := div_nonneg hknn (by positivity)
      have hle : ((m : ℝ) - (k : ℝ)) / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) := by linarith
      have hedge := hΨ ⟨(1 / (m : ℝ), ((m : ℝ) - (k : ℝ)) / (m : ℝ) ^ 2),
        hpos, hone, hsq, hle⟩
      simp only [relation_src, relation_tgt, relation_charge] at hedge
      rw [hsqdiff] at hedge
      have hprev := ih (by omega)
      have hsplit : ((k : ℝ) + 1) / (m : ℝ) = (k : ℝ) / (m : ℝ) + 1 / (m : ℝ) := by
        field_simp
      push_cast at hprev ⊢
      linarith [hsplit]

/-- After `m` steps the height is zero and the drop is exactly one. -/
theorem potential_gap {Ψ : ℝ × ℝ → ℝ} (hΨ : relation.IsPotential Ψ) (m : ℕ) (hm : 1 ≤ m) :
    Ψ (1 / (m : ℝ), 0) + 1 ≤ Ψ (1 / (m : ℝ), 1 / (m : ℝ)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h := potential_drop hΨ m hm m le_rfl
  rwa [sub_self, zero_div, div_self (ne_of_gt hm0)] at h

/-- **Continuous incompleteness.**  No potential for the interpolation relation is
continuous at the origin, even though a bounded exact potential exists. -/
theorem not_continuousAt_of_isPotential {Ψ : ℝ × ℝ → ℝ} (hΨ : relation.IsPotential Ψ) :
    ¬ ContinuousAt Ψ (0, 0) := by
  intro hcont
  have hnat : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlow : Filter.Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1), (0 : ℝ)) : ℝ × ℝ))
      Filter.atTop (nhds ((0 : ℝ), (0 : ℝ))) :=
    hnat.prodMk_nhds tendsto_const_nhds
  have hhigh : Filter.Tendsto
      (fun n : ℕ => ((1 / ((n : ℝ) + 1), 1 / ((n : ℝ) + 1)) : ℝ × ℝ))
      Filter.atTop (nhds ((0 : ℝ), (0 : ℝ))) :=
    hnat.prodMk_nhds hnat
  have hL : Filter.Tendsto (fun n : ℕ => Ψ (1 / ((n : ℝ) + 1), (0 : ℝ)) + 1)
      Filter.atTop (nhds (Ψ (0, 0) + 1)) :=
    (hcont.tendsto.comp hlow).add tendsto_const_nhds
  have hR : Filter.Tendsto (fun n : ℕ => Ψ (1 / ((n : ℝ) + 1), 1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds (Ψ (0, 0))) :=
    hcont.tendsto.comp hhigh
  have hpoint : ∀ n : ℕ,
      Ψ (1 / ((n : ℝ) + 1), (0 : ℝ)) + 1 ≤ Ψ (1 / ((n : ℝ) + 1), 1 / ((n : ℝ) + 1)) := by
    intro n
    have h := potential_gap hΨ (n + 1) (by omega)
    push_cast at h
    exact h
  have hfinal := le_of_tendsto_of_tendsto' hL hR hpoint
  linarith

/-- The budget of the interpolation relation is exactly one. -/
theorem budget_eq_one : relation.budget = 1 := by
  refine le_antisymm budget_le_one ?_
  have hpot := (relation.value_isBoundedPotential hasFiniteBudget).isPotential
  have hgap := potential_gap hpot 1 le_rfl
  have hzero := relation.value_nonneg hasFiniteBudget (1 / ((1 : ℕ) : ℝ), 0)
  have hbud := relation.value_le_budget hasFiniteBudget
    (1 / ((1 : ℕ) : ℝ), 1 / ((1 : ℕ) : ℝ))
  linarith

/-- No potential for the interpolation relation is continuous. -/
theorem not_continuous_of_isPotential {Ψ : ℝ × ℝ → ℝ} (hΨ : relation.IsPotential Ψ) :
    ¬ Continuous Ψ := fun hc => not_continuousAt_of_isPotential hΨ hc.continuousAt

/-- There is no continuous bounded potential, although bounded potentials exist. -/
theorem no_continuous_boundedPotential :
    ¬ ∃ Ψ : ℝ × ℝ → ℝ, relation.IsBoundedPotential Ψ ∧ Continuous Ψ := by
  rintro ⟨Ψ, hΨ, hc⟩
  exact not_continuous_of_isPotential hΨ.isPotential hc

end Interpolation

-- ============================================================================
-- Quit-bonus calibration: an exact positive-charge self-loop
-- ============================================================================

namespace QuitBonus

open Math.PMFProduct

/-- One-stage expected payoff in a two-player quitting-style stage game.  Each
player `i` quits independently with probability `x i`.  If exactly the first player
quits the stage payoff is `wFirst`, if exactly the second quits it is `wSecond`, if
both quit it is `wBoth`, and if nobody quits the continuation value `v` is used. -/
def oneStageUpdate (wFirst wSecond wBoth : Fin 2 → ℝ) (x v : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  x 0 * (1 - x 1) * wFirst i + (1 - x 0) * x 1 * wSecond i + x 0 * x 1 * wBoth i
    + (1 - x 0) * (1 - x 1) * v i

/-- The explicit coefficients of the one-stage update are the coalition masses of
the row, and the continuation coefficient is the continuation mass. -/
theorem oneStageUpdate_eq_coalitionSum (wFirst wSecond wBoth x v : Fin 2 → ℝ) (i : Fin 2) :
    oneStageUpdate wFirst wSecond wBoth x v i
      = coalitionMass x {0} * wFirst i + coalitionMass x {1} * wSecond i
        + coalitionMass x {0, 1} * wBoth i + continueMass x * v i := by
  have h0 : ({0} : Finset (Fin 2))ᶜ = {1} := by decide
  have h1 : ({1} : Finset (Fin 2))ᶜ = {0} := by decide
  have h2 : ({0, 1} : Finset (Fin 2))ᶜ = ∅ := by decide
  have hpair : ∀ f : Fin 2 → ℝ, ∏ j ∈ ({0, 1} : Finset (Fin 2)), f j = f 0 * f 1 :=
    fun f => Finset.prod_pair (show (0 : Fin 2) ≠ 1 by decide)
  simp only [oneStageUpdate, coalitionMass, continueMass, h0, h1, h2,
    Finset.prod_singleton, Finset.prod_empty, hpair, Fin.prod_univ_two]
  ring

/-- Quitting charge of a row: the probability that somebody quits. -/
def quitCharge (x : Fin 2 → ℝ) : ℝ := 1 - continueMass x

/-- Payoff when only the first player quits: `(a, 0)`. -/
def wFirst (a : ℝ) : Fin 2 → ℝ := ![a, 0]

/-- Payoff when only the second player quits: `(1, -1)`. -/
def wSecond : Fin 2 → ℝ := ![1, -1]

/-- Payoff when both players quit: `(0, 1)`. -/
def wBoth : Fin 2 → ℝ := ![0, 1]

/-- The calibrating row: the first player quits with probability one half, the
second continues surely. -/
noncomputable def row : Fin 2 → ℝ := ![1 / 2, 0]

/-- The calibrating value vector `(a, 0)`. -/
def val (a : ℝ) : Fin 2 → ℝ := ![a, 0]

@[simp] theorem continueMass_row : continueMass row = 1 / 2 := by
  norm_num [continueMass, row, Fin.prod_univ_two]

@[simp] theorem quitCharge_row : quitCharge row = 1 / 2 := by
  norm_num [quitCharge]

theorem quitCharge_row_pos : 0 < quitCharge row := by
  rw [quitCharge_row]
  norm_num

/-- **Calibration.**  At the row `x = (1/2, 0)` the one-stage update fixes the value
vector `(a, 0)`: both players' one-stage gaps are exactly zero. -/
theorem oneStageUpdate_fixed (a : ℝ) (i : Fin 2) :
    oneStageUpdate (wFirst a) wSecond wBoth row (val a) i = val a i := by
  fin_cases i <;> norm_num [oneStageUpdate, wFirst, wSecond, wBoth, row, val]
  ring

/-- The charged relation attached to the calibration: a self-loop at the fixed value
vector, carrying the row's quitting charge. -/
noncomputable def relation (a : ℝ) : ChargedRelation (Fin 2 → ℝ) Unit where
  src _ := val a
  tgt _ := val a
  charge _ := quitCharge row
  charge_nonneg _ := quitCharge_row_pos.le

@[simp] theorem relation_charge (a : ℝ) (u : Unit) : (relation a).charge u = 1 / 2 := by
  have h : (relation a).charge u = quitCharge row := rfl
  rw [h, quitCharge_row]

/-- The calibration is an exact positive-charge self-loop, so the budget is
infinite. -/
theorem not_hasFiniteBudget (a : ℝ) : ¬ (relation a).HasFiniteBudget := by
  refine (relation a).not_hasFiniteBudget_of_positive_selfLoop () rfl ?_
  rw [relation_charge]
  norm_num

/-- **Calibration corollary.**  No bounded potential of any kind exists for the
calibrating weight's relation. -/
theorem no_boundedPotential (a : ℝ) :
    ¬ ∃ Φ : (Fin 2 → ℝ) → ℝ, (relation a).IsBoundedPotential Φ := by
  rw [← (relation a).hasFiniteBudget_iff_exists_boundedPotential]
  exact not_hasFiniteBudget a

end QuitBonus

end ChargedPathBudget
end Math
