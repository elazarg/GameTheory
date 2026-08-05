/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Bounded path budgets are exactly bounded potentials

A *charged relation* on a state type is a family of directed edges, each carrying
a source state, a target state, and a nonnegative real charge.  A finite
admissible path is a finite chain of edges with matching endpoints; the charge of
a path is the sum of the charges of its edges.

The **budget** of a charged relation is the supremum of the charges of all its
finite paths.  A **potential** is a real function `Φ` on states obeying the edge
decrement inequality `Φ (tgt e) + charge e ≤ Φ (src e)`.  It is *bounded* when its
range is bounded above and below, and its **oscillation** is
`sSup (range Φ) - sInf (range Φ)`.

## Main definitions

- `ChargedRelation` — edges with source, target, and nonnegative charge
- `ChargedRelation.Path` — finite admissible paths, indexed by their endpoints
- `ChargedRelation.budget`, `ChargedRelation.HasFiniteBudget` — the path budget
- `ChargedRelation.budgetEN` — the same budget as a totally defined `ℝ≥0∞`
- `ChargedRelation.value` — the budget-to-go function
- `ChargedRelation.IsPotential`, `ChargedRelation.IsBoundedPotential`

## Main results

- `ChargedRelation.hasFiniteBudget_iff_exists_boundedPotential` — the budget is
  finite exactly when a bounded potential exists.  The forward witness is `value`;
  the converse is a telescoping bound along paths.
- `ChargedRelation.budget_eq_oscillation_value` and
  `ChargedRelation.isLeast_oscillation` — strong duality: the budget is the
  *minimum* oscillation of a bounded potential, and the minimum is attained by
  `value`.  The two inequalities `budget_le_oscillation` and
  `oscillation_value_le_budget` are stated separately and are usable on their own.
- `ChargedRelation.budgetEN_eq_iInf_oscillation` — the same duality with no
  finiteness hypothesis: in `ℝ≥0∞` the budget always equals the infimum of the
  oscillations of bounded potentials, both sides being `⊤` in the unbounded case.
- `ChargedRelation.isLeast_value` and `ChargedRelation.value_le_iff` — Bellman
  characterisation: `value` is the least nonnegative supersolution.
- `ChargedRelation.not_hasFiniteBudget_of_positive_cycle` and
  `ChargedRelation.not_exists_boundedPotential_of_positive_selfLoop` — a closed
  path of strictly positive charge forces an infinite budget, hence excludes
  bounded potentials of every kind.

## Design notes

The oscillation is taken over *all* states, not only over states touched by an
edge, and the duality is nevertheless exact.  The reason is that the budget-to-go
function is globally nonnegative (the empty path) and globally bounded by the
budget, so its oscillation over all states is already at most the budget; the
telescoping bound supplies the reverse inequality for every bounded potential.
Restricting the oscillation to touched states would therefore not lower the
minimum, and would complicate every statement with a side condition.

No maximising path is ever assumed to exist: `value` is defined as a supremum and
the edge inequality for it is obtained by prepending an edge to an arbitrary path.
-/

universe u v

namespace Math
namespace ChargedPathBudget

open scoped ENNReal

/-- Oscillation of a real-valued function: the spread of its range.  For an
unbounded function the value is junk and every statement about it carries an
explicit boundedness hypothesis. -/
noncomputable def oscillation {State : Type u} (f : State → ℝ) : ℝ :=
  sSup (Set.range f) - sInf (Set.range f)

theorem oscillation_nonneg {State : Type u} {f : State → ℝ}
    (hA : BddAbove (Set.range f)) (hB : BddBelow (Set.range f)) : 0 ≤ oscillation f := by
  rcases isEmpty_or_nonempty State with hs | hs
  · simp [oscillation, Set.range_eq_empty f, Real.sSup_empty, Real.sInf_empty]
  · have := csInf_le_csSup (Set.range_nonempty f) hB hA
    simpa [oscillation, sub_nonneg] using this

/-- A charged relation on `State`: a family of directed edges, each with a source
state, a target state, and a nonnegative real charge. -/
structure ChargedRelation (State : Type u) (Edge : Type v) where
  /-- Source state of an edge. -/
  src : Edge → State
  /-- Target state of an edge. -/
  tgt : Edge → State
  /-- Charge accumulated by traversing an edge. -/
  charge : Edge → ℝ
  /-- Charges are nonnegative. -/
  charge_nonneg : ∀ e, 0 ≤ charge e

namespace ChargedRelation

variable {State : Type u} {Edge : Type v}

/-- A finite admissible path, indexed by its two endpoints.  Endpoint matching is
enforced by the indexing, so there is no side condition to carry around. -/
inductive Path (R : ChargedRelation State Edge) : State → State → Type (max u v)
  /-- The empty path at a state. -/
  | nil (s : State) : Path R s s
  /-- Prepend an edge to a path starting at that edge's target. -/
  | cons (e : Edge) {t : State} (rest : Path R (R.tgt e) t) : Path R (R.src e) t

namespace Path

variable {R : ChargedRelation State Edge}

/-- Total charge of a finite admissible path: the sum of its edge charges. -/
def chargeSum : {s t : State} → R.Path s t → ℝ
  | _, _, .nil _ => 0
  | _, _, .cons e rest => R.charge e + chargeSum rest

/-- Number of edges in a finite admissible path. -/
def length : {s t : State} → R.Path s t → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ rest => rest.length + 1

@[simp] theorem length_nil (s : State) : (Path.nil s : R.Path s s).length = 0 := rfl

@[simp] theorem length_cons (e : Edge) {t : State} (rest : R.Path (R.tgt e) t) :
    (Path.cons e rest).length = rest.length + 1 := rfl

@[simp] theorem chargeSum_nil (s : State) : (Path.nil s : R.Path s s).chargeSum = 0 := rfl

@[simp] theorem chargeSum_cons (e : Edge) {t : State} (rest : R.Path (R.tgt e) t) :
    (Path.cons e rest).chargeSum = R.charge e + rest.chargeSum := rfl

theorem chargeSum_nonneg {s t : State} (p : R.Path s t) : 0 ≤ p.chargeSum := by
  induction p with
  | nil s => simp
  | cons e rest ih =>
      have := R.charge_nonneg e
      simp only [chargeSum_cons]
      linarith

/-- The one-edge path. -/
def single (e : Edge) : R.Path (R.src e) (R.tgt e) := .cons e (.nil _)

@[simp] theorem chargeSum_single (e : Edge) :
    (Path.single (R := R) e).chargeSum = R.charge e := by
  simp [single]

/-- Concatenation of paths. -/
def append : {s t w : State} → R.Path s t → R.Path t w → R.Path s w
  | _, _, _, .nil _, q => q
  | _, _, _, .cons e rest, q => .cons e (append rest q)

@[simp] theorem chargeSum_append {s t w : State} (p : R.Path s t) (q : R.Path t w) :
    (p.append q).chargeSum = p.chargeSum + q.chargeSum := by
  induction p with
  | nil s => simp [append]
  | cons e rest ih =>
      simp only [append, chargeSum_cons, ih]
      ring

/-- Move the terminal endpoint of a path along an equality of states. -/
def castTgt {s t w : State} (h : t = w) (p : R.Path s t) : R.Path s w := h ▸ p

@[simp] theorem chargeSum_castTgt {s t w : State} (h : t = w) (p : R.Path s t) :
    (p.castTgt h).chargeSum = p.chargeSum := by
  subst h
  rfl

/-- Move the initial endpoint of a path along an equality of states. -/
def castSrc {s t w : State} (h : s = t) (p : R.Path s w) : R.Path t w := h ▸ p

@[simp] theorem chargeSum_castSrc {s t w : State} (h : s = t) (p : R.Path s w) :
    (p.castSrc h).chargeSum = p.chargeSum := by
  subst h
  rfl

/-- A one-edge path between explicitly named endpoints.  Using this instead of
`Path.single` keeps the endpoint indices syntactically fixed, which makes the
charge lemmas rewrite cleanly in concrete instances. -/
def edge (e : Edge) {s t : State} (hs : R.src e = s) (ht : R.tgt e = t) : R.Path s t :=
  ((Path.single e).castTgt ht).castSrc hs

@[simp] theorem chargeSum_edge (e : Edge) {s t : State} (hs : R.src e = s)
    (ht : R.tgt e = t) : (Path.edge e hs ht).chargeSum = R.charge e := by
  subst hs
  subst ht
  simp [edge]

/-- Concatenate `n` copies of a closed path. -/
def iterate {s : State} (p : R.Path s s) : ℕ → R.Path s s
  | 0 => .nil s
  | n + 1 => p.append (iterate p n)

@[simp] theorem chargeSum_iterate {s : State} (p : R.Path s s) (n : ℕ) :
    (p.iterate n).chargeSum = n * p.chargeSum := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
      simp only [iterate, chargeSum_append, ih]
      push_cast
      ring

end Path

variable (R : ChargedRelation State Edge)

/-- Charges of the finite admissible paths starting at `s`. -/
def chargesFrom (s : State) : Set ℝ := {x | ∃ t, ∃ p : R.Path s t, p.chargeSum = x}

/-- Charges of all finite admissible paths. -/
def pathCharges : Set ℝ := {x | ∃ s t, ∃ p : R.Path s t, p.chargeSum = x}

theorem mem_pathCharges {s t : State} (p : R.Path s t) : p.chargeSum ∈ R.pathCharges :=
  ⟨s, t, p, rfl⟩

theorem mem_chargesFrom {s t : State} (p : R.Path s t) : p.chargeSum ∈ R.chargesFrom s :=
  ⟨t, p, rfl⟩

theorem chargesFrom_subset (s : State) : R.chargesFrom s ⊆ R.pathCharges := by
  rintro x ⟨t, p, rfl⟩
  exact ⟨s, t, p, rfl⟩

theorem zero_mem_chargesFrom (s : State) : (0 : ℝ) ∈ R.chargesFrom s :=
  ⟨s, Path.nil s, rfl⟩

/-- The path charges of `R` are uniformly bounded. -/
def HasFiniteBudget : Prop := BddAbove R.pathCharges

/-- The path budget: the supremum of the charges of all finite admissible paths.
When the budget is infinite this is junk; every statement about it carries an
explicit `HasFiniteBudget` hypothesis (or is stated for `budgetEN`). -/
noncomputable def budget : ℝ := sSup R.pathCharges

/-- The budget-to-go from `s`: the supremum of the charges of the finite
admissible paths that start at `s`. -/
noncomputable def value (s : State) : ℝ := sSup (R.chargesFrom s)

theorem budget_nonneg : 0 ≤ R.budget :=
  Real.sSup_nonneg (by
    rintro x ⟨s, t, p, rfl⟩
    exact p.chargeSum_nonneg)

theorem chargeSum_le_budget (h : R.HasFiniteBudget) {s t : State} (p : R.Path s t) :
    p.chargeSum ≤ R.budget :=
  le_csSup h (R.mem_pathCharges p)

/-- Elimination rule for the budget: a nonnegative bound on every path charge
bounds the budget. -/
theorem budget_le {c : ℝ} (hc : 0 ≤ c)
    (hp : ∀ {s t : State} (p : R.Path s t), p.chargeSum ≤ c) : R.budget ≤ c :=
  Real.sSup_le (by
    rintro x ⟨s, t, p, rfl⟩
    exact hp p) hc

theorem bddAbove_chargesFrom (h : R.HasFiniteBudget) (s : State) :
    BddAbove (R.chargesFrom s) :=
  h.mono (R.chargesFrom_subset s)

theorem value_nonneg (h : R.HasFiniteBudget) (s : State) : 0 ≤ R.value s :=
  le_csSup (R.bddAbove_chargesFrom h s) (R.zero_mem_chargesFrom s)

theorem chargeSum_le_value (h : R.HasFiniteBudget) {s t : State} (p : R.Path s t) :
    p.chargeSum ≤ R.value s :=
  le_csSup (R.bddAbove_chargesFrom h s) (R.mem_chargesFrom p)

/-- Elimination rule for the budget-to-go: a nonnegative bound on every path
charge from `s` bounds `value s`. -/
theorem value_le {c : ℝ} {s : State} (hc : 0 ≤ c)
    (hp : ∀ {t : State} (p : R.Path s t), p.chargeSum ≤ c) : R.value s ≤ c :=
  Real.sSup_le (by
    rintro x ⟨t, p, rfl⟩
    exact hp p) hc

theorem value_le_budget (h : R.HasFiniteBudget) (s : State) : R.value s ≤ R.budget :=
  R.value_le R.budget_nonneg fun p => R.chargeSum_le_budget h p

-- ============================================================================
-- Potentials
-- ============================================================================

/-- A potential for `R`: traversing an edge decreases it by at least the charge. -/
def IsPotential (Φ : State → ℝ) : Prop :=
  ∀ e : Edge, Φ (R.tgt e) + R.charge e ≤ Φ (R.src e)

/-- A bounded potential: a potential with range bounded above and below. -/
structure IsBoundedPotential (Φ : State → ℝ) : Prop where
  /-- The range of the potential is bounded above. -/
  bddAbove : BddAbove (Set.range Φ)
  /-- The range of the potential is bounded below. -/
  bddBelow : BddBelow (Set.range Φ)
  /-- The edge decrement inequality. -/
  isPotential : R.IsPotential Φ

section PotentialLemmas

variable {R}

/-- Telescoping along a path: a potential drops by at least the path charge. -/
theorem IsPotential.chargeSum_le {Φ : State → ℝ} (hΦ : R.IsPotential Φ) {s t : State}
    (p : R.Path s t) : p.chargeSum ≤ Φ s - Φ t := by
  induction p with
  | nil s => simp
  | cons e rest ih =>
      have h := hΦ e
      simp only [Path.chargeSum_cons]
      linarith

theorem IsBoundedPotential.chargeSum_le_oscillation {Φ : State → ℝ}
    (hΦ : R.IsBoundedPotential Φ) {s t : State} (p : R.Path s t) :
    p.chargeSum ≤ oscillation Φ := by
  have h1 : Φ s ≤ sSup (Set.range Φ) := le_csSup hΦ.bddAbove ⟨s, rfl⟩
  have h2 : sInf (Set.range Φ) ≤ Φ t := csInf_le hΦ.bddBelow ⟨t, rfl⟩
  have h3 := hΦ.isPotential.chargeSum_le p
  simp only [oscillation]
  linarith

/-- A bounded potential caps the budget: this is the converse half of the
budget-to-go theorem. -/
theorem IsBoundedPotential.hasFiniteBudget {Φ : State → ℝ}
    (hΦ : R.IsBoundedPotential Φ) : R.HasFiniteBudget :=
  ⟨oscillation Φ, by
    rintro x ⟨s, t, p, rfl⟩
    exact hΦ.chargeSum_le_oscillation p⟩

end PotentialLemmas

/-- Weak duality: the budget is at most the oscillation of any bounded potential. -/
theorem budget_le_oscillation {Φ : State → ℝ} (hΦ : R.IsBoundedPotential Φ) :
    R.budget ≤ oscillation Φ :=
  R.budget_le (oscillation_nonneg hΦ.bddAbove hΦ.bddBelow)
    fun p => hΦ.chargeSum_le_oscillation p

-- ============================================================================
-- The budget-to-go function is an optimal potential
-- ============================================================================

/-- The budget-to-go obeys the edge decrement inequality.  No maximising path is
assumed: an arbitrary path from `tgt e` is prepended with `e`. -/
theorem value_tgt_add_charge_le_value_src (h : R.HasFiniteBudget) (e : Edge) :
    R.value (R.tgt e) + R.charge e ≤ R.value (R.src e) := by
  have hloop : R.charge e ≤ R.value (R.src e) := by
    have := R.chargeSum_le_value h (Path.single (R := R) e)
    simpa using this
  have key : R.value (R.tgt e) ≤ R.value (R.src e) - R.charge e := by
    refine R.value_le (by linarith) ?_
    intro t q
    have := R.chargeSum_le_value h (Path.cons e q)
    simp only [Path.chargeSum_cons] at this
    linarith
  linarith

theorem value_isBoundedPotential (h : R.HasFiniteBudget) :
    R.IsBoundedPotential R.value where
  bddAbove := ⟨R.budget, by
    rintro x ⟨s, rfl⟩
    exact R.value_le_budget h s⟩
  bddBelow := ⟨0, by
    rintro x ⟨s, rfl⟩
    exact R.value_nonneg h s⟩
  isPotential := fun e => R.value_tgt_add_charge_le_value_src h e

theorem oscillation_value_le_budget (h : R.HasFiniteBudget) :
    oscillation R.value ≤ R.budget := by
  have hA : sSup (Set.range R.value) ≤ R.budget :=
    Real.sSup_le (by
      rintro x ⟨s, rfl⟩
      exact R.value_le_budget h s) R.budget_nonneg
  have hB : (0 : ℝ) ≤ sInf (Set.range R.value) :=
    Real.le_sInf (by
      rintro x ⟨s, rfl⟩
      exact R.value_nonneg h s) le_rfl
  simp only [oscillation]
  linarith

/-- **Budget-to-go theorem.**  The budget is finite exactly when a bounded
potential exists.  The forward witness is the budget-to-go function. -/
theorem hasFiniteBudget_iff_exists_boundedPotential :
    R.HasFiniteBudget ↔ ∃ Φ : State → ℝ, R.IsBoundedPotential Φ :=
  ⟨fun h => ⟨R.value, R.value_isBoundedPotential h⟩, fun ⟨_, hΦ⟩ => hΦ.hasFiniteBudget⟩

/-- **Strong duality.**  The budget equals the oscillation of the budget-to-go
function, so the minimum in `isLeast_oscillation` is attained. -/
theorem budget_eq_oscillation_value (h : R.HasFiniteBudget) :
    R.budget = oscillation R.value :=
  le_antisymm (R.budget_le_oscillation (R.value_isBoundedPotential h))
    (R.oscillation_value_le_budget h)

/-- **Strong duality, packaged.**  The budget is the least oscillation among
bounded potentials, and the least value is attained. -/
theorem isLeast_oscillation (h : R.HasFiniteBudget) :
    IsLeast {c : ℝ | ∃ Φ : State → ℝ, R.IsBoundedPotential Φ ∧ oscillation Φ = c}
      R.budget := by
  constructor
  · exact ⟨R.value, R.value_isBoundedPotential h, (R.budget_eq_oscillation_value h).symm⟩
  · rintro c ⟨Φ, hΦ, rfl⟩
    exact R.budget_le_oscillation hΦ

/-- The budget-to-go attains the budget as its supremum. -/
theorem sSup_range_value (h : R.HasFiniteBudget) :
    sSup (Set.range R.value) = R.budget := by
  have hA : sSup (Set.range R.value) ≤ R.budget :=
    Real.sSup_le (by
      rintro x ⟨s, rfl⟩
      exact R.value_le_budget h s) R.budget_nonneg
  have hB : (0 : ℝ) ≤ sInf (Set.range R.value) :=
    Real.le_sInf (by
      rintro x ⟨s, rfl⟩
      exact R.value_nonneg h s) le_rfl
  have hosc := R.budget_eq_oscillation_value h
  simp only [oscillation] at hosc
  linarith

/-- The budget-to-go has infimum zero: it approaches states with no charge left. -/
theorem sInf_range_value (h : R.HasFiniteBudget) : sInf (Set.range R.value) = 0 := by
  have hA : sSup (Set.range R.value) ≤ R.budget :=
    Real.sSup_le (by
      rintro x ⟨s, rfl⟩
      exact R.value_le_budget h s) R.budget_nonneg
  have hB : (0 : ℝ) ≤ sInf (Set.range R.value) :=
    Real.le_sInf (by
      rintro x ⟨s, rfl⟩
      exact R.value_nonneg h s) le_rfl
  have hosc := R.budget_eq_oscillation_value h
  simp only [oscillation] at hosc
  linarith

-- ============================================================================
-- Bellman characterisation
-- ============================================================================

/-- A nonnegative supersolution of the Bellman inequality. -/
structure IsSupersolution (Ψ : State → ℝ) : Prop where
  /-- Supersolutions are nonnegative. -/
  nonneg : ∀ s, 0 ≤ Ψ s
  /-- The edge decrement inequality. -/
  isPotential : R.IsPotential Ψ

theorem value_isSupersolution (h : R.HasFiniteBudget) : R.IsSupersolution R.value where
  nonneg := R.value_nonneg h
  isPotential := (R.value_isBoundedPotential h).isPotential

/-- Every nonnegative supersolution dominates the budget-to-go.  No finiteness
hypothesis is needed: if the budget from `s` is infinite the supremum defining
`value s` is junk, but the bound still holds because the hypothesis forces the
charges from `s` to be bounded by `Ψ s`. -/
theorem value_le_of_isSupersolution {Ψ : State → ℝ}
    (hΨ : R.IsSupersolution Ψ) (s : State) : R.value s ≤ Ψ s := by
  refine R.value_le (hΨ.nonneg s) ?_
  intro t p
  have h1 := hΨ.isPotential.chargeSum_le p
  have h2 := hΨ.nonneg t
  linarith

/-- **Bellman characterisation.**  The budget-to-go is the least nonnegative
supersolution, in the pointwise order. -/
theorem isLeast_value (h : R.HasFiniteBudget) :
    IsLeast {Ψ : State → ℝ | R.IsSupersolution Ψ} R.value := by
  constructor
  · exact R.value_isSupersolution h
  · intro Ψ hΨ s
    exact R.value_le_of_isSupersolution hΨ s

/-- The local Bellman inequality, in elimination form: `value s` is the least
number that is nonnegative and dominates `charge e + value (tgt e)` for every
edge `e` leaving `s`. -/
theorem value_le_iff (h : R.HasFiniteBudget) (s : State) (c : ℝ) :
    R.value s ≤ c ↔ 0 ≤ c ∧ ∀ e : Edge, R.src e = s → R.charge e + R.value (R.tgt e) ≤ c := by
  constructor
  · intro hle
    refine ⟨le_trans (R.value_nonneg h s) hle, ?_⟩
    rintro e rfl
    have := R.value_tgt_add_charge_le_value_src h e
    linarith
  · rintro ⟨hc, hedge⟩
    refine R.value_le hc ?_
    intro t p
    revert hedge
    cases p with
    | nil s => intro _; simpa using hc
    | cons e rest =>
        intro hedge
        have h1 := hedge e rfl
        have h2 := R.chargeSum_le_value h rest
        simp only [Path.chargeSum_cons]
        linarith

-- ============================================================================
-- Positive closed paths destroy every bounded potential
-- ============================================================================

/-- A closed path of strictly positive charge forces an infinite budget. -/
theorem not_hasFiniteBudget_of_positive_cycle {s : State} (p : R.Path s s)
    (hp : 0 < p.chargeSum) : ¬ R.HasFiniteBudget := by
  intro h
  obtain ⟨n, hn⟩ := exists_nat_gt (R.budget / p.chargeSum)
  have hle : ((n : ℝ)) * p.chargeSum ≤ R.budget := by
    have := R.chargeSum_le_budget h (p.iterate n)
    simpa using this
  have hgt : R.budget < (n : ℝ) * p.chargeSum := by
    rw [div_lt_iff₀ hp] at hn
    linarith
  linarith

/-- A closed path of strictly positive charge excludes bounded potentials of every
kind. -/
theorem not_exists_boundedPotential_of_positive_cycle {s : State} (p : R.Path s s)
    (hp : 0 < p.chargeSum) : ¬ ∃ Φ : State → ℝ, R.IsBoundedPotential Φ := by
  rintro ⟨Φ, hΦ⟩
  exact R.not_hasFiniteBudget_of_positive_cycle p hp hΦ.hasFiniteBudget

/-- A self-loop of strictly positive charge forces an infinite budget. -/
theorem not_hasFiniteBudget_of_positive_selfLoop (e : Edge) (hloop : R.tgt e = R.src e)
    (hcharge : 0 < R.charge e) : ¬ R.HasFiniteBudget := by
  refine R.not_hasFiniteBudget_of_positive_cycle ((Path.single (R := R) e).castTgt hloop) ?_
  simpa using hcharge

/-- **Positive-charge self-loop corollary.**  A self-loop of strictly positive
charge excludes bounded potentials of every kind. -/
theorem not_exists_boundedPotential_of_positive_selfLoop (e : Edge)
    (hloop : R.tgt e = R.src e) (hcharge : 0 < R.charge e) :
    ¬ ∃ Φ : State → ℝ, R.IsBoundedPotential Φ := by
  rintro ⟨Φ, hΦ⟩
  exact R.not_hasFiniteBudget_of_positive_selfLoop e hloop hcharge hΦ.hasFiniteBudget

-- ============================================================================
-- The budget as an extended nonnegative real
-- ============================================================================

/-- The path budget as an extended nonnegative real.  This is totally defined and
equals `⊤` exactly when the budget is infinite. -/
noncomputable def budgetEN : ℝ≥0∞ :=
  ⨆ s : State, ⨆ t : State, ⨆ p : R.Path s t, ENNReal.ofReal p.chargeSum

theorem ofReal_chargeSum_le_budgetEN {s t : State} (p : R.Path s t) :
    ENNReal.ofReal p.chargeSum ≤ R.budgetEN :=
  le_iSup_of_le s (le_iSup_of_le t
    (le_iSup (fun q : R.Path s t => ENNReal.ofReal q.chargeSum) p))

theorem budgetEN_lt_top_iff : R.budgetEN < ⊤ ↔ R.HasFiniteBudget := by
  constructor
  · intro h
    refine ⟨R.budgetEN.toReal, ?_⟩
    rintro x ⟨s, t, p, rfl⟩
    exact (ENNReal.ofReal_le_iff_le_toReal h.ne).1 (R.ofReal_chargeSum_le_budgetEN p)
  · rintro ⟨M, hM⟩
    refine lt_of_le_of_lt (iSup_le fun s => iSup_le fun t => iSup_le fun p => ?_)
      (ENNReal.ofReal_lt_top (r := M))
    exact ENNReal.ofReal_le_ofReal (hM (R.mem_pathCharges p))

theorem budgetEN_eq_top_iff : R.budgetEN = ⊤ ↔ ¬ R.HasFiniteBudget := by
  rw [← budgetEN_lt_top_iff, not_lt_top_iff]

theorem budgetEN_eq_ofReal_budget (h : R.HasFiniteBudget) :
    R.budgetEN = ENNReal.ofReal R.budget := by
  have hne : R.budgetEN ≠ ⊤ := ((R.budgetEN_lt_top_iff).2 h).ne
  refine le_antisymm ?_ ?_
  · exact iSup_le fun s => iSup_le fun t => iSup_le fun p =>
      ENNReal.ofReal_le_ofReal (R.chargeSum_le_budget h p)
  · have hbudget : R.budget ≤ R.budgetEN.toReal := by
      refine R.budget_le ENNReal.toReal_nonneg ?_
      intro s t p
      exact (ENNReal.ofReal_le_iff_le_toReal hne).1 (R.ofReal_chargeSum_le_budgetEN p)
    calc ENNReal.ofReal R.budget ≤ ENNReal.ofReal R.budgetEN.toReal :=
          ENNReal.ofReal_le_ofReal hbudget
      _ = R.budgetEN := ENNReal.ofReal_toReal hne

/-- **Strong duality without a finiteness hypothesis.**  In `ℝ≥0∞` the budget is
always the infimum of the oscillations of bounded potentials.  When no bounded
potential exists the index type is empty and both sides are `⊤`. -/
theorem budgetEN_eq_iInf_oscillation :
    R.budgetEN
      = ⨅ Φ : {Φ : State → ℝ // R.IsBoundedPotential Φ}, ENNReal.ofReal (oscillation Φ.1) := by
  by_cases h : R.HasFiniteBudget
  · refine le_antisymm (le_iInf fun Φ => ?_) ?_
    · rw [R.budgetEN_eq_ofReal_budget h]
      exact ENNReal.ofReal_le_ofReal (R.budget_le_oscillation Φ.2)
    · refine le_trans (iInf_le _ ⟨R.value, R.value_isBoundedPotential h⟩) ?_
      rw [R.budgetEN_eq_ofReal_budget h, ← R.budget_eq_oscillation_value h]
  · have hempty : IsEmpty {Φ : State → ℝ // R.IsBoundedPotential Φ} :=
      ⟨fun Φ => h Φ.2.hasFiniteBudget⟩
    rw [(R.budgetEN_eq_top_iff).2 h, iInf_of_isEmpty, sInf_empty]

end ChargedRelation

end ChargedPathBudget
end Math
