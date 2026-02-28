/-
  AbstractFolk.lean

  A small Lean4 / mathlib skeleton for the "more abstract form" of the Folk Theorem.
  This file focuses on parts that are (a) mathematically clean and (b) typically
  easy to mechanize: defining the feasible set F, the security vector V, the
  individually-rational region IR, and proving basic topological/convex facts
  about IR (convexity, closedness, compactness).

  The actual "folk theorem" statement about equilibrium payoff sets E(δ)
  is included only as a *placeholder theorem statement* (with `sorry`), because
  it depends on a lot of game-specific structure (histories, strategies, incentives),
  and there are multiple inequivalent formal choices there.
-/

import Mathlib.Topology.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Data.Real.Basic

open Set Metric
open scoped Topology

namespace AbstractFolk

/-- `n` players; a payoff vector is a function `Fin n → ℝ` (i.e., `ℝ^n`). -/
abbrev Payoff (n : Nat) : Type := Fin n → ℝ

variable {n : Nat}

/-- The individually rational region:
    `IR(F,V) = { x ∈ F | ∀ i, V i ≤ x i }`. -/
def IR (F : Set (Payoff n)) (V : Payoff n) : Set (Payoff n) :=
  {x | x ∈ F ∧ ∀ i : Fin n, V i ≤ x i}

@[simp] lemma mem_IR {F : Set (Payoff n)} {V : Payoff n} {x : Payoff n} :
    x ∈ IR F V ↔ x ∈ F ∧ ∀ i : Fin n, V i ≤ x i := Iff.rfl

/-- The coordinate "lower bound" set `{x | V i ≤ x i}` is closed. -/
lemma isClosed_coordLower (V : Payoff n) (i : Fin n) :
    IsClosed {x : Payoff n | V i ≤ x i} :=
  isClosed_le continuous_const (continuous_apply i)

/-- The "all coordinates lower bounded by V" set `{x | ∀ i, V i ≤ x i}` is closed. -/
lemma isClosed_allCoordLower (V : Payoff n) :
    IsClosed {x : Payoff n | ∀ i : Fin n, V i ≤ x i} := by
  have : {x : Payoff n | ∀ i : Fin n, V i ≤ x i}
      = ⋂ i : Fin n, {x : Payoff n | V i ≤ x i} := by ext x; simp
  rw [this]
  exact isClosed_iInter (fun i => isClosed_coordLower V i)

/-- If `F` is closed then `IR(F,V)` is closed. -/
lemma isClosed_IR {F : Set (Payoff n)} (V : Payoff n) (hF : IsClosed F) :
    IsClosed (IR F V) := by
  have : IR F V = F ∩ {x : Payoff n | ∀ i : Fin n, V i ≤ x i} := by
    ext x; simp [IR]
  rw [this]
  exact hF.inter (isClosed_allCoordLower V)

/-- If `F` is compact then `IR(F,V)` is compact. -/
lemma isCompact_IR {F : Set (Payoff n)} (V : Payoff n) (hF : IsCompact F) :
    IsCompact (IR F V) := by
  have hF_closed : IsClosed F := hF.isClosed
  have hIR_closed : IsClosed (IR F V) := isClosed_IR V hF_closed
  exact hF.of_isClosed_subset hIR_closed (fun x hx => hx.1)

/-- If `F` is convex, then `IR(F,V)` is convex.
    (Intersection of a convex set with coordinate halfspaces.) -/
lemma convex_IR {F : Set (Payoff n)} (V : Payoff n) (hF : Convex ℝ F) :
    Convex ℝ (IR F V) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hF hx.1 hy.1 ha hb hab, fun i => ?_⟩
  have hax : a * V i ≤ a * x i := mul_le_mul_of_nonneg_left (hx.2 i) ha
  have hby : b * V i ≤ b * y i := mul_le_mul_of_nonneg_left (hy.2 i) hb
  calc V i = (a + b) * V i := by rw [hab, one_mul]
    _ = a * V i + b * V i := by ring
    _ ≤ a * x i + b * y i := add_le_add hax hby

/-- `IR(F,V)` has nonempty interior if it contains a ball. -/
lemma mem_interior_of_ball_subset {F : Set (Payoff n)} {V : Payoff n} {x : Payoff n}
    {r : ℝ} (hr : 0 < r) (hball : ball x r ⊆ IR F V) :
    x ∈ interior (IR F V) :=
  mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (ball_mem_nhds x hr) hball)

/-
  Placeholder for the *abstract* folk theorem shape.

  You'd later instantiate:
  * `F` as the convex hull of stage-game payoff vectors,
  * `V` as the minmax vector,
  * `E δ` as the set of equilibrium payoffs (Nash/SPE/etc.) of the δ-discounted repeated game.

  The hard work is proving the link between the game model and these abstract sets.
-/

-- Abstract equilibrium payoff set as a function of `δ`.
variable (E : ℝ → Set (Payoff n))

/-- A typical abstract folk theorem statement: every interior point of `IR(F,V)` is achievable
    for sufficiently patient players. (Proof omitted; depends on the actual repeated-game model.) -/
theorem abstract_folk_theorem
    (F : Set (Payoff n)) (V : Payoff n) :
    (∀ x, x ∈ interior (IR F V) →
      ∃ δ₀ : ℝ, δ₀ < 1 ∧ ∀ δ : ℝ, δ₀ < δ ∧ δ < 1 → x ∈ E δ) := by
  sorry

end AbstractFolk
