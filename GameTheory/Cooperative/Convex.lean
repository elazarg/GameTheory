module

/-
# Convex coalitional games

Supermodularity means a player's marginal contribution increases as its
predecessor coalition grows. Paying players their successive contributions
in any linear order therefore distributes the grand-coalition worth and
gives every coalition at least what it can earn on its own.
-/

public import GameTheory.Core.Coalitional
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace GameTheory.CoalitionalGame

universe ua

variable {Agent : Type ua} [DecidableEq Agent]

/-- A convex coalitional game has supermodular worth. -/
def IsConvex (G : CoalitionalGame Agent) : Prop :=
  ∀ first second, G.value first + G.value second ≤
    G.value (first ∪ second) + G.value (first ∩ second)

/-- Marginal contributions increase when the existing coalition grows. No
sign restriction is imposed on either worth or marginal contribution. -/
theorem IsConvex.marginalContribution_le {G : CoalitionalGame Agent}
    (convex : G.IsConvex) {first second : Finset Agent}
    (subset : first ⊆ second) {agent : Agent} (absent : agent ∉ second) :
    G.marginalContribution agent first ≤ G.marginalContribution agent second := by
  have inequality := convex (insert agent first) second
  have union : insert agent first ∪ second = insert agent second := by
    ext member
    simp only [Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro ((rfl | member) | member)
      · exact Or.inl rfl
      · exact Or.inr (subset member)
      · exact Or.inr member
    · rintro (rfl | member)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr member
  have inter : insert agent first ∩ second = first := by
    ext member
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | member, inside⟩
      · exact False.elim (absent inside)
      · exact member
    · intro member
      exact ⟨Or.inr member, subset member⟩
  rw [union, inter] at inequality
  unfold marginalContribution
  linarith

private theorem sum_ordered_marginals [LinearOrder Agent]
    (G : CoalitionalGame Agent) (coalition : Finset Agent) :
    (∑ agent ∈ coalition,
      G.marginalContribution agent (coalition.filter (· < agent))) = G.value coalition := by
  induction coalition using Finset.induction_on_max with
  | empty => simp [G.value_empty]
  | insert agent coalition largest induction =>
      have absent : agent ∉ coalition := fun member => (lt_irrefl agent) (largest agent member)
      have before : (insert agent coalition).filter (· < agent) = coalition := by
        ext member
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | inside, smaller⟩
          · exact False.elim ((lt_irrefl _) smaller)
          · exact inside
        · intro inside
          exact ⟨Or.inr inside, largest member inside⟩
      have earlier (member : Agent) (inside : member ∈ coalition) :
          (insert agent coalition).filter (· < member) = coalition.filter (· < member) := by
        rw [Finset.filter_insert, ite_eq_right (not_lt_of_ge (largest member inside).le)]
      rw [Finset.sum_insert absent, before]
      rw [Finset.sum_congr rfl (fun member inside => by rw [earlier member inside]), induction]
      unfold marginalContribution
      linarith

variable [Fintype Agent]

/-- Pay each player the worth it adds to the players preceding it in the
given order. The ordering is a parameter, independent of the game's data. -/
def marginalAllocation (G : CoalitionalGame Agent) (order : LinearOrder Agent) :
    Allocation Agent :=
  fun agent => G.marginalContribution agent
    (Finset.univ.filter (fun earlier => order.lt earlier agent))

/-- Successive marginal payments telescope to the grand-coalition worth,
independently of convexity. -/
theorem marginalAllocation_efficient (G : CoalitionalGame Agent) (order : LinearOrder Agent) :
    payout (G.marginalAllocation order) Finset.univ = G.value Finset.univ := by
  let := order
  exact sum_ordered_marginals G Finset.univ

/-- Every ordering's marginal allocation belongs to a convex game's core. -/
theorem IsConvex.marginalAllocation_isInCore {G : CoalitionalGame Agent}
    (convex : G.IsConvex) (order : LinearOrder Agent) :
    IsInCore G (G.marginalAllocation order) := by
  let := order
  refine ⟨G.marginalAllocation_efficient order, fun coalition => ?_⟩
  calc
    G.value coalition = ∑ agent ∈ coalition,
        G.marginalContribution agent (coalition.filter (· < agent)) :=
      (sum_ordered_marginals G coalition).symm
    _ ≤ payout (G.marginalAllocation order) coalition := by
      apply Finset.sum_le_sum
      intro agent _
      apply convex.marginalContribution_le
      · exact Finset.filter_subset_filter _ (Finset.subset_univ _)
      · simp

/-- Every finite convex coalitional game has a core allocation. -/
theorem IsConvex.exists_core {G : CoalitionalGame Agent} (convex : G.IsConvex) :
    ∃ allocation : Allocation Agent, IsInCore G allocation := by
  let order : LinearOrder Agent := LinearOrder.lift' (Fintype.equivFin Agent)
    (Fintype.equivFin Agent).injective
  exact ⟨G.marginalAllocation order, convex.marginalAllocation_isInCore order⟩

end GameTheory.CoalitionalGame
