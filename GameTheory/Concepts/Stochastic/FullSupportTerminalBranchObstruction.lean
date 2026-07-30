/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PlayerNeutralAnalyticDeflationTerminal
import GameTheory.Concepts.Stochastic.PublicRecurrentClassSupportRank
import Math.Probability.BoundedRealizedAccountAlternative
import Math.Probability.FullSupportChargedClassRegeneration

/-!
# Exact obstruction in the full-support terminal branch

The one-state self-loop is the smallest full-active-support positive charged
class.  It has perfect regeneration, but its support rank cannot decrease
and its constant positive realized charge has no bounded account.  An
arbitrary full payoff-vector target also need not match the recurrent target.

Thus full support, positive aggregate charge, and regeneration do not form a
new atlas leaf by themselves.  The branch needs at least one genuinely new
input:

* a lower independent lexicographic rank coordinate;
* an explicit whole-vector target identification; or
* a realized charge with bounded cumulative sums (equivalently, a bounded
  realized account).
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace FullSupportTerminalBranchObstruction

open Math.Probability
open Math.Probability.EntryReachablePositiveChargedCirculation

abbrev State := Unit
abbrev Index := Unit
abbrev Player := Bool

def kernel (_ : Index) : PMF State :=
  PMF.pure ()

def source (_ : Index) : State :=
  ()

def charge (_ : Index) : ℝ :=
  1

def mass (_ : Index) : ℝ :=
  1

/-- The unit self-loop is reachable from its unique entry. -/
theorem source_reachable (_ : Index) :
    AvailableReachable kernel source () (source ()) :=
  Relation.ReflTransGen.refl

/-- Restriction to entry-reachable indices preserves the unit circulation. -/
theorem restricted_positiveCirculation :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn
        (fun i : ReachableOccupationIndex kernel source () =>
          kernel i.1)
        (fun i : ReachableOccupationIndex kernel source () =>
          source i.1))
      (fun i : ReachableOccupationIndex kernel source () =>
        charge i.1) := by
  apply restrict_positiveChargedCirculation_of_mass_support
    kernel source charge () mass
  · intro i
    simp [mass]
  · intro destination
    cases destination
    simp [mass, actualOccupationColumn, kernel, source]
  · simp [mass, charge]
  · intro i _
    exact source_reachable i

/-- Canonical entry-reachable charged circulation for the unit example. -/
def circulation :
    EntryReachablePositiveChargedCirculation
      kernel source charge () :=
  Classical.choice
    (of_hasNormalizedPositiveChargedCirculation
      restricted_positiveCirculation)

/-- Select the positive communicating class supplied by the circulation. -/
def positiveClass :
    PositiveCommunicatingClass circulation :=
  Classical.choice circulation.exists_positiveCommunicatingClass

/-- The positive class is the entire active support. -/
theorem positiveClass_fullSupport :
    positiveClass.IsFullActiveSupportClass := by
  have hstates :
      positiveClass.closedClass.states =
        (Finset.univ : Finset (circulation.ActiveState)) := by
    apply Finset.eq_univ_of_forall
    intro state
    have hstate :
        state = positiveClass.representative :=
      Subsingleton.elim _ _
    subst state
    simpa only [positiveClass.closedClass_entry] using
      positiveClass.closedClass.entry_mem
  rcases positiveClass.properSupportRankDescent_or_fullActiveSupport
    with hproper | hfull
  · exact False.elim (hproper.1.ne hstates)
  · exact hfull

/-- The full-support branch has the promised fixed-kernel regeneration
data. -/
def regeneration :
    PositiveCommunicatingClass.FullSupportRegeneration
      circulation positiveClass :=
  Classical.choice
    (PositiveCommunicatingClass.exists_fullSupportRegeneration
      circulation positiveClass positiveClass_fullSupport)

/-- Full support is exactly the non-descent branch of support cardinality. -/
theorem no_properSupportRankDescent :
    ¬positiveClass.HasProperSupportRankDescent := by
  intro proper
  exact proper.1.ne positiveClass_fullSupport.1

/-- The class support rank is unchanged despite positive charge and
regeneration. -/
theorem supportRank_eq_activeSupportRank :
    positiveClass.supportRank = circulation.activeSupportRank :=
  regeneration.same_rank

/-- A realized stage charge that is constantly positive. -/
def realizedCharge (_ : ℕ) : ℝ :=
  1

/-- The realized sequence is exactly the unique operational transition's
charge at every stage. -/
theorem realizedCharge_eq_operationalCharge (T : ℕ) :
    realizedCharge T = charge () := by
  rfl

/-- Constant unit charge has linearly growing cumulative sums. -/
theorem cumulative_realizedCharge (T : ℕ) :
    cumulativeChargeAccount realizedCharge T = T := by
  simp [cumulativeChargeAccount, realizedCharge]

/-- Every proposed cumulative-charge bound is eventually exceeded. -/
theorem realizedCharge_unbounded :
    ∀ bound : ℝ, ∃ T,
      bound < |cumulativeChargeAccount realizedCharge T| := by
  intro bound
  obtain ⟨T, hT⟩ := exists_nat_gt bound
  refine ⟨T, ?_⟩
  rw [cumulative_realizedCharge]
  simpa using hT

/-- No bounded account can realize the constant positive charge. -/
theorem no_boundedRealizedAccount :
    ¬∃ (account : ℕ → ℝ) (bound : ℝ),
      (∀ T, |account T| ≤ bound) ∧
        IsRealizedByAccount realizedCharge account := by
  intro bounded
  have cumulativeBounded :
      HasBoundedCumulativeCharge realizedCharge :=
    (hasBoundedCumulativeCharge_iff_exists_boundedAccount
      realizedCharge).2 bounded
  obtain ⟨bound, hbound⟩ := cumulativeBounded
  obtain ⟨T, hT⟩ := realizedCharge_unbounded bound
  exact (not_lt_of_ge (hbound T)) hT

/-- The recurrent payoff vector can disagree with an arbitrary parent
target even in the one-state full-support class. -/
def recurrentTarget (_ : State) (who : Player) : ℝ :=
  if who then 0 else 1

def parentTarget (_ : Player) : ℝ :=
  1

theorem full_target_not_preserved :
    recurrentTarget () ≠ parentTarget := by
  intro equal
  have coordinate := congrFun equal true
  norm_num [recurrentTarget, parentTarget] at coordinate

/-- The smallest full-support example simultaneously has regeneration,
same support rank, target failure, and no bounded realized account. -/
theorem fullSupportRegeneration_without_descent_or_discharge :
    positiveClass.IsFullActiveSupportClass ∧
      Nonempty
        (PositiveCommunicatingClass.FullSupportRegeneration
          circulation positiveClass) ∧
      positiveClass.supportRank = circulation.activeSupportRank ∧
      recurrentTarget () ≠ parentTarget ∧
      ¬∃ (account : ℕ → ℝ) (bound : ℝ),
        (∀ T, |account T| ≤ bound) ∧
          IsRealizedByAccount realizedCharge account :=
  ⟨positiveClass_fullSupport, ⟨regeneration⟩,
    supportRank_eq_activeSupportRank, full_target_not_preserved,
    no_boundedRealizedAccount⟩

end FullSupportTerminalBranchObstruction
end StochasticGame
end GameTheory
