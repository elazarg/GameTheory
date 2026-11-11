module

/-
# Closed graphs of feasible maximizers

A closed feasible graph preserves feasibility at limits. Lower hemicontinuity
also preserves access to strictly better alternatives nearby; it is a separate
requirement. Together with a jointly continuous objective, these laws give a
closed graph of feasible maximizers. Existence, compactness and convexity are
independent questions and are not assumptions of this closedness theorem.
-/

public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.Filter.Extr

@[expose] public section

namespace GameTheory.Math

/-- Feasible maximizers have a closed graph when feasible alternatives vary
lower hemicontinuously and the objective is jointly continuous. -/
theorem isClosed_feasibleMaximizers {X Y Score : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [LinearOrder Score] [TopologicalSpace Score] [OrderClosedTopology Score]
    (feasible : X → Set Y) (objective : X × Y → Score)
    (closed : IsClosed {point : X × Y | point.2 ∈ feasible point.1})
    (lower : LowerHemicontinuous feasible) (continuous : Continuous objective) :
    IsClosed {point : X × Y | point.2 ∈ feasible point.1 ∧
      IsMaxOn (fun alternative => objective (point.1, alternative))
        (feasible point.1) point.2} := by
  let better : (X × Y) → Set Y :=
    fun point => {alternative | objective point < objective (point.1, alternative)}
  have better_open : HasOpenCGraph better :=
    isOpen_lt (continuous.comp continuous_fst)
      (continuous.comp (continuous_fst.fst.prodMk continuous_snd))
  have available_lower : LowerHemicontinuous (fun point : X × Y => feasible point.1) :=
    lower.comp continuous_fst
  have improving_open : IsOpen
      {point : X × Y | (feasible point.1 ∩ better point).Nonempty} := by
    have lower := available_lower.inter_hasOpenCGraph better_open
    simpa only [Set.inter_univ] using
      (lowerHemicontinuous_iff_isOpen_inter_nonempty.mp lower) Set.univ isOpen_univ
  have graph_eq : {point : X × Y | point.2 ∈ feasible point.1 ∧
      IsMaxOn (fun alternative => objective (point.1, alternative))
        (feasible point.1) point.2} =
      {point : X × Y | point.2 ∈ feasible point.1} ∩
        {point : X × Y | (feasible point.1 ∩ better point).Nonempty}ᶜ := by
    ext point
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff,
      isMaxOn_iff, Set.Nonempty, better, not_exists, not_and, not_lt]
  rw [graph_eq]
  exact closed.inter improving_open.isClosed_compl

end GameTheory.Math
