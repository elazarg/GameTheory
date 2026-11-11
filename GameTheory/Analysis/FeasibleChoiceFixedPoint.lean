module

/-
# Simultaneous feasible maximizers

Each coordinate chooses from a compact menu that may depend on the entire
current point. Its objective is compared with that point held fixed. Lower
hemicontinuity preserves access to alternatives; closed feasibility preserves
limits; quasiconcavity makes the maximizing sets convex. Kakutani then supplies
simultaneous feasible optimality, with each coordinate's objective kept separate.
-/

public import GameTheory.Math.ParametricOptimality
public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import FixedPointTheorems.kakutani

@[expose] public section

noncomputable section

namespace GameTheory

/-- Changing feasible menus admit simultaneous coordinate maximizers on a
compact convex product envelope. Menu compactness follows from closed fibers
inside that envelope; no extra compactness certificate is required. -/
theorem exists_feasibleChoice_fixedPoint
    {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (outer : ∀ i, Set (E i)) (outer_convex : ∀ i, Convex ℝ (outer i))
    (outer_compact : ∀ i, IsCompact (outer i)) (outer_nonempty : ∀ i, (outer i).Nonempty)
    (feasible : ∀ i, (Set.pi Set.univ outer) → Set (E i))
    (subset : ∀ i x, feasible i x ⊆ outer i)
    (closed_feasible : ∀ i, IsClosed
      {point : (Set.pi Set.univ outer) × E i | point.2 ∈ feasible i point.1})
    (lower_feasible : ∀ i, LowerHemicontinuous (feasible i))
    (nonempty_feasible : ∀ i x, (feasible i x).Nonempty)
    (score : ∀ i, (Set.pi Set.univ outer) × E i → ℝ)
    (continuous_score : ∀ i, Continuous (score i))
    (quasiconcave_score : ∀ i x,
      QuasiconcaveOn ℝ (feasible i x) (fun alternative => score i (x, alternative))) :
    ∃ x : (Set.pi Set.univ outer), ∀ i, x.1 i ∈ feasible i x ∧
      IsMaxOn (fun alternative => score i (x, alternative)) (feasible i x) (x.1 i) := by
  classical
  let domain : Set (∀ i, E i) := Set.pi Set.univ outer
  let replies (x : domain) : Set (∀ i, E i) := Set.pi Set.univ fun i =>
    {chosen | chosen ∈ feasible i x ∧
      ∀ alternative ∈ feasible i x, score i (x, alternative) ≤ score i (x, chosen)}
  have replies_subset (x : domain) : replies x ⊆ domain :=
    fun _ chosen i offered => subset i x (chosen i offered).1
  have replies_convex (x : domain) : Convex ℝ (replies x) := by
    apply convex_pi
    intro i _
    rintro v ⟨hv, vbest⟩ w ⟨hw, wbest⟩ a b ha hb hab
    have quasi := quasiconcaveOn_iff_min_le.mp (quasiconcave_score i x)
    refine ⟨quasi.1 hv hw ha hb hab, fun alternative offered => ?_⟩
    exact (le_min (vbest alternative offered) (wbest alternative offered)).trans
      (quasi.2 hv hw ha hb hab)
  have replies_nonempty (x : domain) : (replies x).Nonempty := by
    have coordinate_nonempty (i : ι) : ∃ chosen ∈ feasible i x,
        ∀ alternative ∈ feasible i x, score i (x, alternative) ≤ score i (x, chosen) := by
      have closed_fiber : IsClosed (feasible i x) := IsClosed.preimage
        (f := fun value : E i => (x, value))
        (continuous_const.prodMk continuous_id) (closed_feasible i)
      obtain ⟨chosen, member, best⟩ :=
        ((outer_compact i).of_isClosed_subset closed_fiber (subset i x)).exists_isMaxOn
          (nonempty_feasible i x)
          ((continuous_score i).comp (continuous_const.prodMk continuous_id)).continuousOn
      exact ⟨chosen, member, fun _ offered => best offered⟩
    choose chosen member best using coordinate_nonempty
    exact ⟨chosen, fun i _ => ⟨member i, best i⟩⟩
  have replies_closed : closedGraph replies := by
    have coordinate_closed (i : ι) : IsClosed
        {point : domain × E i | point.2 ∈ feasible i point.1 ∧
          ∀ alternative ∈ feasible i point.1,
            score i (point.1, alternative) ≤ score i point} :=
      Math.isClosed_feasibleMaximizers (feasible i) (score i)
        (closed_feasible i) (lower_feasible i) (continuous_score i)
    show IsClosed _
    have graph_eq : {point : domain × (∀ i, E i) | point.2 ∈ replies point.1} =
        ⋂ i, {point : domain × (∀ i, E i) | point.2 i ∈ feasible i point.1 ∧
          ∀ alternative ∈ feasible i point.1,
            score i (point.1, alternative) ≤ score i (point.1, point.2 i)} := by
      ext point
      simp [replies]
    rw [graph_eq]
    exact isClosed_iInter fun i => IsClosed.preimage
      (f := fun point : domain × (∀ j, E j) => (point.1, point.2 i))
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)) (coordinate_closed i)
  have domain_nonempty : domain.Nonempty := by
    choose chosen member using outer_nonempty
    exact ⟨chosen, fun i _ => member i⟩
  obtain ⟨x, optimal⟩ := kakutani_fixed_point domain (convex_pi fun i _ => outer_convex i)
    (isCompact_univ_pi outer_compact) domain_nonempty replies replies_closed
    (fun x => ⟨replies_subset x, replies_convex x, replies_nonempty x⟩)
  exact ⟨x, fun i => ⟨(optimal i (Set.mem_univ i)).1,
    fun _ offered => (optimal i (Set.mem_univ i)).2 _ offered⟩⟩

end GameTheory
