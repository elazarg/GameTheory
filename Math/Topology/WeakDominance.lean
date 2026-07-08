/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Order.Zorn
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Compact upper-semicontinuous weak dominance

This file contains a game-free compactness lemma for pointwise weak dominance.
If own payoffs are upper-semicontinuous on a compact strategy space, every
strategy has an undominated weak dominator.  The proof is Zorn's lemma plus the
finite-intersection property for compact spaces.
-/

noncomputable section

namespace Math
namespace Topology

/-- `s` pointwise weakly dominates `t` for payoff kernel `W`. -/
def PointwiseWeaklyDominates {α β : Type*} (W : α → β → ℝ) (s t : α) : Prop :=
  ∀ b : β, W t b ≤ W s b

/-- Pointwise weak dominance with at least one strict coordinate. -/
def PointwiseWeaklyStrictlyDominates {α β : Type*} (W : α → β → ℝ) (s t : α) :
    Prop :=
  PointwiseWeaklyDominates W s t ∧ ∃ b : β, W t b < W s b

/-- No other point pointwise weakly dominates this one with a strict witness. -/
def PointwiseUndominated {α β : Type*} (W : α → β → ℝ) (s : α) : Prop :=
  ∀ t : α, ¬ PointwiseWeaklyStrictlyDominates W t s

theorem PointwiseWeaklyDominates.refl {α β : Type*} (W : α → β → ℝ) (s : α) :
    PointwiseWeaklyDominates W s s := fun _ => le_rfl

theorem PointwiseWeaklyDominates.trans {α β : Type*} {W : α → β → ℝ} {r s t : α}
    (hrs : PointwiseWeaklyDominates W r s) (hst : PointwiseWeaklyDominates W s t) :
    PointwiseWeaklyDominates W r t := fun b => (hst b).trans (hrs b)

/-- Raising the value of an upper-semicontinuous real function at one closed
point preserves upper-semicontinuity. -/
theorem UpperSemicontinuous.update_of_le
    {α : Type*} [TopologicalSpace α] [T1Space α] [DecidableEq α]
    {f : α → ℝ} (hf : UpperSemicontinuous f) {a : α} {y : ℝ}
    (hfa : f a ≤ y) :
    UpperSemicontinuous (fun x : α => if x = a then y else f x) := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro c
  by_cases hcy : c ≤ y
  · have hclosed_f : IsClosed (f ⁻¹' Set.Ici c) := hf.isClosed_preimage c
    have hclosed_single : IsClosed ({a} : Set α) := isClosed_singleton
    have heq :
        (fun x : α => if x = a then y else f x) ⁻¹' Set.Ici c =
          f ⁻¹' Set.Ici c ∪ ({a} : Set α) := by
      ext x
      by_cases hxa : x = a
      · subst hxa
        simp [hcy]
      · simp [hxa]
    rw [heq]
    exact hclosed_f.union hclosed_single
  · have hyc : y < c := lt_of_not_ge hcy
    have hnot_fa : ¬ c ≤ f a := by linarith
    have hclosed_f : IsClosed (f ⁻¹' Set.Ici c) := hf.isClosed_preimage c
    have heq :
        (fun x : α => if x = a then y else f x) ⁻¹' Set.Ici c =
          f ⁻¹' Set.Ici c := by
      ext x
      by_cases hxa : x = a
      · subst hxa
        simp [hcy, hnot_fa]
      · simp [hxa]
    rw [heq]
    exact hclosed_f

private theorem exists_chain_upper_bound
    {α β : Type*} [TopologicalSpace α] [CompactSpace α]
    (W : α → β → ℝ) (husc : ∀ b : β, UpperSemicontinuousOn (fun a : α => W a b) Set.univ)
    (s : α)
    (D : Set α) (hD : D = {t : α | PointwiseWeaklyDominates W t s})
    (c : Set {t : α // t ∈ D})
    (hc : IsChain (fun x y : {t : α // t ∈ D} => PointwiseWeaklyDominates W y.1 x.1) c)
    (hne : c.Nonempty) :
    ∃ ub : {t : α // t ∈ D},
      ∀ a ∈ c, PointwiseWeaklyDominates W ub.1 a.1 := by
  classical
  let R : {t : α // t ∈ D} → {t : α // t ∈ D} → Prop :=
    fun x y => PointwiseWeaklyDominates W y.1 x.1
  haveI : Std.Refl R := ⟨fun x => PointwiseWeaklyDominates.refl W x.1⟩
  obtain ⟨a₀, ha₀c⟩ := hne
  let Idx : Type _ := {a : {t : α // t ∈ D} // a ∈ c} × β
  let closedSet : Idx → Set α := fun idx =>
    {x : α | W idx.1.1.1 idx.2 ≤ W x idx.2}
  have hclosed : ∀ idx : Idx, IsClosed (closedSet idx) := by
    intro idx
    have hglobal :
        UpperSemicontinuous (fun a : α => W a idx.2) :=
      upperSemicontinuousOn_univ_iff.mp (husc idx.2)
    change IsClosed ((fun a : α => W a idx.2) ⁻¹' Set.Ici (W idx.1.1.1 idx.2))
    exact hglobal.isClosed_preimage (W idx.1.1.1 idx.2)
  have hfinite :
      ∀ u : Finset Idx, (Set.univ ∩ ⋂ idx ∈ u, closedSet idx).Nonempty := by
    intro u
    by_cases hu : u.Nonempty
    · have hupper :
          ∃ z : {a : {t : α // t ∈ D} // a ∈ c},
            ∀ idx ∈ u, R idx.1.1 z.1 := by
        induction u using Finset.induction_on with
        | empty =>
            rcases hu with ⟨idx, hidx⟩
            simp at hidx
        | insert idx₀ u hidxu ih =>
            by_cases hu' : u.Nonempty
            · obtain ⟨z, hz⟩ := ih hu'
              have hcomp := hc.total idx₀.1.2 z.2
              rcases hcomp with hle | hge
              · exact ⟨z, fun j hj => by
                  rw [Finset.mem_insert] at hj
                  rcases hj with hji | hju
                  · simpa [hji] using hle
                  · exact hz j hju⟩
              · exact ⟨idx₀.1, fun j hj => by
                  rw [Finset.mem_insert] at hj
                  rcases hj with hji | hju
                  · simpa [hji, R] using
                      (PointwiseWeaklyDominates.refl W idx₀.1.1.1)
                  · exact PointwiseWeaklyDominates.trans hge (hz j hju)⟩
            · have hu_empty : u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hu'
              subst u
              exact ⟨idx₀.1, fun j hj => by
                have hji : j = idx₀ := by simpa using hj
                simpa [hji, R] using
                  (PointwiseWeaklyDominates.refl W idx₀.1.1.1)⟩
      obtain ⟨z, hz⟩ := hupper
      refine ⟨z.1.1, ⟨Set.mem_univ _, ?_⟩⟩
      exact Set.mem_iInter.mpr fun idx =>
        Set.mem_iInter.mpr fun hidx => hz idx hidx idx.2
    · refine ⟨a₀.1, ⟨Set.mem_univ _, ?_⟩⟩
      change a₀.1 ∈ ⋂ idx : Idx, ⋂ _ : idx ∈ u, closedSet idx
      simp [Finset.not_nonempty_iff_eq_empty.mp hu]
  obtain ⟨x, hx⟩ := isCompact_univ.inter_iInter_nonempty closedSet hclosed hfinite
  have hxall : ∀ idx : Idx, x ∈ closedSet idx := by
    intro idx
    exact Set.mem_iInter.mp hx.2 idx
  have hxD : x ∈ D := by
    rw [hD]
    intro b
    have hxa₀ : W a₀.1 b ≤ W x b :=
      hxall (⟨a₀, ha₀c⟩, b)
    have ha₀D : PointwiseWeaklyDominates W a₀.1 s := by
      simpa [hD] using a₀.2
    exact (ha₀D b).trans hxa₀
  refine ⟨⟨x, hxD⟩, ?_⟩
  intro a hac b
  exact hxall (⟨a, hac⟩, b)

/-- On a compact own-strategy space, upper-semicontinuity of every column is
enough to continue any strategy upward to an undominated point for pointwise
weak dominance. -/
theorem exists_pointwiseUndominated_dominator_of_compact_usc
    {α β : Type*} [TopologicalSpace α] [CompactSpace α]
    (W : α → β → ℝ)
    (husc : ∀ b : β, UpperSemicontinuousOn (fun a : α => W a b) Set.univ)
    (s : α) :
    ∃ t : α, PointwiseWeaklyDominates W t s ∧ PointwiseUndominated W t := by
  classical
  let D : Set α := {t : α | PointwiseWeaklyDominates W t s}
  let αD : Type _ := {t : α // t ∈ D}
  let R : αD → αD → Prop := fun x y => PointwiseWeaklyDominates W y.1 x.1
  haveI : Nonempty αD := ⟨⟨s, PointwiseWeaklyDominates.refl W s⟩⟩
  have htrans : ∀ {a b c : αD}, R a b → R b c → R a c := by
    intro a b c hab hbc
    exact PointwiseWeaklyDominates.trans hbc hab
  have hchains :
      ∀ c : Set αD, IsChain R c → c.Nonempty → ∃ ub, ∀ a ∈ c, R a ub := by
    intro c hc hne
    exact exists_chain_upper_bound W husc s D rfl c hc hne
  obtain ⟨m, hm⟩ := exists_maximal_of_nonempty_chains_bounded
    (r := R) hchains htrans
  refine ⟨m.1, m.2, ?_⟩
  intro u hu
  obtain ⟨hweak, b, hstrict⟩ := hu
  have huD : u ∈ D := by
    intro b
    exact (m.2 b).trans (hweak b)
  have hmu : R m ⟨u, huD⟩ := hweak
  have hum : R ⟨u, huD⟩ m := hm ⟨u, huD⟩ hmu
  exact not_lt_of_ge (hum b) hstrict

end Topology
end Math
