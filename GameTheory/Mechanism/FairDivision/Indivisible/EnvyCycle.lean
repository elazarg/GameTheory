/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Mechanism.FairDivision.Indivisible.RoundRobin
import Math.Fintype.Transport
import Mathlib.Data.Fintype.EquivFin

/-!
# Indivisible Fair Division: Finite-Agent EF1 Selector

This module supplies a finite-agent EF1 allocation selector. The construction
relabels an arbitrary finite nonempty agent type by `Fin (Fintype.card ι)`,
applies the certified round-robin rule, and transports the allocation back.

The construction is theorem-first: it provides the EF1 existence package without
formalizing the cycle-rotation procedure.
-/

namespace GameTheory
namespace SocialChoice
namespace FairDivision
namespace Indivisible

open Finset

variable {ι G : Type*}

private theorem relabelFinValuation_nonnegative {n : ℕ} (e : ι ≃ Fin n)
    {v : AdditiveValuation ι G} (hnn : Nonnegative v) :
    Nonnegative (Math.Fintype.reindex e v) := by
  intro i g
  exact hnn (e.symm i) g

private theorem value_relabelFinValuation {n : ℕ} [DecidableEq G]
    (e : ι ≃ Fin n) (v : AdditiveValuation ι G) (i : ι) (S : Finset G) :
    value (Math.Fintype.reindex e v) (e i) S = value v i S := by
  simp [Math.Fintype.reindex, value]

private theorem pullbackFinAllocation_isAllocation {n : ℕ} [Fintype G]
    [DecidableEq G] (e : ι ≃ Fin n) {A : Allocation (Fin n) G}
    (hA : IsAllocation A) :
    IsAllocation (Math.Fintype.pullback e A) := by
  constructor
  · intro i j hij
    exact hA.1 (e i) (e j) (e.injective.ne hij)
  · intro g
    rcases hA.2 g with ⟨k, hk⟩
    exact ⟨e.symm k, by simpa [Math.Fintype.pullback] using hk⟩

private theorem pullbackFinAllocation_isEF1 {n : ℕ} [DecidableEq G]
    (e : ι ≃ Fin n) {v : AdditiveValuation ι G}
    {A : Allocation (Fin n) G}
    (hA : IsEF1 (Math.Fintype.reindex e v) A) :
    IsEF1 v (Math.Fintype.pullback e A) := by
  intro i j
  specialize hA (e i) (e j)
  rw [value_relabelFinValuation e v i] at hA
  rw [value_relabelFinValuation e v i] at hA
  rcases hA with hnoenvy | ⟨g, hg, hle⟩
  · exact Or.inl (by simpa [Math.Fintype.pullback] using hnoenvy)
  · exact Or.inr ⟨g, by simpa [Math.Fintype.pullback] using hg, by
      simpa [Math.Fintype.pullback, value_relabelFinValuation e v i] using hle⟩

/-- A finite-agent EF1 allocation selected by relabeling agents to `Fin` and
using the certified round-robin rule. -/
noncomputable def envyCycleAllocation [Fintype ι] [Nonempty ι]
    [Fintype G] [DecidableEq G] (v : AdditiveValuation ι G) :
    Allocation ι G :=
  let e := Fintype.equivFin ι
  Math.Fintype.pullback e (roundRobinAllocation (Math.Fintype.reindex e v))

/-- The selected finite-agent EF1 allocation as a certified feasible-allocation rule. -/
noncomputable def envyCycleRule [Fintype ι] [Nonempty ι]
    [Fintype G] [DecidableEq G] (v : AdditiveValuation ι G) :
    {A : Allocation ι G // IsAllocation A} :=
  ⟨envyCycleAllocation v, by
    dsimp [envyCycleAllocation]
    exact pullbackFinAllocation_isAllocation (Fintype.equivFin ι)
      (roundRobinAllocation_isAllocation
        (Math.Fintype.reindex (Fintype.equivFin ι) v))⟩

/-- `envyCycleAllocation` produces a complete partition of the goods. -/
theorem envyCycleAllocation_isAllocation [Fintype ι] [Nonempty ι]
    [Fintype G] [DecidableEq G] (v : AdditiveValuation ι G) :
    IsAllocation (envyCycleAllocation v) :=
  (envyCycleRule v).2

/-- The selected finite-agent allocation is EF1 under nonnegative item values. -/
theorem envyCycleAllocation_isEF1 [Fintype ι] [Nonempty ι]
    [Fintype G] [DecidableEq G] (v : AdditiveValuation ι G)
    (hnn : Nonnegative v) :
    IsEF1 v (envyCycleAllocation v) := by
  dsimp [envyCycleAllocation]
  exact pullbackFinAllocation_isEF1 (Fintype.equivFin ι)
    (roundRobinAllocation_isEF1 (Math.Fintype.reindex (Fintype.equivFin ι) v)
      (relabelFinValuation_nonnegative (Fintype.equivFin ι) hnn))

/-- The bundled finite-agent rule is EF1 under nonnegative item values. -/
theorem envyCycleRule_isEF1 [Fintype ι] [Nonempty ι]
    [Fintype G] [DecidableEq G] (v : AdditiveValuation ι G)
    (hnn : Nonnegative v) :
    IsEF1 v (envyCycleRule v).1 :=
  envyCycleAllocation_isEF1 v hnn

end Indivisible
end FairDivision
end SocialChoice
end GameTheory
