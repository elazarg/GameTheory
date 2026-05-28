/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Generic Reindexing Helpers

Small lemmas for reindexing finite sums and `ENNReal` infinite sums by
involutions.
-/

namespace Math
namespace Reindex

lemma sum_univ_eq_sum_univ_of_involutive
    {α : Type _} [Fintype α] {δ : Type _} [AddCommMonoid δ]
    (e : α → α) (he : Function.Involutive e) (f : α → δ) :
    (∑ x : α, f (e x)) = ∑ x : α, f x := by
  simpa [Function.Involutive.coe_toPerm] using Equiv.sum_comp (he.toPerm e) f

/-- Reindex an `ENNReal` `tsum` by an involution. -/
lemma tsum_eq_tsum_of_involutive
    {α : Type _} (e : α → α) (he : Function.Involutive e) (f : α → ENNReal) :
    (∑' x : α, f (e x)) = ∑' x : α, f x := by
  simpa [Function.Involutive.coe_toPerm] using (he.toPerm e).tsum_eq f

end Reindex
end Math
