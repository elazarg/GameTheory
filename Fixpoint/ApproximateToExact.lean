import Mathlib

set_option autoImplicit false

namespace Fixpoint

open Set
open Function

/--
If a continuous map admits arbitrarily fine approximate fixed points on a compact set,
then it has an exact fixed point on that set.
-/
theorem exists_fixedPoint_of_approx_on_compact
    {X : Type*} [MetricSpace X]
    (S : Set X) (hScompact : IsCompact S)
    (f : X → X) (hcont : Continuous f)
    (happrox : ∀ n : ℕ, ∃ x ∈ S, dist (f x) x ≤ (1 : ℝ) / (n + 1)) :
    ∃ x ∈ S, IsFixedPt f x := by
  let t : ℕ → Set X := fun n => {x | x ∈ S ∧ dist (f x) x ≤ (1 : ℝ) / (n + 1)}

  have hmono : ∀ n, t (n + 1) ⊆ t n := by
    intro n x hx
    rcases hx with ⟨hxS, hxdist⟩
    refine ⟨hxS, ?_⟩
    exact le_trans hxdist (by
      have hpos : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.succ_pos n
      have hlt : (n + 1 : ℝ) < (n + 1) + 1 := by linarith
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using
        (one_div_lt_one_div_of_lt hpos hlt).le)

  have hnonempty : ∀ n, (t n).Nonempty := by
    intro n
    rcases happrox n with ⟨x, hxS, hxdist⟩
    exact ⟨x, ⟨hxS, hxdist⟩⟩

  have hclosed : ∀ n, IsClosed (t n) := by
    intro n
    have hdist_cont : Continuous fun x : X => dist (f x) x :=
      (hcont.dist continuous_id)
    have hdist_closed : IsClosed {x : X | dist (f x) x ≤ (1 : ℝ) / (n + 1)} :=
      isClosed_le hdist_cont continuous_const
    have hSclosed : IsClosed S := hScompact.isClosed
    simpa [t] using hSclosed.inter hdist_closed

  have ht0_compact : IsCompact (t 0) :=
    hScompact.of_isClosed_subset (hclosed 0) (by
      intro x hx
      exact hx.1)

  have hnonempty_iInter : (⋂ n, t n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      t hmono hnonempty ht0_compact hclosed

  rcases hnonempty_iInter with ⟨x, hxall⟩
  have hxS : x ∈ S := by
    exact (mem_iInter.mp hxall 0).1

  have hdist_le_all : ∀ n : ℕ, dist (f x) x ≤ (1 : ℝ) / (n + 1) := by
    intro n
    exact (mem_iInter.mp hxall n).2

  have hdist_zero : dist (f x) x = 0 := by
    by_contra hne
    have hpos : 0 < dist (f x) x := by
      exact lt_of_le_of_ne dist_nonneg (Ne.symm hne)
    rcases exists_nat_one_div_lt hpos with ⟨n, hn⟩
    exact (not_lt_of_ge (hdist_le_all n)) hn

  refine ⟨x, hxS, ?_⟩
  exact dist_eq_zero.mp hdist_zero

end Fixpoint
