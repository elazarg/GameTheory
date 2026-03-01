import Mathlib

set_option autoImplicit false

namespace Fixpoint

open scoped BigOperators

section Core

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Indices with strictly positive coordinate in a simplex point. -/
noncomputable def positiveSupport (x : stdSimplex ℝ ι) : Finset ι :=
  Finset.univ.filter (fun i => 0 < x i)

@[simp] theorem mem_positiveSupport (x : stdSimplex ℝ ι) (i : ι) :
    i ∈ positiveSupport x ↔ 0 < x i := by
  simp [positiveSupport]

/-- A simplex point has at least one strictly positive coordinate. -/
theorem positiveSupport_nonempty (x : stdSimplex ℝ ι) : (positiveSupport x).Nonempty := by
  by_contra hnon
  have hempty : positiveSupport x = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnon
  have hzero : ∀ i : ι, x i = 0 := by
    intro i
    have hnotlt : ¬ 0 < x i := by
      intro hi
      have hmem : i ∈ positiveSupport x := by
        simpa [mem_positiveSupport] using hi
      simpa [hempty] using hmem
    exact le_antisymm (le_of_not_gt hnotlt) (stdSimplex.zero_le x i)
  have hsum0 : (∑ i : ι, x i) = 0 := by
    simp [hzero]
  have hsum1 : (∑ i : ι, x i) = 1 := stdSimplex.sum_eq_one x
  linarith

/-- Choose an index in positive support maximizing `g`. -/
noncomputable def argmaxOnPositiveSupport (x : stdSimplex ℝ ι) (g : ι → ℝ) : ι :=
  Classical.choose (Finset.exists_max_image (positiveSupport x) g (positiveSupport_nonempty x))

theorem argmaxOnPositiveSupport_mem (x : stdSimplex ℝ ι) (g : ι → ℝ) :
    argmaxOnPositiveSupport x g ∈ positiveSupport x := by
  exact (Classical.choose_spec
    (Finset.exists_max_image (positiveSupport x) g (positiveSupport_nonempty x))).1

theorem le_argmaxOnPositiveSupport (x : stdSimplex ℝ ι) (g : ι → ℝ)
    {j : ι} (hj : j ∈ positiveSupport x) :
    g j ≤ g (argmaxOnPositiveSupport x g) := by
  exact (Classical.choose_spec
    (Finset.exists_max_image (positiveSupport x) g (positiveSupport_nonempty x))).2 j hj

/-- Sperner-style label from coordinate differences `x_i - f(x)_i`, restricted to positive support. -/
noncomputable def spernerLabel
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (x : stdSimplex ℝ ι) : ι :=
  argmaxOnPositiveSupport x (fun i => x i - f x i)

theorem spernerLabel_mem_positiveSupport
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (x : stdSimplex ℝ ι) :
    spernerLabel f x ∈ positiveSupport x :=
  argmaxOnPositiveSupport_mem x (fun i => x i - f x i)

theorem spernerLabel_pos
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (x : stdSimplex ℝ ι) :
    0 < x (spernerLabel f x) := by
  simpa [mem_positiveSupport] using spernerLabel_mem_positiveSupport f x

/-- Boundary admissibility consequence: a zero coordinate cannot be the label. -/
theorem spernerLabel_ne_of_coord_eq_zero
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (x : stdSimplex ℝ ι) (i : ι) (hi : x i = 0) :
    spernerLabel f x ≠ i := by
  intro hEq
  have hpos : 0 < x (spernerLabel f x) := spernerLabel_pos f x
  simpa [hEq, hi] using hpos

theorem sub_le_sub_at_spernerLabel
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (x : stdSimplex ℝ ι) {j : ι} (hj : 0 < x j) :
    x j - f x j ≤ x (spernerLabel f x) - f x (spernerLabel f x) := by
  have hj' : j ∈ positiveSupport x := by
    simpa [mem_positiveSupport] using hj
  simpa [spernerLabel] using
    (le_argmaxOnPositiveSupport x (fun i => x i - f x i) hj')

/-- On the positive support of `x`, the total displacement `x_i - f(x)_i` has nonnegative sum. -/
theorem sum_sub_nonneg_on_positiveSupport
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (x : stdSimplex ℝ ι) :
    0 ≤ Finset.sum (positiveSupport x) (fun i => x i - f x i) := by
  have hx_sum_support : Finset.sum (positiveSupport x) (fun i => x i) = 1 := by
    calc
      Finset.sum (positiveSupport x) (fun i => x i)
          = Finset.sum Finset.univ (fun i : ι => if 0 < x i then x i else 0) := by
              simpa [positiveSupport, Finset.sum_filter]
      _ = Finset.sum Finset.univ (fun i : ι => x i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hix : 0 < x i
            · simp [hix]
            · have hix0 : x i = 0 :=
                le_antisymm (le_of_not_gt hix) (stdSimplex.zero_le x i)
              simp [hix, hix0]
      _ = 1 := stdSimplex.sum_eq_one x
  have hf_sum_support_le : Finset.sum (positiveSupport x) (fun i => f x i) ≤ 1 := by
    calc
      Finset.sum (positiveSupport x) (fun i => f x i) ≤ Finset.sum Finset.univ (fun i : ι => f x i) :=
        Finset.sum_le_univ_sum_of_nonneg (fun i => stdSimplex.zero_le (f x) i)
      _ = 1 := stdSimplex.sum_eq_one (f x)
  have hsub :
      Finset.sum (positiveSupport x) (fun i => x i - f x i)
        = Finset.sum (positiveSupport x) (fun i => x i)
          - Finset.sum (positiveSupport x) (fun i => f x i) := by
    simp [sub_eq_add_neg, Finset.sum_add_distrib]
  rw [hsub]
  linarith

/-- There exists a positive-support coordinate with nonnegative displacement. -/
theorem exists_nonneg_sub_on_positiveSupport
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (x : stdSimplex ℝ ι) :
    ∃ i ∈ positiveSupport x, 0 ≤ x i - f x i := by
  by_contra hnone
  have hsne : (positiveSupport x).Nonempty := positiveSupport_nonempty x
  have hallneg : ∀ i ∈ positiveSupport x, x i - f x i < 0 := by
    intro i hi
    exact lt_of_not_ge (by
      intro hge
      exact hnone ⟨i, hi, hge⟩)
  have hsum_lt :
      Finset.sum (positiveSupport x) (fun i => x i - f x i)
        < Finset.sum (positiveSupport x) (fun _ => (0 : ℝ)) := by
    exact Finset.sum_lt_sum_of_nonempty hsne (fun i hi => by simpa using hallneg i hi)
  have hsum_nonneg : 0 ≤ Finset.sum (positiveSupport x) (fun i => x i - f x i) :=
    sum_sub_nonneg_on_positiveSupport f x
  have : ¬ (Finset.sum (positiveSupport x) (fun i => x i - f x i) < 0) := not_lt_of_ge hsum_nonneg
  exact this (by simpa using hsum_lt)

/-- The Sperner label has nonnegative displacement. -/
theorem sub_nonneg_at_spernerLabel
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (x : stdSimplex ℝ ι) :
    0 ≤ x (spernerLabel f x) - f x (spernerLabel f x) := by
  rcases exists_nonneg_sub_on_positiveSupport f x with ⟨j, hjmem, hjnonneg⟩
  have hjpos : 0 < x j := by simpa [mem_positiveSupport] using hjmem
  exact le_trans hjnonneg (sub_le_sub_at_spernerLabel f x hjpos)

end Core

end Fixpoint
