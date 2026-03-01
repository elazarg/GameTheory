import Mathlib
import Fixpoint.BrouwerFromApprox

set_option autoImplicit false

namespace Fixpoint

open scoped BigOperators

section UniformCoordControl

variable {ι : Type*} [Fintype ι]

/-- Coordinate displacement map `x ↦ x_i - f(x)_i` is uniformly continuous on the simplex. -/
theorem uniformContinuous_coordDisplacement
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (hcont : Continuous f)
    (i : ι) :
    UniformContinuous (fun x : stdSimplex ℝ ι => x i - f x i) := by
  have h1 : Continuous (fun x : stdSimplex ℝ ι => x i) :=
    (continuous_apply i).comp continuous_subtype_val
  have h2 : Continuous (fun x : stdSimplex ℝ ι => f x i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp hcont)
  exact CompactSpace.uniformContinuous_of_continuous (h1.sub h2)

/-- Quantitative form of uniform continuity for a fixed displacement coordinate. -/
theorem exists_delta_coordDisplacement_lt
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (hcont : Continuous f)
    (i : ι)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃x y : stdSimplex ℝ ι⦄, dist x y < δ →
      |(x i - f x i) - (y i - f y i)| < ε := by
  have huc : UniformContinuous (fun x : stdSimplex ℝ ι => x i - f x i) :=
    uniformContinuous_coordDisplacement f hcont i
  rcases (Metric.uniformContinuous_iff.1 huc) ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro x y hxy
  have hdist : dist (x i - f x i) (y i - f y i) < ε := hδ hxy
  simpa [Real.dist_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdist

/-- A single `δ` controls displacement variation on all coordinates simultaneously. -/
theorem exists_delta_coordDisplacement_le_all
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (hcont : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃x y : stdSimplex ℝ ι⦄, dist x y < δ →
      ∀ i : ι, |(x i - f x i) - (y i - f y i)| ≤ ε := by
  let disp : stdSimplex ℝ ι → (ι → ℝ) := fun x i => x i - f x i
  have hdisp_cont : Continuous disp := by
    refine continuous_pi ?_
    intro i
    have h1 : Continuous (fun x : stdSimplex ℝ ι => x i) :=
      (continuous_apply i).comp continuous_subtype_val
    have h2 : Continuous (fun x : stdSimplex ℝ ι => f x i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp hcont)
    exact h1.sub h2
  have huc : UniformContinuous disp :=
    CompactSpace.uniformContinuous_of_continuous hdisp_cont
  rcases (Metric.uniformContinuous_iff.1 huc) ε hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro x y hxy i
  have hdist_le : dist (disp x) (disp y) ≤ ε := le_of_lt (hδ hxy)
  have hcoord_le : dist (disp x i) (disp y i) ≤ ε :=
    (dist_pi_le_iff (le_of_lt hε)).1 hdist_le i
  simpa [disp, Real.dist_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hcoord_le

section FiniteBounds

/-- A coordinatewise lower bound together with zero total sum gives a uniform absolute bound. -/
theorem abs_le_card_mul_of_sum_eq_zero_of_lower_bound
    (d : ι → ℝ) {ε : ℝ}
    (hsum : Finset.sum Finset.univ (fun i : ι => d i) = 0)
    (hε : 0 ≤ ε)
    (hlow : ∀ i : ι, -ε ≤ d i) :
    ∀ i : ι, |d i| ≤ (Fintype.card ι : ℝ) * ε := by
  classical
  intro i
  have hsplit : d i + Finset.sum (Finset.univ.erase i) (fun j => d j) = 0 := by
    calc
      d i + Finset.sum (Finset.univ.erase i) (fun j => d j)
          = Finset.sum Finset.univ (fun j : ι => d j) := by
        symm
        simp [Finset.mem_univ]
      _ = 0 := hsum
  have hdi : d i = -Finset.sum (Finset.univ.erase i) (fun j => d j) := by
    exact eq_neg_of_add_eq_zero_left hsplit
  have hsum_lower :
      Finset.sum (Finset.univ.erase i) (fun _ => (-ε))
        ≤ Finset.sum (Finset.univ.erase i) (fun j => d j) := by
    exact Finset.sum_le_sum (fun j hj => hlow j)
  have hupper' :
      d i ≤ ((Finset.univ.erase i).card : ℝ) * ε := by
    calc
      d i = -Finset.sum (Finset.univ.erase i) (fun j => d j) := hdi
      _ ≤ -Finset.sum (Finset.univ.erase i) (fun _ => (-ε)) := by exact neg_le_neg hsum_lower
      _ = ((Finset.univ.erase i).card : ℝ) * ε := by simp
  have hcardleNat : (Finset.univ.erase i).card ≤ Fintype.card ι := by
    exact le_of_lt (by simpa using Finset.card_erase_lt_of_mem (Finset.mem_univ i))
  have hcardle : ((Finset.univ.erase i).card : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast hcardleNat
  have hupper : d i ≤ (Fintype.card ι : ℝ) * ε := by
    exact le_trans hupper' (mul_le_mul_of_nonneg_right hcardle hε)
  have hcard_ge_one_nat : 1 ≤ Fintype.card ι := by
    exact Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨i⟩)
  have hcard_ge_one : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast hcard_ge_one_nat
  have hmul_ge : ε ≤ (Fintype.card ι : ℝ) * ε := by
    calc
      ε = (1 : ℝ) * ε := by ring
      _ ≤ (Fintype.card ι : ℝ) * ε := mul_le_mul_of_nonneg_right hcard_ge_one hε
  have hlower : -((Fintype.card ι : ℝ) * ε) ≤ d i := by
    exact le_trans (neg_le_neg hmul_ge) (hlow i)
  exact abs_le.mpr ⟨hlower, hupper⟩

end FiniteBounds

section ClusterApprox

variable [Nonempty ι]

/--
If points `v i` are `δ`-clustered and each `i`-vertex has nonnegative `i`-displacement,
then one anchor vertex is a coordinatewise approximate fixed point (quantitative bound).
-/
theorem exists_coordwiseApprox_of_labeled_cluster
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (hcont : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ v : ι → stdSimplex ℝ ι,
      (∀ i j : ι, dist (v i) (v j) < δ) →
      (∀ i : ι, 0 ≤ v i i - f (v i) i) →
      ∃ x : stdSimplex ℝ ι, ∀ i : ι, |f x i - x i| ≤ (Fintype.card ι : ℝ) * ε := by
  classical
  rcases exists_delta_coordDisplacement_le_all (f := f) hcont hε with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro v hcluster hlabel
  let a : ι := Classical.arbitrary ι
  refine ⟨v a, ?_⟩
  have hlow : ∀ i : ι, -ε ≤ v a i - f (v a) i := by
    intro i
    have hclose :=
      hδ (x := v a) (y := v i) (hcluster a i) i
    have hdiag_nonneg : 0 ≤ v i i - f (v i) i := hlabel i
    have hleft : -ε ≤ (v a i - f (v a) i) - (v i i - f (v i) i) := (abs_le.mp hclose).1
    linarith
  have hsum0 : Finset.sum Finset.univ (fun i : ι => v a i - f (v a) i) = 0 := by
    calc
      Finset.sum Finset.univ (fun i : ι => v a i - f (v a) i)
          = Finset.sum Finset.univ (fun i : ι => v a i)
            - Finset.sum Finset.univ (fun i : ι => f (v a) i) := by
              simp [Finset.sum_sub_distrib]
      _ = 1 - 1 := by rw [stdSimplex.sum_eq_one (v a), stdSimplex.sum_eq_one (f (v a))]
      _ = 0 := by ring
  intro i
  have habs : |v a i - f (v a) i| ≤ (Fintype.card ι : ℝ) * ε :=
    abs_le_card_mul_of_sum_eq_zero_of_lower_bound
      (d := fun j : ι => v a j - f (v a) j)
      hsum0 (le_of_lt hε) hlow i
  simpa [abs_sub_comm] using habs

/--
Abstract Brouwer reduction:
if for every `δ > 0` there exists a `δ`-cluster of labeled vertices satisfying
nonnegative own-coordinate displacement, then `f` has a fixed point.
-/
theorem exists_fixedPoint_of_arbitrarilyFine_labeled_clusters
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (hcont : Continuous f)
    (hcluster :
      ∀ δ : ℝ, 0 < δ →
        ∃ v : ι → stdSimplex ℝ ι,
          (∀ i j : ι, dist (v i) (v j) < δ) ∧
          (∀ i : ι, 0 ≤ v i i - f (v i) i)) :
    ∃ x : stdSimplex ℝ ι, Function.IsFixedPt f x := by
  have happrox :
      ∀ n : ℕ, ∃ x : stdSimplex ℝ ι, dist (f x) x ≤ (1 : ℝ) / (n + 1) := by
    intro n
    let ε : ℝ := (1 : ℝ) / ((n + 1) * (Fintype.card ι : ℝ))
    have hεpos : 0 < ε := by
      have hn : (0 : ℝ) < (n + 1) := by exact_mod_cast Nat.succ_pos n
      have hcard_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
        exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty ι›)
      unfold ε
      positivity
    rcases exists_coordwiseApprox_of_labeled_cluster
        (f := f) hcont hεpos with ⟨δ, hδpos, hδprop⟩
    rcases hcluster δ hδpos with ⟨v, hvclose, hvlabel⟩
    rcases hδprop v hvclose hvlabel with ⟨x, hxcoord⟩
    refine ⟨x, ?_⟩
    have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ‹Nonempty ι›))
    have hn_ne : (n + 1 : ℝ) ≠ 0 := by positivity
    have hcardMul :
        (Fintype.card ι : ℝ) * ε = (1 : ℝ) / (n + 1) := by
      unfold ε
      field_simp [hcard_ne, hn_ne, mul_comm, mul_left_comm, mul_assoc]
    have hcoord' : ∀ i : ι, |f x i - x i| ≤ (1 : ℝ) / (n + 1) := by
      intro i
      exact (hxcoord i).trans (by simp [hcardMul])
    have hcoordDist : ∀ i : ι, dist (f x i) (x i) ≤ (1 : ℝ) / (n + 1) := by
      intro i
      simpa [Real.dist_eq] using hcoord' i
    have hdist :
        dist (f x) x ≤ (1 : ℝ) / (n + 1) := by
      have hnonneg : 0 ≤ (1 : ℝ) / (n + 1) := by positivity
      simpa [Subtype.dist_eq] using (dist_pi_le_iff hnonneg).2 hcoordDist
    exact hdist
  exact exists_fixedPoint_of_approx_on_stdSimplex f hcont happrox

/--
Scale-indexed cluster families (`1/m`) imply arbitrarily fine clusters (`δ`),
hence a fixed point via `exists_fixedPoint_of_arbitrarilyFine_labeled_clusters`.
-/
theorem exists_fixedPoint_of_labeled_clusters_at_scales
    (f : stdSimplex ℝ ι → stdSimplex ℝ ι)
    (hcont : Continuous f)
    (hscale :
      ∀ m : ℕ, 0 < m →
        ∃ v : ι → stdSimplex ℝ ι,
          (∀ i j : ι, dist (v i) (v j) ≤ (1 : ℝ) / m) ∧
          (∀ i : ι, 0 ≤ v i i - f (v i) i)) :
    ∃ x : stdSimplex ℝ ι, Function.IsFixedPt f x := by
  refine exists_fixedPoint_of_arbitrarilyFine_labeled_clusters (f := f) hcont ?_
  intro δ hδ
  rcases exists_nat_one_div_lt hδ with ⟨n, hn⟩
  let m : ℕ := n + 1
  have hm : 0 < m := Nat.succ_pos n
  rcases hscale m hm with ⟨v, hvdist, hvlabel⟩
  refine ⟨v, ?_, hvlabel⟩
  intro i j
  exact lt_of_le_of_lt (hvdist i j) (by simpa [m] using hn)

end ClusterApprox

end UniformCoordControl

end Fixpoint
