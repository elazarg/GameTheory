/-
# Sequential compactness of finite families of PMFs

The existing standard-simplex bridge and Mathlib's sequential compactness
theorem give one subsequence on which every law in a finite dependent family
converges. No topology is imposed on the semantic PMF type.
-/

import GameTheory.Math.Probability.Convergence
import GameTheory.Math.Probability.Simplex
import Mathlib.Topology.Sequences

noncomputable section

namespace GameTheory.Math.Probability

/-- A sequence of finite dependent families of laws on finite carriers has a
single strictly increasing subsequence along which every mass converges.
The limit is again a family of probability laws, including when some limiting
masses vanish. -/
theorem exists_subseq_pmfConvergesPointwise_pi
    {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, Fintype (A i)]
    (sequence : ℕ → ∀ i, PMF (A i)) :
    ∃ (target : ∀ i, PMF (A i)) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
        ∀ i, PMFConvergesPointwise (fun n => sequence (subseq n) i) (target i) := by
  classical
  have compact : IsCompact { weights : ∀ i, A i → ℝ |
      ∀ i, weights i ∈ simplexWeights (A i) } :=
    isCompact_pi_infinite fun i => isCompact_simplexWeights (A i)
  obtain ⟨weights, hweights, subseq, hsubseq, hlimit⟩ :=
    compact.tendsto_subseq (x := fun n i value => (sequence n i value).toReal)
      (fun n i => PMF.toReal_mem_simplexWeights (sequence n i))
  refine ⟨fun i => PMF.ofSimplex (hweights i), subseq, hsubseq, ?_⟩
  intro i
  apply pmfConvergesPointwise_iff_toReal.mpr
  intro value
  have hcoord := congrFun (PMF.ofSimplex_toReal (hweights i)) value
  rw [hcoord]
  simpa only [Function.comp_def] using
    (((continuous_apply value).comp (continuous_apply i)).tendsto weights).comp hlimit

/-- A sequence of probability laws on a finite carrier has a pointwise
convergent subsequence whose limit is a probability law. -/
theorem exists_subseq_pmfConvergesPointwise
    {α : Type*} [Fintype α] (sequence : ℕ → PMF α) :
    ∃ (target : PMF α) (subseq : ℕ → ℕ),
      StrictMono subseq ∧ PMFConvergesPointwise (fun n => sequence (subseq n)) target := by
  obtain ⟨target, subseq, hsubseq, hlimit⟩ :=
    exists_subseq_pmfConvergesPointwise_pi (ι := Unit) (fun n _ => sequence n)
  exact ⟨target (), subseq, hsubseq, hlimit ()⟩

end GameTheory.Math.Probability
