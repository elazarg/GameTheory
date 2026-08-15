/-
# Mixed profiles as a product of standard simplices

Finite-law/simplex correspondence is provided by
`GameTheory.Math.Probability.Simplex`. This module presents mixed profiles as a
product of simplices over a game signature.
-/

import GameTheory.Core.Form
import GameTheory.Math.Probability.Simplex
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo

/-! ## The polytope of mixed profiles

Independent randomization by finitely many players is a product of simplices,
one per player. Stated as a `Set.pi` it inherits convexity and compactness from
the factors rather than needing either proved again. -/

variable {ι : Type uι}

/-- The signature whose strategies are real weight vectors over the original
ones. Its profiles are the ambient vector space of the fixed-point argument. -/
abbrev GameSignature.weights (sig : GameSignature ι) : GameSignature ι where
  Strategy i := sig.Strategy i → ℝ
  Outcome := sig.Outcome

variable (sig : GameSignature ι) [∀ i, Fintype (sig.Strategy i)]

/-- The mixed profiles, as a subset of the ambient space of weight vectors. -/
def mixedPolytope : Set (Profile sig.weights) :=
  Set.pi Set.univ fun i => stdSimplex ℝ (sig.Strategy i)

theorem mem_mixedPolytope {x : Profile sig.weights} :
    x ∈ mixedPolytope sig ↔ ∀ i, x i ∈ stdSimplex ℝ (sig.Strategy i) := by
  simp [mixedPolytope]

theorem convex_mixedPolytope : Convex ℝ (mixedPolytope sig) :=
  convex_pi fun i _ => convex_stdSimplex ℝ (sig.Strategy i)

theorem isCompact_mixedPolytope : IsCompact (mixedPolytope sig) :=
  isCompact_univ_pi fun i => isCompact_stdSimplex ℝ (sig.Strategy i)

/-- The probability vectors of a mixed profile. -/
def probs (μ : Profile sig.mixed) : Profile sig.weights := fun i => (μ i).prob

theorem probs_mem_mixedPolytope (μ : Profile sig.mixed) : probs sig μ ∈ mixedPolytope sig :=
  (mem_mixedPolytope sig).2 fun i => (μ i).prob_mem_stdSimplex

/-- And back: a point of the polytope is the probability vectors of a unique
mixed profile. -/
def ofPolytope {x : Profile sig.weights} (hx : x ∈ mixedPolytope sig) : Profile sig.mixed :=
  fun i => FinDist.ofSimplex ((mem_mixedPolytope sig).1 hx i)

@[simp]
theorem probs_ofPolytope {x : Profile sig.weights} (hx : x ∈ mixedPolytope sig) :
    probs sig (ofPolytope sig hx) = x := by
  funext i
  exact FinDist.prob_ofSimplex _

@[simp]
theorem ofPolytope_probs (μ : Profile sig.mixed) :
    ofPolytope sig (probs_mem_mixedPolytope sig μ) = μ := by
  funext i
  exact FinDist.ofSimplex_prob (μ i)

/-- If every player has a strategy, the mixed-profile polytope is inhabited. -/
theorem mixedPolytope_nonempty [∀ i, Nonempty (sig.Strategy i)] :
    (mixedPolytope sig).Nonempty :=
  ⟨probs sig fun i => FinDist.pure (Classical.arbitrary (sig.Strategy i)),
    probs_mem_mixedPolytope sig _⟩

end GameTheory
