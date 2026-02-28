import GameTheory.SolutionConcepts

/-!
# GameTheory.DominanceRelations

Structural properties of dominance relations on `KernelGame`.

Provides:
- `WeaklyDominates.refl` — weak dominance is reflexive
- `WeaklyDominates.trans` — weak dominance is transitive
- `StrictlyDominates.toWeaklyDominates` — strict dominance implies weak dominance
- `StrictlyDominates.trans` — strict dominance is transitive
- `IsDominant.weaklyDominates` — a dominant strategy weakly dominates every alternative
-/

namespace GameTheory
namespace KernelGame

variable {ι : Type} {G : KernelGame ι}

/-- Weak dominance is reflexive: every strategy weakly dominates itself. -/
theorem WeaklyDominates.refl (who : ι) (s : G.Strategy who) :
    G.WeaklyDominates who s s := by
  intro σ
  exact le_refl _

/-- Weak dominance is transitive. -/
theorem WeaklyDominates.trans {who : ι} {s t u : G.Strategy who}
    (h1 : G.WeaklyDominates who s t) (h2 : G.WeaklyDominates who t u) :
    G.WeaklyDominates who s u := by
  intro σ
  have hs := h1 σ
  have ht := h2 σ
  linarith

/-- Strict dominance implies weak dominance. -/
theorem StrictlyDominates.toWeaklyDominates {who : ι} {s t : G.Strategy who}
    (h : G.StrictlyDominates who s t) : G.WeaklyDominates who s t := by
  intro σ
  exact le_of_lt (h σ)

/-- Strict dominance is transitive. -/
theorem StrictlyDominates.trans {who : ι} {s t u : G.Strategy who}
    (h1 : G.StrictlyDominates who s t) (h2 : G.StrictlyDominates who t u) :
    G.StrictlyDominates who s u := by
  intro σ
  have hs := h1 σ
  have ht := h2 σ
  linarith

/-- A dominant strategy weakly dominates every alternative. -/
theorem IsDominant.weaklyDominates {who : ι} {s : G.Strategy who}
    (hdom : G.IsDominant who s) (t : G.Strategy who) :
    G.WeaklyDominates who s t := by
  intro σ
  exact hdom σ t

end KernelGame
end GameTheory
