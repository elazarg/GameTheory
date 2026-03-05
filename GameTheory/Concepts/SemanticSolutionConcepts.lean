import GameTheory.Model.Preference
import GameTheory.Concepts.SolutionConcepts

/-!
# GameTheory.Concepts.SemanticSolutionConcepts

Solution concepts over `SemanticGame`, defined in distribution/preference form and
specialized to EU through the semantic model's utility.
-/

namespace GameTheory
namespace SemanticGame

variable {ι : Type}
variable [DecidableEq ι]

/-- Preference-parametric Nash condition for semantic games. -/
def IsNashFor (G : SemanticGame ι)
    (pref : Preference G) (σ : Profile G) : Prop :=
  G.toKernelGame.IsNashFor pref σ

/-- Preference-parametric dominance for semantic games. -/
def IsDominantFor (G : SemanticGame ι)
    (pref : Preference G) (who : ι) (s : G.Strategy who) : Prop :=
  G.toKernelGame.IsDominantFor pref who s

section EU
/-- EU-specialized Nash condition for semantic games. -/
def IsNash (G : SemanticGame ι) (σ : Profile G) : Prop :=
  G.toKernelGame.IsNash σ

/-- EU-specialized dominance for semantic games. -/
def IsDominant (G : SemanticGame ι) (who : ι) (s : G.Strategy who) : Prop :=
  G.toKernelGame.IsDominant who s

/-- EU best response in semantic form. -/
def IsBestResponse (G : SemanticGame ι)
    (who : ι) (σ : Profile G) (s : G.Strategy who) : Prop :=
  G.toKernelGame.IsBestResponse who σ s

theorem isNash_iff_isNashFor_eu (G : SemanticGame ι) (σ : Profile G) :
    G.IsNash σ ↔ G.IsNashFor G.euPref σ :=
  by
    simpa [IsNash, IsNashFor, SemanticGame.euPref, KernelGame.euPref] using
      (KernelGame.IsNash_iff_IsNashFor_eu G.toKernelGame σ)

theorem isDominant_iff_isDominantFor_eu (G : SemanticGame ι)
    (who : ι) (s : G.Strategy who) :
    G.IsDominant who s ↔ G.IsDominantFor G.euPref who s :=
  by
    simpa [IsDominant, IsDominantFor, SemanticGame.euPref, KernelGame.euPref] using
      (KernelGame.IsDominant_iff_IsDominantFor_eu G.toKernelGame who s)

theorem isBestResponse_iff_isBestResponseFor_eu (G : SemanticGame ι)
    (who : ι) (σ : Profile G) (s : G.Strategy who) :
    G.IsBestResponse who σ s ↔ G.toKernelGame.IsBestResponseFor G.euPref who σ s :=
  KernelGame.IsBestResponse_iff_IsBestResponseFor_eu G.toKernelGame who σ s

end EU

end SemanticGame
end GameTheory
