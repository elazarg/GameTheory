import GameTheory.Model.SemanticGame

/-!
# GameTheory.Model.Preference

Preference/deviation schemas over `SemanticGame`, with no commitment to EU.
EU specializations are derived through `toKernelGame`.
-/

namespace GameTheory
namespace SemanticGame

variable {ι : Type}

abbrev Preference (G : SemanticGame ι) : Type _ :=
  ι → PMF G.Outcome → PMF G.Outcome → Prop

abbrev Deviation (G : SemanticGame ι) : Type _ :=
  Profile G → Profile G

/-- No profitable one-shot deviation for player `who` under preference `pref`. -/
def NoProfitableDeviation (G : SemanticGame ι)
    (pref : Preference G) (σ : Profile G) (who : ι) : Prop :=
  ∀ (d : Deviation G), pref who (G.outcomeKernel σ) (G.outcomeKernel (d σ))

/-- Profile-level stability under `pref`. -/
def IsStable (G : SemanticGame ι)
    (pref : Preference G) (σ : Profile G) : Prop :=
  ∀ who, G.NoProfitableDeviation pref σ who

/-- EU preference induced by `G.utility`. -/
def euPref (G : SemanticGame ι) : Preference G :=
  fun who d₁ d₂ =>
    Math.Probability.expect d₁ (fun ω => G.utility ω who) ≥
    Math.Probability.expect d₂ (fun ω => G.utility ω who)

end SemanticGame
end GameTheory
