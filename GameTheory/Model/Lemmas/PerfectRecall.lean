import GameTheory.Model.SemanticForm
import GameTheory.Model.Lemmas.ProjectStates

namespace GameTheory
namespace InfoModel

variable {ι : Type} {M : LSM ι} (I : InfoModel M)

theorem perfectRecall_project_eq_of_obsEq_last
    {i : ι}
    {h₁ h₂ : List M.Label} {ss₁ ss₂ : List M.State} {s₁ s₂ : M.State}
    (hOR : I.ObsRecall)
    (hr₁ : InfoModel.ReachStateTrace M h₁ ss₁)
    (hr₂ : InfoModel.ReachStateTrace M h₂ ss₂)
    (hs₁ : ss₁.getLast? = some s₁)
    (hs₂ : ss₂.getLast? = some s₂)
    (hobs : I.obsEq i s₁ s₂) :
    I.projectStates i ss₁ = I.projectStates i ss₂ := by
  exact hOR i h₁ h₂ ss₁ ss₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ hobs

end InfoModel
end GameTheory
