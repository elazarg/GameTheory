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

private theorem reachActionTrace_nonempty
    {ha : List (M.Label × (∀ j, Option (M.Act j)))}
    {ss : List M.State}
    (hr : InfoModel.ReachActionTrace M ha ss) :
    ss ≠ [] := by
  induction hr with
  | nil => simp
  | snoc _ _ _ => simp

/-- Strong-recall consequence already implied by `PerfectRecall`:
if two reachable action traces end in states with equal current observation for player `i`,
then player `i` has identical full local observation and own-action histories. -/
theorem perfectRecall_histories_eq_of_last_observe_eq
    (hPR : I.PerfectRecall)
    (i : ι)
    {ha₁ ha₂ : List (M.Label × (∀ j, Option (M.Act j)))}
    {ss₁ ss₂ : List M.State}
    (hr₁ : InfoModel.ReachActionTrace M ha₁ ss₁)
    (hr₂ : InfoModel.ReachActionTrace M ha₂ ss₂)
    (hobs :
      I.observe i (ss₁.getLast (reachActionTrace_nonempty (M := M) hr₁)) =
      I.observe i (ss₂.getLast (reachActionTrace_nonempty (M := M) hr₂))) :
    I.projectStates i ss₁ = I.projectStates i ss₂ ∧
    InfoModel.projectActions i ha₁ = InfoModel.projectActions i ha₂ := by
  let s₁ : M.State := ss₁.getLast (reachActionTrace_nonempty (M := M) hr₁)
  let s₂ : M.State := ss₂.getLast (reachActionTrace_nonempty (M := M) hr₂)
  have hs₁ : ss₁.getLast? = some s₁ := by
    simpa [s₁] using
      (List.getLast?_eq_getLast_of_ne_nil (reachActionTrace_nonempty (M := M) hr₁))
  have hs₂ : ss₂.getLast? = some s₂ := by
    simpa [s₂] using
      (List.getLast?_eq_getLast_of_ne_nil (reachActionTrace_nonempty (M := M) hr₂))
  have hObsEq : I.obsEq i s₁ s₂ := by
    exact I.observe_eq_implies_obsEq i (by simpa [s₁, s₂] using hobs)
  have hStates :
      I.projectStates i ss₁ = I.projectStates i ss₂ := by
    exact
      perfectRecall_project_eq_of_obsEq_last (I := I)
        (hOR := I.perfectRecall_obs hPR)
        (hr₁ := hr₁.toReachStateTrace)
        (hr₂ := hr₂.toReachStateTrace)
        (hs₁ := hs₁) (hs₂ := hs₂)
        (hobs := hObsEq)
  have hActs :
      InfoModel.projectActions i ha₁ = InfoModel.projectActions i ha₂ := by
    exact (I.perfectRecall_action hPR) i ha₁ ha₂ ss₁ ss₂ s₁ s₂
      hr₁ hr₂ hs₁ hs₂ hObsEq
  exact ⟨hStates, hActs⟩

end InfoModel
end GameTheory
