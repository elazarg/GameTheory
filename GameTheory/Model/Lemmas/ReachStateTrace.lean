import GameTheory.Model.SemanticForm

namespace GameTheory
namespace InfoModel

variable {ι : Type} {M : LSM ι}

theorem reachStateTrace_nonempty
    {ss : List M.State}
    (hr : InfoModel.ReachStateTrace M ss) :
    ss ≠ [] := by
  induction hr with
  | nil =>
      simp
  | snoc _ _ _ =>
      simp

theorem reachActionTrace_nonempty
    {ha : List (JointAction M)}
    {ss : List M.State}
    (hr : InfoModel.ReachActionTrace M ha ss) :
    ss ≠ [] := by
  induction hr with
  | nil =>
      simp
  | snoc _ _ _ =>
      simp

end InfoModel
end GameTheory
