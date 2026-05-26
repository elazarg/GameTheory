/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.InfoModel.SemanticForm

/-!
# GameTheory.Languages.InfoModel.Lemmas.ReachStateTrace
-/

namespace GameTheory
namespace InfoModel

variable {ι σ : Type} {Act : ι → Type} {I : InfoModel ι σ Act}

theorem reachStateTrace_nonempty
    {ss : List σ}
    (hr : Semantics.SM.ReachStateTrace I.toSM ss) :
    ss ≠ [] := by
  induction hr with
  | nil =>
      simp
  | snoc _ _ _ =>
      simp

theorem reachActionTrace_nonempty
    {ha : List I.JointAction}
    {ss : List σ}
    (hr : Semantics.SM.ReachActionTrace I.toSM ha ss) :
    ss ≠ [] := by
  induction hr with
  | nil =>
      simp
  | snoc _ _ _ =>
      simp

end InfoModel
end GameTheory
