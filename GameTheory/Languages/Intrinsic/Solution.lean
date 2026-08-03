/-
# Selected intrinsic closed-loop solutions

This opt-in theorem leaf recovers the solution-map mathematics from pinned v1
`GameTheory/Languages/Intrinsic/{Syntax,Theorems}.lean` at commit
`a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.  A selected decision profile is
obtained solely from the existing unique-solvability certificate.
-/

import GameTheory.Languages.Intrinsic

namespace GameTheory.Languages.Intrinsic.Model

universe uAgent uNature uDecision

/-- Select the unique closed-loop decision profile certified by solvability. -/
noncomputable def solution (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (profile : M.PureProfile) (nature : M.Nature) :
    (agent : M.Agent) → M.Decision agent :=
  (solvable profile nature).choose

/-- The selected profile satisfies the closed-loop equations. -/
theorem solution_isFixedPoint (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (profile : M.PureProfile) (nature : M.Nature) :
    M.IsFixedPoint profile nature (M.solution solvable profile nature) :=
  (solvable profile nature).choose_spec.1

/-- Any profile satisfying the same closed-loop equations is the selected one. -/
theorem solution_unique (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (profile : M.PureProfile) (nature : M.Nature)
    (decision : (agent : M.Agent) → M.Decision agent)
    (fixed : M.IsFixedPoint profile nature decision) :
    decision = M.solution solvable profile nature :=
  (solvable profile nature).choose_spec.2 decision fixed

/-- The selected decision at each agent has the declared strategy value. -/
theorem solution_apply (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (profile : M.PureProfile) (nature : M.Nature)
    (agent : M.Agent) :
    M.solution solvable profile nature agent =
      (profile agent).act ⟨nature, M.solution solvable profile nature⟩ :=
  M.solution_isFixedPoint solvable profile nature agent

/-- Pointwise equal strategy actions select equal closed-loop decisions. -/
theorem solution_congr (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (left right : M.PureProfile) (nature : M.Nature)
    (actions : ∀ agent (configuration : M.Configuration),
      (left agent).act configuration = (right agent).act configuration) :
    M.solution solvable left nature = M.solution solvable right nature := by
  apply M.solution_unique solvable right nature
  intro agent
  rw [M.solution_apply]
  exact actions agent _

end GameTheory.Languages.Intrinsic.Model
