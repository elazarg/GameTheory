import GameTheory.Model.SemanticForm
import GameTheory.Model.Lemmas.ProjectStates
import GameTheory.Model.Lemmas.ReachStateTrace

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

/-- If two reachable action traces induce the same projected state history for
player `i`, then perfect recall forces the same projected own-action history. -/
theorem actionRecall_of_projectStates_eq
    (hPR : I.PerfectRecall)
    (i : ι)
    {ha₁ ha₂ : List (M.Label × (∀ j, Option (M.Act j)))}
    {ss₁ ss₂ : List M.State}
    (hr₁ : InfoModel.ReachActionTrace M ha₁ ss₁)
    (hr₂ : InfoModel.ReachActionTrace M ha₂ ss₂)
    (hproj : I.projectStates i ss₁ = I.projectStates i ss₂) :
    InfoModel.projectActions i ha₁ = InfoModel.projectActions i ha₂ := by
  have hne1 : ss₁ ≠ [] := InfoModel.reachActionTrace_nonempty (M := M) hr₁
  have hne2 : ss₂ ≠ [] := InfoModel.reachActionTrace_nonempty (M := M) hr₂
  let s1 : M.State := ss₁.getLast hne1
  let s2 : M.State := ss₂.getLast hne2
  have hs1 : ss₁.getLast? = some s1 := by
    simpa [s1] using (List.getLast?_eq_getLast_of_ne_nil hne1)
  have hs2 : ss₂.getLast? = some s2 := by
    simpa [s2] using (List.getLast?_eq_getLast_of_ne_nil hne2)
  have hlastObs :
      Option.map (I.observe i) ss₁.getLast? = Option.map (I.observe i) ss₂.getLast? := by
    simpa [I.projectStates_getLast? i ss₁, I.projectStates_getLast? i ss₂] using
      congrArg List.getLast? hproj
  have hobserve : I.observe i s1 = I.observe i s2 := by
    simpa [hs1, hs2] using hlastObs
  have hobsEq : I.obsEq i s1 s2 :=
    I.observe_eq_implies_obsEq i hobserve
  exact (I.perfectRecall_action hPR) i ha₁ ha₂ ss₁ ss₂ s1 s2
    hr₁ hr₂ hs1 hs2 hobsEq

theorem localHistTokens_eq_of_projectStates_actions_eq
    (i : ι)
    {ha₁ ha₂ : List (M.Label × (∀ j, Option (M.Act j)))}
    {ss₁ ss₂ : List M.State}
    (hLen₁ : ss₁.length = ha₁.length + 1)
    (hLen₂ : ss₂.length = ha₂.length + 1)
    (hproj : I.projectStates i ss₁ = I.projectStates i ss₂)
    (hact : InfoModel.projectActions i ha₁ = InfoModel.projectActions i ha₂) :
    InfoModel.localHistTokens (I := I) i ha₁ ss₁ =
      InfoModel.localHistTokens (I := I) i ha₂ ss₂ := by
  induction ha₁ using List.reverseRecOn generalizing ss₁ ha₂ ss₂ with
  | nil =>
      have hss₁ : ss₁.length = 1 := by
        simpa using hLen₁
      have hss₂ : ss₂.length = 1 := by
        have hlenProj : (I.projectStates i ss₁).length = (I.projectStates i ss₂).length := by
          simp [hproj]
        have : 1 = ss₂.length := by
          simpa [I.projectStates_length i ss₁, I.projectStates_length i ss₂, hss₁] using hlenProj
        omega
      have hha₂ : ha₂ = [] := by
        have : ha₂.length = 0 := by
          simpa [hss₂] using hLen₂
        exact List.eq_nil_of_length_eq_zero this
      subst hha₂
      cases ss₁ with
      | nil =>
          cases hss₁
      | cons s₁ tl₁ =>
          cases tl₁ with
          | nil =>
              cases ss₂ with
              | nil =>
                  cases hss₂
              | cons s₂ tl₂ =>
                  cases tl₂ with
                  | nil =>
                      rfl
                  | cons s₂' tl₂' =>
                      cases hss₂
          | cons s₁' tl₁' =>
              cases hss₁
  | @append_singleton ha x ih =>
      have hlenStates : ss₁.length = ss₂.length := by
        simpa [I.projectStates_length i ss₁, I.projectStates_length i ss₂] using
          congrArg List.length hproj
      cases ha₂ using List.reverseRecOn with
      | nil =>
          have hss₂ : ss₂.length = 1 := by
            simpa using hLen₂
          have hss₁ : ss₁.length = ha.length + 2 := by
            simpa [List.length_append] using hLen₁
          omega
      | append_singleton ha₂ y =>
          have hfull : (ha₂ ++ [y]).length = (ha ++ [x]).length := by
            omega
          have hss₁ne : ss₁ ≠ [] := by
            intro hnil
            simp [hnil] at hLen₁
          have hss₂ne : ss₂ ≠ [] := by
            intro hnil
            simp [hnil] at hLen₂
          let t₁ := ss₁.getLast hss₁ne
          let t₂ := ss₂.getLast hss₂ne
          have hss₁decomp : ss₁.dropLast ++ [t₁] = ss₁ := by
            simpa [t₁] using List.dropLast_append_getLast hss₁ne
          have hss₂decomp : ss₂.dropLast ++ [t₂] = ss₂ := by
            simpa [t₂] using List.dropLast_append_getLast hss₂ne
          have hLen₁' : ss₁.dropLast.length = ha.length + 1 := by
            have : ss₁.dropLast.length + 1 = (ha ++ [x]).length + 1 := by
              simpa [hss₁decomp, List.length_append] using hLen₁
            simpa [List.length_append] using this
          have hLen₂' : ss₂.dropLast.length = ha₂.length + 1 := by
            have : ss₂.dropLast.length + 1 = (ha₂ ++ [y]).length + 1 := by
              simpa [hss₂decomp, List.length_append] using hLen₂
            simpa [List.length_append] using this
          have hproj' : I.projectStates i ss₁.dropLast = I.projectStates i ss₂.dropLast := by
            have hdrop := congrArg List.dropLast hproj
            calc
              I.projectStates i ss₁.dropLast = List.dropLast (I.projectStates i ss₁) := by
                rw [← hss₁decomp, I.projectStates_snoc]
                simp
              _ = List.dropLast (I.projectStates i ss₂) := hdrop
              _ = I.projectStates i ss₂.dropLast := by
                rw [← hss₂decomp, I.projectStates_snoc]
                simp
          have hact' : InfoModel.projectActions i ha = InfoModel.projectActions i ha₂ := by
            have hdrop := congrArg List.dropLast hact
            simpa [InfoModel.projectActions, List.map_append] using hdrop
          have hlastAct : x.2 i = y.2 i := by
            have hlast := congrArg List.getLast? hact
            simpa [InfoModel.projectActions, List.map_append] using hlast
          have hrec := ih hLen₁' hLen₂' hproj' hact'
          rw [← hss₁decomp, ← hss₂decomp]
          rw [InfoModel.localHistTokens_snoc (I := I) i ha ss₁.dropLast hLen₁' x.1 x.2 t₁]
          rw [InfoModel.localHistTokens_snoc (I := I) i ha₂ ss₂.dropLast hLen₂' y.1 y.2 t₂]
          simp [hrec, hlastAct, hproj']

end InfoModel
end GameTheory
