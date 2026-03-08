import GameTheory.Model.SemanticForm
import GameTheory.Model.Lemmas.ProjectStates
import GameTheory.Model.Lemmas.ReachStateTrace

namespace GameTheory
namespace InfoModel

variable {ι σ : Type} {Act : ι → Type} (I : InfoModel ι σ Act)

theorem perfectRecall_project_eq_of_obsEq_last
    {i : ι}
    {ss₁ ss₂ : List σ} {s₁ s₂ : σ}
    (hOR : I.ObsRecall)
    (hr₁ : Semantics.SM.ReachStateTrace I.toSM ss₁)
    (hr₂ : Semantics.SM.ReachStateTrace I.toSM ss₂)
    (hs₁ : ss₁.getLast? = some s₁)
    (hs₂ : ss₂.getLast? = some s₂)
    (hobs : I.obsEq i s₁ s₂) :
    I.projectStates i ss₁ = I.projectStates i ss₂ := by
  exact hOR i ss₁ ss₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ hobs

/-- Strong-recall consequence already implied by `PerfectRecall`:
if two reachable action traces end in states that are indistinguishable for player `i`,
then player `i` has identical full visible history and own-action history. -/
theorem perfectRecall_histories_eq_of_last_observe_eq
    (hPR : I.PerfectRecall)
    (i : ι)
    {ha₁ ha₂ : List I.JointAction}
    {ss₁ ss₂ : List σ}
    (hr₁ : Semantics.SM.ReachActionTrace I.toSM ha₁ ss₁)
    (hr₂ : Semantics.SM.ReachActionTrace I.toSM ha₂ ss₂)
    (hobs :
      I.obsEq i
        (ss₁.getLast (reachActionTrace_nonempty hr₁))
        (ss₂.getLast (reachActionTrace_nonempty hr₂))) :
    I.projectStates i ss₁ = I.projectStates i ss₂ ∧
    I.projectActions i ha₁ = I.projectActions i ha₂ := by
  let s₁ : σ := ss₁.getLast (reachActionTrace_nonempty hr₁)
  let s₂ : σ := ss₂.getLast (reachActionTrace_nonempty hr₂)
  have hs₁ : ss₁.getLast? = some s₁ := by
    simpa [s₁] using
      (List.getLast?_eq_getLast_of_ne_nil (reachActionTrace_nonempty hr₁))
  have hs₂ : ss₂.getLast? = some s₂ := by
    simpa [s₂] using
      (List.getLast?_eq_getLast_of_ne_nil (reachActionTrace_nonempty hr₂))
  have hStates :
      I.projectStates i ss₁ = I.projectStates i ss₂ := by
    exact
      perfectRecall_project_eq_of_obsEq_last (I := I)
        (hOR := I.perfectRecall_obs hPR)
        (hr₁ := hr₁.toReachStateTrace)
        (hr₂ := hr₂.toReachStateTrace)
        (hs₁ := hs₁) (hs₂ := hs₂)
        (hobs := by simpa [s₁, s₂] using hobs)
  have hActs :
      I.projectActions i ha₁ = I.projectActions i ha₂ := by
    exact (I.perfectRecall_action hPR) i ha₁ ha₂ ss₁ ss₂ s₁ s₂
      hr₁ hr₂ hs₁ hs₂ (by simpa [s₁, s₂] using hobs)
  exact ⟨hStates, hActs⟩

/-- If two reachable action traces induce the same visible history for
player `i`, then perfect recall forces the same projected own-action history. -/
theorem actionRecall_of_projectStates_eq
    (hPR : I.PerfectRecall)
    (i : ι)
    {ha₁ ha₂ : List I.JointAction}
    {ss₁ ss₂ : List σ}
    (hr₁ : Semantics.SM.ReachActionTrace I.toSM ha₁ ss₁)
    (hr₂ : Semantics.SM.ReachActionTrace I.toSM ha₂ ss₂)
    (hproj : I.projectStates i ss₁ = I.projectStates i ss₂) :
    I.projectActions i ha₁ = I.projectActions i ha₂ := by
  have hne1 : ss₁ ≠ [] := InfoModel.reachActionTrace_nonempty hr₁
  have hne2 : ss₂ ≠ [] := InfoModel.reachActionTrace_nonempty hr₂
  let s1 : σ := ss₁.getLast hne1
  let s2 : σ := ss₂.getLast hne2
  have hs1 : ss₁.getLast? = some s1 := by
    simpa [s1] using (List.getLast?_eq_getLast_of_ne_nil hne1)
  have hs2 : ss₂.getLast? = some s2 := by
    simpa [s2] using (List.getLast?_eq_getLast_of_ne_nil hne2)
  have hlastPub :
      Option.map I.publicView ss₁.getLast? = Option.map I.publicView ss₂.getLast? := by
    have hpair := congrArg (fun z => z.1.getLast?) hproj
    simpa [I.projectStates_getLast? i ss₁, I.projectStates_getLast? i ss₂] using hpair
  have hlastPriv :
      Option.map (I.observe i) ss₁.getLast? = Option.map (I.observe i) ss₂.getLast? := by
    have hpair := congrArg (fun z => z.2.getLast?) hproj
    simpa [I.projectStates_getLast? i ss₁, I.projectStates_getLast? i ss₂] using hpair
  have hpub : I.publicView s1 = I.publicView s2 := by
    simpa [hs1, hs2] using hlastPub
  have hobserve : I.observe i s1 = I.observe i s2 := by
    simpa [hs1, hs2] using hlastPriv
  have hobsEq : I.obsEq i s1 s2 := ⟨hpub, hobserve⟩
  exact (I.perfectRecall_action hPR) i ha₁ ha₂ ss₁ ss₂ s1 s2
    hr₁ hr₂ hs1 hs2 hobsEq

theorem localHistTokens_eq_of_projectStates_actions_eq
    (i : ι)
    {ha₁ ha₂ : List I.JointAction}
    {ss₁ ss₂ : List σ}
    (hLen₁ : ss₁.length = ha₁.length + 1)
    (hLen₂ : ss₂.length = ha₂.length + 1)
    (hproj : I.projectStates i ss₁ = I.projectStates i ss₂)
    (hact : I.projectActions i ha₁ = I.projectActions i ha₂) :
    InfoModel.localHistTokens (I := I) i ha₁ ss₁ =
      InfoModel.localHistTokens (I := I) i ha₂ ss₂ := by
  induction ha₁ using List.reverseRecOn generalizing ss₁ ha₂ ss₂ with
  | nil =>
      have hss₁ : ss₁.length = 1 := by
        simpa using hLen₁
      have hss₂ : ss₂.length = 1 := by
        have hlenStates : ss₁.length = ss₂.length := by
          calc
            ss₁.length = (I.projectStates i ss₁).2.length := by
              symm
              simpa [InfoModel.projectStates] using I.projectPrivate_length i ss₁
            _ = (I.projectStates i ss₂).2.length := by
              simpa using congrArg (fun z => z.2.length) hproj
            _ = ss₂.length := by
              simpa [InfoModel.projectStates] using I.projectPrivate_length i ss₂
        have : 1 = ss₂.length := by simpa [hss₁] using hlenStates
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
        calc
          ss₁.length = (I.projectStates i ss₁).2.length := by
            symm
            simpa [InfoModel.projectStates] using I.projectPrivate_length i ss₁
          _ = (I.projectStates i ss₂).2.length := by
            simpa using congrArg (fun z => z.2.length) hproj
          _ = ss₂.length := by
            simpa [InfoModel.projectStates] using I.projectPrivate_length i ss₂
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
            have hdrop1 := congrArg Prod.fst hproj
            have hdrop2 := congrArg Prod.snd hproj
            apply Prod.ext
            · calc
                I.projectPublic ss₁.dropLast = List.dropLast (I.projectPublic ss₁) := by
                  rw [← hss₁decomp, I.projectPublic_snoc]
                  simp
                _ = List.dropLast (I.projectPublic ss₂) := by
                  simpa using congrArg List.dropLast hdrop1
                _ = I.projectPublic ss₂.dropLast := by
                  rw [← hss₂decomp, I.projectPublic_snoc]
                  simp
            · calc
                I.projectPrivate i ss₁.dropLast = List.dropLast (I.projectPrivate i ss₁) := by
                  rw [← hss₁decomp, I.projectPrivate_snoc]
                  simp
                _ = List.dropLast (I.projectPrivate i ss₂) := by
                  simpa using congrArg List.dropLast hdrop2
                _ = I.projectPrivate i ss₂.dropLast := by
                  rw [← hss₂decomp, I.projectPrivate_snoc]
                  simp
          have hact' : I.projectActions i ha = I.projectActions i ha₂ := by
            have hdrop := congrArg List.dropLast hact
            simpa [InfoModel.projectActions, List.map_append] using hdrop
          have hlastAct : x i = y i := by
            have hlast := congrArg List.getLast? hact
            simpa [InfoModel.projectActions, List.map_append] using hlast
          have hrec := ih hLen₁' hLen₂' hproj' hact'
          rw [← hss₁decomp, ← hss₂decomp]
          rw [InfoModel.localHistTokens_snoc (I := I) i ha ss₁.dropLast hLen₁' x t₁]
          rw [InfoModel.localHistTokens_snoc (I := I) i ha₂ ss₂.dropLast hLen₂' y t₂]
          simp [hrec, hlastAct, hproj']

end InfoModel
end GameTheory
