import GameTheory.Theorems.KuhnCore
import GameTheory.Model.Lemmas.PerfectRecall
import GameTheory.Model.Lemmas.LocalConditioning
import GameTheory.Model.Lemmas.ReachFactorization

namespace GameTheory
namespace Theorems

open Math
open Math.PMFProduct

section InfoModel

open Execution
open InfoModel

variable {ι : Type} [Fintype ι]
variable {M : LSM ι} (I : InfoModel M)
variable (D : Execution.Dynamics I)
variable (k : Nat)

/-- Player-local history token used for iterated conditioning:
past local observation trace paired with the realized own action. -/
abbrev LocalHistTok (i : ι) : Type :=
  InfoModel.LocalHistTok (I := I) i


/-- Canonical conditional behavioral realization from a mixed profile,
defined by conditioning on one chosen reachable local history witness. -/
noncomputable def mixedToBehavioral
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : InfoModel.MixedProfile (I := I)) :
    BehavioralProfile I := by
  classical
  refine fun i v =>
    if h :
      ∃ ha : List (M.Label × (∀ j, Option (M.Act j))),
      ∃ ss : List M.State,
        InfoModel.ReachActionTrace M ha ss ∧
        I.projectStates i ss = v
    then ?_ else PMF.pure none
  let ha : List (M.Label × (∀ j, Option (M.Act j))) := Classical.choose h
  let ss : List M.State := Classical.choose (Classical.choose_spec h)
  have hv : I.projectStates i ss = v := (Classical.choose_spec (Classical.choose_spec h)).2
  let hist := InfoModel.localHistTokens (I := I) i ha ss
  exact Math.ProbabilityMassFunction.pushforward
    (iterCondMixedLocal (I := I) i (μ i) hist) (fun f => f v)

omit [Fintype ι] in
private theorem reachActionTrace_nonempty
    {ha : List (M.Label × (∀ j, Option (M.Act j)))}
    {ss : List M.State}
    (hr : InfoModel.ReachActionTrace M ha ss) :
    ss ≠ [] := by
  induction hr with
  | nil => simp
  | snoc _ _ _ => simp

omit [Fintype ι] in
private theorem projectStates_getLast?
    (i : ι) (ss : List M.State) :
    (I.projectStates i ss).getLast? = Option.map (I.observe i) ss.getLast? := by
  induction ss with
  | nil => rfl
  | cons s tl ih =>
      cases tl with
      | nil => simp [InfoModel.projectStates]
      | cons s' tl' =>
          simpa [InfoModel.projectStates] using ih

omit [Fintype ι] in
private theorem actionRecall_of_projectStates_eq
    (hPR : I.PerfectRecall)
    (i : ι)
    {ha₁ ha₂ : List (M.Label × (∀ j, Option (M.Act j)))}
    {ss₁ ss₂ : List M.State}
    (hr₁ : InfoModel.ReachActionTrace M ha₁ ss₁)
    (hr₂ : InfoModel.ReachActionTrace M ha₂ ss₂)
    (hproj : I.projectStates i ss₁ = I.projectStates i ss₂) :
    InfoModel.projectActions i ha₁ = InfoModel.projectActions i ha₂ := by
  have hne1 : ss₁ ≠ [] := reachActionTrace_nonempty (M := M) hr₁
  have hne2 : ss₂ ≠ [] := reachActionTrace_nonempty (M := M) hr₂
  let s1 : M.State := ss₁.getLast hne1
  let s2 : M.State := ss₂.getLast hne2
  have hs1 : ss₁.getLast? = some s1 := by
    simpa [s1] using (List.getLast?_eq_getLast_of_ne_nil hne1)
  have hs2 : ss₂.getLast? = some s2 := by
    simpa [s2] using (List.getLast?_eq_getLast_of_ne_nil hne2)
  have hlastObs :
      Option.map (I.observe i) ss₁.getLast? = Option.map (I.observe i) ss₂.getLast? := by
    simpa [projectStates_getLast? (I := I) i ss₁, projectStates_getLast? (I := I) i ss₂] using
      congrArg List.getLast? hproj
  have hobserve : I.observe i s1 = I.observe i s2 := by
    simpa [hs1, hs2] using hlastObs
  have hobsEq : I.obsEq i s1 s2 :=
    I.observe_eq_implies_obsEq i hobserve
  exact (InfoModel.perfectRecall_action (I := I) hPR) i ha₁ ha₂ ss₁ ss₂ s1 s2
    hr₁ hr₂ hs1 hs2 hobsEq

omit [Fintype ι] in
private theorem localHistTokens_eq_of_projectStates_actions_eq
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

omit [Fintype ι] in
private theorem actionTrace_eq_of_labels_projectActions_eq
    {ha₁ ha₂ : List (M.Label × (∀ j, Option (M.Act j)))}
    (hlabels : ha₁.map Prod.fst = ha₂.map Prod.fst)
    (hacts : ∀ i, InfoModel.projectActions i ha₁ = InfoModel.projectActions i ha₂) :
    ha₁ = ha₂ := by
  induction ha₁ generalizing ha₂ with
  | nil =>
      cases ha₂ with
      | nil => rfl
      | cons y ys =>
          simp at hlabels
  | cons x xs ih =>
      cases ha₂ with
      | nil =>
          simp at hlabels
      | cons y ys =>
          have hlabelTail : x.1 = y.1 ∧ xs.map Prod.fst = ys.map Prod.fst := by
            simpa using hlabels
          rcases hlabelTail with ⟨hlabel, htailLabels⟩
          have hheadAct : ∀ i, x.2 i = y.2 i := by
            intro i
            have hi := hacts i
            simpa [InfoModel.projectActions] using congrArg List.head? hi
          have htailActs : ∀ i, InfoModel.projectActions i xs = InfoModel.projectActions i ys := by
            intro i
            have hi := hacts i
            simpa [InfoModel.projectActions, hheadAct i] using hi
          have htail : xs = ys := ih htailLabels htailActs
          cases x with
          | mk lx ax =>
              cases y with
              | mk ly ay =>
                  have hfun : ax = ay := by
                    funext i
                    simpa using hheadAct i
                  simp only [List.cons.injEq, Prod.mk.injEq]
                  exact ⟨⟨hlabel, hfun⟩, htail⟩

omit [Fintype ι] in
private theorem mixedToBehavioral_eq_iterCond_pushforward
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (μ : InfoModel.MixedProfile (I := I))
    (i : ι)
    {ha : List (M.Label × (∀ j, Option (M.Act j)))}
    {ss : List M.State}
    (hr : InfoModel.ReachActionTrace M ha ss) :
    mixedToBehavioral (I := I) μ i (I.projectStates i ss) =
      Math.ProbabilityMassFunction.pushforward
        (iterCondMixedLocal (I := I) i (μ i)
          (InfoModel.localHistTokens (I := I) i ha ss))
        (fun f => f (I.projectStates i ss)) := by
  classical
  unfold mixedToBehavioral
  let v : I.LocalTrace i := I.projectStates i ss
  have hreach :
      ∃ ha' : List (M.Label × (∀ j, Option (M.Act j))),
      ∃ ss' : List M.State,
        InfoModel.ReachActionTrace M ha' ss' ∧
          I.projectStates i ss' = v := by
    exact ⟨ha, ss, hr, rfl⟩
  rw [dif_pos hreach]
  dsimp [v]
  let ha' : List (M.Label × (∀ j, Option (M.Act j))) := Classical.choose hreach
  let ss' : List M.State := Classical.choose (Classical.choose_spec hreach)
  have hr' : InfoModel.ReachActionTrace M ha' ss' :=
    (Classical.choose_spec (Classical.choose_spec hreach)).1
  have hproj :
      I.projectStates i ss' = I.projectStates i ss :=
    (Classical.choose_spec (Classical.choose_spec hreach)).2
  have hacts :
      InfoModel.projectActions i ha' = InfoModel.projectActions i ha :=
    actionRecall_of_projectStates_eq (I := I) hPR i hr' hr hproj
  have hLen' :
      ss'.length = ha'.length + 1 :=
    InfoModel.ReachActionTrace.length_states_eq_succ_actions hr'
  have hLen :
      ss.length = ha.length + 1 :=
    InfoModel.ReachActionTrace.length_states_eq_succ_actions hr
  have hhist :
      InfoModel.localHistTokens (I := I) i ha' ss' =
        InfoModel.localHistTokens (I := I) i ha ss :=
    localHistTokens_eq_of_projectStates_actions_eq
      (I := I) i hLen' hLen hproj hacts
  simp [ha', ss', hhist]

theorem stepPoint_eq_via_query_disintegration
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (μ : InfoModel.MixedProfile (I := I))
    (n : Nat)
    (hs y : List M.Label × List M.State)
    (hlen : hs.2.length = n + 1) :
    let μJ : PMF (PureProfile I) := InfoModel.mixedJoint (I := I) μ
    let C : ENNReal := ∑' π, μJ π * (D.runDistPure n π) hs
    C *
      ((Math.ProbabilityMassFunction.pushforward
        (D.stepDist (mixedToBehavioral (I := I) μ) hs.2)
        (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y)
      =
    ∑' π, μJ π *
      ((D.runDistPure n π) hs *
        ((Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y)) := by
  classical
  let μJ : PMF (PureProfile I) := InfoModel.mixedJoint (I := I) μ
  let v : ∀ i, I.LocalTrace i := fun i => I.projectStates i hs.2
  let stepPureY : PureProfile I → ENNReal := fun π =>
    (Math.ProbabilityMassFunction.pushforward
      (D.stepDist (pureToBehavioral I π) hs.2)
      (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y
  let q : PureProfile I → (∀ i, Option (M.Act i)) := fun π i => π i (v i)
  have hstepPure_dep_q :
      ∀ π : PureProfile I,
        stepPureY π = stepPureY (fun i _ => q π i) := by
    intro π
    unfold stepPureY q
    exact pure_step_pushforward_depends_on_query (I := I) (D := D) hs y π
      (fun i _ => q π i) (by intro i; rfl)
  -- Query-disintegration at `v`, then identification of conditional factors
  -- with `mixedToBehavioral` at `hs.2`.
  -- (Perfect recall is used for witness-independence of local histories.)
  let C : ENNReal := ∑' π, μJ π * (D.runDistPure n π) hs
  by_cases hC0 : C = 0
  · have hsum0 :
      ∑' π, μJ π *
        ((D.runDistPure n π) hs * stepPureY π) = 0 := by
      refine ENNReal.tsum_eq_zero.2 ?_
      intro π
      have hpi0 : μJ π * (D.runDistPure n π) hs = 0 := by
        apply (ENNReal.tsum_eq_zero.1 hC0)
      simpa [stepPureY, mul_assoc] using congrArg (fun z => z * stepPureY π) hpi0
    calc
      C *
        ((Math.ProbabilityMassFunction.pushforward
          (D.stepDist (mixedToBehavioral (I := I) μ) hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y)
          = 0 := by rw [hC0, zero_mul]
      _ = ∑' π, μJ π *
            ((D.runDistPure n π) hs *
              ((Math.ProbabilityMassFunction.pushforward
                (D.stepDist (pureToBehavioral I π) hs.2)
                (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y)) := by
            simpa [stepPureY] using hsum0.symm
  · have hCpos : C ≠ 0 := hC0
    have hexists : ∃ π : PureProfile I, μJ π * (D.runDistPure n π) hs ≠ 0 := by
      by_contra hnone
      apply hCpos
      refine ENNReal.tsum_eq_zero.2 ?_
      intro π
      exact by_contra fun h => hnone ⟨π, h⟩
    obtain ⟨π0, hπ0⟩ := hexists
    have hrun0 : (D.runDistPure n π0) hs ≠ 0 := by
      intro hzero
      apply hπ0
      simp [hzero]
    obtain ⟨ha, hr, hlabels, hcompat⟩ :=
      exists_reachActionTrace_of_runDistPure_ne_zero
        (I := I) (D := D) n π0 hs hrun0
    let hist : ∀ i, List (LocalHistTok (I := I) i) :=
      fun i => InfoModel.localHistTokens (I := I) i ha hs.2
    let μHist : InfoModel.MixedProfile (I := I) :=
      fun i => iterCondMixedLocal (I := I) i (μ i) (hist i)
    have hbeh_now :
        ∀ i,
          mixedToBehavioral (I := I) μ i (I.projectStates i hs.2) =
            InfoModel.realizeBehavioralCanonical (I := I) μHist i
              (I.projectStates i hs.2) := by
      intro i
      simpa [μHist, hist, InfoModel.realizeBehavioralCanonical] using
        mixedToBehavioral_eq_iterCond_pushforward
          (I := I) (hPR := hPR) (μ := μ) i hr
    have hstep_beh :
        D.stepDist (mixedToBehavioral (I := I) μ) hs.2 =
          D.stepDist (InfoModel.realizeBehavioralCanonical (I := I) μHist) hs.2 := by
      apply stepDist_behavioral_depends_on_current_context (I := I) (D := D)
      intro i
      exact hbeh_now i
    have hleft_rewrite :
        (Math.ProbabilityMassFunction.pushforward
          (D.stepDist (mixedToBehavioral (I := I) μ) hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y
          =
        (∑' π, (InfoModel.mixedJoint (I := I) μHist) π * stepPureY π) := by
      calc
        (Math.ProbabilityMassFunction.pushforward
          (D.stepDist (mixedToBehavioral (I := I) μ) hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y
            =
          (Math.ProbabilityMassFunction.pushforward
            (D.stepDist (InfoModel.realizeBehavioralCanonical (I := I) μHist) hs.2)
            (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y := by
              simpa using congrArg
                (fun ν =>
                  (Math.ProbabilityMassFunction.pushforward ν
                    (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y)
                hstep_beh
        _ = (∑' π, (InfoModel.mixedJoint (I := I) μHist) π * stepPureY π) := by
              simpa [stepPureY] using
                (mixedJoint_stepPoint_eq_realizeBehavioralCanonical
                  (I := I) (D := D) μHist hs y).symm
    have hfactor_run :
        ∃ traceMass compatMass : ENNReal,
          C = traceMass * compatMass ∧
          (∑' π, μJ π *
            ((D.runDistPure n π) hs * stepPureY π))
            = traceMass * compatMass *
                (∑' π, (InfoModel.mixedJoint (I := I) μHist) π * stepPureY π) := by
      have hhaLen : ha.length = n := by
        have hreachLen :=
          InfoModel.ReachActionTrace.length_states_eq_succ_actions hr
        exact Nat.succ.inj <| by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            hreachLen.symm.trans hlen
      let traceMass : ENNReal := (D.runDistPure n π0) hs
      let compatMass : ENNReal :=
        ∏ i, localHistMass (I := I) i (μ i) (hist i)
      have hrun_factor :
          ∀ π : PureProfile I,
            (D.runDistPure n π) hs =
              traceMass *
                ∏ i, localHistIndicator (I := I) i (π i) (hist i) := by
        intro π
        dsimp [traceMass]
        calc
          (D.runDistPure n π) hs =
            D.runDistPure ha.length π (ha.map Prod.fst, hs.2) := by
              simp [hlabels, hhaLen]
          _ =
            D.runDistPure ha.length π0 (ha.map Prod.fst, hs.2) *
              ∏ i, localHistIndicator (I := I) i (π i) (hist i) := by
                simpa [hist] using
                  runDistPure_factor_via_localHistIndicators
                    (I := I) (D := D) hPR hr π0 hcompat π
          _ =
            (D.runDistPure n π0) hs *
              ∏ i, localHistIndicator (I := I) i (π i) (hist i) := by
                simp [hlabels, hhaLen]
      have hmixed_factor :
          ∀ π : PureProfile I,
            compatMass * (InfoModel.mixedJoint (I := I) μHist) π =
              μJ π * ∏ i, localHistIndicator (I := I) i (π i) (hist i) := by
        intro π
        simpa [compatMass, μHist, μJ] using
          localHistMass_mul_mixedJoint_iterCond_apply
            (I := I) (μ := μ) (hist := hist) π
      have hsum_indicators :
          ∑' π, μJ π *
            ∏ i, localHistIndicator (I := I) i (π i) (hist i) = compatMass := by
        calc
          ∑' π, μJ π *
            ∏ i, localHistIndicator (I := I) i (π i) (hist i)
              =
            ∑' π, compatMass * (InfoModel.mixedJoint (I := I) μHist) π := by
                refine tsum_congr ?_
                intro π
                exact (hmixed_factor π).symm
          _ = compatMass * ∑' π, (InfoModel.mixedJoint (I := I) μHist) π := by
                rw [ENNReal.tsum_mul_left]
          _ = compatMass * 1 := by
                simpa using congrArg (fun z : ENNReal => compatMass * z)
                  ((InfoModel.mixedJoint (I := I) μHist).tsum_coe)
          _ = compatMass := by simp
      refine ⟨traceMass, compatMass, ?_, ?_⟩
      · calc
          C = ∑' π, μJ π *
              (traceMass *
                ∏ i, localHistIndicator (I := I) i (π i) (hist i)) := by
                refine tsum_congr ?_
                intro π
                rw [hrun_factor π]
          _ = ∑' π, traceMass *
              (μJ π * ∏ i, localHistIndicator (I := I) i (π i) (hist i)) := by
                refine tsum_congr ?_
                intro π
                ac_rfl
          _ = traceMass *
              ∑' π, μJ π *
                ∏ i, localHistIndicator (I := I) i (π i) (hist i) := by
                rw [ENNReal.tsum_mul_left]
          _ = traceMass * compatMass := by
                rw [hsum_indicators]
      · calc
          (∑' π, μJ π *
            ((D.runDistPure n π) hs * stepPureY π))
              =
            ∑' π, μJ π *
              ((traceMass *
                ∏ i, localHistIndicator (I := I) i (π i) (hist i)) *
                stepPureY π) := by
                  refine tsum_congr ?_
                  intro π
                  rw [hrun_factor π]
          _ = ∑' π, traceMass *
              ((μJ π *
                ∏ i, localHistIndicator (I := I) i (π i) (hist i)) *
                stepPureY π) := by
                  refine tsum_congr ?_
                  intro π
                  ac_rfl
          _ = traceMass *
              ∑' π, ((μJ π *
                ∏ i, localHistIndicator (I := I) i (π i) (hist i)) *
                stepPureY π) := by
                  rw [ENNReal.tsum_mul_left]
          _ = traceMass *
              ∑' π, ((compatMass *
                (InfoModel.mixedJoint (I := I) μHist) π) *
                stepPureY π) := by
                  congr 1
                  refine tsum_congr ?_
                  intro π
                  rw [← hmixed_factor π]
          _ = traceMass *
              (compatMass *
                ∑' π, (InfoModel.mixedJoint (I := I) μHist) π * stepPureY π) := by
                  congr 1
                  calc
                    ∑' π, ((compatMass *
                      (InfoModel.mixedJoint (I := I) μHist) π) *
                      stepPureY π)
                        =
                      ∑' π, compatMass *
                        ((InfoModel.mixedJoint (I := I) μHist) π * stepPureY π) := by
                          refine tsum_congr ?_
                          intro π
                          ac_rfl
                    _ = compatMass *
                        ∑' π, (InfoModel.mixedJoint (I := I) μHist) π * stepPureY π := by
                          rw [ENNReal.tsum_mul_left]
          _ = traceMass * compatMass *
              (∑' π, (InfoModel.mixedJoint (I := I) μHist) π * stepPureY π) := by
                ac_rfl
    rcases hfactor_run with ⟨traceMass, compatMass, hCfact, hRfact⟩
    calc
      C *
        ((Math.ProbabilityMassFunction.pushforward
          (D.stepDist (mixedToBehavioral (I := I) μ) hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y)
          = (traceMass * compatMass) *
              (∑' π, (InfoModel.mixedJoint (I := I) μHist) π * stepPureY π) := by
                rw [hCfact, hleft_rewrite]
      _ = ∑' π, μJ π *
            ((D.runDistPure n π) hs * stepPureY π) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hRfact.symm
      _ = ∑' π, μJ π *
            ((D.runDistPure n π) hs *
              ((Math.ProbabilityMassFunction.pushforward
                (D.stepDist (pureToBehavioral I π) hs.2)
                (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y)) := by
            simp [stepPureY]

theorem mixedToBehavioral_stepIndependence
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (μ : InfoModel.MixedProfile (I := I)) :
    ∀ n,
      (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
        (D.runDistPure n π).bind (fun hs =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (mixedToBehavioral (I := I) μ) hs.2)
            (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) =
      (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
        (D.runDistPure n π).bind (fun hs =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (pureToBehavioral I π) hs.2)
            (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) := by
  intro n
  classical
  ext y
  set μJ : PMF (PureProfile I) := InfoModel.mixedJoint (I := I) μ
  let Lfun : (List M.Label × List M.State) → ENNReal :=
    fun hs =>
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (mixedToBehavioral (I := I) μ) hs.2)
        (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y
  let Gfun : (List M.Label × List M.State) → PureProfile I → ENNReal :=
    fun hs π =>
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (pureToBehavioral I π) hs.2)
        (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y
  let FL : PureProfile I → (List M.Label × List M.State) → ENNReal :=
    fun π hs => μJ π * ((D.runDistPure n π) hs * Lfun hs)
  let FR : PureProfile I → (List M.Label × List M.State) → ENNReal :=
    fun π hs => μJ π * ((D.runDistPure n π) hs * Gfun hs π)
  have hswapL :
      (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Lfun hs)
        = ∑' hs, ∑' π, FL π hs := by
    calc
      (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Lfun hs)
          = ∑' π, ∑' hs, μJ π * ((D.runDistPure n π) hs * Lfun hs) := by
              refine tsum_congr ?_
              intro π
              rw [ENNReal.tsum_mul_left]
      _ = ∑' hs, ∑' π, μJ π * ((D.runDistPure n π) hs * Lfun hs) := by
            simpa using
              (ENNReal.tsum_comm
                (f := fun π hs => μJ π * ((D.runDistPure n π) hs * Lfun hs)))
      _ = ∑' hs, ∑' π, FL π hs := by simp [FL]
  have hswapR :
      (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Gfun hs π)
        = ∑' hs, ∑' π, FR π hs := by
    calc
      (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Gfun hs π)
          = ∑' π, ∑' hs, μJ π * ((D.runDistPure n π) hs * Gfun hs π) := by
              refine tsum_congr ?_
              intro π
              rw [ENNReal.tsum_mul_left]
      _ = ∑' hs, ∑' π, μJ π * ((D.runDistPure n π) hs * Gfun hs π) := by
            simpa using
              (ENNReal.tsum_comm
                (f := fun π hs => μJ π * ((D.runDistPure n π) hs * Gfun hs π)))
      _ = ∑' hs, ∑' π, FR π hs := by simp [FR]
  have hPerHs :
      ∀ hs : List M.Label × List M.State, (∑' π, FL π hs) = ∑' π, FR π hs := by
    intro hs
    by_cases hlen : hs.2.length = n + 1
    · let C : ENNReal := ∑' π, μJ π * (D.runDistPure n π) hs
      have hL :
          (∑' π, FL π hs) = C * Lfun hs := by
        calc
          (∑' π, FL π hs)
              = ∑' π, μJ π * ((D.runDistPure n π) hs * Lfun hs) := by
                  simp [FL]
          _ = ∑' π, (μJ π * (D.runDistPure n π) hs) * Lfun hs := by
                apply tsum_congr
                intro π
                ring
          _ = (∑' π, μJ π * (D.runDistPure n π) hs) * Lfun hs := by
                rw [ENNReal.tsum_mul_right]
          _ = C * Lfun hs := rfl
      have hR :
          (∑' π, FR π hs) =
            ∑' π, μJ π * ((D.runDistPure n π) hs * Gfun hs π) := by
        simp [FR, mul_assoc, mul_comm]
      have hBridge :
          C * Lfun hs =
            ∑' π, μJ π * ((D.runDistPure n π) hs * Gfun hs π) := by
        simpa [Lfun, Gfun, C, mul_assoc, mul_left_comm, mul_comm] using
          (stepPoint_eq_via_query_disintegration
            (I := I) (D := D) (hPR := hPR) (μ := μ) (n := n) (hs := hs) (y := y) hlen)
      exact hL.trans (hBridge.trans hR.symm)
    · have hfzero : ∀ π : PureProfile I, (D.runDistPure n π) hs = 0 := by
        intro π
        by_contra hne
        have hlen' :
            hs.2.length = n + 1 := by
          have hrun : (D.runDist n (pureToBehavioral I π)) hs ≠ 0 := by
            simpa [Execution.Dynamics.runDistPure] using hne
          exact InfoModel.runDist_support_stateLength (I := I) (D := D) n
            (pureToBehavioral I π) hs hrun
        exact hlen hlen'
      have hFL0 : (∑' π, FL π hs) = 0 := by
        exact (ENNReal.tsum_eq_zero).2 (by intro π; simp [FL, hfzero π])
      have hFR0 : (∑' π, FR π hs) = 0 := by
        exact (ENNReal.tsum_eq_zero).2 (by intro π; simp [FR, hfzero π])
      rw [hFL0, hFR0]
  calc
    (μJ.bind (fun π =>
      (D.runDistPure n π).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (mixedToBehavioral (I := I) μ) hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))))) y
        = (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Lfun hs) := by
            simp [μJ, Lfun, PMF.bind_apply]
    _ = ∑' hs, ∑' π, FL π hs := hswapL
    _ = ∑' hs, ∑' π, FR π hs := by
          apply tsum_congr
          intro hs
          exact hPerHs hs
    _ = (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Gfun hs π) := hswapR.symm
    _ = (μJ.bind (fun π =>
      (D.runDistPure n π).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))))) y := by
            simp [μJ, Gfun, PMF.bind_apply]

/-- **Kuhn (mixed → behavioral)** at the `InfoModel` level.

Do not strengthen this statement by introducing ad hoc assumptions
on mixed profiles. The intended assumptions are only model-level:
perfect recall and finite horizon.
-/
theorem mixedToBehavioral_correct
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (μ : InfoModel.MixedProfile (I := I)) :
    D.evalBehavioral k (mixedToBehavioral (I := I) μ) =
      (InfoModel.mixedJoint (I := I) μ).bind (D.evalPure k) := by
  exact evalBehavioral_eq_mixed_of_stepIndependence (I := I) (D := D) (k := k) μ
    (mixedToBehavioral (I := I) μ)
    (mixedToBehavioral_stepIndependence (I := I) (D := D) hPR μ)

theorem kuhn_mixed_to_behavioral
    [∀ i, Finite (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall) :
    KuhnMixedToBehavioralViaOutcome
      (BehavioralProfile I) (InfoModel.MixedProfile (I := I)) (PureProfile I) I.Outcome
      (InfoModel.mixedJoint (I := I)) (D.evalBehavioral k) (D.evalPure k) := by
  letI : ∀ i, Fintype (I.LocalTrace i) := fun i => Fintype.ofFinite (I.LocalTrace i)
  intro μ
  refine ⟨mixedToBehavioral (I := I) μ, ?_⟩
  simpa using mixedToBehavioral_correct (I := I) (D := D) (k := k) hPR μ

end InfoModel

end Theorems
end GameTheory

