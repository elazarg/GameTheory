import GameTheory.Theorems.KuhnCore
import GameTheory.Model.Lemmas.PerfectRecall

namespace GameTheory
namespace Theorems

open Math
open Math.PMFProduct

section InfoModel

open Execution

variable {ι : Type} [Fintype ι]
variable {M : LSM ι} (I : InfoModel M)
variable (D : Execution.Dynamics I)
variable (k : Nat)

noncomputable def condMixedLocal
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i))
    (v : I.LocalTrace i)
    (a : Option (M.Act i)) :
    PMF (InfoModel.LocalPure (I := I) i) :=
  if _ : Math.ProbabilityMassFunction.pushforward μi (fun f => f v) a ≠ 0 then
    Math.ProbabilityMassFunction.condOn μi (fun f => f v) a
  else
    μi

/-- Player-local history token used for iterated conditioning:
past local observation trace paired with the realized own action. -/
abbrev LocalHistTok (i : ι) : Type :=
  InfoModel.LocalHistTok (I := I) i

/-- Iterated local conditioning. -/
noncomputable def iterCondMixedLocal
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i)) :
    List (LocalHistTok (I := I) i) → PMF (InfoModel.LocalPure (I := I) i)
  | [] => μi
  | (v, a) :: rest =>
      iterCondMixedLocal i (condMixedLocal (I := I) i μi v a) rest

omit [Fintype ι] in
@[simp] theorem iterCondMixedLocal_nil
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i)) :
    iterCondMixedLocal (I := I) i μi [] = μi := rfl

omit [Fintype ι] in
theorem pushforward_bind_condMixedLocal
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i))
    (v : I.LocalTrace i) :
    (Math.ProbabilityMassFunction.pushforward μi (fun f => f v)).bind
      (condMixedLocal (I := I) i μi v) = μi := by
  classical
  have hcond :
      ∀ a, (Math.ProbabilityMassFunction.pushforward μi (fun f => f v)) a ≠ 0 →
        condMixedLocal (I := I) i μi v a =
          Math.ProbabilityMassFunction.condOn μi (fun f => f v) a := by
    intro a ha
    simp [condMixedLocal, ha]
  calc
    (Math.ProbabilityMassFunction.pushforward μi (fun f => f v)).bind
        (condMixedLocal (I := I) i μi v)
        =
      (Math.ProbabilityMassFunction.pushforward μi (fun f => f v)).bind
        (fun a =>
          Math.ProbabilityMassFunction.condOn μi (fun f => f v) a) := by
            exact Math.ProbabilityMassFunction.bind_congr_of_ne_zero
              (μ := Math.ProbabilityMassFunction.pushforward μi (fun f => f v))
              (f := condMixedLocal (I := I) i μi v)
              (g := fun a => Math.ProbabilityMassFunction.condOn μi (fun f => f v) a)
              hcond
    _ = μi := by
          simpa using
            (Math.ProbabilityMassFunction.bind_pushforward_condOn
              (μ := μi) (proj := fun f => f v) (g := fun f => PMF.pure f)).symm

set_option linter.unusedFintypeInType false in
open Classical in
/-- Decompose a product-measure bind by sampling queried actions first,
then resampling local pure policies from per-player conditionals. -/
theorem mixedJoint_bind_decompose_query
    (μ : InfoModel.MixedProfile (I := I))
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (v : ∀ i, I.LocalTrace i)
    {β : Type}
    (g : PureProfile I → PMF β) :
    (InfoModel.mixedJoint (I := I) μ).bind g =
      (pmfPi (fun i => Math.ProbabilityMassFunction.pushforward (μ i) (fun f => f (v i)))).bind
        (fun acts =>
          (InfoModel.mixedJoint (I := I)
            (fun i => condMixedLocal (I := I) i (μ i) (v i) (acts i))).bind g) := by
  have hplayer :
      ∀ i fi,
        ∑ a : Option (M.Act i),
          (Math.ProbabilityMassFunction.pushforward (μ i) (fun f => f (v i))) a *
            (condMixedLocal (I := I) i (μ i) (v i) a) fi
          = (μ i) fi := by
    intro i fi
    have h := pushforward_bind_condMixedLocal (I := I) i (μ i) (v i)
    have hfi := PMF.ext_iff.mp h fi
    simpa only [PMF.bind_apply, tsum_fintype] using hfi
  apply PMF.ext
  intro y
  simp only [PMF.bind_apply, tsum_fintype, InfoModel.mixedJoint, pmfPi_apply]
  symm
  simp_rw [Finset.mul_sum, ← mul_assoc, ← Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  congr 1
  funext f
  congr 1
  rw [(Fintype.prod_sum
    (fun i a =>
      (Math.ProbabilityMassFunction.pushforward (μ i) (fun f => f (v i))) a *
        (condMixedLocal (I := I) i (μ i) (v i) a) (f i))).symm]
  congr 1
  funext i
  exact hplayer i (f i)

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

/-- For a fixed state-trace prefix, one-step pure extension depends only on the
queried local actions at `projectStates`. -/
theorem pure_step_pushforward_depends_on_query
    [∀ i, Fintype (Option (M.Act i))]
    (hs : List M.Label × List M.State)
    (y : List M.Label × List M.State)
    (π π' : PureProfile I)
    (hquery :
      ∀ i, π i (I.projectStates i hs.2) = π' i (I.projectStates i hs.2)) :
    (Math.ProbabilityMassFunction.pushforward
      (D.stepDist (pureToBehavioral I π) hs.2)
      (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y
      =
    (Math.ProbabilityMassFunction.pushforward
      (D.stepDist (pureToBehavioral I π') hs.2)
      (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y := by
  let ω : I.FlatPolicy := fun k => π k.1 k.2
  let ω' : I.FlatPolicy := fun k => π' k.1 k.2
  have hnow :
      ∀ i, ω ⟨i, I.projectStates i hs.2⟩ = ω' ⟨i, I.projectStates i hs.2⟩ := by
    intro i
    simpa [ω, ω'] using hquery i
  have hstep :
      D.stepDist (pureToBehavioral I (I.reassemblePolicy ω)) hs.2 =
        D.stepDist (pureToBehavioral I (I.reassemblePolicy ω')) hs.2 :=
    InfoModel.stepDist_depends_on_current_context (I := I) (D := D) ω ω' hs.2 hnow
  have hpush := congrArg
    (fun ν =>
      (Math.ProbabilityMassFunction.pushforward ν
        (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y)
    hstep
  simpa [ω, ω'] using hpush

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

private def LocalHistCompatible
    (i : ι)
    (f : InfoModel.LocalPure (I := I) i)
    (hist : List (LocalHistTok (I := I) i)) : Prop :=
  ∀ tok ∈ hist, f tok.1 = tok.2

private noncomputable def localHistIndicator
    (i : ι)
    (f : InfoModel.LocalPure (I := I) i)
    (hist : List (LocalHistTok (I := I) i)) : ENNReal :=
  by
    classical
    exact if LocalHistCompatible (I := I) i f hist then 1 else 0

private noncomputable def localHistMass
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i)) :
    List (LocalHistTok (I := I) i) → ENNReal
  | [] => 1
  | (v, a) :: rest =>
      (Math.ProbabilityMassFunction.pushforward μi (fun f => f v)) a *
        localHistMass i (condMixedLocal (I := I) i μi v a) rest

omit [Fintype ι] in
private theorem localHistMass_mul_iterCondMixedLocal_apply
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i)) :
    ∀ (hist : List (LocalHistTok (I := I) i)) (f : InfoModel.LocalPure (I := I) i),
      localHistMass (I := I) i μi hist *
          iterCondMixedLocal (I := I) i μi hist f =
        μi f * localHistIndicator (I := I) i f hist
  | [], f => by
      classical
      simp [localHistMass, localHistIndicator, LocalHistCompatible]
  | (v, a) :: rest, f => by
      classical
      have ih :=
        localHistMass_mul_iterCondMixedLocal_apply
          i (μi := condMixedLocal (I := I) i μi v a) rest f
      set p : ENNReal :=
        (Math.ProbabilityMassFunction.pushforward μi (fun g => g v)) a
      have hhead :
          p * condMixedLocal (I := I) i μi v a f =
            μi f * if f v = a then 1 else 0 := by
        by_cases hp : p = 0
        · by_cases hfa : f v = a
          · have hf0 : μi f = 0 := by
              apply Math.ProbabilityMassFunction.eq_zero_of_pushforward_eq_zero
                (μ := μi) (proj := fun g => g v) (b := a) hp
              simpa using hfa
            simp [p, hp, condMixedLocal, hfa, hf0]
          · simp [p, hp, condMixedLocal, hfa]
        · have hp' : p ≠ 0 := hp
          have hcond :
              condMixedLocal (I := I) i μi v a =
                Math.ProbabilityMassFunction.condOn μi (fun g => g v) a := by
            simp [condMixedLocal, p, hp']
          rw [hcond]
          rw [Math.ProbabilityMassFunction.condOn_apply
            (μ := μi) (proj := fun g => g v) (b := a) (a := f) hp']
          by_cases hfa : f v = a
          · simp [p, hfa, div_eq_mul_inv, mul_left_comm, mul_comm,
              ENNReal.mul_inv_cancel hp' (PMF.apply_ne_top _ _)]
          · simp [p, hfa]
      calc
        localHistMass (I := I) i μi ((v, a) :: rest) *
            iterCondMixedLocal (I := I) i μi ((v, a) :: rest) f
            =
          p * (localHistMass (I := I) i
            (condMixedLocal (I := I) i μi v a) rest *
              iterCondMixedLocal (I := I) i
                (condMixedLocal (I := I) i μi v a) rest f) := by
                simp [localHistMass, iterCondMixedLocal, p, mul_assoc]
        _ =
          p * ((condMixedLocal (I := I) i μi v a) f *
            localHistIndicator (I := I) i f rest) := by
              rw [ih]
        _ =
          (p * condMixedLocal (I := I) i μi v a f) *
            localHistIndicator (I := I) i f rest := by
              ac_rfl
        _ =
          (μi f * if f v = a then 1 else 0) *
            localHistIndicator (I := I) i f rest := by
              rw [hhead]
        _ =
          μi f *
            (if f v = a then 1 else 0) *
            localHistIndicator (I := I) i f rest := by
              ac_rfl
        _ =
          μi f * localHistIndicator (I := I) i f ((v, a) :: rest) := by
              by_cases hfa : f v = a <;>
                by_cases hrest : LocalHistCompatible (I := I) i f rest <;>
                simp [localHistIndicator, LocalHistCompatible, hfa]

private theorem stepDist_behavioral_depends_on_current_context
    [∀ i, Fintype (Option (M.Act i))]
    (σ τ : BehavioralProfile I) (ss : List M.State)
    (hag : ∀ i, σ i (I.projectStates i ss) = τ i (I.projectStates i ss)) :
    D.stepDist σ ss = D.stepDist τ ss := by
  simp only [Execution.Dynamics.stepDist]
  congr 1
  funext lab
  congr 1
  simp [Execution.Dynamics.jointActionDist, hag]

omit [Fintype ι] in
private theorem localHistCompatible_append_singleton_iff
    (i : ι)
    (f : InfoModel.LocalPure (I := I) i)
    (hist : List (LocalHistTok (I := I) i))
    (v : I.LocalTrace i)
    (a : Option (M.Act i)) :
    LocalHistCompatible (I := I) i f (hist ++ [(v, a)]) ↔
      LocalHistCompatible (I := I) i f hist ∧ f v = a := by
  constructor
  · intro h
    constructor
    · intro tok htok
      exact h tok (by simp [htok])
    · exact h (v, a) (by simp)
  · rintro ⟨hhist, hv⟩ tok htok
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at htok
    rcases htok with htok | htok
    · exact hhist tok htok
    · rcases htok with rfl
      exact hv

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
                  simp [hlabel, hfun, htail]
                  exact hlabel

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

omit [Fintype ι] in
private theorem append_singleton_eq
    {α : Type} {xs ys : List α} {x y : α}
    (h : xs ++ [x] = ys ++ [y]) :
    xs = ys ∧ x = y := by
  have hdrop := congrArg List.dropLast h
  have hlast := congrArg List.getLast? h
  constructor
  · simpa using hdrop
  · have : some x = some y := by simpa using hlast
    exact Option.some.inj this

omit [Fintype ι] in
private theorem pushforward_fixedLabel_apply_same
    (ν : PMF M.State) (lab : M.Label) (t : M.State) :
    Math.ProbabilityMassFunction.pushforward ν (fun u => (lab, u)) (lab, t) = ν t := by
  simp only [ProbabilityMassFunction.pushforward, PMF.bind_apply, PMF.pure_apply, Prod.mk.injEq,
    true_and, mul_ite, mul_one, mul_zero, eq_comm]
  rw [tsum_eq_single t]
  · simp
  · intro a ha
    by_cases hEq : (lab, t) = (lab, a)
    · have : t = a := by simpa using congrArg Prod.snd hEq
      exact False.elim (ha this.symm)
    · simp [hEq]

omit [Fintype ι] in
private theorem pushforward_fixedLabel_apply_ne
    (ν : PMF M.State) (lab lab' : M.Label) (t : M.State) (h : lab' ≠ lab) :
    Math.ProbabilityMassFunction.pushforward ν (fun u => (lab', u)) (lab, t) = 0 := by
  simp only [ProbabilityMassFunction.pushforward, PMF.bind_apply, PMF.pure_apply, Prod.mk.injEq,
    mul_ite, mul_one, mul_zero, eq_comm]
  symm
  rw [ENNReal.tsum_eq_zero]
  intro a
  have hEq : (lab, t) ≠ (lab', a) := by
    intro hpair
    exact h ((by simpa using (congrArg Prod.fst hpair).symm) : lab' = lab)
  simp [hEq]

private theorem stepDist_pure_apply_point
    [∀ i, Fintype (Option (M.Act i))]
    (π : PureProfile I) (ss : List M.State) (lab : M.Label) (t : M.State) :
    let s := (ss.getLast?).getD M.init
    let aCur : ∀ i, Option (M.Act i) := fun i => π i (I.projectStates i ss)
    (D.stepDist (pureToBehavioral I π) ss) (lab, t)
      = (D.labelKernel s) lab * D.nextState lab aCur s t := by
  classical
  let s := (ss.getLast?).getD M.init
  let aCur : ∀ i, Option (M.Act i) := fun i => π i (I.projectStates i ss)
  rw [InfoModel.stepDist_pure (I := I) (D := D) π ss]
  simp only [PMF.bind_apply]
  have hinner :
      ∀ lab',
        (Math.ProbabilityMassFunction.pushforward (D.nextState lab' aCur s)
          (fun u => (lab', u))) (lab, t)
          = if lab' = lab then D.nextState lab aCur s t else 0 := by
    intro lab'
    by_cases h : lab' = lab
    · simpa [h] using
        (pushforward_fixedLabel_apply_same (ν := D.nextState lab' aCur s) lab' t)
    · simpa [h] using
        (pushforward_fixedLabel_apply_ne (ν := D.nextState lab' aCur s) lab lab' t h)
  have hrewrite :
      (∑' lab' : M.Label,
        (D.labelKernel s) lab' *
          (Math.ProbabilityMassFunction.pushforward (D.nextState lab' aCur s)
            (fun u => (lab', u))) (lab, t))
        =
      ∑' lab' : M.Label,
        (D.labelKernel s) lab' *
          (if lab' = lab then D.nextState lab aCur s t else 0) := by
    congr
    funext lab'
    rw [hinner lab']
  rw [hrewrite]
  rw [tsum_eq_single lab]
  · simp [s, aCur]
  · intro lab' hne
    rw [if_neg hne]
    simp

private theorem stepDist_pure_point_nonzero
    [∀ i, Fintype (Option (M.Act i))]
    (π : PureProfile I) (ss : List M.State) (lab : M.Label) (t : M.State)
    (hstep : (D.stepDist (pureToBehavioral I π) ss) (lab, t) ≠ 0) :
    let s := (ss.getLast?).getD M.init
    let aCur : ∀ i, Option (M.Act i) := fun i => π i (I.projectStates i ss)
    (D.labelKernel s) lab ≠ 0 ∧ D.nextState lab aCur s t ≠ 0 := by
  let s := (ss.getLast?).getD M.init
  let aCur : ∀ i, Option (M.Act i) := fun i => π i (I.projectStates i ss)
  have hform := stepDist_pure_apply_point (I := I) (D := D) π ss lab t
  have hprod : (D.labelKernel s) lab * D.nextState lab aCur s t ≠ 0 := by
    simpa [hform] using hstep
  constructor
  · intro hzero
    apply hprod
    rw [hzero, zero_mul]
  · intro hzero
    apply hprod
    rw [hzero, mul_zero]

private theorem pushforward_append_nonzero_exists
    (μ : PMF (M.Label × M.State))
    (h : List M.Label) (ss : List M.State)
    (hs : List M.Label × List M.State)
    (hpush : (Math.ProbabilityMassFunction.pushforward μ
      (fun ls => (h ++ [ls.1], ss ++ [ls.2]))) hs ≠ 0) :
    ∃ lab t, hs = (h ++ [lab], ss ++ [t]) ∧ μ (lab, t) ≠ 0 := by
  classical
  rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_apply] at hpush
  by_contra hnone
  push_neg at hnone
  apply hpush
  rw [ENNReal.tsum_eq_zero]
  intro ls
  rcases ls with ⟨lab, t⟩
  by_cases heq : hs = (h ++ [lab], ss ++ [t])
  · have hμ : μ (lab, t) = 0 := hnone lab t heq
    simp [PMF.pure_apply, heq, hμ]
  · simp [PMF.pure_apply, heq]

private theorem pushforward_append_apply_same
    (μ : PMF (M.Label × M.State))
    (h : List M.Label) (ss : List M.State) (lab : M.Label) (t : M.State) :
    (Math.ProbabilityMassFunction.pushforward μ
      (fun ls => (h ++ [ls.1], ss ++ [ls.2]))) (h ++ [lab], ss ++ [t]) = μ (lab, t) := by
  rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_apply]
  rw [tsum_eq_single (lab, t)]
  · simp [PMF.pure_apply]
  · intro ls hls
    rcases ls with ⟨lab', t'⟩
    have hEq : (h ++ [lab], ss ++ [t]) ≠ (h ++ [lab'], ss ++ [t']) := by
      intro hpair
      have hfst := congrArg Prod.fst hpair
      have hsnd := congrArg Prod.snd hpair
      have h1 := append_singleton_eq hfst
      have h2 := append_singleton_eq hsnd
      apply hls
      cases h1 with
      | intro _ hLab =>
          cases h2 with
          | intro _ hT =>
              cases hLab
              cases hT
              rfl
    simp [PMF.pure_apply, hEq]

private theorem pushforward_append_apply_other
    (μ : PMF (M.Label × M.State))
    (h1 h2 : List M.Label) (ss1 ss2 : List M.State) (lab : M.Label) (t : M.State)
    (hneq : (h1, ss1) ≠ (h2, ss2)) :
    (Math.ProbabilityMassFunction.pushforward μ
      (fun ls => (h1 ++ [ls.1], ss1 ++ [ls.2]))) (h2 ++ [lab], ss2 ++ [t]) = 0 := by
  rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_apply]
  refine (ENNReal.tsum_eq_zero).2 ?_
  intro ls
  rcases ls with ⟨lab', t'⟩
  have hEq : (h2 ++ [lab], ss2 ++ [t]) ≠ (h1 ++ [lab'], ss1 ++ [t']) := by
    intro hpair
    have hfst := congrArg Prod.fst hpair
    have hsnd := congrArg Prod.snd hpair
    have h1' := append_singleton_eq hfst.symm
    have h2' := append_singleton_eq hsnd.symm
    apply hneq
    cases h1' with
    | intro hh hLab =>
        cases h2' with
        | intro hss hT =>
            exact Prod.ext hh hss
  simp [PMF.pure_apply, hEq]

private theorem runDistPure_succ_apply_path
    [∀ i, Fintype (Option (M.Act i))]
    (π : PureProfile I)
    (n : Nat) (hsPrev : List M.Label × List M.State) (lab : M.Label) (t : M.State) :
    D.runDistPure (n + 1) π (hsPrev.1 ++ [lab], hsPrev.2 ++ [t]) =
      D.runDistPure n π hsPrev *
        (D.stepDist (pureToBehavioral I π) hsPrev.2) (lab, t) := by
  rw [Execution.Dynamics.runDistPure,
    InfoModel.runDist_succ (I := I) (D := D) n (pureToBehavioral I π), PMF.bind_apply]
  rw [tsum_eq_single hsPrev]
  · rw [pushforward_append_apply_same]
    simp [Execution.Dynamics.runDistPure]
  · intro hsPrev' hne
    have hzero := pushforward_append_apply_other
      (μ := D.stepDist (pureToBehavioral I π) hsPrev'.2)
      hsPrev'.1 hsPrev.1 hsPrev'.2 hsPrev.2 lab t hne
    simp [hzero]

private theorem exists_prev_of_runDistPure_succ_ne_zero
    [∀ i, Fintype (Option (M.Act i))]
    (π : PureProfile I)
    (n : Nat)
    (hs : List M.Label × List M.State)
    (hhs : D.runDistPure (n + 1) π hs ≠ 0) :
    ∃ hsPrev,
      D.runDistPure n π hsPrev ≠ 0 ∧
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (pureToBehavioral I π) hsPrev.2)
        (fun ls => (hsPrev.1 ++ [ls.1], hsPrev.2 ++ [ls.2]))) hs ≠ 0 := by
  classical
  rw [Execution.Dynamics.runDistPure,
    InfoModel.runDist_succ (I := I) (D := D) n (pureToBehavioral I π),
    PMF.bind_apply] at hhs
  by_contra hnone
  push_neg at hnone
  apply hhs
  rw [ENNReal.tsum_eq_zero]
  intro hsPrev
  by_cases hprev : D.runDistPure n π hsPrev = 0
  · simpa [Execution.Dynamics.runDistPure] using Or.inl hprev
  · simpa [Execution.Dynamics.runDistPure] using Or.inr (hnone hsPrev hprev)

private theorem exists_reachActionTrace_of_runDistPure_ne_zero
    [∀ i, Fintype (Option (M.Act i))]
    (n : Nat) (π : PureProfile I) (hs : List M.Label × List M.State)
    (hhs : D.runDistPure n π hs ≠ 0) :
    ∃ ha : List (M.Label × (∀ j, Option (M.Act j))),
      InfoModel.ReachActionTrace M ha hs.2 ∧
      ha.map Prod.fst = hs.1 ∧
      ∀ i, LocalHistCompatible (I := I) i (π i)
        (InfoModel.localHistTokens (I := I) i ha hs.2) := by
  induction n generalizing hs with
  | zero =>
      rw [Execution.Dynamics.runDistPure,
        InfoModel.runDist_zero (I := I) (D := D) (pureToBehavioral I π)] at hhs
      have hmem : hs ∈ (PMF.pure ([], [M.init]) : PMF (List M.Label × List M.State)).support := by
        simpa [PMF.mem_support_iff] using hhs
      rw [PMF.support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      refine ⟨[], InfoModel.ReachActionTrace.nil, rfl, ?_⟩
      intro _ _ htok
      cases htok
  | succ n ih =>
      obtain ⟨hsPrev, hprev, hpush⟩ :=
        exists_prev_of_runDistPure_succ_ne_zero (I := I) (D := D) π n hs hhs
      obtain ⟨haPrev, hrPrev, hlabelsPrev, hcompatPrev⟩ := ih hsPrev hprev
      obtain ⟨lab, t, hEq, hstep⟩ :=
        pushforward_append_nonzero_exists
          (μ := D.stepDist (pureToBehavioral I π) hsPrev.2)
          hsPrev.1 hsPrev.2 hs hpush
      subst hEq
      let s : M.State := (hsPrev.2.getLast?).getD M.init
      let aCur : ∀ i, Option (M.Act i) := fun i => π i (I.projectStates i hsPrev.2)
      have hstep' := stepDist_pure_point_nonzero (I := I) (D := D) π hsPrev.2 lab t hstep
      have hsLast : hsPrev.2.getLast? = some s := by
        unfold s
        rw [List.getLast?_eq_getLast_of_ne_nil (reachActionTrace_nonempty (M := M) hrPrev)]
        simp
      have hrel : M.step lab aCur s t :=
        D.nextState_sound lab aCur s t hstep'.2
      refine ⟨haPrev ++ [(lab, aCur)], InfoModel.ReachActionTrace.snoc hrPrev hsLast hrel, ?_, ?_⟩
      · simp [hlabelsPrev, List.map_append]
      · intro i
        have hLenPrev : hsPrev.2.length = haPrev.length + 1 :=
          InfoModel.ReachActionTrace.length_states_eq_succ_actions hrPrev
        have htoks :
            InfoModel.localHistTokens (I := I) i (haPrev ++ [(lab, aCur)]) (hsPrev.2 ++ [t]) =
              InfoModel.localHistTokens (I := I) i haPrev hsPrev.2 ++
                [(I.projectStates i hsPrev.2, aCur i)] := by
          simpa using
            (InfoModel.localHistTokens_snoc (I := I) i haPrev hsPrev.2 hLenPrev lab aCur t)
        rw [htoks]
        intro tok htok
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at htok
        rcases htok with htok | htok
        · exact hcompatPrev i tok htok
        · rcases htok with rfl
          rfl

private theorem runDistPure_eq_of_localHistCompatible
    [∀ i, Fintype (Option (M.Act i))]
    {ha : List (M.Label × (∀ j, Option (M.Act j)))}
    {ss : List M.State}
    (hr : InfoModel.ReachActionTrace M ha ss)
    (π π' : PureProfile I)
    (hπ :
      ∀ i, LocalHistCompatible (I := I) i (π i)
        (InfoModel.localHistTokens (I := I) i ha ss))
    (hπ' :
      ∀ i, LocalHistCompatible (I := I) i (π' i)
        (InfoModel.localHistTokens (I := I) i ha ss)) :
    D.runDistPure ha.length π (ha.map Prod.fst, ss) =
      D.runDistPure ha.length π' (ha.map Prod.fst, ss) := by
  induction hr generalizing π π' with
  | nil =>
      simp [Execution.Dynamics.runDistPure]
  | @snoc ha ss s t lab a hrPrev hsLast hrel ih =>
      have hLenPrev :
          ss.length = ha.length + 1 :=
        InfoModel.ReachActionTrace.length_states_eq_succ_actions hrPrev
      have htoks :
          ∀ i,
            InfoModel.localHistTokens (I := I) i (ha ++ [(lab, a)]) (ss ++ [t]) =
              InfoModel.localHistTokens (I := I) i ha ss ++
                [(I.projectStates i ss, a i)] := by
        intro i
        simpa using
          (InfoModel.localHistTokens_snoc (I := I) i ha ss hLenPrev lab a t)
      have hπPrev :
          ∀ i, LocalHistCompatible (I := I) i (π i)
            (InfoModel.localHistTokens (I := I) i ha ss) := by
        intro i
        have hi := hπ i
        rw [htoks i] at hi
        exact
          (localHistCompatible_append_singleton_iff
            (I := I) i (π i)
            (InfoModel.localHistTokens (I := I) i ha ss)
            (I.projectStates i ss) (a i)).1 hi |>.1
      have hπNow : ∀ i, π i (I.projectStates i ss) = a i := by
        intro i
        have hi := hπ i
        rw [htoks i] at hi
        exact
          (localHistCompatible_append_singleton_iff
            (I := I) i (π i)
            (InfoModel.localHistTokens (I := I) i ha ss)
            (I.projectStates i ss) (a i)).1 hi |>.2
      have hπ'Prev :
          ∀ i, LocalHistCompatible (I := I) i (π' i)
            (InfoModel.localHistTokens (I := I) i ha ss) := by
        intro i
        have hi := hπ' i
        rw [htoks i] at hi
        exact
          (localHistCompatible_append_singleton_iff
            (I := I) i (π' i)
            (InfoModel.localHistTokens (I := I) i ha ss)
            (I.projectStates i ss) (a i)).1 hi |>.1
      have hπ'Now : ∀ i, π' i (I.projectStates i ss) = a i := by
        intro i
        have hi := hπ' i
        rw [htoks i] at hi
        exact
          (localHistCompatible_append_singleton_iff
            (I := I) i (π' i)
            (InfoModel.localHistTokens (I := I) i ha ss)
            (I.projectStates i ss) (a i)).1 hi |>.2
      have hprev :
          D.runDistPure ha.length π (ha.map Prod.fst, ss) =
            D.runDistPure ha.length π' (ha.map Prod.fst, ss) :=
        ih π π' hπPrev hπ'Prev
      have hstep :
          (D.stepDist (pureToBehavioral I π) ss) (lab, t) =
            (D.stepDist (pureToBehavioral I π') ss) (lab, t) := by
        let ω : I.FlatPolicy := fun k => π k.1 k.2
        let ω' : I.FlatPolicy := fun k => π' k.1 k.2
        have hnow :
            ∀ i,
              ω ⟨i, I.projectStates i ss⟩ =
                ω' ⟨i, I.projectStates i ss⟩ := by
          intro i
          simpa [ω, ω'] using (hπNow i).trans (hπ'Now i).symm
        have hstepEq :
            D.stepDist (pureToBehavioral I (I.reassemblePolicy ω)) ss =
              D.stepDist (pureToBehavioral I (I.reassemblePolicy ω')) ss :=
          InfoModel.stepDist_depends_on_current_context
            (I := I) (D := D) ω ω' ss hnow
        simpa [ω, ω'] using congrArg (fun ν => ν (lab, t)) hstepEq
      calc
        D.runDistPure (List.length (ha ++ [(lab, a)])) π
            ((ha ++ [(lab, a)]).map Prod.fst, ss ++ [t])
            =
          D.runDistPure ha.length π (ha.map Prod.fst, ss) *
            (D.stepDist (pureToBehavioral I π) ss) (lab, t) := by
              simpa [List.length_append, List.map_append] using
                (runDistPure_succ_apply_path (I := I) (D := D) π ha.length
                  (ha.map Prod.fst, ss) lab t)
        _ =
          D.runDistPure ha.length π' (ha.map Prod.fst, ss) *
            (D.stepDist (pureToBehavioral I π') ss) (lab, t) := by
              rw [hprev, hstep]
        _ =
          D.runDistPure (List.length (ha ++ [(lab, a)])) π'
            ((ha ++ [(lab, a)]).map Prod.fst, ss ++ [t]) := by
              simpa [List.length_append, List.map_append] using
                (runDistPure_succ_apply_path (I := I) (D := D) π' ha.length
                  (ha.map Prod.fst, ss) lab t).symm

private theorem runDistPure_eq_zero_of_not_localHistCompatible
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    {ha : List (M.Label × (∀ j, Option (M.Act j)))}
    {ss : List M.State}
    (hr : InfoModel.ReachActionTrace M ha ss)
    (π : PureProfile I)
    (hnc :
      ¬ ∀ i, LocalHistCompatible (I := I) i (π i)
        (InfoModel.localHistTokens (I := I) i ha ss)) :
    D.runDistPure ha.length π (ha.map Prod.fst, ss) = 0 := by
  by_contra hne
  obtain ⟨ha', hr', hlabels', hcompat'⟩ :=
    exists_reachActionTrace_of_runDistPure_ne_zero
      (I := I) (D := D) ha.length π (ha.map Prod.fst, ss) hne
  have hacts :
      ∀ i, InfoModel.projectActions i ha' = InfoModel.projectActions i ha := by
    intro i
    exact actionRecall_of_projectStates_eq (I := I) hPR i hr' hr rfl
  have htrace : ha' = ha :=
    actionTrace_eq_of_labels_projectActions_eq
      (ha₁ := ha') (ha₂ := ha) hlabels' hacts
  have hcompatAll :
      ∀ i, LocalHistCompatible (I := I) i (π i)
        (InfoModel.localHistTokens (I := I) i ha ss) := by
    intro i
    simpa [htrace] using hcompat' i
  exact hnc hcompatAll

private theorem runDistPure_factor_via_localHistIndicators
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    {ha : List (M.Label × (∀ j, Option (M.Act j)))}
    {ss : List M.State}
    (hr : InfoModel.ReachActionTrace M ha ss)
    (π0 : PureProfile I)
    (hcompat0 :
      ∀ i, LocalHistCompatible (I := I) i (π0 i)
        (InfoModel.localHistTokens (I := I) i ha ss))
    (π : PureProfile I) :
    D.runDistPure ha.length π (ha.map Prod.fst, ss) =
      D.runDistPure ha.length π0 (ha.map Prod.fst, ss) *
        ∏ i, localHistIndicator (I := I) i (π i)
          (InfoModel.localHistTokens (I := I) i ha ss) := by
  classical
  by_cases hcompat :
      ∀ i, LocalHistCompatible (I := I) i (π i)
        (InfoModel.localHistTokens (I := I) i ha ss)
  · have hrun :=
      runDistPure_eq_of_localHistCompatible
        (I := I) (D := D) hr π π0 hcompat hcompat0
    have hprod :
        (∏ i, localHistIndicator (I := I) i (π i)
          (InfoModel.localHistTokens (I := I) i ha ss)) = 1 := by
      refine Finset.prod_eq_one ?_
      intro i _
      simp [localHistIndicator, hcompat i]
    calc
      D.runDistPure ha.length π (ha.map Prod.fst, ss) =
        D.runDistPure ha.length π0 (ha.map Prod.fst, ss) := hrun
      _ =
        D.runDistPure ha.length π0 (ha.map Prod.fst, ss) * 1 := by simp
      _ =
        D.runDistPure ha.length π0 (ha.map Prod.fst, ss) *
          ∏ i, localHistIndicator (I := I) i (π i)
            (InfoModel.localHistTokens (I := I) i ha ss) := by rw [hprod]
  · have hrun0 :=
      runDistPure_eq_zero_of_not_localHistCompatible
        (I := I) (D := D) hPR hr π hcompat
    obtain ⟨i, hi⟩ := not_forall.mp hcompat
    have hprod0 :
        (∏ j, localHistIndicator (I := I) j (π j)
          (InfoModel.localHistTokens (I := I) j ha ss)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp [localHistIndicator, hi]
    simp [hrun0, hprod0]

private theorem localHistMass_mul_mixedJoint_iterCond_apply
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : InfoModel.MixedProfile (I := I))
    (hist : ∀ i, List (LocalHistTok (I := I) i))
    (π : PureProfile I) :
    (∏ i, localHistMass (I := I) i (μ i) (hist i)) *
      (InfoModel.mixedJoint (I := I)
        (fun i => iterCondMixedLocal (I := I) i (μ i) (hist i))) π
      =
    (InfoModel.mixedJoint (I := I) μ) π *
      ∏ i, localHistIndicator (I := I) i (π i) (hist i) := by
  simp only [InfoModel.mixedJoint, pmfPi_apply]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  funext i
  exact localHistMass_mul_iterCondMixedLocal_apply
    (I := I) i (μi := μ i) (hist i) (π i)

private theorem mixedJoint_stepDist_eq_realizeBehavioralCanonical
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : InfoModel.MixedProfile (I := I))
    (ss : List M.State) :
    (InfoModel.mixedJoint (I := I) μ).bind
      (fun π => D.stepDist (pureToBehavioral I π) ss)
      =
    D.stepDist (InfoModel.realizeBehavioralCanonical (I := I) μ) ss := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  simp_rw [InfoModel.stepDist_pure (I := I) (D := D)]
  set s := (ss.getLast?).getD M.init
  conv_lhs => rw [PMF.bind_comm]
  simp only [Execution.Dynamics.stepDist]
  congr 1
  funext lab
  simp only [Math.ProbabilityMassFunction.pushforward]
  conv_lhs =>
    arg 2; ext π
    rw [← PMF.pure_bind (fun i => π i (I.projectStates i ss))
      (fun a => (D.nextState lab a s).bind (fun t => PMF.pure (lab, t)))]
  rw [show ((InfoModel.mixedJoint (I := I) μ).bind fun π =>
      (PMF.pure (fun i => π i (I.projectStates i ss))).bind fun a =>
        (D.nextState lab a s).bind fun t => PMF.pure (lab, t)) =
    ((InfoModel.mixedJoint (I := I) μ).bind
      (fun π => PMF.pure (fun i => π i (I.projectStates i ss)))).bind (fun a =>
        (D.nextState lab a s).bind fun t => PMF.pure (lab, t)) from
    (PMF.bind_bind _ _ _).symm]
  have hJA' :
      (InfoModel.mixedJoint (I := I) μ).bind
        (fun π => PMF.pure (fun i => π i (I.projectStates i ss))) =
      Execution.Dynamics.jointActionDist (I := I)
        (InfoModel.realizeBehavioralCanonical (I := I) μ) ss := by
    simpa [Math.ProbabilityMassFunction.pushforward, InfoModel.mixedJoint,
      Execution.Dynamics.jointActionDist, InfoModel.realizeBehavioralCanonical] using
      (Math.PMFProduct.pmfPi_push_coordwise
        (μ := μ) (g := fun i fi => fi (I.projectStates i ss)))
  rw [hJA']

private theorem mixedJoint_stepPoint_eq_realizeBehavioralCanonical
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : InfoModel.MixedProfile (I := I))
    (hs y : List M.Label × List M.State) :
    (∑' π, (InfoModel.mixedJoint (I := I) μ) π *
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (pureToBehavioral I π) hs.2)
        (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y)
      =
    (Math.ProbabilityMassFunction.pushforward
      (D.stepDist (InfoModel.realizeBehavioralCanonical (I := I) μ) hs.2)
      (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y := by
  have hstep :=
    mixedJoint_stepDist_eq_realizeBehavioralCanonical (I := I) (D := D) μ hs.2
  have hpush := congrArg
    (fun ν =>
      (Math.ProbabilityMassFunction.pushforward ν
        (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y)
    hstep
  have hpushBind :
      ((InfoModel.mixedJoint (I := I) μ).bind
        (fun π =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (pureToBehavioral I π) hs.2)
            (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) y
        =
      (Math.ProbabilityMassFunction.pushforward
        ((InfoModel.mixedJoint (I := I) μ).bind
          (fun π => D.stepDist (pureToBehavioral I π) hs.2))
        (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y := by
          simpa using congrArg (fun ν => ν y) (
            (Math.ProbabilityMassFunction.pushforward_bind
              (μ := InfoModel.mixedJoint (I := I) μ)
              (k := fun π => D.stepDist (pureToBehavioral I π) hs.2)
              (f := fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))).symm)
  calc
    (∑' π, (InfoModel.mixedJoint (I := I) μ) π *
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (pureToBehavioral I π) hs.2)
        (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y)
        =
      ((InfoModel.mixedJoint (I := I) μ).bind
        (fun π =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (pureToBehavioral I π) hs.2)
            (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) y := by
              simp [PMF.bind_apply]
    _ =
      (Math.ProbabilityMassFunction.pushforward
        ((InfoModel.mixedJoint (I := I) μ).bind
          (fun π => D.stepDist (pureToBehavioral I π) hs.2))
        (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y := hpushBind
    _ =
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (InfoModel.realizeBehavioralCanonical (I := I) μ) hs.2)
        (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y := by
          simpa using hpush

/-- Fixed-prefix weighted one-step bridge via query-disintegration.
This is the core mixed→behavioral step identity used inside `hPerHs`. -/
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
            (I := I) (D := D) hPR μ n hs y hlen)
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

