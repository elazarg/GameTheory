import GameTheory.Model.Lemmas.Profiles
import GameTheory.Model.Lemmas.ExecutionLocality
import GameTheory.Model.Lemmas.LocalConditioning
import GameTheory.Model.Lemmas.PerfectRecall

namespace GameTheory
namespace InfoModel

open Execution
open Math.PMFProduct

variable {ι : Type} [Fintype ι]
variable {M : LSM ι} (I : InfoModel M)
variable (D : Execution.Dynamics I)

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
theorem actionTrace_eq_of_labels_projectActions_eq
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
private theorem pushforward_fixedLabel_apply_same
    (ν : PMF M.State) (lab : M.Label) (t : M.State) :
    Math.ProbabilityMassFunction.pushforward ν (fun u => (lab, u)) (lab, t) = ν t := by
  simp only [Math.ProbabilityMassFunction.pushforward, PMF.bind_apply, PMF.pure_apply,
    Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero, eq_comm]
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
  simp only [Math.ProbabilityMassFunction.pushforward, PMF.bind_apply, PMF.pure_apply,
    Prod.mk.injEq, mul_ite, mul_one, mul_zero, eq_comm]
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

omit [Fintype ι] in
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

omit [Fintype ι] in
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

omit [Fintype ι] in
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

theorem exists_reachActionTrace_of_runDistPure_ne_zero
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

theorem runDistPure_factor_via_localHistIndicators
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

theorem mixedJoint_stepPoint_eq_realizeBehavioralCanonical
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
end InfoModel
end GameTheory

