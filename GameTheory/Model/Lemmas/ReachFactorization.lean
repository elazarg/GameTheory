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

private theorem actionTrace_eq_of_projectActions_eq
    {ι : Type} [Nonempty ι] {M : LSM ι}
    {ha₁ ha₂ : List (JointAction M)}
    (hacts : ∀ i, GameTheory.InfoModel.projectActions i ha₁ =
      GameTheory.InfoModel.projectActions i ha₂) :
    ha₁ = ha₂ := by
  induction ha₁ generalizing ha₂ with
  | nil =>
      cases ha₂ with
      | nil => rfl
      | cons y ys =>
          have hi := hacts (Classical.arbitrary ι)
          simp [InfoModel.projectActions] at hi
  | cons x xs ih =>
      cases ha₂ with
      | nil =>
          have hi := hacts (Classical.arbitrary ι)
          simp [InfoModel.projectActions] at hi
      | cons y ys =>
          have hheadAct : ∀ i, x i = y i := by
            intro i
            have hi := hacts i
            simpa [InfoModel.projectActions] using congrArg List.head? hi
          have htailActs : ∀ i, InfoModel.projectActions i xs = InfoModel.projectActions i ys := by
            intro i
            have hi := hacts i
            simpa [InfoModel.projectActions, hheadAct i] using hi
          have htail : xs = ys := ih htailActs
          have hfun : x = y := by
            funext i
            exact hheadAct i
          simp [hfun, htail]

omit [Fintype ι] in
private theorem pushforward_append_nonzero_exists
    (μ : PMF M.State)
    (ss hs : List M.State)
    (hpush : (Math.ProbabilityMassFunction.pushforward μ
      (fun t => ss ++ [t])) hs ≠ 0) :
    ∃ t, hs = ss ++ [t] ∧ μ t ≠ 0 := by
  classical
  rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_apply] at hpush
  by_contra hnone
  push_neg at hnone
  apply hpush
  rw [ENNReal.tsum_eq_zero]
  intro t
  by_cases heq : hs = ss ++ [t]
  · have hμ : μ t = 0 := hnone t heq
    simp [PMF.pure_apply, heq, hμ]
  · simp [PMF.pure_apply, heq]

omit [Fintype ι] in
private theorem pushforward_append_apply_same
    (μ : PMF M.State)
    (ss : List M.State) (t : M.State) :
    (Math.ProbabilityMassFunction.pushforward μ
      (fun u => ss ++ [u])) (ss ++ [t]) = μ t := by
  rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_apply]
  rw [tsum_eq_single t]
  · simp [PMF.pure_apply]
  · intro u hu
    have hEq : ss ++ [t] ≠ ss ++ [u] := by
      intro hpair
      have hs := append_singleton_eq hpair
      exact hu hs.2.symm
    simp [PMF.pure_apply, hEq]

omit [Fintype ι] in
private theorem pushforward_append_apply_other
    (μ : PMF M.State)
    (ss₁ ss₂ : List M.State) (t₂ : M.State)
    (hneq : ss₁ ≠ ss₂) :
    (Math.ProbabilityMassFunction.pushforward μ
      (fun u => ss₁ ++ [u])) (ss₂ ++ [t₂]) = 0 := by
  rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_apply]
  refine (ENNReal.tsum_eq_zero).2 ?_
  intro u
  have hEq : ss₂ ++ [t₂] ≠ ss₁ ++ [u] := by
    intro hpair
    have hs := append_singleton_eq hpair.symm
    exact hneq hs.1
  simp [PMF.pure_apply, hEq]

private theorem runDistPure_succ_apply_path
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    (π : PureProfile I)
    (n : Nat) (ssPrev : List M.State) (t : M.State) :
    D.runDistPure (n + 1) π (ssPrev ++ [t]) =
      D.runDistPure n π ssPrev *
        (D.stepDist (pureToBehavioral I π) ssPrev) t := by
  rw [Execution.Dynamics.runDistPure,
    InfoModel.runDist_succ (I := I) (D := D) n (pureToBehavioral I π), PMF.bind_apply]
  rw [tsum_eq_single ssPrev]
  · rw [pushforward_append_apply_same]
    simp [Execution.Dynamics.runDistPure]
  · intro ssPrev' hne
    have hzero := pushforward_append_apply_other
      (μ := D.stepDist (pureToBehavioral I π) ssPrev')
      ssPrev' ssPrev t hne
    simp [hzero]

private theorem exists_prev_of_runDistPure_succ_ne_zero
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    (π : PureProfile I)
    (n : Nat)
    (ss : List M.State)
    (hss : D.runDistPure (n + 1) π ss ≠ 0) :
    ∃ ssPrev,
      D.runDistPure n π ssPrev ≠ 0 ∧
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (pureToBehavioral I π) ssPrev)
        (fun t => ssPrev ++ [t])) ss ≠ 0 := by
  classical
  rw [Execution.Dynamics.runDistPure,
    InfoModel.runDist_succ (I := I) (D := D) n (pureToBehavioral I π),
    PMF.bind_apply] at hss
  by_contra hnone
  push_neg at hnone
  apply hss
  rw [ENNReal.tsum_eq_zero]
  intro ssPrev
  by_cases hprev : D.runDistPure n π ssPrev = 0
  · simpa [Execution.Dynamics.runDistPure] using Or.inl hprev
  · simpa [Execution.Dynamics.runDistPure] using Or.inr (hnone ssPrev hprev)

/-- Positive mass of a pure run to a state trace determines a compatible
reachable action/state witness. -/
theorem exists_reachActionTrace_of_runDistPure_ne_zero
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    (n : Nat) (π : PureProfile I) (ss : List M.State)
    (hss : D.runDistPure n π ss ≠ 0) :
    ∃ ha : List (JointAction M),
      InfoModel.ReachActionTrace M ha ss ∧
      ∀ i, LocalHistCompatible (I := I) i (π i)
        (InfoModel.localHistTokens (I := I) i ha ss) := by
  induction n generalizing ss with
  | zero =>
      rw [Execution.Dynamics.runDistPure,
        InfoModel.runDist_zero (I := I) (D := D) (pureToBehavioral I π)] at hss
      have hmem : ss ∈ (PMF.pure [M.init] : PMF (List M.State)).support := by
        simpa [PMF.mem_support_iff] using hss
      rw [PMF.support_pure, Set.mem_singleton_iff] at hmem
      subst hmem
      refine ⟨[], InfoModel.ReachActionTrace.nil, ?_⟩
      intro _ _ htok
      cases htok
  | succ n ih =>
      obtain ⟨ssPrev, hprev, hpush⟩ :=
        exists_prev_of_runDistPure_succ_ne_zero (I := I) (D := D) π n ss hss
      obtain ⟨haPrev, hrPrev, hcompatPrev⟩ := ih ssPrev hprev
      obtain ⟨t, hEq, hstep⟩ :=
        pushforward_append_nonzero_exists
          (μ := D.stepDist (pureToBehavioral I π) ssPrev)
          ssPrev ss hpush
      subst hEq
      let s : M.State := (ssPrev.getLast?).getD M.init
      let aCur : JointAction M := fun i => π i (I.projectStates i ssPrev)
      have hstep' : D.nextState aCur s t ≠ 0 := by
        simpa [s, aCur] using (congrArg (fun ν => ν t)
          (stepDist_pure (I := I) (D := D) π ssPrev)) ▸ hstep
      have hsLast : ssPrev.getLast? = some s := by
        unfold s
        rw [List.getLast?_eq_getLast_of_ne_nil (reachActionTrace_nonempty (M := M) hrPrev)]
        simp
      have hrel : M.step aCur s t :=
        D.nextState_sound aCur s t hstep'
      refine ⟨haPrev ++ [aCur], InfoModel.ReachActionTrace.snoc hrPrev hsLast hrel, ?_⟩
      intro i
      have hLenPrev : ssPrev.length = haPrev.length + 1 :=
        InfoModel.ReachActionTrace.length_states_eq_succ_actions hrPrev
      have htoks :
          InfoModel.localHistTokens (I := I) i (haPrev ++ [aCur]) (ssPrev ++ [t]) =
            InfoModel.localHistTokens (I := I) i haPrev ssPrev ++
              [(I.projectStates i ssPrev, aCur i)] := by
        simpa using
          (InfoModel.localHistTokens_snoc (I := I) i haPrev ssPrev hLenPrev aCur t)
      rw [htoks]
      intro tok htok
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at htok
      rcases htok with htok | htok
      · exact hcompatPrev i tok htok
      · rcases htok with rfl
        rfl

private theorem runDistPure_eq_of_localHistCompatible
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    {ha : List (JointAction M)}
    {ss : List M.State}
    (hr : InfoModel.ReachActionTrace M ha ss)
    (π π' : PureProfile I)
    (hπ :
      ∀ i, LocalHistCompatible (I := I) i (π i)
        (InfoModel.localHistTokens (I := I) i ha ss))
    (hπ' :
      ∀ i, LocalHistCompatible (I := I) i (π' i)
        (InfoModel.localHistTokens (I := I) i ha ss)) :
    D.runDistPure ha.length π ss =
      D.runDistPure ha.length π' ss := by
  induction hr generalizing π π' with
  | nil =>
      simp [Execution.Dynamics.runDistPure]
  | @snoc ha ss s t a hrPrev hsLast hrel ih =>
      have hLenPrev :
          ss.length = ha.length + 1 :=
        InfoModel.ReachActionTrace.length_states_eq_succ_actions hrPrev
      have htoks :
          ∀ i,
            InfoModel.localHistTokens (I := I) i (ha ++ [a]) (ss ++ [t]) =
              InfoModel.localHistTokens (I := I) i ha ss ++
                [(I.projectStates i ss, a i)] := by
        intro i
        simpa using
          (InfoModel.localHistTokens_snoc (I := I) i ha ss hLenPrev a t)
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
          D.runDistPure ha.length π ss =
            D.runDistPure ha.length π' ss :=
        ih π π' hπPrev hπ'Prev
      have hstepEq :
          D.stepDist (pureToBehavioral I π) ss =
            D.stepDist (pureToBehavioral I π') ss := by
        let ω : I.FlatPolicy := fun k => π k.1 k.2
        let ω' : I.FlatPolicy := fun k => π' k.1 k.2
        have hnow :
            ∀ i,
              ω ⟨i, I.projectStates i ss⟩ =
                ω' ⟨i, I.projectStates i ss⟩ := by
          intro i
          simpa [ω, ω'] using (hπNow i).trans (hπ'Now i).symm
        exact InfoModel.stepDist_depends_on_current_context
          (I := I) (D := D) ω ω' ss hnow
      have hstep :
          (D.stepDist (pureToBehavioral I π) ss) t =
            (D.stepDist (pureToBehavioral I π') ss) t := by
        exact congrArg (fun ν => ν t) hstepEq
      calc
        D.runDistPure (List.length (ha ++ [a])) π (ss ++ [t])
            =
          D.runDistPure ha.length π ss *
            (D.stepDist (pureToBehavioral I π) ss) t := by
              simpa [List.length_append] using
                (runDistPure_succ_apply_path (I := I) (D := D) π ha.length ss t)
        _ =
          D.runDistPure ha.length π' ss *
            (D.stepDist (pureToBehavioral I π') ss) t := by
              rw [hprev, hstep]
        _ =
          D.runDistPure (List.length (ha ++ [a])) π' (ss ++ [t]) := by
              simpa [List.length_append] using
                (runDistPure_succ_apply_path (I := I) (D := D) π' ha.length ss t).symm

private theorem runDistPure_eq_zero_of_not_localHistCompatible
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    {ha : List (JointAction M)}
    {ss : List M.State}
    (hr : InfoModel.ReachActionTrace M ha ss)
    (π : PureProfile I)
    (hnc :
      ¬ ∀ i, LocalHistCompatible (I := I) i (π i)
        (InfoModel.localHistTokens (I := I) i ha ss)) :
    D.runDistPure ha.length π ss = 0 := by
  by_contra hne
  obtain ⟨ha', hr', hcompat'⟩ :=
    exists_reachActionTrace_of_runDistPure_ne_zero
      (I := I) (D := D) ha.length π ss hne
  have hacts :
      ∀ i, InfoModel.projectActions i ha' = InfoModel.projectActions i ha := by
    intro i
    exact actionRecall_of_projectStates_eq (I := I) hPR i hr' hr rfl
  haveI : Nonempty ι := by
    by_contra hEmpty
    apply hnc
    intro i
    exact False.elim (hEmpty ⟨i⟩)
  have htrace : ha' = ha :=
    actionTrace_eq_of_projectActions_eq hacts
  have hcompatAll :
      ∀ i, LocalHistCompatible (I := I) i (π i)
        (InfoModel.localHistTokens (I := I) i ha ss) := by
    intro i
    simpa [htrace] using hcompat' i
  exact hnc hcompatAll

/-- On a fixed reachable action/state trace, pure-run mass factors as a common
prefix mass times the product of local-history compatibility indicators. -/
theorem runDistPure_factor_via_localHistIndicators
    [DecidableEq ι]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    {ha : List (JointAction M)}
    {ss : List M.State}
    (hr : InfoModel.ReachActionTrace M ha ss)
    (π0 : PureProfile I)
    (hcompat0 :
      ∀ i, LocalHistCompatible (I := I) i (π0 i)
        (InfoModel.localHistTokens (I := I) i ha ss))
    (π : PureProfile I) :
    D.runDistPure ha.length π ss =
      D.runDistPure ha.length π0 ss *
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
      D.runDistPure ha.length π ss =
        D.runDistPure ha.length π0 ss := hrun
      _ = D.runDistPure ha.length π0 ss * 1 := by simp
      _ =
        D.runDistPure ha.length π0 ss *
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

/-- Weighted disintegration at a reachable prefix: pure-run mass factors into a
common prefix mass and a product of local compatibility indicators, while the
mixed product law factors through the iteratively conditioned local marginals. -/
theorem query_disintegration_factorization
    [DecidableEq ι]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (μ : InfoModel.MixedProfile (I := I))
    (n : Nat)
    {hs : List M.State}
    (hlen : hs.length = n + 1)
    {π0 : PureProfile I}
    {ha : List (JointAction M)}
    (hr : InfoModel.ReachActionTrace M ha hs)
    (hcompat : ∀ i, LocalHistCompatible (I := I) i (π0 i)
      (InfoModel.localHistTokens (I := I) i ha hs))
    (stepPureY : PureProfile I → ENNReal) :
    let μJ : PMF (PureProfile I) := InfoModel.mixedJoint (I := I) μ
    let hist : ∀ i, List (InfoModel.LocalHistTok (I := I) i) :=
      fun i => InfoModel.localHistTokens (I := I) i ha hs
    let μHist : InfoModel.MixedProfile (I := I) :=
      fun i => iterCondMixedLocal (I := I) i (μ i) (hist i)
    let C : ENNReal := ∑' π, μJ π * (D.runDistPure n π) hs
    ∃ traceMass compatMass : ENNReal,
      C = traceMass * compatMass ∧
      (∑' π, μJ π * ((D.runDistPure n π) hs * stepPureY π))
        = traceMass * compatMass *
            (∑' π, (InfoModel.mixedJoint (I := I) μHist) π * stepPureY π) := by
  classical
  let μJ : PMF (PureProfile I) := InfoModel.mixedJoint (I := I) μ
  let hist : ∀ i, List (InfoModel.LocalHistTok (I := I) i) :=
    fun i => InfoModel.localHistTokens (I := I) i ha hs
  let μHist : InfoModel.MixedProfile (I := I) :=
    fun i => iterCondMixedLocal (I := I) i (μ i) (hist i)
  let C : ENNReal := ∑' π, μJ π * (D.runDistPure n π) hs
  have hhaLen : ha.length = n := by
    have hreachLen := InfoModel.ReachActionTrace.length_states_eq_succ_actions hr
    exact Nat.succ.inj <| by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        hreachLen.symm.trans hlen
  let traceMass : ENNReal := (D.runDistPure n π0) hs
  let compatMass : ENNReal := ∏ i, localHistMass (I := I) i (μ i) (hist i)
  have hrun_factor :
      ∀ π : PureProfile I,
        (D.runDistPure n π) hs =
          traceMass * ∏ i, localHistIndicator (I := I) i (π i) (hist i) := by
    intro π
    dsimp [traceMass]
    calc
      (D.runDistPure n π) hs = D.runDistPure ha.length π hs := by simp [hhaLen]
      _ =
        D.runDistPure ha.length π0 hs *
          ∏ i, localHistIndicator (I := I) i (π i) (hist i) := by
            simpa [hist] using
              runDistPure_factor_via_localHistIndicators
                (I := I) (D := D) hPR hr π0 hcompat π
      _ =
        (D.runDistPure n π0) hs *
          ∏ i, localHistIndicator (I := I) i (π i) (hist i) := by
            simp [hhaLen]
  have hmixed_factor :
      ∀ π : PureProfile I,
        compatMass * (InfoModel.mixedJoint (I := I) μHist) π =
          μJ π * ∏ i, localHistIndicator (I := I) i (π i) (hist i) := by
    intro π
    simpa [compatMass, μHist, μJ] using
      localHistMass_mul_mixedJoint_iterCond_apply
        (I := I) (μ := μ) (hist := hist) π
  have hsum_indicators :
      ∑' π, μJ π * ∏ i, localHistIndicator (I := I) i (π i) (hist i) = compatMass := by
    calc
      ∑' π, μJ π * ∏ i, localHistIndicator (I := I) i (π i) (hist i)
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
          (traceMass * ∏ i, localHistIndicator (I := I) i (π i) (hist i)) := by
            refine tsum_congr ?_
            intro π
            rw [hrun_factor π]
      _ = ∑' π, traceMass *
          (μJ π * ∏ i, localHistIndicator (I := I) i (π i) (hist i)) := by
            refine tsum_congr ?_
            intro π
            ac_rfl
      _ = traceMass *
          ∑' π, μJ π * ∏ i, localHistIndicator (I := I) i (π i) (hist i) := by
            rw [ENNReal.tsum_mul_left]
      _ = traceMass * compatMass := by rw [hsum_indicators]
  · calc
      (∑' π, μJ π * ((D.runDistPure n π) hs * stepPureY π))
          =
        ∑' π, μJ π *
          ((traceMass * ∏ i, localHistIndicator (I := I) i (π i) (hist i)) *
            stepPureY π) := by
              refine tsum_congr ?_
              intro π
              rw [hrun_factor π]
      _ = ∑' π, traceMass *
          ((μJ π * ∏ i, localHistIndicator (I := I) i (π i) (hist i)) *
            stepPureY π) := by
              refine tsum_congr ?_
              intro π
              ac_rfl
      _ = traceMass *
          ∑' π, ((μJ π * ∏ i, localHistIndicator (I := I) i (π i) (hist i)) *
            stepPureY π) := by
              rw [ENNReal.tsum_mul_left]
      _ = traceMass *
          ∑' π, ((compatMass * (InfoModel.mixedJoint (I := I) μHist) π) * stepPureY π) := by
              congr 1
              refine tsum_congr ?_
              intro π
              rw [← hmixed_factor π]
      _ = traceMass *
          (compatMass * ∑' π, (InfoModel.mixedJoint (I := I) μHist) π * stepPureY π) := by
              congr 1
              calc
                ∑' π, ((compatMass * (InfoModel.mixedJoint (I := I) μHist) π) * stepPureY π)
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

private theorem mixedJoint_stepDist_eq_realizeBehavioralCanonical
    [DecidableEq ι]
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
  set s := (ss.getLast?).getD M.init
  calc
    (InfoModel.mixedJoint (I := I) μ).bind
        (fun π => D.stepDist (pureToBehavioral I π) ss)
      =
    (InfoModel.mixedJoint (I := I) μ).bind
        (fun π => D.nextState (fun i => π i (I.projectStates i ss)) s) := by
          congr 1
          funext π
          simpa [s] using (InfoModel.stepDist_pure (I := I) (D := D) π ss)
    _ =
      (InfoModel.mixedJoint (I := I) μ).bind
        (fun π =>
          (PMF.pure (fun i => π i (I.projectStates i ss))).bind
            (fun a => D.nextState a s)) := by
          congr 1
          funext π
          rw [PMF.pure_bind]
    _ =
      ((InfoModel.mixedJoint (I := I) μ).bind
        (fun π => PMF.pure (fun i => π i (I.projectStates i ss)))).bind
        (fun a => D.nextState a s) := by
          rw [PMF.bind_bind]
    _ =
      (Execution.Dynamics.jointActionDist (I := I)
        (InfoModel.realizeBehavioralCanonical (I := I) μ) ss).bind
        (fun a => D.nextState a s) := by
          have hJA :
              (InfoModel.mixedJoint (I := I) μ).bind
                (fun π => PMF.pure (fun i => π i (I.projectStates i ss))) =
              Execution.Dynamics.jointActionDist (I := I)
                (InfoModel.realizeBehavioralCanonical (I := I) μ) ss := by
            simpa [Math.ProbabilityMassFunction.pushforward, InfoModel.mixedJoint,
              Execution.Dynamics.jointActionDist, InfoModel.realizeBehavioralCanonical] using
              (Math.PMFProduct.pmfPi_push_coordwise
                (μ := μ) (g := fun i fi => fi (I.projectStates i ss)))
          rw [hJA]
    _ = D.stepDist (InfoModel.realizeBehavioralCanonical (I := I) μ) ss := by
          simp [Execution.Dynamics.stepDist, s]

/-- Pointwise one-step bridge between a mixed profile and its canonical
behavioral realization. -/
theorem mixedJoint_stepPoint_eq_realizeBehavioralCanonical
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : InfoModel.MixedProfile (I := I))
    (hs y : List M.State) :
    (∑' π, (InfoModel.mixedJoint (I := I) μ) π *
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (pureToBehavioral I π) hs)
        (fun t => hs ++ [t])) y)
      =
    (Math.ProbabilityMassFunction.pushforward
      (D.stepDist (InfoModel.realizeBehavioralCanonical (I := I) μ) hs)
      (fun t => hs ++ [t])) y := by
  have hstep :=
    mixedJoint_stepDist_eq_realizeBehavioralCanonical (I := I) (D := D) μ hs
  have hpush := congrArg
    (fun ν =>
      (Math.ProbabilityMassFunction.pushforward ν
        (fun t => hs ++ [t])) y)
    hstep
  have hpushBind :
      ((InfoModel.mixedJoint (I := I) μ).bind
        (fun π =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (pureToBehavioral I π) hs)
            (fun t => hs ++ [t]))) y
        =
      (Math.ProbabilityMassFunction.pushforward
        ((InfoModel.mixedJoint (I := I) μ).bind
          (fun π => D.stepDist (pureToBehavioral I π) hs))
        (fun t => hs ++ [t])) y := by
          simpa using congrArg (fun ν => ν y) (
            (Math.ProbabilityMassFunction.pushforward_bind
              (μ := InfoModel.mixedJoint (I := I) μ)
              (k := fun π => D.stepDist (pureToBehavioral I π) hs)
              (f := fun t => hs ++ [t])).symm)
  calc
    (∑' π, (InfoModel.mixedJoint (I := I) μ) π *
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (pureToBehavioral I π) hs)
        (fun t => hs ++ [t])) y)
        =
      ((InfoModel.mixedJoint (I := I) μ).bind
        (fun π =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (pureToBehavioral I π) hs)
            (fun t => hs ++ [t]))) y := by
              simp [PMF.bind_apply]
    _ =
      (Math.ProbabilityMassFunction.pushforward
        ((InfoModel.mixedJoint (I := I) μ).bind
          (fun π => D.stepDist (pureToBehavioral I π) hs))
        (fun t => hs ++ [t])) y := hpushBind
    _ =
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (InfoModel.realizeBehavioralCanonical (I := I) μ) hs)
        (fun t => hs ++ [t])) y := by
          simpa using hpush

end InfoModel
end GameTheory
