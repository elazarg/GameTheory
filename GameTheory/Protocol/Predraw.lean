/-
# Predrawing one participant

One joint draw is linear in a participant's behavioral policy. Over several
steps, an independent finite table realizes that participant's randomization
when its information states are fresh across all distinct history lengths.
Other participants retain their behavioral policies, with no recall assumption.

The existential table covers a finite set of reachable information sites for
the supplied profile, starting history, and horizon. Its policy law may have
infinite support, and its witness is not uniform across opponent profiles.
-/

import GameTheory.Protocol.Information
import GameTheory.Protocol.PolicyRandomization
import GameTheory.Math.Probability.FiniteSampling

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : ExecutionProtocol ι} (M : InformationModel E)

/-- A single joint draw commutes with mixing one participant's local policy.
This does not assert a whole-run mixture law. -/
theorem behavioralJoint_update_bind {α : Type*}
    (profile : Profile M.behavioralSignature) (who : ι)
    (μ : PMF α) (policies : α → M.BehavioralPolicy who)
    {state : E.State} (trace : E.Trace state) (hterm : ¬ E.terminal state) :
    M.behavioralJoint
        (Profile.update profile who (fun info => μ.bind (fun a => policies a info)))
        trace hterm =
      μ.bind (fun a => M.behavioralJoint (Profile.update profile who (policies a))
        trace hterm) := by
  let info := fun i => M.infoOf i trace
  let jointOf : (∀ i, M.Choice i (info i)) →
      { joint : ∀ i, Option (E.Action i) // E.Legal state joint } := fun draw =>
    ⟨fun i => (draw i).1,
      ExecutionProtocol.legal_of_legalOption hterm fun i =>
        (M.menu_adequate i trace (draw i).1).mp (draw i).2⟩
  let mixed : ∀ i, PMF (M.Choice i (info i)) := fun i =>
    (Profile.update profile who (fun state =>
      μ.bind fun a => policies a state)) i (info i)
  have hmixed : mixed who = μ.bind fun a => policies a (info who) := by
    simp [mixed]
  have hproduct : independentProduct mixed =
      μ.bind fun a => independentProduct (fun i =>
        (Profile.update profile who (policies a)) i (info i)) := by
    rw [independentProduct_splitAt mixed who, hmixed, PMF.bind_bind]
    apply bind_congr_on_support
    intro a _
    symm
    rw [independentProduct_splitAt, Profile.update_same]
    have htail :
        (fun i : {i : ι // i ≠ who} =>
          (Profile.update profile who (policies a)) i.1 (info i.1)) =
        (fun i : {i : ι // i ≠ who} => mixed i.1) := by
      funext i
      simp [mixed, Profile.update_of_ne, i.2]
    rw [htail]
  calc
    M.behavioralJoint
        (Profile.update profile who (fun state =>
          μ.bind fun a => policies a state)) trace hterm =
      PMF.map jointOf (independentProduct mixed) := rfl
    _ = μ.bind (fun a => PMF.map jointOf
        (independentProduct (fun i =>
          (Profile.update profile who (policies a)) i (info i)))) := by
      rw [hproduct, PMF.map_bind]
    _ = μ.bind (fun a =>
        M.behavioralJoint (Profile.update profile who (policies a)) trace hterm) := rfl

/-- Predrawing one finite table preserves the complete history law. Freshness
ranges over all histories of different lengths, including unrelated and
inactive histories; it is sufficient and is not identified with perfect recall.
Outside the table the supplied policy must already equal the fallback law. -/
theorem runBehavioralFrom_predrawOneOn
    (who : ι) [DecidableEq (M.InfoState who)]
    (hfresh : ∀ first later : E.History,
      first.trace.length < later.trace.length →
        M.infoOf who later.trace ≠ M.infoOf who first.trace)
    (profile : Profile M.behavioralSignature)
    (fuel : Nat) (policy : M.BehavioralPolicy who)
    (sites : Finset (M.InfoState who)) (fallback : M.Policy who)
    (start : E.History)
    (hfinite : ∀ info, info ∉ sites → policy info = PMF.pure (fallback info)) :
    ((policy.toMixedOn sites fallback).bind fun purePolicy =>
      M.runBehavioralFrom (Profile.update profile who purePolicy.toBehavioral) fuel start) =
      M.runBehavioralFrom (Profile.update profile who policy) fuel start := by
  induction fuel generalizing policy sites fallback start with
  | zero => exact PMF.bind_const _ _
  | succ fuel ih =>
    by_cases hterm : E.terminal start.state
    · simp only [M.runBehavioralFrom_of_terminal _ _ hterm]
      exact PMF.bind_const _ _
    · let info := M.infoOf who start.trace
      let committed := fun choice => policy.commit info choice
      let joint := fun choice =>
        M.behavioralJoint (Profile.update profile who (committed choice)) start.trace hterm
      have hchoiceAt (choice : M.Choice who info)
          (hchoice : choice ∈ (policy info).support)
          (purePolicy : M.Policy who)
          (hpure : purePolicy ∈ ((committed choice).toMixedOn sites fallback).support) :
          purePolicy info = choice := by
        by_cases hmem : info ∈ sites
        · have hmap : purePolicy info ∈
              (((committed choice).toMixedOn sites fallback).map
                (fun p => p info)).support :=
            (PMF.mem_support_map_iff (fun p => p info)
              ((committed choice).toMixedOn sites fallback) (purePolicy info)).2
                ⟨purePolicy, hpure, rfl⟩
          rw [BehavioralPolicy.toMixedOn,
            FiniteAssignment.sampleOn_map_eval_of_mem _ _ _ hmem,
            show committed choice info = PMF.pure choice from
              policy.commit_self info choice,
            PMF.mem_support_pure_iff] at hmap
          exact hmap
        · have hmap : purePolicy info ∈
              (((committed choice).toMixedOn sites fallback).map
                (fun p => p info)).support :=
            (PMF.mem_support_map_iff (fun p => p info)
              ((committed choice).toMixedOn sites fallback) (purePolicy info)).2
                ⟨purePolicy, hpure, rfl⟩
          rw [BehavioralPolicy.toMixedOn,
            FiniteAssignment.sampleOn_map_eval_of_not_mem _ _ _ hmem,
            PMF.mem_support_pure_iff] at hmap
          have hpolicy := hfinite info hmem
          rw [hpolicy, PMF.mem_support_pure_iff] at hchoice
          exact hmap.trans hchoice.symm
      have hhere (choice : M.Choice who info)
          (hchoice : choice ∈ (policy info).support)
          (purePolicy : M.Policy who)
          (hpure : purePolicy ∈ ((committed choice).toMixedOn sites fallback).support) :
          M.behavioralJoint
              (Profile.update profile who purePolicy.toBehavioral)
              start.trace hterm = joint choice := by
        apply M.behavioralJoint_congr
        intro i
        by_cases hi : i = who
        · subst i
          simp [committed, info, Policy.toBehavioral, hchoiceAt choice hchoice purePolicy hpure]
        · simp [Profile.update_of_ne, hi]
      have hcontinuation (choice : M.Choice who info)
          (hchoice : choice ∈ (policy info).support)
          (draw : { joint : ∀ i, Option (E.Action i) // E.Legal start.state joint })
          (target : E.State) (realized : target ∈ (E.step start.state draw).support) :
          ((committed choice).toMixedOn sites fallback).bind (fun purePolicy =>
            M.runBehavioralFrom
              (Profile.update profile who purePolicy.toBehavioral)
              fuel (start.extend draw.2 realized)) =
            M.runBehavioralFrom (Profile.update profile who policy)
              fuel (start.extend draw.2 realized) := by
        have hfiniteCommit : ∀ other, other ∉ sites →
            committed choice other = PMF.pure (fallback other) := by
          intro other hnot
          by_cases hsame : other = info
          · subst other
            have heq : choice = fallback info := by
              rw [hfinite info hnot, PMF.mem_support_pure_iff] at hchoice
              exact hchoice
            simp [committed, heq]
          · simpa [committed, BehavioralPolicy.commit_of_ne _ _ _ hsame] using
              hfinite other hnot
        have hind := ih (committed choice) sites fallback
          (start.extend draw.2 realized) hfiniteCommit
        refine hind.trans ?_
        apply M.runBehavioralFrom_congr
        intro later hreach _ i
        by_cases hi : i = who
        · subst i
          simp only [Profile.update_same]
          apply BehavioralPolicy.commit_of_ne
          apply hfresh start later
          have hlength := hreach.trace_length_le
          simp only [ExecutionProtocol.History.extend, ExecutionProtocol.Trace.length] at hlength
          omega
        · simp [Profile.update_of_ne, hi]
      have hdraw : M.behavioralJoint (Profile.update profile who policy) start.trace hterm =
          (policy info).bind joint := by
        rw [← M.behavioralJoint_update_bind profile who (policy info) committed]
        apply M.behavioralJoint_congr
        intro i
        by_cases hi : i = who
        · subst i
          simp [committed, info, PMF.bind_pure]
        · simp [Profile.update_of_ne, hi]
      rw [(policy.toMixedOn_factor M sites fallback hfinite info),
        PMF.bind_bind,
        M.runBehavioralFrom_succ_of_not_terminal _ fuel hterm, hdraw,
        PMF.bind_bind]
      apply bind_congr_on_support
      intro choice hchoice
      simp only [M.runBehavioralFrom_succ_of_not_terminal _ fuel hterm]
      apply (bind_congr_on_support _ fun purePolicy hpure => by
        rw [hhere choice hchoice purePolicy hpure]).trans
      rw [PMF.bind_comm ((committed choice).toMixedOn sites fallback) (joint choice)]
      apply bind_congr_on_support
      intro draw _
      rw [bind_bindOnSupport_comm]
      exact bindOnSupport_congr _ fun target realized =>
        hcontinuation choice hchoice draw target realized

omit [DecidableEq ι] in
/-- Finite local choice supports and finite transition supports keep each
bounded behavioral history law finitely supported, even when the state and
information carriers are infinite. -/
theorem runBehavioralFrom_support_finite_of_finite_branching
    (profile : Profile M.behavioralSignature) (fuel : ℕ) (start : E.History)
    (hchoices : ∀ history : E.History, ¬ E.terminal history.state → ∀ i,
      (profile i (M.infoOf i history.trace)).support.Finite)
    (hsteps : ∀ {state : E.State}
      (draw : { joint : ∀ i, Option (E.Action i) // E.Legal state joint }),
      (E.step state draw).support.Finite) :
    (M.runBehavioralFrom profile fuel start).support.Finite := by
  induction fuel generalizing start with
  | zero =>
    simpa only [InformationModel.runBehavioralFrom,
      ExecutionProtocol.runRandomizedFor_zero, PMF.support_pure] using
      Set.finite_singleton start
  | succ fuel ih =>
    by_cases hterm : E.terminal start.state
    · rw [M.runBehavioralFrom_of_terminal _ _ hterm]
      simpa only [PMF.support_pure] using Set.finite_singleton start
    · rw [M.runBehavioralFrom_succ_of_not_terminal _ fuel hterm,
        PMF.support_bind]
      have hjoint :
          (M.behavioralJoint profile start.trace hterm).support.Finite := by
        have hdraws :
            (independentProduct (fun i => profile i (M.infoOf i start.trace))).support.Finite :=
          (Set.Finite.pi' fun i => hchoices start (fun h => hterm h) i).subset
            (fun draws hdraws =>
              (independentProduct_support_iff _ draws).1 hdraws)
        unfold InformationModel.behavioralJoint
        rw [PMF.support_map]
        exact hdraws.image _
      apply hjoint.biUnion
      intro draw hdraw
      rw [PMF.support_bindOnSupport]
      apply (hsteps draw).biUnion'
      intro target htarget
      exact ih (start.extend draw.2 htarget)

omit [DecidableEq ι] in
/-- Finite branching along the bounded run yields a finite cover for the
single-participant table construction. -/
theorem behavioralSupportSitesFrom_finite_of_finite_branching
    (profile : Profile M.behavioralSignature) (fuel : ℕ) (start : E.History)
    (hchoices : ∀ history : E.History, ¬ E.terminal history.state → ∀ i,
      (profile i (M.infoOf i history.trace)).support.Finite)
    (hsteps : ∀ {state : E.State}
      (draw : { joint : ∀ i, Option (E.Action i) // E.Legal state joint }),
      (E.step state draw).support.Finite) (i : ι) :
    (M.behavioralSupportSitesFrom profile fuel start i).Finite := by
  have hrun (elapsed : ℕ) (hbound : elapsed ≤ fuel) :
      (M.runBehavioralFrom profile elapsed start).support.Finite :=
    M.runBehavioralFrom_support_finite_of_finite_branching profile elapsed start
      hchoices hsteps
  have hunion :
      (⋃ elapsed ∈ Set.Iic fuel,
        (M.runBehavioralFrom profile elapsed start).support.image
          (fun history => M.infoOf i history.trace)).Finite := by
    apply (Set.finite_Iic fuel).biUnion
    intro elapsed hbound
    exact (hrun elapsed (Set.mem_Iic.mp hbound)).image _
  apply hunion.subset
  intro info hinfo
  rcases hinfo with ⟨elapsed, hbound, history, hhistory, hterm, hinfo⟩
  exact Set.mem_iUnion₂.mpr ⟨elapsed, Set.mem_Iic.mpr hbound,
    ⟨history, hhistory, hinfo⟩⟩

/-- A finite reachable-site cover yields a PMF over one participant's total
pure policies by sampling those sites. The PMF itself may have infinite support.
The witness can depend on the whole profile, starting history, and horizon. -/
theorem exists_predrawOne (who : ι)
    (hfresh : ∀ first later : E.History,
      first.trace.length < later.trace.length →
        M.infoOf who later.trace ≠ M.infoOf who first.trace)
    (profile : Profile M.behavioralSignature) (fuel : Nat) (start : E.History)
    (hsitesFinite :
      (M.behavioralSupportSitesFrom profile fuel start who).Finite) :
    ∃ policies : PMF (M.Policy who),
      (policies.bind fun policy =>
        M.runBehavioralFrom (Profile.update profile who policy.toBehavioral) fuel start) =
        M.runBehavioralFrom profile fuel start := by
  classical
  let sites := hsitesFinite.toFinset
  let fallback := (profile who).supportFallback
  let finitePolicy := BehavioralPolicy.restrictRandomization M (profile who) sites fallback
  refine ⟨finitePolicy.toMixedOn sites fallback, ?_⟩
  have hfinite : ∀ info, info ∉ sites →
      finitePolicy info = PMF.pure (fallback info) := by
    intro info hinfo
    simp [finitePolicy, BehavioralPolicy.restrictRandomization, hinfo]
  rw [M.runBehavioralFrom_predrawOneOn who hfresh profile fuel finitePolicy
    sites fallback start hfinite]
  symm
  apply M.runBehavioralFrom_congr_on_support
  intro elapsed helapsed later hlater hactive i
  by_cases hi : i = who
  · subst i
    have hmem := M.mem_behavioralSupportSitesFrom profile fuel elapsed helapsed
      start later hlater hactive who
    simp [finitePolicy, sites, BehavioralPolicy.restrictRandomization,
      (Set.Finite.mem_toFinset hsitesFinite).2 hmem]
  · simp [Profile.update_of_ne, hi]

end GameTheory.Protocol.InformationModel
