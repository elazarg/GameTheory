/-
# Predrawing one participant

One joint draw is linear in a participant's behavioral policy. Over several
steps, an independent finite table realizes that participant's randomization
when its information states are fresh across all distinct history lengths.
Other participants retain their behavioral policies, with no recall assumption.

The existential table covers only the finite support of the supplied profile,
starting history, and horizon. It is not uniform across opponent profiles.
-/

import GameTheory.Protocol.Information

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : ExecutionProtocol ι} (M : InformationModel E)

/-- A single joint draw commutes with mixing one participant's local policy.
This does not assert a whole-run mixture law. -/
theorem behavioralJoint_update_bind {α : Type*}
    (profile : Profile M.behavioralSignature) (who : ι)
    (μ : FinDist α) (policies : α → M.BehavioralPolicy who)
    {state : E.State} (trace : E.Trace state) (hterm : ¬ E.terminal state) :
    M.behavioralJoint
        (Profile.update profile who (fun info => μ.bind (fun a => policies a info)))
        trace hterm =
      μ.bind (fun a => M.behavioralJoint (Profile.update profile who (policies a))
        trace hterm) := by
  have hupdate (replacement : M.BehavioralPolicy who) :
      (fun i => (Profile.update profile who replacement) i (M.infoOf i trace)) =
        FinDist.DependentAssignment.setOne (fun i => profile i (M.infoOf i trace))
          ⟨who, replacement (M.infoOf who trace)⟩ := by
    funext i
    by_cases hi : i = who
    · subst i
      simp
    · simp [Profile.update_of_ne, hi]
  simp only [behavioralJoint, hupdate]
  rw [FinDist.pi_update_bind, FinDist.map_bind]

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
    (hfinite : ∀ info, info ∉ sites → policy info = FinDist.pure (fallback info)) :
    ((policy.toMixedOn sites fallback).bind fun purePolicy =>
      M.runBehavioralFrom (Profile.update profile who purePolicy.toBehavioral) fuel start) =
      M.runBehavioralFrom (Profile.update profile who policy) fuel start := by
  induction fuel generalizing policy sites fallback start with
  | zero => exact FinDist.bind_const _ _
  | succ fuel ih =>
    by_cases hterm : E.terminal start.state
    · simp only [M.runBehavioralFrom_of_terminal _ _ hterm]
      exact FinDist.bind_const _ _
    · let info := M.infoOf who start.trace
      let restLaw := policy.toMixedOn (sites.erase info) fallback
      let assemble : M.Choice who info → M.Policy who → M.Policy who := fun choice rest =>
        FinDist.DependentAssignment.setOne rest ⟨info, choice⟩
      let committed := fun choice => policy.commit info choice
      let joint := fun choice =>
        M.behavioralJoint (Profile.update profile who (committed choice)) start.trace hterm
      have hhere (choice : M.Choice who info) (rest : M.Policy who) :
          M.behavioralJoint
              (Profile.update profile who (assemble choice rest).toBehavioral)
              start.trace hterm = joint choice := by
        apply M.behavioralJoint_congr
        intro i
        by_cases hi : i = who
        · subst i
          simp [assemble, committed, info, Policy.toBehavioral]
        · simp [Profile.update_of_ne, hi]
      have hcontinuation (choice : M.Choice who info)
          (draw : { joint : ∀ i, Option (E.Action i) // E.Legal start.state joint })
          (target : E.State) (realized : target ∈ (E.step start.state draw).support) :
          restLaw.bind (fun rest =>
            M.runBehavioralFrom
              (Profile.update profile who (assemble choice rest).toBehavioral)
              fuel (start.extend draw.2 realized)) =
            M.runBehavioralFrom (Profile.update profile who policy)
              fuel (start.extend draw.2 realized) := by
        have htable := M.toMixedOn_commit_erase policy sites fallback info choice
        have hind := ih (committed choice) (sites.erase info)
          (assemble choice fallback) (start.extend draw.2 realized)
          (M.commit_finiteSupport policy sites fallback hfinite info choice)
        rw [← htable, FinDist.bind_map] at hind
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
          simp [committed, info, FinDist.bind_pure]
        · simp [Profile.update_of_ne, hi]
      rw [M.toMixedOn_factor policy sites fallback hfinite info,
        FinDist.bind_map, FinDist.product, FinDist.bind_bind,
        M.runBehavioralFrom_succ_of_not_terminal _ fuel hterm, hdraw,
        FinDist.bind_bind]
      apply FinDist.bind_congr
      intro choice _
      rw [FinDist.bind_map]
      dsimp only [assemble] at hhere
      simp only [M.runBehavioralFrom_succ_of_not_terminal _ fuel hterm, hhere]
      rw [FinDist.bind_comm restLaw (joint choice)]
      apply FinDist.bind_congr
      intro draw _
      rw [FinDist.bind_bindOnSupport_comm]
      exact FinDist.bindOnSupport_congr fun target realized =>
        hcontinuation choice draw target realized

/-- A finite run admits a finite law over one participant's total pure policies.
The witness can depend on the whole profile, starting history, and horizon.
Neither information states nor action carriers need be finite. -/
theorem exists_predrawOne (who : ι)
    (hfresh : ∀ first later : E.History,
      first.trace.length < later.trace.length →
        M.infoOf who later.trace ≠ M.infoOf who first.trace)
    (profile : Profile M.behavioralSignature) (fuel : Nat) (start : E.History) :
    ∃ policies : FinDist (M.Policy who),
      (policies.bind fun policy =>
        M.runBehavioralFrom (Profile.update profile who policy.toBehavioral) fuel start) =
        M.runBehavioralFrom profile fuel start := by
  classical
  let sites := M.behavioralSupportSitesFrom profile fuel start who
  let fallback := (profile who).supportFallback
  let finitePolicy := BehavioralPolicy.restrictRandomization M (profile who) sites fallback
  refine ⟨finitePolicy.toMixedOn sites fallback, ?_⟩
  have hfinite : ∀ info, info ∉ sites →
      finitePolicy info = FinDist.pure (fallback info) := by
    intro info hinfo
    simp [finitePolicy, BehavioralPolicy.restrictRandomization, hinfo]
  rw [M.runBehavioralFrom_predrawOneOn who hfresh profile fuel finitePolicy
    sites fallback start hfinite]
  symm
  apply M.runBehavioralFrom_congr_on_support
  intro elapsed helapsed later hlater _ i
  by_cases hi : i = who
  · subst i
    have hmem := M.mem_behavioralSupportSitesFrom profile fuel elapsed helapsed
      start later hlater who
    simp [finitePolicy, sites, BehavioralPolicy.restrictRandomization, hmem]
  · simp [Profile.update_of_ne, hi]

end GameTheory.Protocol.InformationModel
