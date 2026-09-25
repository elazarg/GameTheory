/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Conditioning

/-! # Sequential sampling of finite transcripts

A policy samples an action list by updating its local view after each draw.
When deterministic state transitions induce exactly these view updates, sampling
the whole list in advance preserves the complete endpoint law and every later
continuation. This requires no player, protocol, or finite carrier.

Conversely, conditioning a fixed-length transcript law on its chosen prefix
realizes that law with the same sampler, preserving arbitrary correlations.
The default action makes that conditional policy total, including off-path
prefixes and exhausted transcripts.
-/

noncomputable section

namespace GameTheory.Math.Probability.SequentialSampling

universe us uv ua

variable {State : Type us} {View : Type uv} {Action : Type ua}

/-- Sample a fixed number of actions using only a local view and its updates. -/
def transcript (update : View → Action → View) (policy : View → PMF Action) :
    Nat → View → PMF (List Action)
  | 0, _ => PMF.pure []
  | count + 1, view => (policy view).bind fun action =>
      (transcript update policy count (update view action)).map (action :: ·)

theorem transcript_length (update : View → Action → View) (policy : View → PMF Action) :
    ∀ count view actions, actions ∈ (transcript update policy count view).support →
      actions.length = count := by
  intro count
  induction count with
  | zero =>
      intro view actions reached
      rw [transcript, PMF.mem_support_pure_iff] at reached
      subst actions
      rfl
  | succ count ih =>
      intro view actions reached
      rw [transcript, PMF.support_bind] at reached
      obtain ⟨action, _, reached⟩ := Set.mem_iUnion₂.mp reached
      rw [PMF.support_map] at reached
      obtain ⟨rest, supported, rfl⟩ := reached
      simp only [List.length_cons, ih _ _ supported]

private theorem iterate_bind (kernel : State → PMF State) (count : Nat)
    (law : PMF State) :
    (fun law => law.bind kernel)^[count] law =
      law.bind (fun state => (fun law => law.bind kernel)^[count] (PMF.pure state)) := by
  induction count with
  | zero => simp only [Function.iterate_zero_apply, PMF.bind_pure]
  | succ count ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, PMF.bind_bind]

/-- Sampling a transcript in advance agrees with repeated policy invocations
on states whenever no new information arrives between actions. Equality is of
the full endpoint state law, including any hidden state. -/
theorem transcript_eq_iteration (update : View → Action → View)
    (policy : View → PMF Action) (observe : State → View)
    (step : State → Action → State)
    (observe_step : ∀ state action, observe (step state action) = update (observe state) action)
    (count : Nat) (state : State) :
    (transcript update policy count (observe state)).map (fun actions => actions.foldl step state) =
      (fun law => law.bind (fun current =>
        (policy (observe current)).map (step current)))^[count] (PMF.pure state) := by
  induction count generalizing state with
  | zero => simp only [transcript, PMF.pure_map, Function.iterate_zero_apply, List.foldl_nil]
  | succ count ih =>
      rw [transcript, PMF.map_bind]
      calc
        _ = (policy (observe state)).bind (fun action =>
            (transcript update policy count (observe (step state action))).map
              (fun actions => actions.foldl step (step state action))) := by
          apply bind_congr_on_support
          intro action _
          rw [PMF.map_comp, observe_step]
          rfl
        _ = (policy (observe state)).bind (fun action =>
            (fun law => law.bind (fun current =>
              (policy (observe current)).map (step current)))^[count]
                (PMF.pure (step state action))) := by simp only [ih]
        _ = (fun law => law.bind (fun current =>
              (policy (observe current)).map (step current)))^[count]
                ((policy (observe state)).map (step state)) := by
          rw [iterate_bind, PMF.bind_map]
          rfl
        _ = _ := by rw [Function.iterate_succ_apply, PMF.pure_bind]

/-- Any subsequent kernel sees the same complete endpoint law. This assertion
does not claim preservation of intermediate decision roots. -/
theorem continuation_eq {Result : Type*} (update : View → Action → View)
    (policy : View → PMF Action) (observe : State → View)
    (step : State → Action → State)
    (observe_step : ∀ state action, observe (step state action) = update (observe state) action)
    (count : Nat) (state : State) (continuation : State → PMF Result) :
    ((transcript update policy count (observe state)).map
      (fun actions => actions.foldl step state)).bind continuation =
      ((fun law => law.bind (fun current =>
        (policy (observe current)).map (step current)))^[count]
          (PMF.pure state)).bind continuation := by
  rw [transcript_eq_iteration update policy observe step observe_step]

/-- Retaining a fixed prefix in the view is equivalent to supplying it to the
policy at every subsequent invocation. -/
theorem transcript_append (policy : List Action → PMF Action) (count : Nat)
    (initial past : List Action) :
    transcript (fun past action => past ++ [action]) policy count (initial ++ past) =
      transcript (fun past action => past ++ [action])
        (fun rest => policy (initial ++ rest)) count past := by
  induction count generalizing past with
  | zero => rfl
  | succ count ih =>
      simp only [transcript]
      apply bind_congr_on_support
      intro action _
      rw [List.append_assoc, ih]

/-- The transcript sampler specialized to full own-action recall. -/
def run (policy : List Action → PMF Action) (count : Nat) : PMF (List Action) :=
  transcript (fun past action => past ++ [action]) policy count []

@[simp] theorem run_zero (policy : List Action → PMF Action) :
    run policy 0 = PMF.pure [] := rfl

theorem run_succ (policy : List Action → PMF Action) (count : Nat) :
    run policy (count + 1) = (policy []).bind fun action =>
      (run (fun past => policy (action :: past)) count).map (action :: ·) := by
  unfold run
  rw [transcript]
  apply bind_congr_on_support
  intro action _
  have shift := transcript_append policy count [action] []
  simpa using congrArg (PMF.map (action :: ·)) shift

variable [Inhabited Action]

/-- A total continuation after observing the first action. Null prefixes use
an exhausted transcript, whose next action is the default. -/
def conditionOnHead (law : PMF (List Action)) (action : Action) :
    PMF (List Action) := by
  classical
  exact if h : action ∈ (law.map (List.headD · default)).support then
    fiberPosterior law (List.headD · default) action h
  else PMF.pure []

theorem conditionOnHead_eq_fiberPosterior (law : PMF (List Action))
    (action : Action)
    (h : action ∈ (law.map (List.headD · default)).support) :
    conditionOnHead law action =
      fiberPosterior law (List.headD · default) action h := by
  classical
  unfold conditionOnHead
  exact dite_eq_left h

private theorem conditionOnHead_reconstruct (law : PMF (List Action)) :
    (law.map (List.headD · default)).bind (conditionOnHead law) = law := by
  rw [← PMF.bindOnSupport_eq_bind]
  exact fiberPosterior_reconstruct_irrelevant law (List.headD · default)
    (fun action _ => conditionOnHead law action)
    (fun action h => conditionOnHead_eq_fiberPosterior law action h)

/-- A total conditional policy for a transcript law. Its off-path behavior is
defined by the default action. -/
def next (law : PMF (List Action)) : List Action → PMF Action
  | [] => law.map (List.headD · default)
  | action :: past =>
      next ((conditionOnHead law action).map List.tail) past

/-- Every fixed-length transcript law is realized using only past chosen
actions, including laws with infinite support. -/
theorem run_next (law : PMF (List Action)) (count : Nat)
    (lengths : ∀ actions ∈ law.support, actions.length = count) :
    run (next law) count = law := by
  induction count generalizing law with
  | zero =>
      have hsubset : law.support ⊆ ({[]} : Set (List Action)) := by
        intro actions member
        have hlength := lengths actions member
        cases actions with
        | nil => simp
        | cons action rest => simp at hlength
      exact (pmf_eq_pure_of_support_subset_singleton law [] hsubset).symm
  | succ count ih =>
      rw [run_succ]
      have hrec := conditionOnHead_reconstruct law
      conv_rhs => rw [← hrec]
      apply bind_congr_on_support
      intro action supported
      have hsupported : action ∈ (law.map (List.headD · default)).support := by
        simpa only [next] using supported
      have remaining : ∀ rest ∈
          ((conditionOnHead law action).map List.tail).support,
          rest.length = count := by
        intro rest member
        rw [PMF.support_map] at member
        obtain ⟨actions, conditioned, rfl⟩ := member
        have hcond : actions ∈
            (fiberPosterior law (List.headD · default) action hsupported).support := by
          simpa only [conditionOnHead_eq_fiberPosterior law action hsupported] using
            conditioned
        have hmem : actions ∈
            {actions | List.headD actions default = action} ∩ law.support := by
          rw [fiberPosterior_support law (List.headD · default)
            action hsupported] at hcond
          exact hcond
        have length := lengths actions hmem.2
        simp only [List.length_tail]
        omega
      have hpolicy : (fun past => next law (action :: past)) =
          next ((conditionOnHead law action).map List.tail) := rfl
      rw [hpolicy, ih _ remaining, PMF.map_comp]
      have hprefix : ∀ actions ∈ (conditionOnHead law action).support,
          action :: actions.tail = actions := by
        intro actions conditioned
        have hcond : actions ∈
            (fiberPosterior law (List.headD · default) action hsupported).support := by
          simpa only [conditionOnHead_eq_fiberPosterior law action hsupported] using
            conditioned
        have hmem : actions ∈
            {actions | List.headD actions default = action} ∩ law.support := by
          rw [fiberPosterior_support law (List.headD · default)
            action hsupported] at hcond
          exact hcond
        have length := lengths actions hmem.2
        cases actions with
        | nil => simp only [List.length_nil] at length; omega
        | cons first rest =>
            exact congrArg (· :: rest) hmem.1.symm
      calc
        (conditionOnHead law action).map (fun actions => action :: actions.tail) =
            (conditionOnHead law action).map id := by
          rw [← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
          apply bind_congr_on_support
          intro actions member
          simp [hprefix actions member]
        _ = conditionOnHead law action := PMF.map_id _

end GameTheory.Math.Probability.SequentialSampling
