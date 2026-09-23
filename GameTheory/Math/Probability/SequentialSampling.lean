/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.FinDist

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
def transcript (update : View → Action → View) (policy : View → FinDist Action) :
    Nat → View → FinDist (List Action)
  | 0, _ => FinDist.pure []
  | count + 1, view => (policy view).bind fun action =>
      (transcript update policy count (update view action)).map (action :: ·)

theorem transcript_length (update : View → Action → View) (policy : View → FinDist Action) :
    ∀ count view actions, actions ∈ (transcript update policy count view).support →
      actions.length = count := by
  intro count
  induction count with
  | zero =>
      intro view actions reached
      cases FinDist.mem_support_pure.mp reached
      rfl
  | succ count ih =>
      intro view actions reached
      rw [transcript, FinDist.support_bind] at reached
      obtain ⟨action, _, reached⟩ := Set.mem_iUnion₂.mp reached
      rw [FinDist.support_map] at reached
      obtain ⟨rest, supported, rfl⟩ := reached
      simp only [List.length_cons, ih _ _ supported]

private theorem iterate_bind (kernel : State → FinDist State) (count : Nat)
    (law : FinDist State) :
    (fun law => law.bind kernel)^[count] law =
      law.bind (fun state => (fun law => law.bind kernel)^[count] (FinDist.pure state)) := by
  induction count with
  | zero => simp only [Function.iterate_zero_apply, FinDist.bind_pure]
  | succ count ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, FinDist.bind_bind]

/-- Sampling a transcript in advance agrees with repeated policy invocations
on states whenever no new information arrives between actions. Equality is of
the full endpoint state law, including any hidden state. -/
theorem transcript_eq_iteration (update : View → Action → View)
    (policy : View → FinDist Action) (observe : State → View)
    (step : State → Action → State)
    (observe_step : ∀ state action, observe (step state action) = update (observe state) action)
    (count : Nat) (state : State) :
    (transcript update policy count (observe state)).map (fun actions => actions.foldl step state) =
      (fun law => law.bind (fun current =>
        (policy (observe current)).map (step current)))^[count] (FinDist.pure state) := by
  induction count generalizing state with
  | zero => simp only [transcript, FinDist.map_pure, Function.iterate_zero_apply, List.foldl_nil]
  | succ count ih =>
      rw [transcript, FinDist.map_bind]
      calc
        _ = (policy (observe state)).bind (fun action =>
            (transcript update policy count (observe (step state action))).map
              (fun actions => actions.foldl step (step state action))) := by
          apply FinDist.bind_congr
          intro action _
          rw [FinDist.map_comp, observe_step]
          rfl
        _ = (policy (observe state)).bind (fun action =>
            (fun law => law.bind (fun current =>
              (policy (observe current)).map (step current)))^[count]
                (FinDist.pure (step state action))) := by simp only [ih]
        _ = (fun law => law.bind (fun current =>
              (policy (observe current)).map (step current)))^[count]
                ((policy (observe state)).map (step state)) := by
          rw [iterate_bind, FinDist.bind_map]
        _ = _ := by rw [Function.iterate_succ_apply, FinDist.pure_bind]

/-- Any subsequent kernel sees the same complete endpoint law. This assertion
does not claim preservation of intermediate decision roots. -/
theorem continuation_eq {Result : Type*} (update : View → Action → View)
    (policy : View → FinDist Action) (observe : State → View)
    (step : State → Action → State)
    (observe_step : ∀ state action, observe (step state action) = update (observe state) action)
    (count : Nat) (state : State) (continuation : State → FinDist Result) :
    ((transcript update policy count (observe state)).map
      (fun actions => actions.foldl step state)).bind continuation =
      ((fun law => law.bind (fun current =>
        (policy (observe current)).map (step current)))^[count]
          (FinDist.pure state)).bind continuation := by
  rw [transcript_eq_iteration update policy observe step observe_step]

/-- Retaining a fixed prefix in the view is equivalent to supplying it to the
policy at every subsequent invocation. -/
theorem transcript_append (policy : List Action → FinDist Action) (count : Nat)
    (initial past : List Action) :
    transcript (fun past action => past ++ [action]) policy count (initial ++ past) =
      transcript (fun past action => past ++ [action])
        (fun rest => policy (initial ++ rest)) count past := by
  induction count generalizing past with
  | zero => rfl
  | succ count ih =>
      simp only [transcript]
      apply FinDist.bind_congr
      intro action _
      rw [List.append_assoc, ih]

/-- The transcript sampler specialized to full own-action recall. -/
def run (policy : List Action → FinDist Action) (count : Nat) : FinDist (List Action) :=
  transcript (fun past action => past ++ [action]) policy count []

@[simp] theorem run_zero (policy : List Action → FinDist Action) :
    run policy 0 = FinDist.pure [] := rfl

theorem run_succ (policy : List Action → FinDist Action) (count : Nat) :
    run policy (count + 1) = (policy []).bind fun action =>
      (run (fun past => policy (action :: past)) count).map (action :: ·) := by
  unfold run
  rw [transcript]
  apply FinDist.bind_congr
  intro action _
  have shift := transcript_append policy count [action] []
  simpa using congrArg (FinDist.map (action :: ·)) shift

variable [Inhabited Action]

/-- A total conditional policy for a transcript law. Null prefixes use the
law's conditioning fallback, and an empty remaining list supplies `default`. -/
def next (law : FinDist (List Action)) : List Action → FinDist Action
  | [] => law.map (List.headD · default)
  | action :: past =>
      next ((law.condOnFibre (List.headD · default) action).map List.tail) past

/-- Every fixed-length transcript law is realized using only past chosen
actions. Conditioning preserves correlations; the policy is defined even at
prefixes having zero probability. -/
theorem run_next (law : FinDist (List Action)) (count : Nat)
    (lengths : ∀ actions ∈ law.support, actions.length = count) :
    run (next law) count = law := by
  induction count generalizing law with
  | zero =>
      show FinDist.pure [] = law
      calc
        _ = law.map (fun _ => []) := (FinDist.map_const _ _).symm
        _ = law.map id := FinDist.map_congr_of_eq_on_support fun actions member => by
          have length := lengths actions member
          cases actions <;> simp_all
        _ = law := FinDist.map_id _
  | succ count ih =>
      rw [run_succ]
      show ((law.map (List.headD · default)).bind fun action =>
        (run (next ((law.condOnFibre (List.headD · default) action).map List.tail))
          count).map (action :: ·)) = law
      conv_rhs => rw [FinDist.eq_bind_condOnFibre law (List.headD · default)]
      apply FinDist.bind_congr
      intro action supported
      have remaining : ∀ rest ∈
          ((law.condOnFibre (List.headD · default) action).map List.tail).support,
          rest.length = count := by
        intro rest member
        rw [FinDist.support_map] at member
        obtain ⟨actions, conditioned, rfl⟩ := member
        have length := lengths actions (FinDist.support_condOnFibre law _ action conditioned)
        simp only [List.length_tail]
        omega
      rw [ih _ remaining, FinDist.map_comp]
      calc
        _ = (law.condOnFibre (List.headD · default) action).map id := by
          apply FinDist.map_congr_of_eq_on_support
          intro actions member
          have head := FinDist.condOnFibre_mem_fibre law
            (List.headD · default) action supported actions member
          have length := lengths actions (FinDist.support_condOnFibre law _ action member)
          cases actions with
          | nil => simp only [List.length_nil] at length; omega
          | cons first rest =>
              show action :: rest = first :: rest
              exact congrArg (· :: rest) head.symm
        _ = _ := FinDist.map_id _

end GameTheory.Math.Probability.SequentialSampling
