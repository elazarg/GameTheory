import GameTheory.Math.Probability.SequentialSampling
import GameTheory.Math.Probability.Uniform

/-! # Correlated reconstruction and no-incoming-information controls -/

noncomputable section

namespace GameTheory.Tests.SequentialSampling

open GameTheory.Math.Probability
open GameTheory.Math.Probability.SequentialSampling

private def coin : PMF Bool := PMF.uniformOfFintype Bool

private theorem coin_support (value : Bool) : value ∈ coin.support :=
  PMF.mem_support_uniformOfFintype value

private def correlated : PMF (List Bool) := coin.map fun value => [value, value]

/-- Conditioning realizes a genuinely correlated two-step law. -/
theorem correlated_reconstruction : run (next correlated) 2 = correlated := by
  apply run_next
  intro actions member
  rw [correlated, PMF.support_map] at member
  obtain ⟨value, _, rfl⟩ := member
  rfl

/-- Both constant transcripts have positive probability. -/
theorem correlated_two_branches :
    [false, false] ∈ correlated.support ∧ [true, true] ∈ correlated.support := by
  constructor <;> rw [correlated, PMF.support_map]
  · exact ⟨false, coin_support false, rfl⟩
  · exact ⟨true, coin_support true, rfl⟩

/-- Independent unconditional draws do not reconstruct the correlated law. -/
theorem independent_draws_do_not_reconstruct :
    coin.bind (fun first => coin.map (fun second => [first, second])) ≠ correlated := by
  intro equal
  have mixed : [false, true] ∈
      (coin.bind (fun first => coin.map (fun second => [first, second]))).support := by
    rw [PMF.support_bind]
    apply Set.mem_iUnion_of_mem false
    apply Set.mem_iUnion_of_mem (coin_support false)
    rw [PMF.support_map]
    exact ⟨true, coin_support true, rfl⟩
  rw [equal, correlated, PMF.support_map] at mixed
  obtain ⟨value, _, equalList⟩ := mixed
  cases value <;> simp at equalList

/-- A zero-probability prefix still has a specified total next-action law. -/
theorem off_path_prefix :
    next (PMF.pure [false, false]) [true] = PMF.pure false := by
  simp [next, conditionOnHead, PMF.pure_map]

/-- The sampler itself needs no typeclass supplying a default action. -/
theorem zero_length_without_default {Action View : Type*}
    (advance : View → Action → View) (choose : View → PMF Action) (view : View) :
    transcript advance choose 0 view = PMF.pure [] := rfl

/-- Conditional reconstruction also covers a zero-length response. -/
theorem zero_length_reconstruction :
    run (next (PMF.pure ([] : List Bool))) 0 = PMF.pure [] := by
  apply run_next
  intro actions member
  rw [PMF.mem_support_pure_iff] at member
  subst actions
  rfl

/-- Asking for another action after an exhausted response returns the default. -/
theorem exhausted_response_default :
    next (PMF.pure ([] : List Bool)) [] = PMF.pure default := by
  simp [next, PMF.pure_map]

private abbrev HiddenState := {state : ℕ × Bool // Even state.1}

private def observe (state : HiddenState) : Bool := state.1.2

private def update (_ : Bool) (action : Bool) : Bool := !action

private def step (state : HiddenState) (action : Bool) : HiddenState :=
  ⟨(state.1.1, !action), state.2⟩

private def policy (view : Bool) : PMF Bool :=
  if view then coin else PMF.pure true

private theorem observe_step (state : HiddenState) (action : Bool) :
    observe (step state action) = update (observe state) action := rfl

/-- The policy changes its law with the view, so the endpoint theorem is not
being tested solely on a constant policy. -/
theorem local_policy_nonconstant : policy false ≠ policy true := by
  intro equal
  have supported : false ∈ (policy true).support := coin_support false
  rw [← equal] at supported
  simp [policy] at supported

/-- Distinct hidden states use exactly the same transcript law. -/
theorem hidden_states_share_transcript (count : Nat) :
    transcript update policy count (observe ⟨(0, true), by simp⟩) =
      transcript update policy count (observe ⟨(2, true), by norm_num⟩) := rfl

/-- The full endpoint theorem applies on an invariant subtype and then projects
to the original state. The consumer needs no new induction on transcripts. -/
theorem hidden_endpoint_projection (count : Nat) (state : HiddenState) :
    (transcript update policy count (observe state)).map
        (fun actions => (actions.foldl step state).1) =
      ((fun law => law.bind (fun current =>
        (policy (observe current)).map (step current)))^[count]
          (PMF.pure state)).map Subtype.val := by
  rw [← transcript_eq_iteration update policy observe step observe_step]
  rw [PMF.map_comp]
  rfl

/-- Any later stochastic continuation on the hidden endpoint is preserved. -/
theorem hidden_continuation (count : Nat) (state : HiddenState)
    (later : HiddenState → PMF ℕ) :
    ((transcript update policy count (observe state)).map
        (fun actions => actions.foldl step state)).bind later =
      ((fun law => law.bind (fun current =>
        (policy (observe current)).map (step current)))^[count]
          (PMF.pure state)).bind later :=
  continuation_eq update policy observe step observe_step count state later

private def revealObserve (state : Bool × Bool × Bool) : Bool := state.2.1

private def revealStep (state : Bool × Bool × Bool) (action : Bool) : Bool × Bool × Bool :=
  (state.1, state.1, action)

/-- Revealing hidden information cannot be represented by a local update of
the old view and own action. -/
theorem incoming_information_rejects_local_update :
    ¬ ∃ localUpdate : Bool → Bool → Bool, ∀ state action,
      revealObserve (revealStep state action) = localUpdate (revealObserve state) action := by
  rintro ⟨localUpdate, agrees⟩
  have first := agrees (false, false, false) false
  have second := agrees (true, false, false) false
  exact Bool.false_ne_true (first.trans second.symm)

/-- Ignoring that incoming information actually changes the complete endpoint
law after two actions. -/
theorem incoming_information_changes_endpoint :
    (transcript (fun view (_ : Bool) => view) PMF.pure 2 false).map
        (fun actions => actions.foldl revealStep (true, false, false)) ≠
      (fun law => law.bind (fun current =>
        (PMF.pure (revealObserve current)).map (revealStep current)))^[2]
          (PMF.pure (true, false, false)) := by
  simp only [transcript, PMF.pure_bind, PMF.pure_map, List.foldl_cons,
    List.foldl_nil, Function.iterate_succ_apply, Function.iterate_zero_apply,
    revealStep, revealObserve]
  intro equal
  have supported : (true, true, false) ∈ (PMF.pure (true, true, false)).support :=
    by simp
  rw [equal, PMF.mem_support_pure_iff] at supported
  cases supported

end GameTheory.Tests.SequentialSampling
