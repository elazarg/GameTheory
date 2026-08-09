/-
# Chance-rooted Zermelo integration witness

Nature first selects a live branch or a terminal branch with equal positive
probability. On the live branch, immediate exit pays `5`, while continuing
reaches a second decision where reward pays `1` and punishment pays `0`.
Backward induction must therefore prescribe exit on path and reward at the
consequential off-path decision. The test exercises chance, global contingent
plans, perfect-information separation, and the public EFG existence theorem.
-/

import GameTheory.Languages.EFG.Zermelo

noncomputable section

namespace GameTheory.Tests.EFGZermelo

open GameTheory.Languages GameTheory.Protocol GameTheory.Probability
open GameTheory.Protocol.ExecutionProtocol

inductive State
  | chance | left | second | right | exited | lnone | lpunish | lreward
  | punished | rewarded | snone | sexit | scontinue
  deriving DecidableEq, Fintype

inductive Action | exit | continue | punish | reward deriving DecidableEq, Fintype

def fairCoin : FinDist State := FinDist.mix (1 / 2) (by norm_num) (by norm_num)
  (FinDist.pure .left) (FinDist.pure .right)

theorem fairCoin_support (s : State) : s ∈ fairCoin.support ↔
    s = .left ∨ s = .right := by
  rw [← FinDist.prob_pos_iff]
  cases s <;> simp [fairCoin, FinDist.prob_mix, FinDist.prob_pure_eq_ite]
  all_goals norm_num

def next : State → Option Action → State
  | .left, none => .lnone
  | .left, some .exit => .exited
  | .left, some .continue => .second
  | .left, some .punish => .lpunish
  | .left, some .reward => .lreward
  | .second, none => .snone
  | .second, some .exit => .sexit
  | .second, some .continue => .scontinue
  | .second, some .punish => .punished
  | .second, some .reward => .rewarded
  | state, _ => state

@[reducible] def execution : ExecutionProtocol Unit where
  State := State
  Action _ := Action
  init := .chance
  active s _ := s = .left ∨ s = .second
  available s _ := match s with
    | .left => {Action.exit, .continue}
    | .second => {Action.punish, .reward}
    | _ => Set.univ
  terminal
    | .chance | .left | .second => False
    | _ => True
  step s joint := match s with
    | .chance => fairCoin
    | state => FinDist.pure (next state (joint.1 ()))
  progress := by
    intro s ht
    cases s <;> simp_all
    · exact ⟨fun _ => none, fun _ => by simp⟩
    · exact ⟨fun _ => some .exit, fun _ => by simp⟩
    · exact ⟨fun _ => some .punish, fun _ => by simp⟩

theorem chance_not_terminal : ¬ execution.terminal .chance := by simp

theorem init_not_mem_step (s : State) (j : Unit → Option Action)
    (hj : execution.Legal s j) : State.chance ∉ (execution.step s ⟨j, hj⟩).support := by
  cases s with
  | chance =>
      intro hmem
      exact (fairCoin_support .chance).mp hmem |>.elim (by simp) (by simp)
  | left =>
      cases hc : j () with
      | none => simp [execution, next, hc]
      | some action => cases action <;> simp [execution, next, hc]
  | second =>
      cases hc : j () with
      | none => simp [execution, next, hc]
      | some action => cases action <;> simp [execution, next, hc]
  | right | exited | lnone | lpunish | lreward | punished | rewarded |
      snone | sexit | scontinue => exact False.elim (hj.1 True.intro)

def sourceOf : State → Option State
  | .chance => none
  | .left | .right => some .chance
  | .second | .exited | .lnone | .lpunish | .lreward => some .left
  | .punished | .rewarded | .snone | .sexit | .scontinue => some .second

theorem sourceOf_mem_step {t s : State} {j : Unit → Option Action}
    (hj : execution.Legal s j)
    (hr : t ∈ (execution.step s ⟨j, hj⟩).support) :
    sourceOf t = some s := by
  cases s with
  | chance =>
      rw [fairCoin_support] at hr
      rcases hr with rfl | rfl <;> rfl
  | left =>
      have ht : t = next .left (j ()) := by
        simpa [execution] using hr
      subst t
      cases hc : j () with
      | none => simp [next, sourceOf]
      | some action => cases action <;> simp [next, sourceOf]
  | second =>
      have ht : t = next .second (j ()) := by
        simpa [execution] using hr
      subst t
      cases hc : j () with
      | none => simp [next, sourceOf]
      | some action => cases action <;> simp [next, sourceOf]
  | right | exited | lnone | lpunish | lreward | punished | rewarded |
      snone | sexit | scontinue => exact False.elim (hj.1 True.intro)

theorem next_left_injective : Function.Injective (next .left) := by
  intro first second heq
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some second => cases second <;> simp [next] at heq
  | some first =>
      cases second with
      | none => cases first <;> simp [next] at heq
      | some second =>
          cases first <;> cases second <;> simp [next] at heq ⊢

theorem next_second_injective : Function.Injective (next .second) := by
  intro first second heq
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some second => cases second <;> simp [next] at heq
  | some first =>
      cases second with
      | none => cases first <;> simp [next] at heq
      | some second =>
          cases first <;> cases second <;> simp [next] at heq ⊢

theorem predecessor_unique {t s₁ s₂ : State} {j₁ j₂ : Unit → Option Action}
    (h₁ : execution.Legal s₁ j₁) (h₂ : execution.Legal s₂ j₂)
    (r₁ : t ∈ (execution.step s₁ ⟨j₁, h₁⟩).support)
    (r₂ : t ∈ (execution.step s₂ ⟨j₂, h₂⟩).support) : s₁ = s₂ ∧ j₁ = j₂ := by
  have hs : s₁ = s₂ := Option.some.inj
    ((sourceOf_mem_step h₁ r₁).symm.trans (sourceOf_mem_step h₂ r₂))
  subst s₂
  refine ⟨rfl, ?_⟩
  cases s₁ with
  | chance =>
      have firstNoop := execution.eq_noop_of_legal_of_inactive h₁ (by simp)
      have secondNoop := execution.eq_noop_of_legal_of_inactive h₂ (by simp)
      exact firstNoop.trans secondNoop.symm
  | left =>
      have hr₁ : t = next .left (j₁ ()) := by
        simpa [execution] using r₁
      have hr₂ : t = next .left (j₂ ()) := by
        simpa [execution] using r₂
      have hjoint := next_left_injective (hr₁.symm.trans hr₂)
      funext who
      cases who
      exact hjoint
  | second =>
      have hr₁ : t = next .second (j₁ ()) := by
        simpa [execution] using r₁
      have hr₂ : t = next .second (j₂ ()) := by
        simpa [execution] using r₂
      have hjoint := next_second_injective (hr₁.symm.trans hr₂)
      funext who
      cases who
      exact hjoint
  | right | exited | lnone | lpunish | lreward | punished | rewarded |
      snone | sexit | scontinue => exact False.elim (h₁.1 True.intro)

theorem treeShaped : execution.IsTreeShaped :=
  execution.isTreeShaped_of_predecessor_unique init_not_mem_step predecessor_unique

theorem singleMover (s : State) {a b : Unit} (_ : execution.active s a)
    (_ : execution.active s b) : a = b := by cases a; cases b; rfl

@[reducible] def signals : InfoSignals execution where
  PublicSignal := State
  PrivateSignal _ := Unit
  initialPublic := .chance
  initialPrivate _ := ()
  publicSignal e := e.target
  privateSignal _ _ := ()
  InfoState _ := State
  initInfo _ _ x := x
  pushInfo _ _ _ _ x := x

theorem infoOf_state : ∀ {s : State} (tr : execution.Trace s), signals.infoOf () tr = s
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def menu : State → Set (Option Action)
  | .left => {some .exit, some .continue}
  | .second => {some .punish, some .reward}
  | _ => {none}

@[reducible] def information : InformationModel execution where
  toInfoSignals := signals
  menu _ := menu
  menu_adequate := by
    intro _ s tr c
    rw [infoOf_state]
    cases s <;> cases c <;> simp [menu, LegalOption]

@[reducible] def game : Languages.EFG.Game Unit where
  execution := execution
  information := information
  treeShaped := treeShaped
  singleMover := singleMover

instance (i : information.InfoState ()) : Finite (information.Choice () i) := by
  dsimp [InformationModel.Choice]; infer_instance

instance (i : information.InfoState ()) : Nonempty (information.Choice () i) := by
  cases i with
  | left => exact ⟨⟨some .exit, by simp [menu]⟩⟩
  | second => exact ⟨⟨some .punish, by simp [menu]⟩⟩
  | chance | right | exited | lnone | lpunish | lreward | punished | rewarded |
      snone | sexit | scontinue => exact ⟨⟨none, by simp [menu]⟩⟩

def rank : State → ℕ
  | .chance => 3 | .left => 2 | .second => 1 | _ => 0

theorem rank_decreases (s t : State) (h : execution.Successor t s) : rank t < rank s := by
  rcases h with ⟨j, hj, hr⟩
  cases s with
  | chance =>
      rw [fairCoin_support] at hr
      rcases hr with rfl | rfl <;> decide
  | left =>
      have ht : t = next .left (j ()) := by
        simpa [execution] using hr
      subst t
      cases hc : j () with
      | none => simp [next, rank]
      | some action => cases action <;> simp [next, rank]
  | second =>
      have ht : t = next .second (j ()) := by
        simpa [execution] using hr
      subst t
      cases hc : j () with
      | none => simp [next, rank]
      | some action => cases action <;> simp [next, rank]
  | right | exited | lnone | lpunish | lreward | punished | rewarded |
      snone | sexit | scontinue => exact False.elim (hj.1 True.intro)

theorem wellFoundedPlay : execution.WellFoundedPlay :=
  wellFoundedPlay_of_rank rank rank_decreases

theorem perfect : game.HasPerfectInformation := by
  intro who first second _ _ _ _ hi
  cases who
  have hs : first.state = second.state := by simpa [infoOf_state] using hi
  cases first with
  | mk s tr =>
    cases second with
    | mk t tr' =>
      dsimp at hs
      subst t
      exact congrArg (fun trace => ExecutionProtocol.History.mk s trace)
        ((treeShaped s).elim tr tr')

/-- Nonconstant terminal utility makes exit optimal at the first decision and
reward strictly better than punishment at the resulting off-path decision. -/
def utility (h : game.History) (_ : Unit) : ℝ := match h.state with
  | .exited => 5 | .rewarded => 1 | _ => 0

/-- The public EFG surface constructs a pure SPE on the hostile witness. -/
theorem exists_subgamePerfect : ∃ p : Profile game.strategicSignature,
    game.IsSubgamePerfect wellFoundedPlay p utility :=
  game.exists_isSubgamePerfect wellFoundedPlay perfect utility

end GameTheory.Tests.EFGZermelo
