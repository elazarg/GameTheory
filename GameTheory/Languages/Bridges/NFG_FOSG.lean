/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.NFG.Syntax
import GameTheory.Languages.NFG.Compile
import GameTheory.Languages.FOSG.Compile

/-!
# NFG → FOSG: one-shot embedding

Embeds any finite normal-form game into a one-step factored-observation
stochastic game.  The FOSG has two world states (initial and terminal), every
player active at the initial state, no observations, and a single deterministic
transition whose reward is the NFG payoff.

## Definitions
- `NFG.NFGGame.toFOSG` — the one-shot FOSG presentation of an NFG.
- `NFG.NFGGame.toFOSG_boundedHorizon` — bounded horizon at depth 1.

## Theorems
- `NFG.NFGGame.toFOSG_terminal_iff` — terminal states are exactly `true`.
- `NFG.NFGGame.toFOSG_active_init` — every player is active initially.
- `NFG.NFGGame.toFOSG_udist_eq` — the bounded-horizon kernel game of the one-shot
  FOSG, played by lifted pure strategies, has the same joint utility
  distribution as the NFG payoff.
- `NFG.NFGGame.toFOSG_morphism` — NFG → FOSG soundness packaged as a
  `KernelGame.Morphism` from the NFG kernel game to the one-shot FOSG kernel game.
-/

namespace NFG

open GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type}
variable [∀ i, Nonempty (A i)]

namespace NFGGame

/-- Extract a pure NFG profile from a legal joint action at the initial
state.  Every player is active there, so every component is `some`; we
fall back to `Classical.arbitrary` on the unreachable `none` branch. -/
noncomputable def actionsOfJoint (a : JointAction A) : ∀ i, A i :=
  fun i =>
    match a i with
    | some ai => ai
    | none => Classical.arbitrary _

/-- One-shot FOSG presentation of a normal-form game.

States are `Bool`: `false` is the initial state (every player active);
`true` is the unique terminal state.  The single transition is deterministic
and lands in `true`; its reward is the NFG payoff under the joint action.
Observations are trivial (`PUnit`). -/
noncomputable def toFOSG (G : NFGGame ι A) :
    FOSG ι Bool A (fun _ => PUnit) PUnit where
  init := false
  active := fun w => if w then ∅ else Finset.univ
  availableActions := fun w _ => if w then ∅ else Set.univ
  terminal := fun w => w = true
  transition := fun _ _ => PMF.pure true
  reward := fun _ a _ i => G.utility (G.outcome (actionsOfJoint a.1)) i
  privObs := fun _ _ _ _ => PUnit.unit
  pubObs := fun _ _ _ => PUnit.unit
  terminal_active_eq_empty := fun {w} hw => by
    subst hw
    simp
  terminal_no_legal := fun {w} {a} hw hlegal => hlegal.1 hw
  nonterminal_exists_legal := fun {w} hw => by
    have hwfalse : w = false := by cases w <;> simp_all
    refine ⟨fun i => some (Classical.arbitrary (A i)), ?_, ?_⟩
    · simp [hwfalse]
    · intro i
      simp [hwfalse]

/-- Terminal states of the one-shot FOSG are exactly `true`. -/
@[simp] theorem toFOSG_terminal_iff (G : NFGGame ι A) (w : Bool) :
    (G.toFOSG).terminal w ↔ w = true := Iff.rfl

/-- Every player is active at the initial state of the one-shot FOSG. -/
@[simp] theorem toFOSG_active_init (G : NFGGame ι A) :
    (G.toFOSG).active false = Finset.univ := by
  simp [toFOSG]

/-- The initial state is nonterminal. -/
@[simp] theorem toFOSG_not_terminal_init (G : NFGGame ι A) :
    ¬ (G.toFOSG).terminal false := by
  simp [toFOSG]

/-- The transition from the initial state lands in `true`. -/
@[simp] theorem toFOSG_transition_init (G : NFGGame ι A) (a : (G.toFOSG).LegalAction false) :
    (G.toFOSG).transition false a = PMF.pure true := rfl

/-- The one-shot FOSG has bounded horizon `1`. -/
theorem toFOSG_boundedHorizon (G : NFGGame ι A) :
    (G.toFOSG).BoundedHorizon 1 := by
  intro h hlen
  change (G.toFOSG).terminal h.lastState
  rcases hsteps : h.steps with _ | ⟨e, rest⟩
  · rw [hsteps] at hlen; simp at hlen
  · rcases hrest : rest with _ | ⟨e2, rest2⟩
    · -- single-step case: h.steps = [e]
      have hchain := h.chain
      rw [hsteps, hrest] at hchain
      have hsrc : e.src = false := hchain.1
      have hdst : e.dst = true := by
        cases hd : e.dst with
        | true => rfl
        | false =>
            exfalso
            have hsupp : (G.toFOSG).transition e.src e.act e.dst ≠ 0 := e.support
            simp [toFOSG, hd] at hsupp
      have hlast : h.lastState = e.dst := by
        change (G.toFOSG).lastStateFrom (G.toFOSG).init h.steps = e.dst
        rw [hsteps, hrest]
        rfl
      rw [hlast, hdst]
      simp [toFOSG]
    · -- ≥2-step case: contradicts hlen
      rw [hsteps, hrest] at hlen
      simp at hlen

/-- In the one-shot FOSG, a history with empty player view for player `i` must
be the empty history. Each realized step contributes a nonempty player view, so
an empty view forces an empty step list. -/
theorem toFOSG_history_eq_nil_of_playerView_nil
    (G : NFGGame ι A) {i : ι} {h : (G.toFOSG).History}
    (hv : h.playerView i = []) :
    h = GameTheory.FOSG.History.nil (G.toFOSG) := by
  apply GameTheory.FOSG.History.ext
  rcases hsteps : h.steps with _ | ⟨e, rest⟩
  · rfl
  · exfalso
    have hview : h.playerView i =
        e.playerView i ++ GameTheory.FOSG.History.playerViewFrom i rest := by
      rw [GameTheory.FOSG.History.playerView, hsteps]
      rfl
    rw [hview] at hv
    have hpos := GameTheory.FOSG.Step.playerView_length_pos e i
    have hlen : (e.playerView i ++ GameTheory.FOSG.History.playerViewFrom i rest).length = 0 := by
      rw [hv]; rfl
    rw [List.length_append] at hlen
    omega

/-- A nonempty one-shot FOSG history ends in the terminal state `true`: the
single transition always lands in `true`, so any realized step terminates. -/
theorem toFOSG_lastState_true_of_steps_ne_nil
    (G : NFGGame ι A) {h : (G.toFOSG).History} (hne : h.steps ≠ []) :
    h.lastState = true := by
  rcases hsteps : h.steps with _ | ⟨e, rest⟩
  · exact absurd hsteps hne
  · have hsupp : (G.toFOSG).transition e.src e.act e.dst ≠ 0 := e.support
    have hdst : e.dst = true := by
      cases hd : e.dst with
      | true => rfl
      | false =>
          exfalso
          simp [toFOSG, hd] at hsupp
    have hchain := h.chain
    rw [hsteps] at hchain
    -- the chain pins e.src and forces rest to be empty (e.dst = true is terminal)
    have hrestnil : rest = [] := by
      rcases hrest : rest with _ | ⟨e2, rest2⟩
      · rfl
      · exfalso
        have htail : (G.toFOSG).StepChainFrom e.dst (e2 :: rest2) := by
          rw [hrest] at hchain; exact hchain.2
        have he2src : e2.src = e.dst := htail.1
        have hterm : (G.toFOSG).terminal e2.src := by
          rw [he2src, hdst]; rfl
        exact (G.toFOSG).not_legal_of_terminal (a := e2.act.1) hterm e2.act.2
    have hlast : h.lastState = e.dst := by
      change (G.toFOSG).lastStateFrom (G.toFOSG).init h.steps = e.dst
      rw [hsteps, hrestnil]
      rfl
    rw [hlast, hdst]

section Soundness

variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

-- `DecidableEq (A i)` is needed to define the behavioral lift (the `if v = []`
-- branch), so it appears only in proof terms, not in some lemma statements.
set_option linter.unusedDecidableInType false

/-- Per-player behavioral lift of an NFG action into the one-shot FOSG: play
`some a` at the empty information state (the initial decision point) and `none`
thereafter (where the player is inactive at the terminal state). -/
noncomputable def liftBehavioral (G : NFGGame ι A) (i : ι) (a : A i) :
    (G.toFOSG).LegalBehavioralStrategy i :=
  ⟨fun v => if v = ([] : (G.toFOSG).InfoState i) then PMF.pure (some a) else PMF.pure none,
   by
     intro h oi hoi
     by_cases hview : h.playerView i = ([] : (G.toFOSG).InfoState i)
     · -- empty view: history is nil, lastState = false, every player active
       have hh : h = GameTheory.FOSG.History.nil (G.toFOSG) :=
         G.toFOSG_history_eq_nil_of_playerView_nil hview
       simp only [hview, if_true, PMF.support_pure, Set.mem_singleton_iff] at hoi
       subst hoi
       rw [GameTheory.FOSG.mem_availableMoves_iff]
       have hlast : h.lastState = false := by rw [hh]; rfl
       refine ⟨?_, ?_⟩
       · rw [hlast]; simp [toFOSG]
       · rw [hlast]; simp [toFOSG]
     · -- nonempty view: player inactive at terminal state, `none` is the only move
       simp only [if_neg hview, PMF.support_pure, Set.mem_singleton_iff] at hoi
       subst hoi
       rw [GameTheory.FOSG.mem_availableMoves_iff]
       have hne : h.steps ≠ [] := by
         intro hnil
         exact hview (by rw [GameTheory.FOSG.History.playerView, hnil]; rfl)
       have hlast : h.lastState = true := G.toFOSG_lastState_true_of_steps_ne_nil hne
       change i ∉ (G.toFOSG).active h.lastState
       rw [hlast]; simp [toFOSG]⟩

/-- The all-`some` joint action induced by a pure NFG profile is legal at the
initial state of the one-shot FOSG, where every player is active. -/
noncomputable def jointActionOf (G : NFGGame ι A) (s : ∀ i, A i) :
    (G.toFOSG).LegalAction false :=
  ⟨fun i => some (s i), by
    rw [GameTheory.FOSG.legal_iff_forall]
    refine ⟨by simp [toFOSG], ?_⟩
    intro i
    refine ⟨?_, ?_⟩
    · simp [toFOSG]
    · simp [toFOSG]⟩

omit [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] in
@[simp] theorem jointActionOf_val (G : NFGGame ι A) (s : ∀ i, A i) :
    (G.jointActionOf s).1 = fun i => some (s i) := rfl

omit [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] in
theorem actionsOfJoint_jointActionOf (G : NFGGame ι A) (s : ∀ i, A i) :
    actionsOfJoint (G.jointActionOf s).1 = s := by
  funext i
  simp [actionsOfJoint, jointActionOf]

/-- The profile of behavioral lifts of a pure NFG profile. -/
noncomputable def liftProfile (G : NFGGame ι A) (s : ∀ i, A i) :
    (G.toFOSG).LegalBehavioralProfile :=
  fun i => G.liftBehavioral i (s i)

/-- At the initial history, the induced legal-action law of a lifted pure
profile is the point mass on the corresponding all-`some` joint action. -/
theorem toFOSG_legalActionLaw_nil (G : NFGGame ι A) (s : ∀ i, A i)
    (hterm : ¬ (G.toFOSG).terminal (GameTheory.FOSG.History.nil (G.toFOSG)).lastState) :
    (G.toFOSG).legalActionLaw (G.liftProfile s)
        (GameTheory.FOSG.History.nil (G.toFOSG)) hterm =
      PMF.pure (G.jointActionOf s) := by
  apply PMF.ext
  intro a
  rw [(G.toFOSG).legalActionLaw_apply (G.liftProfile s) _ hterm]
  rw [(G.toFOSG).jointActionDist_apply]
  have hstep : ∀ i, (G.liftProfile s).toProfile i ([] : (G.toFOSG).InfoState i)
      = PMF.pure (some (s i)) := by
    intro i
    change (G.liftBehavioral i (s i)).1 ([] : (G.toFOSG).InfoState i) = PMF.pure (some (s i))
    rw [liftBehavioral]
    simp only [if_pos]
  have hfac : ∀ i, ((G.liftProfile s).toProfile i
      ((GameTheory.FOSG.History.nil (G.toFOSG)).playerView i)) (a.1 i) =
      if a.1 i = some (s i) then (1 : ENNReal) else 0 := by
    intro i
    rw [GameTheory.FOSG.History.playerView_nil, hstep i]
    simp [PMF.pure_apply]
  simp_rw [hfac]
  by_cases ha : a = G.jointActionOf s
  · subst ha
    have hlhs : (∏ x, if (G.jointActionOf s).1 x = some (s x) then (1 : ENNReal) else 0) = 1 := by
      refine Finset.prod_eq_one ?_
      intro i _
      rw [if_pos]
      rfl
    rw [hlhs]
    exact (PMF.pure_apply_self _).symm
  · have hex : ∃ i, a.1 i ≠ some (s i) := by
      by_contra hcon
      apply ha
      apply Subtype.ext
      funext i
      by_contra hne
      exact hcon ⟨i, hne⟩
    obtain ⟨i, hi⟩ := hex
    have hlhs : (∏ x, if a.1 x = some (s x) then (1 : ENNReal) else 0) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [if_neg hi]
    rw [hlhs]
    exact (PMF.pure_apply_of_ne (G.jointActionOf s) a ha).symm

/-- `terminal` of the one-shot FOSG (`w = true`) is decidable. -/
instance instDecidablePredToFOSGTerminal (G : NFGGame ι A) :
    DecidablePred (G.toFOSG).terminal :=
  fun w => decEq w true

/-- Finite history type of the one-shot FOSG, from its horizon bound. -/
noncomputable instance instFintypeToFOSGHistory (G : NFGGame ι A) :
    Fintype (G.toFOSG).History :=
  (G.toFOSG).historyFintypeOfBoundedHorizon G.toFOSG_boundedHorizon

omit [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] in
/-- The transition out of the initial state has full support on `true`. -/
theorem toFOSG_transition_init_support (G : NFGGame ι A)
    (a : (G.toFOSG).LegalAction false) :
    (G.toFOSG).transition false a true ≠ 0 := by
  rw [toFOSG_transition_init]
  simp

/-- The single one-step realized history reached by playing the all-`some`
joint action `jointActionOf s` from the initial state. -/
noncomputable def oneStepHistory (G : NFGGame ι A) (s : ∀ i, A i) :
    (G.toFOSG).History :=
  (GameTheory.FOSG.History.nil (G.toFOSG)).snoc (G.jointActionOf s) true
    (by
      have h := G.toFOSG_transition_init_support (G.jointActionOf s)
      exact h)

/-- The horizon-1 run distribution of a lifted pure profile is the point mass
on the corresponding one-step history. -/
theorem toFOSG_runDist_one (G : NFGGame ι A) (s : ∀ i, A i) :
    (G.toFOSG).runDist 1 (G.liftProfile s) = PMF.pure (G.oneStepHistory s) := by
  have hterm : ¬ (G.toFOSG).terminal (GameTheory.FOSG.History.nil (G.toFOSG)).lastState := by
    rw [GameTheory.FOSG.History.lastState_nil]
    exact G.toFOSG_not_terminal_init
  rw [GameTheory.FOSG.runDist, show (1 : Nat) = 0 + 1 from rfl,
    GameTheory.FOSG.History.runDistFrom_succ_nonterminal _ _ _ hterm]
  rw [toFOSG_legalActionLaw_nil G s hterm]
  -- the bind/pure live at `LegalAction nil.lastState`; `nil.lastState` is `false`
  -- definitionally, so rewrite via the defeq pure-bind step manually
  have hbind : ((PMF.pure (G.jointActionOf s)).bind fun a =>
        ((G.toFOSG).transition (GameTheory.FOSG.History.nil (G.toFOSG)).lastState a).bind
          fun dst => GameTheory.FOSG.History.runDistFrom (G.toFOSG) (G.liftProfile s) 0
            ((GameTheory.FOSG.History.nil (G.toFOSG)).extendByOutcome a dst)) =
      ((G.toFOSG).transition (GameTheory.FOSG.History.nil (G.toFOSG)).lastState
          (G.jointActionOf s)).bind
        fun dst => GameTheory.FOSG.History.runDistFrom (G.toFOSG) (G.liftProfile s) 0
          ((GameTheory.FOSG.History.nil (G.toFOSG)).extendByOutcome (G.jointActionOf s) dst) :=
    PMF.pure_bind (G.jointActionOf s) _
  refine hbind.trans ?_
  -- inner: transition nil.lastState (jointActionOf s) is pure true
  have htrans : (G.toFOSG).transition (GameTheory.FOSG.History.nil (G.toFOSG)).lastState
      (G.jointActionOf s) = PMF.pure true := rfl
  rw [htrans]
  have hbind2 : ((PMF.pure true).bind fun dst =>
        GameTheory.FOSG.History.runDistFrom (G.toFOSG) (G.liftProfile s) 0
          ((GameTheory.FOSG.History.nil (G.toFOSG)).extendByOutcome (G.jointActionOf s) dst)) =
      GameTheory.FOSG.History.runDistFrom (G.toFOSG) (G.liftProfile s) 0
        ((GameTheory.FOSG.History.nil (G.toFOSG)).extendByOutcome (G.jointActionOf s) true) :=
    PMF.pure_bind true _
  rw [hbind2, GameTheory.FOSG.History.runDistFrom_zero]
  -- extendByOutcome (jointActionOf s) true = oneStepHistory
  congr 1
  rw [GameTheory.FOSG.History.extendByOutcome_of_support
    (h := GameTheory.FOSG.History.nil (G.toFOSG)) (a := G.jointActionOf s) (dst := true)
    (G.toFOSG_transition_init_support (G.jointActionOf s))]
  rfl

omit [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] in
/-- The utility vector of the one-step history equals the NFG payoff of the
underlying pure profile. -/
theorem toFOSG_oneStepHistory_utility (G : NFGGame ι A) (s : ∀ i, A i) (i : ι) :
    GameTheory.FOSG.History.utility (G.oneStepHistory s) i =
      G.utility (G.outcome s) i := by
  rw [oneStepHistory, GameTheory.FOSG.History.utility_snoc,
    GameTheory.FOSG.History.utility_nil]
  -- reward false (jointActionOf s) true i = G.utility (G.outcome (actionsOfJoint ...)) i
  change (0 : ℝ) + G.utility (G.outcome (actionsOfJoint (G.jointActionOf s).1)) i =
    G.utility (G.outcome s) i
  rw [G.actionsOfJoint_jointActionOf s, zero_add]

/-- Utility-distribution soundness of the one-shot FOSG embedding: the bounded
horizon kernel game of `G.toFOSG`, played by lifted pure strategies, has the
same joint utility distribution as the NFG's own kernel game. -/
theorem toFOSG_udist_eq (G : NFGGame ι A) (s : ∀ i, A i) :
    ((G.toFOSG).toKernelGameOfBoundedHorizon G.toFOSG_boundedHorizon).udist
        (G.liftProfile s) =
      PMF.pure (G.utility (G.outcome s)) := by
  rw [GameTheory.KernelGame.udist,
    GameTheory.FOSG.toKernelGameOfBoundedHorizon_outcomeKernel,
    toFOSG_runDist_one]
  have hpb : ((PMF.pure (G.oneStepHistory s)).bind fun ω =>
        PMF.pure (((G.toFOSG).toKernelGameOfBoundedHorizon G.toFOSG_boundedHorizon).utility ω)) =
      PMF.pure (((G.toFOSG).toKernelGameOfBoundedHorizon G.toFOSG_boundedHorizon).utility
        (G.oneStepHistory s)) :=
    PMF.pure_bind (G.oneStepHistory s) _
  refine hpb.trans ?_
  congr 1
  funext i
  exact G.toFOSG_oneStepHistory_utility s i

/-- NFG → FOSG soundness, packaged as a `KernelGame.Morphism`. The one-shot FOSG
embedding of `G` (compiled at its horizon bound `1`) refines `G`'s own kernel
game: mapping each pure NFG strategy to its behavioral lift preserves the joint
utility distribution. -/
noncomputable def toFOSG_morphism (G : NFGGame ι A) :
    GameTheory.KernelGame.Morphism G.toKernelGame
      ((G.toFOSG).toKernelGameOfBoundedHorizon G.toFOSG_boundedHorizon) where
  stratMap := fun i a => G.liftBehavioral i a
  udist_preserved := fun s =>
    (toFOSG_udist_eq G s).trans (NFGGame.toKernelGame_udist G s).symm

end Soundness

end NFGGame

end NFG
