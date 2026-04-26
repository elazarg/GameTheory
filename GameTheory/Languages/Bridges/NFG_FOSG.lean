import GameTheory.Languages.NFG.Syntax
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
-/

namespace NFG

open GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
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

omit [∀ i, DecidableEq (A i)] in
/-- Terminal states of the one-shot FOSG are exactly `true`. -/
@[simp] theorem toFOSG_terminal_iff (G : NFGGame ι A) (w : Bool) :
    (G.toFOSG).terminal w ↔ w = true := Iff.rfl

omit [∀ i, DecidableEq (A i)] in
/-- Every player is active at the initial state of the one-shot FOSG. -/
@[simp] theorem toFOSG_active_init (G : NFGGame ι A) :
    (G.toFOSG).active false = Finset.univ := by
  simp [toFOSG]

omit [∀ i, DecidableEq (A i)] in
/-- The initial state is nonterminal. -/
@[simp] theorem toFOSG_not_terminal_init (G : NFGGame ι A) :
    ¬ (G.toFOSG).terminal false := by
  simp [toFOSG]

omit [∀ i, DecidableEq (A i)] in
/-- The transition from the initial state lands in `true`. -/
@[simp] theorem toFOSG_transition_init
    (G : NFGGame ι A) (a : (G.toFOSG).LegalAction false) :
    (G.toFOSG).transition false a = PMF.pure true := rfl

omit [∀ i, DecidableEq (A i)] in
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

end NFGGame

end NFG
