import Math.Probability
import Mathlib.Data.Finset.Basic

/-!
# GameTheory.Languages.FOSG.Basic

Factored-observation stochastic games in their native form.

This is the paper-faithful core: transitions emit player-private and public
observations. Bridges to other language layers belong elsewhere.
-/

namespace GameTheory

open Math.Probability

/-- Joint action profile with optional participation for each player. -/
abbrev JointAction {ι : Type} (Act : ι → Type) : Type :=
  ∀ i, Option (Act i)

/-- Paper-faithful factorized legality of a joint action: every active player
chooses an available action, and inactive players choose `none`. -/
def JointActionLegal {ι W : Type}
    (Act : ι → Type)
    (active : W → Finset ι)
    (terminal : W → Prop)
    (availableActions : W → (i : ι) → Set (Act i))
    (w : W) (a : JointAction Act) : Prop :=
  ¬ terminal w ∧
    ∀ i, match a i with
      | some ai => i ∈ active w ∧ ai ∈ availableActions w i
      | none => i ∉ active w

/-- A factored-observation stochastic game. -/
structure FOSG (ι W : Type) [DecidableEq ι]
    (Act : ι → Type) (PrivObs : ι → Type) (PubObs : Type) where
  /-- Initial world state. -/
  init : W
  /-- Active players at a world state. -/
  active : W → Finset ι
  /-- Available concrete actions for each player at each world state. -/
  availableActions : W → (i : ι) → Set (Act i)
  /-- Terminal-state predicate. -/
  terminal : W → Prop
  /-- Stochastic next-state kernel for legal joint actions. -/
  transition :
    (w : W) →
      {a : JointAction Act // JointActionLegal Act active terminal availableActions w a} →
      PMF W
  /-- Per-player transition reward. -/
  reward :
    (w : W) →
      {a : JointAction Act // JointActionLegal Act active terminal availableActions w a} →
      W → ι → ℝ
  /-- Player-private observation emitted by a transition. -/
  privObs :
    (i : ι) → (w : W) →
      {a : JointAction Act // JointActionLegal Act active terminal availableActions w a} →
      W → PrivObs i
  /-- Public observation emitted by a transition. -/
  pubObs :
    (w : W) →
      {a : JointAction Act // JointActionLegal Act active terminal availableActions w a} →
      W → PubObs
  /-- Terminal states have no active strategic players. -/
  terminal_active_eq_empty :
    ∀ {w : W}, terminal w → active w = ∅
  /-- Terminal states admit no legal joint action. -/
  terminal_no_legal :
    ∀ {w : W} {a : JointAction Act},
      terminal w → ¬ JointActionLegal Act active terminal availableActions w a
  /-- Every nonterminal state admits at least one legal joint action. -/
  nonterminal_exists_legal :
    ∀ {w : W}, ¬ terminal w →
      ∃ a : JointAction Act, JointActionLegal Act active terminal availableActions w a

namespace FOSG

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

/-- The all-`none` joint action. -/
def noopAction (Act : ι → Type) : JointAction Act :=
  fun _ => none

omit [DecidableEq ι] in
@[simp] theorem noopAction_apply (i : ι) :
    noopAction Act i = none := rfl

/-- Legal joint actions at a given state. -/
abbrev legal
    (G : FOSG ι W Act PrivObs PubObs)
    (w : W) (a : JointAction Act) : Prop :=
  JointActionLegal Act G.active G.terminal G.availableActions w a

/-- Local legality of one player's optional move at a world state. -/
abbrev availableActionsAtState
    (G : FOSG ι W Act PrivObs PubObs)
    (w : W) (i : ι) : Set (Act i) :=
  G.availableActions w i

theorem mem_availableActionsAtState_iff
    {G : FOSG ι W Act PrivObs PubObs}
    {w : W} {i : ι} {ai : Act i} :
    ai ∈ G.availableActionsAtState w i ↔ ai ∈ G.availableActions w i := by
  rfl

/-- Local legality of one player's optional move at a world state. -/
def locallyLegalAtState
    (G : FOSG ι W Act PrivObs PubObs)
    (w : W) (i : ι) : Option (Act i) → Prop
  | some ai => i ∈ G.active w ∧ ai ∈ G.availableActions w i
  | none => i ∉ G.active w

theorem legal_iff_forall
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} {a : JointAction Act} :
    G.legal w a ↔ ¬ G.terminal w ∧ ∀ i, G.locallyLegalAtState w i (a i) := by
  unfold legal JointActionLegal locallyLegalAtState
  rfl

abbrev LegalAction (G : FOSG ι W Act PrivObs PubObs) (w : W) : Type :=
  {a : JointAction Act // G.legal w a}

theorem legalAction_val
    (G : FOSG ι W Act PrivObs PubObs) {w : W} (a : G.LegalAction w) :
    G.legal w a.1 :=
  a.2

theorem inactive_eq_none
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} {a : G.LegalAction w} {i : ι}
    (hi : i ∉ G.active w) :
    a.1 i = none := by
  cases h : a.1 i with
  | none =>
      exact rfl
  | some ai =>
      have : i ∈ G.active w ∧ ai ∈ G.availableActions w i := by
        simpa [h] using (a.2.2 i)
      exact False.elim (hi this.1)

theorem legal_inactive_none
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} {a : G.LegalAction w} {i : ι}
    (hi : i ∉ G.active w) :
    a.1 i = none :=
  G.inactive_eq_none hi

theorem active_has_some
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} {a : G.LegalAction w} {i : ι}
    (hi : i ∈ G.active w) :
    ∃ ai : Act i, a.1 i = some ai := by
  cases h : a.1 i with
  | none =>
      have : i ∉ G.active w := by simpa [h] using (a.2.2 i)
      exact False.elim (this hi)
  | some ai =>
      exact ⟨ai, rfl⟩

theorem legal_active_some
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} {a : G.LegalAction w} {i : ι}
    (hi : i ∈ G.active w) :
    ∃ ai : Act i, a.1 i = some ai :=
  G.active_has_some hi

theorem active_eq_empty_of_terminal
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} (hw : G.terminal w) :
    G.active w = ∅ :=
  G.terminal_active_eq_empty hw

theorem not_legal_of_terminal
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} {a : JointAction Act} (hw : G.terminal w) :
    ¬ G.legal w a :=
  G.terminal_no_legal hw

theorem exists_legal_of_not_terminal
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} (hw : ¬ G.terminal w) :
    ∃ a : JointAction Act, G.legal w a :=
  G.nonterminal_exists_legal hw

theorem legal_noopAction_of_active_empty_of_not_terminal
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} (hactive : G.active w = ∅) (hterm : ¬ G.terminal w) :
    G.legal w (noopAction Act) := by
  refine ⟨hterm, ?_⟩
  intro i
  simp [noopAction, hactive]

end FOSG

end GameTheory
