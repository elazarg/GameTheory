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

/-- A factored-observation stochastic game. -/
structure FOSG (ι W : Type) [DecidableEq ι]
    (Act : ι → Type) (PrivObs : ι → Type) (PubObs : Type) where
  /-- Initial world state. -/
  init : W
  /-- Active players at a world state. -/
  active : W → Finset ι
  /-- Terminal-state predicate. -/
  terminal : W → Prop
  /-- Legal joint actions at a world state. -/
  legal : W → JointAction Act → Prop
  /-- Stochastic next-state kernel for legal joint actions. -/
  transition : (w : W) → {a : JointAction Act // legal w a} → PMF W
  /-- Per-player transition reward. -/
  reward : (w : W) → {a : JointAction Act // legal w a} → W → ι → ℝ
  /-- Player-private observation emitted by a transition. -/
  privObs : (i : ι) → (w : W) → {a : JointAction Act // legal w a} → W → PrivObs i
  /-- Public observation emitted by a transition. -/
  pubObs : (w : W) → {a : JointAction Act // legal w a} → W → PubObs
  /-- Inactive players contribute `none`. -/
  legal_inactive_none :
    ∀ {w : W} {a : JointAction Act} {i : ι},
      legal w a → i ∉ active w → a i = none
  /-- Active players choose an actual action. -/
  legal_active_some :
    ∀ {w : W} {a : JointAction Act} {i : ι},
      legal w a → i ∈ active w → ∃ ai : Act i, a i = some ai
  /-- Terminal states have no active strategic players. -/
  terminal_active_eq_empty :
    ∀ {w : W}, terminal w → active w = ∅
  /-- Terminal states admit no legal joint action. -/
  terminal_no_legal :
    ∀ {w : W} {a : JointAction Act}, terminal w → ¬ legal w a
  /-- Every nonterminal state admits at least one legal joint action. -/
  nonterminal_exists_legal :
    ∀ {w : W}, ¬ terminal w → ∃ a : JointAction Act, legal w a

namespace FOSG

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

/-- Legal joint actions at a given state. -/
abbrev LegalAction (G : FOSG ι W Act PrivObs PubObs) (w : W) : Type :=
  {a : JointAction Act // G.legal w a}

/-- Forget the legality proof attached to a legal joint action. -/
abbrev LegalAction.val'
    (G : FOSG ι W Act PrivObs PubObs) {w : W} (a : G.LegalAction w) :
    JointAction Act :=
  a.1

theorem legalAction_val
    (G : FOSG ι W Act PrivObs PubObs) {w : W} (a : G.LegalAction w) :
    G.legal w a.1 :=
  a.2

theorem inactive_eq_none
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} {a : G.LegalAction w} {i : ι}
    (hi : i ∉ G.active w) :
    a.1 i = none :=
  G.legal_inactive_none a.2 hi

theorem active_has_some
    (G : FOSG ι W Act PrivObs PubObs)
    {w : W} {a : G.LegalAction w} {i : ι}
    (hi : i ∈ G.active w) :
    ∃ ai : Act i, a.1 i = some ai :=
  G.legal_active_some a.2 hi

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

end FOSG

end GameTheory
