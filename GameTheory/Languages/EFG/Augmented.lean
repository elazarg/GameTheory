import GameTheory.Languages.EFG.Syntax

/-!
# GameTheory.Languages.EFG.Augmented

Augmented extensive-form games in the sense of the FOSG paper.

This layer is intentionally a thin wrapper over the existing `EFGGame` core.
The underlying tree, chance structure, and acting-player infosets remain the
same as in `Syntax.lean`; the augmentation adds:

- a public partition over all reachable histories
- a player information partition over all reachable histories for every player

This matches the paper's definition of an augmented EFG more closely than the
historical/classical EFG formalization, where infosets are only present when
the player acts.
-/

namespace EFG

/-- A reachable history together with its endpoint node. -/
structure ReachableNode (G : EFGGame) where
  hist : List (HistoryStep G.inf)
  node : GameTree G.inf G.Outcome
  reach : ReachBy hist G.tree node

namespace ReachableNode

variable {G : EFGGame}

/-- Forget the endpoint and keep only the underlying history. -/
abbrev steps (h : ReachableNode G) : List (HistoryStep G.inf) := h.hist

/-- History-prefix relation on reachable nodes. -/
def IsPrefix (g h : ReachableNode G) : Prop :=
  ∃ suffix, g.hist ++ suffix = h.hist

/-- Strict prefix relation on reachable nodes. -/
def IsStrictPrefix (g h : ReachableNode G) : Prop :=
  g.IsPrefix h ∧ g.hist ≠ h.hist

theorem prefix_refl (h : ReachableNode G) : h.IsPrefix h := by
  exact ⟨[], by simp⟩

theorem prefix_trans {g h k : ReachableNode G}
    (hgh : g.IsPrefix h) (hhk : h.IsPrefix k) : g.IsPrefix k := by
  rcases hgh with ⟨s₁, hs₁⟩
  rcases hhk with ⟨s₂, hs₂⟩
  refine ⟨s₁ ++ s₂, ?_⟩
  rw [← hs₂, ← hs₁, List.append_assoc]

/-- The acting player at a reachable node, if any. -/
def player? (h : ReachableNode G) : Option G.inf.Player :=
  match h.node with
  | .terminal _ => none
  | .chance _ _ _ _ => none
  | .decision (p := p) _ _ => some p

/-- The action arity at a reachable node, if it is a decision node. -/
def actionArity? (h : ReachableNode G) : Option Nat :=
  match h.node with
  | .terminal _ => none
  | .chance _ _ _ _ => none
  | .decision (p := p) I _ => some (G.inf.arity p I)

/-- Reachable nodes ending at a decision of player `p`. -/
def IsDecisionFor (h : ReachableNode G) (p : G.inf.Player) : Prop :=
  ∃ (I : G.inf.Infoset p) (next : G.inf.Act I → GameTree G.inf G.Outcome),
    h.node = .decision I next

theorem isDecisionFor_iff_player
    (h : ReachableNode G) (p : G.inf.Player) :
    h.IsDecisionFor p ↔ h.player? = some p := by
  constructor
  · rintro ⟨I, next, hnode⟩
    cases h with
    | mk hist node reach =>
        cases hnode
        rfl
  · cases h with
    | mk hist node reach =>
        cases node with
        | terminal z =>
            simp [IsDecisionFor, player?]
        | chance k μ hk next =>
            simp [IsDecisionFor, player?]
        | @decision q I next =>
            intro hplayer
            cases hplayer
            exact ⟨I, next, rfl⟩

theorem actionArity?_eq_some_of_isDecisionFor
    {h : ReachableNode G} {p : G.inf.Player}
    (hdec : h.IsDecisionFor p) :
    ∃ n, h.actionArity? = some n := by
  rcases hdec with ⟨I, next, hnode⟩
  cases h with
  | mk hist node reach =>
      cases hnode
      exact ⟨G.inf.arity p I, rfl⟩

end ReachableNode

/-- A reachable decision node of player `p`. This is the natural domain for
the "infoset identifies legal actions" property from the paper. -/
structure ReachableDecision (G : EFGGame) (p : G.inf.Player) where
  hist : List (HistoryStep G.inf)
  I : G.inf.Infoset p
  next : G.inf.Act I → GameTree G.inf G.Outcome
  reach : ReachBy hist G.tree (.decision I next)

namespace ReachableDecision

variable {G : EFGGame} {p : G.inf.Player}

/-- Forget a reachable decision node down to a general reachable history/node. -/
def toReachableNode (d : ReachableDecision G p) : ReachableNode G :=
  ⟨d.hist, .decision d.I d.next, d.reach⟩

@[simp] theorem toReachableNode_player
    (d : ReachableDecision G p) :
    d.toReachableNode.player? = some p := rfl

@[simp] theorem toReachableNode_actionArity
    (d : ReachableDecision G p) :
    d.toReachableNode.actionArity? = some (G.inf.arity p d.I) := rfl

end ReachableDecision

/-- An augmented extensive-form game is a plain `EFGGame` together with:

- a public information state on every reachable history
- a player information state on every reachable history, for every player

Each player information state refines the public state, and for histories where
the player acts, the information state identifies the available actions via the
underlying infoset arity. -/
structure AugmentedGame where
  base : EFGGame
  PubState : Type
  InfoState : base.inf.Player → Type
  publicState : ReachableNode base → PubState
  playerState : (p : base.inf.Player) → ReachableNode base → InfoState p
  publicOf : (p : base.inf.Player) → InfoState p → PubState
  publicOf_playerState :
    ∀ (p : base.inf.Player) (h : ReachableNode base),
      publicOf p (playerState p h) = publicState h
  actionIdentified :
    ∀ {p : base.inf.Player}
      (d₁ d₂ : ReachableDecision base p),
      playerState p d₁.toReachableNode = playerState p d₂.toReachableNode →
      base.inf.arity p d₁.I = base.inf.arity p d₂.I

namespace AugmentedGame

variable (G : AugmentedGame)

/-- The underlying classical / forgetful extensive-form game. -/
abbrev forget : EFGGame := G.base

/-- Public partition fiber of a public state. -/
def publicSet (s : G.PubState) : Set (ReachableNode G.base) :=
  { h | G.publicState h = s }

/-- Player-`p` information-set fiber of a player information state. -/
def infoSet (p : G.base.inf.Player) (s : G.InfoState p) : Set (ReachableNode G.base) :=
  { h | G.playerState p h = s }

/-- Decision-point information set: the histories in a player's information set
where that player is to act. -/
def decisionInfoSet (p : G.base.inf.Player) (s : G.InfoState p) :
    Set (ReachableNode G.base) :=
  { h | h.IsDecisionFor p ∧ G.playerState p h = s }

theorem mem_decisionInfoSet_iff
    (p : G.base.inf.Player) (s : G.InfoState p) (h : ReachableNode G.base) :
    h ∈ G.decisionInfoSet p s ↔ h.IsDecisionFor p ∧ G.playerState p h = s := Iff.rfl

theorem decisionInfoSet_subset_infoSet
    (p : G.base.inf.Player) (s : G.InfoState p) :
    G.decisionInfoSet p s ⊆ G.infoSet p s := by
  intro h hh
  exact hh.2

/-- Player information partitions refine the public partition. -/
theorem infoSet_subset_publicSet
    (p : G.base.inf.Player) (s : G.InfoState p) :
    G.infoSet p s ⊆ G.publicSet (G.publicOf p s) := by
  intro h hh
  change G.publicState h = G.publicOf p s
  rw [← G.publicOf_playerState p h, hh]

theorem decisionInfoSet_subset_publicSet
    (p : G.base.inf.Player) (s : G.InfoState p) :
    G.decisionInfoSet p s ⊆ G.publicSet (G.publicOf p s) :=
  Set.Subset.trans (G.decisionInfoSet_subset_infoSet p s) (G.infoSet_subset_publicSet p s)

/-- The paper's "no thick public sets" property: no public set contains a
history together with one of its strict extensions. -/
def NoThickPublicSets : Prop :=
  ∀ {g h : ReachableNode G.base},
    G.publicState g = G.publicState h →
    g.IsPrefix h →
    g.hist = h.hist

/-- Perfect recall for the underlying extensive-form tree. This is the
classical EFG perfect-recall notion already used elsewhere in the codebase. -/
def PerfectRecall : Prop :=
  _root_.EFG.PerfectRecall G.base.tree

/-- If two decision histories of player `p` have the same player information
state, then they induce the same number of available actions. -/
theorem decisionArity_eq_of_playerState_eq
    {p : G.base.inf.Player}
    (d₁ d₂ : ReachableDecision G.base p)
    (hEq : G.playerState p d₁.toReachableNode = G.playerState p d₂.toReachableNode) :
    d₁.toReachableNode.actionArity? = d₂.toReachableNode.actionArity? := by
  change some (G.base.inf.arity p d₁.I) = some (G.base.inf.arity p d₂.I)
  simpa using congrArg some (G.actionIdentified d₁ d₂ hEq)

/-- The corresponding action types at two decision histories with the same
player information state are canonically equivalent. -/
noncomputable def actEquivOfPlayerStateEq
    {p : G.base.inf.Player}
    (d₁ d₂ : ReachableDecision G.base p)
    (hEq : G.playerState p d₁.toReachableNode = G.playerState p d₂.toReachableNode) :
    G.base.inf.Act d₁.I ≃ G.base.inf.Act d₂.I := by
  classical
  let harity := G.actionIdentified d₁ d₂ hEq
  exact Equiv.cast (by simp [InfoStructure.Act, harity])

end AugmentedGame

end EFG
