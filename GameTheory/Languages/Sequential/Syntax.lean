import GameTheory.Core.GameForm
import Math.PMFProduct
import Math.Probability

/-!
# Sequential Game Protocol

A sequential game protocol defines the mechanics of a finite multi-step game
with `n` players. The protocol separates game physics (signals, views,
transitions) from analysis (utility, equilibria, common-knowledge assumptions).

## Design

A game is a finite list of **rounds**. Each round specifies:
- A signal distribution (nature's move — possibly correlated across players)
- A view function (what each player observes: state + their private signal)
- A transition function (deterministic state update from joint actions)

**State** is an opaque type that threads through rounds. It can carry phase,
round counters, partial assignments, memory — whatever the specific game needs.

**Actions** are `Option A`: every player can always choose not to act (`none`).
Sequential play, folding, and termination are all modeled through `none`.

**Strategies** are pure and memoryless at the protocol level: `V → Option A`.
Mixed strategies, memory, and recall are analysis-layer concerns.

All randomness enters through signals (nature as a player whose strategy
is fixed). The transition is deterministic.

## Main definitions

- `Round` — one round of signal / view / action / transition
- `Protocol` — a list of rounds + initial state
- `PureStrategy`, `PureProfile` — per-player and joint pure strategies
- `BehavioralStrategy`, `BehavioralProfile` — mixed/behavioral versions
- `Round.eval` — one-round stochastic kernel given a profile
- `Protocol.eval` — full evaluation producing `PMF State`
-/

namespace GameTheory

open Math.Probability
open Math.PMFProduct

-- ============================================================================
-- Round: one round of play
-- ============================================================================

/-- One round of a sequential game.
    - `S` : state type (threads through the game)
    - `n` : number of players
    - `V` : view/observation type
    - `A` : action type (`Option A` used in practice)
    - `Sig` : signal type (nature's private message to each player) -/
structure Round (n : ℕ) (S V A Sig : Type) where
  /-- Nature's move: a joint signal distribution, possibly correlated. -/
  signal : S → PMF (Fin n → Sig)
  /-- What player `i` observes given the state and their private signal. -/
  view : Fin n → S → Sig → V
  /-- Deterministic state transition from current state and joint action.
      Actions are `Option A`: `none` means the player does not act. -/
  transition : S → (Fin n → Option A) → S

-- ============================================================================
-- Protocol: a finite sequence of rounds
-- ============================================================================

/-- A sequential game protocol: an initial state and a finite list of rounds. -/
structure Protocol (n : ℕ) (S V A Sig : Type) where
  /-- The initial state. -/
  init : S
  /-- The sequence of rounds, played in order. -/
  rounds : List (Round n S V A Sig)

-- ============================================================================
-- Strategies and profiles
-- ============================================================================

/-- A pure memoryless strategy for one player: maps view to optional action. -/
abbrev PureStrategy (V A : Type) := V → Option A

/-- A joint pure strategy profile: one strategy per player. -/
abbrev PureProfile (n : ℕ) (V A : Type) := Fin n → PureStrategy V A

/-- A behavioral strategy: maps view to a distribution over optional actions. -/
abbrev BehavioralStrategy (V A : Type) := V → PMF (Option A)

/-- A behavioral profile: one behavioral strategy per player. -/
abbrev BehavioralProfile (n : ℕ) (V A : Type) := Fin n → BehavioralStrategy V A

-- ============================================================================
-- Evaluation: running the protocol
-- ============================================================================

variable {n : ℕ} {S V A Sig : Type}

/-- Evaluate one round under a pure profile: draw signals, compute views,
    apply strategies, transition deterministically. -/
noncomputable def Round.eval (r : Round n S V A Sig) (σ : PureProfile n V A)
    (s : S) : PMF S :=
  (r.signal s).map fun sig =>
    r.transition s (fun i => σ i (r.view i s (sig i)))

/-- Evaluate one round under a behavioral profile. -/
noncomputable def Round.evalMixed [Fintype (Option A)]
    (r : Round n S V A Sig) (σ : BehavioralProfile n V A)
    (s : S) : PMF S :=
  (r.signal s).bind fun sig =>
    (pmfPi fun i => σ i (r.view i s (sig i))).map fun acts =>
      r.transition s acts

/-- Evaluate a sequence of rounds under a pure profile, threading state. -/
noncomputable def evalRounds (rounds : List (Round n S V A Sig))
    (σ : PureProfile n V A) (s : S) : PMF S :=
  rounds.foldl (fun dist r => dist.bind (r.eval σ)) (PMF.pure s)

/-- Evaluate the full protocol under a pure profile. -/
noncomputable def Protocol.eval (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) : PMF S :=
  evalRounds G.rounds σ G.init

/-- Evaluate a sequence of rounds under a behavioral profile. -/
noncomputable def evalRoundsMixed [Fintype (Option A)]
    (rounds : List (Round n S V A Sig))
    (σ : BehavioralProfile n V A) (s : S) : PMF S :=
  rounds.foldl (fun dist r => dist.bind (r.evalMixed σ)) (PMF.pure s)

/-- Evaluate the full protocol under a behavioral profile. -/
noncomputable def Protocol.evalMixed [Fintype (Option A)]
    (G : Protocol n S V A Sig) (σ : BehavioralProfile n V A) : PMF S :=
  evalRoundsMixed G.rounds σ G.init

-- ============================================================================
-- Pure ↪ Behavioral lifting
-- ============================================================================

/-- Lift a pure strategy to a behavioral strategy (point-mass distributions). -/
noncomputable def PureStrategy.toBehavioral (s : PureStrategy V A) :
    BehavioralStrategy V A :=
  fun v => PMF.pure (s v)

/-- Lift a pure profile to a behavioral profile. -/
noncomputable def PureProfile.toBehavioral (σ : PureProfile n V A) :
    BehavioralProfile n V A :=
  fun i => (σ i).toBehavioral

-- ============================================================================
-- Basic lemmas
-- ============================================================================

@[simp]
theorem PureStrategy.toBehavioral_apply (s : PureStrategy V A) (v : V) :
    s.toBehavioral v = PMF.pure (s v) := rfl

@[simp]
theorem PureProfile.toBehavioral_apply (σ : PureProfile n V A) (i : Fin n) :
    σ.toBehavioral i = (σ i).toBehavioral := rfl


-- ============================================================================
-- Perfect recall
-- ============================================================================

/-- A round-step record: the state and signals seen at one round. -/
structure RoundRecord (n : ℕ) (S Sig : Type) where
  state : S
  signals : Fin n → Sig

/-- Player `i`'s view at a round, given the round and a record. -/
def Round.playerView (r : Round n S V A Sig) (i : Fin n) (rec : RoundRecord n S Sig) : V :=
  r.view i rec.state (rec.signals i)

/-- An execution record at one round: state, signals, and the joint action taken. -/
structure ExecRecord (n : ℕ) (S A Sig : Type) extends RoundRecord n S Sig where
  actions : Fin n → Option A

/-- Coerce an `ExecRecord` to its underlying `RoundRecord`. -/
def ExecRecord.toRound (r : ExecRecord n S A Sig) : RoundRecord n S Sig := r.toRoundRecord

/-- Perfect recall (view only) for a sequential protocol: if two execution
prefixes produce the same view for player `i` at round `k`, then they produced
the same view at every previous round.

This is a structural condition on the view functions: the view at round `k` encodes
enough information to determine the player's full observation history. -/
def Protocol.PerfectRecall (G : Protocol n S V A Sig) : Prop :=
  ∀ (i : Fin n) (k : Nat) (hk : k < G.rounds.length)
    (recs₁ recs₂ : Fin (k + 1) → RoundRecord n S Sig),
    -- Same view at round k
    G.rounds[k].playerView i (recs₁ ⟨k, Nat.lt_succ_self k⟩) =
      G.rounds[k].playerView i (recs₂ ⟨k, Nat.lt_succ_self k⟩) →
    -- Implies same view at every previous round
    ∀ (j : Nat) (hj : j < k),
      G.rounds[j].playerView i (recs₁ ⟨j, by omega⟩) =
        G.rounds[j].playerView i (recs₂ ⟨j, by omega⟩)

/-- Full perfect recall for a sequential protocol: if two execution
prefixes produce the same view for player `i` at round `k`, then they produced
the same view AND the same own-action at every previous round.

This is the standard game-theoretic notion of perfect recall, which requires
that a player remembers both what they observed and what they did. -/
def Protocol.FullRecall (G : Protocol n S V A Sig) : Prop :=
  ∀ (i : Fin n) (k : Nat) (hk : k < G.rounds.length)
    (recs₁ recs₂ : Fin (k + 1) → ExecRecord n S A Sig),
    -- Same view at round k
    G.rounds[k].playerView i (recs₁ ⟨k, Nat.lt_succ_self k⟩).toRound =
      G.rounds[k].playerView i (recs₂ ⟨k, Nat.lt_succ_self k⟩).toRound →
    -- Implies same view AND same own-action at every previous round
    ∀ (j : Nat) (hj : j < k),
      G.rounds[j].playerView i (recs₁ ⟨j, by omega⟩).toRound =
        G.rounds[j].playerView i (recs₂ ⟨j, by omega⟩).toRound ∧
      (recs₁ ⟨j, by omega⟩).actions i = (recs₂ ⟨j, by omega⟩).actions i

/-- Full recall implies view-only perfect recall. -/
theorem Protocol.FullRecall.toPerfectRecall {G : Protocol n S V A Sig}
    (h : G.FullRecall) : G.PerfectRecall := by
  intro i k hk recs₁ recs₂ hview j hj
  exact (h i k hk (fun m => ⟨recs₁ m, fun _ => none⟩)
    (fun m => ⟨recs₂ m, fun _ => none⟩) hview j hj).1

/-- No absent-mindedness: each view value uniquely identifies a round.
If the same view `v` can be produced at rounds `k₁` and `k₂` (for any states
and signals), then `k₁ = k₂`. This is the sequential-protocol analogue of the
standard condition that no information set is visited twice on any play path. -/
def Protocol.ViewDeterminesRound (G : Protocol n S V A Sig) : Prop :=
  ∀ (i : Fin n) (k₁ : Fin G.rounds.length) (k₂ : Fin G.rounds.length)
    (s₁ s₂ : S) (sig₁ sig₂ : Sig),
    G.rounds[k₁].view i s₁ sig₁ = G.rounds[k₂].view i s₂ sig₂ →
    k₁ = k₂

-- ============================================================================
-- Bridge to GameForm / KernelGame
-- ============================================================================

/-- A protocol gives a `GameForm`: pure profiles in, final-state distribution out. -/
noncomputable def Protocol.toGameForm (G : Protocol n S V A Sig) :
    GameForm (Fin n) where
  Strategy := fun _ => PureStrategy V A
  Outcome := S
  outcomeKernel := fun σ => G.eval σ

/-- A protocol paired with a utility function gives a `KernelGame`. -/
noncomputable def Protocol.toKernelGame (G : Protocol n S V A Sig)
    (u : S → Fin n → ℝ) : KernelGame (Fin n) where
  Strategy := fun _ => PureStrategy V A
  Outcome := S
  utility := fun s i => u s i
  outcomeKernel := fun σ => G.eval σ

theorem Protocol.toKernelGame_toGameForm (G : Protocol n S V A Sig)
    (u : S → Fin n → ℝ) :
    (G.toKernelGame u).toGameForm = G.toGameForm := rfl

end GameTheory
