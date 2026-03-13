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
