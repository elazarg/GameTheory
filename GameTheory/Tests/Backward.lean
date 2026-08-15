import GameTheory.Protocol.Backward

noncomputable section

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

/-!
# Backward-induction regression fixture

One fair coin, then one consequential decision, then stop. Small enough that
every value is a closed form, and asymmetric enough that the closed form is a
genuine mixture rather than a copy of some payoff.

Each probe below names the wrong implementation it kills.

1. `backwardValue_sensitive_to_successor` — a value that ignored its successors
   (returned `payoff source`, or a constant, or reused the chooser's action
   without following it) would be unchanged when a terminal successor's payoff
   moves. It is not.
2. `backwardValue_ignores_interior_payoff` — a value that stopped after one
   expectation, reading `payoff` at the states the first transition reaches
   rather than recursing, would see the deliberately loud payoff `100` planted at
   the interior state `pick`. It does not.
3. `backwardValue_sensitive_to_chooser` — a value that discarded the chooser's
   answer, or synthesized its own legal action from `progress`, would give the
   same number for both policies. It does not.
4. `backwardValue_flip_ne_terminal_payoffs` — the root value is `1/2`, which is
   neither terminal payoff, so the recursion is genuinely averaging rather than
   selecting a branch (a maximum would give `1`, a minimum `0`).
5. `expect_runFor_grab_base` — and the fuelled evaluator agrees with all of it.

The last section closes the loop: each of those three wrong implementations is
written down and *refuted in Lean*, by proving that the property the
corresponding probe asserts of `backwardValue` is false for it. A probe that
cannot fail is not a probe, and here that is a theorem rather than a claim.
-/

namespace GameTheory.Tests.Backward

open ExecutionProtocol

/-- Probe states: a chance node, one decision node, two terminal outcomes. -/
inductive Spot
  | /-- The chance node the game starts at. -/ flip
  | /-- The single decision node. -/ pick
  | /-- Terminal: the player grabbed. -/ grabbed
  | /-- Terminal: the player passed, or chance passed for them. -/ passed
  deriving DecidableEq

/-- The single player's actions. -/
inductive Move
  | /-- Grab. -/ grab
  | /-- Pass. -/ pass
  deriving DecidableEq

/-- Where a move leads. -/
def Move.outcome : Move → Spot
  | .grab => .grabbed
  | .pass => .passed

/-- The fair coin at the root: half the time the player gets to decide, half the
time chance passes on their behalf. The asymmetry is what makes the root value a
nondegenerate mixture. -/
def coin : FinDist Spot :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure .pick) (FinDist.pure .passed)

/-- `coin` unfolded. The `norm_num` side conditions are proofs, so the two sides
are definitionally equal. -/
theorem coin_eq_mix :
    coin = FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure Spot.pick) (FinDist.pure Spot.passed) := rfl

/-- Only the two branches carry mass. -/
theorem mem_support_coin {target : Spot} (hmem : target ∈ coin.support) :
    target = .pick ∨ target = .passed := by
  by_contra hno
  push Not at hno
  have hzero : coin.prob target = 0 := by
    rw [coin_eq_mix, FinDist.prob_mix, FinDist.prob_pure_of_ne hno.1,
      FinDist.prob_pure_of_ne hno.2]
    ring
  exact (FinDist.prob_pos_iff.2 hmem).ne' hzero

/-- Expectation against the coin, in closed form. -/
theorem expect_coin (observable : Spot → ℝ) :
    coin.expect observable = 1 / 2 * observable .pick + 1 / 2 * observable .passed := by
  rw [coin_eq_mix, FinDist.expect_mix, FinDist.expect_pure, FinDist.expect_pure]
  norm_num

/-- One player, one coin, one decision that matters, then stop.

The transition at the decision node is written with `Option.elim` rather than a
`match`, so that facts about it are proved by `cases` on the chosen action
instead of by rewriting a match scrutinee; nothing else about the encoding
depends on that choice.

Marked `@[reducible]` for the reason already recorded in
`GameTheory.Tests.Execution`: without it `probe.State` does not reduce to `Spot`
at `instances` transparency, so instance search and `simp` fail on the concrete
protocol. -/
@[reducible]
def probe : ExecutionProtocol Unit where
  State := Spot
  Action _ := Move
  init := .flip
  active state _ := state = .pick
  available _ _ := Set.univ
  terminal state := state = .grabbed ∨ state = .passed
  step state joint :=
    match state with
    | .flip => coin
    | _ => FinDist.pure ((joint.1 ()).elim Spot.passed Move.outcome)
  progress := by
    intro state _
    by_cases hpick : state = Spot.pick
    · exact ⟨fun _ => some .grab, fun _ => ⟨hpick, Set.mem_univ _⟩⟩
    · exact ⟨fun _ => none, fun _ => hpick⟩

theorem flip_not_terminal : ¬ probe.terminal Spot.flip := by simp

theorem pick_not_terminal : ¬ probe.terminal Spot.pick := by simp

theorem passed_terminal : probe.terminal Spot.passed := by simp

/-- Every move ends the game, which is what makes the decision node's successors
terminal. -/
theorem outcome_terminal (move : Move) : probe.terminal move.outcome := by
  cases move <;> simp [Move.outcome]

/-! ### The certificate for the probe -/

/-- Distance to the end of play. -/
def rank : Spot → ℕ
  | .flip => 2
  | .pick => 1
  | .grabbed => 0
  | .passed => 0

/-- Whatever the decision node's joint action is, its target has already
stopped. -/
theorem rank_outcome (choice : Option Move) :
    rank (choice.elim Spot.passed Move.outcome) = 0 := by
  cases choice with
  | none => rfl
  | some move => cases move <;> rfl

/-- **The concrete certificate.** The rank drops on every realized legal step, so
`probe` admits backward induction. Terminal states are handled by legality alone:
they have no legal joint action, hence no successors. -/
theorem probe_wellFoundedPlay : probe.WellFoundedPlay := by
  refine wellFoundedPlay_of_rank rank fun source target hsucc => ?_
  obtain ⟨joint, hlegal, hmem⟩ := hsucc
  cases source with
  | flip => rcases mem_support_coin hmem with rfl | rfl <;> simp [rank]
  | pick =>
    have hpure :
        target ∈ (FinDist.pure ((joint ()).elim Spot.passed Move.outcome)).support := hmem
    rw [FinDist.mem_support_pure.1 hpure, rank_outcome]
    simp [rank]
  | grabbed => exact absurd (Or.inl rfl) hlegal.1
  | passed => exact absurd (Or.inr rfl) hlegal.1

/-! ### Policies and closed-form values -/

/-- Play `move` at the decision node; everywhere else the no-op is forced.
Parameterizing by the move is what makes the chooser-dependence probe a
comparison of two instances of one definition. -/
def policy (move : Move) : probe.Chooser := fun state hterm =>
  if hpick : state = Spot.pick then
    ⟨fun _ => some move, hterm, fun _ => ⟨hpick, Set.mem_univ _⟩⟩
  else ⟨fun _ => none, hterm, fun _ => hpick⟩

/-- The transition at the root is the coin, whatever the policy. -/
theorem step_flip (move : Move) :
    probe.step Spot.flip (policy move Spot.flip flip_not_terminal) = coin := rfl

/-- The transition at the decision node is the policy's move, resolved. -/
theorem step_pick (move : Move) :
    probe.step Spot.pick (policy move Spot.pick pick_not_terminal) =
      FinDist.pure move.outcome := rfl

/-- The value at the decision node is the payoff of the move the policy plays.
This is one backward-induction step past a terminal state. -/
theorem backwardValue_pick (move : Move) (payoff : Spot → ℝ) :
    probe.backwardValue probe_wellFoundedPlay (policy move) payoff Spot.pick =
      payoff move.outcome := by
  rw [backwardValue_of_not_terminal pick_not_terminal, step_pick, FinDist.expect_pure,
    backwardValue_of_terminal (outcome_terminal move)]

/-- **The closed form.** Two backward-induction steps past the terminal states:
the root value mixes the payoff the policy earns at the decision node with the
payoff chance forces. Note which arguments appear — the move's outcome and
`passed` — and which do not: the payoffs at `flip` and `pick`. -/
theorem backwardValue_flip (move : Move) (payoff : Spot → ℝ) :
    probe.backwardValue probe_wellFoundedPlay (policy move) payoff Spot.flip =
      1 / 2 * payoff move.outcome + 1 / 2 * payoff Spot.passed := by
  rw [backwardValue_of_not_terminal flip_not_terminal, step_flip, expect_coin,
    backwardValue_pick, backwardValue_of_terminal passed_terminal]

/-! ### The payoff assignments the probes compare -/

/-- Grabbing pays `1`, passing pays `0`. The interior states carry a loud `7`
that a correct backward-induction value must never read. -/
def basePayoff : Spot → ℝ
  | .flip => 7
  | .pick => 7
  | .grabbed => 1
  | .passed => 0

/-- `basePayoff`, changed at exactly one terminal successor: `passed` now pays
`1`. -/
def raisedPayoff : Spot → ℝ
  | .flip => 7
  | .pick => 7
  | .grabbed => 1
  | .passed => 1

/-- `basePayoff`, changed at exactly one *interior* state: `pick` now pays `100`.
No terminal payoff moved. -/
def loudInteriorPayoff : Spot → ℝ
  | .flip => 7
  | .pick => 100
  | .grabbed => 1
  | .passed => 0

theorem backwardValue_grab_base :
    probe.backwardValue probe_wellFoundedPlay (policy .grab) basePayoff Spot.flip =
      1 / 2 := by
  rw [backwardValue_flip]
  norm_num [basePayoff, Move.outcome]

theorem backwardValue_grab_raised :
    probe.backwardValue probe_wellFoundedPlay (policy .grab) raisedPayoff Spot.flip =
      1 := by
  rw [backwardValue_flip]
  norm_num [raisedPayoff, Move.outcome]

theorem backwardValue_grab_loudInterior :
    probe.backwardValue probe_wellFoundedPlay (policy .grab) loudInteriorPayoff Spot.flip =
      1 / 2 := by
  rw [backwardValue_flip]
  norm_num [loudInteriorPayoff, Move.outcome]

theorem backwardValue_pass_base :
    probe.backwardValue probe_wellFoundedPlay (policy .pass) basePayoff Spot.flip = 0 := by
  rw [backwardValue_flip]
  norm_num [basePayoff, Move.outcome]

/-! ### The probes -/

/-- **Probe 1.** Changing one terminal successor's payoff changes the root value,
so the value genuinely depends on its successors' values. Kills any
implementation that returns `payoff source`, a constant, or the payoff of the
state it starts at. -/
theorem backwardValue_sensitive_to_successor :
    probe.backwardValue probe_wellFoundedPlay (policy .grab) basePayoff Spot.flip ≠
      probe.backwardValue probe_wellFoundedPlay (policy .grab) raisedPayoff Spot.flip := by
  rw [backwardValue_grab_base, backwardValue_grab_raised]
  norm_num

/-- **Probe 2.** Changing an *interior* state's payoff does not change the root
value, so the recursion really passes through the decision node instead of
stopping after one expectation. Kills a one-step implementation
`expect (step source ..) payoff`, which would report `1/2 * 100 + 1/2 * 0`
under `loudInteriorPayoff`. -/
theorem backwardValue_ignores_interior_payoff :
    probe.backwardValue probe_wellFoundedPlay (policy .grab) basePayoff Spot.flip =
      probe.backwardValue probe_wellFoundedPlay (policy .grab) loudInteriorPayoff
        Spot.flip := by
  rw [backwardValue_grab_base, backwardValue_grab_loudInterior]

/-- **Probe 3.** The value depends on the chooser's answer. Kills any
implementation that consults the chooser and discards the result, or that
manufactures its own legal action from `progress` and `Classical.choice`. -/
theorem backwardValue_sensitive_to_chooser :
    probe.backwardValue probe_wellFoundedPlay (policy .grab) basePayoff Spot.flip ≠
      probe.backwardValue probe_wellFoundedPlay (policy .pass) basePayoff Spot.flip := by
  rw [backwardValue_grab_base, backwardValue_pass_base]
  norm_num

/-- **Probe 4.** The root value is neither terminal payoff, so the recursion
averages rather than selecting a branch. Kills a maximizing or minimizing
implementation as surely as a copying one. -/
theorem backwardValue_flip_ne_terminal_payoffs :
    probe.backwardValue probe_wellFoundedPlay (policy .grab) basePayoff Spot.flip ≠
        basePayoff .grabbed ∧
      probe.backwardValue probe_wellFoundedPlay (policy .grab) basePayoff Spot.flip ≠
        basePayoff .passed := by
  rw [backwardValue_grab_base]
  constructor <;> norm_num [basePayoff]

/-! ### Probe 5: the two evaluators agree

`StopsWithin` is the evaluator half's certificate and `WellFoundedPlay` is this
half's. Discharging both on one game shows they describe one semantics. -/

/-- The probe game has stopped after two steps under either policy. -/
theorem probe_stopsWithin (move : Move) : probe.StopsWithin (policy move) 2 Spot.flip := by
  intro reached hreached
  rw [runFor_succ_of_not_terminal (policy move) 1 flip_not_terminal, step_flip,
    FinDist.support_bind] at hreached
  simp only [Set.mem_iUnion, exists_prop] at hreached
  obtain ⟨spot, hspot, hrun⟩ := hreached
  rcases mem_support_coin hspot with rfl | rfl
  · rw [runFor_succ_of_not_terminal (policy move) 0 pick_not_terminal, step_pick,
      FinDist.pure_bind, runFor_zero, FinDist.mem_support_pure] at hrun
    rw [hrun]
    exact outcome_terminal move
  · rw [runFor_of_terminal (policy move) 1 passed_terminal,
      FinDist.mem_support_pure] at hrun
    rw [hrun]
    exact passed_terminal

/-- Backward induction and the fuelled evaluator compute the same number on the
probe game. -/
theorem expect_runFor_eq_backwardValue (move : Move) (payoff : Spot → ℝ) :
    (probe.runFor (policy move) 2 Spot.flip).expect payoff =
      probe.backwardValue probe_wellFoundedPlay (policy move) payoff Spot.flip :=
  (backwardValue_eq_expect_runFor (probe_stopsWithin move)).symm

/-- Concretely: the run law's expected payoff is the backward-induction value
`1/2`, so probes 1-4 constrain the forward semantics too. -/
theorem expect_runFor_grab_base :
    (probe.runFor (policy .grab) 2 Spot.flip).expect basePayoff = 1 / 2 := by
  rw [expect_runFor_eq_backwardValue, backwardValue_grab_base]

/-! ### The probes have teeth

Each wrong implementation named above is written down here, and the property its
probe asserts of `backwardValue` is *refuted* for it. So probes 1-3 are not
satisfiable by accident: each one separates the real definition from a specific
plausible mistake. -/

/-- Wrong implementation A: stop after a single expectation instead of recursing,
reading `payoff` at the states the first transition reaches. -/
def oneStepValue (chooser : probe.Chooser) (payoff : Spot → ℝ) (source : Spot) : ℝ :=
  if hterm : probe.terminal source then payoff source
  else (probe.step source (chooser source hterm)).expect payoff

theorem oneStepValue_flip (move : Move) (payoff : Spot → ℝ) :
    oneStepValue (policy move) payoff Spot.flip =
      1 / 2 * payoff Spot.pick + 1 / 2 * payoff Spot.passed := by
  unfold oneStepValue
  rw [dif_neg flip_not_terminal, step_flip, expect_coin]

/-- Probe 2 refutes implementation A: it reads the interior payoff, so the two
payoff assignments that differ only at `pick` give `7/2` and `50`. -/
theorem oneStepValue_fails_probe_two :
    oneStepValue (policy .grab) basePayoff Spot.flip ≠
      oneStepValue (policy .grab) loudInteriorPayoff Spot.flip := by
  rw [oneStepValue_flip, oneStepValue_flip]
  norm_num [basePayoff, loudInteriorPayoff]

/-- Wrong implementation B: ignore the successors entirely. -/
def sourceOnlyValue (payoff : Spot → ℝ) (source : Spot) : ℝ := payoff source

/-- Probe 1 refutes implementation B: moving a terminal successor's payoff leaves
it fixed. -/
theorem sourceOnlyValue_fails_probe_one :
    sourceOnlyValue basePayoff Spot.flip = sourceOnlyValue raisedPayoff Spot.flip := rfl

/-- Wrong implementation C: recurse correctly, but discard the chooser's answer
and play a fixed action instead — what a runner built from `progress` and
`Classical.choice` would do. -/
def chooserBlindValue (_chooser : probe.Chooser) (payoff : Spot → ℝ) : Spot → ℝ :=
  probe.backwardValue probe_wellFoundedPlay (policy .grab) payoff

/-- Probe 3 refutes implementation C: both policies get the same number. -/
theorem chooserBlindValue_fails_probe_three :
    chooserBlindValue (policy .grab) basePayoff Spot.flip =
      chooserBlindValue (policy .pass) basePayoff Spot.flip := rfl

end GameTheory.Tests.Backward
