/-
# The two execution presentations on one game

The same game — a fair coin, then one consequential decision — encoded twice:
once as a general-state `ExecutionProtocol` (in `GameTheory.Tests.Execution`)
and once as a finite-first `Tree`. What separates them is what each needs in
order to produce an outcome law and a strategy type.

Three probes, all built in up front:

* **agreement** — the two induce the *same* outcome law, so neither
  is quietly modelling a different game;
* **discrimination** — in both, the law depends on the chosen action,
  so neither test would pass an evaluator that discarded the strategy;
* **cost** — the finite-first evaluator is structural, while the general-state
  runner needs a fuel argument plus a `StopsWithin` certificate to become a
  total evaluator. The certificate is exhibited.
-/

import GameTheory.Protocol.Tree
import GameTheory.Tests.Execution

noncomputable section

namespace GameTheory.Tests

open GameTheory GameTheory.Protocol GameTheory.Probability

/-! ## The general-state presentation: full outcome laws

`GameTheory.Tests.Execution` proved the two policies differ. Here are the laws
themselves, which is what the tree must reproduce. -/

theorem runFor_two_take :
    coinThenMove.runFor takePolicy 2 .chance = FinDist.pure .tookIt := by
  refine FinDist.ext_of_prob fun spot => ?_
  rw [ExecutionProtocol.runFor_succ_of_chance takePolicy 1 coinThenMove_chance_isChance,
    FinDist.prob_bind, ExecutionProtocol.chanceLaw]
  show (FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure Spot.heads) (FinDist.pure Spot.tails)).expect
      (fun s => (coinThenMove.runFor takePolicy 1 s).prob spot) = _
  rw [FinDist.expect_mix, FinDist.expect_pure, FinDist.expect_pure,
    runFor_one_heads_take, runFor_one_tails_take]
  ring

theorem runFor_two_leave :
    coinThenMove.runFor leavePolicy 2 .chance = FinDist.pure .leftIt := by
  refine FinDist.ext_of_prob fun spot => ?_
  rw [ExecutionProtocol.runFor_succ_of_chance leavePolicy 1 coinThenMove_chance_isChance,
    FinDist.prob_bind, ExecutionProtocol.chanceLaw]
  show (FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure Spot.heads) (FinDist.pure Spot.tails)).expect
      (fun s => (coinThenMove.runFor leavePolicy 1 s).prob spot) = _
  rw [FinDist.expect_mix, FinDist.expect_pure, FinDist.expect_pure,
    runFor_one_heads_leave, runFor_one_tails_leave]
  ring

/-! ## Cost of the general-state presentation: a bounded-horizon certificate

`runFor` is fuelled, so it is not yet an evaluator. `StopsWithin` is the
certificate that makes it one, and it is small: one support computation. -/

theorem takePolicy_stopsWithin : coinThenMove.StopsWithin takePolicy 2 .chance := by
  intro reached hreached
  rw [runFor_two_take] at hreached
  rw [FinDist.mem_support_pure.1 hreached]
  simp

/-- With the certificate, extra fuel is provably irrelevant: the fuelled runner
becomes a total evaluator. -/
theorem runFor_take_stable {fuel : ℕ} (hfuel : 2 ≤ fuel) :
    coinThenMove.runFor takePolicy fuel .chance = FinDist.pure .tookIt := by
  rw [ExecutionProtocol.runFor_eq_of_stopsWithin_le takePolicy_stopsWithin hfuel,
    runFor_two_take]

/-! ## The finite-first presentation: the same game as a tree -/

/-- The fair coin as a law over branches. -/
def fairCoin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure true) (FinDist.pure false)

/-- After the coin, the player moves and the move decides the outcome. -/
def coinBranch : Tree Unit (fun _ => Move) Spot :=
  .node () fun move => .leaf move.resolve

/-- The whole game: a coin, then the decision, on either side. -/
def coinTree : Tree Unit (fun _ => Move) Spot := .chance fairCoin coinBranch coinBranch

/-- Taking, as a contingent plan for one branch. -/
def takeBranchPlan : Tree.PureStrategy coinBranch := (.take, fun _ => PUnit.unit)

/-- Leaving, as a contingent plan for one branch. -/
def leaveBranchPlan : Tree.PureStrategy coinBranch := (.leave, fun _ => PUnit.unit)

/-- Take on both sides of the coin. -/
def takePlan : Tree.PureStrategy coinTree := (takeBranchPlan, takeBranchPlan)

/-- Leave on both sides of the coin. -/
def leavePlan : Tree.PureStrategy coinTree := (leaveBranchPlan, leaveBranchPlan)

theorem eval_coinBranch_take :
    Tree.eval coinBranch takeBranchPlan = FinDist.pure .tookIt := rfl

theorem eval_coinBranch_leave :
    Tree.eval coinBranch leaveBranchPlan = FinDist.pure .leftIt := rfl

theorem eval_coinTree_take : Tree.eval coinTree takePlan = FinDist.pure .tookIt := by
  show fairCoin.bind (fun branch =>
    if branch then Tree.eval coinBranch takeBranchPlan
    else Tree.eval coinBranch takeBranchPlan) = _
  rw [eval_coinBranch_take]
  simp

theorem eval_coinTree_leave : Tree.eval coinTree leavePlan = FinDist.pure .leftIt := by
  show fairCoin.bind (fun branch =>
    if branch then Tree.eval coinBranch leaveBranchPlan
    else Tree.eval coinBranch leaveBranchPlan) = _
  rw [eval_coinBranch_leave]
  simp

/-! ## Probe 1: the two agree

Neither presentation is quietly modelling a different game. -/

theorem candidates_agree_take :
    Tree.eval coinTree takePlan = coinThenMove.runFor takePolicy 2 .chance := by
  rw [eval_coinTree_take, runFor_two_take]

theorem candidates_agree_leave :
    Tree.eval coinTree leavePlan = coinThenMove.runFor leavePolicy 2 .chance := by
  rw [eval_coinTree_leave, runFor_two_leave]

/-! ## Probe 2: the tree candidate is also sensitive to the plan

The same hole that review found in the protocol slice would be invisible here
without this. An evaluator that ignored the contingent plan would make the two
plans agree. -/

theorem takePlan_ne_leavePlan :
    Tree.eval coinTree takePlan ≠ Tree.eval coinTree leavePlan := by
  rw [eval_coinTree_take, eval_coinTree_leave]
  intro hequal
  have hmass := congrArg (fun law => FinDist.prob law Spot.tookIt) hequal
  simp [FinDist.prob_pure_eq_ite] at hmass

/-! ## Probe 3: hostile test 5, the extracted strategy type is finite

Finiteness comes from the *local* action carriers, over the tree's own decision
sites. -/

instance : Fintype Move := ⟨{.take, .leave}, by intro m; cases m <;> simp⟩

example : Fintype (Tree.PureStrategy coinTree) := inferInstance

/-- Four contingent plans: one action on each side of the coin. -/
theorem card_pureStrategy_coinTree : Fintype.card (Tree.PureStrategy coinTree) = 4 := by
  rfl

end GameTheory.Tests
