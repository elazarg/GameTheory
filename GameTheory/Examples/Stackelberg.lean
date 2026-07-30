/-
# Stackelberg commitment through the sequential layer

The leader-follower presentation is a finite `Protocol.Tree`. Its plan type
stores a leader commitment and a follower action after every possible
commitment. The underlying simultaneous game is independently presented as a
`TableGame`, so its equilibrium statement uses the canonical static `IsNash`
predicate.

This replaces the pinned v1 `StackelbergGame` structure and its parallel
solution predicates with two already validated semantic roots.
-/

import GameTheory.Finite.Correctness
import GameTheory.Protocol.Tree
import Mathlib.Tactic.DeriveFintype

namespace GameTheory.Examples.Stackelberg

open GameTheory GameTheory.Finite GameTheory.Probability GameTheory.Protocol

/-- A maximizing commitment beats any comparison whose recorded response is
the response function's value there. This is the mathematical payload of v1's
generic leader-payoff projection, without a parallel game structure. -/
theorem leaderPayoff_ge_of_maximizes {Leader Follower : Type}
    (payoff : Leader → Follower → ℝ) (response : Leader → Follower)
    (chosen comparison : Leader) (comparisonResponse : Follower)
    (hmaximizes : ∀ alternative,
      payoff alternative (response alternative) ≤
        payoff chosen (response chosen))
    (hresponse : response comparison = comparisonResponse) :
    payoff comparison comparisonResponse ≤ payoff chosen (response chosen) := by
  rw [← hresponse]
  exact hmaximizes comparison

/-- Two best responses coincide when the designated response is unique. This
retains v1's generic uniqueness lemma independently of any game wrapper. -/
theorem response_eq_of_unique {Leader Follower : Type}
    (payoff : Leader → Follower → ℝ) (response : Leader → Follower)
    (commitment : Leader) (candidate : Follower)
    (hresponse : ∀ alternative,
      payoff commitment alternative ≤ payoff commitment (response commitment))
    (hcandidate : ∀ alternative,
      payoff commitment alternative ≤ payoff commitment candidate)
    (hunique : ∀ alternative,
      payoff commitment candidate ≤ payoff commitment alternative →
      payoff commitment alternative ≤ payoff commitment candidate →
      alternative = candidate) :
    response commitment = candidate :=
  hunique (response commitment) (hresponse candidate)
    (hcandidate (response commitment))

/-- The two strategic roles. -/
inductive Player
  | leader
  | follower
  deriving DecidableEq, Fintype, Repr

/-- The incumbent's commitment. -/
inductive LeaderAction
  | fight
  | accommodate
  deriving DecidableEq, Fintype, Repr

/-- The entrant's response. -/
inductive FollowerAction
  | enter
  | stayOut
  deriving DecidableEq, Fintype, Repr

/-- Each role has its own action carrier. -/
def Action : Player → Type
  | .leader => LeaderAction
  | .follower => FollowerAction

instance (who : Player) : Fintype (Action who) := by
  cases who <;> simp [Action] <;> infer_instance

instance (who : Player) : DecidableEq (Action who) := by
  cases who <;> simp [Action] <;> infer_instance

/-- The realized commitment and response. -/
structure Outcome where
  leader : LeaderAction
  follower : FollowerAction
  deriving DecidableEq, Repr

/-- Incumbent payoff. -/
def leaderPayoff : LeaderAction → FollowerAction → ℚ
  | .fight, .enter => 0
  | .fight, .stayOut => 2
  | .accommodate, .enter => 1
  | .accommodate, .stayOut => 2

/-- Entrant payoff. -/
def followerPayoff : LeaderAction → FollowerAction → ℚ
  | .fight, .enter => -1
  | .fight, .stayOut => 0
  | .accommodate, .enter => 1
  | .accommodate, .stayOut => 0

/-- The entrant stays out after a threat to fight and enters after
accommodation. -/
def followerResponse : LeaderAction → FollowerAction
  | .fight => .stayOut
  | .accommodate => .enter

@[simp]
theorem followerResponse_accommodate :
    followerResponse .accommodate = .enter := rfl

/-- The follower response is optimal after every possible commitment. -/
theorem followerResponse_optimal (commitment : LeaderAction)
    (alternative : FollowerAction) :
    followerPayoff commitment alternative ≤
      followerPayoff commitment (followerResponse commitment) := by
  cases commitment <;> cases alternative <;>
    norm_num [followerPayoff, followerResponse]

/-- The best response is unique at each commitment in this example. -/
theorem followerResponse_unique (commitment : LeaderAction)
    (candidate : FollowerAction)
    (hbest : ∀ alternative,
      followerPayoff commitment alternative ≤
        followerPayoff commitment candidate) :
    candidate = followerResponse commitment := by
  cases commitment with
  | fight =>
      cases candidate with
      | enter =>
          have h := hbest .stayOut
          norm_num [followerPayoff] at h
      | stayOut => rfl
  | accommodate =>
      cases candidate with
      | enter => rfl
      | stayOut =>
          have h := hbest .enter
          norm_num [followerPayoff] at h

/-- Entry deterrence as a two-stage finite tree. -/
def entryTree : Tree Player Action Outcome :=
  .node .leader fun commitment =>
    .node .follower fun response =>
      .leaf ⟨commitment, response⟩

/-- A plan that commits to `commitment` and uses the follower's contingent
best response at either follower decision node. -/
def entryPlan (commitment : LeaderAction) : Tree.PureStrategy entryTree :=
  (commitment, fun observed =>
    (followerResponse observed, fun _ => PUnit.unit))

/-- Structural tree evaluation realizes the committed action and its response.
No separate Stackelberg evaluator is introduced. -/
theorem eval_entryPlan (commitment : LeaderAction) :
    Tree.eval entryTree (entryPlan commitment) =
      FinDist.pure ⟨commitment, followerResponse commitment⟩ := rfl

/-- The leader's value after the follower best-responds. -/
def commitmentValue (commitment : LeaderAction) : ℚ :=
  leaderPayoff commitment (followerResponse commitment)

/-- Fighting maximizes the leader's payoff over all commitments. -/
theorem fight_maximizes_commitment (alternative : LeaderAction) :
    commitmentValue alternative ≤ commitmentValue .fight := by
  cases alternative <;>
    norm_num [commitmentValue, leaderPayoff, followerResponse]

/-- The underlying simultaneous entry-deterrence game. -/
def simultaneousGame : TableGame Player where
  Action := Action
  actionFintype := inferInstance
  actionDecEq := inferInstance
  payoff profile
    | .leader => leaderPayoff (profile .leader) (profile .follower)
    | .follower => followerPayoff (profile .leader) (profile .follower)

/-- The simultaneous profile where the incumbent accommodates and the entrant
enters. -/
def accommodateEnter : Profile simultaneousGame.sig
  | .leader => .accommodate
  | .follower => .enter

/-- The simultaneous profile where the incumbent fights and the entrant stays
out. -/
def fightStayOut : Profile simultaneousGame.sig
  | .leader => .fight
  | .follower => .stayOut

#guard simultaneousGame.enumerateNash.card = 2
#guard simultaneousGame.isNash accommodateEnter
#guard simultaneousGame.isNash fightStayOut

/-- Accommodation and entry form a Nash equilibrium of the simultaneous
presentation. -/
theorem accommodateEnter_isNash :
    IsNash simultaneousGame.toForm (euPreference simultaneousGame.utility)
      accommodateEnter := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-- Fight and stay out form the second, weak simultaneous Nash equilibrium. -/
theorem fightStayOut_isNash :
    IsNash simultaneousGame.toForm (euPreference simultaneousGame.utility)
      fightStayOut := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-- Commitment to fight yields strictly more than the leader receives at the
accommodation-entry simultaneous equilibrium. -/
theorem leaderAdvantage_strict :
    commitmentValue .fight >
      simultaneousGame.payoff accommodateEnter .leader := by
  change (2 : ℚ) > 1
  norm_num

/-- The weak leader-advantage statement follows from the strict comparison. -/
theorem leaderAdvantage :
    commitmentValue .fight ≥
      simultaneousGame.payoff accommodateEnter .leader :=
  leaderAdvantage_strict.le

end GameTheory.Examples.Stackelberg
