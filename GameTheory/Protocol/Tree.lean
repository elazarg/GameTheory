/-
# Finite game trees

A presentation in which inductive trees are primary and evaluation is structural
rather than fuelled. It is faithful only for single-mover games; see
`GameTheory.Protocol.Execution` for the general interface.

Two properties are what it buys.

* Evaluation needs no fuel and no horizon certificate — `eval` is structural
  recursion, total by construction.
* The extracted strategy type is indexed by the tree's *own* decision sites,
  because `PureStrategy` is defined by recursion on the tree. It is finite as
  soon as the local action carriers are.

Chance is a binary node carrying a `FinDist Bool`, so a chance law is
normalized by construction and no proof obligation is stored in the
constructor.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι ua uo

variable {ι : Type uι} {Action : ι → Type ua} {Outcome : Type uo}

/-- A finite game tree: an outcome, a binary chance node, or a decision node. -/
inductive Tree (ι : Type uι) (Action : ι → Type ua) (Outcome : Type uo) :
    Type (max uι ua uo)
  | /-- Play stops with this outcome. -/
    leaf (outcome : Outcome) : Tree ι Action Outcome
  | /-- Nature picks a branch according to a normalized law. -/
    chance (law : FinDist Bool) (whenTrue whenFalse : Tree ι Action Outcome) :
      Tree ι Action Outcome
  | /-- `mover` chooses, and play continues in the corresponding subtree. -/
    node (mover : ι) (child : Action mover → Tree ι Action Outcome) :
      Tree ι Action Outcome

namespace Tree

/-- A contingent plan for a tree: an action at every decision site the tree
actually has, and nothing else. Defined by recursion on the tree, so it cannot
mention a node the tree does not contain. -/
@[reducible]
def PureStrategy : Tree ι Action Outcome → Type (max uι ua)
  | .leaf _ => PUnit
  | .chance _ whenTrue whenFalse => PureStrategy whenTrue × PureStrategy whenFalse
  | .node mover child => Action mover × ((a : Action mover) → PureStrategy (child a))

/-- The outcome law of a strategy. Structural recursion: no fuel, no horizon
certificate, and no partiality. -/
def eval : (tree : Tree ι Action Outcome) → PureStrategy tree → FinDist Outcome
  | .leaf outcome, _ => FinDist.pure outcome
  | .chance law whenTrue whenFalse, plan =>
      law.bind fun branch =>
        if branch then eval whenTrue plan.1 else eval whenFalse plan.2
  | .node _ child, plan => eval (child plan.1) (plan.2 plan.1)

@[simp]
theorem eval_leaf (outcome : Outcome)
    (plan : PureStrategy (Tree.leaf (ι := ι) (Action := Action) outcome)) :
    eval (.leaf outcome) plan = FinDist.pure outcome := rfl

@[simp]
theorem eval_chance (law : FinDist Bool) (whenTrue whenFalse : Tree ι Action Outcome)
    (plan : PureStrategy (.chance law whenTrue whenFalse)) :
    eval (.chance law whenTrue whenFalse) plan =
      law.bind fun branch =>
        if branch then eval whenTrue plan.1 else eval whenFalse plan.2 := rfl

@[simp]
theorem eval_node (mover : ι) (child : Action mover → Tree ι Action Outcome)
    (plan : PureStrategy (.node mover child)) :
    eval (.node mover child) plan = eval (child plan.1) (plan.2 plan.1) := rfl

/-! ## Hostile test: the extracted strategy type is genuinely finite

Finiteness of the plan type follows from finiteness of the *local* action
carriers, by induction over the tree's own structure. -/

/-- The enumeration of contingent plans, built over the tree's decision
sites. -/
@[reducible]
def pureStrategyFintype [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)] :
    (tree : Tree ι Action Outcome) → Fintype (PureStrategy tree)
  | .leaf _ => inferInstanceAs (Fintype PUnit)
  | .chance _ whenTrue whenFalse =>
      letI := pureStrategyFintype whenTrue
      letI := pureStrategyFintype whenFalse
      inferInstanceAs (Fintype (PureStrategy whenTrue × PureStrategy whenFalse))
  | .node mover child =>
      letI (a : Action mover) := pureStrategyFintype (child a)
      inferInstanceAs
        (Fintype (Action mover × ((a : Action mover) → PureStrategy (child a))))

instance instFintypePureStrategy [∀ i, Fintype (Action i)] [∀ i, DecidableEq (Action i)]
    (tree : Tree ι Action Outcome) : Fintype (PureStrategy tree) :=
  pureStrategyFintype tree

end Tree

end GameTheory.Protocol
