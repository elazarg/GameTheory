/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.EFG.Syntax

/-!
# EFG Tree Shapes

Tree-shape predicates for `GameTree`.
-/

namespace EFG

/-- Root is `GameTree.chance`. -/
inductive ChanceRoot {S : InfoStructure} {Outcome : Type} :
    GameTree S Outcome → Prop where
  | chance {k : Nat} {μ : PMF (Fin k)} {hk : 0 < k}
      {next : Fin k → GameTree S Outcome} :
      ChanceRoot (GameTree.chance k μ hk next)

/-- Exactly `n` decision layers before a tail tree. -/
inductive DecisionSpineThen {S : InfoStructure} {Outcome : Type}
    (Tail : GameTree S Outcome → Prop) :
    Nat → GameTree S Outcome → Prop where
  | done {tree : GameTree S Outcome} (tail : Tail tree) :
      DecisionSpineThen Tail 0 tree
  | decision {n : Nat} {p : S.Player} {I : S.Infoset p}
      {next : S.Act I → GameTree S Outcome}
      (tail : ∀ action, DecisionSpineThen Tail n (next action)) :
      DecisionSpineThen Tail (n + 1) (GameTree.decision I next)

/-- Exactly `n` decision layers before a chance node. -/
abbrev DecisionSpineThenChance {S : InfoStructure} {Outcome : Type} :
    Nat → GameTree S Outcome → Prop :=
  DecisionSpineThen (S := S) (Outcome := Outcome) ChanceRoot

namespace DecisionSpineThenChance

/-- Zero decision layers before chance. -/
theorem chance {S : InfoStructure} {Outcome : Type}
    {k : Nat} {μ : PMF (Fin k)} {hk : 0 < k}
    {next : Fin k → GameTree S Outcome} :
    DecisionSpineThenChance 0 (GameTree.chance k μ hk next) :=
  DecisionSpineThen.done ChanceRoot.chance

/-- Add one decision layer. -/
theorem decision {S : InfoStructure} {Outcome : Type}
    {n : Nat} {p : S.Player} {I : S.Infoset p}
    {next : S.Act I → GameTree S Outcome}
    (tail : ∀ action, DecisionSpineThenChance n (next action)) :
    DecisionSpineThenChance (n + 1) (GameTree.decision I next) :=
  DecisionSpineThen.decision tail

end DecisionSpineThenChance

mutual

/-- Terminals, or repeated rounds of `players` decisions followed by chance. -/
inductive FullTreeShape {S : InfoStructure} {Outcome : Type}
    (players : Nat) : GameTree S Outcome → Prop where
  | terminal {outcome : Outcome} :
      FullTreeShape players (GameTree.terminal outcome)
  | round {tree : GameTree S Outcome}
      (spine : RoundSpineShape players players tree) :
      FullTreeShape players tree

/-- Decision prefix of a `FullTreeShape` round. -/
inductive RoundSpineShape {S : InfoStructure} {Outcome : Type}
    (players : Nat) : Nat → GameTree S Outcome → Prop where
  | chance {k : Nat} {μ : PMF (Fin k)} {hk : 0 < k}
      {next : Fin k → GameTree S Outcome}
      (tail : ∀ outcome, FullTreeShape players (next outcome)) :
      RoundSpineShape players 0 (GameTree.chance k μ hk next)
  | decision {n : Nat} {p : S.Player} {I : S.Infoset p}
      {next : S.Act I → GameTree S Outcome}
      (tail : ∀ action, RoundSpineShape players n (next action)) :
      RoundSpineShape players (n + 1) (GameTree.decision I next)

end

end EFG
