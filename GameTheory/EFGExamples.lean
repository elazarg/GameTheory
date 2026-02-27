import Mathlib.Probability.ProbabilityMassFunction.Constructions

import GameTheory.EFG

/-!
# EFG Examples

Example extensive-form game trees with evaluation and perfect recall proofs.
-/

namespace EFG

open GameTheory

/-! ## InfoStructures for the examples -/

/-- 2-player, each player has one infoset with 2 actions. -/
abbrev twoPlayerS : InfoStructure where
  n := 2
  Infoset := fun _ => Unit
  arity := fun _ _ => 2
  arity_pos := fun _ _ => by omega

/-- 1-player, one infoset with 2 actions. -/
abbrev onePlayerS : InfoStructure where
  n := 1
  Infoset := fun _ => Unit
  arity := fun _ _ => 2
  arity_pos := fun _ _ => by omega

/-! ## Example trees -/

/-- Sequential game: P0 picks L/R, then P1 picks L/R.
    Payoffs: (LL)=(3,3), (LR)=(0,0), (RL)=(0,0), (RR)=(1,1) -/
noncomputable abbrev seqTree : GameTree twoPlayerS (Payoff twoPlayerS.Player) :=
  .decision (p := (0 : Fin 2)) () fun
    | 0 => .decision (p := (1 : Fin 2)) () fun
      | 0 => .terminal (fun i => if i == (0 : Fin 2) then 3 else 3)
      | 1 => .terminal (fun i => if i == (0 : Fin 2) then 0 else 0)
    | 1 => .decision (p := (1 : Fin 2)) () fun
      | 0 => .terminal (fun i => if i == (0 : Fin 2) then 0 else 0)
      | 1 => .terminal (fun i => if i == (0 : Fin 2) then 1 else 1)

/-- Matching pennies: P0 picks H(0)/T(1), P1 picks H(0)/T(1).
    P1 cannot observe P0's choice (same infoSet = imperfect info). -/
noncomputable abbrev matchingPenniesTree : GameTree twoPlayerS (Payoff twoPlayerS.Player) :=
  .decision (p := (0 : Fin 2)) () fun
    | 0 => .decision (p := (1 : Fin 2)) () fun
      | 0 => .terminal (fun i => if i == (0 : Fin 2) then 1 else -1)
      | 1 => .terminal (fun i => if i == (0 : Fin 2) then -1 else 1)
    | 1 => .decision (p := (1 : Fin 2)) () fun
      | 0 => .terminal (fun i => if i == (0 : Fin 2) then -1 else 1)
      | 1 => .terminal (fun i => if i == (0 : Fin 2) then 1 else -1)

/-- Uniform PMF on `Fin 2` (coin flip). -/
noncomputable def coinFlip : PMF (Fin 2) :=
  PMF.ofFintype (fun _ => (2 : ENNReal)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))

/-- Hidden decision: chance 50/50, then P0 guesses blind.
    Same infoSet in both branches = imperfect info. -/
noncomputable abbrev hiddenDecTree : GameTree onePlayerS (Payoff onePlayerS.Player) :=
  .chance 2 coinFlip (by omega) fun
    | 0 => .decision (p := (0 : Fin 1)) () fun
      | 0 => .terminal (fun _ => 1)
      | 1 => .terminal (fun _ => 0)
    | 1 => .decision (p := (0 : Fin 1)) () fun
      | 0 => .terminal (fun _ => 0)
      | 1 => .terminal (fun _ => 1)

/-! ## WFTree proofs -/

theorem seqTree_wf : WFTree seqTree := allWFTree seqTree
theorem matchingPenniesTree_wf : WFTree matchingPenniesTree := allWFTree matchingPenniesTree
theorem hiddenDecTree_wf : WFTree hiddenDecTree := allWFTree hiddenDecTree

/-! ## EU proofs (via KernelGame) -/

/-- Strategy profile: always pick the first action. -/
def alwaysFirst : PureProfile twoPlayerS :=
  fun _ _ => ⟨0, twoPlayerS.arity_pos _ _⟩

/-- Strategy profile: always pick the last action. -/
def alwaysLast : PureProfile twoPlayerS :=
  fun p I => ⟨twoPlayerS.arity p I - 1,
   Nat.sub_lt (twoPlayerS.arity_pos p I) Nat.one_pos⟩

/-- The sequential game as an `EFGGame`. -/
noncomputable def seqGame : EFGGame where
  inf := twoPlayerS
  Outcome := Payoff twoPlayerS.Player
  tree := seqTree
  utility := id

/-- Under alwaysFirst, seqGame yields EU 3 for P0. -/
private noncomputable example :
    seqGame.toKernelGame.eu (pureToBehavioral alwaysFirst) (0 : Fin 2) = 3 := by
  simp [KernelGame.eu, EFGGame.toKernelGame, seqGame,
        GameTree.evalDistProfile, GameTree.evalDist,
        pureToBehavioral, alwaysFirst, twoPlayerS, expect_pure]

/-- Under alwaysLast, seqGame yields EU 1 for P0. -/
private noncomputable example :
    seqGame.toKernelGame.eu (pureToBehavioral alwaysLast) (0 : Fin 2) = 1 := by
  simp [KernelGame.eu, EFGGame.toKernelGame, seqGame,
        GameTree.evalDistProfile, GameTree.evalDist,
        pureToBehavioral, alwaysLast, twoPlayerS, expect_pure]

/-! ## Perfect recall proofs

For these small trees, perfect recall is proved by exhaustive case analysis
on `ReachBy` paths. Each info set appears at most once per root-to-leaf
path, so any two paths to the same info set have identical player
histories. -/

/-- Helper: in seqTree, all playerHistories to any reachable decision node are []. -/
private theorem seqTree_playerHistory_nil :
    ∀ h {p : twoPlayerS.Player} (I : twoPlayerS.Infoset p)
    (next : twoPlayerS.Act I → GameTree twoPlayerS (Payoff twoPlayerS.Player)),
    ReachBy h seqTree (.decision I next) →
    playerHistory twoPlayerS p h = [] := by
  intro h p I next hr
  -- seqTree is .decision (p:=0) () f
  rcases ReachBy_decision_inv hr with ⟨rfl, rfl, _, _⟩ | ⟨a, rest, rfl, hr'⟩
  · -- h = [], playerHistory _ _ [] = []
    rfl
  · -- h = .action 0 () a.val :: rest
    fin_cases a <;> (
      rcases ReachBy_decision_inv hr' with ⟨rfl, rfl, _, _⟩ | ⟨b, rest', rfl, hr''⟩
      · -- rest = [], I = player 1's infoset
        -- playerHistory twoPlayerS 1 [.action 0 () _] → 0 ≠ 1, filtered → []
        simp [playerHistory]
      · -- from terminal to decision — impossible
        fin_cases b <;> nomatch hr'')

/-- seqTree has perfect recall. -/
theorem seqTree_perfectRecall : PerfectRecall seqTree := by
  intro h₁ h₂ p I next₁ next₂ hr₁ hr₂
  rw [seqTree_playerHistory_nil h₁ I next₁ hr₁,
      seqTree_playerHistory_nil h₂ I next₂ hr₂]

/-- Helper: in matchingPenniesTree, all playerHistories to any reachable decision node are []. -/
private theorem mpTree_playerHistory_nil :
    ∀ h {p : twoPlayerS.Player} (I : twoPlayerS.Infoset p)
    (next : twoPlayerS.Act I → GameTree twoPlayerS (Payoff twoPlayerS.Player)),
    ReachBy h matchingPenniesTree (.decision I next) →
    playerHistory twoPlayerS p h = [] := by
  intro h p I next hr
  rcases ReachBy_decision_inv hr with ⟨rfl, rfl, _, _⟩ | ⟨a, rest, rfl, hr'⟩
  · rfl
  · fin_cases a <;> (
      rcases ReachBy_decision_inv hr' with ⟨rfl, rfl, _, _⟩ | ⟨b, rest', rfl, hr''⟩
      · simp [playerHistory]
      · fin_cases b <;> nomatch hr'')

/-- matchingPenniesTree has perfect recall. -/
theorem matchingPenniesTree_perfectRecall :
    PerfectRecall matchingPenniesTree := by
  intro h₁ h₂ p I next₁ next₂ hr₁ hr₂
  rw [mpTree_playerHistory_nil h₁ I next₁ hr₁,
      mpTree_playerHistory_nil h₂ I next₂ hr₂]

/-- Helper: in hiddenDecTree, all playerHistories to any reachable decision node are []. -/
private theorem hdTree_playerHistory_nil :
    ∀ h {p : onePlayerS.Player} (I : onePlayerS.Infoset p)
    (next : onePlayerS.Act I → GameTree onePlayerS (Payoff onePlayerS.Player)),
    ReachBy h hiddenDecTree (.decision I next) →
    playerHistory onePlayerS p h = [] := by
  intro h p I next hr
  -- hiddenDecTree is .chance 2 coinFlip _ f
  rcases ReachBy_chance_inv' hr with ⟨b, rest, rfl, hr'⟩
  -- hr' : ReachBy rest (f b) (.decision I next), f b is .decision (p:=0) () _
  fin_cases b <;> (
    rcases ReachBy_decision_inv hr' with ⟨rfl, rfl, _, _⟩ | ⟨a, rest', rfl, hr''⟩
    · -- rest = [], h = [.chance _]
      -- playerHistory _ _ [.chance _] = [] (chance steps filtered)
      simp [playerHistory]
    · -- from terminal to decision — impossible
      fin_cases a <;> nomatch hr'')

/-- hiddenDecTree has perfect recall. -/
theorem hiddenDecTree_perfectRecall :
    PerfectRecall hiddenDecTree := by
  intro h₁ h₂ p I next₁ next₂ hr₁ hr₂
  rw [hdTree_playerHistory_nil h₁ I next₁ hr₁,
      hdTree_playerHistory_nil h₂ I next₂ hr₂]

end EFG
