import GameTheory.NFG
import GameTheory.EFG

/-! ## NFG → EFG: simultaneous game as a sequential tree -/
namespace NFG

open EFG

/-- InfoStructure for a 2-player simultaneous game.
    Each player has one info set (Unit). Player 0 has `n₁` actions, player 1 has `n₂`. -/
@[reducible] def mkSimInfoS (n₁ n₂ : Nat) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) : InfoStructure where
  n := 2
  Infoset := fun _ => Unit
  arity := fun p _ => match p.val with | 0 => n₁ | _ => n₂
  arity_pos := fun p _ => by fin_cases p <;> assumption

/-- Build an EFG tree from an NFG-style payoff function over action indices.
    Player 0 moves first (info set ()), then player 1 (info set ()), sequentially. -/
noncomputable def mkSimultaneousTree (n₁ n₂ : Nat)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    {Outcome : Type}
    (payoff : Fin n₁ → Fin n₂ → Outcome) :
    GameTree (mkSimInfoS n₁ n₂ hn₁ hn₂) Outcome :=
  .decision (p := (0 : Fin 2)) () (fun a₁ =>
    .decision (p := (1 : Fin 2)) () (fun a₂ =>
      .terminal (payoff a₁ a₂)))

/-- The EFG tree under a pure behavioral profile produces the correct payoff. -/
theorem mkSimultaneousTree_evalDist (n₁ n₂ : Nat)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    {Outcome : Type}
    (payoff : Fin n₁ → Fin n₂ → Outcome)
    (a₁ : Fin n₁) (a₂ : Fin n₂)
    (σ : BehavioralProfile (mkSimInfoS n₁ n₂ hn₁ hn₂))
    (hσ₁ : σ 0 () = PMF.pure a₁) (hσ₂ : σ 1 () = PMF.pure a₂) :
    (mkSimultaneousTree n₁ n₂ hn₁ hn₂ payoff).evalDist σ =
    PMF.pure (payoff a₁ a₂) := by
  simp [mkSimultaneousTree, GameTree.evalDist, hσ₁, hσ₂]

end NFG
