import GameTheory.NFG
import GameTheory.EFG

/-! ## NFG → EFG: simultaneous game as a sequential tree -/
namespace NFG

/-- Arity function for a 2-player simultaneous game:
    infoSet 0 has `n₁` actions, everything else has `n₂`. -/
@[reducible] private def simArity (n₁ n₂ : Nat) : Nat → Nat
  | 0 => n₁ | _ => n₂

/-- InfoStructure for a 2-player simultaneous game.
    InfoSet 0 → player `p₁` with `n₁` actions,
    InfoSet 1 → player `p₂` with `n₂` actions. -/
def mkSimInfoS {ι : Type} (p₁ p₂ : ι) (n₁ n₂ : Nat)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) : EFG.InfoStructure ι where
  player | 0 => p₁ | _ => p₂
  arity := simArity n₁ n₂
  arity_pos I := by unfold simArity; split <;> omega

/-- Build an EFG tree from an NFG-style payoff function over action indices.
    Player `p₁` moves first (infoSet=0), then player `p₂` (infoSet=1), sequentially. -/
noncomputable def mkSimultaneousTree {ι : Type} (n₁ n₂ : Nat) (p₁ p₂ : ι)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (payoff : Fin n₁ → Fin n₂ → GameTheory.Payoff ι) :
    EFG.GameTree ι (mkSimInfoS p₁ p₂ n₁ n₂ hn₁ hn₂) :=
  .decision 0 (fun a₁ =>
    .decision 1 (fun a₂ =>
      .terminal (payoff a₁ a₂)))

/-- The EFG tree under a pure behavioral strategy produces the correct payoff. -/
theorem mkSimultaneousTree_evalDist {ι : Type} (n₁ n₂ : Nat) (p₁ p₂ : ι)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (payoff : Fin n₁ → Fin n₂ → GameTheory.Payoff ι)
    (a₁ : Fin n₁) (a₂ : Fin n₂)
    (σ : EFG.BehavioralStrategy (mkSimInfoS p₁ p₂ n₁ n₂ hn₁ hn₂))
    (hσ₁ : σ 0 = PMF.pure a₁) (hσ₂ : σ 1 = PMF.pure a₂) :
    (mkSimultaneousTree n₁ n₂ p₁ p₂ hn₁ hn₂ payoff).evalDist σ =
    PMF.pure (payoff a₁ a₂) := by
  simp [mkSimultaneousTree, EFG.GameTree.evalDist, hσ₁, hσ₂]

end NFG
