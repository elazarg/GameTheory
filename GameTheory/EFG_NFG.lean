import GameTheory.NFG
import GameTheory.EFG

/-!
# EFG → Strategic Form

Three constructions converting an extensive-form game to its strategic form:

1. **`toNFGGame`** — `NFGGame` where chance is absorbed into expected payoffs.
   `Outcome` is `Payoff`, `utility` is `id`. Works for any EFG.

2. **`toNFGGameDet`** — `NFGGame` for deterministic (chance-free) EFGs.
   Shares `Outcome` and `utility` with the EFG.

### Key theorems
- `toNFGGameDet_outcomeKernel` — deterministic NFG matches strategic kernel game
-/

namespace EFG

open GameTheory

-- ============================================================================
-- § 2. Deterministic strategic form (NFGGame)
-- ============================================================================

/-- Strategic form of an EFG as an `NFGGame`. Chance is absorbed into expected
    payoffs: the outcome of a pure-strategy profile is its expected payoff vector,
    and `utility` is the identity. -/
noncomputable def EFGGame.toNFGGame (G : EFGGame) :
    NFG.NFGGame G.inf.Player (fun p => PureStrategy G.inf p) where
  Outcome := Payoff G.inf.Player
  outcome := fun σ p =>
    expect (G.tree.evalDist (pureToBehavioral σ)) (fun ω => G.utility ω p)
  utility := id

-- ============================================================================
-- § 3. Deterministic strategic form (NFGGame preserving Outcome)
-- ============================================================================

/-- Strategic form of a deterministic (chance-free) EFG as an `NFGGame`.
    Shares `Outcome` and `utility` with the EFG; the outcome function is
    the deterministic tree evaluation `evalPure`. -/
def EFGGame.toNFGGameDet (G : EFGGame) (_hd : IsDeterministic G.tree) :
    NFG.NFGGame G.inf.Player (fun p => PureStrategy G.inf p) where
  Outcome := G.Outcome
  outcome := G.tree.evalPure
  utility := G.utility

/-- For a deterministic EFG, the deterministic NFG's kernel game produces
    the same outcome distribution as the EFG's strategic kernel game. -/
theorem toNFGGameDet_outcomeKernel (G : EFGGame) (hd : IsDeterministic G.tree)
    (σ : PureProfile G.inf) :
    (G.toNFGGameDet hd).toKernelGame.outcomeKernel σ =
    G.toStrategicKernelGame.outcomeKernel σ :=
  (evalDist_pureToBehavioral_eq_pure G.tree σ hd).symm

/-- Semantics equality for deterministic EFG → NFG bridge. -/
theorem toNFGGameDet_semantics_eq (G : EFGGame) (hd : IsDeterministic G.tree)
    (σ : PureProfile G.inf) :
    (G.toNFGGameDet hd).toKernelGame.outcomeKernel σ =
    G.toStrategicKernelGame.outcomeKernel σ :=
  toNFGGameDet_outcomeKernel G hd σ

end EFG
