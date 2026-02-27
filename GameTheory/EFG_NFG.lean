import GameTheory.NFG
import GameTheory.EFG

/-!
# EFG → Strategic Form

Three constructions converting an extensive-form game to its strategic form:

1. **`toStrategicKernelGame`** — `KernelGame` preserving outcome distributions.
   Shares `Outcome` and `utility` with the EFG; all `KernelGame` solution
   concepts transfer via a single distribution-equivalence theorem.

2. **`toNFGGame`** — `NFGGame` where chance is absorbed into expected payoffs.
   `Outcome` is `Payoff`, `utility` is `id`. Works for any EFG.

3. **`toNFGGameDet`** — `NFGGame` for deterministic (chance-free) EFGs.
   Shares `Outcome` and `utility` with the EFG.

### Key theorems
- `toStrategicKernelGame_outcomeKernel` — distribution equivalence
- `toNFGGameDet_outcomeKernel` — deterministic NFG matches strategic kernel game
- `pureToBehavioral_update` — behavioral update matches pure update
-/

namespace EFG

open GameTheory

-- ============================================================================
-- Distribution-preserving strategic form (KernelGame)
-- ============================================================================

/-- Strategic form of an EFG as a `KernelGame`, preserving outcome distributions.
    Strategies are pure contingent plans; the outcome kernel evaluates the game
    tree under the corresponding behavioral profile. -/
noncomputable def EFGGame.toStrategicKernelGame (G : EFGGame) :
    KernelGame G.inf.Player where
  Strategy := fun p => PureStrategy G.inf p
  Outcome := G.Outcome
  utility := G.utility
  outcomeKernel := fun σ => G.tree.evalDist (pureToBehavioral σ)

/-- The strategic kernel game produces the same outcome distribution as the
    EFG kernel game under the corresponding behavioral profile.
    Since both games share `Outcome` and `utility`, any property defined on
    `KernelGame` (EU, Nash, dominance, …) transfers automatically. -/
theorem toStrategicKernelGame_outcomeKernel (G : EFGGame) (σ : PureProfile G.inf) :
    G.toStrategicKernelGame.outcomeKernel σ =
    G.toKernelGame.outcomeKernel (pureToBehavioral σ) := by
  rfl

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

-- ============================================================================
-- § 4. pureToBehavioral_update
-- ============================================================================

/-- Updating a pure profile and then lifting to behavioral is the same as
    lifting first and then updating the behavioral profile. -/
theorem pureToBehavioral_update {S : InfoStructure}
    (σ : PureProfile S) (p : S.Player) (s' : PureStrategy S p) :
    pureToBehavioral (Function.update σ p s') =
    Function.update (pureToBehavioral σ) p (fun I => PMF.pure (s' I)) := by
  funext p' I
  by_cases h : p' = p
  · subst h; simp [pureToBehavioral]
  · simp [pureToBehavioral, h]

end EFG
