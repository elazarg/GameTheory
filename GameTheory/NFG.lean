import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Constructions

import GameTheory.KernelGame
import GameTheory.Probability
import GameTheory.PMFProduct
import GameTheory.SolutionConcepts

/-!
# Normal-Form Games (NFG)

Finite normal-form (strategic-form) games with pure strategies,
Nash equilibrium, and dominance.

Provides:
- `NFGame` — finite normal-form game structure
- `IsNashPure`, `IsDominant`, `dominant_is_nash` — pure solution concepts
- `toKernelGame` — bridge to `KernelGame`
- `IsNashPure_iff_kernelGame`, `IsDominant_iff_kernelGame` — bridge theorems
- `pmfPi` — independent product of PMFs (for mixed strategies)
- `toMixedKernelGame`, `IsNashMixed` — mixed strategy Nash
- `mkSimultaneousTree` — NFG → EFG embedding
-/

namespace NFG

/-- A finite normal-form game.
  - `ι` is the type of players
  - `A i` is the type of actions for player `i`
  - `payoff s i` is the payoff to player `i` under strategy profile `s` -/
structure NFGame (ι : Type) [Fintype ι] [DecidableEq ι]
    (A : ι → Type) [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] where
  payoff : (∀ i, A i) → ι → ℝ

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- A (pure) strategy profile: each player picks an action. -/
abbrev StrategyProfile (A : ι → Type) := ∀ i, A i

/-- Deviate: replace player `i`'s action in profile `s` with `a`.
    This is `Function.update` kept for NFG readability. -/
def deviate (s : StrategyProfile A) (i : ι) (a : A i) : StrategyProfile A :=
  Function.update s i a

omit [Fintype ι] [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] in
@[simp]
theorem deviate_same (s : StrategyProfile A) (i : ι) (a : A i) :
    deviate s i a i = a := by
  simp [deviate]

omit [Fintype ι] [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] in
@[simp]
theorem deviate_other (s : StrategyProfile A) (i j : ι) (a : A i) (h : j ≠ i) :
    deviate s i a j = s j := by
  simp [deviate, h]

/-- A pure Nash equilibrium: no player can improve by unilateral deviation. -/
def IsNashPure (G : NFGame ι A) (s : StrategyProfile A) : Prop :=
  ∀ i (a' : A i), G.payoff s i ≥ G.payoff (deviate s i a') i

/-- Action `a` is dominant for player `i`: regardless of others' actions,
    `a` yields at least as high a payoff as any alternative. -/
def IsDominant (G : NFGame ι A) (i : ι) (a : A i) : Prop :=
  ∀ (s : StrategyProfile A) (a' : A i),
    G.payoff (deviate s i a) i ≥ G.payoff (deviate s i a') i

/-- If every player has a dominant action, the profile of dominant actions
    is a pure Nash equilibrium. -/
theorem dominant_is_nash (G : NFGame ι A) (s : StrategyProfile A)
    (hdom : ∀ i, IsDominant G i (s i)) : IsNashPure G s := by
  intro i a'
  have h := hdom i s a'
  simp only [deviate, Function.update_eq_self, ge_iff_le] at h
  exact h

/-! ## NFG → KernelGame bridge -/

/-- NFG as a deterministic kernel: pure profile → point-mass payoff distribution. -/
noncomputable def NFGame.toKernel (G : NFGame ι A) :
    GameTheory.Kernel (∀ i, A i) (GameTheory.Payoff ι) :=
  GameTheory.Kernel.ofFun G.payoff

/-- NFG as a kernel-based game. Outcome type is the action profile. -/
noncomputable def NFGame.toKernelGame (G : NFGame ι A) :
    GameTheory.KernelGame ι where
  Strategy := A
  Outcome := ∀ i, A i
  utility := G.payoff
  outcomeKernel := fun σ => PMF.pure σ

/-- Pure Nash in NFG is equivalent to Nash in the kernel game. -/
theorem IsNashPure_iff_kernelGame (G : NFGame ι A) (s : StrategyProfile A) :
    IsNashPure G s ↔ G.toKernelGame.IsNash s := by
  simp only [IsNashPure, GameTheory.KernelGame.IsNash, GameTheory.KernelGame.eu,
      NFGame.toKernelGame, GameTheory.expect_pure, deviate]

/-- Dominance in NFG is equivalent to dominance in the kernel game. -/
theorem IsDominant_iff_kernelGame (G : NFGame ι A) (i : ι) (a : A i) :
    IsDominant G i a ↔ G.toKernelGame.IsDominant i a := by
  simp only [IsDominant, GameTheory.KernelGame.IsDominant, GameTheory.KernelGame.eu,
      NFGame.toKernelGame, GameTheory.expect_pure, deviate]

/-! ## Mixed strategies -/

/-- A mixed strategy profile: each player independently randomizes over actions. -/
abbrev MixedProfile (A : ι → Type) [∀ i, Fintype (A i)] := ∀ i, PMF (A i)

/-- NFG as a kernel-based game with mixed strategies.
    The outcome kernel maps independent per-player PMFs to a joint distribution
    over pure action profiles via the product PMF construction. -/
noncomputable def NFGame.toMixedKernelGame
    (G : NFGame ι A) : GameTheory.KernelGame ι where
  Strategy := fun i => PMF (A i)
  Outcome := ∀ i, A i
  utility := G.payoff
  outcomeKernel := fun σ => pmfPi σ

/-- A mixed Nash equilibrium: no player can improve expected payoff by
    changing their marginal distribution. -/
def IsNashMixed (G : NFGame ι A)
    (σ : MixedProfile A) : Prop :=
  G.toMixedKernelGame.IsNash σ

end NFG
