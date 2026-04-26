import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Normal-Form Game Syntax

Finite normal-form (strategic-form) games with pure strategies,
Nash equilibrium, and dominance.

Provides:
- `NFGGame` — finite normal-form game structure
- `StrategyProfile`, `deviate` — strategy profiles and deviation
- `IsNashPure`, `IsDominant`, `dominant_is_nash` — pure solution concepts
-/

namespace NFG

/-- A finite normal-form game.
  - `ι` is the type of players
  - `A i` is the type of actions for player `i`
  - `Outcome` is the type of game outcomes
  - `outcome` maps a strategy profile to its outcome
  - `utility` maps an outcome to per-player payoffs -/
structure NFGGame (ι : Type) [Fintype ι] [DecidableEq ι]
    (A : ι → Type) [∀ i, Fintype (A i)] where
  Outcome : Type
  outcome : (∀ i, A i) → Outcome
  utility : Outcome → ι → ℝ

variable {ι : Type} [DecidableEq ι]
variable {A : ι → Type}

/-- A (pure) strategy profile: each player picks an action. -/
abbrev StrategyProfile (A : ι → Type) := ∀ i, A i

/-- Deviate: replace player `i`'s action in profile `s` with `a`.
    This is `Function.update` kept for NFG readability. -/
def deviate (s : StrategyProfile A) (i : ι) (a : A i) : StrategyProfile A :=
  Function.update s i a

@[simp]
theorem deviate_same (s : StrategyProfile A) (i : ι) (a : A i) :
    deviate s i a i = a := by
  simp [deviate]

@[simp]
theorem deviate_other (s : StrategyProfile A) (i j : ι) (a : A i) (h : j ≠ i) :
    deviate s i a j = s j := by
  simp [deviate, h]

variable [Fintype ι] [∀ i, Fintype (A i)]

/-- A pure Nash equilibrium: no player can improve by unilateral deviation. -/
def IsNashPure (G : NFGGame ι A) (s : StrategyProfile A) : Prop :=
  ∀ i (a' : A i), G.utility (G.outcome s) i ≥ G.utility (G.outcome (deviate s i a')) i

/-- Action `a` is dominant for player `i`: regardless of others' actions,
    `a` yields at least as high a utility as any alternative. -/
def IsDominant (G : NFGGame ι A) (i : ι) (a : A i) : Prop :=
  ∀ (s : StrategyProfile A) (a' : A i),
    G.utility (G.outcome (deviate s i a)) i ≥ G.utility (G.outcome (deviate s i a')) i

/-- If every player has a dominant action, the profile of dominant actions
    is a pure Nash equilibrium. -/
theorem dominant_is_nash (G : NFGGame ι A) (s : StrategyProfile A)
    (hdom : ∀ i, IsDominant G i (s i)) : IsNashPure G s := by
  intro i a'
  have h := hdom i s a'
  simp only [deviate, Function.update_eq_self, ge_iff_le] at h
  exact h

end NFG
