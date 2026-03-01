import GameTheory.SymmetricGame
import GameTheory.ApproximateNash

/-!
# Evolutionarily Stable Strategies

An evolutionarily stable strategy (ESS) is a strategy that, if adopted by
the entire population, cannot be invaded by any mutant strategy. This
formalizes Maynard Smith and Price (1973).

We work in a symmetric 2-player game with uniform strategy type `S`.
The payoff function `u : S → S → ℝ` gives the payoff to a player using
the first argument against an opponent using the second.

## Main definitions

* `IsESS` — evolutionarily stable strategy
* `IsNSS` — neutrally stable strategy (weak version)

## Main results

* `IsESS.isNash_symmetric` — every ESS is a symmetric Nash equilibrium
* `IsESS.isNSS` — every ESS is neutrally stable
-/

namespace GameTheory

variable {S : Type}

/-- A strategy `s` is an ESS if:
    1. `u(s, s) ≥ u(t, s)` for all `t` (Nash condition), and
    2. if `u(s, s) = u(t, s)` then `u(s, t) > u(t, t)` (stability). -/
def IsESS (u : S → S → ℝ) (s : S) : Prop :=
  (∀ t, u s s ≥ u t s) ∧
  (∀ t, u s s = u t s → s ≠ t → u s t > u t t)

/-- A strategy `s` is neutrally stable if:
    1. `u(s, s) ≥ u(t, s)` for all `t`, and
    2. if `u(s, s) = u(t, s)` then `u(s, t) ≥ u(t, t)`. -/
def IsNSS (u : S → S → ℝ) (s : S) : Prop :=
  (∀ t, u s s ≥ u t s) ∧
  (∀ t, u s s = u t s → u s t ≥ u t t)

/-- Every ESS is neutrally stable. -/
theorem IsESS.isNSS {u : S → S → ℝ} {s : S} (h : IsESS u s) : IsNSS u s := by
  refine ⟨h.1, fun t heq => ?_⟩
  by_cases hs : s = t
  · subst hs; exact le_refl _
  · exact le_of_lt (h.2 t heq hs)

/-- An ESS is a symmetric Nash equilibrium of the 2-player game:
    `u(s, s) ≥ u(t, s)` for all alternative strategies `t`. -/
theorem IsESS.nash_condition {u : S → S → ℝ} {s : S} (h : IsESS u s) :
    ∀ t, u s s ≥ u t s := h.1

/-- If `s` is ESS and `t ≠ s` achieves the same payoff against `s`,
    then `s` does strictly better against `t`. -/
theorem IsESS.stability {u : S → S → ℝ} {s : S} (h : IsESS u s)
    {t : S} (heq : u s s = u t s) (hne : s ≠ t) : u s t > u t t :=
  h.2 t heq hne

/-- A strict Nash ESS: if `u(s,s) > u(t,s)` for all `t ≠ s`,
    then `s` is automatically ESS (the stability condition is vacuous). -/
theorem isESS_of_strict_nash {u : S → S → ℝ} {s : S}
    (hstrict : ∀ t, t ≠ s → u s s > u t s) : IsESS u s := by
  refine ⟨fun t => ?_, fun t heq hne => ?_⟩
  · by_cases h : t = s
    · subst h; exact le_refl _
    · exact le_of_lt (hstrict t h)
  · exact absurd heq (ne_of_gt (hstrict t hne.symm))

end GameTheory
