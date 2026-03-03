import GameTheory.SymmetricGame
import GameTheory.ApproximateNash
import Math.Probability

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

open Math.Probability

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

/-- **ESS isolation**: if `s` and `t` are both ESS and `s ≠ t`, then
    `u(s,s) > u(t,s)`. Different ESS are strictly separated. -/
theorem IsESS.strict_against_other_ess {u : S → S → ℝ} {s t : S}
    (hs : IsESS u s) (ht : IsESS u t) (hne : s ≠ t) :
    u s s > u t s := by
  -- From s being ESS: u(s,s) ≥ u(t,s)
  have hge := hs.1 t
  -- Suppose u(s,s) = u(t,s), then stability gives u(s,t) > u(t,t)
  -- But from t being ESS: u(t,t) ≥ u(s,t), contradiction
  by_contra h
  push_neg at h
  have heq : u s s = u t s := le_antisymm h hge
  have hstab := hs.2 t heq hne
  have hge2 := ht.1 s
  linarith

end GameTheory
