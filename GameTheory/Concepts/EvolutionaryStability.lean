import GameTheory.Concepts.SymmetricGame
import GameTheory.Concepts.ApproximateNash
import Math.Probability

/-!
# Evolutionarily Stable Strategies

An evolutionarily stable strategy (ESS) is a strategy that, if adopted by
the entire population, cannot be invaded by any mutant strategy. This
formalizes Maynard Smith and Price (1973).

## Main definitions

* `IsESS` — evolutionarily stable strategy
* `IsNSS` — neutrally stable strategy (weak version)

## Main results

* `IsESS.isNSS` — every ESS is neutrally stable
* `IsESS.nash_condition` — every ESS satisfies the Nash condition
* `isESS_of_strict_nash` — a strict Nash strategy is automatically ESS
* `IsESS.strict_against_other_ess` — different ESS are strictly separated
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
  have hge := hs.1 t
  by_contra h
  push Not at h
  have heq : u s s = u t s := le_antisymm h hge
  have hstab := hs.2 t heq hne
  have hge2 := ht.1 s
  linarith

-- ============================================================================
-- ESS → Nash equilibrium bridge
-- ============================================================================

/-- Build a 2-player symmetric EU function from a payoff matrix `u`.
    Player `i`'s payoff is `u (σ i) (σ (opponent i))`. -/
def symmetricEU (u : S → S → ℝ) : (Fin 2 → S) → Fin 2 → ℝ :=
  fun σ => ![u (σ 0) (σ 1), u (σ 1) (σ 0)]

open Classical in
/-- An ESS induces a Nash equilibrium of the corresponding 2-player
    symmetric `ofEU` game at the symmetric profile. -/
theorem IsESS.isNash_symmetric {u : S → S → ℝ} {s : S} (h : IsESS u s) :
    (KernelGame.ofEU (fun _ : Fin 2 => S) (symmetricEU u)).IsNash (fun _ => s) := by
  intro who s'
  simp only [KernelGame.eu, KernelGame.ofEU, Math.Probability.expect_pure, ge_iff_le, id]
  fin_cases who <;>
    simp only [symmetricEU, Function.update, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    exact h.1 s'

end GameTheory
