/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Dominance.DominanceSolvable

/-!
# Rationalizability

Iterated elimination of strictly dominated strategies and rationalizability.

A strategy is **rationalizable** if it survives all rounds of iterated
elimination of strictly dominated strategies. This is a fundamental solution
concept weaker than Nash equilibrium: every Nash equilibrium strategy is
rationalizable, but not conversely.

Following Bernheim (1984) and Pearce (1984), the standard notion eliminates a
strategy when it is strictly dominated by a **mixed** strategy over the surviving
strategies — equivalently, when it is never a best response to any belief over
the opponents' surviving profiles. A pure strategy can be strictly dominated by a
mixed strategy even when no single pure strategy dominates it, so the mixed
notion (`Survives`, `IsRationalizable`) eliminates more than the pure-domination
notion (`SurvivesPure`, `IsPureRationalizable`); the latter therefore
over-approximates the rationalizable set and is recorded here as the weaker
variant.

The expected payoff of a mixed deviation `p : PMF (G.Strategy who)` against a
pure opponent profile `σ` is `expect p (fun a => G.eu (Function.update σ who a) who)`,
randomizing only the own strategy while opponents stay pure; by linearity this
agrees with deviating in the mixed extension.

## Main definitions

* `KernelGame.Survives` — survives round `n` of elimination by mixed domination
* `KernelGame.IsRationalizable` — survives all rounds (the standard notion)
* `KernelGame.SurvivesPure` / `KernelGame.IsPureRationalizable` — the weaker
  pure-domination variant

## Main results

* `KernelGame.Survives.mono` — survival is monotone decreasing in rounds
* `KernelGame.IsNash.isRationalizable` — Nash equilibrium strategies are
  rationalizable (no mixed strategy strictly beats a best response)
* `KernelGame.IsDominant.isRationalizable` — dominant strategies are rationalizable
* `KernelGame.IsRationalizable.not_globally_dominated` — a rationalizable strategy
  is not `StrictlyDominatedByMixed`
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

/-- A strategy survives round `n` of iterated elimination of strategies that are
    strictly dominated by a **mixed** strategy (the standard Bernheim–Pearce
    notion).

    - Round 0: all strategies survive.
    - Round n+1: `s` survives if it survived round `n` and there is no mixed
      strategy `p` supported on round-`n` survivors that strictly beats `s` in
      expected utility against every profile of round-`n` survivors. -/
def Survives (G : KernelGame ι) : ℕ → (who : ι) → G.Strategy who → Prop
  | 0 => fun _ _ => True
  | n + 1 => fun who s =>
      G.Survives n who s ∧
      ¬∃ p : PMF (G.Strategy who),
        (∀ a ∈ p.support, G.Survives n who a) ∧
        ∀ (σ : Profile G), (∀ j, G.Survives n j (σ j)) →
          expect p (fun a => G.eu (Function.update σ who a) who) >
            G.eu (Function.update σ who s) who

/-- Surviving round `n+1` implies surviving round `n`. -/
theorem Survives.prev {G : KernelGame ι} {n : ℕ} {who : ι} {s : G.Strategy who}
    (h : G.Survives (n + 1) who s) : G.Survives n who s :=
  h.1

/-- Survival is monotone in the number of rounds. -/
theorem Survives.mono {G : KernelGame ι} {m n : ℕ} (hmn : m ≤ n)
    {who : ι} {s : G.Strategy who} (h : G.Survives n who s) :
    G.Survives m who s := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact ih h.prev

/-- A strategy is **rationalizable** if it survives all rounds of iterated
    elimination of mixed-strictly-dominated strategies. -/
def IsRationalizable (G : KernelGame ι) (who : ι) (s : G.Strategy who) : Prop :=
  ∀ n, G.Survives n who s

/-- Nash equilibrium strategies survive all rounds of elimination: a best
    response cannot be strictly beaten in expectation by any mixed deviation
    (evaluated at the Nash profile, every mixed deviation does at most as well). -/
theorem IsNash.survives {G : KernelGame ι} [∀ i, Finite (G.Strategy i)]
    {σ : Profile G} (hN : G.IsNash σ) :
    ∀ (n : ℕ) (who : ι), G.Survives n who (σ who) := by
  intro n
  induction n with
  | zero => intro _; trivial
  | succ n ih =>
    intro who
    refine ⟨ih who, ?_⟩
    rintro ⟨p, _hp_supp, hp_dom⟩
    have h := hp_dom σ ih
    simp only [Function.update_eq_self] at h
    have hle : expect p (fun a => G.eu (Function.update σ who a) who) ≤ G.eu σ who := by
      have hmono := expect_mono p (fun a => G.eu (Function.update σ who a) who)
        (fun _ => G.eu σ who) (fun a => hN who a)
      simpa using hmono
    linarith

/-- Nash equilibrium strategies are rationalizable. -/
theorem IsNash.isRationalizable {G : KernelGame ι} [∀ i, Finite (G.Strategy i)]
    {σ : Profile G} (hN : G.IsNash σ) (who : ι) :
    G.IsRationalizable who (σ who) :=
  fun n => hN.survives n who

/-- Every strategy in a dominant-strategy profile survives all rounds. -/
theorem dominantProfile_survives {G : KernelGame ι} [∀ i, Finite (G.Strategy i)]
    (σ : Profile G) (hdom_all : ∀ j, G.IsDominant j (σ j)) :
    ∀ n who, G.Survives n who (σ who) :=
  (dominant_is_nash G σ hdom_all).survives

/-- A dominant strategy is rationalizable when the other players have a
dominant-strategy profile. -/
theorem IsDominant.isRationalizable {G : KernelGame ι} [∀ i, Finite (G.Strategy i)]
    {who : ι} {s : G.Strategy who} (hdom : G.IsDominant who s)
    (σ₀ : Profile G)
    (hdom_other : ∀ j, j ≠ who → G.IsDominant j (σ₀ j)) :
    G.IsRationalizable who s :=
  fun n => by
    let σ : Profile G := Function.update σ₀ who s
    have hdom_all : ∀ j, G.IsDominant j (σ j) := by
      intro j
      by_cases hj : j = who
      · subst hj
        simpa [σ] using hdom
      · simpa [σ, Function.update, hj] using hdom_other j hj
    have hsurv := dominantProfile_survives (G := G) σ hdom_all n who
    simpa [σ] using hsurv

/-- A rationalizable strategy is not strictly dominated by any mixed strategy
    against all profiles (the first-round elimination). -/
theorem IsRationalizable.not_globally_dominated {G : KernelGame ι}
    {who : ι} {s : G.Strategy who} (hs : G.IsRationalizable who s) :
    ¬ G.StrictlyDominatedByMixed who s := by
  intro h
  obtain ⟨p, hdom⟩ := h
  have hs1 := hs 1
  exact hs1.2 ⟨p, fun a _ => trivial, fun σ _ => hdom σ⟩

/-! ## The weaker pure-domination variant

Eliminating only by a *pure* dominator removes fewer strategies, so the pure
notion below over-approximates the rationalizable set. It is the special case of
the mixed notion in which the dominator is a point mass, recorded for
comparison. -/

/-- A strategy survives round `n` of iterated elimination of strategies strictly
    dominated by a **pure** survivor (the weaker, non-standard variant). -/
def SurvivesPure (G : KernelGame ι) : ℕ → (who : ι) → G.Strategy who → Prop
  | 0 => fun _ _ => True
  | n + 1 => fun who s =>
      G.SurvivesPure n who s ∧
      ¬∃ t : G.Strategy who, G.SurvivesPure n who t ∧
        ∀ (σ : Profile G), (∀ j, G.SurvivesPure n j (σ j)) →
          G.eu (Function.update σ who t) who > G.eu (Function.update σ who s) who

/-- Surviving pure round `n+1` implies surviving round `n`. -/
theorem SurvivesPure.prev {G : KernelGame ι} {n : ℕ} {who : ι} {s : G.Strategy who}
    (h : G.SurvivesPure (n + 1) who s) : G.SurvivesPure n who s :=
  h.1

/-- Pure survival is monotone in the number of rounds. -/
theorem SurvivesPure.mono {G : KernelGame ι} {m n : ℕ} (hmn : m ≤ n)
    {who : ι} {s : G.Strategy who} (h : G.SurvivesPure n who s) :
    G.SurvivesPure m who s := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact ih h.prev

/-- A strategy is **pure-rationalizable** if it survives all rounds of iterated
    elimination of pure-strictly-dominated strategies. -/
def IsPureRationalizable (G : KernelGame ι) (who : ι) (s : G.Strategy who) : Prop :=
  ∀ n, G.SurvivesPure n who s

/-- Nash equilibrium strategies survive all rounds of pure elimination. -/
theorem IsNash.survivesPure {G : KernelGame ι} {σ : Profile G}
    (hN : G.IsNash σ) : ∀ (n : ℕ) (who : ι), G.SurvivesPure n who (σ who) := by
  intro n
  induction n with
  | zero => intro _; trivial
  | succ n ih =>
    intro who
    refine ⟨ih who, ?_⟩
    intro ⟨_t, _ht_surv, ht_dom⟩
    have h_dom := ht_dom σ ih
    have h_nash := hN who _t
    simp only [Function.update_eq_self] at h_dom
    linarith

/-- Nash equilibrium strategies are pure-rationalizable. -/
theorem IsNash.isPureRationalizable {G : KernelGame ι} {σ : Profile G}
    (hN : G.IsNash σ) (who : ι) : G.IsPureRationalizable who (σ who) :=
  fun n => hN.survivesPure n who

/-- Every strategy in a dominant-strategy profile survives all rounds of pure
elimination. -/
theorem dominantProfile_survivesPure {G : KernelGame ι} (σ : Profile G)
    (hdom_all : ∀ j, G.IsDominant j (σ j)) :
    ∀ n who, G.SurvivesPure n who (σ who) :=
  (dominant_is_nash G σ hdom_all).survivesPure

/-- A dominant strategy is pure-rationalizable when the other players have a
dominant-strategy profile. -/
theorem IsDominant.isPureRationalizable {G : KernelGame ι}
    {who : ι} {s : G.Strategy who} (hdom : G.IsDominant who s)
    (σ₀ : Profile G)
    (hdom_other : ∀ j, j ≠ who → G.IsDominant j (σ₀ j)) :
    G.IsPureRationalizable who s :=
  fun n => by
    let σ : Profile G := Function.update σ₀ who s
    have hdom_all : ∀ j, G.IsDominant j (σ j) := by
      intro j
      by_cases hj : j = who
      · subst hj
        simpa [σ] using hdom
      · simpa [σ, Function.update, hj] using hdom_other j hj
    have hsurv := dominantProfile_survivesPure (G := G) σ hdom_all n who
    simpa [σ] using hsurv

end KernelGame

end GameTheory
