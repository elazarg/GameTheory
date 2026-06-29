/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import GameTheory.Concepts.Equilibrium.SolutionConcepts

/-!
# GameTheory.Concepts.Dominance.DominanceSolvable

Relationships between dominance and best-response / Nash equilibrium concepts
for kernel-based games.

Provides:
- `StrictlyDominates.not_best_response` — a strictly dominated strategy is never a best response
- `StrictlyDominatedByMixed` — a pure strategy strictly dominated by a *mixed* strategy
- `StrictlyDominatedByMixed.not_best_response` — the mixed generalization: a
  mixed-dominated strategy is never a best response
- `StrictlyDominates.toStrictlyDominatedByMixed` — pure dominance is the
  point-mass case of mixed dominance
- `WeaklyDominates.best_response_of_best_response` — weak dominance preserves best-response status
- `nash_never_strictly_dominated` — Nash equilibrium strategies are never strictly dominated
- `IsDominant.isBestResponse` — a dominant strategy is a best response against every profile
-/

namespace GameTheory

open Math.Probability

variable {ι : Type} [DecidableEq ι]

namespace KernelGame

/-- A strictly dominated strategy is never a best response.
    If `s` strictly dominates `t` for player `who`, then for every opponent
    profile `σ`, `t` cannot be a best response. -/
theorem StrictlyDominates.not_best_response {G : KernelGame ι} {who : ι}
    {s t : G.Strategy who} (hsd : G.StrictlyDominates who s t) :
    ∀ σ : Profile G, ¬ G.IsBestResponse who σ t := by
  intro σ hbr
  have hbr_s := hbr s
  have hsd_σ := hsd σ
  linarith

/-- A pure strategy `t` is **strictly dominated by a mixed strategy** if some
    mixed strategy `p` yields strictly higher expected utility than `t` against
    every opponent profile. A pure strategy can be mixed-dominated even when no
    single pure strategy dominates it, so this is genuinely weaker than
    `StrictlyDominates`. The expected payoff of the mixed deviation against a
    pure profile `σ` randomizes only the own coordinate. -/
def StrictlyDominatedByMixed (G : KernelGame ι) (who : ι) (t : G.Strategy who) : Prop :=
  ∃ p : PMF (G.Strategy who),
    ∀ σ : Profile G,
      expect p (fun a => G.eu (Function.update σ who a) who) >
        G.eu (Function.update σ who t) who

/-- A strategy strictly dominated by a mixed strategy is never a best response —
    the mixed generalization of `StrictlyDominates.not_best_response`. If `t`
    were a best response, it would weakly beat every pure action, hence beat the
    mixture, contradicting strict mixed dominance. -/
theorem StrictlyDominatedByMixed.not_best_response {G : KernelGame ι}
    [∀ i, Finite (G.Strategy i)] {who : ι} {t : G.Strategy who}
    (hsd : G.StrictlyDominatedByMixed who t) :
    ∀ σ : Profile G, ¬ G.IsBestResponse who σ t := by
  obtain ⟨p, hp⟩ := hsd
  intro σ hbr
  have hp_σ := hp σ
  have hle : expect p (fun a => G.eu (Function.update σ who a) who)
      ≤ G.eu (Function.update σ who t) who := by
    have hmono := expect_mono p (fun a => G.eu (Function.update σ who a) who)
      (fun _ => G.eu (Function.update σ who t) who) (fun a => hbr a)
    simpa using hmono
  linarith

/-- Pure strict dominance is the point-mass case of mixed dominance: if `s`
    strictly dominates `t`, the point mass at `s` strictly mixed-dominates `t`.
    Hence eliminating by mixed dominators removes at least as much as eliminating
    by pure ones. -/
theorem StrictlyDominates.toStrictlyDominatedByMixed {G : KernelGame ι} {who : ι}
    {s t : G.Strategy who} (hsd : G.StrictlyDominates who s t) :
    G.StrictlyDominatedByMixed who t :=
  ⟨PMF.pure s, fun σ => by simpa [expect_pure] using hsd σ⟩

/-- If `s` weakly dominates `t` and `t` is a best response against `σ`,
    then `s` is also a best response against `σ`. -/
theorem WeaklyDominates.best_response_of_best_response {G : KernelGame ι} {who : ι}
    {s t : G.Strategy who} (hwd : G.WeaklyDominates who s t) (σ : Profile G)
    (hbr : G.IsBestResponse who σ t) : G.IsBestResponse who σ s := by
  intro s'
  have h1 := hbr s'
  have h2 := hwd σ
  linarith

/-- In a Nash equilibrium, no player's strategy is strictly dominated.
    That is, if `σ` is Nash then for every player `who` and strategy `s`,
    `s` does not strictly dominate `σ who`. -/
theorem nash_never_strictly_dominated {G : KernelGame ι} {σ : Profile G}
    (hN : G.IsNash σ) (who : ι) (s : G.Strategy who) :
    ¬ G.StrictlyDominates who s (σ who) := by
  classical
  intro hsd
  have hsd_σ := hsd σ
  simp only [Function.update_eq_self] at hsd_σ
  have hN_who := hN who s
  linarith

/-- A dominant strategy is a best response against every profile. -/
theorem IsDominant.isBestResponse {G : KernelGame ι} {who : ι} {s : G.Strategy who}
    (hdom : G.IsDominant who s) (σ : Profile G) : G.IsBestResponse who σ s := by
  intro s'
  exact hdom σ s'

end KernelGame

end GameTheory
