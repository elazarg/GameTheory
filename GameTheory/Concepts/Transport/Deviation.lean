/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.Coalition

/-!
# Deviating units, deviation families, and family morphisms

A **deviation family** collects, for each *deviating unit* `u` drawn from an
abstract index type `U`, the deviations that unit may perform on a status-quo
profile distribution. Taking `U = ι` recovers unilateral (single-player)
deviations; taking `U = Coalition ι` gives coalitional ones; an adversarial
scheduler promoted to a participant is just one more unit. The equilibrium
predicate `IsDeviationEqFor` asks that no unit has a profitable deviation, with
`pref u` supplying the profitability test for unit `u`.

For coalition units the profitability test is an aggregation policy over
per-player preferences. `ParetoBlocks` and `AllStrictBlocks` are the two named
blocking criteria; their negations `noParetoBlock` and `noAllStrictBlock` are
the aggregators that fit the `pref` slot of `IsDeviationEqFor`, yielding
strong-Nash and `t`-resilience style equilibria respectively.

`DeviationFamily.Hom` reindexes deviating units, and equilibrium transports
along such a morphism.
-/

namespace GameTheory

open Math.Probability

/-- A **coalition** of players: a nonempty finite set. Coalitions are the
deviating units of coalitional solution concepts (strong Nash, `t`-resilience);
individual players embed as the singleton coalitions via `Coalition.singleton`. -/
abbrev Coalition (ι : Type) : Type := {C : Finset ι // C.Nonempty}

namespace Coalition

variable {ι : Type}

/-- The singleton coalition `{i}`, embedding a player into the coalition units. -/
def singleton (i : ι) : Coalition ι := ⟨{i}, Finset.singleton_nonempty i⟩

end Coalition

/-- Coalition `C` **Pareto-blocks** the move from the status-quo outcome law
`old` to the deviated law `new`: every member weakly prefers `new` while some
member strictly prefers it. This is the strong-Nash blocking criterion — the
coalition analogue of `GameForm.ParetoDominatesFor`, taking weak and strict
preferences as separate relations with the preferred law first. -/
def ParetoBlocks {ι Ω : Type} (playerPref playerSPref : ι → PMF Ω → PMF Ω → Prop)
    (C : Coalition ι) (old new : PMF Ω) : Prop :=
  (∀ i ∈ C.val, playerPref i new old) ∧ (∃ i ∈ C.val, playerSPref i new old)

/-- Coalition `C` **all-strictly-blocks** the move from `old` to `new`: every
member strictly prefers `new`. This is the `t`-resilience style blocking
criterion. -/
def AllStrictBlocks {ι Ω : Type} (playerSPref : ι → PMF Ω → PMF Ω → Prop)
    (C : Coalition ι) (old new : PMF Ω) : Prop :=
  ∀ i ∈ C.val, playerSPref i new old

/-- Coalition profitability test in the **Pareto (strong-Nash) orientation**:
`C` cannot Pareto-block the move `old → new`. This is the coalition aggregator
for the `pref` slot of `IsDeviationEqFor`, whose universal reading over
deviations then expresses "no coalition has a Pareto-improving joint deviation"
— strong Nash. -/
def noParetoBlock {ι Ω : Type} (playerPref playerSPref : ι → PMF Ω → PMF Ω → Prop)
    (C : Coalition ι) (old new : PMF Ω) : Prop :=
  ¬ ParetoBlocks playerPref playerSPref C old new

/-- Coalition profitability test in the **all-strict (`t`-resilience)
orientation**: `C` cannot strictly improve every member by moving `old → new`.
The coalition aggregator for the `pref` slot of `IsDeviationEqFor`, expressing
"no coalition has a joint deviation that strictly benefits all of its members". -/
def noAllStrictBlock {ι Ω : Type} (playerSPref : ι → PMF Ω → PMF Ω → Prop)
    (C : Coalition ι) (old new : PMF Ω) : Prop :=
  ¬ AllStrictBlocks playerSPref C old new

namespace GameForm

variable {ι : Type}

/-- A **deviation family** over a type `U` of deviating units. For each unit
`u : U`, `Dev u` enumerates the deviations available to `u`, and `deviate`
turns a status-quo profile distribution together with a chosen deviation into
the post-deviation profile distribution. Unilateral deviations are the case
`U = ι`; coalitional deviations the case `U = Coalition ι`. -/
structure DeviationFamily (F : GameForm ι) (U : Type) where
  /-- The deviations available to each unit. -/
  Dev : U → Type
  /-- Apply a unit's chosen deviation to a status-quo profile distribution. -/
  deviate : PMF F.Profile → ∀ u : U, Dev u → PMF F.Profile

/-- A profile distribution `μ` is a **deviation-family equilibrium** for `Δ`
under `pref`: for every unit `u` and every deviation `d` available to `u`,
`pref u` relates the status-quo outcome law to the post-deviation outcome law.

The orientation matches the rest of the library: `pref u old new` reads "unit
`u` does not strictly gain by moving from the status-quo law `old` to the
deviated law `new`", so the predicate asserts the absence of any profitable
deviation. -/
def IsDeviationEqFor (F : GameForm ι) {U : Type}
    (pref : U → PMF F.Outcome → PMF F.Outcome → Prop)
    (μ : PMF F.Profile) (Δ : DeviationFamily F U) : Prop :=
  ∀ u : U, ∀ d : Δ.Dev u,
    pref u (F.correlatedOutcome μ) (F.correlatedOutcome (Δ.deviate μ u d))

/-- A **morphism of deviation families** along a reindexing `m : U' → U` of
deviating units. Each source deviation available to `u'` maps to a target
deviation available to `m u'` inducing the *same* post-deviation profile
distribution. -/
structure DeviationFamily.Hom {F : GameForm ι} {U U' : Type} (m : U' → U)
    (Δ' : DeviationFamily F U') (Δ : DeviationFamily F U) where
  /-- Reindex each source deviation to a target deviation of the image unit. -/
  map : ∀ u', Δ'.Dev u' → Δ.Dev (m u')
  /-- The reindexed deviation acts identically on every status-quo distribution. -/
  deviate_eq : ∀ μ u' d', Δ.deviate μ (m u') (map u' d') = Δ'.deviate μ u' d'

/-- Equilibrium transports along a family morphism: a `Δ`-equilibrium under
`pref` is a `Δ'`-equilibrium under the reindexed preference `pref ∘ m`.
Restricting the target arsenal to the image of `map` can only make the
equilibrium easier to satisfy. -/
theorem DeviationFamily.Hom.isDeviationEqFor {F : GameForm ι} {U U' : Type}
    {m : U' → U} {Δ' : DeviationFamily F U'} {Δ : DeviationFamily F U}
    (φ : DeviationFamily.Hom m Δ' Δ)
    {pref : U → PMF F.Outcome → PMF F.Outcome → Prop} {μ : PMF F.Profile}
    (hEq : F.IsDeviationEqFor pref μ Δ) :
    F.IsDeviationEqFor (fun u' => pref (m u')) μ Δ' := by
  intro u' d'
  have h := hEq (m u') (φ.map u' d')
  rwa [φ.deviate_eq μ u' d'] at h

section Coalition
variable [DecidableEq ι]

/-- The **coalition constant-deviation family**: for each coalition `C`, a
deviation assigns every member `i ∈ C` a replacement strategy. Applied to a
status-quo profile distribution, each member substitutes their chosen strategy
while every non-member keeps their status-quo draw. This is the distribution-level
counterpart of `KernelGame.coalitionDeviation`; the singleton coalitions recover
the unilateral `constantDeviationProfileFamily` (see `constantToCoalitionHom`). -/
noncomputable def coalitionConstantDeviationFamily (F : GameForm ι) :
    DeviationFamily F (Coalition ι) where
  Dev := fun C => ∀ i ∈ C.val, F.Strategy i
  deviate := fun μ C d =>
    μ.bind fun σ => PMF.pure fun i => if h : i ∈ C.val then d i h else σ i

@[simp] theorem coalitionConstantDeviationFamily_deviate (F : GameForm ι)
    (μ : PMF F.Profile) (C : Coalition ι) (d : ∀ i ∈ C.val, F.Strategy i) :
    F.coalitionConstantDeviationFamily.deviate μ C d =
      μ.bind (fun σ => PMF.pure (fun i => if h : i ∈ C.val then d i h else σ i)) :=
  rfl

@[simp] theorem coalitionConstantDeviationFamily_deviate_pure (F : GameForm ι)
    (σ : F.Profile) (C : Coalition ι) (d : ∀ i ∈ C.val, F.Strategy i) :
    F.coalitionConstantDeviationFamily.deviate (PMF.pure σ) C d =
      PMF.pure (fun i => if h : i ∈ C.val then d i h else σ i) := by
  simp [coalitionConstantDeviationFamily_deviate, PMF.pure_bind]

/-- A pure coalition deviation is the shared coalition-profile override. -/
theorem coalitionConstantDeviationFamily_deviate_pure_eq_override
    (F : GameForm ι) (σ : F.Profile) (C : Coalition ι)
    (d : ∀ i ∈ C.val, F.Strategy i) :
    F.coalitionConstantDeviationFamily.deviate (PMF.pure σ) C d =
      PMF.pure (F.overrideCoalition C.val (fun i => d i i.2) σ) := by
  rw [coalitionConstantDeviationFamily_deviate_pure]
  change PMF.pure (fun i => if h : i ∈ C.val then d i h else σ i) =
    PMF.pure (fun i => if h : i ∈ C.val then d i h else σ i)
  rfl

end Coalition

end GameForm

end GameTheory
