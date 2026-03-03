import GameTheory.KernelGame

/-!
# GameTheory.GameForm

A `GameForm` is a `KernelGame` minus utility: the pure protocol layer of a game.
It captures strategies, outcomes, and the stochastic outcome mechanism, but says
nothing about player preferences.

This decomposition makes explicit a key structural observation:
- **Protocol** (GameForm): strategy spaces, outcome kernel, deviation structure
- **Behavior** (utility/preferences): what players want
- **Solution concepts** (Nash, dominance): protocol + behavior composed

## Main definitions

- `GameForm` -- strategy-indexed outcome kernel without utility
- `GameForm.Profile`, `GameForm.outcomeDist`, `GameForm.correlatedOutcome`
- `GameForm.deviateProfile` -- unilateral deviation (derivable, not primitive)
- `GameForm.withUtility` -- attach utility to recover a `KernelGame`
- `KernelGame.toGameForm` -- strip utility
- `GameForm.IsNashFor` -- Nash equilibrium parameterized by an arbitrary preference
- `GameForm.IsBestResponseFor` -- best response parameterized by preference
- `GameForm.WeaklyDominatesFor`, `StrictlyDominatesFor` -- dominance w.r.t. preference
- `GameForm.IsStrictNashFor`, `IsStrictDominantFor` -- strict solution concepts
- `GameForm.ParetoDominatesFor`, `IsParetoEfficientFor` -- Pareto w.r.t. preference
- `GameForm.IsCorrelatedEqFor`, `IsCoarseCorrelatedEqFor` -- correlated eq w.r.t. pref

## Classification of game-theoretic concepts

**Pure protocol** (definable on `GameForm` alone):
- Strategy spaces, outcome distributions, deviation structure
- Kuhn's theorem (behavioral <-> mixed strategies)
- `evalDist`, perfect recall, information sets
- Symmetry of the game form

**Pure behavior** (preference/utility only, no protocol needed):
- `euPref`, `PrefPreorder`, welfare comparisons
- Risk attitudes, utility transformations

**Composed** (protocol + preference):
- `IsNashFor`, `IsDominantFor` -- require both deviation structure and preference
- `ParetoDominatesFor` -- requires both outcome comparison and the feasible set
- `IsCorrelatedEqFor` -- protocol (correlation device) + preference

**Quasi-linear** (behavioral structure that references outcome space):
- Expected utility `eu` -- linear functional on outcome distributions
- Social welfare functions -- aggregate utility over outcomes
-/

namespace GameTheory

-- ============================================================================
-- Section 1: GameForm structure
-- ============================================================================

/-- A game form: the protocol layer of a game, without utility.
    Captures strategy spaces, outcomes, and the stochastic mechanism
    mapping strategy profiles to outcome distributions. -/
structure GameForm (ι : Type) where
  Strategy : ι → Type
  Outcome : Type
  outcomeKernel : Kernel (∀ i, Strategy i) Outcome

namespace GameForm

variable {ι : Type}

/-- A strategy profile: one strategy per player. -/
abbrev Profile (F : GameForm ι) := ∀ i, F.Strategy i

/-- Outcome distribution under a strategy profile. -/
noncomputable def outcomeDist (F : GameForm ι) (σ : F.Profile) : PMF F.Outcome :=
  F.outcomeKernel σ

/-- Outcome distribution under a correlated profile distribution (correlation device). -/
noncomputable def correlatedOutcome (F : GameForm ι)
    (μ : PMF (F.Profile)) : PMF F.Outcome :=
  Kernel.pushforward F.outcomeKernel μ

/-- A point-mass profile distribution induces the same outcome distribution
    as direct evaluation at that profile. -/
@[simp] theorem correlatedOutcome_pure (F : GameForm ι) (σ : F.Profile) :
    F.correlatedOutcome (PMF.pure σ) = F.outcomeKernel σ := by
  simp [correlatedOutcome]

-- ============================================================================
-- Section 2: Derivable protocol operations
-- ============================================================================

open Classical in
/-- Unilateral deviation: replace player `who`'s strategy in profile `σ`. -/
noncomputable def deviateProfile (F : GameForm ι) (σ : F.Profile)
    (who : ι) (s' : F.Strategy who) : F.Profile :=
  Function.update σ who s'

open Classical in
/-- Outcome distribution after a unilateral deviation. -/
noncomputable def deviateOutcome (F : GameForm ι) (σ : F.Profile)
    (who : ι) (s' : F.Strategy who) : PMF F.Outcome :=
  F.outcomeKernel (F.deviateProfile σ who s')

open Classical in
/-- Push a profile distribution through unilateral deviation to get
    the resulting outcome distribution. -/
noncomputable def deviateDistribution (F : GameForm ι)
    (μ : PMF (F.Profile)) (who : ι) (s' : F.Strategy who) : PMF F.Outcome :=
  μ.bind (fun σ => F.outcomeKernel (F.deviateProfile σ who s'))

open Classical in
/-- Constant deviation: every profile in the support gets the same deviation applied. -/
noncomputable def constDeviateDistribution (F : GameForm ι)
    (σ : F.Profile) (who : ι) (s' : F.Strategy who) : PMF F.Outcome :=
  F.outcomeKernel (F.deviateProfile σ who s')

open Classical in
@[simp] theorem deviateProfile_same (F : GameForm ι) (σ : F.Profile)
    (who : ι) : F.deviateProfile σ who (σ who) = σ := by
  simp [deviateProfile]

open Classical in
@[simp] theorem deviateOutcome_same (F : GameForm ι) (σ : F.Profile)
    (who : ι) : F.deviateOutcome σ who (σ who) = F.outcomeKernel σ := by
  simp [deviateOutcome]

-- ============================================================================
-- Section 2b: Function-based deviation (for correlated equilibrium)
-- ============================================================================

open Classical in
/-- Profile-level deviation with a deviation function: replace player `who`'s
    strategy by applying `dev` to their current strategy. -/
noncomputable def deviateProfileFn (F : GameForm ι) (σ : F.Profile)
    (who : ι) (dev : F.Strategy who → F.Strategy who) : F.Profile :=
  Function.update σ who (dev (σ who))

/-- Push a profile distribution through a recommendation-dependent deviation. -/
noncomputable def deviateDistributionFn (F : GameForm ι)
    (μ : PMF F.Profile) (who : ι)
    (dev : F.Strategy who → F.Strategy who) : PMF F.Profile :=
  μ.bind (fun σ => PMF.pure (F.deviateProfileFn σ who dev))

open Classical in
/-- Push a profile distribution through a constant unilateral deviation. -/
noncomputable def constDeviateDistributionFn (F : GameForm ι)
    (μ : PMF F.Profile) (who : ι) (s' : F.Strategy who) : PMF F.Profile :=
  μ.bind (fun σ => PMF.pure (Function.update σ who s'))

-- ============================================================================
-- Section 3: Bridge to KernelGame
-- ============================================================================

/-- Attach a utility function to a game form to get a full kernel game. -/
def withUtility (F : GameForm ι) (u : F.Outcome → Payoff ι) : KernelGame ι where
  Strategy := F.Strategy
  Outcome := F.Outcome
  utility := u
  outcomeKernel := F.outcomeKernel

end GameForm

namespace KernelGame

variable {ι : Type}

/-- Strip utility from a kernel game to get its underlying game form. -/
def toGameForm (G : KernelGame ι) : GameForm ι where
  Strategy := G.Strategy
  Outcome := G.Outcome
  outcomeKernel := G.outcomeKernel

@[simp] theorem toGameForm_Strategy (G : KernelGame ι) :
    G.toGameForm.Strategy = G.Strategy := rfl

@[simp] theorem toGameForm_Outcome (G : KernelGame ι) :
    G.toGameForm.Outcome = G.Outcome := rfl

@[simp] theorem toGameForm_outcomeKernel (G : KernelGame ι) :
    G.toGameForm.outcomeKernel = G.outcomeKernel := rfl

/-- Round-trip: stripping utility then reattaching recovers the original game. -/
@[simp] theorem toGameForm_withUtility (G : KernelGame ι) :
    G.toGameForm.withUtility G.utility = G := by
  cases G; rfl

end KernelGame

namespace GameForm

variable {ι : Type}

@[simp] theorem withUtility_Strategy (F : GameForm ι) (u : F.Outcome → Payoff ι) :
    (F.withUtility u).Strategy = F.Strategy := rfl

@[simp] theorem withUtility_Outcome (F : GameForm ι) (u : F.Outcome → Payoff ι) :
    (F.withUtility u).Outcome = F.Outcome := rfl

@[simp] theorem withUtility_outcomeKernel (F : GameForm ι) (u : F.Outcome → Payoff ι) :
    (F.withUtility u).outcomeKernel = F.outcomeKernel := rfl

@[simp] theorem withUtility_utility (F : GameForm ι) (u : F.Outcome → Payoff ι) :
    (F.withUtility u).utility = u := rfl

/-- Round-trip: attaching utility then stripping recovers the original form. -/
@[simp] theorem withUtility_toGameForm (F : GameForm ι) (u : F.Outcome → Payoff ι) :
    (F.withUtility u).toGameForm = F := by
  cases F; rfl

-- ============================================================================
-- Section 4: Functorial operations
-- ============================================================================

/-- Push outcomes through a function. Strategies and kernel structure unchanged;
    only the interpretation of outcomes changes. -/
noncomputable def map (F : GameForm ι) (f : F.Outcome → β) : GameForm ι where
  Strategy := F.Strategy
  Outcome := β
  outcomeKernel := fun σ => (F.outcomeKernel σ).bind (fun ω => PMF.pure (f ω))

@[simp] theorem map_Strategy (F : GameForm ι) (f : F.Outcome → β) :
    (F.map f).Strategy = F.Strategy := rfl

@[simp] theorem map_Outcome (F : GameForm ι) (f : F.Outcome → β) :
    (F.map f).Outcome = β := rfl

theorem map_outcomeKernel (F : GameForm ι) (f : F.Outcome → β) (σ : F.Profile) :
    (F.map f).outcomeKernel σ = (F.outcomeKernel σ).bind (fun ω => PMF.pure (f ω)) := rfl

/-- Mapping by `id` is the identity (up to the bind-pure law). -/
theorem map_id (F : GameForm ι) :
    F.map id = F := by
  cases F
  simp [map, PMF.bind_pure]

/-- Mapping composes: `map g . map f = map (g . f)`. -/
theorem map_comp (F : GameForm ι) (f : F.Outcome → β) (g : β → γ) :
    (F.map f).map g = F.map (g ∘ f) := by
  simp [map, PMF.bind_bind, PMF.pure_bind]

-- ============================================================================
-- Section 5: Product of game forms
-- ============================================================================

/-- Independent product of two game forms: players choose a strategy pair,
    outcomes are drawn independently from each form's kernel, and the result
    is a pair of outcomes. -/
noncomputable def product (F₁ F₂ : GameForm ι) : GameForm ι where
  Strategy := fun i => F₁.Strategy i × F₂.Strategy i
  Outcome := F₁.Outcome × F₂.Outcome
  outcomeKernel := fun σ =>
    (F₁.outcomeKernel (fun i => (σ i).1)).bind (fun ω₁ =>
      (F₂.outcomeKernel (fun i => (σ i).2)).bind (fun ω₂ =>
        PMF.pure (ω₁, ω₂)))

@[simp] theorem product_Outcome (F₁ F₂ : GameForm ι) :
    (F₁.product F₂).Outcome = (F₁.Outcome × F₂.Outcome) := rfl

/-- Left projection of a product game form recovers the first form's outcome distribution. -/
theorem product_map_fst (F₁ F₂ : GameForm ι) (σ : (F₁.product F₂).Profile) :
    ((F₁.product F₂).outcomeKernel σ).bind (fun p => PMF.pure p.1) =
      F₁.outcomeKernel (fun i => (σ i).1) := by
  simp [product, PMF.bind_bind, PMF.pure_bind, PMF.bind_pure]

/-- Right projection of a product game form recovers the second form's outcome distribution. -/
theorem product_map_snd (F₁ F₂ : GameForm ι) (σ : (F₁.product F₂).Profile) :
    ((F₁.product F₂).outcomeKernel σ).bind (fun p => PMF.pure p.2) =
      F₂.outcomeKernel (fun i => (σ i).2) := by
  simp [product, PMF.bind_bind, PMF.pure_bind]

-- ============================================================================
-- Section 6: Pure behavior: preference preorder
-- ============================================================================

end GameForm

/-- Preference relation with per-player reflexivity/transitivity laws.
    Defined at the `GameTheory` level since it is a pure behavioral concept
    independent of any game structure. -/
class PrefPreorder {ι : Type} {α : Type} (pref : ι → α → α → Prop) : Prop where
  refl : ∀ i x, pref i x x
  trans : ∀ i x y z, pref i x y → pref i y z → pref i x z

namespace GameForm

variable {ι : Type}

-- ============================================================================
-- Section 7: Preference-parameterized solution concepts on GameForm
-- ============================================================================

open Classical in
/-- A strategy profile `σ` is a Nash equilibrium w.r.t. preference `pref` on outcome
    distributions if no player prefers the outcome distribution from any unilateral
    deviation over the status quo distribution.

    `pref who d₁ d₂` means player `who` weakly prefers `d₁` over `d₂`.
    Nash requires: for all deviations, `pref who (current) (deviated)`. -/
def IsNashFor (F : GameForm ι)
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (σ : F.Profile) : Prop :=
  ∀ (who : ι) (s' : F.Strategy who),
    pref who (F.outcomeKernel σ) (F.outcomeKernel (Function.update σ who s'))

open Classical in
/-- An action `s` is dominant for player `who` w.r.t. a preference if `who` weakly
    prefers the outcome from playing `s` against any opponent profile. -/
def IsDominantFor (F : GameForm ι)
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (who : ι) (s : F.Strategy who) : Prop :=
  ∀ (σ : F.Profile) (s' : F.Strategy who),
    pref who (F.outcomeKernel (Function.update σ who s))
             (F.outcomeKernel (Function.update σ who s'))

open Classical in
/-- Preference-parameterized best response (on outcome distributions). -/
def IsBestResponseFor (F : GameForm ι)
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (who : ι) (σ : F.Profile) (s : F.Strategy who) : Prop :=
  ∀ (s' : F.Strategy who),
    pref who (F.outcomeKernel (Function.update σ who s))
      (F.outcomeKernel (Function.update σ who s'))

open Classical in
/-- `s` weakly dominates `t` for player `who` w.r.t. preference `pref`. -/
def WeaklyDominatesFor (F : GameForm ι)
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (who : ι) (s t : F.Strategy who) : Prop :=
  ∀ (σ : F.Profile),
    pref who (F.outcomeKernel (Function.update σ who s))
             (F.outcomeKernel (Function.update σ who t))

open Classical in
/-- `s` strictly dominates `t` for player `who` w.r.t. strict preference `spref`. -/
def StrictlyDominatesFor (F : GameForm ι)
    (spref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (who : ι) (s t : F.Strategy who) : Prop :=
  ∀ (σ : F.Profile),
    spref who (F.outcomeKernel (Function.update σ who s))
              (F.outcomeKernel (Function.update σ who t))

open Classical in
/-- Strict Nash equilibrium w.r.t. a strict preference: every unilateral deviation
    to a different strategy is strictly worse. -/
def IsStrictNashFor (F : GameForm ι)
    (spref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (σ : F.Profile) : Prop :=
  ∀ (who : ι) (s' : F.Strategy who), s' ≠ σ who →
    spref who (F.outcomeKernel σ) (F.outcomeKernel (Function.update σ who s'))

open Classical in
/-- Strictly dominant strategy w.r.t. a strict preference. -/
def IsStrictDominantFor (F : GameForm ι)
    (spref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (who : ι) (s : F.Strategy who) : Prop :=
  ∀ (σ : F.Profile) (s' : F.Strategy who), s' ≠ s →
    spref who (F.outcomeKernel (Function.update σ who s))
              (F.outcomeKernel (Function.update σ who s'))

/-- Profile `σ` Pareto-dominates profile `τ` w.r.t. weak preference `pref`
    and strict preference `spref`. -/
def ParetoDominatesFor (F : GameForm ι)
    (pref spref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (σ τ : F.Profile) : Prop :=
  (∀ i : ι, pref i (F.outcomeKernel σ) (F.outcomeKernel τ)) ∧
    ∃ i : ι, spref i (F.outcomeKernel σ) (F.outcomeKernel τ)

/-- Profile `σ` is Pareto-efficient w.r.t. `pref`/`spref` (no Pareto improvement exists). -/
def IsParetoEfficientFor (F : GameForm ι)
    (pref spref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (σ : F.Profile) : Prop :=
  ¬ ∃ τ : F.Profile, F.ParetoDominatesFor pref spref τ σ

/-- Correlated equilibrium w.r.t. preference `pref`: no player gains from
    recommendation-dependent deviation. -/
def IsCorrelatedEqFor (F : GameForm ι)
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (μ : PMF F.Profile) : Prop :=
  ∀ (who : ι) (dev : F.Strategy who → F.Strategy who),
    pref who (F.correlatedOutcome μ)
      (F.correlatedOutcome (F.deviateDistributionFn μ who dev))

/-- Coarse correlated equilibrium w.r.t. preference `pref`: no player gains from
    constant unilateral deviation. -/
def IsCoarseCorrelatedEqFor (F : GameForm ι)
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (μ : PMF F.Profile) : Prop :=
  ∀ (who : ι) (s' : F.Strategy who),
    pref who (F.correlatedOutcome μ)
      (F.correlatedOutcome (F.constDeviateDistributionFn μ who s'))

-- ============================================================================
-- Section 8: Properties of *For solution concepts
-- ============================================================================

open Classical in
/-- A profile of dominant strategies is Nash (for any preference). -/
theorem dominant_is_nash_for (F : GameForm ι)
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (σ : F.Profile)
    (hdom : ∀ i, F.IsDominantFor pref i (σ i)) :
    F.IsNashFor pref σ := by
  intro who s'
  have h := hdom who σ s'
  rwa [Function.update_eq_self] at h

open Classical in
/-- A profile is Nash for `pref` iff every player plays a best response for `pref`. -/
theorem isNashFor_iff_bestResponseFor (F : GameForm ι)
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop) (σ : F.Profile) :
    F.IsNashFor pref σ ↔ ∀ who, F.IsBestResponseFor pref who σ (σ who) := by
  constructor
  · intro hNash who s'
    have := hNash who s'
    rwa [Function.update_eq_self]
  · intro hBR who s'
    have := hBR who s'
    rwa [Function.update_eq_self] at this

/-- A dominant-for strategy is a best-response-for against any profile. -/
theorem IsDominantFor.isBestResponseFor {F : GameForm ι}
    {pref : ι → PMF F.Outcome → PMF F.Outcome → Prop}
    {who : ι} {s : F.Strategy who}
    (hdom : F.IsDominantFor pref who s) (σ : F.Profile) :
    F.IsBestResponseFor pref who σ s := by
  intro s'
  exact hdom σ s'

/-- Monotonicity of Nash-for: if `pref₂` implies `pref₁` pointwise, then
    Nash-for `pref₂` implies Nash-for `pref₁`. -/
theorem IsNashFor.mono {F : GameForm ι}
    {pref₁ pref₂ : ι → PMF F.Outcome → PMF F.Outcome → Prop}
    (h : ∀ i d₁ d₂, pref₂ i d₁ d₂ → pref₁ i d₁ d₂)
    {σ : F.Profile} (hN : F.IsNashFor pref₂ σ) : F.IsNashFor pref₁ σ := by
  intro who s'
  exact h who _ _ (hN who s')

/-- Monotonicity of dominant-for: if `pref₂` implies `pref₁` pointwise, then
    dominant-for `pref₂` implies dominant-for `pref₁`. -/
theorem IsDominantFor.mono {F : GameForm ι}
    {pref₁ pref₂ : ι → PMF F.Outcome → PMF F.Outcome → Prop}
    (h : ∀ i d₁ d₂, pref₂ i d₁ d₂ → pref₁ i d₁ d₂)
    {who : ι} {s : F.Strategy who}
    (hdom : F.IsDominantFor pref₂ who s) : F.IsDominantFor pref₁ who s := by
  intro σ s'
  exact h who _ _ (hdom σ s')

/-- Weak dominance is reflexive (given `PrefPreorder`). -/
theorem WeaklyDominatesFor.refl {F : GameForm ι}
    {pref : ι → PMF F.Outcome → PMF F.Outcome → Prop} [PrefPreorder pref]
    (who : ι) (s : F.Strategy who) :
    F.WeaklyDominatesFor pref who s s := by
  intro σ
  exact PrefPreorder.refl who _

/-- Weak dominance is transitive (given `PrefPreorder`). -/
theorem WeaklyDominatesFor.trans {F : GameForm ι}
    {pref : ι → PMF F.Outcome → PMF F.Outcome → Prop} [PrefPreorder pref]
    {who : ι} {s t u : F.Strategy who}
    (h1 : F.WeaklyDominatesFor pref who s t)
    (h2 : F.WeaklyDominatesFor pref who t u) :
    F.WeaklyDominatesFor pref who s u := by
  intro σ
  exact PrefPreorder.trans who _ _ _ (h1 σ) (h2 σ)

/-- Strict dominance implies weak dominance (given `spref → pref`). -/
theorem StrictlyDominatesFor.toWeaklyDominatesFor {F : GameForm ι}
    {pref spref : ι → PMF F.Outcome → PMF F.Outcome → Prop}
    (himpl : ∀ i d₁ d₂, spref i d₁ d₂ → pref i d₁ d₂)
    {who : ι} {s t : F.Strategy who}
    (h : F.StrictlyDominatesFor spref who s t) :
    F.WeaklyDominatesFor pref who s t := by
  intro σ
  exact himpl who _ _ (h σ)

/-- A dominant strategy weakly dominates every alternative. -/
theorem IsDominantFor.weaklyDominatesFor {F : GameForm ι}
    {pref : ι → PMF F.Outcome → PMF F.Outcome → Prop}
    {who : ι} {s : F.Strategy who}
    (hdom : F.IsDominantFor pref who s) (t : F.Strategy who) :
    F.WeaklyDominatesFor pref who s t := by
  intro σ
  exact hdom σ t

/-- A strict Nash for `spref` is Nash for `pref` (given `spref → pref`). -/
theorem IsStrictNashFor.isNashFor {F : GameForm ι}
    {pref spref : ι → PMF F.Outcome → PMF F.Outcome → Prop}
    (himpl : ∀ i d₁ d₂, spref i d₁ d₂ → pref i d₁ d₂)
    [PrefPreorder pref]
    {σ : F.Profile} (hstrict : F.IsStrictNashFor spref σ) :
    F.IsNashFor pref σ := by
  classical
  intro who s'
  by_cases h : s' = σ who
  · subst h; simp only [Function.update_eq_self]; exact PrefPreorder.refl who _
  · exact himpl who _ _ (hstrict who s' h)

/-- No profile Pareto-dominates itself (given `spref` is irreflexive). -/
theorem ParetoDominatesFor.irrefl {F : GameForm ι}
    {pref spref : ι → PMF F.Outcome → PMF F.Outcome → Prop}
    (hirr : ∀ i x, ¬ spref i x x)
    (σ : F.Profile) : ¬ F.ParetoDominatesFor pref spref σ σ := by
  intro ⟨_, ⟨i, hi⟩⟩
  exact hirr i _ hi

/-- Pareto dominance is asymmetric (given strict preference contradicts reverse weak). -/
theorem ParetoDominatesFor.asymm {F : GameForm ι}
    {pref spref : ι → PMF F.Outcome → PMF F.Outcome → Prop}
    (hanti : ∀ i x y, spref i x y → ¬ pref i y x)
    (σ τ : F.Profile) :
    F.ParetoDominatesFor pref spref σ τ → ¬ F.ParetoDominatesFor pref spref τ σ := by
  intro ⟨_, ⟨i, hi⟩⟩ ⟨hge, _⟩
  exact hanti i _ _ hi (hge i)

/-- Every correlated equilibrium (for pref) is a coarse correlated equilibrium (for pref). -/
theorem IsCorrelatedEqFor.toCoarseCorrelatedEqFor {F : GameForm ι}
    {pref : ι → PMF F.Outcome → PMF F.Outcome → Prop}
    {μ : PMF F.Profile}
    (hce : F.IsCorrelatedEqFor pref μ) : F.IsCoarseCorrelatedEqFor pref μ := by
  intro who s'
  exact hce who (fun _ => s')

open Classical in
/-- The identity deviation leaves the profile distribution unchanged. -/
theorem deviateDistributionFn_id (F : GameForm ι) (μ : PMF F.Profile) (who : ι) :
    F.deviateDistributionFn μ who _root_.id = μ := by
  simp only [deviateDistributionFn, deviateProfileFn, _root_.id]
  conv_lhs => arg 2; ext σ; rw [Function.update_eq_self]
  exact PMF.bind_pure μ

end GameForm

end GameTheory
