/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Equilibrium.StrongNash
import GameTheory.Concepts.Transport.Pref

/-!
# Flow invariance and its coalition boundary

Following Candogan–Menache–Ozdaglar–Parrilo (*Flows and Decompositions of Games*,
Math. Oper. Res. 2011), a game's unilateral equilibria depend only on the utility
*differences* along unilateral-deviation edges — the "flow" on the game graph —
not on utility levels. Adding a **nonstrategic component** `w`, whose contribution
to a player's expected utility no unilateral deviation of that player can move,
leaves Nash / correlated / coarse-correlated equilibria untouched.

This is a preference-level invariance: `addNonstrategic w` changes the outcome
laws' utilities, so the two games are not related by a law-based `Transport`; only
their preference *verdicts* along matched deviations agree. It is therefore an
instance of `GameForm.PrefSimulates`, transported by `PrefSimulates.transfer`.

The invariance is **stratified by the deviating unit**: a nonstrategic component
cancels in every *unilateral* incentive comparison (the deviating player's own
`w`-expectation is fixed), but not in a *coalition* one — when other members move,
the opponents' strategies change and `w` need not be constant. So two same-flow
games share Nash but can differ on strong Nash. The last section is a
machine-checked witness of exactly this boundary.
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

/-- Add a **nonstrategic component** `w` to a game: each player's utility gains a
term `w o i` at outcome `o`. Strategies, outcomes, and the outcome kernel are
unchanged, so the underlying `GameForm` is identical — only the payoffs shift. -/
def addNonstrategic (G : KernelGame ι) (w : G.Outcome → Payoff ι) : KernelGame ι where
  Strategy := G.Strategy
  Outcome := G.Outcome
  utility := fun o i => G.utility o i + w o i
  outcomeKernel := G.outcomeKernel

@[simp] theorem addNonstrategic_Strategy (G : KernelGame ι) (w : G.Outcome → Payoff ι) :
    (G.addNonstrategic w).Strategy = G.Strategy := rfl

@[simp] theorem addNonstrategic_Outcome (G : KernelGame ι) (w : G.Outcome → Payoff ι) :
    (G.addNonstrategic w).Outcome = G.Outcome := rfl

@[simp] theorem addNonstrategic_outcomeKernel (G : KernelGame ι) (w : G.Outcome → Payoff ι) :
    (G.addNonstrategic w).outcomeKernel = G.outcomeKernel := rfl

@[simp] theorem addNonstrategic_utility (G : KernelGame ι) (w : G.Outcome → Payoff ι)
    (o : G.Outcome) (i : ι) :
    (G.addNonstrategic w).utility o i = G.utility o i + w o i := rfl

@[simp] theorem addNonstrategic_toGameForm (G : KernelGame ι) (w : G.Outcome → Payoff ι) :
    (G.addNonstrategic w).toGameForm = G.toGameForm := rfl

/-- A component `w` is **nonstrategic for the unilateral family `Δ`** (`U = ι`, the
deviating unit *is* the player): for every player `i` and deviation `d`, the
`i`-expectation of `w` is unchanged by `i`'s own deviation. This is precisely what
the verdict argument at unit `i` consults, so it is the minimal hypothesis making
`w` cancel in every unilateral incentive comparison. -/
def NonstrategicForUnilateral (G : KernelGame ι)
    (Δ : GameForm.DeviationFamily G.toGameForm ι) (w : G.Outcome → Payoff ι) : Prop :=
  ∀ (μ : PMF G.toGameForm.Profile) (i : ι) (d : Δ.Dev i),
    expect (G.toGameForm.correlatedOutcome (Δ.deviate μ i d)) (fun o => w o i) =
      expect (G.toGameForm.correlatedOutcome μ) (fun o => w o i)

/-- A payoff-shaped function is expectation-summable when each player's
component is absolutely summable under every outcome law induced by a profile
distribution.

This is a uniform well-definedness condition for expected-utility comparisons.
If `f` and `g` are expectation-summable, expectation is additive on `f + g`
under every correlated outcome law. Finite outcome spaces and playerwise
bounded payoffs satisfy the condition.

The condition is global and independent of a deviation family. A result about
a fixed distribution or a restricted family of deviations may require only a
weaker local summability assumption. -/
def ExpectSummable (G : KernelGame ι) (f : G.Outcome → Payoff ι) : Prop :=
  ∀ (μ : PMF G.toGameForm.Profile) (i : ι),
    Summable fun o => (G.toGameForm.correlatedOutcome μ o).toReal * f o i

/-- On a finite outcome space every payoff is expectation-summable: a family
indexed by a finite type is summable. -/
theorem ExpectSummable.of_finite (G : KernelGame ι) [Finite G.Outcome]
    (f : G.Outcome → Payoff ι) : G.ExpectSummable f := by
  intro μ i
  haveI : Finite G.toGameForm.Outcome := ‹Finite G.Outcome›
  exact Summable.of_finite

/-- A per-player bounded payoff is expectation-summable. This is the case that
admits countably infinite outcome spaces with bounded payoffs (e.g. discounted
repeated games): the outcome-law weights are summable, so a bounded integrand
against them is summable. -/
theorem ExpectSummable.of_bounded (G : KernelGame ι) (f : G.Outcome → Payoff ι)
    (M : ι → ℝ) (hM : ∀ o i, |f o i| ≤ M i) : G.ExpectSummable f :=
  fun μ i =>
    expect_summable_of_bounded (G.toGameForm.correlatedOutcome μ)
      (fun o => f o i) (fun o => hM o i)

/-- **The verdict cancels forward.** If `w` is nonstrategic for `Δ`, then along the
identity correspondence every `Δ`-deviation's non-profitability under the base EU
preference implies its non-profitability under the shifted EU preference: the
`w`-expectation is the same at both endpoints, so it cancels from the comparison. -/
theorem addNonstrategic_prefSimulates_euPref (G : KernelGame ι)
    (Δ : GameForm.DeviationFamily G.toGameForm ι) (w : G.Outcome → Payoff ι)
    (hns : G.NonstrategicForUnilateral Δ w)
    (hu : G.ExpectSummable G.utility) (hw : G.ExpectSummable w) :
    GameForm.PrefSimulates (G := G.toGameForm) (H := G.toGameForm)
      Eq G.euPref (G.addNonstrategic w).euPref Δ Δ := by
  intro μG μH hrel who d
  cases hrel
  refine ⟨d, fun hsrc => ?_⟩
  have hb := hns μG who d
  have edev := expect_add_of_summable (G.toGameForm.correlatedOutcome (Δ.deviate μG who d))
    (fun o => G.utility o who) (fun o => w o who)
    (hu (Δ.deviate μG who d) who) (hw (Δ.deviate μG who d) who)
  have esq := expect_add_of_summable (G.toGameForm.correlatedOutcome μG)
    (fun o => G.utility o who) (fun o => w o who) (hu μG who) (hw μG who)
  simp only [KernelGame.euPref, addNonstrategic_utility, ge_iff_le] at hsrc ⊢
  simp only [toGameForm_Outcome, addNonstrategic_Outcome] at hb hsrc edev esq ⊢
  linarith

/-- **The verdict cancels backward.** The reverse direction of
`addNonstrategic_prefSimulates_euPref`: the shifted preference's verdict implies
the base preference's, since the `w`-expectation cancels either way. The two facts
together give preference-level invariance (`PrefSimulates.transfer_iff`). -/
theorem addNonstrategic_prefSimulates_euPref_flip (G : KernelGame ι)
    (Δ : GameForm.DeviationFamily G.toGameForm ι) (w : G.Outcome → Payoff ι)
    (hns : G.NonstrategicForUnilateral Δ w)
    (hu : G.ExpectSummable G.utility) (hw : G.ExpectSummable w) :
    GameForm.PrefSimulates (G := G.toGameForm) (H := G.toGameForm)
      Eq (G.addNonstrategic w).euPref G.euPref Δ Δ := by
  intro μG μH hrel who d
  cases hrel
  refine ⟨d, fun hsrc => ?_⟩
  have hb := hns μG who d
  have edev := expect_add_of_summable (G.toGameForm.correlatedOutcome (Δ.deviate μG who d))
    (fun o => G.utility o who) (fun o => w o who)
    (hu (Δ.deviate μG who d) who) (hw (Δ.deviate μG who d) who)
  have esq := expect_add_of_summable (G.toGameForm.correlatedOutcome μG)
    (fun o => G.utility o who) (fun o => w o who) (hu μG who) (hw μG who)
  simp only [KernelGame.euPref, addNonstrategic_utility, ge_iff_le] at hsrc ⊢
  simp only [toGameForm_Outcome, addNonstrategic_Outcome] at hb hsrc edev esq ⊢
  linarith

/-- **Nash invariance under a nonstrategic component.** If `w` is nonstrategic for
the constant unilateral (Nash) family, the shifted game has exactly the same Nash
equilibria: the nonstrategic payoff cancels in every player's unilateral incentive
comparison. This is the flow-invariance of Nash — the equilibria see only the
utility differences along deviation edges. -/
theorem isNash_addNonstrategic_iff [DecidableEq ι] (G : KernelGame ι)
    (w : G.Outcome → Payoff ι)
    (hns : G.NonstrategicForUnilateral G.toGameForm.constantDeviationProfileFamily w)
    (hu : G.ExpectSummable G.utility) (hw : G.ExpectSummable w)
    (σ : G.Profile) :
    (G.addNonstrategic w).IsNash σ ↔ G.IsNash σ := by
  rw [(G.addNonstrategic w).IsNash_iff_IsNashFor_eu, G.IsNash_iff_IsNashFor_eu]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact GameForm.PrefSimulates.transfer
      (addNonstrategic_prefSimulates_euPref_flip G _ w hns hu hw) rfl h
  · exact GameForm.PrefSimulates.transfer
      (addNonstrategic_prefSimulates_euPref G _ w hns hu hw) rfl h

/-- **Coarse-correlated-equilibrium invariance.** A nonstrategic component for the
constant unilateral family preserves the coarse correlated equilibria of any
correlation device: constant unilateral deviations see only utility differences,
which the flow fixes. -/
theorem isCoarseCorrelatedEq_addNonstrategic_iff [DecidableEq ι] (G : KernelGame ι)
    (w : G.Outcome → Payoff ι)
    (hns : G.NonstrategicForUnilateral G.toGameForm.constantDeviationProfileFamily w)
    (hu : G.ExpectSummable G.utility) (hw : G.ExpectSummable w)
    (μ : PMF G.Profile) :
    (G.addNonstrategic w).IsCoarseCorrelatedEq μ ↔ G.IsCoarseCorrelatedEq μ := by
  rw [(G.addNonstrategic w).IsCoarseCorrelatedEq_iff_IsCoarseCorrelatedEqFor_eu,
    G.IsCoarseCorrelatedEq_iff_IsCoarseCorrelatedEqFor_eu]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact GameForm.PrefSimulates.transfer
      (addNonstrategic_prefSimulates_euPref_flip G _ w hns hu hw) rfl h
  · exact GameForm.PrefSimulates.transfer
      (addNonstrategic_prefSimulates_euPref G _ w hns hu hw) rfl h

/-- **Correlated-equilibrium invariance.** A nonstrategic component for the
recommendation family preserves the correlated equilibria of any correlation
device: recommendation-dependent unilateral deviations see only utility
differences, which the flow fixes. -/
theorem isCorrelatedEq_addNonstrategic_iff [DecidableEq ι] (G : KernelGame ι)
    (w : G.Outcome → Payoff ι)
    (hns : G.NonstrategicForUnilateral G.toGameForm.recommendationDeviationFamily w)
    (hu : G.ExpectSummable G.utility) (hw : G.ExpectSummable w)
    (μ : PMF G.Profile) :
    (G.addNonstrategic w).IsCorrelatedEq μ ↔ G.IsCorrelatedEq μ := by
  rw [(G.addNonstrategic w).IsCorrelatedEq_iff_IsCorrelatedEqFor_eu,
    G.IsCorrelatedEq_iff_IsCorrelatedEqFor_eu]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact GameForm.PrefSimulates.transfer
      (addNonstrategic_prefSimulates_euPref_flip G _ w hns hu hw) rfl h
  · exact GameForm.PrefSimulates.transfer
      (addNonstrategic_prefSimulates_euPref G _ w hns hu hw) rfl h

/-!
### The concrete `w σ i = wᵢ(σ₋ᵢ)` justification

In a strategic-form game whose outcome is the played profile (`ofPureEU`), the
nonstrategic components are exactly the `w` whose `i`-component ignores player `i`'s
own strategy. Both the constant (Nash/CCE) and recommendation (CE) unilateral
families are nonstrategic for such a `w`, because a player's own deviation moves
only their own coordinate — on which `w σ i` does not depend.
-/

/-- `w` **depends only on opponents**: its `i`-component is unchanged by any move of
player `i`. This is the concrete flow shape `w σ i = wᵢ(σ₋ᵢ)`. -/
def DependsOnlyOnOthers {S : ι → Type} (w : (∀ i, S i) → Payoff ι) : Prop :=
  ∀ (i : ι) (σ σ' : ∀ j, S j), (∀ j, j ≠ i → σ j = σ' j) → w σ i = w σ' i

/-- For a strategic-form game (`ofPureEU`), the outcome mechanism is the identity
correlation device: the correlated outcome law of a profile distribution is that
distribution itself. -/
@[simp] theorem ofPureEU_correlatedOutcome (S : ι → Type) (u : (∀ i, S i) → Payoff ι)
    (ν : PMF (∀ i, S i)) :
    (ofPureEU S u).toGameForm.correlatedOutcome ν = ν := by
  simp only [GameForm.correlatedOutcome, ofPureEU, Kernel.pushforward]
  exact PMF.bind_pure ν

/-- The nonstrategic expectation is unmoved by any profile-update that keeps
coordinate `i` free: after the identity correlation device, `expect_map` pushes the
update inside, where `DependsOnlyOnOthers` makes it vanish. -/
theorem nonstrategic_expect_of_agree_off (S : ι → Type) (u : (∀ i, S i) → Payoff ι)
    (w : (∀ i, S i) → Payoff ι) (hw : DependsOnlyOnOthers w)
    (μ : PMF (∀ i, S i)) (i : ι) (g : (∀ j, S j) → (∀ j, S j))
    (hg : ∀ σ j, j ≠ i → g σ j = σ j) :
    expect ((ofPureEU S u).toGameForm.correlatedOutcome (μ.bind (fun σ => PMF.pure (g σ))))
        (fun o => w o i) =
      expect ((ofPureEU S u).toGameForm.correlatedOutcome μ) (fun o => w o i) := by
  rw [ofPureEU_correlatedOutcome, ofPureEU_correlatedOutcome]
  change expect (PMF.map g μ) (fun o => w o i) = expect μ (fun o => w o i)
  rw [expect_map]
  refine congrArg (expect μ) ?_
  funext σ
  exact hw i (g σ) σ (fun j hj => hg σ j hj)

/-- **Constant (Nash/CCE) deviations are nonstrategic** for an opponent-only `w` in
a strategic-form game: a constant unilateral replacement moves only the deviating
player's coordinate. -/
theorem ofPureEU_nonstrategic_constant [DecidableEq ι] (S : ι → Type)
    (u : (∀ i, S i) → Payoff ι) (w : (∀ i, S i) → Payoff ι)
    (hw : DependsOnlyOnOthers w) :
    (ofPureEU S u).NonstrategicForUnilateral
      (ofPureEU S u).toGameForm.constantDeviationProfileFamily w := by
  intro μ i d
  rw [GameForm.constantDeviationProfileFamily_deviate]
  unfold GameForm.constDeviateDistributionFn
  exact nonstrategic_expect_of_agree_off S u w hw μ i (fun σ => Function.update σ i d)
    (fun σ j hj => Function.update_of_ne hj d σ)

/-- **Recommendation (CE) deviations are nonstrategic** for an opponent-only `w` in
a strategic-form game: a recommendation-dependent unilateral deviation likewise
moves only the deviating player's coordinate. -/
theorem ofPureEU_nonstrategic_recommendation [DecidableEq ι] (S : ι → Type)
    (u : (∀ i, S i) → Payoff ι) (w : (∀ i, S i) → Payoff ι)
    (hw : DependsOnlyOnOthers w) :
    (ofPureEU S u).NonstrategicForUnilateral
      (ofPureEU S u).toGameForm.recommendationDeviationFamily w := by
  intro μ i dev
  rw [GameForm.recommendationDeviationFamily_deviate]
  unfold GameForm.deviateDistributionFn GameForm.deviateProfileFn
  exact nonstrategic_expect_of_agree_off S u w hw μ i (fun σ => Function.update σ i (dev (σ i)))
    (fun σ j hj => Function.update_of_ne hj (dev (σ i)) σ)

/-- Expected utility of a nonstrategic shift of a strategic-form game at a pure
profile: the base payoff plus the shift, both read off the played profile. -/
@[simp] theorem eu_addNonstrategic_ofPureEU (S : ι → Type) (u : (∀ i, S i) → Payoff ι)
    (w : (∀ i, S i) → Payoff ι) (σ : ∀ i, S i) (i : ι) :
    ((ofPureEU S u).addNonstrategic w).eu σ i = u σ i + w σ i := by
  simp only [KernelGame.eu, addNonstrategic, ofPureEU, expect_pure]

end KernelGame

/-!
## The coalition boundary

The flow determines the *unilateral* solution concepts (Nash / CE / CCE) but not
the *coalitional* ones. A nonstrategic component cancels in every unilateral
incentive constraint, but not in coalition constraints: when other coalition
members deviate, the opponents' strategies — on which each player's `w`-component
depends — change too, so `w` no longer cancels. The following two two-player games
have the same flow (identical Nash equilibria at every profile) yet differ on
strong Nash.
-/

namespace FlowInvarianceExample

open KernelGame

/-- The zero game on two `Bool`-strategy players: strategic-form, all payoffs `0`. -/
noncomputable def G₀ : KernelGame Bool := KernelGame.ofPureEU (fun _ => Bool) (fun _ _ => (0 : ℝ))

/-- A nonstrategic component in which each player's reward depends only on the
*other* player's move (`!p ≠ p` on `Bool`): player `p` is paid `1` when the
opponent plays `true`. This has the flow shape `w σ p = wₚ(σ₋ₚ)`. -/
def w : (Bool → Bool) → Payoff Bool := fun σ p => if σ (!p) then (1 : ℝ) else 0

/-- The same game with the nonstrategic component added. It has the same flow as
`G₀` — hence the same Nash equilibria — but its coalitional structure differs. -/
noncomputable def G₁ : KernelGame Bool := G₀.addNonstrategic w

theorem w_dependsOnlyOnOthers : DependsOnlyOnOthers w := by
  intro i σ σ' h
  simp only [w]
  rw [h (!i) (by cases i <;> decide)]

/-- **Same flow ⇒ same Nash.** Because `w` depends only on opponents, adding it does
not change any player's unilateral incentives, so `G₀` and `G₁` have identical Nash
equilibria at every profile. -/
theorem isNash_iff (σ : G₀.Profile) : G₁.IsNash σ ↔ G₀.IsNash σ := by
  haveI : Finite G₀.Outcome := inferInstanceAs (Finite (Bool → Bool))
  exact KernelGame.isNash_addNonstrategic_iff G₀ w
    (ofPureEU_nonstrategic_constant (fun _ => Bool) (fun _ _ => (0 : ℝ)) w w_dependsOnlyOnOthers)
    (KernelGame.ExpectSummable.of_finite G₀ G₀.utility)
    (KernelGame.ExpectSummable.of_finite G₀ w) σ

/-- In `G₀` the all-`false` profile is strong Nash: all payoffs are `0`, so no
coalition can strictly improve any member. -/
theorem g0_isStrongNash : G₀.IsStrongNash (fun _ => false) := by
  intro C τ _ i _
  simp [G₀]

/-- In `G₁` the all-`false` profile is **not** strong Nash: the grand coalition can
move to all-`true`, taking both players from `0` to `1` — a Pareto-improving joint
deviation. The nonstrategic component did not cancel across this coalition move. -/
theorem g1_not_isStrongNash : ¬ G₁.IsStrongNash (fun _ => false) := by
  intro hSN
  rw [KernelGame.isStrongNash_iff_no_profitableCoalitionDeviation] at hSN
  refine hSN Finset.univ (fun _ => true) ⟨fun i _ => ?_, false, Finset.mem_univ _, ?_⟩
  · rw [G₁.coalitionDeviation_univ]
    simp [G₁, G₀, w]
  · rw [G₁.coalitionDeviation_univ]
    simp [G₁, G₀, w]

end FlowInvarianceExample

end GameTheory
