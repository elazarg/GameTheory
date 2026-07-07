/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Mechanism.BayesianGame
import Math.Fintype

/-!
# Games in informational form

Prior-free games of incomplete information. Each player receives a private
signal and then chooses an action; payoffs depend on the full signal profile and
the realized action profile. Adding a prior turns such a game into a
`BayesianGame`.

This is intentionally smaller than the full Bayesian-game layer: it captures
the ex-post and signal-blind transfer notions used in Monderer--Tennenholtz's
discussion of k-implementation under incomplete information.
-/

namespace GameTheory

/-- A prior-free game with private signals and signal-contingent payoffs. -/
structure InformationalGame (ι : Type) where
  /-- Private signal/type space for each player. -/
  Signal : ι → Type
  /-- Action space for each player. -/
  Act : ι → Type
  /-- Payoff at a full signal profile and realized action profile. -/
  utility : (∀ i, Signal i) → (∀ i, Act i) → Payoff ι

namespace InformationalGame

variable {ι : Type} [DecidableEq ι]

/-- A full signal profile. -/
abbrev SignalProfile (G : InformationalGame ι) := ∀ i, G.Signal i

/-- A realized action profile. -/
abbrev ActionProfile (G : InformationalGame ι) := ∀ i, G.Act i

/-- A pure strategy maps a player's private signal to an action. -/
abbrev Strategy (G : InformationalGame ι) (i : ι) := G.Signal i → G.Act i

/-- A profile of pure signal-contingent strategies. -/
abbrev StrategyProfile (G : InformationalGame ι) := ∀ i, G.Strategy i

/-- The action profile induced by a pure strategy profile at a signal profile. -/
def play (G : InformationalGame ι) (σ : G.StrategyProfile)
    (θ : G.SignalProfile) : G.ActionProfile :=
  fun i => σ i (θ i)

/-- Ex-post equilibrium: at every signal profile, no player can profitably
deviate from the action prescribed by their strategy. -/
def IsExPostEq (G : InformationalGame ι) (σ : G.StrategyProfile) : Prop :=
  ∀ (θ : G.SignalProfile) (i : ι) (a : G.Act i),
    G.utility θ (G.play σ θ) i ≥
      G.utility θ (Function.update (G.play σ θ) i a) i

/-- A signal-blind transfer depends only on the realized action profile. -/
abbrev ActionTransfer (G : InformationalGame ι) := G.ActionProfile → Payoff ι

/-- Utility after adding a signal-blind transfer. -/
def subsidizedUtility (G : InformationalGame ι) (V : G.ActionTransfer)
    (θ : G.SignalProfile) (a : G.ActionProfile) (i : ι) : ℝ :=
  G.utility θ a i + V a i

/-- Ex-post equilibrium after signal-blind transfers. -/
def IsExPostEqWithTransfer (G : InformationalGame ι) (V : G.ActionTransfer)
    (σ : G.StrategyProfile) : Prop :=
  ∀ (θ : G.SignalProfile) (i : ι) (a : G.Act i),
    G.subsidizedUtility V θ (G.play σ θ) i ≥
      G.subsidizedUtility V θ (Function.update (G.play σ θ) i a) i

/-- Signal-blind ex-post dominance for one player's signal-contingent strategy.
The comparison is pointwise in the full signal profile and in all opponent
action profiles. -/
def IsExPostDominantStrategyWithTransfer (G : InformationalGame ι)
    (V : G.ActionTransfer) (i : ι) (b : G.Strategy i) : Prop :=
  ∀ (θ : G.SignalProfile) (a : G.ActionProfile) (a' : G.Act i),
    G.subsidizedUtility V θ (Function.update a i (b (θ i))) i ≥
      G.subsidizedUtility V θ (Function.update a i a') i

/-- Every player's strategy is ex-post dominant after signal-blind transfers. -/
def IsExPostDominantProfileWithTransfer (G : InformationalGame ι)
    (V : G.ActionTransfer) (σ : G.StrategyProfile) : Prop :=
  ∀ i : ι, G.IsExPostDominantStrategyWithTransfer V i (σ i)

/-- A minimal signal-blind ex-post-dominant k-implementation notion for games
in informational form: transfers are nonnegative, the target strategy profile is
ex-post dominant, and payments on target play are bounded by `k` at every signal
profile. -/
def IsSignalBlindExPostDominantKImplementation (G : InformationalGame ι)
    [Fintype ι] (V : G.ActionTransfer) (σ : G.StrategyProfile) (k : ℝ) : Prop :=
  (∀ a i, 0 ≤ V a i) ∧
    G.IsExPostDominantProfileWithTransfer V σ ∧
      ∀ θ : G.SignalProfile, (∑ i, V (G.play σ θ) i) ≤ k

/-- Signal-blind weak dominance between signal-contingent strategies after
transfers. The comparison is pointwise in the full signal profile and every
opponent action profile. -/
def WeaklyDominatesWithTransfer (G : InformationalGame ι)
    (V : G.ActionTransfer) (i : ι) (b c : G.Strategy i) : Prop :=
  ∀ (θ : G.SignalProfile) (a : G.ActionProfile),
    G.subsidizedUtility V θ (Function.update a i (b (θ i))) i ≥
      G.subsidizedUtility V θ (Function.update a i (c (θ i))) i

/-- Signal-blind weak dominance with an existential strict pointwise witness. -/
def WeaklyStrictlyDominatesWithTransfer (G : InformationalGame ι)
    (V : G.ActionTransfer) (i : ι) (b c : G.Strategy i) : Prop :=
  G.WeaklyDominatesWithTransfer V i b c ∧
    ∃ (θ : G.SignalProfile) (a : G.ActionProfile),
      G.subsidizedUtility V θ (Function.update a i (b (θ i))) i >
        G.subsidizedUtility V θ (Function.update a i (c (θ i))) i

/-- Undominated signal-contingent strategies under signal-blind weak dominance
with a strict witness. -/
def IsUndominatedWithTransfer (G : InformationalGame ι)
    (V : G.ActionTransfer) (i : ι) (b : G.Strategy i) : Prop :=
  ∀ c : G.Strategy i, ¬ G.WeaklyStrictlyDominatesWithTransfer V i c b

/-- Strategy profiles whose every signal-contingent component is undominated. -/
def undominatedStrategyProfilesWithTransfer (G : InformationalGame ι)
    (V : G.ActionTransfer) : Set G.StrategyProfile :=
  {σ | ∀ i, G.IsUndominatedWithTransfer V i (σ i)}

/-- Signal-blind implementation in informational games via undominated
signal-contingent strategies. -/
def IsSignalBlindImplementation (G : InformationalGame ι)
    (V : G.ActionTransfer) (O : Set G.StrategyProfile) : Prop :=
  (∀ a i, 0 ≤ V a i) ∧
    (G.undominatedStrategyProfilesWithTransfer V).Nonempty ∧
      ∀ σ : G.StrategyProfile,
        σ ∈ G.undominatedStrategyProfilesWithTransfer V → σ ∈ O

/-- k-bounded signal-blind implementation in informational games. Transfers are
bounded on every realized signal profile of every surviving strategy profile. -/
def IsSignalBlindKImplementation (G : InformationalGame ι) [Fintype ι]
    (V : G.ActionTransfer) (O : Set G.StrategyProfile) (k : ℝ) : Prop :=
  G.IsSignalBlindImplementation V O ∧
    ∀ σ : G.StrategyProfile,
      σ ∈ G.undominatedStrategyProfilesWithTransfer V →
        ∀ θ : G.SignalProfile, (∑ i, V (G.play σ θ) i) ≤ k

theorem IsExPostDominantProfileWithTransfer.toExPostEqWithTransfer
    {G : InformationalGame ι} {V : G.ActionTransfer} {σ : G.StrategyProfile}
    (h : G.IsExPostDominantProfileWithTransfer V σ) :
    G.IsExPostEqWithTransfer V σ := by
  intro θ i a
  have hi := h i θ (G.play σ θ) a
  have hsame : Function.update (G.play σ θ) i (σ i (θ i)) = G.play σ θ := by
    funext j
    by_cases hji : j = i
    · subst hji
      simp [play]
    · simp [Function.update_of_ne hji]
  simpa [subsidizedUtility, hsame] using hi

theorem IsSignalBlindExPostDominantKImplementation.nonneg
    {G : InformationalGame ι} [Fintype ι] {V : G.ActionTransfer}
    {σ : G.StrategyProfile} {k : ℝ}
    (h : G.IsSignalBlindExPostDominantKImplementation V σ k) :
    ∀ a i, 0 ≤ V a i :=
  h.1

theorem IsSignalBlindExPostDominantKImplementation.exPostDominantProfile
    {G : InformationalGame ι} [Fintype ι] {V : G.ActionTransfer}
    {σ : G.StrategyProfile} {k : ℝ}
    (h : G.IsSignalBlindExPostDominantKImplementation V σ k) :
    G.IsExPostDominantProfileWithTransfer V σ :=
  h.2.1

theorem IsSignalBlindExPostDominantKImplementation.cost_bound
    {G : InformationalGame ι} [Fintype ι] {V : G.ActionTransfer}
    {σ : G.StrategyProfile} {k : ℝ}
    (h : G.IsSignalBlindExPostDominantKImplementation V σ k) :
    ∀ θ : G.SignalProfile, (∑ i, V (G.play σ θ) i) ≤ k :=
  h.2.2

theorem WeaklyStrictlyDominatesWithTransfer.irrefl
    {G : InformationalGame ι} {V : G.ActionTransfer} {i : ι}
    (b : G.Strategy i) :
    ¬ G.WeaklyStrictlyDominatesWithTransfer V i b b := by
  rintro ⟨_, θ, a, hstrict⟩
  exact lt_irrefl _ hstrict

theorem WeaklyStrictlyDominatesWithTransfer.trans
    {G : InformationalGame ι} {V : G.ActionTransfer} {i : ι}
    {a b c : G.Strategy i}
    (hab : G.WeaklyStrictlyDominatesWithTransfer V i a b)
    (hbc : G.WeaklyStrictlyDominatesWithTransfer V i b c) :
    G.WeaklyStrictlyDominatesWithTransfer V i a c := by
  refine ⟨?_, ?_⟩
  · intro θ σ
    exact le_trans (hbc.1 θ σ) (hab.1 θ σ)
  · obtain ⟨θ, σ, hstrict⟩ := hab.2
    refine ⟨θ, σ, ?_⟩
    have hbc_weak := hbc.1 θ σ
    linarith

/-- On a finite signal-contingent strategy set, every strategy is either
undominated or dominated by an undominated strategy. -/
theorem exists_undominated_or_dominator_withTransfer
    {G : InformationalGame ι} {V : G.ActionTransfer} {i : ι}
    [Finite (G.Strategy i)] (b : G.Strategy i) :
    ∃ t : G.Strategy i,
      G.IsUndominatedWithTransfer V i t ∧
        (t = b ∨ G.WeaklyStrictlyDominatesWithTransfer V i t b) := by
  exact Math.exists_maximal_or_rel_of_finite_trans_irrefl
    (G.WeaklyStrictlyDominatesWithTransfer V i)
    (fun a b c hab hbc =>
      WeaklyStrictlyDominatesWithTransfer.trans hab hbc)
    (fun a => WeaklyStrictlyDominatesWithTransfer.irrefl a)
    b

/-- On a finite signal-contingent strategy set, every dominated strategy is
dominated by an undominated strategy. -/
theorem exists_undominated_dominator_withTransfer
    {G : InformationalGame ι} {V : G.ActionTransfer} {i : ι}
    [Finite (G.Strategy i)] {b : G.Strategy i}
    (hdominated :
      ∃ t : G.Strategy i, G.WeaklyStrictlyDominatesWithTransfer V i t b) :
    ∃ t : G.Strategy i,
      G.IsUndominatedWithTransfer V i t ∧
        G.WeaklyStrictlyDominatesWithTransfer V i t b := by
  exact Math.exists_maximal_rel_of_finite_trans_irrefl
    (G.WeaklyStrictlyDominatesWithTransfer V i)
    (fun a b c hab hbc =>
      WeaklyStrictlyDominatesWithTransfer.trans hab hbc)
    (fun a => WeaklyStrictlyDominatesWithTransfer.irrefl a)
    hdominated

theorem IsSignalBlindImplementation.nonneg
    {G : InformationalGame ι} {V : G.ActionTransfer} {O : Set G.StrategyProfile}
    (h : G.IsSignalBlindImplementation V O) :
    ∀ a i, 0 ≤ V a i :=
  h.1

theorem IsSignalBlindImplementation.nonempty
    {G : InformationalGame ι} {V : G.ActionTransfer} {O : Set G.StrategyProfile}
    (h : G.IsSignalBlindImplementation V O) :
    (G.undominatedStrategyProfilesWithTransfer V).Nonempty :=
  h.2.1

theorem IsSignalBlindImplementation.subset
    {G : InformationalGame ι} {V : G.ActionTransfer} {O : Set G.StrategyProfile}
    (h : G.IsSignalBlindImplementation V O) :
    ∀ σ : G.StrategyProfile,
      σ ∈ G.undominatedStrategyProfilesWithTransfer V → σ ∈ O :=
  h.2.2

theorem IsSignalBlindKImplementation.implementation
    {G : InformationalGame ι} [Fintype ι] {V : G.ActionTransfer}
    {O : Set G.StrategyProfile} {k : ℝ}
    (h : G.IsSignalBlindKImplementation V O k) :
    G.IsSignalBlindImplementation V O :=
  h.1

theorem singleton_target_undominated_of_isSignalBlindImplementation
    {G : InformationalGame ι} {V : G.ActionTransfer} {σ : G.StrategyProfile}
    (h : G.IsSignalBlindImplementation V ({σ} : Set G.StrategyProfile)) :
    σ ∈ G.undominatedStrategyProfilesWithTransfer V := by
  obtain ⟨τ, hτ⟩ := h.nonempty
  have hτσ : τ = σ := Set.mem_singleton_iff.mp (h.subset τ hτ)
  rwa [← hτσ]

/-- If a signal-blind transfer implements a singleton strategy profile by
undominated signal-contingent strategies, then that profile is ex-post dominant
under the same transfer. -/
theorem singleton_signalBlindImplementation_isExPostDominant
    {G : InformationalGame ι} [∀ i, Finite (G.Strategy i)]
    {V : G.ActionTransfer} {σ : G.StrategyProfile}
    (h : G.IsSignalBlindImplementation V ({σ} : Set G.StrategyProfile)) :
    G.IsExPostDominantProfileWithTransfer V σ := by
  classical
  intro i θ a a'
  by_cases ha' : a' = σ i (θ i)
  · simp [subsidizedUtility, ha']
  let c : G.Strategy i := Function.update (σ i) (θ i) a'
  have hc_ne : c ≠ σ i := by
    intro hc
    have hcθ := congrFun hc (θ i)
    simp [c, ha'] at hcθ
  have hσundom :=
    singleton_target_undominated_of_isSignalBlindImplementation (G := G) h
  have hc_not_undom : ¬ G.IsUndominatedWithTransfer V i c := by
    intro hcundom
    have hprof :
        Function.update σ i c ∈ G.undominatedStrategyProfilesWithTransfer V := by
      intro j
      by_cases hji : j = i
      · subst hji
        simpa using hcundom
      · simpa [Function.update_of_ne hji] using hσundom j
    have hmem := h.subset (Function.update σ i c) hprof
    have heq : Function.update σ i c = σ := Set.mem_singleton_iff.mp hmem
    have hc_eq : c = σ i := by
      simpa using congrFun heq i
    exact hc_ne hc_eq
  have hc_dominated :
      ∃ t : G.Strategy i, G.WeaklyStrictlyDominatesWithTransfer V i t c := by
    by_contra hnone
    exact hc_not_undom (by
      intro t ht
      exact hnone ⟨t, ht⟩)
  obtain ⟨t, htundom, htc⟩ :=
    exists_undominated_dominator_withTransfer (G := G) (V := V) hc_dominated
  have htprof :
      Function.update σ i t ∈ G.undominatedStrategyProfilesWithTransfer V := by
    intro j
    by_cases hji : j = i
    · subst hji
      simpa using htundom
    · simpa [Function.update_of_ne hji] using hσundom j
  have htmem := h.subset (Function.update σ i t) htprof
  have hteq : Function.update σ i t = σ := Set.mem_singleton_iff.mp htmem
  have ht_eq : t = σ i := by
    simpa using congrFun hteq i
  have hσc : G.WeaklyStrictlyDominatesWithTransfer V i (σ i) c := by
    simpa [ht_eq] using htc
  have hweak := hσc.1 θ a
  simpa [c, subsidizedUtility] using hweak

/-- Add a common prior to a game in informational form. -/
def toBayesianGame (G : InformationalGame ι) (prior : PMF G.SignalProfile) :
    BayesianGame ι where
  Θ := G.Signal
  Act := G.Act
  prior := prior
  utility := G.utility

/-- Ex-post equilibrium is Bayes-Nash for every finite-support common prior. -/
theorem IsExPostEq.toBayesNash {G : InformationalGame ι}
    [Finite G.SignalProfile] {σ : G.StrategyProfile}
    (h : G.IsExPostEq σ) (prior : PMF G.SignalProfile) :
    (G.toBayesianGame prior).BayesNash σ := by
  rw [BayesianGame.bayesNash_iff_exAnteEU]
  intro who s'
  change
    Math.Probability.expect prior
        (fun θ => G.utility θ (fun i => (Function.update σ who s') i (θ i)) who) ≤
      Math.Probability.expect prior
        (fun θ => G.utility θ (G.play σ θ) who)
  apply Math.Probability.expect_mono
  intro θ
  have hdevActions :
      (fun i => (Function.update σ who s') i (θ i)) =
        Function.update (G.play σ θ) who (s' (θ who)) := by
    funext i
    by_cases hi : i = who
    · subst hi
      simp
    · simp [play, Function.update_of_ne hi]
  have hpoint := h θ who (s' (θ who))
  simpa [hdevActions] using hpoint

end InformationalGame

end GameTheory
