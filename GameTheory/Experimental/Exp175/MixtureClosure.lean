module

/-
EXP-175: binary convexity does not imply closure under arbitrary PMF mixtures.

A total preorder ranks infinite-support laws above finite-support laws. It
respects every binary mixture but a countable mixture of indifferent point
masses escapes a finite-support bound. Direct client prototypes distinguish
full weak comparison from exclusion of a strict gain, retaining each numerical
client's source of actual-law expectation-definedness.
-/

public import GameTheory.Core.Utility
public import GameTheory.Tests.InfiniteExpectation

@[expose] public section

noncomputable section

namespace GameTheory.Experimental.MixtureClosure

open GameTheory.Math.Probability

/-- Infinite-support laws form the preferred indifference class; all
finite-support laws form the other class. -/
def supportPreference : WeakPreference Unit ℕ :=
  fun _ preferred alternative => preferred.support.Infinite ∨ alternative.support.Finite

theorem supportPreference_reflexive : Preference.Reflexive supportPreference := by
  classical
  intro _ law
  by_cases hfinite : law.support.Finite
  · exact Or.inr hfinite
  · exact Or.inl hfinite

theorem supportPreference_transitive : Preference.Transitive supportPreference := by
  intro _ preferred middle alternative hfirst hsecond
  rcases hfirst with hpreferred | hmiddle
  · exact Or.inl hpreferred
  · rcases hsecond with hmiddleInfinite | halternative
    · exact (hmiddleInfinite hmiddle).elim
    · exact Or.inr halternative

theorem supportPreference_total : Preference.Total supportPreference := by
  classical
  intro _ preferred alternative
  by_cases hfinite : preferred.support.Finite
  · exact Or.inr (Or.inr hfinite)
  · exact Or.inl (Or.inl hfinite)

/-- A binary mixture cannot introduce an outcome absent from both laws. -/
theorem support_mix_subset_union (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (μ ν : PMF ℕ) : (mix t h0 h1 μ ν).support ⊆ μ.support ∪ ν.support := by
  classical
  intro a ha
  by_cases hμ : a ∈ μ.support
  · exact Or.inl hμ
  by_cases hν : a ∈ ν.support
  · exact Or.inr hν
  have hzero : mix t h0 h1 μ ν a = 0 := by
    rw [mix_apply, (μ.apply_eq_zero_iff a).2 hμ, (ν.apply_eq_zero_iff a).2 hν]
    simp
  exact (((mix t h0 h1 μ ν).mem_support_iff a).1 ha hzero).elim

theorem finite_support_mix (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    {μ ν : PMF ℕ} (hμ : μ.support.Finite) (hν : ν.support.Finite) :
    (mix t h0 h1 μ ν).support.Finite :=
  (hμ.union hν).subset (support_mix_subset_union t h0 h1 μ ν)

/-- Every positive component of a binary mixture contributes all its
supported outcomes. Together with the union bound, this characterizes finite
support for interior mixture weights. -/
theorem finite_support_mix_iff (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (ht0 : 0 < t) (ht1 : t < 1) (μ ν : PMF ℕ) :
    (mix t h0 h1 μ ν).support.Finite ↔ μ.support.Finite ∧ ν.support.Finite := by
  constructor
  · intro hfinite
    exact ⟨hfinite.subset (fun _ ha => mem_support_mix_left t h0 h1 ht0 ha),
      hfinite.subset (fun _ ha => mem_support_mix_right t h0 h1 ht1 ha)⟩
  · rintro ⟨hμ, hν⟩
    exact finite_support_mix t h0 h1 hμ hν

/-- Finite binary mixing respects the support-size classes, including weights
zero and one. This does not assert closure under countable mixtures. -/
theorem supportPreference_convex : Preference.Convex supportPreference := by
  classical
  intro _ t h0 h1 firstPreferred firstAlternative secondPreferred secondAlternative
    hfirst hsecond
  by_cases ht0 : t = 0
  · subst t
    simpa only [mix_zero] using hsecond
  by_cases ht1 : t = 1
  · subst t
    simpa only [mix_one] using hfirst
  have ht0pos : 0 < t := lt_of_le_of_ne h0 (Ne.symm ht0)
  have ht1lt : t < 1 := lt_of_le_of_ne h1 ht1
  change firstPreferred.support.Infinite ∨ firstAlternative.support.Finite at hfirst
  change secondPreferred.support.Infinite ∨ secondAlternative.support.Finite at hsecond
  change (mix t h0 h1 firstPreferred secondPreferred).support.Infinite ∨
    (mix t h0 h1 firstAlternative secondAlternative).support.Finite
  by_cases hinfiniteFirst : firstPreferred.support.Infinite
  · exact Or.inl (Set.Infinite.mono
      (fun _ ha => mem_support_mix_left t h0 h1 ht0pos ha) hinfiniteFirst)
  by_cases hinfiniteSecond : secondPreferred.support.Infinite
  · exact Or.inl (Set.Infinite.mono
      (fun _ ha => mem_support_mix_right t h0 h1 ht1lt ha) hinfiniteSecond)
  exact Or.inr (finite_support_mix t h0 h1
    (hfirst.resolve_left hinfiniteFirst) (hsecond.resolve_left hinfiniteSecond))

/-- An infinite-support law is strictly preferred to every point mass. -/
theorem supportPreference_strict_pure (law : PMF ℕ) (hinfinite : law.support.Infinite)
    (n : ℕ) : Preference.strict supportPreference () law (PMF.pure n) := by
  change (law.support.Infinite ∨ (PMF.pure n).support.Finite) ∧
    ¬ ((PMF.pure n).support.Infinite ∨ law.support.Finite)
  refine ⟨Or.inl hinfinite, ?_⟩
  rintro (hpure | hlaw)
  · apply hpure
    simpa only [PMF.support_pure] using Set.finite_singleton n
  · exact hinfinite hlaw

open GameTheory.Tests.InfiniteExpectation in
/-- Every natural has positive mass in this countably supported law. -/
theorem halving_support : halving.support = Set.univ := by
  apply Set.eq_univ_of_forall
  intro n
  rw [PMF.mem_support_iff]
  show ENNReal.ofReal ((1 : ℝ) / 2 / 2 ^ n) ≠ 0
  exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'

open GameTheory.Tests.InfiniteExpectation in
theorem halving_support_infinite : halving.support.Infinite := by
  rw [halving_support]
  exact Set.infinite_univ

/-- Every deterministic component is indifferent to the finite-support base. -/
theorem every_pure_below_base (n : ℕ) :
    supportPreference () (PMF.pure 0) (PMF.pure n) := by
  right
  simpa only [PMF.support_pure] using Set.finite_singleton n

open GameTheory.Tests.InfiniteExpectation in
/-- Binary convexity, even with a total preorder, does not preserve this upper
bound when countably many pure laws are mixed. -/
theorem countable_mixture_escapes_bound :
    ¬ supportPreference () (PMF.pure 0) (halving.bind PMF.pure) := by
  rw [PMF.bind_pure]
  exact (supportPreference_strict_pure halving halving_support_infinite 0).2

open GameTheory.Tests.InfiniteExpectation in
theorem binary_convex_not_countably_closed :
    Preference.Reflexive supportPreference ∧
    Preference.Transitive supportPreference ∧
    Preference.Total supportPreference ∧
    Preference.Convex supportPreference ∧
    (∀ n : ℕ, supportPreference () (PMF.pure 0) (PMF.pure n)) ∧
    ¬ supportPreference () (PMF.pure 0) (halving.bind PMF.pure) :=
  ⟨supportPreference_reflexive, supportPreference_transitive,
    supportPreference_total, supportPreference_convex, every_pure_below_base,
    countable_mixture_escapes_bound⟩



open GameTheory.Math.Probability

universe uι us uo uα uΩ

/-- Pure tests suffice when the actual family of pure deviation laws has an
upper contour closed under its supported mixtures. -/
theorem isNash_mixed_iff_of_bind_comparisons
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (F : GameForm.{uι, us, uo} ι)
    (prefers : WeakPreference ι F.sig.Outcome)
    (profile : Profile F.sig.mixed)
    (hclose : ∀ who (μ : PMF (F.sig.Strategy who)),
      (∀ a ∈ μ.support, prefers who (F.mixed.play profile)
        (F.mixed.play (Profile.update profile who (PMF.pure a)))) →
      prefers who (F.mixed.play profile)
        (μ.bind fun a => F.mixed.play (Profile.update profile who (PMF.pure a)))) :
    IsNash F.mixed prefers profile ↔
      ∀ who a, prefers who (F.mixed.play profile)
        (F.mixed.play (Profile.update profile who (PMF.pure a))) := by
  rw [isNash_iff]
  constructor
  · intro hnash who a
    exact hnash who (PMF.pure a)
  · intro hpure who μ
    have hbound := hclose who μ (fun a _ => hpure who a)
    have hlaw := GameForm.mixed_play_update F profile who μ
    exact (congrArg (prefers who (F.mixed.play profile)) hlaw).mpr hbound

/-- Expected utility supplies the local closure only after the actual mixture
is known to have an expectation. No condition on unrelated laws is required. -/
theorem eu_isNash_mixed_iff_of_bind_comparisons
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (F : GameForm.{uι, us, uo} ι) (utility : Utility F.sig)
    (profile : Profile F.sig.mixed)
    (hdev : ∀ who (replacement : PMF (F.sig.Strategy who)),
      UtilityHasExpectation utility who
        (F.mixed.play (Profile.update profile who replacement))) :
    IsNash F.mixed (euPreference utility) profile ↔
      ∀ who a, euPreference utility who (F.mixed.play profile)
        (F.mixed.play (Profile.update profile who (PMF.pure a))) := by
  apply isNash_mixed_iff_of_bind_comparisons F (euPreference utility) profile
  intro who μ hpure
  apply euPreference_bind μ _ hpure
  rw [← GameForm.mixed_play_update F profile who μ]
  exact hdev who μ

/-- For ruling out strict gains, the positive half of the alleged strict gain
may itself supply the domain guard needed by the closure argument. -/
theorem not_strict_bind_of_guarded_comparisons
    {Ω : Type uΩ} {α : Type uα}
    (prefers : PMF Ω → PMF Ω → Prop) (μ : PMF α) (q : α → PMF Ω)
    (base : PMF Ω)
    (hclose : prefers (μ.bind q) base →
      (∀ a ∈ μ.support, prefers base (q a)) → prefers base (μ.bind q))
    (hpure : ∀ a ∈ μ.support, prefers base (q a)) :
    ¬ Rank.strict prefers (μ.bind q) base := by
  rintro ⟨hguard, hnot⟩
  exact hnot (hclose hguard hpure)

/-- A strict expected-utility gain carries its own expectation guard, so this
contradiction requires no extra assumption on the mixed law. -/
theorem eu_no_strict_bind_gain
    {Ω : Type uΩ} {α : Type uα} {ι : Type uι}
    (utility : Ω → ι → ℝ) (who : ι)
    (μ : PMF α) (q : α → PMF Ω) (base : PMF Ω)
    (hpure : ∀ a ∈ μ.support, euPreference utility who base (q a)) :
    ¬ Rank.strict (euPreference utility who) (μ.bind q) base :=
  not_strict_bind_of_guarded_comparisons (euPreference utility who) μ q base
    (fun hguard hall => euPreference_bind μ q hall hguard.1) hpure


end GameTheory.Experimental.MixtureClosure
