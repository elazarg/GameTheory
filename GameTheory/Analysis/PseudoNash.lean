/-
# Pseudo-Nash against expected-utility concepts

For bounded utilities, the empirical-mean preference of a fixed game is
expected-utility preference: a law's constant utility ensemble computationally
mean-dominates another's exactly when its expected utility is at least as
large. So every equilibrium concept stated through a preference coincides for
the two. In particular, a profile of a fixed game is a pseudo-Nash equilibrium
exactly when it is a Nash equilibrium, and the same holds for the mixed
extension, whose outcome carrier is the game's. Likewise strong pseudo-Nash is
strong Nash, and pseudo-Nash with a constant payoff tolerance `ε` is `ε`-Nash.

The equality of preferences rests on sign balance: centred sums are positive
about as often as negative, at a polynomial rate. It is proved by Lindeberg
replacement against a symmetric `±σ` walk rather than by a Berry–Esseen bound.

In games whose play depends on the size, pseudo-Nash is bracketed by
expected-utility concepts under polynomially bounded payoffs: Nash with a
polynomial margin implies it, and it implies Nash up to negligible slack.

Primary reference: A. Psomas, A. Terzoglou, Y. Wei, and V. Zikas,
“Pseudo-Equilibria, or: How to Stop Worrying About Crypto and Just Analyze the
Game,” arXiv:2506.22089 (2025).
-/
import GameTheory.Core.Approximate
import GameTheory.Core.ExpectedUtility
import GameTheory.Core.PseudoNashCoalition
import GameTheory.Core.PseudoNashTolerance
import GameTheory.Math.Probability.MeanComparisonExpectation

noncomputable section

namespace GameTheory

open Filter GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι} {Outcome : Type uo}

/-- For bounded utilities, comparing constant utility ensembles by
computational mean dominance is comparing expected utilities. -/
theorem empiricalMeanPreference_eq_euPreference (utility : Outcome → ι → ℝ)
    (hbounded : ∀ who, ∃ C, ∀ outcome, |utility outcome who| ≤ C) :
    empiricalMeanPreference utility = euPreference utility := by
  funext who preferred alternative
  obtain ⟨C, hC⟩ := hbounded who
  have hsupport : ∀ law : PMF Outcome,
      ∀ x ∈ (law.map fun outcome => utility outcome who).support, |x| ≤ C := by
    intro law x hx
    rw [PMF.mem_support_map_iff] at hx
    obtain ⟨outcome, _, rfl⟩ := hx
    exact hC outcome
  have hmean : ∀ law : PMF Outcome,
      lawMean (law.map fun outcome => utility outcome who) =
        expectedUtility utility who law := by
    intro law
    rw [lawMean, expect_map]
    rfl
  apply propext
  rw [euPreference_iff_of_bounded utility who preferred alternative hC,
    empiricalMeanPreference_apply,
    computationallyMeanDominates_const_iff (hsupport preferred) (hsupport alternative),
    hmean, hmean]

/-- **Pseudo-Nash is Nash** in a fixed game with bounded utilities. -/
theorem ParameterizedGame.isPseudoNash_constant_iff_isNash [DecidableEq ι] (F : GameForm ι)
    (utility : F.sig.Outcome → ι → ℝ)
    (hbounded : ∀ who, ∃ C, ∀ outcome, |utility outcome who| ≤ C) (profile : Profile F.sig) :
    (ParameterizedGame.constant F utility).IsPseudoNash profile ↔
      IsNash F (euPreference utility) profile := by
  rw [ParameterizedGame.isPseudoNash_constant_iff,
    empiricalMeanPreference_eq_euPreference utility hbounded]

/-- **Strong pseudo-Nash is strong Nash** in a fixed game with bounded
utilities. -/
theorem ParameterizedGame.isStrongPseudoNash_constant_iff_isStrongNash [DecidableEq ι]
    (F : GameForm ι) (utility : F.sig.Outcome → ι → ℝ)
    (hbounded : ∀ who, ∃ C, ∀ outcome, |utility outcome who| ≤ C) (profile : Profile F.sig) :
    (ParameterizedGame.constant F utility).IsStrongPseudoNash profile ↔
      IsStrongNash F (euPreference utility) profile := by
  rw [ParameterizedGame.isStrongPseudoNash_constant_iff,
    empiricalMeanPreference_eq_euPreference utility hbounded]

private theorem lawMean_map_add {μ : PMF ℝ} {R : ℝ} (hμ : ∀ x ∈ μ.support, |x| ≤ R) (e : ℝ) :
    lawMean (μ.map (· + e)) = lawMean μ + e := by
  have hid : PayoffIntegrable μ id := payoffIntegrable_of_support_abs_le hμ id fun x hx => hx
  rw [lawMean, expect_map]
  change expect μ (fun x => id x + e) = _
  rw [expect_add hid (payoffIntegrable_constant μ e), expect_constant]

/-- **Constant payoff tolerance in a fixed game is `ε`-Nash**, for bounded
utilities. -/
theorem ParameterizedGame.isTolerantPseudoNash_constant_iff [DecidableEq ι] (F : GameForm ι)
    (utility : F.sig.Outcome → ι → ℝ)
    (hbounded : ∀ who, ∃ C, ∀ outcome, |utility outcome who| ≤ C) (ε : ℝ)
    (profile : Profile F.sig) :
    (ParameterizedGame.constant F utility).IsTolerantPseudoNash (fun _ => ε) profile ↔
      IsεNash F utility ε profile := by
  rw [ParameterizedGame.IsTolerantPseudoNash, IsεNash, isNash_iff]
  refine forall_congr' fun who => forall_congr' fun replacement => ?_
  obtain ⟨C, hC⟩ := hbounded who
  have hsupport : ∀ law : PMF F.sig.Outcome,
      ∀ x ∈ (law.map fun outcome => utility outcome who).support, |x| ≤ C := by
    intro law x hx
    rw [PMF.mem_support_map_iff] at hx
    obtain ⟨outcome, _, rfl⟩ := hx
    exact hC outcome
  have hshifted : ∀ law : PMF F.sig.Outcome,
      ∀ x ∈ ((law.map fun outcome => utility outcome who).map (· + ε)).support,
        |x| ≤ C + |ε| := by
    intro law x hx
    rw [PMF.mem_support_map_iff] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (abs_add_le _ _).trans (add_le_add (hsupport law y hy) le_rfl)
  have hmean : ∀ law : PMF F.sig.Outcome,
      lawMean (law.map fun outcome => utility outcome who) =
        expectedUtility utility who law := by
    intro law
    rw [lawMean, expect_map]
    rfl
  have hC0 : ∀ law : PMF F.sig.Outcome, ∀ x ∈ (law.map fun outcome => utility outcome who).support,
      |x| ≤ C + |ε| := fun law x hx => (hsupport law x hx).trans (le_add_of_nonneg_right
        (abs_nonneg ε))
  rw [euPreferenceWithin_iff ε utility who _ _
      (payoffIntegrable_of_bounded _ _ hC) (payoffIntegrable_of_bounded _ _ hC)]
  change ComputationallyMeanDominates
      (fun _ => ((F.play profile).map fun outcome => utility outcome who).map (· + ε))
      (fun _ => (F.play (Profile.update profile who replacement)).map
        fun outcome => utility outcome who) ↔ _
  rw [computationallyMeanDominates_const_iff (hshifted _) (hC0 _), lawMean_map_add (hsupport _),
    hmean, hmean]

/-! ## Parameterized games with polynomially bounded payoffs

When the game itself depends on the size, pseudo-Nash is bracketed by two
expected-utility concepts, both under payoffs bounded by a polynomial in the
size: Nash with a mean margin `κ ^ (-a)` for a fixed exponent `a` implies
pseudo-Nash, which implies Nash up to negligible slack. Nash at every size
implies neither: a strict margin that is negligible, or polynomial with an
exponent growing with the size, can be reversed at every polynomial number of
draws. -/

/-- The payoffs that occur are eventually bounded by a fixed power of the
size, for every player at every profile. -/
def ParameterizedGame.PolyBoundedPayoffs (G : ParameterizedGame.{uι, us, uo} ι) : Prop :=
  ∃ b : ℕ, ∀ᶠ κ : ℕ in atTop, ∀ who (profile : Profile G.sig),
    ∀ x ∈ (G.utilityLaw who profile κ).support, |x| ≤ (κ : ℝ) ^ b

/-- Nash up to negligible slack: no unilateral deviation gains a non-negligible
amount of expected utility. -/
def ParameterizedGame.IsNegligibleNash [DecidableEq ι] (G : ParameterizedGame.{uι, us, uo} ι)
    (profile : Profile G.sig) : Prop :=
  ∀ who (replacement : G.sig.Strategy who) (a : ℕ), ∀ᶠ κ : ℕ in atTop,
    lawMean (G.utilityLaw who (Profile.update profile who replacement) κ) ≤
      lawMean (G.utilityLaw who profile κ) + ((κ : ℝ) ^ a)⁻¹

/-- Nash with a polynomial margin: every unilateral deviation eventually either
leaves the deviator's utility law unchanged or loses at least `κ ^ (-a)` in
expectation, for an exponent `a` that may depend on the deviation but not on
the size. -/
def ParameterizedGame.IsPolynomiallyStrictNash [DecidableEq ι]
    (G : ParameterizedGame.{uι, us, uo} ι) (profile : Profile G.sig) : Prop :=
  ∀ who (replacement : G.sig.Strategy who), ∃ a : ℕ, ∀ᶠ κ : ℕ in atTop,
    G.utilityLaw who (Profile.update profile who replacement) κ = G.utilityLaw who profile κ ∨
      lawMean (G.utilityLaw who (Profile.update profile who replacement) κ) + ((κ : ℝ) ^ a)⁻¹ ≤
        lawMean (G.utilityLaw who profile κ)

private theorem eventually_support_le [DecidableEq ι] {G : ParameterizedGame.{uι, us, uo} ι}
    {b : ℕ} (hb : ∀ᶠ κ : ℕ in atTop, ∀ who (profile : Profile G.sig),
      ∀ x ∈ (G.utilityLaw who profile κ).support, |x| ≤ (κ : ℝ) ^ b)
    (who : ι) (profile : Profile G.sig) (replacement : G.sig.Strategy who) :
    ∀ᶠ κ : ℕ in atTop,
      (∀ x ∈ (G.utilityLaw who profile κ).support, |x| ≤ (κ : ℝ) ^ b) ∧
        ∀ y ∈ (G.utilityLaw who (Profile.update profile who replacement) κ).support,
          |y| ≤ (κ : ℝ) ^ b := by
  filter_upwards [hb] with κ hκ using ⟨hκ who profile, hκ who _⟩

/-- **Pseudo-Nash implies Nash up to negligible slack** when payoffs are
polynomially bounded. -/
theorem ParameterizedGame.isNegligibleNash_of_isPseudoNash [DecidableEq ι]
    {G : ParameterizedGame.{uι, us, uo} ι} (hG : G.PolyBoundedPayoffs)
    {profile : Profile G.sig} (h : G.IsPseudoNash profile) : G.IsNegligibleNash profile := by
  obtain ⟨b, hb⟩ := hG
  intro who replacement a
  exact lawMean_le_of_computationallyMeanDominates (eventually_support_le hb who profile
    replacement) ((ParameterizedGame.isPseudoNash_iff G profile).mp h who replacement) a

/-- **Nash with a polynomial margin is pseudo-Nash** when payoffs are
polynomially bounded. -/
theorem ParameterizedGame.isPseudoNash_of_isPolynomiallyStrictNash [DecidableEq ι]
    {G : ParameterizedGame.{uι, us, uo} ι} (hG : G.PolyBoundedPayoffs)
    {profile : Profile G.sig} (h : G.IsPolynomiallyStrictNash profile) :
    G.IsPseudoNash profile := by
  obtain ⟨b, hb⟩ := hG
  rw [ParameterizedGame.isPseudoNash_iff]
  intro who replacement
  obtain ⟨a, ha⟩ := h who replacement
  exact computationallyMeanDominates_of_polyMargin (a := a)
    (eventually_support_le hb who profile replacement) ha

end GameTheory
