/-
# Pseudo-Nash is Nash in fixed games

For bounded utilities, the empirical-mean preference of a fixed game is
expected-utility preference: a law's constant utility ensemble computationally
mean-dominates another's exactly when its expected utility is at least as
large. So every equilibrium concept stated through a preference coincides for
the two. In particular, a profile of a fixed game is a pseudo-Nash equilibrium
exactly when it is a Nash equilibrium, and the same holds for the mixed
extension, whose outcome carrier is the game's.

The equality of preferences rests on sign balance: centred sums are positive
about as often as negative, at a polynomial rate. It is proved by Lindeberg
replacement against a symmetric `±σ` walk rather than by a Berry–Esseen bound.

Primary reference: A. Psomas, A. Terzoglou, Y. Wei, and V. Zikas,
“Pseudo-Equilibria, or: How to Stop Worrying About Crypto and Just Analyze the
Game,” arXiv:2506.22089 (2025).
-/
import GameTheory.Core.PseudoNash
import GameTheory.Core.ExpectedUtility
import GameTheory.Math.Probability.MeanComparisonExpectation

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι uo

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
  rw [euPreference_iff_of_bounded utility who preferred alternative hC, empiricalMeanPreference,
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

end GameTheory
