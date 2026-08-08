/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticFinkObstruction
import Math.Probability.AnalyticOccupationRealization

/-!
# Player-owned analytic occupation responses

The occupation circulation supplied by the unrestricted family of all pure
deviations can mix deviations owned by several players. Such a mixed
circulation need not decompose into a circulation available to the owner of
the selected response.

For unilateral implementation the correct unconditional construction is to
run the analytic occupation alternative on the smaller operational family
consisting of:

* every prescribed baseline transition; and
* every pure deviation owned by the selected player.

The circulation branch is then player-owned by construction. In the
separator branch, the bounded potential controls arbitrary switching among
exactly the baseline and unilateral transitions available to that player.

This ownership theorem does not change the formal score orientation carried
by the Fink obstruction. In particular, it does not claim that a negatively
oriented Bellman charge becomes a profitable forward action, nor that the
sum of Bellman charges around the returned circulation is positive. Those
stronger conclusions require a separate nonnegative charge-lifting
hypothesis.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm

open Filter Math Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

/-- Baseline transitions together with all pure deviations of one fixed
player. The sum type records whether a step obeys the prescribed transition
or uses a player-owned pure response. -/
abbrev OwnerOccupationIndex
    (G : StochasticGame ι) (who : ι) :=
  G.State ⊕ (G.State × G.Act who)

/-- Embed the player-owned operational family into the unrestricted family
of all baseline and pure-deviation transitions. -/
def ownerOccupationIndexEmbedding
    (who : ι) :
    OwnerOccupationIndex G who →
      G.State ⊕ (Σ owner : ι, G.State × G.Act owner)
  | Sum.inl source => Sum.inl source
  | Sum.inr response =>
      Sum.inr ⟨who, response.1, response.2⟩

/-- Actual analytic occupation columns available to one deviating player:
all prescribed baseline transitions and that player's pure deviations. -/
def rawOwnerAnalyticOccupationColumn
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    ℝ → OwnerOccupationIndex G who → G.State → ℝ :=
  fun t index destination =>
    germ.rawAnalyticOccupationColumn t
      (ownerOccupationIndexEmbedding who index) destination

/-- Semantic transition kernel associated with a player-owned occupation
index at one valid positive germ parameter. -/
def finkOwnerActualOccupationKernelAt
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) :
    OwnerOccupationIndex G who → PMF G.State :=
  fun index =>
    germ.finkActualOccupationKernelAt ht
      (ownerOccupationIndexEmbedding who index)

/-- Source of a player-owned baseline or pure-deviation transition. -/
def ownerActualOccupationSource
    (who : ι) :
    OwnerOccupationIndex G who → G.State :=
  fun index =>
    finkActualOccupationSource
      (ownerOccupationIndexEmbedding who index)

/-- Every coordinate of the player-owned actual occupation family is
analytic because it is a restriction of the unrestricted analytic family. -/
theorem analytic_rawOwnerAnalyticOccupationColumn
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    ∀ index destination,
      AnalyticAt ℝ
        (fun t =>
          germ.rawOwnerAnalyticOccupationColumn
            who t index destination) 0 := by
  intro index destination
  exact germ.analytic_rawAnalyticOccupationColumn
    (ownerOccupationIndexEmbedding who index) destination

/-- Player-owned actual occupation columns have zero total mass throughout
the same punctured neighborhood as the unrestricted family. -/
theorem eventually_sum_rawOwnerAnalyticOccupationColumn_eq_zero
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ index,
        ∑ destination,
          germ.rawOwnerAnalyticOccupationColumn
            who t index destination = 0 := by
  filter_upwards [
    germ.eventually_sum_rawAnalyticOccupationColumn_eq_zero
  ] with t ht
  intro index
  exact ht (ownerOccupationIndexEmbedding who index)

/-- Pairing a player-owned raw occupation column with a potential is the
expected drift of its genuine semantic baseline or unilateral transition. -/
theorem potential_pair_rawOwnerAnalyticOccupationColumn_eq
    (germ : G.AnalyticBellmanGerm)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (who : ι) (potential : G.State → ℝ)
    (index : OwnerOccupationIndex G who) :
    (∑ destination,
      potential destination *
        germ.rawOwnerAnalyticOccupationColumn
          who t index destination) =
      expect
          (germ.finkOwnerActualOccupationKernelAt ht who index)
          potential -
        potential (ownerActualOccupationSource who index) := by
  exact germ.potential_pair_rawAnalyticOccupationColumn_eq
    ht potential (ownerOccupationIndexEmbedding who index)

namespace AnalyticOrientedFinkObstructionResponse

/-- The selected pure response, regarded as an element of the operational
family containing only its owner's deviations. -/
def ownerResponseIndex
    {germ : G.AnalyticBellmanGerm}
    {H K : G.State → Payoff ι}
    (C : AnalyticOrientedFinkObstructionResponse germ H K) :
    OwnerOccupationIndex G C.response.1 :=
  Sum.inr (C.response.2.1, C.response.2.2)

/-- **Owned operational occupation alternative.**

The selected analytic Fink response either belongs to a pole-cleared
nonnegative circulation using only prescribed transitions and pure
deviations of its owner, or it has a bounded analytic separator whose drift
is nonnegative under every transition in that same unilateral operational
family and is a positive power law on the selected response.

This theorem does not attempt to decompose a circulation that already uses
several owners. It reruns the exact finite alternative on the operational
family relevant to unilateral implementation. -/
theorem ownerAnalyticCirculation_xor_boundedPotential
    {germ : G.AnalyticBellmanGerm}
    {H K : G.State → Payoff ι}
    (C : AnalyticOrientedFinkObstructionResponse germ H K) :
    Xor
      (Nonempty
        (AnalyticPositiveCirculation
          (germ.rawOwnerAnalyticOccupationColumn C.response.1)
          C.ownerResponseIndex))
      (Nonempty
        (AnalyticBoundedOccupationSeparator
          (germ.rawOwnerAnalyticOccupationColumn C.response.1)
          C.ownerResponseIndex)) := by
  exact analyticPositiveCirculation_xor_boundedSeparator
    (germ.rawOwnerAnalyticOccupationColumn C.response.1)
    C.ownerResponseIndex
    (analytic_rawOwnerAnalyticOccupationColumn
      germ C.response.1)
    (eventually_sum_rawOwnerAnalyticOccupationColumn_eq_zero
      germ C.response.1)

/-- At a valid parameter in the owner-specific separator branch, every
baseline transition and every pure deviation of the selected owner has
nonnegative semantic potential drift. The selected response has the exact
positive analytic charge. -/
theorem ownerBoundedPotential_semanticDriftAt
    {germ : G.AnalyticBellmanGerm}
    {H K : G.State → Payoff ι}
    (C : AnalyticOrientedFinkObstructionResponse germ H K)
    (B : AnalyticBoundedOccupationSeparator
      (germ.rawOwnerAnalyticOccupationColumn C.response.1)
      C.ownerResponseIndex)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) germ.radius)
    (hB :
      (∀ destination,
        0 ≤ B.potential t destination ∧
          B.potential t destination ≤ 1) ∧
      (∀ index :
          {index : OwnerOccupationIndex G C.response.1 //
            index ≠ C.ownerResponseIndex},
        0 ≤ ∑ destination,
          B.potential t destination *
            germ.rawOwnerAnalyticOccupationColumn
              C.response.1 t index.1 destination) ∧
      (∑ destination,
        B.potential t destination *
          germ.rawOwnerAnalyticOccupationColumn
            C.response.1 t C.ownerResponseIndex destination) =
        B.charge * t ^ B.poleOrder) :
    (∀ index : OwnerOccupationIndex G C.response.1,
      0 ≤
        expect
            (germ.finkOwnerActualOccupationKernelAt
              ht C.response.1 index)
            (B.potential t) -
          B.potential t
            (ownerActualOccupationSource C.response.1 index)) ∧
    expect
          (germ.finkOwnerActualOccupationKernelAt
            ht C.response.1 C.ownerResponseIndex)
          (B.potential t) -
        B.potential t
          (ownerActualOccupationSource
            C.response.1 C.ownerResponseIndex) =
      B.charge * t ^ B.poleOrder := by
  have hpair (index : OwnerOccupationIndex G C.response.1) :=
    germ.potential_pair_rawOwnerAnalyticOccupationColumn_eq
      ht C.response.1 (B.potential t) index
  constructor
  · intro index
    rw [← hpair index]
    by_cases hi : index = C.ownerResponseIndex
    · subst index
      rw [hB.2.2]
      exact mul_nonneg B.charge_pos.le
        (pow_nonneg (le_of_lt ht.1) _)
    · exact hB.2.1 ⟨index, hi⟩
  · rw [← hpair C.ownerResponseIndex]
    exact hB.2.2

/-- In the owner-specific separator branch, arbitrary history-dependent
switching between obedience and pure deviations of the selected owner can
use the selected response only a bounded expected number of times. The bound
is uniform over the unilateral switching rule at each fixed valid
parameter. -/
theorem eventually_ownerSelectedUseBudget
    {germ : G.AnalyticBellmanGerm}
    {H K : G.State → Payoff ι}
    (C : AnalyticOrientedFinkObstructionResponse germ H K)
    (B : AnalyticBoundedOccupationSeparator
      (germ.rawOwnerAnalyticOccupationColumn C.response.1)
      C.ownerResponseIndex) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ (ht : t ∈ Ioo (0 : ℝ) germ.radius)
        (initial : G.State)
        (choice :
          ∀ n, (Fin (n + 1) → G.State) →
            OwnerOccupationIndex G C.response.1),
        (∀ n history,
          ownerActualOccupationSource
              C.response.1 (choice n history) =
            history (Fin.last n)) →
        ∀ T,
          (B.charge * t ^ B.poleOrder) *
              expect
                (adaptiveHistoryLaw
                  (adaptiveMarkovStep initial
                    (selectedTransitionComparison
                      (germ.finkOwnerActualOccupationKernelAt
                        ht C.response.1)
                      choice))
                  (T + 1))
                (selectedTransitionUseCount
                  choice C.ownerResponseIndex T) ≤
            1 := by
  filter_upwards [B.eventual] with t hB
  intro ht initial choice hsource T
  obtain ⟨hdrift, hmargin⟩ :=
    C.ownerBoundedPotential_semanticDriftAt B ht hB
  exact margin_mul_expect_selectedTransitionUseCount_le_one
    initial
    (germ.finkOwnerActualOccupationKernelAt ht C.response.1)
    (ownerActualOccupationSource C.response.1)
    choice C.ownerResponseIndex (B.potential t)
    hB.1 hsource hdrift hmargin.ge T

/-- Behavioral-strategy form of the owner-specific separator budget.

The unilateral selector may randomize after every finite state history.
The separator bounds the expected cumulative conditional probability mass
assigned to the distinguished response, rather than only the use count of a
pure history-dependent selector. -/
theorem eventually_ownerSelectedMassBudget
    {germ : G.AnalyticBellmanGerm}
    {H K : G.State → Payoff ι}
    (C : AnalyticOrientedFinkObstructionResponse germ H K)
    (B : AnalyticBoundedOccupationSeparator
      (germ.rawOwnerAnalyticOccupationColumn C.response.1)
      C.ownerResponseIndex) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ (ht : t ∈ Ioo (0 : ℝ) germ.radius)
        (initial : G.State)
        (selection :
          ∀ n, (Fin (n + 1) → G.State) →
            PMF (OwnerOccupationIndex G C.response.1)),
        (∀ n history index,
          selection n history index ≠ 0 →
            ownerActualOccupationSource C.response.1 index =
              history (Fin.last n)) →
        ∀ T,
          (B.charge * t ^ B.poleOrder) *
              expect
                (adaptiveHistoryLaw
                  (adaptiveMarkovStep initial
                    (mixedTransitionComparison
                      (germ.finkOwnerActualOccupationKernelAt
                        ht C.response.1)
                      selection))
                  (T + 1))
                (selectedTransitionMassSum
                  selection C.ownerResponseIndex T) ≤
            1 := by
  filter_upwards [B.eventual] with t hB
  intro ht initial selection hsource T
  obtain ⟨hdrift, hmargin⟩ :=
    C.ownerBoundedPotential_semanticDriftAt B ht hB
  exact margin_mul_expect_selectedTransitionMassSum_le_one
    initial
    (germ.finkOwnerActualOccupationKernelAt ht C.response.1)
    (ownerActualOccupationSource C.response.1)
    selection C.ownerResponseIndex (B.potential t)
    hB.1 hsource hdrift hmargin.ge T

end AnalyticOrientedFinkObstructionResponse

end AnalyticBellmanGerm
end StochasticGame
end GameTheory
