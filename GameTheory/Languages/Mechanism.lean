/-
# Direct-revelation mechanisms

A mechanism asks each agent to report something private and maps the reports to
an outcome. The question this encoding answers is whether mechanism design needs
its own solution concept, and the answer is no: *strategyproofness is
`IsDominantProfile` of the induced game form*, with truthful reporting as the
profile. Nothing is defined twice, and the definition below is an abbreviation
rather than a new predicate.

The instance is the two-bidder second-price auction, where truth is dominant,
paired with the first-price auction, where it is not. The second half is what
makes the first half informative: an encoding that quietly made every report
equivalent would satisfy the strategyproofness theorem and fail the refutation.

Read the workarounds at the bottom before concluding anything from either.
-/

import GameTheory.Core.Response
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory.Languages

open GameTheory Probability

universe uι us

/-- Each agent reports something private; the mechanism maps the reports to an
outcome. -/
structure Mechanism (ι : Type uι) where
  /-- What agent `i` is asked to report. -/
  Report : ι → Type us
  /-- What the mechanism produces. -/
  Outcome : Type us
  /-- How the reports are resolved. -/
  choose : (∀ i, Report i) → Outcome

namespace Mechanism

variable {ι : Type uι} [DecidableEq ι] (M : Mechanism ι)

/-- The induced game form: a report is a strategy, and the mechanism is played
deterministically. -/
@[reducible]
def toForm : GameForm ι where
  sig := { Strategy := M.Report, Outcome := M.Outcome }
  play reports := FinDist.pure (M.choose reports)

/-- **Strategyproofness is dominance**, and this is a definition only in the
sense that it names an existing one. A mechanism is strategyproof for a given
notion of truth when reporting truthfully is dominant for every agent, whatever
the others report. -/
def IsStrategyproof (utility : M.Outcome → ι → ℝ) (truth : ∀ i, M.Report i) : Prop :=
  IsDominantProfile M.toForm (euPreference utility) truth

omit [DecidableEq ι] in
/-- What an agent gets, read off the outcome the reports produce. -/
theorem utility_toForm (utility : M.Outcome → ι → ℝ) (reports : ∀ i, M.Report i) (who : ι) :
    expectedUtility utility who (M.toForm.play reports) = utility (M.choose reports) who :=
  FinDist.expect_pure ..

/-- Strategyproofness unfolded to the comparison it actually makes: no report
beats the truth against any profile of the others' reports. -/
theorem isStrategyproof_iff (utility : M.Outcome → ι → ℝ) (truth : ∀ i, M.Report i) :
    M.IsStrategyproof utility truth ↔
      ∀ (who : ι) (misreport : M.Report who) (reports : Profile M.toForm.sig),
        utility (M.choose (Profile.update reports who misreport)) who ≤
          utility (M.choose (Profile.update reports who (truth who))) who := by
  constructor
  · intro hproof who misreport reports
    have := hproof who misreport reports
    rwa [euPreference_apply, utility_toForm, utility_toForm] at this
  · intro hbeat who misreport reports
    rw [euPreference_apply, utility_toForm, utility_toForm]
    exact hbeat who misreport reports

end Mechanism

/-! ## The two-bidder auctions

Both auctions award the item to the higher bidder and break ties in favour of
the first. They differ only in what the winner pays, and that difference is the
whole of the theory below. -/

/-- Who won and what they pay. -/
abbrev Award := Fin 2 × ℝ

/-- The winner's surplus is their private value less the price; the loser gets
nothing. -/
def surplus (value : Fin 2 → ℝ) (award : Award) (who : Fin 2) : ℝ :=
  if award.1 = who then value who - award.2 else 0

/-- **The second-price auction.** The higher bidder wins and pays the other
bid. -/
@[reducible]
def vickrey : Mechanism (Fin 2) where
  Report _ := ℝ
  Outcome := Award
  choose bids := if bids 0 < bids 1 then (1, bids 0) else (0, bids 1)

/-- **The first-price auction.** The higher bidder wins and pays their own
bid. -/
@[reducible]
def firstPrice : Mechanism (Fin 2) where
  Report _ := ℝ
  Outcome := Award
  choose bids := if bids 0 < bids 1 then (1, bids 1) else (0, bids 0)

/-- **Truthful bidding is dominant in the second-price auction.** The winner's
price does not depend on their own bid, so the bid only decides *whether* they
win — and bidding their value makes them win exactly when winning is worth
having. -/
theorem vickrey_isStrategyproof (value : Fin 2 → ℝ) :
    vickrey.IsStrategyproof (surplus value) value := by
  rw [Mechanism.isStrategyproof_iff]
  intro who misreport bids
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) who with rfl | rfl
  · show surplus value (if _ < _ then _ else _) 0 ≤ surplus value (if _ < _ then _ else _) 0
    rw [Profile.update_same, Profile.update_of_ne _ _ (by decide),
      Profile.update_same, Profile.update_of_ne _ _ (by decide)]
    unfold surplus
    split_ifs <;> (simp_all; try linarith)
  · show surplus value (if _ < _ then _ else _) 1 ≤ surplus value (if _ < _ then _ else _) 1
    rw [Profile.update_same, Profile.update_of_ne _ _ (by decide),
      Profile.update_same, Profile.update_of_ne _ _ (by decide)]
    unfold surplus
    split_ifs <;> (simp_all; try linarith)

/-- What the first bidder's report buys them, with the other report fixed. -/
theorem firstPrice_choose_zero (reports : Profile firstPrice.toForm.sig) (bid : ℝ) :
    firstPrice.choose (Profile.update reports 0 bid) =
      if bid < reports 1 then (1, reports 1) else (0, bid) := by
  show (if Profile.update reports 0 bid 0 < Profile.update reports 0 bid 1 then _ else _) = _
  rw [Profile.update_same, Profile.update_of_ne _ _ (by decide)]

/-- **And it is not dominant in the first-price auction.** Against an opponent
bidding nothing, a bidder who values the item at one and says so pays exactly
what it is worth to them; shading the bid to a half wins the same item for
half the price.

This is the discriminating probe. The theorem above would be equally true of an
encoding in which no report ever mattered, and this one would not. -/
theorem firstPrice_not_isStrategyproof :
    ¬ firstPrice.IsStrategyproof (surplus ![1, 1]) ![1, 1] := by
  rw [Mechanism.isStrategyproof_iff]
  intro hproof
  have hbeat := hproof 0 (1 / 2) ![1, 0]
  rw [firstPrice_choose_zero, firstPrice_choose_zero] at hbeat
  norm_num [surplus] at hbeat

/-! ## Workarounds

Each concession the encoding makes, stated plainly.

*Two bidders, not `n`.* The general auction needs the highest of a finite family
of bids and a tie-breaking rule over it. That is arithmetic rather than
architecture — nothing in the interface resists it — but it is not done here,
and until it is, no statement below should be read as covering the general case.

*Real-valued money.* Reports are real numbers, so the strategy carriers are
infinite. The executable frontend cannot touch these games and neither can the
existence theorem. Dominance needs neither, which is why the flagship of
mechanism design is provable at this layer and the flagship of equilibrium
theory is not.

*No revelation principle.* Nothing here proves that restricting attention to
direct mechanisms is without loss. That statement quantifies over all
mechanisms, including indirect ones, and there is no encoding of an indirect
mechanism in this module to quantify over.

*No participation or budget conditions.* Individual rationality and budget
balance are not stated, so "strategyproof" here means exactly dominance of truth
and nothing more. A mechanism that charged every agent a thousand regardless of
outcome would satisfy every theorem in this module.

*The truth is a parameter.* `IsStrategyproof` takes the truthful report profile
as an argument rather than deriving it. For an auction the truth is the agent's
own valuation and the identification is invisible, because a report and a value
are both reals; for a mechanism whose report type differs from its type space it
would be a real modelling obligation.

The finding, as distinct from the concessions: the encoding needed no new
solution concept, no fake agents, and no extension of the game form.
`IsStrategyproof` is `IsDominantProfile` with the truthful profile substituted,
and `isStrategyproof_iff` is the proof that unfolding it reaches the inequality
an economist would write. -/

end GameTheory.Languages
