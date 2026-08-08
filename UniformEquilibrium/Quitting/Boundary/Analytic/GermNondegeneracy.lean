/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Analytic.Germ
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct

/-!
# The germ's quit family is nondegenerate off the zero-solo class

`QuittingAnalyticGerm.lean` feeds the quit-rate family of an analytic Bellman
germ to `Math.AnalyticOrderComparison` and obtains a converging normalized
direction, but only under an undischarged hypothesis:

    ∃ i, ¬ ∀ᶠ t in 𝓝[>] 0, quittingGermQuitRate g i t = 0

("somebody quits with positive probability arbitrarily close to `t = 0`").
This file discharges it, and in the favourable direction: its failure lands
*exactly* in a class that is already solved.

## The argument

Suppose every coordinate's quit rate is eventually zero on the right.  The
index set is finite, so the finitely many `∀ᶠ` statements intersect
(`Filter.eventually_all`), and `𝓝[>] (0:ℝ)` is `NeBot`, so there is a genuine
parameter `t` with `0 < t`, `t < 1`, `t < g.radius`, and
`quittingGermQuitRate g i t = 0` for **every** `i`.  At such a `t`:

* the decoded row is all-continue — a Boolean marginal with zero real quit mass
  is `PMF.pure false` (`quittingGermRoot_eq_quittingAllContinueRoot`);
* the germ's active value **vanishes**
  (`quittingGermValue_eq_zero_of_forall_quittingGermQuitRate_eq_zero`).  This
  step needs the *Bellman equality*, not just the two best-response
  inequalities: at the all-continue row the one-stage successor payoff is the
  continuation itself, so the recursion reads `W = (1 - t^q) * W`, and `t > 0`
  forces `W = 0`.  The inequalities alone would only bound `W`;
* hence the endpoint gap is `Σ_i - (A_i + c_{-i} * W_i) = r_i({i}) - 0`, and
  complementarity at continue-mass `1` gives `r_i({i}) ≤ 0` at every `i` —
  which is `IsQuittingZeroSolo reward`.

The `t < 1` condition is not decorative: it is what makes the discount factor
`1 - t ^ g.ramification` strictly positive, which
`isεQuittingRootEndpointNash_quittingGermRoot` requires.  Every `𝓝[>] 0`
eventually-statement supplies it, but it has to be taken.

## Main results

* `isQuittingZeroSolo_of_eventually_quittingGermQuitRate_eq_zero` — the core
  implication (1)
* `exists_not_eventually_quittingGermQuitRate_eq_zero_of_not_isQuittingZeroSolo`
  — its contrapositive, the usable form (2)
* `quittingGerm_zeroSolo_or_leadingOrderNormalization` — the dichotomy (3),
  marked `HEADLINE`
* `exists_quittingGermQuitRate_leadingOrder_normalization_of_not_isQuittingZeroSolo`
  — the entry point of `QuittingAnalyticGerm` with the germ-internal
  nondegeneracy hypothesis replaced by `¬ IsQuittingZeroSolo reward` (4)
* `exists_quittingGermAbsorption_leadingOrder_normalization_of_not_isQuittingZeroSolo`
  — the same, read on the germ's absorption `1 - ∏_j (1 - y_j)`, with the
  matching branch pinned rather than squeezed
-/

noncomputable section

namespace GameTheory

open Filter Set Topology
open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## An all-continue parameter of the germ -/

/-- **A parameter with all quit rates zero decodes to the all-continue row.**
A Boolean marginal whose real quit mass vanishes is `PMF.pure false`. -/
theorem quittingGermRoot_eq_quittingAllContinueRoot
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius)
    (hzero : ∀ i, quittingGermQuitRate g i t = 0) :
    quittingGermRoot g ht = (quittingAllContinueRoot : ι → PMF Bool) := by
  funext i
  change quittingGermRoot g ht i = PMF.pure false
  refine pmf_eq_pure_false_of_apply_true_toReal_eq_zero _ ?_
  rw [quittingGermRoot_apply_true_toReal g ht i, hzero i]

/-- **At an all-continue parameter the germ's active value vanishes.**

This is where the *Bellman equality* is indispensable.  At the all-continue
row the one-stage successor payoff is exactly the continuation vector, so the
active-state recursion of the germ reads `W = (1 - t ^ q) * W`; since `t > 0`
the factor `t ^ q` is nonzero and `W = 0`.  The two best-response inequalities
alone do not give this: they only compare `W` with the two endpoint payoffs. -/
theorem quittingGermValue_eq_zero_of_forall_quittingGermQuitRate_eq_zero
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius)
    (hzero : ∀ i, quittingGermQuitRate g i t = 0) :
    quittingGermValue g t = (0 : Payoff ι) := by
  funext who
  have hrec := quittingGermValue_eq_smul_rootSuccessorPayoff g ht who
  rw [quittingGermRoot_eq_quittingAllContinueRoot g ht hzero,
    quittingRootSuccessorPayoff_allContinueRoot_eq reward
      (quittingGermValue g t)] at hrec
  have hpow : (0 : ℝ) < t ^ g.ramification := pow_pos ht.1 _
  have hmul : t ^ g.ramification * quittingGermValue g t who = 0 := by
    linear_combination hrec
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd h (ne_of_gt hpow)
  · simpa using h

/-- **The core implication, at one parameter.**  If every quit rate vanishes
at a parameter `0 < t < min (g.radius) 1`, then the weight is zero-solo.

At that parameter the decoded row is all-continue, the active value is `0`, so
the germ's endpoint gap is `r_i({i}) - 0`; complementarity at continue-mass
`1` (i.e. `y_i = 0 < 1`) forces it to be nonpositive at every coordinate. -/
theorem isQuittingZeroSolo_of_forall_quittingGermQuitRate_eq_zero
    (g : (quittingGame reward).AnalyticBellmanGerm) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) g.radius) (ht1 : t < 1)
    (hzero : ∀ i, quittingGermQuitRate g i t = 0) :
    IsQuittingZeroSolo reward := by
  intro who
  have hnash := isεQuittingRootEndpointNash_quittingGermRoot g ht ht1 who
  rw [quittingGermRoot_eq_quittingAllContinueRoot g ht hzero,
    quittingGermValue_eq_zero_of_forall_quittingGermQuitRate_eq_zero g ht
      hzero] at hnash
  have hquit := hnash.1
  rw [quittingRootEndpointDifference_allContinueRoot] at hquit
  simpa [quittingAllContinueRoot] using hquit

/-! ## The core implication and its contrapositive -/

/-- **(1) The core implication.**  If every coordinate's quit rate is
eventually zero to the right of `0`, then the weight is zero-solo.

The index set is finite, so the finitely many eventually-statements intersect;
`𝓝[>] (0:ℝ)` is `NeBot`, so the intersection produces a genuine parameter,
which additionally satisfies `t < 1` and `t < g.radius` because those hold
eventually too. -/
theorem isQuittingZeroSolo_of_eventually_quittingGermQuitRate_eq_zero
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hzero : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ), quittingGermQuitRate g i t = 0) :
    IsQuittingZeroSolo reward := by
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, quittingGermQuitRate g i t = 0 :=
    Filter.eventually_all.mpr hzero
  have hone : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 := Iio_mem_nhds (by norm_num)
  have hlt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    hone.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht, ht1, hz⟩ :=
    ((eventually_mem_Ioo_radius g).and (hlt.and hall)).exists
  exact isQuittingZeroSolo_of_forall_quittingGermQuitRate_eq_zero g ht ht1 hz

/-- **(2) The contrapositive, the usable form.**  On a weight that is *not*
zero-solo, every analytic Bellman germ has a nondegenerate quit family.  So
the hypothesis `hne` of
`exists_quittingGermQuitRate_leadingOrder_normalization` is automatic on
exactly the weights the quitting program still has open. -/
theorem exists_not_eventually_quittingGermQuitRate_eq_zero_of_not_isQuittingZeroSolo
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hnot : ¬IsQuittingZeroSolo reward) :
    ∃ i, ¬∀ᶠ t in 𝓝[>] (0 : ℝ), quittingGermQuitRate g i t = 0 := by
  by_contra hc
  exact hnot (isQuittingZeroSolo_of_eventually_quittingGermQuitRate_eq_zero g
    fun i => not_not.mp fun hi => hc ⟨i, hi⟩)

/-- The same statement in the "not everybody continues near `0`" phrasing of
`exists_not_eventually_quittingGermQuitRate_eq_zero_iff`.

The converse fails: a zero-solo weight may perfectly well carry a germ whose
quit rates are not identically zero, so this is an implication and not an
equivalence. -/
theorem not_eventually_forall_quittingGermQuitRate_eq_zero_of_not_isQuittingZeroSolo
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hnot : ¬IsQuittingZeroSolo reward) :
    ¬∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, quittingGermQuitRate g i t = 0 :=
  (exists_not_eventually_quittingGermQuitRate_eq_zero_iff g).mp
    (exists_not_eventually_quittingGermQuitRate_eq_zero_of_not_isQuittingZeroSolo
      g hnot)

/-! ## The leading-order package, named -/

/-- The conclusion of `exists_quittingGermQuitRate_leadingOrder_normalization`,
named so that the dichotomy below can carry it as a disjunct: a least order
`m`, a nonnegative leading vector `a` with positive total supported exactly on
the leading set, positivity of the total quit mass to the right of `0`,
convergence of every normalized quit share, and the three-way comparison of the
exact discount complement `t ^ g.ramification` against the total quit mass. -/
def QuittingGermLeadingOrderNormalization
    (g : (quittingGame reward).AnalyticBellmanGerm) : Prop :=
  ∃ (m : ℕ) (a : ι → ℝ),
    Math.familyAnalyticOrder (quittingGermQuitRate g) = m ∧
    (∀ i, 0 ≤ a i) ∧
    (0 < ∑ j, a j) ∧
    (∀ i, a i ≠ 0 ↔ i ∈ Math.leadingSet (quittingGermQuitRate g)) ∧
    (∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ∑ j, quittingGermQuitRate g j t) ∧
    (∀ i, Tendsto
      (fun t => quittingGermQuitRate g i t / ∑ j, quittingGermQuitRate g j t)
      (𝓝[>] (0 : ℝ)) (𝓝 (a i / ∑ j, a j))) ∧
    (m < g.ramification → Tendsto
      (fun t : ℝ => t ^ g.ramification / ∑ j, quittingGermQuitRate g j t)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
    (g.ramification = m → Tendsto
      (fun t : ℝ => t ^ g.ramification / ∑ j, quittingGermQuitRate g j t)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / ∑ j, a j))) ∧
    (g.ramification < m → Tendsto
      (fun t : ℝ => t ^ g.ramification / ∑ j, quittingGermQuitRate g j t)
      (𝓝[>] (0 : ℝ)) atTop)

/-- **(4) The usable entry point.**  The leading-order normalization of a
germ's quit family, with the germ-internal nondegeneracy hypothesis replaced
by the weight-level condition `¬ IsQuittingZeroSolo reward`. -/
theorem exists_quittingGermQuitRate_leadingOrder_normalization_of_not_isQuittingZeroSolo
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hnot : ¬IsQuittingZeroSolo reward) :
    ∃ (m : ℕ) (a : ι → ℝ),
      Math.familyAnalyticOrder (quittingGermQuitRate g) = m ∧
      (∀ i, 0 ≤ a i) ∧
      (0 < ∑ j, a j) ∧
      (∀ i, a i ≠ 0 ↔ i ∈ Math.leadingSet (quittingGermQuitRate g)) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ∑ j, quittingGermQuitRate g j t) ∧
      (∀ i, Tendsto
        (fun t => quittingGermQuitRate g i t / ∑ j, quittingGermQuitRate g j t)
        (𝓝[>] (0 : ℝ)) (𝓝 (a i / ∑ j, a j))) ∧
      (m < g.ramification → Tendsto
        (fun t : ℝ => t ^ g.ramification / ∑ j, quittingGermQuitRate g j t)
        (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
      (g.ramification = m → Tendsto
        (fun t : ℝ => t ^ g.ramification / ∑ j, quittingGermQuitRate g j t)
        (𝓝[>] (0 : ℝ)) (𝓝 (1 / ∑ j, a j))) ∧
      (g.ramification < m → Tendsto
        (fun t : ℝ => t ^ g.ramification / ∑ j, quittingGermQuitRate g j t)
        (𝓝[>] (0 : ℝ)) atTop) :=
  exists_quittingGermQuitRate_leadingOrder_normalization g
    (exists_not_eventually_quittingGermQuitRate_eq_zero_of_not_isQuittingZeroSolo
      g hnot)

/-- **The absorption form of the entry point.**  The three-way comparison of
the exact discount complement `t ^ q` against the germ's *absorption*
`1 - ∏_j (1 - y_j)`, with the germ-internal nondegeneracy hypothesis replaced
by `¬ IsQuittingZeroSolo reward`.

In the matching branch the absorption's own analytic order and leading
coefficient are pinned — order exactly `m`, leading coefficient exactly
`∑ j, a j` — so the limit is `1 / ∑ j, a j` and not merely something between
`1 / (|ι| · ∑ j, a j)` and `1 / ∑ j, a j`. -/
theorem exists_quittingGermAbsorption_leadingOrder_normalization_of_not_isQuittingZeroSolo
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hnot : ¬IsQuittingZeroSolo reward) :
    ∃ (m : ℕ) (a : ι → ℝ),
      Math.familyAnalyticOrder (quittingGermQuitRate g) = m ∧
      (∀ i, 0 ≤ a i) ∧
      (0 < ∑ j, a j) ∧
      (∀ i, a i ≠ 0 ↔ i ∈ Math.leadingSet (quittingGermQuitRate g)) ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < quittingGermAbsorption g t) ∧
      (m < g.ramification → Tendsto
        (fun t : ℝ => t ^ g.ramification / quittingGermAbsorption g t)
        (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
      (g.ramification = m →
        analyticOrderAt (quittingGermAbsorption g) 0 = m ∧
        Tendsto (fun t : ℝ => quittingGermAbsorption g t / t ^ m)
          (𝓝[>] (0 : ℝ)) (𝓝 (∑ j, a j)) ∧
        Tendsto (fun t : ℝ => t ^ g.ramification / quittingGermAbsorption g t)
          (𝓝[>] (0 : ℝ)) (𝓝 (1 / ∑ j, a j))) ∧
      (g.ramification < m → Tendsto
        (fun t : ℝ => t ^ g.ramification / quittingGermAbsorption g t)
        (𝓝[>] (0 : ℝ)) atTop) :=
  exists_quittingGermAbsorption_leadingOrder_normalization g
    (exists_not_eventually_quittingGermQuitRate_eq_zero_of_not_isQuittingZeroSolo
      g hnot)

/-- The named form of the entry point. -/
theorem quittingGermLeadingOrderNormalization_of_not_isQuittingZeroSolo
    (g : (quittingGame reward).AnalyticBellmanGerm)
    (hnot : ¬IsQuittingZeroSolo reward) :
    QuittingGermLeadingOrderNormalization g :=
  exists_quittingGermQuitRate_leadingOrder_normalization_of_not_isQuittingZeroSolo
    g hnot

/-! ## The dichotomy -/

/-- **(3) The dichotomy.**  For every quitting weight and every analytic
Bellman germ of it, exactly one of two already-usable things happens:

* the weight is zero-solo, and then the landed
  `quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo` hands over the
  zero vector as a uniform equilibrium payoff outright; or
* the germ's quit family is nondegenerate and the whole leading-order
  normalization package of `QuittingAnalyticGerm` applies — with **no**
  undischarged side condition.

`HEADLINE` — this removes the one hypothesis that the analytic-germ route
carried, by showing its failure is not a gap but the solved branch: a
downstream argument may case on this disjunction and never carry a
nondegeneracy premise.  What it does **not** do is prove that the second
branch leads anywhere: it supplies a converging normalized quit direction and
a comparison of the ramification `q` with the family order `m`, and says
nothing about whether that data yields a uniform equilibrium payoff.  It also
says nothing about which of the two branches a given weight falls into beyond
the sign test `r_i({i}) ≤ 0`, and nothing about the *existence* of the
associated equilibrium in the second branch. -/
theorem quittingGerm_zeroSolo_or_leadingOrderNormalization
    (g : (quittingGame reward).AnalyticBellmanGerm) :
    (IsQuittingZeroSolo reward ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none (0 : Payoff ι)) ∨
      QuittingGermLeadingOrderNormalization g := by
  by_cases hzs : IsQuittingZeroSolo reward
  · exact Or.inl ⟨hzs,
      quittingGame_isUniformEquilibriumPayoff_zero_of_zeroSolo reward hzs⟩
  · exact Or.inr
      (quittingGermLeadingOrderNormalization_of_not_isQuittingZeroSolo g hzs)

/-- The dichotomy with the germ produced on the spot: every quitting weight
admits an analytic Bellman germ, so the disjunction above is available for
every weight without any germ having to be supplied. -/
theorem exists_analyticBellmanGerm_zeroSolo_or_leadingOrderNormalization
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ g : (quittingGame reward).AnalyticBellmanGerm,
      (IsQuittingZeroSolo reward ∧
          (quittingGame reward).IsUniformEquilibriumPayoff none
            (0 : Payoff ι)) ∨
        QuittingGermLeadingOrderNormalization g := by
  obtain ⟨g⟩ := nonempty_analyticBellmanGerm_quittingGame reward
  exact ⟨g, quittingGerm_zeroSolo_or_leadingOrderNormalization g⟩

end GameTheory
