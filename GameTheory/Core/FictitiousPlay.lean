/-
# Fictitious-play trajectories

Fictitious play repeatedly chooses a pure best response to the independent
empirical marginals of past play.  This file owns the topology-free state and
recurrence.  Claims about limits of these beliefs live in the analytic
consumer; the core interface itself is just finite-support probability and the
canonical best-response predicate.
-/

import GameTheory.Core.Mixed
import GameTheory.Core.Response

noncomputable section

namespace GameTheory

open Probability

universe uι us uo

namespace UtilityGame

variable {ι : Type uι}
variable (G : UtilityGame.{uι, us, uo} ι)

/-- The empirical law of one player's actions during the first `T` rounds. -/
def empiricalMarginal (history : ℕ → Profile G.form.sig) (who : ι)
    (T : ℕ) [NeZero T] : FinDist (G.form.sig.Strategy who) :=
  (FinDist.uniformFin T).map fun round : Fin T => history round.val who

/-- An empirical marginal is the uniform finite average of the matching past
actions. -/
theorem empiricalMarginal_prob (history : ℕ → Profile G.form.sig) (who : ι)
    (T : ℕ) [NeZero T] [DecidableEq (G.form.sig.Strategy who)]
    (action : G.form.sig.Strategy who) :
    (G.empiricalMarginal history who T).prob action =
      ((Finset.univ.filter fun round : Fin T => history round who = action).card : ℝ) / T := by
  rw [empiricalMarginal, FinDist.prob_map, FinDist.expect_uniformFin]
  simp [div_eq_mul_inv, mul_comm, eq_comm]

/-- Expectation under an empirical marginal is the ordinary finite average. -/
theorem empiricalMarginal_expect (history : ℕ → Profile G.form.sig) (who : ι)
    (T : ℕ) [NeZero T] (observable : G.form.sig.Strategy who → ℝ) :
    (G.empiricalMarginal history who T).expect observable =
      (∑ round : Fin T, observable (history round who)) / T := by
  rw [empiricalMarginal, FinDist.expect_map, FinDist.expect_uniformFin]

/-- Adding one observation updates every empirical expectation by the usual
running-average recurrence. -/
theorem empiricalMarginal_succ_expect (history : ℕ → Profile G.form.sig)
    (who : ι) (t : ℕ) (observable : G.form.sig.Strategy who → ℝ) :
    (G.empiricalMarginal history who (t + 2)).expect observable =
      ((t + 1 : ℝ) / (t + 2 : ℝ)) *
          (G.empiricalMarginal history who (t + 1)).expect observable +
        (1 / (t + 2 : ℝ)) * observable (history (t + 1) who) := by
  rw [G.empiricalMarginal_expect, G.empiricalMarginal_expect]
  have hsum :
      (∑ round : Fin (t + 2), observable (history round who)) =
        (∑ round : Fin (t + 1), observable (history round who)) +
          observable (history (t + 1) who) := by
    rw [show t + 2 = (t + 1) + 1 by omega, Fin.sum_univ_castSucc]
    rfl
  rw [hsum]
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp

/-- The independent empirical belief profile available after `T` rounds. -/
def empiricalBelief (history : ℕ → Profile G.form.sig) (T : ℕ) [NeZero T] :
    Profile G.form.sig.mixed :=
  fun who => G.empiricalMarginal history who T

variable [Fintype ι] [DecidableEq ι]

/-- A history is fictitious play when every action after the initial round is
a pure best response to the empirical belief formed from all earlier rounds.
The predicate reuses the canonical mixed extension and `IsBestResponse`; it is
not a parallel equilibrium or payoff semantics. -/
def IsFictitiousPlay (history : ℕ → Profile G.form.sig) : Prop :=
  ∀ (t : ℕ) (who : ι),
    IsBestResponse G.form.mixed (euPreference G.utility) who
      (G.empiricalBelief history (t + 1))
      (FinDist.pure (history (t + 1) who))

/-- The defining best-response obligation of fictitious play. -/
theorem IsFictitiousPlay.isBestResponse {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) (who : ι) :
    IsBestResponse G.form.mixed (euPreference G.utility) who
      (G.empiricalBelief history (t + 1))
      (FinDist.pure (history (t + 1) who)) :=
  hplay t who

end UtilityGame

end GameTheory
