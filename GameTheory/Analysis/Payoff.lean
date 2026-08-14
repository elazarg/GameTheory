/-
# The mixed payoff as a polynomial in the weights

Expected utility of a mixed profile is defined through composition of laws,
which is the right definition and the wrong shape for topology. Written out over
the finite profile space it is a polynomial: a sum over pure profiles of the
product of the players' weights times that profile's utility.

That rewriting is what buys continuity, and it buys one more thing that matters
as much. Exactly one factor of each product belongs to any given player, so the
payoff is *affine* in one player's weights with the others held fixed. Affine in
each coordinate separately is what makes a best-response set convex, and convex
best responses are the hypothesis a set-valued fixed-point theorem cannot do
without.
-/

import GameTheory.Analysis.Simplex
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory

open Probability

universe uι us uo

variable {ι : Type uι} [Fintype ι] [DecidableEq ι] {F : GameForm ι}
variable [∀ i, Fintype (F.sig.Strategy i)]

variable (F) in
/-- The expected utility of a mixed profile, written as a polynomial in the
players' weight vectors. -/
def payoff (utility : F.sig.Outcome → ι → ℝ) (who : ι) (x : Profile F.sig.weights) : ℝ :=
  ∑ s : Profile F.sig, (∏ i, x i (s i)) * expectedUtility utility who (F.play s)

variable {utility : F.sig.Outcome → ι → ℝ}

/-- On the weights of an actual mixed profile the polynomial *is* the expected
utility. Everything proved about the polynomial therefore transfers back. -/
theorem payoff_probs (μ : Profile F.sig.mixed) (who : ι) :
    payoff F utility who (probs F.sig μ) = expectedUtility utility who (F.mixed.play μ) := by
  show _ = ((FinDist.pi μ).bind F.play).expect _
  rw [FinDist.expect_bind, FinDist.expect_eq_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [FinDist.prob_pi]; rfl

/-- The polynomial is continuous, being a finite sum of finite products of
coordinates. -/
theorem continuous_payoff (who : ι) : Continuous (payoff F utility who) :=
  continuous_finsetSum _ fun s _ =>
    (continuous_finsetProd _ fun i _ =>
      (continuous_apply (s i)).comp (continuous_apply i)).mul continuous_const

/-! ## Affine in one player's weights

The factorization below is the whole reason a best response is a convex set: it
exhibits the payoff as a linear functional of the deviator's own weights, with
coefficients that do not mention them. -/

omit [∀ i, Fintype (F.sig.Strategy i)] in
/-- Splitting off the deviator's own factor. -/
theorem prod_update (x : Profile F.sig.weights) (who : ι) (v : F.sig.Strategy who → ℝ)
    (s : Profile F.sig) :
    (∏ i, Profile.update x who v i (s i)) =
      v (s who) * ∏ i ∈ Finset.univ.erase who, x i (s i) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun i => Profile.update x who v i (s i))
    (Finset.mem_univ who)]
  congr 1
  · rw [Profile.update_same]
  · exact Finset.prod_congr rfl fun i hi => by
      rw [Profile.update_of_ne _ _ (Finset.ne_of_mem_erase hi)]

/-- **The payoff is linear in the deviator's own weights**: their weight on a
strategy multiplies a coefficient that does not mention it. -/
theorem payoff_update (x : Profile F.sig.weights) (who : ι) (v : F.sig.Strategy who → ℝ) :
    payoff F utility who (Profile.update x who v) =
      ∑ s : Profile F.sig, v (s who) *
        ((∏ i ∈ Finset.univ.erase who, x i (s i)) * expectedUtility utility who (F.play s)) := by
  show ∑ s : Profile F.sig, _ = _
  exact Finset.sum_congr rfl fun s _ => by rw [prod_update, mul_assoc]

/-- Hence the deviator's payoff, as a function of their own weights, is affine —
which is all the convexity argument uses. -/
theorem payoff_update_mix (x : Profile F.sig.weights) (who : ι)
    (v w : F.sig.Strategy who → ℝ) (a b : ℝ) :
    payoff F utility who (Profile.update x who (a • v + b • w)) =
      a * payoff F utility who (Profile.update x who v) +
        b * payoff F utility who (Profile.update x who w) := by
  simp only [payoff_update, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  show (a * v (s who) + b * w (s who)) * _ = _
  ring

end GameTheory
