/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Adaptive.CertificateTargetPerturbation
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.FixedDepthAdaptiveCertificate

/-!
# Approximate target transport through a finite public selector

The fixed-depth splice does not require literal preservation of the parent
target.  If the selected expected child target is within half the requested
error, construct a certificate at that selected target using the other half
of the budget and then retarget it.

This is useful when an analytic or polyhedral construction supplies only an
approximate child lottery at the finite accuracy currently being compiled.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι Child : Type} {G : StochasticGame ι}
  [Fintype ι] [DecidableEq ι]
  [Finite G.State] [∀ who, Finite (G.Act who)]
  [Finite Child]
  {entry : Child → G.State} {target : Child → Payoff ι}
  {selector : DeviationSafePublicCoinSelector G Child}
  {initial : G.State} {fuel : ℕ}

namespace FixedDepthAdaptivePotentialSplice

/-- A deviation-safe fixed-depth selector whose expected child target is
within half the requested tolerance inherits a parent adaptive certificate.

The first half of the budget constructs the selector/child splice at its
own expected target.  The second half pays for moving that target to the
advertised parent payoff. -/
theorem isAdaptivePotentialCertificateAt_of_approximateTarget
    (selection : G.BehaviorProfile)
    (parentTarget : Payoff ι) (error : ℝ) (error_pos : 0 < error)
    (rank_le : selector.process.rank initial ≤ fuel)
    (terminal_entry :
      ∀ state, selector.process.terminal state →
        state = entry (selector.process.observe state))
    (target_close :
      ∀ who,
        |expect (selector.process.value initial)
            (fun child => target child who) -
          parentTarget who| ≤ error / 2)
    (childCertificates :
      ∀ child childError, 0 < childError →
        G.IsAdaptivePotentialCertificateAt
          (entry child) (target child) childError) :
    G.IsAdaptivePotentialCertificateAt
      initial parentTarget error := by
  let selectedTarget : Payoff ι :=
    fun who =>
      expect (selector.process.value initial)
        (fun child => target child who)
  have selectedCertificate :
      G.IsAdaptivePotentialCertificateAt
        initial selectedTarget (error / 2) := by
    apply
      isAdaptivePotentialCertificateAt_of_fixedDepthSelector_allErrors
        (selector := selector) (entry := entry) (target := target)
        selection selectedTarget (error / 2) (by linarith)
        rank_le terminal_entry
    · intro who
      rfl
    · exact childCertificates
  have retargeted :=
    selectedCertificate.retarget
      (perturbedTarget := parentTarget)
      (targetError := error / 2)
      (by linarith)
      (by
        intro who
        exact target_close who)
  rw [show error / 2 + error / 2 = error by ring] at retargeted
  exact retargeted

end FixedDepthAdaptivePotentialSplice

end StochasticGame
end GameTheory
