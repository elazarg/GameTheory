/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AdaptiveSystemEnforcementLedger
import GameTheory.Concepts.Stochastic.PublicFixedDepthAdaptiveCertificate

/-!
# Randomized recurrent-child composition

This file records the equilibrium-level consequence of the fixed-depth
public-coin splice.

A deviation-safe selector has a terminal-child law which is independent of
the complete behavior profile used during selection.  If that law transports
the whole child payoff vector to the parent target, every terminal selector
state is the advertised child entry state, and every child target has an
adaptive-potential equilibrium certificate, then the parent target has one
as well.  Hence it is a uniform-equilibrium payoff.

The conditioning interface used for a deviation spanning both phases is made
explicit below: after conditioning on a fixed-depth public base, the root
deviation becomes `afterHistoryStrategy deviation base`, a legal behavior
strategy in the selected child game.  No independent pre/post deviation
split is assumed.

The only selection loss in the underlying constructor is the finite charge

`fuel * (payoffBound + targetBound)`.

At requested error `δ`, an Archimedean accounting horizon makes its Cesàro
contribution at most `δ / 2`; child certificates are invoked at error
`δ / 2`.  Thus the bounded prefix causes no asymptotic loss.

There is one important scope restriction.  `DeviationSafePublicCoinSelector`
identifies the game transition with its stopped kernel at every state.  Its
terminal states therefore self-loop under every joint action.  The theorems
below close the whole-vector target seam for that globally stopped interface,
but do not construct the variable-stopping-time splice needed to enter a
nonabsorbing recurrent child immediately when a merely local
`FinitePublicCoinStoppingRegion` terminates.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι Child : Type} {G : StochasticGame ι}

namespace FixedDepthAdaptivePotentialSplice

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ who, Finite (G.Act who)] [Finite Child]
  {entry : Child → G.State} {target : Child → Payoff ι}
  {childError : ℝ}
  {selector : DeviationSafePublicCoinSelector G Child}
  {selection : G.BehaviorProfile} {initial : G.State} {fuel : ℕ}

omit [Finite Child] in
/-- Exact suffix-conditioning interface for a deviation which was chosen
before the public selector ran.

Conditioning on `base` does not require a fresh existential deviation:
restriction of the original full-history strategy is already a behavior
strategy of the child game. -/
theorem afterHistoryProfile_update_eq_rebasedDeviation
    [Fintype Child]
    {family :
      G.FiniteChildAdaptivePotentialFamily entry target childError}
    (splice :
      G.FixedDepthAdaptivePotentialSplice selector family
        selection initial fuel)
    (base : G.Hist fuel) (who : ι)
    (deviation : G.BehaviorStrategy who) :
    G.afterHistoryProfile
        (Function.update splice.profile who deviation) base =
      Function.update
        (G.canonicalTerminalChildProfile fuel selection
          splice.childProfile base)
        who (G.afterHistoryStrategy deviation base) := by
  exact
    G.afterHistoryProfile_update_terminalChildDispatcher_canonical
      fuel selection splice.childProfile base who deviation

/-- Exact whole-vector transport through a finite deviation-safe public
selector preserves adaptive-potential equilibrium certificates.

The composed profile plays `selection` for `fuel` stages and then uses the
canonical public terminal-child dispatcher. -/
theorem isAdaptivePotentialEquilibriumCertificate_of_fixedDepthSelector
    (selection : G.BehaviorProfile)
    (parentTarget : Payoff ι)
    (hfuel : selector.process.rank initial ≤ fuel)
    (hentry : ∀ state, selector.process.terminal state →
      state = entry (selector.process.observe state))
    (hexact : ∀ who,
      expect (selector.process.value initial)
        (fun child => target child who) = parentTarget who)
    (childCertificates : ∀ child,
      G.IsAdaptivePotentialEquilibriumCertificate
        (entry child) (target child)) :
    G.IsAdaptivePotentialEquilibriumCertificate
      initial parentTarget := by
  letI : Fintype Child := Fintype.ofFinite Child
  intro error herror
  apply isAdaptivePotentialCertificateAt_of_fixedDepthSelector_allErrors
    (selector := selector) (entry := entry) (target := target)
    selection parentTarget error herror hfuel hentry hexact
  intro child childError hchildError
  exact childCertificates child childError hchildError

/-- Public-phase form of the same composition at any requested positive
accuracy.

The exact-stage-gap compiler turns the composed adaptive system at error
`error / 2` into a public response ledger, and hence a public-phase
punishment system, at error `error`. -/
theorem isPublicPhasePunishmentSystemAt_of_fixedDepthSelector
    (selection : G.BehaviorProfile)
    (parentTarget : Payoff ι) (error : ℝ) (herror : 0 < error)
    (hfuel : selector.process.rank initial ≤ fuel)
    (hentry : ∀ state, selector.process.terminal state →
      state = entry (selector.process.observe state))
    (hexact : ∀ who,
      expect (selector.process.value initial)
        (fun child => target child who) = parentTarget who)
    (childCertificates : ∀ child,
      G.IsAdaptivePotentialEquilibriumCertificate
        (entry child) (target child)) :
    G.IsPublicPhasePunishmentSystemAt initial parentTarget error := by
  letI : Fintype Child := Fintype.ofFinite Child
  have certificate :
      G.IsAdaptivePotentialCertificateAt
        initial parentTarget (error / 2) := by
    exact
      isAdaptivePotentialCertificateAt_of_fixedDepthSelector_allErrors
        (selector := selector) (entry := entry) (target := target)
        selection parentTarget (error / 2) (by linarith)
        hfuel hentry hexact
        (fun child childError hchildError =>
          childCertificates child childError hchildError)
  obtain ⟨profile, ⟨system⟩⟩ :=
    (G.isAdaptivePotentialCertificateAt_iff_exists_system
      initial parentTarget (error / 2)).mp certificate
  have publicSystem :=
    (system.toExactStageGapPublicResponseEnforcementLedgerAt
      (by linarith)).toIsPublicPhasePunishmentSystemAt
  simpa only [show 2 * (error / 2) = error by ring] using publicSystem

/-- Uniform-equilibrium payoff composition for a randomized recurrent child.

This is the semantic capstone: exact terminal-law transport and public suffix
rebasing leave only a bounded selection prefix, whose Cesàro effect vanishes.
-/
theorem isUniformEquilibriumPayoff_of_fixedDepthSelector
    (selection : G.BehaviorProfile)
    (parentTarget : Payoff ι)
    (hfuel : selector.process.rank initial ≤ fuel)
    (hentry : ∀ state, selector.process.terminal state →
      state = entry (selector.process.observe state))
    (hexact : ∀ who,
      expect (selector.process.value initial)
        (fun child => target child who) = parentTarget who)
    (childCertificates : ∀ child,
      G.IsAdaptivePotentialEquilibriumCertificate
        (entry child) (target child)) :
    G.IsUniformEquilibriumPayoff initial parentTarget := by
  letI : Fintype Child := Fintype.ofFinite Child
  apply
    G.isUniformEquilibriumPayoff_of_isAdaptivePotentialEquilibriumCertificate
  exact isAdaptivePotentialEquilibriumCertificate_of_fixedDepthSelector
    (selector := selector) (entry := entry) (target := target)
    selection parentTarget hfuel hentry hexact childCertificates

end FixedDepthAdaptivePotentialSplice

end StochasticGame
end GameTheory
