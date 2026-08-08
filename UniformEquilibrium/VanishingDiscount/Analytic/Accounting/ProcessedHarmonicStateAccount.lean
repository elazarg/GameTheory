/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.ProcessedJetAccountBoundary
import Math.Probability.HarmonicStateAccount

/-!
# State-potential account carried by a processed harmonic jet

An already-processed lower value jet has an endpoint-harmonic leading
coefficient.  For each player coordinate, evaluating that coefficient along
the realized state path gives a bounded account.  Its exact increment is the
observed successor-versus-endpoint-kernel discrepancy, and its conditional
mean under any adaptive comparison kernel is the corresponding
comparison-versus-endpoint drift.

This closes only the state-potential accounting identity.  The processed-span
membership does not prove that a strategic response charge, stage forcing,
reset cost, or Bellman remainder equals this observed increment.  Such an
identification is a separate theorem-sized hypothesis; the singleton
counterexample in `Math.Probability.HarmonicStateAccount` shows it cannot
follow from harmonicity alone.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace LowerValueJet

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {germ : G.AnalyticBellmanGerm}

/-- The selected coordinate of the leading lower value jet. -/
def endpointCoordinatePotential
    (jet : germ.LowerValueJet) (who : ι) :
    G.State → ℝ :=
  fun state => jet.factor 0 state who

/-- The account obtained by evaluating the selected leading coordinate
along a realized state path. -/
def endpointCoordinateAccount
    (jet : germ.LowerValueJet) (who : ι)
    (path : ℕ → G.State) : ℕ → ℝ :=
  statePotentialAccount (jet.endpointCoordinatePotential who) path

/-- The exact observed charge paid by the endpoint-coordinate account. -/
def endpointCoordinateObservedCharge
    (jet : germ.LowerValueJet) (who : ι)
    (path : ℕ → G.State) : ℕ → ℝ :=
  statePotentialIncrement (jet.endpointCoordinatePotential who) path

/-- The exact additional identity required to charge a named strategic
quantity to the processed harmonic state potential.  Neither harmonicity nor
processed-span membership constructs this equality. -/
def IsEndpointCoordinateDiscrepancyCharge
    (jet : germ.LowerValueJet) (who : ι)
    (path : ℕ → G.State) (charge : ℕ → ℝ) : Prop :=
  ∀ t,
    charge t =
      markovPotentialDiscrepancy
        (G.finkStateKernel germ.endpointFinkPoint)
        (jet.endpointCoordinatePotential who)
        (path t) (path (t + 1))

omit [DecidableEq G.State] in
/-- The endpoint-coordinate observed charge is always realized by its
state-potential account. -/
theorem endpointCoordinateObservedCharge_isRealizedByAccount
    (jet : germ.LowerValueJet) (who : ι)
    (path : ℕ → G.State) :
    IsRealizedByAccount
      (jet.endpointCoordinateObservedCharge who path)
      (jet.endpointCoordinateAccount who path) :=
  statePotentialIncrement_isRealizedByAccount
    (jet.endpointCoordinatePotential who) path

omit [DecidableEq G.State] in
/-- The endpoint-coordinate account is uniformly bounded on the finite state
space. -/
theorem abs_endpointCoordinateAccount_le
    (jet : germ.LowerValueJet) (who : ι)
    (path : ℕ → G.State) (t : ℕ) :
    |jet.endpointCoordinateAccount who path t| ≤
      finiteStatePotentialBound
        (jet.endpointCoordinatePotential who) :=
  abs_statePotentialAccount_le_finiteStatePotentialBound
    (jet.endpointCoordinatePotential who) path t

omit [DecidableEq G.State] in
/-- A processed leading jet is harmonic for the endpoint state kernel in
every player coordinate. -/
theorem endpointCoordinatePotential_harmonic_of_processed
    (jet : germ.LowerValueJet)
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (who : ι) (state : G.State) :
    expect
        (G.finkStateKernel germ.endpointFinkPoint state)
        (jet.endpointCoordinatePotential who) =
      jet.endpointCoordinatePotential who state := by
  have harmonic :
      G.finkContinuationResidualVector
          (jet.factor 0) germ.endpointFinkPoint = 0 :=
    (germ.mem_endpointHarmonicSubmodule_iff (jet.factor 0)).mp
      (span.carrier_le processed)
  have coordinate := congrFun (congrFun harmonic state) who
  simp only [Pi.zero_apply] at coordinate
  unfold finkContinuationResidualVector finkContinuationResidual at coordinate
  rw [G.expect_finkStateKernel_eq]
  change
    G.finkContinuationEU
        (jet.factor 0) germ.endpointFinkPoint state who =
      jet.factor 0 state who
  linarith

omit [DecidableEq G.State] in
/-- The exact leading coupled Bellman transition factor of a processed jet
is zero.  Thus the hierarchy's processed witness does not itself name a
nonzero strategic charge; any such charge must first be identified with the
observed state-potential discrepancy (or controlled as a separate
remainder). -/
theorem coupledTransitionFactor_zero_of_processed
    (jet : germ.LowerValueJet)
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier) :
    jet.coupledTransitionFactor 0 = 0 := by
  apply jet.coupledTransitionFactor_zero_eq_zero_iff.mpr
  exact
    (germ.mem_endpointHarmonicSubmodule_iff (jet.factor 0)).mp
      (span.carrier_le processed)

omit [DecidableEq G.State] in
/-- For a processed jet, the exact observed account charge is the Markov
discrepancy against the endpoint prescribed kernel. -/
theorem endpointMarkovDiscrepancy_eq_observedCharge_of_processed
    (jet : germ.LowerValueJet)
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (who : ι) (path : ℕ → G.State) (t : ℕ) :
    markovPotentialDiscrepancy
        (G.finkStateKernel germ.endpointFinkPoint)
        (jet.endpointCoordinatePotential who)
        (path t) (path (t + 1)) =
      jet.endpointCoordinateObservedCharge who path t := by
  exact
    markovPotentialDiscrepancy_eq_statePotentialIncrement_of_harmonic
      (G.finkStateKernel germ.endpointFinkPoint)
      (jet.endpointCoordinatePotential who)
      (jet.endpointCoordinatePotential_harmonic_of_processed
        span processed who)
      path t

omit [DecidableEq G.State] in
/-- Complete positive accounting statement available from a processed
harmonic jet: along every path, its observed endpoint-kernel discrepancies
are increments of one uniformly bounded account. -/
theorem processedHarmonic_hasBoundedObservedDiscrepancyAccount
    (jet : germ.LowerValueJet)
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (who : ι) (path : ℕ → G.State) :
    (∀ t,
        |jet.endpointCoordinateAccount who path t| ≤
          finiteStatePotentialBound
            (jet.endpointCoordinatePotential who)) ∧
      IsRealizedByAccount
        (fun t =>
          markovPotentialDiscrepancy
            (G.finkStateKernel germ.endpointFinkPoint)
            (jet.endpointCoordinatePotential who)
            (path t) (path (t + 1)))
        (jet.endpointCoordinateAccount who path) := by
  exact
    harmonicMarkovDiscrepancy_isRealizedByBoundedAccount
      (G.finkStateKernel germ.endpointFinkPoint)
      (jet.endpointCoordinatePotential who)
      (jet.endpointCoordinatePotential_harmonic_of_processed
        span processed who)
      path

omit [DecidableEq G.State] in
/-- A strategic charge is paid by the processed harmonic account once the
missing same-coefficient discrepancy identity is supplied explicitly. -/
theorem processedHarmonic_hasBoundedAccount_of_discrepancyCharge
    (jet : germ.LowerValueJet)
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier)
    (who : ι) (path : ℕ → G.State) (charge : ℕ → ℝ)
    (identified :
      jet.IsEndpointCoordinateDiscrepancyCharge who path charge) :
    (∀ t,
        |jet.endpointCoordinateAccount who path t| ≤
          finiteStatePotentialBound
            (jet.endpointCoordinatePotential who)) ∧
      IsRealizedByAccount charge
        (jet.endpointCoordinateAccount who path) := by
  rcases
      jet.processedHarmonic_hasBoundedObservedDiscrepancyAccount
        span processed who path with
    ⟨bounded, realized⟩
  refine ⟨bounded, ?_⟩
  intro t
  rw [identified t]
  exact realized t

end LowerValueJet
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
