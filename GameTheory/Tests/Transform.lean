/-
# Concrete transformation regression tests

These tests exercise the promoted API. The player swap uses
unequal strategy carriers; the strategy flip exercises recommendation-dependent
correlated deviations.
-/

import GameTheory.Core.Transform

noncomputable section

namespace GameTheory.Tests.Transform

open Probability

/-- Outcome relabeling exercises the generic preference pullback, not only the
expected-utility specialization. -/
theorem outcome_pullback_nash
    (F : GameForm Bool) {Outcome' : Type*}
    (relabel : F.sig.Outcome → Outcome')
    (weaklyPrefers : WeakPreference Bool Outcome')
    (profile : Profile F.sig) :
    IsNash (F.mapOutcome relabel) weaklyPrefers profile ↔
      IsNash F (Preference.comapOutcome relabel weaklyPrefers) profile :=
  isNash_mapOutcome_comap F relabel weaklyPrefers profile

abbrev HeterogeneousStrategy : Bool → Type
  | false => Bool
  | true => Fin 3

abbrev heterogeneousSignature : GameSignature Bool where
  Strategy := HeterogeneousStrategy
  Outcome := Unit

abbrev heterogeneousForm : GameForm Bool where
  sig := heterogeneousSignature
  play _ := FinDist.pure ()

def playerSwap : Bool ≃ Bool :=
  Equiv.swap false true

def heterogeneousProfile : Profile heterogeneousSignature
  | false => false
  | true => 0

def heterogeneousMixedProfile :
    Profile (heterogeneousSignature.reindexPlayers playerSwap).mixed :=
  Profile.reindexPlayers playerSwap
    (heterogeneousForm.purify heterogeneousProfile)

/-- Mixed lifting survives an actual swap of unequal strategy carriers. -/
theorem heterogeneous_mixed_lifting :
    (heterogeneousForm.mixed.reindexPlayers playerSwap).play
        heterogeneousMixedProfile =
      (heterogeneousForm.reindexPlayers playerSwap).mixed.play
        heterogeneousMixedProfile :=
  mixed_reindexPlayers_play heterogeneousForm playerSwap
    heterogeneousMixedProfile

/-- Nash transport survives the same heterogeneous player swap. -/
theorem heterogeneous_nash_transport
    (weaklyPrefers : WeakPreference Bool Unit) :
    IsNash (heterogeneousForm.reindexPlayers playerSwap)
        (Preference.reindexPlayers playerSwap weaklyPrefers)
        (Profile.reindexPlayers playerSwap heterogeneousProfile) ↔
      IsNash heterogeneousForm weaklyPrefers heterogeneousProfile :=
  isNash_reindexPlayers heterogeneousForm weaklyPrefers playerSwap
    heterogeneousProfile

abbrev boolSignature : GameSignature Bool where
  Strategy _ := Bool
  Outcome := Unit

abbrev boolForm : GameForm Bool where
  sig := boolSignature
  play _ := FinDist.pure ()

def strategyFlip (_ : Bool) : Bool ≃ Bool :=
  Equiv.swap false true

theorem strategyFlip_false (player : Bool) :
    strategyFlip player false = true := by
  simp [strategyFlip]

/-- CE transport conjugates the nonidentity response space in both directions. -/
theorem flipped_correlated_transport
    (weaklyPrefers : WeakPreference Bool Unit)
    (statusQuo : FinDist (Profile boolSignature)) :
    IsCorrelatedEq (boolForm.relabelStrategies strategyFlip)
        weaklyPrefers
        (statusQuo.map (Profile.relabelStrategies strategyFlip)) ↔
      IsCorrelatedEq boolForm weaklyPrefers statusQuo :=
  isCorrelatedEq_relabelStrategies boolForm weaklyPrefers strategyFlip
    statusQuo

end GameTheory.Tests.Transform
