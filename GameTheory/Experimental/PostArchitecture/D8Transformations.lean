import GameTheory.Core.Transform

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.D8Transformations

/-! Concrete hostile fixtures for the canonical transformation API. -/

open GameTheory
open GameTheory.Math.Probability

namespace Hostile


abbrev HeterogeneousStrategy : Bool → Type
  | false => Bool
  | true => Fin 3

abbrev heterogeneousSignature : GameTheory.GameSignature Bool where
  Strategy := HeterogeneousStrategy
  Outcome := Unit

def heterogeneousForm : GameTheory.GameForm Bool where
  sig := heterogeneousSignature
  play _ := PMF.pure ()

def playerSwap : Bool ≃ Bool :=
  Equiv.swap false true

def heterogeneousProfile : GameTheory.Profile heterogeneousSignature
  | false => false
  | true => 0

def heterogeneousMixedProfile :
    GameTheory.Profile
      (GameSignature.reindexPlayers heterogeneousSignature playerSwap).mixed :=
  Profile.reindexPlayers playerSwap
    (heterogeneousForm.purify heterogeneousProfile)

/-- The mixed lifting theorem survives an actual swap of unequal strategy
carriers. -/
theorem heterogeneous_mixed_lifting :
    (GameForm.reindexPlayers heterogeneousForm.mixed playerSwap).play
        heterogeneousMixedProfile =
      (GameForm.reindexPlayers heterogeneousForm playerSwap).mixed.play
        heterogeneousMixedProfile :=
  mixed_reindexPlayers_play heterogeneousForm playerSwap
    heterogeneousMixedProfile

/-- Nash transport also survives the heterogeneous player swap. -/
theorem heterogeneous_nash_transport
    (weaklyPrefers :
      GameTheory.WeakPreference Bool heterogeneousSignature.Outcome) :
    GameTheory.IsNash
        (GameForm.reindexPlayers heterogeneousForm playerSwap)
        (Preference.reindexPlayers playerSwap weaklyPrefers)
        (Profile.reindexPlayers playerSwap heterogeneousProfile) ↔
      GameTheory.IsNash heterogeneousForm weaklyPrefers
        heterogeneousProfile :=
  isNash_reindexPlayers heterogeneousForm weaklyPrefers playerSwap
    heterogeneousProfile

abbrev boolSignature : GameTheory.GameSignature Bool where
  Strategy _ := Bool
  Outcome := Unit

def boolForm : GameTheory.GameForm Bool where
  sig := boolSignature
  play _ := PMF.pure ()

def strategyFlip (_ : Bool) : Bool ≃ Bool :=
  Equiv.swap false true

/-- The strategy equivalence is genuinely nonidentity at both coordinates. -/
theorem strategyFlip_false (player : Bool) :
    strategyFlip player false = true := by
  simp [strategyFlip]

/-- Correlated-equilibrium transport conjugates a nonidentity response space;
it is not merely a carrier-renaming statement. -/
theorem flipped_correlated_transport
    (weaklyPrefers : GameTheory.WeakPreference Bool Unit)
    (statusQuo : PMF (GameTheory.Profile boolSignature)) :
    GameTheory.IsCorrelatedEq
        (GameForm.relabelStrategies boolForm strategyFlip)
        weaklyPrefers
        (statusQuo.map (Profile.relabelStrategies strategyFlip)) ↔
      GameTheory.IsCorrelatedEq boolForm weaklyPrefers statusQuo :=
  isCorrelatedEq_relabelStrategies boolForm weaklyPrefers strategyFlip
    statusQuo


end Hostile

end GameTheory.Experimental.PostArchitecture.D8Transformations
