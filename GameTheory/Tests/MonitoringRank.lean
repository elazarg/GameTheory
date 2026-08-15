/-
# Monitoring-rank witnesses

Two players have Boolean stage actions.  Perfect public action observation
separates the two unilateral deviations at the all-false profile, whereas a
constant public signal cannot identify even one player's deviation.  The
positive fixture also consumes the bridge from a rank row to the generated
one-signal prefix law.
-/

import GameTheory.Repeated.MonitoringRank

noncomputable section

namespace GameTheory.Tests.MonitoringRank

open GameTheory GameTheory.Math.Probability

abbrev Player := Bool

@[reducible]
def signature : GameSignature Player where
  Strategy _ := Bool
  Outcome := Unit

@[reducible]
def form : GameForm Player where
  sig := signature
  play _ := FinDist.pure ()

@[reducible]
def game : UtilityGame Player where
  form := form
  utility _ _ := 0

def base : Profile signature := fun _ => false

def firstChanged : Profile signature :=
  Profile.update base false true

def secondChanged : Profile signature :=
  Profile.update base true true

theorem firstChanged_ne_base : firstChanged ≠ base := by
  intro hequal
  have := congrFun hequal false
  simp [firstChanged, base] at this

theorem secondChanged_ne_base : secondChanged ≠ base := by
  intro hequal
  have := congrFun hequal true
  simp [secondChanged, base] at this

theorem firstChanged_ne_secondChanged : firstChanged ≠ secondChanged := by
  intro hequal
  have := congrFun hequal false
  simp [firstChanged, secondChanged, base] at this

/-- Perfect public action observation records the entire chosen stage
profile. -/
@[reducible]
def perfectMonitoring : game.PublicMonitoring where
  Signal := Profile signature
  signalLaw profile := FinDist.pure profile

/-- An uninformative monitor emits the same public signal after every stage
profile. -/
@[reducible]
def constantMonitoring : game.PublicMonitoring where
  Signal := Unit
  signalLaw _ := FinDist.pure ()

def trueDeviation (who : Player) :
    UtilityGame.PublicMonitoring.NontrivialDeviation
      (G := game) base who :=
  ⟨true, by simp [base]⟩

theorem nontrivialDeviation_unique (who : Player)
    (deviation : UtilityGame.PublicMonitoring.NontrivialDeviation
      (G := game) base who) :
    deviation = trueDeviation who := by
  apply Subtype.ext
  cases haction : deviation.1 with
  | false => exact False.elim (deviation.2 (by simp [base, haction]))
  | true => rfl

/-- Perfect profile observation has pairwise full rank at the base profile:
the two players' deviations move probability mass to different public
signals. -/
theorem perfect_pairwiseFullRank :
    perfectMonitoring.PairwiseFullRank base false true := by
  rw [UtilityGame.PublicMonitoring.PairwiseFullRank,
    Fintype.linearIndependent_iff]
  intro coefficient hzero deviation
  letI : Unique
      (UtilityGame.PublicMonitoring.NontrivialDeviation
        (G := game) base false) := {
    default := trueDeviation false
    uniq := nontrivialDeviation_unique false
  }
  letI : Unique
      (UtilityGame.PublicMonitoring.NontrivialDeviation
        (G := game) base true) := {
    default := trueDeviation true
    uniq := nontrivialDeviation_unique true
  }
  have hfirst := congrFun hzero firstChanged
  have hsecond := congrFun hzero secondChanged
  simp only [Fintype.sum_sum_type, Fintype.sum_unique, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] at hfirst hsecond
  have hdefaultFalse :
      (default : UtilityGame.PublicMonitoring.NontrivialDeviation
        (G := game) base false) = trueDeviation false :=
    nontrivialDeviation_unique false default
  have hdefaultTrue :
      (default : UtilityGame.PublicMonitoring.NontrivialDeviation
        (G := game) base true) = trueDeviation true :=
    nontrivialDeviation_unique true default
  rw [hdefaultFalse, hdefaultTrue] at hfirst hsecond
  have hfirstCoefficient :
      coefficient (Sum.inl (trueDeviation false)) = 0 := by
    have hfirst' :
        coefficient (Sum.inl (trueDeviation false)) *
            ((FinDist.pure firstChanged).prob firstChanged -
              (FinDist.pure base).prob firstChanged) +
          coefficient (Sum.inr (trueDeviation true)) *
            ((FinDist.pure secondChanged).prob firstChanged -
              (FinDist.pure base).prob firstChanged) = 0 := hfirst
    rw [FinDist.prob_pure_self,
      FinDist.prob_pure_of_ne firstChanged_ne_base,
      FinDist.prob_pure_of_ne firstChanged_ne_secondChanged] at hfirst'
    norm_num at hfirst'
    exact hfirst'
  have hsecondCoefficient :
      coefficient (Sum.inr (trueDeviation true)) = 0 := by
    have hsecond' :
        coefficient (Sum.inl (trueDeviation false)) *
            ((FinDist.pure firstChanged).prob secondChanged -
              (FinDist.pure base).prob secondChanged) +
          coefficient (Sum.inr (trueDeviation true)) *
            ((FinDist.pure secondChanged).prob secondChanged -
              (FinDist.pure base).prob secondChanged) = 0 := hsecond
    rw [FinDist.prob_pure_of_ne firstChanged_ne_secondChanged.symm,
      FinDist.prob_pure_of_ne secondChanged_ne_base,
      FinDist.prob_pure_self] at hsecond'
    norm_num at hsecond'
    exact hsecond'
  cases deviation with
  | inl deviation =>
      simpa [nontrivialDeviation_unique false deviation] using
        hfirstCoefficient
  | inr deviation =>
      simpa [nontrivialDeviation_unique true deviation] using
        hsecondCoefficient
/-
The explicit probability calculations above deliberately expose which public
signal identifies which deviator.  A proof by cardinality alone would not
exercise the monitoring kernel.
-/

/-- The numerical API reads the same witness as rank two, one independent
deviation direction for each player. -/
theorem perfect_pairwiseDeviationRank_eq_two :
    perfectMonitoring.pairwiseDeviationRank base false true = 2 := by
  letI : Unique
      (UtilityGame.PublicMonitoring.NontrivialDeviation
        (G := game) base false) := {
    default := trueDeviation false
    uniq := nontrivialDeviation_unique false
  }
  letI : Unique
      (UtilityGame.PublicMonitoring.NontrivialDeviation
        (G := game) base true) := {
    default := trueDeviation true
    uniq := nontrivialDeviation_unique true
  }
  calc
    perfectMonitoring.pairwiseDeviationRank base false true =
        Fintype.card
            (UtilityGame.PublicMonitoring.NontrivialDeviation
              (G := game) base false) +
          Fintype.card
            (UtilityGame.PublicMonitoring.NontrivialDeviation
              (G := game) base true) :=
      (UtilityGame.PublicMonitoring.pairwiseFullRank_iff_pairwiseDeviationRank_eq_card
          perfectMonitoring base false true).1 perfect_pairwiseFullRank
    _ = 2 := by simp

/-- With a constant signal, the unique nontrivial deviation has the zero
signal-effect row, so individual full rank fails. -/
theorem constant_not_individualFullRank :
    ¬ constantMonitoring.IndividualFullRank base false := by
  intro hfull
  exact hfull.signalLaw_update_ne (trueDeviation false) rfl

def stationaryBase : perfectMonitoring.MonitoredProfile :=
  perfectMonitoring.stationaryMonitoredProfile base

/-- The abstract deviation row is observed in the repeated semantics as an
actual one-signal-prefix probability change. -/
theorem firstDeviation_prefixEffect :
    perfectMonitoring.deviationSignalVector base false true firstChanged =
      (perfectMonitoring.signalHistoryLaw
          (Profile.update
            (sig := perfectMonitoring.monitoredSignature)
            stationaryBase false
            (perfectMonitoring.oneShotDeviation stationaryBase false true))
          1).prob
          (perfectMonitoring.singletonHistory firstChanged) -
        (perfectMonitoring.signalHistoryLaw stationaryBase 1).prob
          (perfectMonitoring.singletonHistory firstChanged) := by
  simpa [stationaryBase,
    UtilityGame.PublicMonitoring.stationaryMonitoredProfile] using
    perfectMonitoring.deviationSignalVector_eq_oneShotHistoryProb_sub
      stationaryBase false true firstChanged

/-- In the concrete perfect-monitoring fixture that prefix probability rises
from zero to one. -/
theorem firstDeviation_prefixEffect_eq_one :
    (perfectMonitoring.signalHistoryLaw
        (Profile.update
          (sig := perfectMonitoring.monitoredSignature)
          stationaryBase false
          (perfectMonitoring.oneShotDeviation stationaryBase false true))
        1).prob
        (perfectMonitoring.singletonHistory firstChanged) -
      (perfectMonitoring.signalHistoryLaw stationaryBase 1).prob
        (perfectMonitoring.singletonHistory firstChanged) = 1 := by
  rw [← firstDeviation_prefixEffect]
  show (FinDist.pure firstChanged).prob firstChanged -
      (FinDist.pure base).prob firstChanged = 1
  rw [FinDist.prob_pure_self,
    FinDist.prob_pure_of_ne firstChanged_ne_base]
  norm_num

end GameTheory.Tests.MonitoringRank
