/-
# Rank conditions for finite public monitoring

This module measures how unilateral changes in a prescribed stage profile
change the next public-signal law.  The rows are probability differences, so
standard individual and pairwise full-rank conditions are ordinary linear
independence statements.

The rank condition is intentionally one-period.  Its connection to repeated
play is explicit: `deviationSignalVector_eq_oneShotHistoryProb_sub` identifies
each row with the change in the generated one-signal prefix law caused by the
canonical monitored one-shot deviation.  No infinite signal-path law is used.
-/

import GameTheory.Repeated.MonitoringContinuation
import Mathlib.LinearAlgebra.Matrix.Rank

noncomputable section

open scoped BigOperators

namespace GameTheory

open Probability

universe uι us uo uy

variable {ι : Type uι}

namespace UtilityGame.PublicMonitoring

variable {G : UtilityGame.{uι, us, uo} ι}

/-- A stage action for one player distinct from the prescribed action. -/
abbrev NontrivialDeviation (profile : Profile G.form.sig) (who : ι) :=
  {action : G.form.sig.Strategy who // action ≠ profile who}

/-- Change in each public-signal probability after one unilateral stage
deviation. -/
def deviationSignalVector (M : G.PublicMonitoring) [DecidableEq ι]
    (profile : Profile G.form.sig) (who : ι)
    (action : G.form.sig.Strategy who) : M.Signal → ℝ :=
  fun signal =>
    (M.signalLaw (Profile.update profile who action)).prob signal -
      (M.signalLaw profile).prob signal

/-- Matrix whose rows are the signal-law changes caused by one player's
nontrivial stage deviations. -/
def deviationSignalMatrix (M : G.PublicMonitoring) [DecidableEq ι]
    (profile : Profile G.form.sig) (who : ι) :
    Matrix (NontrivialDeviation profile who) M.Signal ℝ :=
  fun deviation => M.deviationSignalVector profile who deviation.1

/-- One player's nontrivial deviations have linearly independent public-signal
effects at the prescribed stage profile. -/
def IndividualFullRank (M : G.PublicMonitoring) [DecidableEq ι]
    (profile : Profile G.form.sig) (who : ι) : Prop :=
  LinearIndependent ℝ (M.deviationSignalMatrix profile who)

/-- Combined signal-effect family for deviations by either of two players. -/
def pairwiseDeviationSignalFamily (M : G.PublicMonitoring) [DecidableEq ι]
    (profile : Profile G.form.sig) (first second : ι) :
    Matrix
      (NontrivialDeviation profile first ⊕
        NontrivialDeviation profile second)
      M.Signal ℝ :=
  Sum.elim (M.deviationSignalMatrix profile first)
    (M.deviationSignalMatrix profile second)

/-- Deviations by two players have jointly linearly independent public-signal
effects.  The intended use is for distinct players. -/
def PairwiseFullRank (M : G.PublicMonitoring) [DecidableEq ι]
    (profile : Profile G.form.sig) (first second : ι) : Prop :=
  LinearIndependent ℝ
    (M.pairwiseDeviationSignalFamily profile first second)

/-- Numerical rank of one player's deviation-signal matrix. -/
noncomputable def individualDeviationRank (M : G.PublicMonitoring)
    [DecidableEq ι] [Fintype M.Signal]
    (profile : Profile G.form.sig) (who : ι) : ℕ :=
  (M.deviationSignalMatrix profile who).rank

/-- Numerical rank of the combined deviation-signal matrix for two players. -/
noncomputable def pairwiseDeviationRank (M : G.PublicMonitoring)
    [DecidableEq ι] [Fintype M.Signal]
    (profile : Profile G.form.sig) (first second : ι) : ℕ :=
  (M.pairwiseDeviationSignalFamily profile first second).rank

/-- On a finite deviation family, individual full rank is exactly maximal row
rank. -/
theorem individualFullRank_iff_individualDeviationRank_eq_card
    (M : G.PublicMonitoring) [DecidableEq ι] [Fintype M.Signal]
    (profile : Profile G.form.sig) (who : ι)
    [Fintype (NontrivialDeviation profile who)] :
    M.IndividualFullRank profile who ↔
      M.individualDeviationRank profile who =
        Fintype.card (NontrivialDeviation profile who) := by
  let matrix : Matrix (NontrivialDeviation profile who) M.Signal ℝ :=
    M.deviationSignalMatrix profile who
  show LinearIndependent ℝ matrix ↔ matrix.rank = _
  constructor
  · exact LinearIndependent.rank_matrix
  · intro hrank
    rw [linearIndependent_iff_card_eq_finrank_span]
    show Fintype.card (NontrivialDeviation profile who) =
      Module.finrank ℝ
        (Submodule.span ℝ (Set.range matrix.row))
    rw [← Matrix.rank_eq_finrank_span_row]
    exact hrank.symm

/-- On finite deviation families, pairwise full rank is exactly maximal
combined row rank. -/
theorem pairwiseFullRank_iff_pairwiseDeviationRank_eq_card
    (M : G.PublicMonitoring) [DecidableEq ι] [Fintype M.Signal]
    (profile : Profile G.form.sig) (first second : ι)
    [Fintype (NontrivialDeviation profile first)]
    [Fintype (NontrivialDeviation profile second)] :
    M.PairwiseFullRank profile first second ↔
      M.pairwiseDeviationRank profile first second =
        Fintype.card (NontrivialDeviation profile first) +
          Fintype.card (NontrivialDeviation profile second) := by
  let matrix : Matrix
      (NontrivialDeviation profile first ⊕
        NontrivialDeviation profile second) M.Signal ℝ :=
    M.pairwiseDeviationSignalFamily profile first second
  show LinearIndependent ℝ matrix ↔ matrix.rank = _
  constructor
  · intro hindependent
    dsimp [matrix] at hindependent ⊢
    simpa only [pairwiseDeviationSignalFamily, Fintype.card_sum] using
      hindependent.rank_matrix
  · intro hrank
    rw [linearIndependent_iff_card_eq_finrank_span]
    show Fintype.card
        (NontrivialDeviation profile first ⊕
          NontrivialDeviation profile second) =
      Module.finrank ℝ
        (Submodule.span ℝ (Set.range matrix.row))
    rw [← Matrix.rank_eq_finrank_span_row, Fintype.card_sum]
    exact hrank.symm

/-- Every deviation row sums to zero because it is the difference of two
probability laws. -/
theorem sum_deviationSignalVector_eq_zero
    (M : G.PublicMonitoring) [DecidableEq ι] [Fintype M.Signal]
    (profile : Profile G.form.sig) (who : ι)
    (action : G.form.sig.Strategy who) :
    ∑ signal, M.deviationSignalVector profile who action signal = 0 := by
  simp only [deviationSignalVector, Finset.sum_sub_distrib,
    FinDist.sum_prob, sub_self]

/-- Individual full rank forces every nontrivial deviation to change the
public signal law. -/
theorem IndividualFullRank.signalLaw_update_ne
    {M : G.PublicMonitoring} [DecidableEq ι]
    {profile : Profile G.form.sig} {who : ι}
    (hfull : M.IndividualFullRank profile who)
    (deviation : NontrivialDeviation profile who) :
    M.signalLaw (Profile.update profile who deviation.1) ≠
      M.signalLaw profile := by
  intro hequal
  apply hfull.ne_zero deviation
  funext signal
  simp only [deviationSignalMatrix, deviationSignalVector]
  rw [hequal]
  exact sub_self _

/-- Under individual full rank, distinct nontrivial deviations induce
distinct public signal laws. -/
theorem IndividualFullRank.signalLaw_update_injective
    {M : G.PublicMonitoring} [DecidableEq ι]
    {profile : Profile G.form.sig} {who : ι}
    (hfull : M.IndividualFullRank profile who) :
    Function.Injective fun deviation : NontrivialDeviation profile who =>
      M.signalLaw (Profile.update profile who deviation.1) := by
  intro first second hequal
  apply hfull.injective
  funext signal
  simp only [deviationSignalMatrix, deviationSignalVector]
  rw [congrArg (fun law => law.prob signal) hequal]

/-- The length-one history whose only public signal is `signal`. -/
def singletonHistory (M : G.PublicMonitoring) (signal : M.Signal) :
    M.SignalHistory 1 :=
  fun _ => signal

/-- The probability of a length-one history is exactly the probability of its
only signal under the current stage profile. -/
theorem prob_signalHistoryLaw_one
    (M : G.PublicMonitoring) [DecidableEq M.Signal]
    (profile : M.MonitoredProfile) (signal : M.Signal) :
    (M.signalHistoryLaw profile 1).prob (M.singletonHistory signal) =
      (M.signalLaw
        (fun i => profile i 0 (fun index => index.elim0))).prob signal := by
  rw [M.signalHistoryLaw_succ, M.signalHistoryLaw_zero,
    FinDist.pure_bind]
  let empty : M.SignalHistory 0 := fun index => index.elim0
  let append : M.Signal → M.SignalHistory 1 := fun next => Fin.snoc empty next
  have hinjective : Function.Injective append := by
    intro first second hequal
    exact congrFun hequal 0
  have hprob := FinDist.prob_map_of_injective append hinjective
    (M.signalLaw fun i => profile i 0 empty) signal
  have hsingleton : M.singletonHistory signal = append signal := by
    funext index
    fin_cases index
    rfl
  rw [hsingleton]
  simpa [empty, append] using hprob

/-- A deviation-signal row is the exact change in the generated one-signal
prefix law caused by the canonical monitored one-shot deviation. -/
theorem deviationSignalVector_eq_oneShotHistoryProb_sub
    (M : G.PublicMonitoring) [DecidableEq ι] [DecidableEq M.Signal]
    (profile : M.MonitoredProfile) (who : ι)
    (action : G.form.sig.Strategy who) (signal : M.Signal) :
    M.deviationSignalVector
        (fun i => profile i 0 (fun index => index.elim0)) who action signal =
      (M.signalHistoryLaw
          (Profile.update (sig := M.monitoredSignature) profile who
            (M.oneShotDeviation profile who action)) 1).prob
            (M.singletonHistory signal) -
        (M.signalHistoryLaw profile 1).prob
          (M.singletonHistory signal) := by
  rw [M.prob_signalHistoryLaw_one, M.prob_signalHistoryLaw_one,
    M.currentProfile_update_oneShotDeviation]
  rfl

end UtilityGame.PublicMonitoring

end GameTheory
