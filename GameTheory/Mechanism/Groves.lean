/-
# Groves mechanisms

The mechanism data is capability-free. Finite social-welfare aggregation and
report-independence certificates are required only by the truthfulness
theorems. For every true-type profile, the mechanism induces one deterministic
`UtilityGame`; ex-post equilibrium is ordinary Nash in that game.

Primary references: E. H. Clarke, “Multipart Pricing of Public Goods,”
*Public Choice* 11 (1971); T. Groves, “Incentives in Teams,” *Econometrica* 41
(1973).
-/

import GameTheory.Mechanism.Auction
import GameTheory.Mechanism.QuasiLinear

noncomputable section

open scoped BigOperators

namespace GameTheory.Mechanism

/-- Data for a Groves mechanism: dependent report types, outcomes, valuations,
an allocation rule, and report-indexed Groves offsets.  Efficiency and
own-report independence are theorem-local certificates because they are the
operations that require finite enumeration and profile updates. -/
structure GrovesSetup (ι : Type) where
  /-- Type and report space of each player. -/
  Θ : ι → Type
  /-- Allocation outcome. -/
  Outcome : Type
  /-- Value of an outcome at a player's reported type. -/
  val : (i : ι) → Θ i → Outcome → ℝ
  /-- Outcome selected from a report profile. -/
  alloc : (∀ i, Θ i) → Outcome
  /-- The Groves offset for each player. -/
  h : (i : ι) → (∀ j, Θ j) → ℝ

namespace GrovesSetup

variable {ι : Type} (V : GrovesSetup ι)

/-- The canonical game signature whose strategies are Groves type reports and
whose retained outcome is the complete report profile. -/
abbrev reportSignature : GameSignature ι where
  Strategy := V.Θ
  Outcome := ∀ i, V.Θ i

/-- A dependent profile of reports for a Groves setup. -/
abbrev ReportProfile := Profile V.reportSignature

/-- Reportwise allocative efficiency: at every report profile, the selected
outcome maximizes the total valuation induced by those reports. -/
def IsEfficient [Fintype ι] : Prop :=
  ∀ (report : V.ReportProfile) (outcome : V.Outcome),
    ∑ i, V.val i (report i) outcome ≤
      ∑ i, V.val i (report i) (V.alloc report)

/-- Groves payment: the report-independent offset less other players' reported welfare. -/
def grovesPayment [Fintype ι] [DecidableEq ι]
    (report : V.ReportProfile) (who : ι) : ℝ :=
  V.h who report -
    ∑ other ∈ Finset.univ.erase who,
      V.val other (report other) (V.alloc report)

/-- True quasilinear utility at a report profile. -/
def trueUtility [Fintype ι] [DecidableEq ι] (who : ι) (trueType : V.Θ who)
    (report : V.ReportProfile) : ℝ :=
  V.val who trueType (V.alloc report) - V.grovesPayment report who

/-- True utility is total reported welfare with the true own coordinate, less
the Groves offset. -/
theorem trueUtility_eq [Fintype ι] [DecidableEq ι] (who : ι) (trueType : V.Θ who)
    (report : V.ReportProfile) :
    V.trueUtility who trueType report =
      V.val who trueType (V.alloc report) +
        ∑ other ∈ Finset.univ.erase who,
          V.val other (report other) (V.alloc report) -
        V.h who report := by
  simp only [trueUtility, grovesPayment]
  ring

/-- Truthful reporting weakly dominates any alternative against fixed opposing
reports.  The two premises are exactly the efficient-allocation and
own-report-independent-offset certificates used by the proof. -/
theorem groves_truthful [Fintype ι] [DecidableEq ι]
    (alloc_efficient : V.IsEfficient)
    (h_independent : ∀ (who : ι) (report : V.ReportProfile) (replacement : V.Θ who),
      V.h who (Profile.update report who replacement) = V.h who report)
    (report : V.ReportProfile) (who : ι) (trueType alternative : V.Θ who) :
    V.trueUtility who trueType (Profile.update report who alternative) ≤
      V.trueUtility who trueType (Profile.update report who trueType) := by
  let truthfulReport := Profile.update report who trueType
  let deviatingReport := Profile.update report who alternative
  rw [V.trueUtility_eq who trueType truthfulReport,
    V.trueUtility_eq who trueType deviatingReport]
  have hh : V.h who truthfulReport = V.h who deviatingReport := by
    rw [show V.h who truthfulReport = V.h who report from
      h_independent who report trueType]
    exact (h_independent who report alternative).symm
  have hothers :
      ∑ other ∈ Finset.univ.erase who,
          V.val other (deviatingReport other) (V.alloc deviatingReport) =
        ∑ other ∈ Finset.univ.erase who,
          V.val other (truthfulReport other) (V.alloc deviatingReport) := by
    apply Finset.sum_congr rfl
    intro other hother
    have hne : other ≠ who := (Finset.mem_erase.mp hother).1
    simp only [truthfulReport, deviatingReport, Profile.update_of_ne _ _ hne]
  rw [hothers, ← hh]
  have hefficient := alloc_efficient truthfulReport (V.alloc deviatingReport)
  have hsplit (outcome : V.Outcome) :
      ∑ i, V.val i (truthfulReport i) outcome =
        V.val who trueType outcome +
          ∑ other ∈ Finset.univ.erase who,
            V.val other (truthfulReport other) outcome := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ who)]
    simp only [truthfulReport, Profile.update_same]
  rw [hsplit, hsplit] at hefficient
  linarith

/-- The deterministic utility game at a fixed profile of true types. Reports
are strategies and realized outcomes retain the report profile. -/
def toUtilityGame [Fintype ι] [DecidableEq ι] (trueTypes : V.ReportProfile) : UtilityGame ι :=
  Auction.auctionGame V.alloc V.grovesPayment
    (fun i outcome => V.val i (trueTypes i) outcome)

/-- Truthful reporting as a type-contingent dependent strategy. -/
def truthfulStrategy : ∀ i, V.Θ i → V.Θ i := fun _ type => type

/-- At a true-type profile, the truthful direct report is that same profile. -/
@[simp]
theorem toUtilityGame_play_truthful [Fintype ι] [DecidableEq ι]
    (trueTypes : V.ReportProfile) :
    (V.toUtilityGame trueTypes).form.play
        (fun i => V.truthfulStrategy i (trueTypes i)) =
      GameTheory.Math.Probability.FinDist.pure trueTypes := by
  rfl

/-- Truthful reporting is an ex-post equilibrium: for every true-type profile,
the truthful report profile is ordinary expected-utility Nash. -/
theorem truthfulStrategy_isExPostNash [Fintype ι] [DecidableEq ι]
    (alloc_efficient : V.IsEfficient)
    (h_independent : ∀ (who : ι) (report : V.ReportProfile) (replacement : V.Θ who),
      V.h who (Profile.update report who replacement) = V.h who report) :
    ∀ trueTypes : V.ReportProfile,
      IsNash (V.toUtilityGame trueTypes).form
        (euPreference (V.toUtilityGame trueTypes).utility) trueTypes := by
  intro trueTypes
  rw [isNash_iff]
  intro who alternative
  rw [euPreference_apply]
  simp only [toUtilityGame, Auction.auctionGame_expectedUtility]
  have htruth := V.groves_truthful alloc_efficient h_independent trueTypes who
    (trueTypes who) alternative
  rw [Profile.update_eq_self] at htruth
  unfold trueUtility at htruth
  exact htruth

/-- Forget the Groves-specific offset presentation and expose the shared
quasilinear direct-mechanism data. -/
def toQuasiLinearMechanism [Fintype ι] [DecidableEq ι] :
    Mechanism.QuasiLinearMechanism ι V.Outcome where
  Ty := V.Θ
  value := V.val
  choose := V.alloc
  payment := V.grovesPayment

@[simp]
theorem toQuasiLinearMechanism_trueUtility [Fintype ι] [DecidableEq ι]
    (report : V.ReportProfile) (who : ι) (trueType : V.Θ who) :
    V.toQuasiLinearMechanism.trueUtility report who trueType =
      V.trueUtility who trueType report :=
  rfl

/-- Efficient Groves allocation with own-report-independent offsets is DSIC
through the canonical quasilinear direct-mechanism predicate. -/
theorem toQuasiLinearMechanism_isDSIC [Fintype ι] [DecidableEq ι]
    (alloc_efficient : V.IsEfficient)
    (h_independent : ∀ (who : ι) (report : V.ReportProfile)
      (replacement : V.Θ who),
      V.h who (Profile.update report who replacement) = V.h who report) :
    V.toQuasiLinearMechanism.IsDSIC := by
  intro who types reports misreport
  show V.trueUtility who (types who)
      (Profile.update reports who misreport) ≤
    V.trueUtility who (types who)
      (Profile.update reports who (types who))
  exact V.groves_truthful alloc_efficient h_independent reports who
    (types who) misreport

end GrovesSetup

end GameTheory.Mechanism
