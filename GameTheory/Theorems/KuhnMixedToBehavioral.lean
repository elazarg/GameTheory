import GameTheory.Theorems.KuhnCore
import GameTheory.Model.Lemmas.PerfectRecall
import GameTheory.Model.Lemmas.LocalHistories
import GameTheory.Model.Lemmas.LocalConditioning
import GameTheory.Model.Lemmas.ReachFactorization

namespace GameTheory
namespace Theorems

open Math
open Math.PMFProduct

section InfoModel

open Execution
open InfoModel

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {M : LSM ι} (I : InfoModel M)
variable (D : Execution.Dynamics I)
variable (k : Nat)

/-- Player-local history token used for iterated conditioning:
past local observation trace paired with the realized own action. -/
abbrev LocalHistTok (i : ι) : Type :=
  InfoModel.LocalHistTok (I := I) i


/-- Canonical conditional behavioral realization from a mixed profile,
defined by conditioning on one chosen reachable local history witness. -/
noncomputable def mixedToBehavioral
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : InfoModel.MixedProfile (I := I)) :
    BehavioralProfile I := by
  classical
  refine fun i v =>
    if h :
      ∃ ha : List (JointAction M),
      ∃ ss : List M.State,
        InfoModel.ReachActionTrace M ha ss ∧
        I.projectStates i ss = v
    then ?_ else PMF.pure none
  let ha : List (JointAction M) := Classical.choose h
  let ss : List M.State := Classical.choose (Classical.choose_spec h)
  have hv : I.projectStates i ss = v := (Classical.choose_spec (Classical.choose_spec h)).2
  let hist := InfoModel.localHistTokens (I := I) i ha ss
  exact Math.ProbabilityMassFunction.pushforward
    (iterCondMixedLocal (I := I) i (μ i) hist) (fun f => f v)

omit [Fintype ι] [DecidableEq ι] in
theorem mixedToBehavioral_eq_iterCond_pushforward
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (μ : InfoModel.MixedProfile (I := I))
    (i : ι)
    {ha : List (JointAction M)}
    {ss : List M.State}
    (hr : InfoModel.ReachActionTrace M ha ss) :
    mixedToBehavioral (I := I) μ i (I.projectStates i ss) =
      Math.ProbabilityMassFunction.pushforward
        (iterCondMixedLocal (I := I) i (μ i)
          (InfoModel.localHistTokens (I := I) i ha ss))
        (fun f => f (I.projectStates i ss)) := by
  classical
  unfold mixedToBehavioral
  let v : I.LocalTrace i := I.projectStates i ss
  have hreach :
      ∃ ha' : List (JointAction M),
      ∃ ss' : List M.State,
        InfoModel.ReachActionTrace M ha' ss' ∧
          I.projectStates i ss' = v := by
    exact ⟨ha, ss, hr, rfl⟩
  rw [dif_pos hreach]
  dsimp [v]
  let ha' : List (JointAction M) := Classical.choose hreach
  let ss' : List M.State := Classical.choose (Classical.choose_spec hreach)
  have hr' : InfoModel.ReachActionTrace M ha' ss' :=
    (Classical.choose_spec (Classical.choose_spec hreach)).1
  have hproj :
      I.projectStates i ss' = I.projectStates i ss :=
    (Classical.choose_spec (Classical.choose_spec hreach)).2
  have hacts :
      InfoModel.projectActions i ha' = InfoModel.projectActions i ha :=
    actionRecall_of_projectStates_eq (I := I) hPR i hr' hr hproj
  have hLen' :
      ss'.length = ha'.length + 1 :=
    InfoModel.ReachActionTrace.length_states_eq_succ_actions hr'
  have hLen :
      ss.length = ha.length + 1 :=
    InfoModel.ReachActionTrace.length_states_eq_succ_actions hr
  have hhist :
      InfoModel.localHistTokens (I := I) i ha' ss' =
        InfoModel.localHistTokens (I := I) i ha ss :=
    localHistTokens_eq_of_projectStates_actions_eq
      (I := I) i hLen' hLen hproj hacts
  simp [ha', ss', hhist]

/-- Mixed profile obtained by conditioning each player's local pure-plan law on
the local history realized along a reachable prefix. -/
noncomputable def conditionedMixedProfile
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : InfoModel.MixedProfile (I := I))
    (ha : List (JointAction M))
    (ss : List M.State) :
    InfoModel.MixedProfile (I := I) :=
  fun i => iterCondMixedLocal (I := I) i (μ i)
    (InfoModel.localHistTokens (I := I) i ha ss)
/-- Explicit-action version of
`kuhn_conditioning_distributes_over_sequencing`.

At a reachable prefix, conditioning the mixed profile on the realized local
history and then taking one action/state continuation step yields exactly the
same distribution as first passing to `mixedToBehavioral` and then stepping. -/
theorem kuhn_conditioning_distributes_over_sequencing_actionState
    [∀ i, Finite (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (μ : InfoModel.MixedProfile (I := I))
    {ha : List (JointAction M)}
    {ss : List M.State}
    (hr : InfoModel.ReachActionTrace M ha ss) :
    D.stepActionStateDist (mixedToBehavioral (I := I) μ) ss =
      (InfoModel.mixedJoint (I := I)
        (conditionedMixedProfile (I := I) μ ha ss)).bind
        (fun π => D.stepActionStateDist (pureToBehavioral I π) ss) := by
  classical
  letI : ∀ i, Fintype (I.LocalTrace i) := fun i => Fintype.ofFinite (I.LocalTrace i)
  have hbeh_now :
      ∀ i,
        mixedToBehavioral (I := I) μ i (I.projectStates i ss) =
          InfoModel.realizeBehavioralCanonical (I := I)
            (conditionedMixedProfile (I := I) μ ha ss) i
            (I.projectStates i ss) := by
    intro i
    simpa [conditionedMixedProfile, InfoModel.realizeBehavioralCanonical] using
      mixedToBehavioral_eq_iterCond_pushforward
        (I := I) (hPR := hPR) (μ := μ) i hr
  have hstep_beh :
      D.stepActionStateDist (mixedToBehavioral (I := I) μ) ss =
        D.stepActionStateDist
          (InfoModel.realizeBehavioralCanonical (I := I)
            (conditionedMixedProfile (I := I) μ ha ss))
          ss := by
    apply stepActionStateDist_behavioral_depends_on_current_context (I := I) (D := D)
    intro i
    exact hbeh_now i
  calc
    D.stepActionStateDist (mixedToBehavioral (I := I) μ) ss
        =
      D.stepActionStateDist
        (InfoModel.realizeBehavioralCanonical (I := I)
          (conditionedMixedProfile (I := I) μ ha ss))
        ss := hstep_beh
    _ =
      (InfoModel.mixedJoint (I := I)
        (conditionedMixedProfile (I := I) μ ha ss)).bind
        (fun π => D.stepActionStateDist (pureToBehavioral I π) ss) := by
          symm
          exact mixedJoint_stepActionStateDist_eq_realizeBehavioralCanonical
            (I := I) (D := D)
            (conditionedMixedProfile (I := I) μ ha ss) ss

/-- Most general one-step reachable-prefix form of Kuhn's dynamic consistency.

After conditioning the mixed profile on a reachable prefix, any statistic of the
next explicit action/state step can be computed either:
- by first passing to `mixedToBehavioral` and then stepping once, or
- by averaging pure one-step continuations under the conditioned mixed profile.

This is the strongest local continuation law in the current development; the
state-only and explicit action/state theorems are its special cases. -/
theorem kuhn_conditioning_distributes_over_sequencing_map
    [∀ i, Finite (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    {β : Type*}
    (hPR : I.PerfectRecall)
    (μ : InfoModel.MixedProfile (I := I))
    {ha : List (JointAction M)}
    {ss : List M.State}
    (hr : InfoModel.ReachActionTrace M ha ss)
    (f : JointAction M × M.State → β) :
    Math.ProbabilityMassFunction.pushforward
      (D.stepActionStateDist (mixedToBehavioral (I := I) μ) ss) f =
      (InfoModel.mixedJoint (I := I)
        (conditionedMixedProfile (I := I) μ ha ss)).bind
        (fun π =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepActionStateDist (pureToBehavioral I π) ss) f) := by
  letI : ∀ i, Fintype (I.LocalTrace i) := fun i => Fintype.ofFinite (I.LocalTrace i)
  have hstep :=
    kuhn_conditioning_distributes_over_sequencing_actionState
      (I := I) (D := D) (hPR := hPR) (μ := μ) hr
  calc
    Math.ProbabilityMassFunction.pushforward
      (D.stepActionStateDist (mixedToBehavioral (I := I) μ) ss) f
        =
      Math.ProbabilityMassFunction.pushforward
        ((InfoModel.mixedJoint (I := I)
          (conditionedMixedProfile (I := I) μ ha ss)).bind
          (fun π => D.stepActionStateDist (pureToBehavioral I π) ss))
        f := by simpa using congrArg (fun ν => Math.ProbabilityMassFunction.pushforward ν f) hstep
    _ =
      (InfoModel.mixedJoint (I := I)
        (conditionedMixedProfile (I := I) μ ha ss)).bind
        (fun π =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepActionStateDist (pureToBehavioral I π) ss) f) := by
          simpa using Math.ProbabilityMassFunction.pushforward_bind
            (μ := InfoModel.mixedJoint (I := I)
              (conditionedMixedProfile (I := I) μ ha ss))
            (k := fun π => D.stepActionStateDist (pureToBehavioral I π) ss)
            (f := f)

-- Reachable-prefix distributive law: conditioning the mixed profile on the
-- realized local history and then taking one continuation step gives the same
-- continuation law as first passing to `mixedToBehavioral`.
theorem kuhn_conditioning_distributes_over_sequencing
    [∀ i, Finite (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (μ : InfoModel.MixedProfile (I := I))
    {ha : List (JointAction M)}
    {ss : List M.State}
    (hr : InfoModel.ReachActionTrace M ha ss) :
    Math.ProbabilityMassFunction.pushforward
      (D.stepDist (mixedToBehavioral (I := I) μ) ss)
      (fun t => ss ++ [t]) =
    (InfoModel.mixedJoint (I := I)
      (conditionedMixedProfile (I := I) μ ha ss)).bind
      (fun π =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) ss)
          (fun t => ss ++ [t])) := by
  classical
  letI : ∀ i, Fintype (I.LocalTrace i) := fun i => Fintype.ofFinite (I.LocalTrace i)
  let μHist : InfoModel.MixedProfile (I := I) := conditionedMixedProfile (I := I) μ ha ss
  calc
    (Math.ProbabilityMassFunction.pushforward
      (D.stepDist (mixedToBehavioral (I := I) μ) ss)
      (fun t => ss ++ [t]))
        =
      Math.ProbabilityMassFunction.pushforward
        (D.stepActionStateDist (mixedToBehavioral (I := I) μ) ss)
        (fun x => ss ++ [x.2]) := by
          rw [← Execution.Dynamics.stepDist_eq_pushforward_stepActionStateDist
            (I := I) (D := D) (σ := mixedToBehavioral (I := I) μ) (ss := ss)]
          simpa [Function.comp] using
            (Math.ProbabilityMassFunction.pushforward_comp
              (μ := D.stepActionStateDist (mixedToBehavioral (I := I) μ) ss)
              (f := Prod.snd) (g := fun t => ss ++ [t]))
    _ =
      (InfoModel.mixedJoint (I := I) μHist).bind
        (fun π =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepActionStateDist (pureToBehavioral I π) ss)
            (fun x => ss ++ [x.2])) := by
          simpa [μHist] using
            (kuhn_conditioning_distributes_over_sequencing_map
              (I := I) (D := D) (hPR := hPR) (μ := μ) hr
              (fun x => ss ++ [x.2]))
    _ =
      (InfoModel.mixedJoint (I := I) μHist).bind
        (fun π =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (pureToBehavioral I π) ss)
            (fun t => ss ++ [t])) := by
              refine Math.ProbabilityMassFunction.bind_congr_on_support
                (μ := InfoModel.mixedJoint (I := I) μHist)
                (f := fun π =>
                  Math.ProbabilityMassFunction.pushforward
                    (D.stepActionStateDist (pureToBehavioral I π) ss)
                    (fun x => ss ++ [x.2]))
                (g := fun π =>
                  Math.ProbabilityMassFunction.pushforward
                    (D.stepDist (pureToBehavioral I π) ss)
                    (fun t => ss ++ [t])) ?_
              intro π _
              calc
                Math.ProbabilityMassFunction.pushforward
                  (D.stepActionStateDist (pureToBehavioral I π) ss)
                  (fun x => ss ++ [x.2])
                    =
                  Math.ProbabilityMassFunction.pushforward
                    (Math.ProbabilityMassFunction.pushforward
                      (D.stepActionStateDist (pureToBehavioral I π) ss)
                      Prod.snd)
                    (fun t => ss ++ [t]) := by
                      symm
                      simpa [Function.comp] using
                        (Math.ProbabilityMassFunction.pushforward_comp
                          (μ := D.stepActionStateDist (pureToBehavioral I π) ss)
                          (f := Prod.snd) (g := fun t => ss ++ [t]))
                _ =
                  Math.ProbabilityMassFunction.pushforward
                    (D.stepDist (pureToBehavioral I π) ss)
                    (fun t => ss ++ [t]) := by
                      rw [Execution.Dynamics.stepDist_eq_pushforward_stepActionStateDist
                        (I := I) (D := D) (σ := pureToBehavioral I π) (ss := ss)]

private theorem reachable_stepPoint_eq_conditioned_sum
    [∀ i, Finite (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (μ : InfoModel.MixedProfile (I := I))
    {ha : List (JointAction M)}
    {hs : List M.State}
    (hr : InfoModel.ReachActionTrace M ha hs)
    (y : List M.State) :
    let μHist : InfoModel.MixedProfile (I := I) := conditionedMixedProfile (I := I) μ ha hs
    let stepPureY : PureProfile I → ENNReal := fun π =>
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (pureToBehavioral I π) hs)
        (fun t => hs ++ [t])) y
    (Math.ProbabilityMassFunction.pushforward
      (D.stepDist (mixedToBehavioral (I := I) μ) hs)
      (fun t => hs ++ [t])) y
      =
    ∑' π, (InfoModel.mixedJoint (I := I) μHist) π * stepPureY π := by
  classical
  letI : ∀ i, Fintype (I.LocalTrace i) := fun i => Fintype.ofFinite (I.LocalTrace i)
  let μHist : InfoModel.MixedProfile (I := I) := conditionedMixedProfile (I := I) μ ha hs
  let stepPureY : PureProfile I → ENNReal := fun π =>
    (Math.ProbabilityMassFunction.pushforward
      (D.stepDist (pureToBehavioral I π) hs)
      (fun t => hs ++ [t])) y
  calc
    (Math.ProbabilityMassFunction.pushforward
      (D.stepDist (mixedToBehavioral (I := I) μ) hs)
      (fun t => hs ++ [t])) y
        =
      ((InfoModel.mixedJoint (I := I) μHist).bind
        (fun π =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (pureToBehavioral I π) hs)
            (fun t => hs ++ [t]))) y := by
              simpa [μHist] using congrArg (fun ν => ν y)
                (kuhn_conditioning_distributes_over_sequencing
                  (I := I) (D := D) (hPR := hPR) (μ := μ) hr)
    _ = ∑' π, (InfoModel.mixedJoint (I := I) μHist) π * stepPureY π := by
          simp [PMF.bind_apply, stepPureY]

/-- Weighted bridge at a fixed state prefix. The behavioral side is supplied by
the reachable-prefix sequencing law, while the remaining weighted algebra is
discharged by reach-conditioned disintegration/factorization. -/
theorem stepPoint_eq_via_query_disintegration
    [∀ i, Finite (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (μ : InfoModel.MixedProfile (I := I))
    (n : Nat)
    (hs y : List M.State)
    (hlen : hs.length = n + 1) :
    let μJ : PMF (PureProfile I) := InfoModel.mixedJoint (I := I) μ
    let C : ENNReal := ∑' π, μJ π * (D.runDistPure n π) hs
    C *
      ((Math.ProbabilityMassFunction.pushforward
        (D.stepDist (mixedToBehavioral (I := I) μ) hs)
        (fun t => hs ++ [t])) y)
      =
    ∑' π, μJ π *
      ((D.runDistPure n π) hs *
        ((Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) hs)
          (fun t => hs ++ [t])) y)) := by
  classical
  letI : ∀ i, Fintype (I.LocalTrace i) := fun i => Fintype.ofFinite (I.LocalTrace i)
  let μJ : PMF (PureProfile I) := InfoModel.mixedJoint (I := I) μ
  let stepPureY : PureProfile I → ENNReal := fun π =>
    (Math.ProbabilityMassFunction.pushforward
      (D.stepDist (pureToBehavioral I π) hs)
      (fun t => hs ++ [t])) y
  let C : ENNReal := ∑' π, μJ π * (D.runDistPure n π) hs
  by_cases hC0 : C = 0
  · have hsum0 :
      ∑' π, μJ π *
        ((D.runDistPure n π) hs * stepPureY π) = 0 := by
      refine ENNReal.tsum_eq_zero.2 ?_
      intro π
      have hpi0 : μJ π * (D.runDistPure n π) hs = 0 := by
        apply (ENNReal.tsum_eq_zero.1 hC0)
      simpa [stepPureY, mul_assoc] using congrArg (fun z => z * stepPureY π) hpi0
    calc
      C *
        ((Math.ProbabilityMassFunction.pushforward
          (D.stepDist (mixedToBehavioral (I := I) μ) hs)
          (fun t => hs ++ [t])) y)
          = 0 := by rw [hC0, zero_mul]
      _ = ∑' π, μJ π *
            ((D.runDistPure n π) hs *
              ((Math.ProbabilityMassFunction.pushforward
                (D.stepDist (pureToBehavioral I π) hs)
                (fun t => hs ++ [t])) y)) := by
            simpa [stepPureY] using hsum0.symm
  · have hCpos : C ≠ 0 := hC0
    have hexists : ∃ π : PureProfile I, μJ π * (D.runDistPure n π) hs ≠ 0 := by
      by_contra hnone
      apply hCpos
      refine ENNReal.tsum_eq_zero.2 ?_
      intro π
      exact by_contra fun h => hnone ⟨π, h⟩
    obtain ⟨π0, hπ0⟩ := hexists
    have hrun0 : (D.runDistPure n π0) hs ≠ 0 := by
      intro hzero
      apply hπ0
      simp [hzero]
    obtain ⟨ha, hr, hcompat⟩ :=
      exists_reachActionTrace_of_runDistPure_ne_zero
        (I := I) (D := D) n π0 hs hrun0
    let μHist : InfoModel.MixedProfile (I := I) :=
      conditionedMixedProfile (I := I) μ ha hs
    have hleft_rewrite :
        (Math.ProbabilityMassFunction.pushforward
          (D.stepDist (mixedToBehavioral (I := I) μ) hs)
          (fun t => hs ++ [t])) y
          =
        (∑' π, (InfoModel.mixedJoint (I := I) μHist) π * stepPureY π) := by
      simpa [μHist] using
        reachable_stepPoint_eq_conditioned_sum
          (I := I) (D := D) (hPR := hPR) (μ := μ) hr y
    have hfactor_run :
        ∃ traceMass compatMass : ENNReal,
          C = traceMass * compatMass ∧
          (∑' π, μJ π *
            ((D.runDistPure n π) hs * stepPureY π))
            = traceMass * compatMass *
                (∑' π, (InfoModel.mixedJoint (I := I) μHist) π * stepPureY π) := by
      simpa [μHist, C, conditionedMixedProfile] using
        InfoModel.query_disintegration_factorization
          (I := I) (D := D) (hPR := hPR) (μ := μ) n hlen
          (π0 := π0) hr hcompat stepPureY
    rcases hfactor_run with ⟨traceMass, compatMass, hCfact, hRfact⟩
    calc
      C *
        ((Math.ProbabilityMassFunction.pushforward
          (D.stepDist (mixedToBehavioral (I := I) μ) hs)
          (fun t => hs ++ [t])) y)
          = (traceMass * compatMass) *
              (∑' π, (InfoModel.mixedJoint (I := I) μHist) π * stepPureY π) := by
                rw [hCfact, hleft_rewrite]
      _ = ∑' π, μJ π *
            ((D.runDistPure n π) hs * stepPureY π) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hRfact.symm
      _ = ∑' π, μJ π *
            ((D.runDistPure n π) hs *
              ((Math.ProbabilityMassFunction.pushforward
                (D.stepDist (pureToBehavioral I π) hs)
                (fun t => hs ++ [t])) y)) := by
            simp [stepPureY]

theorem mixedToBehavioral_stepIndependence
    [∀ i, Finite (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (μ : InfoModel.MixedProfile (I := I)) :
    ∀ n,
      (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
        (D.runDistPure n π).bind (fun hs =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (mixedToBehavioral (I := I) μ) hs)
            (fun t => hs ++ [t]))) =
      (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
        (D.runDistPure n π).bind (fun hs =>
          Math.ProbabilityMassFunction.pushforward
            (D.stepDist (pureToBehavioral I π) hs)
            (fun t => hs ++ [t]))) := by
  intro n
  classical
  letI : ∀ i, Fintype (I.LocalTrace i) := fun i => Fintype.ofFinite (I.LocalTrace i)
  ext y
  set μJ : PMF (PureProfile I) := InfoModel.mixedJoint (I := I) μ
  let Lfun : (List M.State) → ENNReal :=
    fun hs =>
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (mixedToBehavioral (I := I) μ) hs)
        (fun t => hs ++ [t])) y
  let Gfun : (List M.State) → PureProfile I → ENNReal :=
    fun hs π =>
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (pureToBehavioral I π) hs)
        (fun t => hs ++ [t])) y
  let FL : PureProfile I → (List M.State) → ENNReal :=
    fun π hs => μJ π * ((D.runDistPure n π) hs * Lfun hs)
  let FR : PureProfile I → (List M.State) → ENNReal :=
    fun π hs => μJ π * ((D.runDistPure n π) hs * Gfun hs π)
  have hswapL :
      (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Lfun hs)
        = ∑' hs, ∑' π, FL π hs := by
    calc
      (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Lfun hs)
          = ∑' π, ∑' hs, μJ π * ((D.runDistPure n π) hs * Lfun hs) := by
              refine tsum_congr ?_
              intro π
              rw [ENNReal.tsum_mul_left]
      _ = ∑' hs, ∑' π, μJ π * ((D.runDistPure n π) hs * Lfun hs) := by
            simpa using
              (ENNReal.tsum_comm
                (f := fun π hs => μJ π * ((D.runDistPure n π) hs * Lfun hs)))
      _ = ∑' hs, ∑' π, FL π hs := by simp [FL]
  have hswapR :
      (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Gfun hs π)
        = ∑' hs, ∑' π, FR π hs := by
    calc
      (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Gfun hs π)
          = ∑' π, ∑' hs, μJ π * ((D.runDistPure n π) hs * Gfun hs π) := by
              refine tsum_congr ?_
              intro π
              rw [ENNReal.tsum_mul_left]
      _ = ∑' hs, ∑' π, μJ π * ((D.runDistPure n π) hs * Gfun hs π) := by
            simpa using
              (ENNReal.tsum_comm
                (f := fun π hs => μJ π * ((D.runDistPure n π) hs * Gfun hs π)))
      _ = ∑' hs, ∑' π, FR π hs := by simp [FR]
  have hPerHs :
      ∀ hs : List M.State, (∑' π, FL π hs) = ∑' π, FR π hs := by
    intro hs
    by_cases hlen : hs.length = n + 1
    · let C : ENNReal := ∑' π, μJ π * (D.runDistPure n π) hs
      have hL :
          (∑' π, FL π hs) = C * Lfun hs := by
        calc
          (∑' π, FL π hs)
              = ∑' π, μJ π * ((D.runDistPure n π) hs * Lfun hs) := by
                  simp [FL]
          _ = ∑' π, (μJ π * (D.runDistPure n π) hs) * Lfun hs := by
                apply tsum_congr
                intro π
                ring
          _ = (∑' π, μJ π * (D.runDistPure n π) hs) * Lfun hs := by
                rw [ENNReal.tsum_mul_right]
          _ = C * Lfun hs := rfl
      have hR :
          (∑' π, FR π hs) =
            ∑' π, μJ π * ((D.runDistPure n π) hs * Gfun hs π) := by
        simp [FR, mul_assoc, mul_comm]
      have hBridge :
          C * Lfun hs =
            ∑' π, μJ π * ((D.runDistPure n π) hs * Gfun hs π) := by
        simpa [Lfun, Gfun, C, mul_assoc, mul_left_comm, mul_comm] using
          (stepPoint_eq_via_query_disintegration
            (I := I) (D := D) (hPR := hPR) (μ := μ) (n := n) (hs := hs) (y := y) hlen)
      exact hL.trans (hBridge.trans hR.symm)
    · have hfzero : ∀ π : PureProfile I, (D.runDistPure n π) hs = 0 := by
        intro π
        by_contra hne
        have hlen' :
            hs.length = n + 1 := by
          have hrun : (D.runDist n (pureToBehavioral I π)) hs ≠ 0 := by
            simpa [Execution.Dynamics.runDistPure] using hne
          exact InfoModel.runDist_support_stateLength (I := I) (D := D) n
            (pureToBehavioral I π) hs hrun
        exact hlen hlen'
      have hFL0 : (∑' π, FL π hs) = 0 := by
        exact (ENNReal.tsum_eq_zero).2 (by intro π; simp [FL, hfzero π])
      have hFR0 : (∑' π, FR π hs) = 0 := by
        exact (ENNReal.tsum_eq_zero).2 (by intro π; simp [FR, hfzero π])
      rw [hFL0, hFR0]
  calc
    (μJ.bind (fun π =>
      (D.runDistPure n π).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (mixedToBehavioral (I := I) μ) hs)
          (fun t => hs ++ [t])))) y
        = (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Lfun hs) := by
            simp [μJ, Lfun, PMF.bind_apply]
    _ = ∑' hs, ∑' π, FL π hs := hswapL
    _ = ∑' hs, ∑' π, FR π hs := by
          apply tsum_congr
          intro hs
          exact hPerHs hs
    _ = (∑' π, μJ π * ∑' hs, (D.runDistPure n π) hs * Gfun hs π) := hswapR.symm
    _ = (μJ.bind (fun π =>
      (D.runDistPure n π).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) hs)
          (fun t => hs ++ [t])))) y := by
            simp [μJ, Gfun, PMF.bind_apply]

/-- Kuhn's mixed-to-behavioral direction for `InfoModel` outcome distributions. -/
theorem mixedToBehavioral_correct
    [∀ i, Finite (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall)
    (μ : InfoModel.MixedProfile (I := I)) :
    D.evalBehavioral k (mixedToBehavioral (I := I) μ) =
      (InfoModel.mixedJoint (I := I) μ).bind (D.evalPure k) := by
  letI : ∀ i, Fintype (I.LocalTrace i) := fun i => Fintype.ofFinite (I.LocalTrace i)
  exact evalBehavioral_eq_mixed_of_stepIndependence (I := I) (D := D) (k := k) μ
    (mixedToBehavioral (I := I) μ)
    (mixedToBehavioral_stepIndependence (I := I) (D := D) hPR μ)

theorem kuhn_mixed_to_behavioral
    [∀ i, Finite (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hPR : I.PerfectRecall) :
    KuhnMixedToBehavioralViaOutcome
      (BehavioralProfile I) (InfoModel.MixedProfile (I := I)) (PureProfile I) I.Outcome
      (InfoModel.mixedJoint (I := I)) (D.evalBehavioral k) (D.evalPure k) := by
  letI : ∀ i, Fintype (I.LocalTrace i) := fun i => Fintype.ofFinite (I.LocalTrace i)
  intro μ
  refine ⟨mixedToBehavioral (I := I) μ, ?_⟩
  simpa using mixedToBehavioral_correct (I := I) (D := D) (k := k) hPR μ

end InfoModel

end Theorems
end GameTheory



