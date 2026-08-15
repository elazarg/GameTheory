/-
# Chronological stochastic histories and restart calculus

This module projects proof-facing finite-history laws from the canonical
Protocol runner.  It does not define a stochastic runner: every law below is a
map or support-dependent map of `runBehavioral`.
-/

import GameTheory.Stochastic.PublicPolicy
import GameTheory.Stochastic.Uniform

noncomputable section

namespace GameTheory.Stochastic

open GameTheory.Math.Probability Stochastic Protocol Protocol.ExecutionProtocol

universe uι us ua

namespace Game

variable {ι : Type uι} (G : Stochastic.Game.{uι, us, ua} ι)

/-- A fixed-length stochastic history in play order. -/
abbrev ChronologicalHistory (horizon : ℕ) := Fin horizon → G.StageRecord

private def reverseHistoryEquiv : G.PublicHistory ≃ G.PublicHistory where
  toFun := List.reverse
  invFun := List.reverse
  left_inv := List.reverse_reverse
  right_inv := List.reverse_reverse

/-- Reverse chronological lists and length-indexed chronological histories are
exactly equivalent when the length is retained. -/
def chronologicalHistoryEquiv :
    G.PublicHistory ≃ Σ horizon, G.ChronologicalHistory horizon :=
  G.reverseHistoryEquiv.trans List.equivSigmaTuple

/-- Expose one canonical realized trace as proof-free stochastic records.  The
list keeps the information-state convention: newest record first. -/
def publicHistoryOfTrace (initial : G.State) [∀ i, Nonempty (G.Action i)] :
    {state : G.State} → (G.toExecution initial).Trace state → G.PublicHistory
  | _, .start => []
  | _, .extend prior joint isLegal realized =>
      G.stageRecordOfEvent initial
        ⟨_, joint, isLegal, _, realized⟩ ::
        publicHistoryOfTrace initial prior

@[simp]
theorem publicHistoryOfTrace_start (initial : G.State)
    [∀ i, Nonempty (G.Action i)] :
    G.publicHistoryOfTrace initial
        (Trace.start : (G.toExecution initial).Trace initial) = [] :=
  rfl

@[simp]
theorem publicHistoryOfTrace_extend (initial : G.State)
    [∀ i, Nonempty (G.Action i)] {source target : G.State}
    (prior : (G.toExecution initial).Trace source)
    (joint : ∀ i, Option (G.Action i))
    (isLegal : (G.toExecution initial).Legal source joint)
    (realized : target ∈
      ((G.toExecution initial).step source ⟨joint, isLegal⟩).support) :
    G.publicHistoryOfTrace initial
        (.extend prior joint isLegal realized) =
      G.stageRecordOfEvent initial
        ⟨source, joint, isLegal, target, realized⟩ ::
        G.publicHistoryOfTrace initial prior :=
  rfl

@[simp]
theorem publicHistoryOfTrace_length (initial : G.State)
    [∀ i, Nonempty (G.Action i)] :
    ∀ {state : G.State} (trace : (G.toExecution initial).Trace state),
      (G.publicHistoryOfTrace initial trace).length = trace.length
  | _, .start => rfl
  | _, .extend prior joint isLegal realized => by
      simp only [publicHistoryOfTrace, List.length_cons, Trace.length]
      rw [publicHistoryOfTrace_length initial prior]

/-- Perfect monitoring exposes exactly the proof-free history projection to
every player. -/
theorem perfectMonitoring_infoOf_eq_publicHistoryOfTrace
    (initial : G.State) [∀ i, Nonempty (G.Action i)] (who : ι) :
    ∀ {state : G.State} (trace : (G.toExecution initial).Trace state),
      (G.perfectMonitoring initial).infoOf who trace =
        G.publicHistoryOfTrace initial trace
  | _, .start => rfl
  | _, .extend prior joint isLegal realized => by
      simp only [InfoSignals.infoOf, perfectMonitoring, perfectSignals,
        publicHistoryOfTrace]
      rw [perfectMonitoring_infoOf_eq_publicHistoryOfTrace initial who prior]

/-- The chronological tuple represented by a reverse-chronological list of a
known length.  The equality proof is erased behind the construction. -/
def chronologicalOfPublicHistory {horizon : ℕ}
    (history : G.PublicHistory) (hlength : history.length = horizon) :
    G.ChronologicalHistory horizon :=
  Equiv.vectorEquivFin G.StageRecord horizon
    ⟨history.reverse, by simpa using hlength⟩

/-- Return a chronological tuple to the public information-state convention. -/
def publicHistoryOfChronological {horizon : ℕ}
    (history : G.ChronologicalHistory horizon) : G.PublicHistory :=
  ((Equiv.vectorEquivFin G.StageRecord horizon).symm history).toList.reverse

@[simp]
theorem publicHistoryOfChronological_chronologicalOfPublicHistory
    {horizon : ℕ} (history : G.PublicHistory)
    (hlength : history.length = horizon) :
    G.publicHistoryOfChronological
        (G.chronologicalOfPublicHistory history hlength) = history := by
  unfold publicHistoryOfChronological chronologicalOfPublicHistory
  rw [Equiv.symm_apply_apply]
  simp

section FinitePlayers

variable [Fintype ι]

/-- The proof-free public-history law is a projection of canonical behavioral
play, not an independently recursive stochastic law. -/
def publicHistoryLaw (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (horizon : ℕ) :
    FinDist G.PublicHistory :=
  FinDist.map
    (fun history => G.publicHistoryOfTrace initial history.trace)
    ((G.perfectMonitoring initial).runBehavioral profile horizon)

/-- Project canonical continuation play from an already realized history. -/
def publicHistoryLawFrom (initial : G.State)
    [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (horizon : ℕ)
    (start : (G.toExecution initial).History) : FinDist G.PublicHistory :=
  FinDist.map
    (fun history => G.publicHistoryOfTrace initial history.trace)
    ((G.perfectMonitoring initial).runBehavioralFrom profile horizon start)

@[simp]
theorem publicHistoryLawFrom_init (initial : G.State)
    [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (horizon : ℕ) :
    G.publicHistoryLawFrom initial profile horizon
        (G.toExecution initial).initHistory =
      G.publicHistoryLaw initial profile horizon :=
  rfl

/-- Projected continuation laws inherit exact adjacent-horizon composition
from the canonical runner. -/
theorem publicHistoryLawFrom_add (initial : G.State)
    [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (firstFuel secondFuel : ℕ)
    (start : (G.toExecution initial).History) :
    G.publicHistoryLawFrom initial profile (firstFuel + secondFuel) start =
      ((G.perfectMonitoring initial).runBehavioralFrom profile firstFuel start).bind
        (G.publicHistoryLawFrom initial profile secondFuel) := by
  unfold publicHistoryLawFrom
  rw [(G.perfectMonitoring initial).runBehavioralFrom_add,
    FinDist.map_bind]

/-- Every public history in the nonterminating stochastic horizon law has the
requested length. -/
theorem length_eq_of_mem_support_publicHistoryLaw
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (horizon : ℕ)
    {history : G.PublicHistory}
    (hmem : history ∈ (G.publicHistoryLaw initial profile horizon).support) :
    history.length = horizon := by
  rw [publicHistoryLaw, FinDist.support_map] at hmem
  obtain ⟨result, hresult, rfl⟩ := hmem
  rw [G.publicHistoryOfTrace_length]
  have hlength :=
    (G.toExecution initial).trace_length_eq_of_mem_support_runRandomizedFor
      ((G.perfectMonitoring initial).randomizedChooser profile)
      (fun state => by simp) horizon
      (G.toExecution initial).initHistory result hresult
  simpa [ExecutionProtocol.initHistory, Trace.length] using hlength

/-- A genuinely fixed-horizon chronological law, obtained only by using the
support invariant of `publicHistoryLaw`. -/
def chronologicalHistoryLaw (initial : G.State)
    [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (horizon : ℕ) :
    FinDist (G.ChronologicalHistory horizon) :=
  (G.publicHistoryLaw initial profile horizon).bindOnSupport fun history hmem =>
    FinDist.pure <|
      G.chronologicalOfPublicHistory history
        (G.length_eq_of_mem_support_publicHistoryLaw initial profile horizon hmem)

/-- Mapping the fixed chronological law back to public histories recovers the
canonical projected law exactly. -/
theorem map_publicHistoryOfChronological_chronologicalHistoryLaw
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (horizon : ℕ) :
    FinDist.map G.publicHistoryOfChronological
        (G.chronologicalHistoryLaw initial profile horizon) =
      G.publicHistoryLaw initial profile horizon := by
  unfold chronologicalHistoryLaw
  rw [FinDist.map_bindOnSupport]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun history => FinDist.pure history)]
  · exact FinDist.bind_pure _
  · intro history hmem
    rw [FinDist.map_pure,
      G.publicHistoryOfChronological_chronologicalOfPublicHistory]

/-- Stage utility read directly from one proof-free stochastic record. -/
def stageRecordUtility (record : G.StageRecord) (who : ι) : ℝ :=
  G.stageUtility record.source record.joint who

/-- Average payoff on a proof-free public history.  List order is irrelevant
for the finite sum, so this works with the monitoring convention directly. -/
def publicHistoryAverageUtility (horizon : ℕ)
    (history : G.PublicHistory) (who : ι) : ℝ :=
  (horizon : ℝ)⁻¹ * (history.map fun record => G.stageRecordUtility record who).sum

omit [Fintype ι] in
private theorem valueSum_eq_publicHistory_sum (initial : G.State)
    [∀ i, Nonempty (G.Action i)] :
    ∀ {state : G.State} (trace : (G.toExecution initial).Trace state) (who : ι),
      trace.valueSum (fun event => G.eventUtility initial event who) =
        ((G.publicHistoryOfTrace initial trace).map
          (fun record => G.stageRecordUtility record who)).sum
  | _, .start, _ => rfl
  | _, .extend prior joint isLegal realized, who => by
      simp only [Trace.valueSum_extend, publicHistoryOfTrace_extend,
        List.map_cons, List.sum_cons]
      rw [valueSum_eq_publicHistory_sum initial prior who]
      simp only [eventUtility, stageRecordUtility]
      ac_rfl

omit [Fintype ι] in
/-- Canonical trace evaluation and proof-free public-history evaluation agree
pointwise. -/
theorem historyAverageUtility_eq_publicHistoryAverageUtility
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (horizon : ℕ) (history : (G.toExecution initial).History) (who : ι) :
    G.historyAverageUtility initial horizon history who =
      G.publicHistoryAverageUtility horizon
        (G.publicHistoryOfTrace initial history.trace) who := by
  unfold historyAverageUtility publicHistoryAverageUtility History.valueSum
  rw [G.valueSum_eq_publicHistory_sum initial history.trace who]

/-- Expected finite-horizon payoff evaluated solely on the proof-free public
history law. -/
def publicFiniteAveragePayoff (initial : G.State)
    [∀ i, Nonempty (G.Action i)] (horizon : ℕ)
    (profile : G.BehaviorProfile initial) (who : ι) : ℝ :=
  expectedUtility (G.publicHistoryAverageUtility horizon) who
    (G.publicHistoryLaw initial profile horizon)

/-- The proof-free evaluator is exactly the canonical finite-average payoff. -/
theorem publicFiniteAveragePayoff_eq_finiteAveragePayoff
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (horizon : ℕ) (profile : G.BehaviorProfile initial) (who : ι) :
    G.publicFiniteAveragePayoff initial horizon profile who =
      G.finiteAveragePayoff initial horizon profile who := by
  unfold publicFiniteAveragePayoff publicHistoryLaw finiteAveragePayoff
  rw [G.horizonForm_play, expectedUtility_map]
  apply congrArg (fun utility => expectedUtility utility who
    ((G.perfectMonitoring initial).runBehavioral profile horizon))
  funext history player
  exact (G.historyAverageUtility_eq_publicHistoryAverageUtility
    initial horizon history player).symm

/-- Uniform deviation-cap certificates can be written entirely with the
proof-free public-history evaluator.  This is a characterization of the one
canonical certificate, not a second uniform-equilibrium predicate. -/
theorem hasUniformDeviationCapConstructor_iff_publicHistoryPayoff
    [DecidableEq ι] (initial : G.State)
    [∀ i, Nonempty (G.Action i)] (value : ι → ℝ) :
    G.HasUniformDeviationCapConstructor initial value ↔
      ∀ delta : ℝ, 0 < delta →
        ∃ (profile : G.BehaviorProfile initial) (threshold : ℕ),
          ∀ horizon, threshold ≤ horizon →
            (∀ who,
              |G.publicFiniteAveragePayoff initial horizon profile who -
                value who| ≤ delta) ∧
            ∀ who (deviation :
              (G.perfectMonitoring initial).BehavioralPolicy who),
              G.publicFiniteAveragePayoff initial horizon
                  (Profile.update profile who deviation) who ≤
                value who + delta := by
  unfold HasUniformDeviationCapConstructor
  constructor <;> intro hcertificate delta hdelta <;>
    obtain ⟨profile, threshold, hprofile⟩ := hcertificate delta hdelta <;>
    exact ⟨profile, threshold, fun horizon hhorizon => by
      simpa only [G.publicFiniteAveragePayoff_eq_finiteAveragePayoff] using
        hprofile horizon hhorizon⟩

/-! ## Proof-free restart inputs -/

/-- Shift a canonical behavioral profile past a proof-free public prefix.  It
is still the same behavioral-policy carrier: a continuation history is simply
prepended to the already observed reverse-chronological prefix. -/
def afterPublicHistory
    {initial restart : G.State} [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (observed : G.PublicHistory) :
    G.BehaviorProfile restart :=
  fun i continuation => profile i (continuation ++ observed)

omit [Fintype ι] in
@[simp]
theorem afterPublicHistory_apply
    {initial restart : G.State} [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (observed continuation : G.PublicHistory)
    (i : ι) :
    (G.afterPublicHistory (restart := restart) profile observed) i continuation =
      profile i (continuation ++ observed) :=
  rfl

omit [Fintype ι] in
@[simp]
theorem afterPublicHistory_nil
    {initial restart : G.State} [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) :
    G.afterPublicHistory (restart := restart) profile [] = profile := by
  funext i continuation
  unfold afterPublicHistory
  rw [List.append_nil]

omit [Fintype ι] in
/-- Restarting twice composes prefixes in the order induced by the
reverse-chronological information convention. -/
theorem afterPublicHistory_afterPublicHistory
    {initial firstRestart secondRestart : G.State}
    [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial)
    (firstPrefix secondPrefix : G.PublicHistory) :
    G.afterPublicHistory (restart := secondRestart)
        (G.afterPublicHistory (restart := firstRestart) profile firstPrefix)
        secondPrefix =
      G.afterPublicHistory (restart := secondRestart) profile
        (secondPrefix ++ firstPrefix) := by
  funext i continuation
  unfold afterPublicHistory
  rw [List.append_assoc]

omit [Fintype ι] in
/-- Shifting ordinary public policies before compilation is the same canonical
behavioral profile as shifting their compiled profile. -/
theorem toBehaviorProfile_after
    {initial restart : G.State} [∀ i, Nonempty (G.Action i)]
    (profile : G.PublicProfile initial) (observed : G.PublicHistory) :
    G.toBehaviorProfile restart
        (PublicProfile.after (restart := restart) profile observed) =
      G.afterPublicHistory (restart := restart)
        (G.toBehaviorProfile initial profile) observed := by
  funext i continuation
  unfold toBehaviorProfile toBehavioralPolicy PublicProfile.after
    PublicPolicy.after afterPublicHistory
  apply FinDist.map_congr_of_eq_on_support
  intro action _
  apply Subtype.ext
  rfl

/-- At a fresh restart, the shifted profile draws exactly the joint-action law
the original profile draws after the represented realized history. -/
theorem behavioralJoint_afterPublicHistory_init
    {initial : G.State} [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial)
    (start : (G.toExecution initial).History) :
    (G.perfectMonitoring start.state).behavioralJoint
        (G.afterPublicHistory (restart := start.state) profile
          (G.publicHistoryOfTrace initial start.trace))
        (G.toExecution start.state).initHistory.trace (by simp) =
      (G.perfectMonitoring initial).behavioralJoint profile start.trace (by simp) := by
  unfold InformationModel.behavioralJoint
  congr 1
  apply congrArg FinDist.pi
  funext i
  rw [G.perfectMonitoring_infoOf_eq_publicHistoryOfTrace initial i start.trace]
  rfl

/-- A fresh canonical run from `restart`, with policies shifted past the
proof-free prefix.  This is a named use of the sole Protocol runner. -/
def restartHistoryLaw {initial : G.State}
    [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (observed : G.PublicHistory)
    (restart : G.State) (horizon : ℕ) : FinDist G.PublicHistory :=
  G.publicHistoryLaw restart
    (G.afterPublicHistory (restart := restart) profile observed) horizon

/-- Restarting a profile that was already shifted is one restart at the
combined reverse-chronological prefix. -/
theorem restartHistoryLaw_afterPublicHistory
    {initial firstRestart : G.State} [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial)
    (firstObserved nextObserved : G.PublicHistory)
    (restart : G.State) (horizon : ℕ) :
    G.restartHistoryLaw
        (G.afterPublicHistory (restart := firstRestart) profile firstObserved)
        nextObserved restart horizon =
      G.restartHistoryLaw profile (nextObserved ++ firstObserved)
        restart horizon := by
  unfold restartHistoryLaw
  rw [G.afterPublicHistory_afterPublicHistory]

@[simp]
theorem restartHistoryLaw_zero {initial : G.State}
    [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (observed : G.PublicHistory)
    (restart : G.State) :
    G.restartHistoryLaw profile observed restart 0 = FinDist.pure [] := by
  unfold restartHistoryLaw publicHistoryLaw InformationModel.runBehavioral
    InformationModel.runBehavioralFrom
  rw [ExecutionProtocol.runRandomizedFor_zero, FinDist.map_pure]
  rfl

/-- Convert a suffix law from a restart into complete public histories. -/
def splicePrefix (observed continuation : G.PublicHistory) : G.PublicHistory :=
  continuation ++ observed

/-- The complete-history law represented by a proof-free restart. -/
def restartedFullHistoryLaw {initial : G.State}
    [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (observed : G.PublicHistory)
    (restart : G.State) (horizon : ℕ) : FinDist G.PublicHistory :=
  FinDist.map (G.splicePrefix observed)
    (G.restartHistoryLaw profile observed restart horizon)

/-- One-step continuation from a realized canonical history is exactly a fresh
run from its endpoint under the shifted profile, with the old prefix spliced
back onto the result.  This is the smallest restart identity that can expose
an action-dependent transition mismatch. -/
theorem publicHistoryLawFrom_one_eq_restartedFullHistoryLaw
    {initial : G.State} [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial)
    (start : (G.toExecution initial).History) :
    G.publicHistoryLawFrom initial profile 1 start =
      G.restartedFullHistoryLaw profile
        (G.publicHistoryOfTrace initial start.trace) start.state 1 := by
  have horiginal : ¬ (G.toExecution initial).terminal start.state := by simp
  have hfresh : ¬ (G.toExecution start.state).terminal start.state := by simp
  unfold publicHistoryLawFrom restartedFullHistoryLaw restartHistoryLaw
    publicHistoryLaw InformationModel.runBehavioral
  rw [(G.perfectMonitoring initial).runBehavioralFrom_succ_of_not_terminal
      profile 0 horiginal,
    (G.perfectMonitoring start.state).runBehavioralFrom_succ_of_not_terminal
      (G.afterPublicHistory (restart := start.state) profile
        (G.publicHistoryOfTrace initial start.trace)) 0 hfresh,
    G.behavioralJoint_afterPublicHistory_init profile start]
  simp only [FinDist.map_bind, FinDist.map_bindOnSupport,
    FinDist.map_comp]
  apply FinDist.bind_congr
  intro draw hdraw
  apply FinDist.bindOnSupport_congr
  intro target realized
  simp only [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_zero, FinDist.map_pure]
  apply congrArg FinDist.pure
  simp only [Function.comp_apply, splicePrefix, History.extend,
    ExecutionProtocol.initHistory, publicHistoryOfTrace, List.singleton_append]
  rfl

/-- The restart identity holds for every continuation horizon. -/
theorem publicHistoryLawFrom_eq_restartedFullHistoryLaw
    {initial : G.State} [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial)
    (start : (G.toExecution initial).History) :
    ∀ horizon,
      G.publicHistoryLawFrom initial profile horizon start =
        G.restartedFullHistoryLaw profile
          (G.publicHistoryOfTrace initial start.trace) start.state horizon := by
  intro horizon
  induction horizon generalizing initial with
  | zero =>
      unfold publicHistoryLawFrom restartedFullHistoryLaw restartHistoryLaw
        publicHistoryLaw InformationModel.runBehavioral
        InformationModel.runBehavioralFrom
      simp only [ExecutionProtocol.runRandomizedFor_zero, FinDist.map_pure,
        splicePrefix, ExecutionProtocol.initHistory, publicHistoryOfTrace,
        List.nil_append]
  | succ fuel ih =>
      have horiginal : ¬ (G.toExecution initial).terminal start.state := by simp
      have hfresh : ¬ (G.toExecution start.state).terminal start.state := by simp
      unfold publicHistoryLawFrom restartedFullHistoryLaw restartHistoryLaw
        publicHistoryLaw InformationModel.runBehavioral
      rw [(G.perfectMonitoring initial).runBehavioralFrom_succ_of_not_terminal
          profile fuel horiginal,
        (G.perfectMonitoring start.state).runBehavioralFrom_succ_of_not_terminal
          (G.afterPublicHistory (restart := start.state) profile
            (G.publicHistoryOfTrace initial start.trace)) fuel hfresh,
        G.behavioralJoint_afterPublicHistory_init profile start]
      simp only [FinDist.map_bind, FinDist.map_bindOnSupport, FinDist.map_comp]
      apply FinDist.bind_congr
      intro draw hdraw
      apply FinDist.bindOnSupport_congr
      intro target realized
      let originalNext : (G.toExecution initial).History :=
        start.extend draw.2 realized
      let freshNext : (G.toExecution start.state).History :=
        (G.toExecution start.state).initHistory.extend draw.2 realized
      conv_rhs => rw [← FinDist.map_comp]
      have hcontinuation :
          G.publicHistoryLawFrom initial profile fuel originalNext =
            FinDist.map (G.splicePrefix (G.publicHistoryOfTrace initial start.trace))
              (G.publicHistoryLawFrom start.state
                (G.afterPublicHistory (restart := start.state) profile
                  (G.publicHistoryOfTrace initial start.trace)) fuel freshNext) := by
        rw [ih profile originalNext]
        rw [ih
          (G.afterPublicHistory (restart := start.state) profile
            (G.publicHistoryOfTrace initial start.trace)) freshNext]
        unfold restartedFullHistoryLaw restartHistoryLaw
        simp only [originalNext, freshNext, History.extend,
          ExecutionProtocol.initHistory, publicHistoryOfTrace]
        rw [G.afterPublicHistory_afterPublicHistory, FinDist.map_comp]
        apply congrArg (fun relabel => FinDist.map relabel _)
        funext continuation
        simp only [Function.comp_apply, splicePrefix]
        rw [List.append_assoc]
        rw [List.singleton_append]
        rfl
      exact hcontinuation

/-- One restarted stage is exposed entirely in ordinary simultaneous actions
and native stochastic transitions.  Its continuation is another named restart
law, so clients can disintegrate horizons without touching Protocol traces. -/
theorem restartHistoryLaw_succ_toPublicProfile
    {initial : G.State} [∀ i, Nonempty (G.Action i)]
    (profile : G.PublicProfile initial) (observed : G.PublicHistory)
    (restart : G.State) (fuel : ℕ) :
    G.restartHistoryLaw (G.toBehaviorProfile initial profile)
        observed restart (fuel + 1) =
      (FinDist.pi fun i => profile i observed).bind fun actions =>
        (G.transition restart actions).bindOnSupport fun target _ =>
          FinDist.map
            (fun continuation => continuation ++
              [{ source := restart, joint := actions, target := target }])
            (G.restartHistoryLaw (G.toBehaviorProfile initial profile)
              ({ source := restart, joint := actions, target := target } :: observed)
              target fuel) := by
  let shifted : G.PublicProfile restart :=
    PublicProfile.after (restart := restart) profile observed
  have hcompiled :
      G.afterPublicHistory (restart := restart)
          (G.toBehaviorProfile initial profile) observed =
        G.toBehaviorProfile restart shifted := by
    exact (G.toBehaviorProfile_after profile observed).symm
  unfold restartHistoryLaw publicHistoryLaw InformationModel.runBehavioral
  rw [hcompiled]
  rw [G.runBehavioralFrom_succ_toBehaviorProfile restart shifted fuel
    (G.toExecution restart).initHistory]
  simp only [FinDist.map_bind, FinDist.map_bindOnSupport]
  apply FinDist.bind_congr
  · intro actions _
    apply FinDist.bindOnSupport_congr
    intro target realized
    let first : (G.toExecution restart).History :=
      (G.toExecution restart).initHistory.extend
        (G.canonicalJoint restart restart actions).2
        (G.canonicalRealized restart realized)
    have hfirst : G.publicHistoryOfTrace restart first.trace =
        [{ source := restart, joint := actions, target := target }] := by
      unfold first
      simp only [History.extend, ExecutionProtocol.initHistory,
        publicHistoryOfTrace]
      apply congrArg (fun record => [record])
      rfl
    have hcontinuation :=
      G.publicHistoryLawFrom_eq_restartedFullHistoryLaw
        (G.toBehaviorProfile restart shifted) first fuel
    unfold restartedFullHistoryLaw at hcontinuation
    rw [hfirst, ← hcompiled, G.restartHistoryLaw_afterPublicHistory]
      at hcontinuation
    unfold restartHistoryLaw publicHistoryLaw InformationModel.runBehavioral
      at hcontinuation
    exact hcontinuation

end FinitePlayers

end Game

end GameTheory.Stochastic
