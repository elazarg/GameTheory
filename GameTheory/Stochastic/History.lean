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

/-- Recover one player's Protocol own-play record from the proof-free public
history alone. -/
private def ownPlayOfPublicHistory (who : ι) :
    G.PublicHistory → List (G.PublicHistory × G.Action who)
  | [] => []
  | event :: prior =>
      (prior, event.joint who) ::
        ownPlayOfPublicHistory who prior

private theorem perfectMonitoring_ownPlay_eq_ownPlayOfPublicHistory
    (initial : G.State) [∀ i, Nonempty (G.Action i)] (who : ι) :
    ∀ {state : G.State} (trace : (G.toExecution initial).Trace state),
      (G.perfectMonitoring initial).ownPlay who trace =
        ownPlayOfPublicHistory G who
          (G.publicHistoryOfTrace initial trace)
  | _, .start => rfl
  | _, .extend prior joint isLegal realized => by
      have hjoint :
          joint who = some
            ((G.stageRecordOfEvent initial
              ⟨_, joint, isLegal, _, realized⟩).joint who) :=
        G.stageRecordOfEvent_joint initial
          ⟨_, joint, isLegal, _, realized⟩ who
      rw [InfoSignals.ownPlay_extend,
        G.publicHistoryOfTrace_extend]
      simp only [ownPlayOfPublicHistory]
      rw [hjoint,
        G.perfectMonitoring_infoOf_eq_publicHistoryOfTrace initial who prior]
      simp only
      rw [perfectMonitoring_ownPlay_eq_ownPlayOfPublicHistory initial who prior]

/-- Full public monitoring remembers every player's own past information and
actions, hence satisfies Protocol perfect recall. -/
theorem perfectMonitoring_perfectRecall
    (initial : G.State) [∀ i, Nonempty (G.Action i)] :
    (G.perfectMonitoring initial).PerfectRecall := by
  intro who first second traceFirst traceSecond hinfo
  rw [G.perfectMonitoring_infoOf_eq_publicHistoryOfTrace initial who traceFirst,
    G.perfectMonitoring_infoOf_eq_publicHistoryOfTrace initial who traceSecond]
    at hinfo
  rw [perfectMonitoring_ownPlay_eq_ownPlayOfPublicHistory G initial who traceFirst,
    perfectMonitoring_ownPlay_eq_ownPlayOfPublicHistory G initial who traceSecond,
    hinfo]

/-- Perfect monitoring therefore supplies the no-revisit premise used by the
behavioral-to-mixed Kuhn direction. -/
theorem perfectMonitoring_actsOnceWhereItMatters
    (initial : G.State) [∀ i, Nonempty (G.Action i)] :
    (G.perfectMonitoring initial).ActsOnceWhereItMatters :=
  (G.perfectMonitoring initial).actsOnceWhereItMatters_of_perfectRecall
    (G.perfectMonitoring_perfectRecall initial)

/-- The chronological tuple represented by a reverse-chronological list of a
known length.  The equality proof is erased behind the construction. -/
def chronologicalOfPublicHistory {horizon : ℕ}
    (history : G.PublicHistory) (hlength : history.length = horizon) :
    G.ChronologicalHistory horizon :=
  Equiv.vectorEquivFin G.StageRecord horizon
    (⟨history.reverse, by simpa using hlength⟩ : List.Vector G.StageRecord horizon)

/-- Return a chronological tuple to the public information-state convention. -/
def publicHistoryOfChronological {horizon : ℕ}
    (history : G.ChronologicalHistory horizon) : G.PublicHistory :=
  ((Equiv.vectorEquivFin G.StageRecord horizon).symm history).toList.reverse

-- `List.Vector` is a subtype synonym that the elaborator does not unfold when
-- checking a rewrite motive, so the anonymous constructor below records the
-- underlying subtype rather than the vector type.
set_option backward.isDefEq.respectTransparency false in
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
    PMF G.PublicHistory :=
  PMF.map
    (fun history => G.publicHistoryOfTrace initial history.trace)
    ((G.perfectMonitoring initial).runBehavioral profile horizon)

/-- Project canonical continuation play from an already realized history. -/
def publicHistoryLawFrom (initial : G.State)
    [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (horizon : ℕ)
    (start : (G.toExecution initial).History) : PMF G.PublicHistory :=
  PMF.map
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
    PMF.map_bind]

/-- Every public history in the nonterminating stochastic horizon law has the
requested length. -/
theorem length_eq_of_mem_support_publicHistoryLaw
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (horizon : ℕ)
    {history : G.PublicHistory}
    (hmem : history ∈ (G.publicHistoryLaw initial profile horizon).support) :
    history.length = horizon := by
  rw [publicHistoryLaw, PMF.support_map] at hmem
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
    PMF (G.ChronologicalHistory horizon) :=
  (G.publicHistoryLaw initial profile horizon).bindOnSupport fun history hmem =>
    PMF.pure <|
      G.chronologicalOfPublicHistory history
        (G.length_eq_of_mem_support_publicHistoryLaw initial profile horizon hmem)

/-- Mapping the fixed chronological law back to public histories recovers the
canonical projected law exactly. -/
theorem map_publicHistoryOfChronological_chronologicalHistoryLaw
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (horizon : ℕ) :
    PMF.map G.publicHistoryOfChronological
        (G.chronologicalHistoryLaw initial profile horizon) =
      G.publicHistoryLaw initial profile horizon := by
  unfold chronologicalHistoryLaw
  rw [map_bindOnSupport]
  calc
    _ = (G.publicHistoryLaw initial profile horizon).bind PMF.pure := by
      apply bindOnSupport_eq_bind_of_eq_on_support
      intro history hmem
      simp [PMF.map,
        G.publicHistoryOfChronological_chronologicalOfPublicHistory]
    _ = G.publicHistoryLaw initial profile horizon := PMF.bind_pure _

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
    (profile : G.BehaviorProfile initial) (who : ι)
    (hintegrable : UtilityIntegrable (G.publicHistoryAverageUtility horizon) who
      (G.publicHistoryLaw initial profile horizon)) : ℝ :=
  expectedUtility (G.publicHistoryAverageUtility horizon) who
    (G.publicHistoryLaw initial profile horizon) hintegrable

/-- Public-history payoff is defined exactly when the compiled history payoff is. -/
theorem publicFiniteAverageIntegrable_iff (initial : G.State)
    [∀ i, Nonempty (G.Action i)] (horizon : ℕ)
    (profile : G.BehaviorProfile initial) (who : ι) :
    UtilityIntegrable (G.publicHistoryAverageUtility horizon) who
        (G.publicHistoryLaw initial profile horizon) ↔
      UtilityIntegrable (G.horizonUtility initial horizon) who
        ((G.horizonForm initial horizon).play profile) := by
  rw [G.horizonForm_play]
  unfold publicHistoryLaw UtilityIntegrable
  rw [payoffIntegrable_map_iff]
  simp only [Function.comp_def, horizonUtility,
    G.historyAverageUtility_eq_publicHistoryAverageUtility]

/-- The proof-free evaluator is exactly the canonical finite-average payoff. -/
theorem publicFiniteAveragePayoff_eq_finiteAveragePayoff
    (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (horizon : ℕ) (profile : G.BehaviorProfile initial) (who : ι)
    (hpublic : UtilityIntegrable (G.publicHistoryAverageUtility horizon) who
      (G.publicHistoryLaw initial profile horizon))
    (hcanonical : UtilityIntegrable (G.horizonUtility initial horizon) who
      ((G.horizonForm initial horizon).play profile)) :
    G.publicFiniteAveragePayoff initial horizon profile who hpublic =
      G.finiteAveragePayoff initial horizon profile who hcanonical := by
  let μ := (G.perfectMonitoring initial).runBehavioral profile horizon
  let projection := fun history : (G.toExecution initial).History =>
    G.publicHistoryOfTrace initial history.trace
  let u := fun history : G.PublicHistory =>
    G.publicHistoryAverageUtility horizon history who
  let v := fun history : (G.toExecution initial).History =>
    G.horizonUtility initial horizon history who
  have hp : PayoffIntegrable (μ.map projection) u := hpublic
  have hpu : PayoffIntegrable μ (u ∘ projection) :=
    (payoffIntegrable_map_iff projection μ u).mp hp
  have hv : PayoffIntegrable μ v := by
    simpa only [G.horizonForm_play] using hcanonical
  have hpoint : ∀ history ∈ μ.support, u (projection history) = v history := by
    intro history _
    exact (G.historyAverageUtility_eq_publicHistoryAverageUtility
      initial horizon history who).symm
  have heq : expect (μ.map projection) u hp = expect μ v hv :=
    (expect_map projection μ u hpu hp).trans
      (expect_congr_on_support hpoint hpu hv)
  exact heq

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
              ∃ hpublic : UtilityIntegrable
                  (G.publicHistoryAverageUtility horizon) who
                  (G.publicHistoryLaw initial profile horizon),
                |G.publicFiniteAveragePayoff initial horizon profile who hpublic -
                  value who| ≤ delta) ∧
            ∀ who (deviation :
              (G.perfectMonitoring initial).BehavioralPolicy who),
              ∃ hpublic : UtilityIntegrable
                  (G.publicHistoryAverageUtility horizon) who
                  (G.publicHistoryLaw initial
                    (Profile.update profile who deviation) horizon),
                G.publicFiniteAveragePayoff initial horizon
                  (Profile.update profile who deviation) who hpublic ≤
                  value who + delta := by
  unfold HasUniformDeviationCapConstructor
  constructor
  · intro hcertificate delta hdelta
    obtain ⟨profile, threshold, hprofile⟩ := hcertificate delta hdelta
    refine ⟨profile, threshold, fun horizon hhorizon => ?_⟩
    obtain ⟨honPath, hdeviation⟩ := hprofile horizon hhorizon
    constructor
    · intro who
      obtain ⟨hcanonical, hclose⟩ := honPath who
      let hpublic := (G.publicFiniteAverageIntegrable_iff initial horizon
        profile who).2 hcanonical
      refine ⟨hpublic, ?_⟩
      rw [G.publicFiniteAveragePayoff_eq_finiteAveragePayoff
        initial horizon profile who hpublic hcanonical]
      exact hclose
    · intro who deviation
      obtain ⟨hcanonical, hbound⟩ := hdeviation who deviation
      let hpublic := (G.publicFiniteAverageIntegrable_iff initial horizon
        (Profile.update profile who deviation) who).2 hcanonical
      refine ⟨hpublic, ?_⟩
      rw [G.publicFiniteAveragePayoff_eq_finiteAveragePayoff
        initial horizon (Profile.update profile who deviation) who
        hpublic hcanonical]
      exact hbound
  · intro hcertificate delta hdelta
    obtain ⟨profile, threshold, hprofile⟩ := hcertificate delta hdelta
    refine ⟨profile, threshold, fun horizon hhorizon => ?_⟩
    obtain ⟨honPath, hdeviation⟩ := hprofile horizon hhorizon
    constructor
    · intro who
      obtain ⟨hpublic, hclose⟩ := honPath who
      let hcanonical := (G.publicFiniteAverageIntegrable_iff initial horizon
        profile who).1 hpublic
      refine ⟨hcanonical, ?_⟩
      rw [← G.publicFiniteAveragePayoff_eq_finiteAveragePayoff
        initial horizon profile who hpublic hcanonical]
      exact hclose
    · intro who deviation
      obtain ⟨hpublic, hbound⟩ := hdeviation who deviation
      let hcanonical := (G.publicFiniteAverageIntegrable_iff initial horizon
        (Profile.update profile who deviation) who).1 hpublic
      refine ⟨hcanonical, ?_⟩
      rw [← G.publicFiniteAveragePayoff_eq_finiteAveragePayoff
        initial horizon (Profile.update profile who deviation) who
        hpublic hcanonical]
      exact hbound

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
  apply congrArg (fun f => PMF.map f (profile i (continuation ++ observed)))
  funext action
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
  apply congrArg independentProduct
  funext i
  rw [G.perfectMonitoring_infoOf_eq_publicHistoryOfTrace initial i start.trace]
  rfl

/-- A fresh canonical run from `restart`, with policies shifted past the
proof-free prefix.  This is a named use of the sole Protocol runner. -/
def restartHistoryLaw {initial : G.State}
    [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (observed : G.PublicHistory)
    (restart : G.State) (horizon : ℕ) : PMF G.PublicHistory :=
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
    G.restartHistoryLaw profile observed restart 0 = PMF.pure [] := by
  unfold restartHistoryLaw publicHistoryLaw InformationModel.runBehavioral
    InformationModel.runBehavioralFrom
  rw [ExecutionProtocol.runRandomizedFor_zero, PMF.map, PMF.pure_bind, Function.comp_apply]
  rfl

/-- Convert a suffix law from a restart into complete public histories. -/
def splicePrefix (observed continuation : G.PublicHistory) : G.PublicHistory :=
  continuation ++ observed

/-- The complete-history law represented by a proof-free restart. -/
def restartedFullHistoryLaw {initial : G.State}
    [∀ i, Nonempty (G.Action i)]
    (profile : G.BehaviorProfile initial) (observed : G.PublicHistory)
    (restart : G.State) (horizon : ℕ) : PMF G.PublicHistory :=
  PMF.map (G.splicePrefix observed)
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
  simp only [PMF.map_bind, map_bindOnSupport,
    PMF.map_comp]
  apply bind_congr_on_support
  intro draw hdraw
  apply bindOnSupport_congr
  intro target realized
  simp only [InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_zero, PMF.map, PMF.pure_bind, Function.comp_apply]
  apply congrArg PMF.pure
  simp only [splicePrefix, History.extend,
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
      simp only [ExecutionProtocol.runRandomizedFor_zero, PMF.map,
        PMF.pure_bind, Function.comp_apply,
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
      simp only [PMF.map_bind, map_bindOnSupport, PMF.map_comp]
      apply bind_congr_on_support
      intro draw hdraw
      apply bindOnSupport_congr
      intro target realized
      let originalNext : (G.toExecution initial).History :=
        start.extend draw.2 realized
      let freshNext : (G.toExecution start.state).History :=
        (G.toExecution start.state).initHistory.extend draw.2 realized
      conv_rhs => rw [← PMF.map_comp]
      have hcontinuation :
          G.publicHistoryLawFrom initial profile fuel originalNext =
            PMF.map (G.splicePrefix (G.publicHistoryOfTrace initial start.trace))
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
        rw [G.afterPublicHistory_afterPublicHistory, PMF.map_comp]
        apply congrArg (fun relabel => PMF.map relabel _)
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
      (independentProduct fun i => profile i observed).bind fun actions =>
        (G.transition restart actions).bindOnSupport fun target _ =>
          PMF.map
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
  simp only [PMF.map_bind, map_bindOnSupport]
  apply bind_congr_on_support
  · intro actions _
    apply bindOnSupport_congr
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
