/-
# Localizing subgame comparisons at the root

A whole-policy deviation inside a proper subgame can be spliced into the
incumbent policy: follow the deviation at the information states met below the
subgame root and the incumbent everywhere else. Closure of the subgame under
information makes the splice a legal information-local policy. Its outcome law
from the start of play differs from the incumbent's exactly by the subgame
deviation's difference, scaled by the probability that incumbent play reaches
the subgame root.

So a subgame comparison at a root reached with positive probability is a
positive multiple of a Nash comparison: subgame perfection adds to Nash only the
comparisons at unreached proper subgames. Both facts are stated here as mass
identities, without subtraction, over the well-founded terminal-history law.
-/

import GameTheory.Analysis.IncentiveHierarchy
import GameTheory.Analysis.Protocol.Incentives
import GameTheory.Protocol.SubgamePerfect

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability
open scoped ENNReal

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

namespace ExecutionProtocol

variable (E)

variable {E}

/-- A history reaching a child of another history, other than the child
itself, already reaches the parent: ancestors are unique at each depth. -/
theorem historyReaches_of_extend {root history : E.History}
    {joint : ∀ i, Option (E.Action i)} {isLegal : E.Legal history.state joint}
    {reached : E.State}
    {realized : reached ∈ (E.step history.state ⟨joint, isLegal⟩).support}
    (hreach : E.HistoryReaches root (history.extend isLegal realized))
    (hne : history.extend isLegal realized ≠ root) :
    E.HistoryReaches root history := by
  obtain ⟨fuel, hroot⟩ := hreach
  have hchild : (history.extend isLegal realized).trace.length =
      history.trace.length + 1 := by
    simp [History.extend, Trace.length]
  have hle := hroot.trace_length_le
  rcases Nat.lt_or_ge root.trace.length (history.trace.length + 1) with hlt | hge
  · obtain ⟨ancestor, ancestorFuel, hlength, hancestor⟩ :=
      E.exists_ancestor_of_le history (depth := root.trace.length) (by omega)
    have hone : E.ReachesWithin 1 history (history.extend isLegal realized) :=
      .step joint isLegal realized (.refl 0 _)
    have hsame : root = ancestor :=
      ReachesWithin.eq_start_of_same_length hroot (hancestor.trans hone) hlength.symm
    exact ⟨ancestorFuel, by simpa only [← hsame] using hancestor⟩
  · exact absurd (hroot.eq_of_trace_length_eq (by omega)) hne

/-- Every terminal history in the support of the law from a history is reached
from it. -/
theorem historyBackwardLaw_support_reaches {certificate : E.WellFoundedHistories}
    {chooser : E.HistoryChooser} (start : E.History) :
    ∀ final ∈ (E.historyBackwardLaw certificate chooser start).support,
      E.HistoryReaches start final := by
  induction start using certificate.induction with
  | _ current ih =>
      intro final hfinal
      by_cases hterm : E.terminal current.state
      · rw [E.historyBackwardLaw_of_terminal hterm, PMF.support_pure,
          Set.mem_singleton_iff] at hfinal
        subst hfinal
        exact HistoryReaches.refl E _
      · rw [E.historyBackwardLaw_of_not_terminal hterm,
          PMF.mem_support_bindOnSupport_iff] at hfinal
        obtain ⟨reached, realized, hmem⟩ := hfinal
        let chosen := chooser current hterm
        exact HistoryReaches.step E chosen.2 realized
          (ih (current.extend chosen.2 realized) ⟨chosen.1, chosen.2, realized⟩ final hmem)

variable (E)

/-- The probability that play from `start` passes through `root`, as the mass
of the terminal histories continuing `root`. -/
def subtreeMass (certificate : E.WellFoundedHistories) (chooser : E.HistoryChooser)
    (root start : E.History) : ℝ≥0∞ :=
  (E.historyBackwardLaw certificate chooser start).toOuterMeasure
    {final | E.HistoryReaches root final}

variable {E}

theorem subtreeMass_self (certificate : E.WellFoundedHistories) (chooser : E.HistoryChooser)
    (root : E.History) : E.subtreeMass certificate chooser root root = 1 := by
  rw [subtreeMass, PMF.toOuterMeasure_apply_eq_one_iff]
  exact E.historyBackwardLaw_support_reaches root

theorem subtreeMass_le_one (certificate : E.WellFoundedHistories) (chooser : E.HistoryChooser)
    (root start : E.History) : E.subtreeMass certificate chooser root start ≤ 1 := by
  rw [subtreeMass, PMF.toOuterMeasure_apply]
  calc
    _ ≤ ∑' final, E.historyBackwardLaw certificate chooser start final :=
      ENNReal.tsum_le_tsum fun final => Set.indicator_le_self _ _ final
    _ = 1 := PMF.tsum_coe _

/-- **Mass decomposition.** Let a combined chooser follow a local chooser at
every history continuing `root` and a base chooser everywhere else. From any
history that is `root` or does not continue it, the combined law plus the
subtree mass times the base law at `root` equals the base law plus the subtree
mass times the local law at `root`. -/
theorem historyBackwardLaw_add_subtreeMass (certificate : E.WellFoundedHistories)
    {base inside combined : E.HistoryChooser} {root : E.History}
    (hinside : ∀ later, E.HistoryReaches root later →
      ∀ hterm, combined later hterm = inside later hterm)
    (houtside : ∀ later, ¬ E.HistoryReaches root later →
      ∀ hterm, combined later hterm = base later hterm) :
    ∀ start, (start = root ∨ ¬ E.HistoryReaches root start) → ∀ final,
      E.historyBackwardLaw certificate combined start final +
          E.subtreeMass certificate base root start *
            E.historyBackwardLaw certificate base root final =
        E.historyBackwardLaw certificate base start final +
          E.subtreeMass certificate base root start *
            E.historyBackwardLaw certificate inside root final := by
  intro start
  induction start using certificate.induction with
  | _ current ih =>
      intro hcurrent final
      by_cases hroot : current = root
      · subst current
        have hlaw : E.historyBackwardLaw certificate combined root =
            E.historyBackwardLaw certificate inside root :=
          E.historyBackwardLaw_congr_of_reaches root hinside
        rw [hlaw, subtreeMass_self, one_mul, one_mul, add_comm]
      have hnot : ¬ E.HistoryReaches root current := hcurrent.resolve_left hroot
      by_cases hterm : E.terminal current.state
      · have hmass : E.subtreeMass certificate base root current = 0 := by
          rw [subtreeMass, E.historyBackwardLaw_of_terminal hterm, PMF.toOuterMeasure_pure_apply]
          simp [hnot]
        rw [hmass, zero_mul, zero_mul, add_zero, add_zero, E.historyBackwardLaw_of_terminal hterm,
          E.historyBackwardLaw_of_terminal hterm]
      · let chosen := base current hterm
        have hchosen : combined current hterm = chosen := houtside current hnot hterm
        have hcombined := E.historyBackwardLaw_of_not_terminal_of_chooser_eq
          (certificate := certificate) hterm chosen hchosen
        have hbase := E.historyBackwardLaw_of_not_terminal_of_chooser_eq
          (certificate := certificate) (chooser := base) hterm chosen rfl
        have hmass : E.subtreeMass certificate base root current =
            ∑' reached, E.step current.state chosen reached *
              if hzero : E.step current.state chosen reached = 0 then 0
              else E.subtreeMass certificate base root
                (current.extend chosen.2 ((PMF.mem_support_iff _ _).2 hzero)) := by
          rw [subtreeMass, hbase, PMF.toOuterMeasure_bindOnSupport_apply]
          rfl
        rw [hmass, hcombined, hbase, PMF.bindOnSupport_apply, PMF.bindOnSupport_apply,
          ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add,
          ← ENNReal.tsum_add]
        refine tsum_congr fun reached => ?_
        by_cases hzero : E.step current.state chosen reached = 0
        · simp [hzero]
        · have hmem : reached ∈ (E.step current.state chosen).support :=
            (PMF.mem_support_iff _ _).2 hzero
          let child := current.extend chosen.2 hmem
          have hchild : child = root ∨ ¬ E.HistoryReaches root child := by
            by_cases hsame : child = root
            · exact Or.inl hsame
            · exact Or.inr fun hreach => hnot (historyReaches_of_extend hreach hsame)
          have hstep := ih child ⟨chosen.1, chosen.2, hmem⟩ hchild final
          simp only [hzero, dite_false]
          rw [mul_assoc, mul_assoc, ← mul_add, ← mul_add]
          exact congrArg _ hstep

end ExecutionProtocol

namespace InformationModel

variable [DecidableEq ι] (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-! ## Splicing a deviation below a subgame root -/

/-- An information state at which `who` acts at some nonterminal history
continuing `root`. -/
def IsInsideInfo (root : E.History) (who : ι) (info : M.InfoState who) : Prop :=
  ∃ later, E.HistoryReaches root later ∧ ¬ E.terminal later.state ∧
    E.active later.state who ∧ M.infoOf who later.trace = info

open Classical in
/-- Follow `inside` at the information states met below `root` and `outside`
everywhere else. -/
def splicePolicy (root : E.History) {who : ι} (inside outside : M.Policy who) :
    M.Policy who :=
  fun info => if M.IsInsideInfo root who info then inside info else outside info

/-- Below the root, the spliced deviation plays the whole deviation. -/
theorem historyChooser_splice_of_reaches (profile : Profile M.strategicSignature)
    {root : E.History} {who : ι} (deviation : M.Policy who) {later : E.History}
    (hreach : E.HistoryReaches root later) (hterm : ¬ E.terminal later.state) :
    M.historyChooser (Profile.update profile who
        (M.splicePolicy root deviation (profile who))) later hterm =
      M.historyChooser (Profile.update profile who deviation) later hterm := by
  apply Subtype.ext
  funext player
  change (Profile.update profile who (M.splicePolicy root deviation (profile who))
      player).act (M.infoOf player later.trace) =
    (Profile.update profile who deviation player).act (M.infoOf player later.trace)
  by_cases hplayer : player = who
  · subst player
    simp only [Profile.update_same]
    by_cases hactive : E.active later.state who
    · have hinside : M.IsInsideInfo root who (M.infoOf who later.trace) :=
        ⟨later, hreach, hterm, hactive, rfl⟩
      simp [splicePolicy, Policy.act, hinside]
    · have := M.subsingleton_choice_of_not_active later.trace hactive
      exact congrArg Subtype.val (Subsingleton.elim _ _)
  · simp only [Profile.update_of_ne _ _ hplayer]

/-- Outside a proper subgame, the spliced deviation plays the incumbent policy. -/
theorem historyChooser_splice_of_not_reaches (profile : Profile M.strategicSignature)
    {root : E.History} (hroot : M.IsSubgameRoot root) {who : ι} (deviation : M.Policy who)
    {later : E.History} (hnot : ¬ E.HistoryReaches root later)
    (hterm : ¬ E.terminal later.state) :
    M.historyChooser (Profile.update profile who
        (M.splicePolicy root deviation (profile who))) later hterm =
      M.historyChooser profile later hterm := by
  apply Subtype.ext
  funext player
  change (Profile.update profile who (M.splicePolicy root deviation (profile who))
      player).act (M.infoOf player later.trace) =
    (profile player).act (M.infoOf player later.trace)
  by_cases hplayer : player = who
  · subst player
    simp only [Profile.update_same]
    by_cases hactive : E.active later.state who
    · have houtside : ¬ M.IsInsideInfo root who (M.infoOf who later.trace) := by
        rintro ⟨inside, hinside, hinsideTerm, hinsideActive, hinfo⟩
        exact hnot (hroot who inside later hinside hinsideTerm hinsideActive hterm hactive hinfo)
      simp [splicePolicy, Policy.act, houtside]
    · have := M.subsingleton_choice_of_not_active later.trace hactive
      exact congrArg Subtype.val (Subsingleton.elim _ _)
  · simp only [Profile.update_of_ne _ _ hplayer]

/-! ## Subgame and root comparisons -/

/-- The well-founded terminal-history law of a pure profile from each history. -/
def historyPlay (certificate : E.WellFoundedHistories) :
    E.History → Profile M.strategicSignature → PMF E.History :=
  fun history profile => E.historyBackwardLaw certificate (M.historyChooser profile) history

/-- The probability that incumbent play from the start reaches `root`. -/
def rootReach (certificate : E.WellFoundedHistories) (profile : Profile M.strategicSignature)
    (root : E.History) : ℝ≥0∞ :=
  E.subtreeMass certificate (M.historyChooser profile) root E.initHistory

omit [DecidableEq ι] in
theorem rootReach_ne_top (certificate : E.WellFoundedHistories)
    (profile : Profile M.strategicSignature) (root : E.History) :
    M.rootReach certificate profile root ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (E.subtreeMass_le_one _ _ _ _)

/-- **Splice decomposition.** From the start of play, the spliced deviation's
law plus the reach of the root times the incumbent's subgame law equals the
incumbent's law plus the reach times the deviation's subgame law. -/
theorem historyPlay_splice_add (certificate : E.WellFoundedHistories)
    (profile : Profile M.strategicSignature) {root : E.History} (hroot : M.IsSubgameRoot root)
    {who : ι} (deviation : M.Policy who) (final : E.History) :
    M.historyPlay certificate E.initHistory
          (Profile.update profile who (M.splicePolicy root deviation (profile who))) final +
        M.rootReach certificate profile root *
          M.historyPlay certificate root profile final =
      M.historyPlay certificate E.initHistory profile final +
        M.rootReach certificate profile root *
          M.historyPlay certificate root (Profile.update profile who deviation) final := by
  have hstart : E.initHistory = root ∨ ¬ E.HistoryReaches root E.initHistory := by
    by_cases hsame : E.initHistory = root
    · exact Or.inl hsame
    · refine Or.inr fun ⟨fuel, hreach⟩ => hsame ?_
      have hle := hreach.trace_length_le
      have hzero : E.initHistory.trace.length = 0 := rfl
      exact hreach.eq_of_trace_length_eq (by omega)
  exact E.historyBackwardLaw_add_subtreeMass certificate
    (fun later hreach hterm => M.historyChooser_splice_of_reaches profile deviation hreach hterm)
    (fun later hnot hterm =>
      M.historyChooser_splice_of_not_reaches profile hroot deviation hnot hterm)
    E.initHistory hstart final

variable {Observation : Type*}

/-- The root comparison of one whole-policy deviation: the Nash family of the
terminal-history law. -/
def rootComparison (certificate : E.WellFoundedHistories) (observe : E.History → Observation)
    (profile : Profile M.strategicSignature) (who : ι) (deviation : M.Policy who) :
    IncentiveComparison Observation :=
  M.continuationComparison (M.historyPlay certificate) observe profile who
    (⟨E.initHistory, M.initHistory_isSubgameRoot⟩, deviation)

omit [DecidableEq ι] in
open Classical in
private theorem map_add_mul {μ ν : PMF E.History} (observe : E.History → Observation)
    (weight : ℝ≥0∞) (outcome : Observation) :
    μ.map observe outcome + weight * ν.map observe outcome =
      ∑' final, if outcome = observe final then μ final + weight * ν final else 0 := by
  rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine tsum_congr fun final => ?_
  split_ifs <;> simp

/-- **Localization.** A subgame comparison at a proper root is localized in
the root comparison of its spliced deviation, with weight the probability that
incumbent play reaches the root. -/
theorem continuationComparison_isLocalizedIn_rootComparison
    (certificate : E.WellFoundedHistories) (observe : E.History → Observation)
    (profile : Profile M.strategicSignature) {root : E.History} (hroot : M.IsSubgameRoot root)
    {who : ι} (deviation : M.Policy who) :
    (M.continuationComparison (M.historyPlay certificate) observe profile who
        (⟨root, hroot⟩, deviation)).IsLocalizedIn
      (M.rootComparison certificate observe profile who
        (M.splicePolicy root deviation (profile who)))
      (M.rootReach certificate profile root).toReal := by
  apply IncentiveComparison.isLocalizedIn_of_mass ENNReal.toReal_nonneg
  intro outcome
  rw [ENNReal.ofReal_toReal (M.rootReach_ne_top certificate profile root)]
  simp only [rootComparison, continuationComparison]
  rw [map_add_mul, map_add_mul]
  refine tsum_congr fun final => ?_
  split_ifs
  · exact (M.historyPlay_splice_add certificate profile hroot deviation final).symm
  · rfl

/-- The root comparisons are the subgame comparisons at the initial history:
subgame perfection refines Nash of the terminal-history law. -/
theorem implies_rootComparison (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation) (profile : Profile M.strategicSignature) :
    IncentiveComparison.Implies
      (M.continuationComparison (M.historyPlay certificate) observe profile)
      (M.rootComparison certificate observe profile) :=
  fun _ respected who _ => respected who _

/-- **The gap between subgame perfection and Nash.** For every utility,
subgame perfection is Nash together with the subgame comparisons at proper
roots that incumbent play does not reach. Comparisons at reached roots are
positive multiples of Nash comparisons. -/
theorem holds_continuation_iff [Finite Observation] (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation) (profile : Profile M.strategicSignature)
    (utility : Observation → ι → ℝ) :
    (∀ who deviation, (M.continuationComparison (M.historyPlay certificate) observe profile
        who deviation).Holds (utility · who)) ↔
      (∀ who deviation,
          (M.rootComparison certificate observe profile who deviation).Holds (utility · who)) ∧
        ∀ who (deviation : M.ContinuationDeviation M.strategicSignature who),
          M.rootReach certificate profile deviation.1.1 = 0 →
            (M.continuationComparison (M.historyPlay certificate) observe profile who
              deviation).Holds (utility · who) := by
  let _ : Fintype Observation := Fintype.ofFinite _
  constructor
  · intro holds
    exact ⟨M.implies_rootComparison certificate observe profile utility holds,
      fun who deviation _ => holds who deviation⟩
  · rintro ⟨hroot, hunreached⟩ who ⟨⟨root, proper⟩, deviation⟩
    by_cases hreach : M.rootReach certificate profile root = 0
    · exact hunreached who ⟨⟨root, proper⟩, deviation⟩ hreach
    · have hpositive : 0 < (M.rootReach certificate profile root).toReal :=
        ENNReal.toReal_pos hreach (M.rootReach_ne_top certificate profile root)
      exact ((M.continuationComparison_isLocalizedIn_rootComparison certificate observe profile
        proper deviation).holds_iff hpositive _).1 (hroot who _)

/-- **Coincidence at fully reaching profiles.** When incumbent play reaches
every proper subgame root with positive probability, Nash implies subgame
perfection for every utility, so the two concepts coincide. -/
theorem implies_continuation_of_reached [Fintype Observation]
    (certificate : E.WellFoundedHistories) (observe : E.History → Observation)
    (profile : Profile M.strategicSignature)
    (hreached : ∀ root, M.IsSubgameRoot root → M.rootReach certificate profile root ≠ 0) :
    IncentiveComparison.Implies (M.rootComparison certificate observe profile)
      (M.continuationComparison (M.historyPlay certificate) observe profile) :=
  fun utility hroot => (M.holds_continuation_iff certificate observe profile utility).2
    ⟨hroot, fun _ deviation hzero => absurd hzero (hreached _ deviation.1.2)⟩

/-- Subgame perfection is continuation Nash of the terminal-history law. -/
theorem isSubgamePerfect_iff_isContinuationNash (certificate : E.WellFoundedHistories)
    (profile : Profile M.strategicSignature) (utility : E.History → ι → ℝ) :
    M.IsSubgamePerfect certificate profile utility ↔
      M.IsContinuationNash (M.historyPlay certificate) profile utility := by
  rw [isContinuationNash_iff]
  unfold IsSubgamePerfect ExecutionProtocol.historyBackwardExtendedValue
  exact forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => ⟨fun ⟨hdev, hbase, hle⟩ => ⟨hbase, hdev, hle⟩,
      fun ⟨hbase, hdev, hle⟩ => ⟨hdev, hbase, hle⟩⟩

/-! ## The separating counterparts

When Nash does not imply subgame perfection, library games realize both
separations. The continuation of a failing subgame, as a one-shot game form,
has its equilibria implied by the source's subgame perfection but not by its
Nash equilibria; the failing subgame is unreached. The strategic form of the
whole game is implied, as a one-shot game, by exactly the Nash comparisons,
so compiling it back into the sequential game preserves Nash but not subgame
perfection. -/

/-- A continuation game as a one-shot game form over whole policies. -/
@[reducible]
def subgameForm (certificate : E.WellFoundedHistories) (root : E.History) : GameForm ι where
  sig := M.strategicSignature
  play := M.historyPlay certificate root

/-- Nash comparisons of a continuation game are the subgame comparisons at
its root. -/
theorem equilibriumComparison_subgameForm (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation) (profile : Profile M.strategicSignature)
    {root : E.History} (hroot : M.IsSubgameRoot root) (who : ι) (deviation : M.Policy who) :
    equilibriumComparison (M.subgameForm certificate root) (PMF.pure profile)
        (DeviationScheme.unilateralConstant _) observe who deviation =
      M.continuationComparison (M.historyPlay certificate) observe profile who
        (⟨root, hroot⟩, deviation) := by
  simp [equilibriumComparison, continuationComparison, GameForm.outcomeLaw,
    DeviationScheme.unilateralConstant_apply, PMF.pure_map]

/-- The strategic form's Nash comparisons are the root comparisons. -/
theorem equilibriumComparison_strategicForm (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation) (profile : Profile M.strategicSignature)
    (who : ι) (deviation : M.Policy who) :
    equilibriumComparison (M.subgameForm certificate E.initHistory) (PMF.pure profile)
        (DeviationScheme.unilateralConstant _) observe who deviation =
      M.rootComparison certificate observe profile who deviation :=
  M.equilibriumComparison_subgameForm certificate observe profile
    M.initHistory_isSubgameRoot who deviation

/-- **Descent fails through a continuation game.** If Nash does not imply
subgame perfection at a profile, some proper subgame is unreached and its
continuation game is a target whose equilibria are implied by subgame
perfection of the source but not by its Nash equilibria. -/
theorem exists_subgameForm_separating [Finite Observation]
    (certificate : E.WellFoundedHistories) (observe : E.History → Observation)
    (profile : Profile M.strategicSignature)
    (hfails : ¬ IncentiveComparison.Implies (M.rootComparison certificate observe profile)
      (M.continuationComparison (M.historyPlay certificate) observe profile)) :
    ∃ (root : E.History) (_hroot : M.IsSubgameRoot root),
      M.rootReach certificate profile root = 0 ∧
      IncentiveComparison.Implies
        (M.continuationComparison (M.historyPlay certificate) observe profile)
        (equilibriumComparison (M.subgameForm certificate root) (PMF.pure profile)
          (DeviationScheme.unilateralConstant _) observe) ∧
      ¬ IncentiveComparison.Implies (M.rootComparison certificate observe profile)
        (equilibriumComparison (M.subgameForm certificate root) (PMF.pure profile)
          (DeviationScheme.unilateralConstant _) observe) := by
  let _ : Fintype Observation := Fintype.ofFinite _
  simp only [IncentiveComparison.Implies, not_forall] at hfails
  obtain ⟨utility, hroot, who, ⟨⟨root, proper⟩, deviation⟩, hfail⟩ := hfails
  have hunreached : M.rootReach certificate profile root = 0 := by
    by_contra hreach
    have hpositive : 0 < (M.rootReach certificate profile root).toReal :=
      ENNReal.toReal_pos hreach (M.rootReach_ne_top certificate profile root)
    exact hfail (((M.continuationComparison_isLocalizedIn_rootComparison certificate observe
      profile proper deviation).holds_iff hpositive _).1 (hroot who _))
  refine ⟨root, proper, hunreached, fun utility' holds player replacement => ?_, fun hwitness => ?_⟩
  · exact (congrArg (fun comparison : IncentiveComparison Observation =>
      comparison.Holds (utility' · player)) (M.equilibriumComparison_subgameForm certificate
        observe profile proper player replacement)).mpr (holds player _)
  · exact hfail ((congrArg (fun comparison : IncentiveComparison Observation =>
      comparison.Holds (utility · who)) (M.equilibriumComparison_subgameForm certificate
        observe profile proper who deviation)).mp (hwitness utility hroot who deviation))

/-- **Ascent fails from the strategic form.** The strategic form, as a
one-shot game, is implied by exactly the root comparisons: compiling it into
the sequential game preserves Nash, and preserves subgame perfection only when
Nash already implies it. -/
theorem strategicForm_implies_iff (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation) (profile : Profile M.strategicSignature) :
    IncentiveComparison.Implies
        (equilibriumComparison (M.subgameForm certificate E.initHistory) (PMF.pure profile)
          (DeviationScheme.unilateralConstant _) observe)
        (M.rootComparison certificate observe profile) ∧
      (IncentiveComparison.Implies
          (equilibriumComparison (M.subgameForm certificate E.initHistory) (PMF.pure profile)
            (DeviationScheme.unilateralConstant _) observe)
          (M.continuationComparison (M.historyPlay certificate) observe profile) ↔
        IncentiveComparison.Implies (M.rootComparison certificate observe profile)
          (M.continuationComparison (M.historyPlay certificate) observe profile)) := by
  have hholds (utility : Observation → ι → ℝ) (who : ι) (deviation : M.Policy who) :
      (equilibriumComparison (M.subgameForm certificate E.initHistory) (PMF.pure profile)
          (DeviationScheme.unilateralConstant _) observe who deviation).Holds (utility · who) ↔
        (M.rootComparison certificate observe profile who deviation).Holds (utility · who) := by
    rw [M.equilibriumComparison_strategicForm certificate observe profile who deviation]
  refine ⟨fun utility holds who deviation => (hholds utility who deviation).1 (holds who _),
    ⟨fun himplies utility hroot => himplies utility fun who deviation =>
      (hholds utility who deviation).2 (hroot who _),
    fun himplies utility hroot => himplies utility fun who deviation =>
      (hholds utility who deviation).1 (hroot who _)⟩⟩

omit [DecidableEq ι] in
/-- Under a bounded horizon the terminal-history law is the bounded run, so
the strategic form is the library's compiled game form. -/
theorem historyPlay_eq_runFrom (certificate : E.WellFoundedHistories) {bound : ℕ}
    (bounded : E.BoundedHorizon bound) (history : E.History)
    (profile : Profile M.strategicSignature) :
    M.historyPlay certificate history profile = M.runFrom profile bound history :=
  E.historyBackwardLaw_eq_runHistoryFor (certificate := certificate)
    (E.stopsHistoryWithin_of_bound bounded (M.historyChooser profile) history)

end InformationModel

end GameTheory.Protocol
