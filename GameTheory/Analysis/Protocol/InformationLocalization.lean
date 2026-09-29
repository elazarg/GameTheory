/-
# Localizing sequential rationality at the root

At a decision information site the deviating player compares whole
replacement policies under its belief over the site's histories. Splice the
replacement into the incumbent policy at the information states met below the
site and keep the incumbent everywhere else. When those information states do
not recur outside the site's subtrees (as decision recall guarantees), the
splice is a legal behavioral policy, and its outcome law from the start of play
differs from the incumbent's by the reach-weighted sum of the site histories'
continuation differences. Under Bayes beliefs that sum is the site's mass times
the belief-weighted difference, so a sequential-rationality comparison at a site
of positive mass is a positive multiple of a Nash comparison of the behavioral
game. Sequential rationality adds to Nash only the comparisons at sites of mass
zero.

The mass identity is proved over the well-founded terminal-history law of an
arbitrary randomized chooser and an arbitrary antichain of roots.
-/

import GameTheory.Analysis.IncentiveHierarchy
import GameTheory.Analysis.Protocol.Incentives
import GameTheory.Analysis.Protocol.SubgameLocalization
import GameTheory.Protocol.BehavioralBayes
import GameTheory.Protocol.BehavioralTerminal
import GameTheory.Protocol.DecisionRecall

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability
open scoped ENNReal

universe uι us ua up uq uk

variable {ι : Type uι} {E : ExecutionProtocol.{uι, us, ua} ι}

/-- A mixture of identities of the decomposition shape is again one. The
extended-real sums are over the mixture's outcomes and over the roots. -/
private theorem mixture_add_tsum {γ ρ : Type*} (weight : γ → ℝ≥0∞)
    (first second : γ → ℝ≥0∞) (mass : γ → ρ → ℝ≥0∞) (base inside : ρ → ℝ≥0∞)
    (h : ∀ c, weight c ≠ 0 →
      first c + ∑' r, mass c r * base r = second c + ∑' r, mass c r * inside r) :
    ∑' c, weight c * first c + ∑' r, (∑' c, weight c * mass c r) * base r =
      ∑' c, weight c * second c + ∑' r, (∑' c, weight c * mass c r) * inside r := by
  have hswap (value : ρ → ℝ≥0∞) :
      ∑' r, (∑' c, weight c * mass c r) * value r =
        ∑' c, weight c * ∑' r, mass c r * value r := by
    simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
    exact ENNReal.tsum_comm
  rw [hswap, hswap, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine tsum_congr fun c => ?_
  by_cases hzero : weight c = 0
  · simp [hzero]
  · rw [← mul_add, ← mul_add, h c hzero]

namespace ExecutionProtocol

/-- Two histories with a common descendant are comparable. -/
theorem historyReaches_comparable {first second final : E.History}
    (hfirst : E.HistoryReaches first final) (hsecond : E.HistoryReaches second final) :
    E.HistoryReaches first second ∨ E.HistoryReaches second first := by
  obtain ⟨firstFuel, hfirstReach⟩ := hfirst
  obtain ⟨secondFuel, hsecondReach⟩ := hsecond
  rcases le_total first.trace.length second.trace.length with hle | hle
  · obtain ⟨ancestor, fuel, hlength, hancestor⟩ := E.exists_ancestor_of_le second hle
    have hsame := ReachesWithin.eq_start_of_same_length hfirstReach
      (hancestor.trans hsecondReach) hlength.symm
    exact Or.inl ⟨fuel, hsame ▸ hancestor⟩
  · obtain ⟨ancestor, fuel, hlength, hancestor⟩ := E.exists_ancestor_of_le first hle
    have hsame := ReachesWithin.eq_start_of_same_length hsecondReach
      (hancestor.trans hfirstReach) hlength.symm
    exact Or.inr ⟨fuel, hsame ▸ hancestor⟩

/-- Every terminal history in the support of a randomized law from a history is
reached from it. -/
theorem randomizedBackwardLaw_support_reaches {certificate : E.WellFoundedHistories}
    {chooser : E.RandomizedChooser} (start : E.History) :
    ∀ final ∈ (E.randomizedBackwardLaw certificate chooser start).support,
      E.HistoryReaches start final := by
  induction start using certificate.induction with
  | _ current ih =>
      intro final hfinal
      by_cases hterm : E.terminal current.state
      · rw [E.randomizedBackwardLaw_of_terminal hterm, PMF.support_pure,
          Set.mem_singleton_iff] at hfinal
        subst hfinal
        exact HistoryReaches.refl E _
      · rw [E.randomizedBackwardLaw_of_not_terminal hterm, PMF.mem_support_bind_iff] at hfinal
        obtain ⟨drawn, -, hdrawn⟩ := hfinal
        rw [PMF.mem_support_bindOnSupport_iff] at hdrawn
        obtain ⟨reached, realized, hmem⟩ := hdrawn
        exact HistoryReaches.step E drawn.2 realized
          (ih (current.extend drawn.2 realized) ⟨drawn.1, drawn.2, realized⟩ final hmem)

variable (E)

/-- The probability that play from `start` passes through `root`. -/
def coneMass (certificate : E.WellFoundedHistories) (chooser : E.RandomizedChooser)
    (root start : E.History) : ℝ≥0∞ :=
  (E.randomizedBackwardLaw certificate chooser start).toOuterMeasure
    {final | E.HistoryReaches root final}

variable {E}

/-- **Mass decomposition over an antichain of roots.** Let a combined chooser
follow a local chooser at every history continuing some root and a base
chooser everywhere else. From any root, or any history continuing no root, the
combined law plus the root-mass-weighted base laws at the roots equals the base
law plus the root-mass-weighted local laws at the roots. -/
theorem randomizedBackwardLaw_add_coneMass (certificate : E.WellFoundedHistories)
    {base inside combined : E.RandomizedChooser} (IsRoot : E.History → Prop)
    (hanti : ∀ first second, IsRoot first → IsRoot second →
      E.HistoryReaches first second → first = second)
    (hinside : ∀ later, (∃ root, IsRoot root ∧ E.HistoryReaches root later) →
      ∀ hterm, combined later hterm = inside later hterm)
    (houtside : ∀ later, (∀ root, IsRoot root → ¬ E.HistoryReaches root later) →
      ∀ hterm, combined later hterm = base later hterm) :
    ∀ start, (IsRoot start ∨ ∀ root, IsRoot root → ¬ E.HistoryReaches root start) →
      ∀ final,
        E.randomizedBackwardLaw certificate combined start final +
            ∑' root : {root // IsRoot root}, E.coneMass certificate base root start *
              E.randomizedBackwardLaw certificate base root final =
          E.randomizedBackwardLaw certificate base start final +
            ∑' root : {root // IsRoot root}, E.coneMass certificate base root start *
              E.randomizedBackwardLaw certificate inside root final := by
  classical
  intro start
  induction start using certificate.induction with
  | _ current ih =>
      intro hcurrent final
      rcases hcurrent with hroot | houter
      · have hlaw : E.randomizedBackwardLaw certificate combined current =
            E.randomizedBackwardLaw certificate inside current :=
          E.randomizedBackwardLaw_congr_of_reaches current fun later hreach =>
            hinside later ⟨current, hroot, hreach⟩
        have hmass (root : {root // IsRoot root}) :
            E.coneMass certificate base root current =
              if root.1 = current then 1 else 0 := by
          split_ifs with hsame
          · rw [coneMass, hsame, PMF.toOuterMeasure_apply_eq_one_iff]
            exact E.randomizedBackwardLaw_support_reaches current
          · rw [coneMass, PMF.toOuterMeasure_apply_eq_zero_iff]
            refine Set.disjoint_left.2 fun final hfinal hcone => hsame ?_
            rcases historyReaches_comparable hcone
                (E.randomizedBackwardLaw_support_reaches current final hfinal) with
              hforward | hbackward
            · exact hanti _ _ root.2 hroot hforward
            · exact (hanti _ _ hroot root.2 hbackward).symm
        have hother (value : E.History → ℝ≥0∞) (root : {root // IsRoot root})
            (hne : root ≠ ⟨current, hroot⟩) :
            E.coneMass certificate base root current * value root = 0 := by
          have hdiff : root.1 ≠ current := fun hsame => hne (Subtype.ext hsame)
          simp [hmass, hdiff]
        rw [tsum_eq_single ⟨current, hroot⟩
            (hother fun root => E.randomizedBackwardLaw certificate base root final),
          tsum_eq_single ⟨current, hroot⟩
            (hother fun root => E.randomizedBackwardLaw certificate inside root final),
          hmass, hlaw]
        simp only [↓reduceIte, one_mul]
        exact add_comm _ _
      · by_cases hterm : E.terminal current.state
        · have hmass (root : {root // IsRoot root}) :
              E.coneMass certificate base root current = 0 := by
            rw [coneMass, E.randomizedBackwardLaw_of_terminal hterm,
              PMF.toOuterMeasure_pure_apply]
            simp [houter root.1 root.2]
          simp only [hmass, zero_mul, tsum_zero, add_zero,
            E.randomizedBackwardLaw_of_terminal hterm]
        · have hchooser := houtside current houter hterm
          have hcombined := E.randomizedBackwardLaw_of_not_terminal (certificate := certificate)
            (chooser := combined) hterm
          rw [hchooser] at hcombined
          have hbase := E.randomizedBackwardLaw_of_not_terminal (certificate := certificate)
            (chooser := base) hterm
          have hmass (root : {root // IsRoot root}) :
              E.coneMass certificate base root current =
                ∑' drawn, base current hterm drawn *
                  ∑' reached, E.step current.state drawn reached *
                    if hzero : E.step current.state drawn reached = 0 then 0
                    else E.coneMass certificate base root
                      (current.extend drawn.2 ((PMF.mem_support_iff _ _).2 hzero)) := by
            rw [coneMass, hbase, PMF.toOuterMeasure_bind_apply]
            refine tsum_congr fun drawn => ?_
            rw [PMF.toOuterMeasure_bindOnSupport_apply]
            rfl
          simp only [hmass]
          rw [hcombined, hbase, PMF.bind_apply, PMF.bind_apply]
          refine mixture_add_tsum _ _ _ _ _ _ fun drawn _ => ?_
          rw [PMF.bindOnSupport_apply, PMF.bindOnSupport_apply]
          refine mixture_add_tsum _ _ _ _ _ _ fun reached hzero => ?_
          simp only [hzero, dite_false]
          have hmem : reached ∈ (E.step current.state drawn).support :=
            (PMF.mem_support_iff _ _).2 hzero
          let child := current.extend drawn.2 hmem
          have hchild : IsRoot child ∨ ∀ root, IsRoot root → ¬ E.HistoryReaches root child := by
            by_cases hisRoot : IsRoot child
            · exact Or.inl hisRoot
            · refine Or.inr fun root hroot hreach => ?_
              have hne : child ≠ root := fun hsame => hisRoot (hsame ▸ hroot)
              exact houter root hroot (historyReaches_of_extend hreach hne)
          exact ih child ⟨drawn.1, drawn.2, hmem⟩ hchild final

end ExecutionProtocol

namespace InformationModel

variable [Fintype ι] [DecidableEq ι] (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-! ## Splicing a deviation below an information site -/

/-- A history in a decision information site. -/
abbrev IsSiteHistory {who : ι} (site : M.InformationSite who) (history : E.History) : Prop :=
  M.infoOf who history.trace = site.1

omit [Fintype ι] [DecidableEq ι] in
theorem siteHistory_antichain {who : ι} {site : M.InformationSite who}
    (hanti : site.IsHistoryAntichain) :
    ∀ first second, M.IsSiteHistory site first → M.IsSiteHistory site second →
      E.HistoryReaches first second → first = second := by
  rintro first second hfirst hsecond ⟨fuel, hreach⟩
  cases hreach with
  | refl => rfl
  | step joint isLegal realized rest =>
      exact absurd rest (hanti ⟨first, hfirst⟩ ⟨second, hsecond⟩ joint isLegal _ realized _)

/-- The deviating player's information met below the site's histories does
not recur at histories outside their subtrees. -/
def IsClosedBelow {who : ι} (site : M.InformationSite who) : Prop :=
  ∀ inside outside : E.History,
    (∃ root, M.IsSiteHistory site root ∧ E.HistoryReaches root inside) →
    ¬ E.terminal inside.state → E.active inside.state who →
    ¬ E.terminal outside.state → E.active outside.state who →
    M.infoOf who inside.trace = M.infoOf who outside.trace →
    ∃ root, M.IsSiteHistory site root ∧ E.HistoryReaches root outside

/-- An information state at which the deviator acts below the site. -/
def IsBelowInfo {who : ι} (site : M.InformationSite who) (info : M.InfoState who) : Prop :=
  ∃ later, (∃ root, M.IsSiteHistory site root ∧ E.HistoryReaches root later) ∧
    ¬ E.terminal later.state ∧ E.active later.state who ∧ M.infoOf who later.trace = info

open Classical in
/-- Follow `inside` at the information states met below the site and `outside`
everywhere else. -/
def spliceBehavioral {who : ι} (site : M.InformationSite who)
    (inside outside : M.BehavioralPolicy who) : M.BehavioralPolicy who :=
  fun info => if M.IsBelowInfo site info then inside info else outside info

omit [Fintype ι] [DecidableEq ι] in
private theorem policy_eq_of_not_active {who : ι} (first second : M.BehavioralPolicy who)
    {later : E.History} (hactive : ¬ E.active later.state who) :
    first (M.infoOf who later.trace) = second (M.infoOf who later.trace) := by
  have := M.subsingleton_choice_of_not_active later.trace hactive
  let choice := (first (M.infoOf who later.trace)).support_nonempty.some
  exact (eq_pure_of_subsingleton _ choice).trans (eq_pure_of_subsingleton _ choice).symm

theorem randomizedChooser_splice_of_below (profile : Profile M.behavioralSignature)
    {who : ι} (site : M.InformationSite who) (deviation : M.BehavioralPolicy who)
    {later : E.History}
    (hbelow : ∃ root, M.IsSiteHistory site root ∧ E.HistoryReaches root later)
    (hterm : ¬ E.terminal later.state) :
    M.randomizedChooser (Profile.update (sig := M.behavioralSignature) profile who
        (M.spliceBehavioral site deviation (profile who))) later hterm =
      M.randomizedChooser (Profile.update (sig := M.behavioralSignature) profile who
        deviation) later hterm := by
  refine M.behavioralJoint_congr later.trace hterm fun player => ?_
  by_cases hplayer : player = who
  · subst player
    simp only [Profile.update_same]
    by_cases hactive : E.active later.state who
    · have hinside : M.IsBelowInfo site (M.infoOf who later.trace) :=
        ⟨later, hbelow, hterm, hactive, rfl⟩
      simp [spliceBehavioral, hinside]
    · exact M.policy_eq_of_not_active _ _ hactive
  · simp only [Profile.update_of_ne _ _ hplayer]

theorem randomizedChooser_splice_of_not_below (profile : Profile M.behavioralSignature)
    {who : ι} {site : M.InformationSite who} (hclosed : M.IsClosedBelow site)
    (deviation : M.BehavioralPolicy who) {later : E.History}
    (hnot : ∀ root, M.IsSiteHistory site root → ¬ E.HistoryReaches root later)
    (hterm : ¬ E.terminal later.state) :
    M.randomizedChooser (Profile.update (sig := M.behavioralSignature) profile who
        (M.spliceBehavioral site deviation (profile who))) later hterm =
      M.randomizedChooser profile later hterm := by
  refine M.behavioralJoint_congr later.trace hterm fun player => ?_
  by_cases hplayer : player = who
  · subst player
    simp only [Profile.update_same]
    by_cases hactive : E.active later.state who
    · have houtside : ¬ M.IsBelowInfo site (M.infoOf who later.trace) := by
        rintro ⟨inside, hinside, hinsideTerm, hinsideActive, hinfo⟩
        obtain ⟨root, hroot, hreach⟩ :=
          hclosed inside later hinside hinsideTerm hinsideActive hterm hactive hinfo
        exact hnot root hroot hreach
      simp [spliceBehavioral, houtside]
    · exact M.policy_eq_of_not_active _ _ hactive
  · simp only [Profile.update_of_ne _ _ hplayer]

/-! ## Behavioral root comparisons -/

variable {Observation : Type*}

/-- The Nash comparison of one whole behavioral deviation at the start of play. -/
def behavioralRootComparison (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation) (profile : Profile M.behavioralSignature)
    (who : ι) (deviation : M.BehavioralPolicy who) : IncentiveComparison Observation where
  prescribed := (M.runBehavioralTerminalFrom certificate profile E.initHistory).map observe
  alternative := (M.runBehavioralTerminalFrom certificate
    (Profile.update (sig := M.behavioralSignature) profile who deviation)
      E.initHistory).map observe

/-- **Splice decomposition at a site.** -/
theorem runBehavioralTerminalFrom_splice_add (certificate : E.WellFoundedHistories)
    (profile : Profile M.behavioralSignature) {who : ι} {site : M.InformationSite who}
    (hanti : site.IsHistoryAntichain) (hclosed : M.IsClosedBelow site)
    (deviation : M.BehavioralPolicy who) (final : E.History) :
    M.runBehavioralTerminalFrom certificate
        (Profile.update (sig := M.behavioralSignature) profile who
          (M.spliceBehavioral site deviation (profile who))) E.initHistory final +
        ∑' root : M.InformationHistory who site.1,
          E.coneMass certificate (M.randomizedChooser profile) root E.initHistory *
            M.runBehavioralTerminalFrom certificate profile root final =
      M.runBehavioralTerminalFrom certificate profile E.initHistory final +
        ∑' root : M.InformationHistory who site.1,
          E.coneMass certificate (M.randomizedChooser profile) root E.initHistory *
            M.runBehavioralTerminalFrom certificate
              (Profile.update (sig := M.behavioralSignature) profile who deviation) root final := by
  have hstart : M.IsSiteHistory site E.initHistory ∨
      ∀ root, M.IsSiteHistory site root → ¬ E.HistoryReaches root E.initHistory := by
    by_cases hsite : M.IsSiteHistory site E.initHistory
    · exact Or.inl hsite
    · refine Or.inr fun root hroot ⟨fuel, hreach⟩ => hsite ?_
      have hle := hreach.trace_length_le
      have hzero : E.initHistory.trace.length = 0 := rfl
      rw [hreach.eq_of_trace_length_eq (by omega)]
      exact hroot
  exact E.randomizedBackwardLaw_add_coneMass certificate (M.IsSiteHistory site)
    (M.siteHistory_antichain hanti)
    (fun later hbelow hterm => M.randomizedChooser_splice_of_below profile site deviation
      hbelow hterm)
    (fun later hnot hterm => M.randomizedChooser_splice_of_not_below profile hclosed deviation
      hnot hterm)
    E.initHistory hstart final

omit [DecidableEq ι] in
/-- A history's reach weight is the mass of terminal play passing through it. -/
theorem coneMass_eq_historyReachWeight (certificate : E.WellFoundedHistories)
    (profile : Profile M.behavioralSignature) (root : E.History) :
    E.coneMass certificate (M.randomizedChooser profile) root E.initHistory =
      M.historyReachWeight profile root := by
  classical
  rw [ExecutionProtocol.coneMass, E.randomizedBackwardLaw_eq_bind_runRandomizedFor certificate _
    root.trace.length, PMF.toOuterMeasure_bind_apply]
  have hprefix (prior : E.History)
      (hprior : prior ∈ (M.runBehavioral profile root.trace.length).support) :
      (E.randomizedBackwardLaw certificate (M.randomizedChooser profile) prior).toOuterMeasure
          {final | E.HistoryReaches root final} = if prior = root then 1 else 0 := by
    split_ifs with hsame
    · subst prior
      rw [PMF.toOuterMeasure_apply_eq_one_iff]
      exact E.randomizedBackwardLaw_support_reaches root
    · rw [PMF.toOuterMeasure_apply_eq_zero_iff]
      refine Set.disjoint_left.2 fun final hfinal hcone => hsame ?_
      obtain ⟨fuel, hpriorReach⟩ := E.randomizedBackwardLaw_support_reaches prior final hfinal
      obtain ⟨rootFuel, hrootReach⟩ := hcone
      have hdepth := M.runBehavioralFrom_reachesWithin profile root.trace.length
        E.initHistory prior hprior
      have hupper : prior.trace.length ≤ root.trace.length := by
        simpa [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length]
          using hdepth.trace_length_le_add
      have hlower : root.trace.length ≤ prior.trace.length := by
        rcases E.runRandomizedFor_terminal_or_length (M.randomizedChooser profile)
            root.trace.length E.initHistory prior hprior with hterminal | hlength
        · have hfinalEq : final = prior := hpriorReach.eq_of_terminal hterminal
          subst final
          exact hrootReach.trace_length_le
        · simpa [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length] using hlength
      exact ExecutionProtocol.ReachesWithin.eq_start_of_same_length hpriorReach hrootReach
        (Nat.le_antisymm hupper hlower)
  have hterm (prior : E.History) :
      M.runBehavioral profile root.trace.length prior *
          (E.randomizedBackwardLaw certificate (M.randomizedChooser profile) prior).toOuterMeasure
            {final | E.HistoryReaches root final} =
        if prior = root then M.runBehavioral profile root.trace.length prior else 0 := by
    by_cases hsupport : prior ∈ (M.runBehavioral profile root.trace.length).support
    · rw [hprefix prior hsupport]
      split_ifs <;> simp
    · have hzero := (PMF.apply_eq_zero_iff _ _).2 hsupport
      simp [hzero]
  change ∑' prior, M.runBehavioral profile root.trace.length prior * _ = _
  rw [tsum_congr hterm, tsum_ite_eq]
  rfl

/-! ## Localization of sequential rationality -/

omit [Fintype ι] [DecidableEq ι] in
open Classical in
private theorem map_add_mul {μ ν : PMF E.History} (observe : E.History → Observation)
    (weight : ℝ≥0∞) (outcome : Observation) :
    μ.map observe outcome + weight * ν.map observe outcome =
      ∑' final, if outcome = observe final then μ final + weight * ν final else 0 := by
  rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine tsum_congr fun final => ?_
  split_ifs <;> simp

/-- The site's mass times a Bayes belief-weighted continuation law is the
reach-weighted sum of the site histories' continuation laws. -/
theorem informationMass_mul_assessmentLaw (certificate : E.WellFoundedHistories)
    (A : M.BehavioralAssessment) {who : ι}
    (site : M.InformationSite who) (hanti : site.IsHistoryAntichain)
    (hmass : 0 < M.informationMass A.strategy who site)
    (hbayes : BehavioralAssessment.IsBayesConsistentAt M A who site hanti hmass)
    (policy : M.BehavioralPolicy who) (final : E.History) :
    M.informationMass A.strategy who site *
        M.assessmentLaw certificate A site policy final =
      ∑' root : M.InformationHistory who site.1,
        E.coneMass certificate (M.randomizedChooser A.strategy) root E.initHistory *
          M.runBehavioralTerminalFrom certificate
            (Profile.update (sig := M.behavioralSignature) A.strategy who policy) root final := by
  have hfinite : M.informationMass A.strategy who site ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (M.informationMass_le_one A.strategy who site hanti)
      ENNReal.one_lt_top)
  rw [assessmentLaw, assessmentLawWith, PMF.bind_apply, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun root => ?_
  rw [hbayes root, ← mul_assoc, ENNReal.mul_div_cancel hmass.ne' hfinite,
    M.coneMass_eq_historyReachWeight certificate]

/-- **Localization at an information site.** Under Bayes beliefs at a site of
positive mass whose deviator information is closed below it, a
sequential-rationality comparison is localized in the Nash comparison of the
spliced deviation, with weight the site's mass. -/
theorem assessmentComparison_isLocalizedIn (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation)
    (A : M.BehavioralAssessment) {who : ι} (site : M.InformationSite who)
    (hanti : site.IsHistoryAntichain) (hclosed : M.IsClosedBelow site)
    (hmass : 0 < M.informationMass A.strategy who site)
    (hbayes : BehavioralAssessment.IsBayesConsistentAt M A who site hanti hmass)
    (policy : M.BehavioralPolicy who) :
    (M.assessmentComparison certificate observe A who (site, policy)).IsLocalizedIn
      (M.behavioralRootComparison certificate observe A.strategy who
        (M.spliceBehavioral site policy (A.strategy who)))
      (M.informationMass A.strategy who site).toReal := by
  have hfinite : M.informationMass A.strategy who site ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (M.informationMass_le_one A.strategy who site hanti)
      ENNReal.one_lt_top)
  apply IncentiveComparison.isLocalizedIn_of_mass ENNReal.toReal_nonneg
  intro outcome
  rw [ENNReal.ofReal_toReal hfinite]
  simp only [behavioralRootComparison, assessmentComparison_prescribed,
    assessmentComparison_alternative]
  rw [map_add_mul, map_add_mul]
  refine tsum_congr fun final => ?_
  split_ifs
  · have hsplice := M.runBehavioralTerminalFrom_splice_add certificate A.strategy hanti hclosed
      policy final
    rw [M.informationMass_mul_assessmentLaw certificate A site hanti hmass hbayes,
      M.informationMass_mul_assessmentLaw certificate A site hanti hmass hbayes]
    simp only [Profile.update_eq_self] at hsplice ⊢
    exact hsplice.symm
  · rfl

/-- **Nash plus the unreached sites is sequential rationality.** For a Bayes
consistent assessment whose deviator information is closed below every site,
a utility satisfying every behavioral Nash comparison and every
sequential-rationality comparison at sites of mass zero satisfies every
sequential-rationality comparison. -/
theorem holds_assessment_of_root [Fintype Observation] (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation)
    (A : M.BehavioralAssessment) (hanti : M.DecisionInformationAntichain)
    (hclosed : ∀ who (site : M.InformationSite who), M.IsClosedBelow site)
    (hbayes : BehavioralAssessment.IsBayesConsistent M A hanti)
    (utility : Observation → ι → ℝ)
    (hroot : ∀ who deviation, (M.behavioralRootComparison certificate observe A.strategy who
      deviation).Holds (utility · who))
    (hunreached : ∀ who (deviation : M.AssessmentDeviation who),
      M.informationMass A.strategy who deviation.1 = 0 →
        (M.assessmentComparison certificate observe A who deviation).Holds
          (utility · who)) :
    ∀ who deviation,
      (M.assessmentComparison certificate observe A who deviation).Holds
        (utility · who) := by
  rintro who ⟨site, policy⟩
  by_cases hzero : M.informationMass A.strategy who site = 0
  · exact hunreached who (site, policy) hzero
  · have hmass : 0 < M.informationMass A.strategy who site := pos_iff_ne_zero.2 hzero
    have hfinite : M.informationMass A.strategy who site ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (M.informationMass_le_one A.strategy who site (hanti who site))
        ENNReal.one_lt_top)
    exact ((M.assessmentComparison_isLocalizedIn certificate observe A site
      (hanti who site) (hclosed who site) hmass (hbayes who site hmass) policy).holds_iff
        (ENNReal.toReal_pos hzero hfinite) _).1 (hroot who _)

/-- **Coincidence at fully reached sites.** When every decision information
site has positive mass, behavioral Nash implies sequential rationality for
every utility. -/
theorem implies_assessment_of_positive [Fintype Observation] (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation)
    (A : M.BehavioralAssessment) (hanti : M.DecisionInformationAntichain)
    (hclosed : ∀ who (site : M.InformationSite who), M.IsClosedBelow site)
    (hbayes : BehavioralAssessment.IsBayesConsistent M A hanti)
    (hpositive : ∀ who (site : M.InformationSite who), 0 < M.informationMass A.strategy who site) :
    IncentiveComparison.Implies (M.behavioralRootComparison certificate observe A.strategy)
      (M.assessmentComparison certificate observe A) :=
  fun utility hroot => M.holds_assessment_of_root certificate observe A hanti hclosed
    hbayes utility hroot fun who deviation hzero => absurd hzero (hpositive who deviation.1).ne'

/-! ## Decision recall closes information below a site -/

omit [Fintype ι] [DecidableEq ι] in
/-- Every entry of an own-play record was made at an ancestor with that
information state. -/
theorem exists_ancestor_of_mem_ownPlay (who : ι) :
    ∀ {state : E.State} (trace : E.Trace state) {entry : M.InfoState who × E.Action who},
      entry ∈ M.ownPlay who trace →
        ∃ ancestor : E.History, M.infoOf who ancestor.trace = entry.1 ∧
          E.HistoryReaches ancestor ⟨state, trace⟩
  | _, .start, _, hmem => by simp [InfoSignals.ownPlay] at hmem
  | _, .extend prior joint isLegal realized, entry, hmem => by
      have hstep : E.ReachesWithin 1 ⟨_, prior⟩ ⟨_, .extend prior joint isLegal realized⟩ :=
        .step joint isLegal realized (.refl 0 _)
      rw [InfoSignals.ownPlay_extend] at hmem
      cases hjoint : joint who with
      | none =>
          simp only [hjoint] at hmem
          obtain ⟨ancestor, hinfo, fuel, hreach⟩ := exists_ancestor_of_mem_ownPlay who prior hmem
          exact ⟨ancestor, hinfo, fuel + 1, hreach.trans hstep⟩
      | some action =>
          simp only [hjoint, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · exact ⟨⟨_, prior⟩, rfl, 1, hstep⟩
          · obtain ⟨ancestor, hinfo, fuel, hreach⟩ :=
              exists_ancestor_of_mem_ownPlay who prior hmem
            exact ⟨ancestor, hinfo, fuel + 1, hreach.trans hstep⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **Decision recall closes information below every site.** -/
theorem isClosedBelow_of_decisionRecall (hrecall : M.DecisionRecall) {who : ι}
    (site : M.InformationSite who) : M.IsClosedBelow site := by
  rintro inside outside ⟨root, hroot, fuel, hreach⟩ hinsideTerm hinsideActive _ _ hinfo
  obtain ⟨insideSite, hinsideSite⟩ :=
    M.exists_informationSite_of_active who inside hinsideTerm hinsideActive
  have hown : M.ownPlay who inside.trace = M.ownPlay who outside.trace :=
    hrecall who insideSite ⟨inside, hinsideSite.symm⟩ ⟨outside, (hinfo.symm.trans hinsideSite.symm)⟩
  cases hreach with
  | refl => exact ⟨outside, hinfo.symm.trans hroot, ExecutionProtocol.HistoryReaches.refl E _⟩
  | step joint isLegal realized rest =>
      obtain ⟨_, _, action, haction⟩ := site.2
      have hmenu : some action ∈ M.menu who (M.infoOf who root.trace) := by
        rw [hroot]
        exact haction
      have hrootActive : E.active root.state who :=
        ((M.menu_adequate who root.trace (some action)).mp hmenu).1
      obtain ⟨chosen, hchosen⟩ := (E.legalOption_of_legal isLegal who).exists_eq_some_of_active
        (joint who) hrootActive
      have hentry : (M.infoOf who root.trace, chosen) ∈
          M.ownPlay who (root.extend isLegal realized).trace := by
        simp only [ExecutionProtocol.History.extend, InfoSignals.ownPlay_extend, hchosen,
          List.mem_cons, true_or]
      have hsuffix := M.ownPlay_isSuffix_of_reachesWithin who rest
      rw [hown] at hsuffix
      obtain ⟨ancestor, hancestor, hreachOutside⟩ :=
        M.exists_ancestor_of_mem_ownPlay who outside.trace (hsuffix.subset hentry)
      exact ⟨ancestor, hancestor.trans hroot, hreachOutside⟩

/-- **Coincidence under decision recall.** For a Bayes-consistent assessment in
a game with decision recall whose every decision site has positive mass,
behavioral Nash implies sequential rationality for every utility. -/
theorem implies_assessment_of_decisionRecall [Fintype Observation]
    (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation) (A : M.BehavioralAssessment)
    (hrecall : M.DecisionRecall)
    (hbayes : BehavioralAssessment.IsBayesConsistent M A (hrecall.decisionInformationAntichain))
    (hpositive : ∀ who (site : M.InformationSite who), 0 < M.informationMass A.strategy who site) :
    IncentiveComparison.Implies (M.behavioralRootComparison certificate observe A.strategy)
      (M.assessmentComparison certificate observe A) :=
  M.implies_assessment_of_positive certificate observe A
    (hrecall.decisionInformationAntichain)
    (fun _ site => M.isClosedBelow_of_decisionRecall hrecall site) hbayes hpositive

/-! ## Aggregation: sequential rationality implies Nash -/

omit [Fintype ι] [DecidableEq ι] in
/-- A nonempty own-play record was made at a strictly earlier nonterminal
ancestor at which the player was active. -/
theorem exists_acting_ancestor_of_mem_ownPlay (who : ι) :
    ∀ {state : E.State} (trace : E.Trace state) {entry : M.InfoState who × E.Action who},
      entry ∈ M.ownPlay who trace →
        ∃ ancestor : E.History, E.active ancestor.state who ∧ ¬ E.terminal ancestor.state ∧
          ancestor.trace.length < trace.length ∧ E.HistoryReaches ancestor ⟨state, trace⟩
  | _, .start, _, hmem => by simp [InfoSignals.ownPlay] at hmem
  | _, .extend prior joint isLegal realized, entry, hmem => by
      have hstep : E.ReachesWithin 1 ⟨_, prior⟩ ⟨_, .extend prior joint isLegal realized⟩ :=
        .step joint isLegal realized (.refl 0 _)
      rw [InfoSignals.ownPlay_extend] at hmem
      cases hjoint : joint who with
      | none =>
          simp only [hjoint] at hmem
          obtain ⟨ancestor, hactive, hterm, hlength, fuel, hreach⟩ :=
            exists_acting_ancestor_of_mem_ownPlay who prior hmem
          refine ⟨ancestor, hactive, hterm, ?_, fuel + 1, hreach.trans hstep⟩
          simp only [ExecutionProtocol.Trace.length]
          omega
      | some action =>
          have hlegal := E.legalOption_of_legal isLegal who
          rw [hjoint] at hlegal
          refine ⟨⟨_, prior⟩, hlegal.1, isLegal.1, ?_, 1, hstep⟩
          simp [ExecutionProtocol.Trace.length]

/-- A decision history at which the player has not acted before. -/
def IsInitialDecision (who : ι) (history : E.History) : Prop :=
  E.active history.state who ∧ M.ownPlay who history.trace = [] ∧
    ∃ site : M.InformationSite who, site.1 = M.infoOf who history.trace

omit [Fintype ι] [DecidableEq ι] in
theorem initialDecision_antichain (who : ι) :
    ∀ first second, M.IsInitialDecision who first → M.IsInitialDecision who second →
      E.HistoryReaches first second → first = second := by
  rintro first second ⟨hactive, -, -⟩ ⟨-, hempty, -⟩ ⟨fuel, hreach⟩
  cases hreach with
  | refl => rfl
  | step joint isLegal realized rest =>
      exfalso
      obtain ⟨action, haction⟩ :=
        (E.legalOption_of_legal isLegal who).exists_eq_some_of_active (joint who) hactive
      have hentry : (M.infoOf who first.trace, action) ∈
          M.ownPlay who (first.extend isLegal realized).trace := by
        simp [ExecutionProtocol.History.extend, InfoSignals.ownPlay_extend, haction]
      have hlater := (M.ownPlay_isSuffix_of_reachesWithin who rest).subset hentry
      rw [hempty] at hlater
      simp at hlater

omit [Fintype ι] [DecidableEq ι] in
/-- Every nonterminal history at which the player is active continues an
initial decision. -/
theorem exists_initialDecision_of_active (who : ι) :
    ∀ (depth : ℕ) (later : E.History), later.trace.length = depth →
      ¬ E.terminal later.state → E.active later.state who →
        ∃ root, M.IsInitialDecision who root ∧ E.HistoryReaches root later := by
  intro depth
  induction depth using Nat.strong_induction_on with
  | _ depth ih =>
      intro later hlength hterm hactive
      cases hplay : M.ownPlay who later.trace with
      | nil =>
          exact ⟨later, ⟨hactive, hplay,
            M.exists_informationSite_of_active who later hterm hactive⟩,
            ExecutionProtocol.HistoryReaches.refl E _⟩
      | cons entry rest =>
          have hmem : entry ∈ M.ownPlay who later.trace := by
            rw [hplay]
            exact List.mem_cons_self
          obtain ⟨ancestor, hancestorActive, hancestorTerm, hshorter, ancestorFuel,
            hancestorReach⟩ := M.exists_acting_ancestor_of_mem_ownPlay who later.trace hmem
          obtain ⟨root, hroot, rootFuel, hrootReach⟩ :=
            ih ancestor.trace.length (by omega) ancestor rfl hancestorTerm hancestorActive
          exact ⟨root, hroot, rootFuel + ancestorFuel, hrootReach.trans hancestorReach⟩

theorem randomizedChooser_update_of_not_initial (profile : Profile M.behavioralSignature)
    (who : ι) (deviation : M.BehavioralPolicy who) {later : E.History}
    (hnot : ∀ root, M.IsInitialDecision who root → ¬ E.HistoryReaches root later)
    (hterm : ¬ E.terminal later.state) :
    M.randomizedChooser (Profile.update (sig := M.behavioralSignature) profile who deviation)
        later hterm = M.randomizedChooser profile later hterm := by
  refine M.behavioralJoint_congr later.trace hterm fun player => ?_
  by_cases hplayer : player = who
  · subst player
    simp only [Profile.update_same]
    have hinactive : ¬ E.active later.state who := fun hactive => by
      obtain ⟨root, hroot, hreach⟩ :=
        M.exists_initialDecision_of_active who _ later rfl hterm hactive
      exact hnot root hroot hreach
    exact M.policy_eq_of_not_active _ _ hinactive
  · simp only [Profile.update_of_ne _ _ hplayer]

/-- **Decomposition over initial decisions.** -/
theorem runBehavioralTerminalFrom_update_add (certificate : E.WellFoundedHistories)
    (profile : Profile M.behavioralSignature) (who : ι) (deviation : M.BehavioralPolicy who)
    (final : E.History) :
    M.runBehavioralTerminalFrom certificate
        (Profile.update (sig := M.behavioralSignature) profile who
          deviation) E.initHistory final +
        ∑' root : {root // M.IsInitialDecision who root},
          E.coneMass certificate (M.randomizedChooser profile) root E.initHistory *
            M.runBehavioralTerminalFrom certificate profile root final =
      M.runBehavioralTerminalFrom certificate profile E.initHistory final +
        ∑' root : {root // M.IsInitialDecision who root},
          E.coneMass certificate (M.randomizedChooser profile) root E.initHistory *
            M.runBehavioralTerminalFrom certificate
              (Profile.update (sig := M.behavioralSignature) profile who deviation) root final := by
  have hstart : M.IsInitialDecision who E.initHistory ∨
      ∀ root, M.IsInitialDecision who root → ¬ E.HistoryReaches root E.initHistory := by
    by_cases hinit : M.IsInitialDecision who E.initHistory
    · exact Or.inl hinit
    · refine Or.inr fun root hroot ⟨fuel, hreach⟩ => hinit ?_
      have hle := hreach.trace_length_le
      have hzero : E.initHistory.trace.length = 0 := rfl
      rw [hreach.eq_of_trace_length_eq (by omega)]
      exact hroot
  exact E.randomizedBackwardLaw_add_coneMass certificate (M.IsInitialDecision who)
    (M.initialDecision_antichain who) (fun _ _ _ => rfl)
    (fun later hnot hterm => M.randomizedChooser_update_of_not_initial profile who deviation
      hnot hterm)
    E.initHistory hstart final

omit [Fintype ι] [DecidableEq ι] in
/-- Roots forming an antichain carry total mass at most one. -/
theorem tsum_coneMass_le_one (certificate : E.WellFoundedHistories) (chooser : E.RandomizedChooser)
    (IsRoot : E.History → Prop)
    (hanti : ∀ first second, IsRoot first → IsRoot second →
      E.HistoryReaches first second → first = second) (start : E.History) :
    ∑' root : {root // IsRoot root}, E.coneMass certificate chooser root start ≤ 1 := by
  classical
  simp only [ExecutionProtocol.coneMass, PMF.toOuterMeasure_apply]
  rw [ENNReal.tsum_comm]
  calc
    _ ≤ ∑' final, E.randomizedBackwardLaw certificate chooser start final := by
      refine ENNReal.tsum_le_tsum fun final => ?_
      by_cases hsome : ∃ root : {root // IsRoot root}, E.HistoryReaches root final
      · obtain ⟨root, hroot⟩ := hsome
        rw [tsum_eq_single root fun other hother => Set.indicator_of_notMem (fun hreach =>
          hother (Subtype.ext ?_)) _]
        · exact Set.indicator_le_self _ _ _
        · rcases ExecutionProtocol.historyReaches_comparable hreach hroot with hforward | hbackward
          · exact hanti _ _ other.2 root.2 hforward
          · exact (hanti _ _ root.2 other.2 hbackward).symm
      · push Not at hsome
        have hzero (root : {root // IsRoot root}) :
            {final | E.HistoryReaches root final}.indicator
              (E.randomizedBackwardLaw certificate chooser start) final = 0 :=
          Set.indicator_of_notMem (s := {final | E.HistoryReaches root final}) (hsome root) _
        rw [tsum_congr hzero, tsum_zero]
        exact bot_le
    _ = 1 := PMF.tsum_coe _

omit [Fintype ι] [DecidableEq ι] in
open Classical in
/-- Sums over initial decisions regroup by decision information site. -/
theorem tsum_initialDecision_eq (who : ι) (value : E.History → ℝ≥0∞) :
    ∑' root : {root // M.IsInitialDecision who root}, value root =
      ∑' site : M.InformationSite who, ∑' history : M.InformationHistory who site.1,
        if M.IsInitialDecision who history.1 then value history.1 else 0 := by
  classical
  rw [show (∑' root : {root // M.IsInitialDecision who root}, value root) =
      ∑' root, {root | M.IsInitialDecision who root}.indicator value root from
    tsum_subtype {root | M.IsInitialDecision who root} value]
  have hsite (site : M.InformationSite who) :
      ∑' history : M.InformationHistory who site.1,
          (if M.IsInitialDecision who history.1 then value history.1 else 0) =
        ∑' history : E.History,
          {history : E.History | M.infoOf who history.trace = site.1}.indicator
          (fun history => if M.IsInitialDecision who history then value history else 0)
            history :=
    tsum_subtype {history : E.History | M.infoOf who history.trace = site.1}
      (fun history => if M.IsInitialDecision who history then value history else 0)
  simp only [hsite]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun history => ?_
  by_cases hroot : M.IsInitialDecision who history
  · obtain ⟨_, _, rootSite, hrootSite⟩ := id hroot
    rw [tsum_eq_single rootSite fun other hother => Set.indicator_of_notMem (fun hinfo =>
      hother (Subtype.ext (hinfo.symm.trans hrootSite.symm))) _]
    simp [Set.indicator, hrootSite, hroot]
  · simp [Set.indicator, hroot]

omit [DecidableEq ι] in
/-- A reach weight is at most its site's mass. -/
theorem historyReachWeight_le_informationMass (A : M.BehavioralAssessment) {who : ι}
    (site : M.InformationSite who) (history : M.InformationHistory who site.1) :
    M.historyReachWeight A.strategy history.1 ≤ M.informationMass A.strategy who site :=
  ENNReal.le_tsum (f := fun history : M.InformationHistory who site.1 =>
    M.historyReachWeight A.strategy history.1) history

omit [Fintype ι] [DecidableEq ι] in
private theorem sum_map_mul [Fintype Observation] (law : PMF E.History)
    (observe : E.History → Observation) (weight : Observation → ℝ≥0∞) :
    ∑ outcome, law.map observe outcome * weight outcome =
      ∑' final, law final * weight (observe final) := by
  classical
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [← tsum_fintype (L := SummationFilter.unconditional _), ENNReal.tsum_comm]
  refine tsum_congr fun final => ?_
  rw [tsum_eq_single (observe final) fun outcome hne => by simp [hne]]
  simp

/-- **Sequential rationality implies Nash.** In a game with decision recall and
well-founded play, a Bayes-consistent assessment that is sequentially rational
for a utility is a behavioral Nash equilibrium for it: every whole-policy
deviation's root comparison is the mass-weighted sum of the comparisons at the
player's initial decision sites. -/
theorem holds_root_of_assessment [Fintype Observation] (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation)
    (A : M.BehavioralAssessment) (hrecall : M.DecisionRecall)
    (hbayes : BehavioralAssessment.IsBayesConsistent M A hrecall.decisionInformationAntichain)
    (utility : Observation → ι → ℝ)
    (hrational : ∀ who deviation,
      (M.assessmentComparison certificate observe A who deviation).Holds (utility · who)) :
    ∀ who deviation, (M.behavioralRootComparison certificate observe A.strategy who
      deviation).Holds (utility · who) := by
  classical
  intro who deviation
  have : Nonempty Observation :=
    ⟨((M.runBehavioralTerminalFrom certificate A.strategy E.initHistory).map
      observe).support_nonempty.some⟩
  obtain ⟨lowest, hlowest⟩ := Finite.exists_min fun outcome => utility outcome who
  let shifted : Observation → ℝ := fun outcome => utility outcome who - utility lowest who
  have hshifted : ∀ outcome, 0 ≤ shifted outcome := fun outcome => sub_nonneg.2 (hlowest outcome)
  have hshift (comparison : IncentiveComparison Observation) :
      comparison.Holds (utility · who) ↔ comparison.Holds shifted := by
    have h := comparison.holds_add_const shifted (utility lowest who)
    have hfun : (fun outcome => shifted outcome + utility lowest who) =
        fun outcome => utility outcome who := funext fun _ => sub_add_cancel _ _
    rw [hfun] at h
    exact h
  let weight : E.History → ℝ≥0∞ := fun final => ENNReal.ofReal (shifted (observe final))
  let value : PMF E.History → ℝ≥0∞ := fun law => ∑' final, law final * weight final
  have hvalue (law : PMF E.History) :
      ∑ outcome, law.map observe outcome * ENNReal.ofReal (shifted outcome) = value law :=
    sum_map_mul law observe _
  let deviated := Profile.update (sig := M.behavioralSignature) A.strategy who deviation
  let mass : E.History → ℝ≥0∞ := fun root =>
    E.coneMass certificate (M.randomizedChooser A.strategy) root E.initHistory
  -- the decomposition, integrated against the shifted utility
  have hidentity : value (M.runBehavioralTerminalFrom certificate deviated E.initHistory) +
      ∑' root : {root // M.IsInitialDecision who root},
        mass root * value (M.runBehavioralTerminalFrom certificate A.strategy root) =
      value (M.runBehavioralTerminalFrom certificate A.strategy E.initHistory) +
      ∑' root : {root // M.IsInitialDecision who root},
        mass root * value (M.runBehavioralTerminalFrom certificate deviated root) := by
    have hswap (law : E.History → PMF E.History) :
        ∑' root : {root // M.IsInitialDecision who root}, mass root * value (law root) =
          ∑' final, (∑' root : {root // M.IsInitialDecision who root},
            mass root * law root final) * weight final := by
      simp only [value, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right, mul_assoc]
      exact ENNReal.tsum_comm
    rw [hswap, hswap]
    simp only [value, ← ENNReal.tsum_add, ← add_mul]
    exact tsum_congr fun final => by
      rw [M.runBehavioralTerminalFrom_update_add certificate A.strategy who deviation final]
  -- each site's aggregated deviation value is at most its incumbent value
  have hsite (site : M.InformationSite who) :
      ∑' history : M.InformationHistory who site.1,
          (if M.IsInitialDecision who history.1 then
            mass history.1 *
              value (M.runBehavioralTerminalFrom certificate deviated history.1) else 0) ≤
        ∑' history : M.InformationHistory who site.1,
          (if M.IsInitialDecision who history.1 then
            mass history.1 *
              value (M.runBehavioralTerminalFrom certificate A.strategy history.1)
            else 0) := by
    by_cases hinitial : ∃ history : M.InformationHistory who site.1,
        M.IsInitialDecision who history.1
    · obtain ⟨witness, hwitness⟩ := hinitial
      have hall (history : M.InformationHistory who site.1) :
          M.IsInitialDecision who history.1 := by
        obtain ⟨_, _, action, haction⟩ := site.2
        have hmenu : some action ∈ M.menu who (M.infoOf who history.1.trace) := by
          rw [history.2]
          exact haction
        refine ⟨((M.menu_adequate who history.1.trace (some action)).mp hmenu).1, ?_,
          site, history.2.symm⟩
        rw [← hwitness.2.1]
        exact hrecall who site history witness
      simp only [hall, ↓reduceIte]
      have hmassEq (history : M.InformationHistory who site.1) :
          mass history.1 = M.historyReachWeight A.strategy history.1 :=
        M.coneMass_eq_historyReachWeight certificate A.strategy history.1
      by_cases hzero : M.informationMass A.strategy who site = 0
      · have hnull (history : M.InformationHistory who site.1) : mass history.1 = 0 := by
          rw [hmassEq]
          exact le_antisymm (hzero ▸ M.historyReachWeight_le_informationMass A site history)
            bot_le
        simp [hnull]
      · have hpositive : 0 < M.informationMass A.strategy who site := pos_iff_ne_zero.2 hzero
        have hanti := hrecall.decisionInformationAntichain who site
        have hbayesSite := hbayes who site hpositive
        have haggregate (policy : M.BehavioralPolicy who) :
            ∑' history : M.InformationHistory who site.1, mass history.1 *
                value (M.runBehavioralTerminalFrom certificate
                  (Profile.update (sig := M.behavioralSignature) A.strategy who policy)
                  history.1) =
              M.informationMass A.strategy who site *
                value (M.assessmentLaw certificate A site policy) := by
          simp only [value, ← ENNReal.tsum_mul_left]
          simp only [← mul_assoc]
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun final => ?_
          rw [ENNReal.tsum_mul_right, M.informationMass_mul_assessmentLaw certificate A
            site hanti hpositive hbayesSite policy final]
        have hincumbent := haggregate (A.strategy who)
        rw [Profile.update_eq_self] at hincumbent
        rw [haggregate deviation, hincumbent]
        refine mul_le_mul' le_rfl ?_
        have hholds := (hshift _).1 (hrational who (site, deviation))
        rw [IncentiveComparison.holds_iff_ennreal _ _ hshifted] at hholds
        simp only [assessmentComparison_prescribed, assessmentComparison_alternative,
          hvalue] at hholds
        exact hholds
    · push Not at hinitial
      simp [hinitial]
  have hle : ∑' root : {root // M.IsInitialDecision who root},
        mass root * value (M.runBehavioralTerminalFrom certificate deviated root) ≤
      ∑' root : {root // M.IsInitialDecision who root},
        mass root * value (M.runBehavioralTerminalFrom certificate A.strategy root) := by
    rw [M.tsum_initialDecision_eq who
        (fun root => mass root * value (M.runBehavioralTerminalFrom certificate deviated root)),
      M.tsum_initialDecision_eq who
        (fun root => mass root * value (M.runBehavioralTerminalFrom certificate A.strategy root))]
    exact ENNReal.tsum_le_tsum hsite
  -- the incumbent aggregate is finite
  let top : ℝ≥0∞ := ENNReal.ofReal (∑ outcome, shifted outcome)
  have hweight (final : E.History) : weight final ≤ top :=
    ENNReal.ofReal_le_ofReal (Finset.single_le_sum (fun outcome _ => hshifted outcome)
      (Finset.mem_univ _))
  have hvalueTop (law : PMF E.History) : value law ≤ top :=
    calc
      value law ≤ ∑' final, law final * top :=
        ENNReal.tsum_le_tsum fun final => mul_le_mul' le_rfl (hweight final)
      _ = top := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have hfinite : ∑' root : {root // M.IsInitialDecision who root},
      mass root * value (M.runBehavioralTerminalFrom certificate A.strategy root) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑ outcome, shifted outcome)) ?_
    calc
      _ ≤ ∑' root : {root // M.IsInitialDecision who root}, mass root * top :=
        ENNReal.tsum_le_tsum fun root => mul_le_mul' le_rfl (hvalueTop _)
      _ = (∑' root : {root // M.IsInitialDecision who root}, mass root) * top :=
        ENNReal.tsum_mul_right
      _ ≤ 1 * top := mul_le_mul' (tsum_coneMass_le_one certificate
        (M.randomizedChooser A.strategy) (M.IsInitialDecision who)
        (M.initialDecision_antichain who) E.initHistory) le_rfl
      _ = top := one_mul _
  rw [hshift, IncentiveComparison.holds_iff_ennreal _ _ hshifted]
  simp only [behavioralRootComparison, hvalue]
  have hsum := hidentity.le.trans (add_le_add le_rfl hle)
  exact (ENNReal.add_le_add_iff_right hfinite).1 hsum

/-- **Sequential rationality and Nash coincide at fully reached sites.** With
decision recall, well-founded play, and Bayes beliefs at every site of positive
mass, sequential rationality implies behavioral Nash for every utility; when
every decision site has positive mass the converse holds too. -/
theorem assessment_iff_root_of_positive [Fintype Observation] (certificate : E.WellFoundedHistories)
    (observe : E.History → Observation)
    (A : M.BehavioralAssessment) (hrecall : M.DecisionRecall)
    (hbayes : BehavioralAssessment.IsBayesConsistent M A hrecall.decisionInformationAntichain)
    (hpositive : ∀ who (site : M.InformationSite who), 0 < M.informationMass A.strategy who site) :
    IncentiveComparison.Implies (M.assessmentComparison certificate observe A)
        (M.behavioralRootComparison certificate observe A.strategy) ∧
      IncentiveComparison.Implies (M.behavioralRootComparison certificate observe A.strategy)
        (M.assessmentComparison certificate observe A) :=
  ⟨fun utility hrational => M.holds_root_of_assessment certificate observe A hrecall
      hbayes utility hrational,
    M.implies_assessment_of_decisionRecall certificate observe A hrecall hbayes hpositive⟩

end InformationModel

end GameTheory.Protocol
