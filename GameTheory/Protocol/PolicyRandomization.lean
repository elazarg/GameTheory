/-
# Randomization of information-local policies

This leaf module develops mixed-to-behavioral reading, finite-site predrawing,
and the realization theorems over the canonical information model.
-/

import GameTheory.Protocol.Information
import GameTheory.Protocol.HistoryPathMass
import GameTheory.Math.Probability.FiniteSampling
import GameTheory.Math.Probability.Conditioning

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability ExecutionProtocol

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace InformationModel

variable (M : InformationModel E)
/-! ### Reading a single draw back as local randomization

A mixed policy answers an information state once, so the local law it induces
there is the law of that answer *given* that the draw could have brought play to
that information state. The condition is a statement about the player's own
record, and recall is what makes that record a function of the information state
rather than of a particular history in it. -/

open Classical in
/-- The record a player's own moves leave at an information state, read off some
history that produces it. Which history is read does not matter under recall,
which is the theorem below; without recall this is merely some choice. -/
noncomputable def recordAt (i : ι) (info : M.InfoState i) :
    List (M.InfoState i × E.Action i) :=
  if hreached : ∃ h : E.History, M.infoOf i h.trace = info then
    M.ownPlay i (Classical.choose hreached).trace
  else []

/-- **What recall is for.** With it, the record at an information state is the
record along *every* history that produces it, so the arbitrary choice above is
no choice at all. -/
theorem recordAt_eq_ownPlay (hrecall : M.PerfectRecall) (i : ι) (h : E.History) :
    M.recordAt i (M.infoOf i h.trace) = M.ownPlay i h.trace := by
  have hreached : ∃ g : E.History, M.infoOf i g.trace = M.infoOf i h.trace := ⟨h, rfl⟩
  rw [recordAt, dite_eq_left hreached]
  exact hrecall i _ _ (Classical.choose_spec hreached)

/-- The pure policies whose own choices match a record of past moves. -/
def Consistent (i : ι) (record : List (M.InfoState i × E.Action i)) : Set (M.Policy i) :=
  { policy | ∀ step ∈ record, (policy step.1).1 = some step.2 }

/-- The pure policies that could have brought play to an information state. -/
def ConsistentAt (i : ι) (info : M.InfoState i) : Set (M.Policy i) :=
  M.Consistent i (M.recordAt i info)

/-- **What the recall direction actually needs.** Two histories a player cannot
tell apart constrain its policy the same way.

This is weaker than recall, and the gap is not an artefact: recall compares the
*records* two histories leave, while nothing downstream reads a record except
through the set of policies it rules out. A player that forgets the order of its
own past moves, or how many times it repeated one, still constrains its policy
identically — so it fails recall and satisfies this. -/
def ConstrainsAlike : Prop :=
  ∀ (i : ι) {first second : E.State} (traceFirst : Trace E first) (traceSecond : Trace E second),
    M.infoOf i traceFirst = M.infoOf i traceSecond →
      M.Consistent i (M.ownPlay i traceFirst) = M.Consistent i (M.ownPlay i traceSecond)

variable {M} in
/-- Recall is the special case that compares the records themselves. -/
theorem constrainsAlike_of_perfectRecall (hrecall : M.PerfectRecall) : M.ConstrainsAlike := by
  intro i _ _ traceFirst traceSecond hinfo
  rw [hrecall i traceFirst traceSecond hinfo]

variable {M} in
/-- **And the gap is real.** Records differing only in the order of a player's
own moves rule out the same policies, so a player that forgets the order fails
recall and still constrains alike. -/
theorem consistent_eq_of_perm {i : ι} {first second : List (M.InfoState i × E.Action i)}
    (hperm : first.Perm second) : M.Consistent i first = M.Consistent i second := by
  ext policy
  exact ⟨fun hpolicy step hstep => hpolicy step (hperm.mem_iff.mpr hstep),
    fun hpolicy step hstep => hpolicy step (hperm.mem_iff.mp hstep)⟩

variable {M} in
/-- Under it, the constraint attached to an information state is the constraint
along every history producing it — which is all the argument ever asks of the
arbitrary choice inside `recordAt`. -/
theorem consistentAt_eq_consistent_ownPlay (hconstrain : M.ConstrainsAlike) (i : ι)
    (h : E.History) :
    M.ConsistentAt i (M.infoOf i h.trace) = M.Consistent i (M.ownPlay i h.trace) := by
  have hreached : ∃ g : E.History, M.infoOf i g.trace = M.infoOf i h.trace := ⟨h, rfl⟩
  rw [ConsistentAt, recordAt, dite_eq_left hreached]
  exact hconstrain i _ _ (Classical.choose_spec hreached)

/-- A longer record is a stronger constraint. -/
theorem consistent_subset_of_isSuffix {i : ι}
    {shorter longer : List (M.InfoState i × E.Action i)} (hsuffix : shorter <:+ longer) :
    M.Consistent i longer ⊆ M.Consistent i shorter :=
  fun _ hpolicy step hstep => hpolicy step (hsuffix.subset hstep)

/-- **What a step commits the player to, for the rest of play.** Having answered
one information state, every policy still consistent with any later history
answers it the same way. -/
theorem consistentAt_subset_of_step (hconstrain : M.ConstrainsAlike) (i : ι) {h : E.History}
    {joint : ∀ j, Option (E.Action j)} (isLegal : E.Legal h.state joint)
    {target : E.State} (realized : target ∈ (E.step h.state ⟨joint, isLegal⟩).support)
    {action : E.Action i} (hjoint : joint i = some action)
    {fuel : ℕ} {later : E.History}
    (hreach : ExecutionProtocol.ReachesWithin E fuel (h.extend isLegal realized) later) :
    M.ConsistentAt i (M.infoOf i later.trace) ⊆
      { policy : M.Policy i | (policy (M.infoOf i h.trace)).1 = some action } := by
  intro policy hpolicy
  have hstep : (M.infoOf i h.trace, action) ∈
      M.ownPlay i (h.extend isLegal realized).trace := by
    show _ ∈ M.ownPlay i (Trace.extend _ joint isLegal realized)
    rw [InfoSignals.ownPlay_extend, hjoint]
    exact List.mem_cons_self
  rw [M.consistentAt_eq_consistent_ownPlay hconstrain i later] at hpolicy
  exact hpolicy _ ((M.ownPlay_isSuffix_of_reachesWithin i hreach).subset hstep)

variable {M} in
open Classical in
/-- A mixed policy read as a behavioral one: at each information state, the law
of the action it prescribes there, conditioned on the policies that could have
brought play to that information state.

Where no such policy has positive mass the conditioning is undefined, and the
reading falls back on a policy supplied for the purpose. A policy is the right
thing to fall back on: it already chooses legally at every information state,
including ones no history produces, where the menu law says nothing and the menu
could otherwise be empty.

The fallback is a parameter rather than a canonical choice because it must be
*stable*: an argument that conditions the law as play advances compares the
readings of a law and of that law conditioned, and a fallback read off the law's
own support would move when the support shrinks. Holding one fixed says the
reading is determined up to its behaviour where play never goes. -/
noncomputable def MixedPolicy.toBehavioralWith {i : ι} (mixed : M.MixedPolicy i)
    (fallback : M.Policy i) : M.BehavioralPolicy i := fun info =>
  if hreachable : ∃ policy ∈ M.ConsistentAt i info, policy ∈ mixed.support then
    PMF.map (fun policy => policy info) (mixed.filter (M.ConsistentAt i info) hreachable)
  else PMF.pure (fallback info)

variable {M} in
/-- The reading with nothing supplied: fall back on a policy the law itself gives
mass to. -/
noncomputable def MixedPolicy.toBehavioral {i : ι} (mixed : M.MixedPolicy i) :
    M.BehavioralPolicy i :=
  mixed.toBehavioralWith mixed.support_nonempty.choose

variable {M} in
/-- The degenerate case: a single draw that is not really random reads back as
the policy it draws. Both branches give that answer, so nothing here depends on
whether the information state was reachable at all. -/
theorem MixedPolicy.toBehavioral_pure {i : ι} (policy : M.Policy i) :
    MixedPolicy.toBehavioral (M := M) (PMF.pure policy) = policy.toBehavioral := by
  classical
  funext info
  rw [MixedPolicy.toBehavioral, MixedPolicy.toBehavioralWith]
  split
  · rename_i hreachable
    have ha : policy ∈ M.ConsistentAt i info := by
      obtain ⟨q, hq, hsupport⟩ := hreachable
      rw [PMF.mem_support_pure_iff] at hsupport
      subst q
      exact hq
    rw [filter_pure_of_mem policy _ ha, PMF.pure_map]
    rfl
  · have hchosen := (PMF.pure policy : M.MixedPolicy i).support_nonempty.choose_spec
    rw [PMF.mem_support_pure_iff] at hchosen
    rw [hchosen]
    rfl

variable {M} in
/-- Reading a deterministic policy with that same policy as the zero-mass
fallback recovers its pointwise deterministic behavioral policy. -/
theorem MixedPolicy.toBehavioralWith_pure_self {i : ι}
    (policy : M.Policy i) :
    MixedPolicy.toBehavioralWith (M := M) (PMF.pure policy) policy =
      policy.toBehavioral := by
  classical
  funext info
  rw [MixedPolicy.toBehavioralWith]
  split
  · rename_i hreachable
    have ha : policy ∈ M.ConsistentAt i info := by
      obtain ⟨q, hq, hsupport⟩ := hreachable
      rw [PMF.mem_support_pure_iff] at hsupport
      subst q
      exact hq
    rw [filter_pure_of_mem policy _ ha, PMF.pure_map]
    rfl
  · rfl

variable {M} in
/-- A behavioral policy as a mixed one: draw the action for every information
state in advance, independently. Whether the two laws agree is exactly the
question above, and this construction is where it is asked.

Scope: this draws for *every* information state, so it asks the player's
information states to be finite in number. Use `BehavioralPolicy.toMixedOn`
when only a supplied finite set should be predrawn, or the existential bounded
runner theorems below when the ambient information carrier may be infinite. -/
def BehavioralPolicy.toMixed {i : ι} [Fintype (M.InfoState i)]
    (policy : M.BehavioralPolicy i) : M.MixedPolicy i :=
  independentProduct policy

variable {M} in
/-- Predraw a behavioral policy on a supplied finite set of information states.
The fallback supplies a deterministic answer everywhere else. Unlike
`toMixed`, this operation does not require the ambient information-state
carrier to be finite. -/
def BehavioralPolicy.toMixedOn {i : ι} [DecidableEq (M.InfoState i)]
    (policy : M.BehavioralPolicy i) (sites : Finset (M.InfoState i))
    (fallback : M.Policy i) : M.MixedPolicy i :=
  FiniteAssignment.sampleOn policy sites fallback






variable {M} in
/-- The behavioral profile that has committed to one choice at one information
state and is unchanged elsewhere.

It is built from the same coordinate decomposition the product factorization
uses, rather than by updating a dependent function pointwise. That is not only
tidier: updating pointwise would transport a value along an equality of
information states, and this layer keeps such transports out. -/
def BehavioralPolicy.commit {i : ι} [DecidableEq (M.InfoState i)]
    (policy : M.BehavioralPolicy i) (info : M.InfoState i) (choice : M.Choice i info) :
    M.BehavioralPolicy i :=
  (Equiv.piSplitAt info fun w => PMF (M.Choice i w)).symm
    (PMF.pure choice, fun w => policy w.1)

variable {M} in
/-- The behavioral profile using a supplied law at one information state and
the original laws everywhere else.  Like `commit`, this uses the coordinate
split rather than a dependent pointwise update. -/
def BehavioralPolicy.withLaw {i : ι} [DecidableEq (M.InfoState i)]
    (policy : M.BehavioralPolicy i) (info : M.InfoState i)
    (law : PMF (M.Choice i info)) : M.BehavioralPolicy i :=
  (Equiv.piSplitAt info fun w => PMF (M.Choice i w)).symm
    (law, fun w => policy w.1)

variable {M} in
@[simp]
theorem BehavioralPolicy.commit_self {i : ι} [DecidableEq (M.InfoState i)]
    (policy : M.BehavioralPolicy i) (info : M.InfoState i) (choice : M.Choice i info) :
    policy.commit info choice info = PMF.pure choice := by
  simp [commit]

variable {M} in
@[simp]
theorem BehavioralPolicy.commit_of_ne {i : ι} [DecidableEq (M.InfoState i)]
    (policy : M.BehavioralPolicy i) (info : M.InfoState i) (choice : M.Choice i info)
    {other : M.InfoState i} (hne : other ≠ info) :
    policy.commit info choice other = policy other := by
  simp [commit, hne]

variable {M} in
@[simp]
theorem BehavioralPolicy.withLaw_self {i : ι} [DecidableEq (M.InfoState i)]
    (policy : M.BehavioralPolicy i) (info : M.InfoState i)
    (law : PMF (M.Choice i info)) :
    policy.withLaw info law info = law := by
  simp [withLaw]

variable {M} in
@[simp]
theorem BehavioralPolicy.withLaw_of_ne {i : ι} [DecidableEq (M.InfoState i)]
    (policy : M.BehavioralPolicy i) (info : M.InfoState i)
    (law : PMF (M.Choice i info))
    {other : M.InfoState i} (hne : other ≠ info) :
    policy.withLaw info law other = policy other := by
  simp [withLaw, hne]

variable {M} in
/-- Reinstalling a behavioral policy's own local law changes nothing. -/
theorem BehavioralPolicy.withLaw_eq_self {i : ι}
    [DecidableEq (M.InfoState i)]
    (policy : M.BehavioralPolicy i) (info : M.InfoState i) :
    policy.withLaw info (policy info) = policy := by
  funext other
  by_cases hsame : other = info
  · subst other
    rw [BehavioralPolicy.withLaw_self]
  · rw [BehavioralPolicy.withLaw_of_ne _ _ _ hsame]

variable {M} in
/-- A pure commitment at an information state forgets whichever law had just
been installed at that same state. -/
theorem BehavioralPolicy.withLaw_commit {i : ι}
    [DecidableEq (M.InfoState i)]
    (policy : M.BehavioralPolicy i) (info : M.InfoState i)
    (law : PMF (M.Choice i info)) (choice : M.Choice i info) :
    (policy.withLaw info law).commit info choice =
      policy.commit info choice := by
  funext other
  by_cases hsame : other = info
  · subst other
    rw [BehavioralPolicy.commit_self, BehavioralPolicy.commit_self]
  · rw [BehavioralPolicy.commit_of_ne _ _ _ hsame,
      BehavioralPolicy.commit_of_ne _ _ _ hsame,
      BehavioralPolicy.withLaw_of_ne _ _ _ hsame]

/-- The next local draw factors out of finite predrawing. If its site was omitted,
the off-site purity certificate supplies the deterministic draw. -/
theorem BehavioralPolicy.toMixedOn_factor {i : ι}
    [DecidableEq (M.InfoState i)]
    (policy : M.BehavioralPolicy i) (sites : Finset (M.InfoState i))
    (fallback : M.Policy i)
    (hfinite : ∀ info, info ∉ sites → policy info = PMF.pure (fallback info))
    (info : M.InfoState i) :
    policy.toMixedOn sites fallback =
      (policy info).bind (fun choice =>
        (policy.commit info choice).toMixedOn sites fallback) := by
  by_cases hinfo : info ∈ sites
  · exact FiniteAssignment.sampleOn_factor_of_mem policy sites fallback hinfo
      (fun choice => policy.commit info choice)
      (fun choice => policy.commit_self info choice)
      (fun choice other hne => policy.commit_of_ne info choice hne)
  · have hpure := hfinite info hinfo
    have hcommit : policy.commit info (fallback info) = policy := by
      funext other
      by_cases hsame : other = info
      · subst other
        rw [policy.commit_self, hpure]
      · exact policy.commit_of_ne info (fallback info) hsame
    rw [hpure, PMF.pure_bind, hcommit]




/-- **Committing keeps the profile mixed.** Re-extending the rest of a drawn
policy with a fixed choice at one information state is again the mixed reading
of a behavioral profile — the one that has committed there.

This is what lets an induction over play stay on full profiles: a coordinate
already consulted becomes a point mass rather than disappearing from the index,
and point masses need no bookkeeping. -/
theorem BehavioralPolicy.toMixed_commit {i : ι} [Fintype (M.InfoState i)]
    [DecidableEq (M.InfoState i)] (policy : M.BehavioralPolicy i) (info : M.InfoState i)
    (choice : M.Choice i info) :
    (policy.commit info choice).toMixed =
      PMF.map
        (fun rest => (Equiv.piSplitAt info fun w => M.Choice i w).symm (choice, rest))
        (independentProduct fun w : {w // w ≠ info} => policy w.1) := by
  rw [toMixed, independentProduct_splitAt]
  have hrest : (fun w : {w // w ≠ info} =>
      policy.commit info choice w.1) =
      (fun w : {w // w ≠ info} => policy w.1) :=
    funext fun w => policy.commit_of_ne info choice w.2
  rw [hrest, commit_self, PMF.pure_bind]

variable {M} in
/-- The construction is the right one in the degenerate case: a deterministic
policy, randomized nowhere, comes back as the point mass at itself. -/
theorem Policy.toBehavioral_toMixed {i : ι} [Fintype (M.InfoState i)]
    (policy : M.Policy i) :
    policy.toBehavioral.toMixed = PMF.pure policy :=
  independentProduct_pure policy

/-! ## When the two randomizations agree

Drawing at each information state and drawing once over policies give the same
law exactly when the single draw is never asked to answer twice. The proof
follows play: at each step the drawn policy is factored at the information
states about to be consulted, its first factor is matched against the local
draw, and the rest is re-read as a mixed profile that has committed there. The
commitment is then invisible, because the coordinate is never consulted again —
or, where the player does not move, because there was nothing to choose. -/

/-- Reassembling a policy from its value at one information state and its values
elsewhere returns that value there. -/
theorem piSplitAt_symm_self {i : ι} [DecidableEq (M.InfoState i)] (info : M.InfoState i)
    (q : M.Choice i info × ∀ w : {w // w ≠ info}, M.Choice i w.1) :
    (Equiv.piSplitAt info fun w => M.Choice i w).symm q info = q.1 := by
  simp

/-- Unfolding one step of deterministic play against a chooser value already
known. Naming the value keeps the rewrite out of the dependent position it would
otherwise land in. -/
theorem runFrom_succ_of_chooser_eq (policies : (i : ι) → M.Policy i) {h : E.History}
    (hterm : ¬ E.terminal h.state)
    (chosen : { joint : ∀ i, Option (E.Action i) // E.Legal h.state joint })
    (hchosen : M.historyChooser policies h hterm = chosen) (fuel : ℕ) :
    M.runFrom policies (fuel + 1) h =
      (E.step h.state chosen).bindOnSupport fun _ realized =>
        M.runFrom policies fuel (h.extend chosen.2 realized) := by
  subst hchosen
  rw [runFrom, ExecutionProtocol.runHistoryFor_succ_of_not_terminal _ fuel hterm]
  rfl

/-- A commitment made at one step is invisible from the next one on: either the
player never meets that information state again while moving, or it does not
move there and had nothing to choose. -/
theorem commit_agree_of_actsOnce [∀ i, DecidableEq (M.InfoState i)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (β : (i : ι) → M.BehavioralPolicy i) {h : E.History}
    (draw : (i : ι) → M.Choice i (M.infoOf i h.trace))
    {joint : ∀ i, Option (E.Action i)} (isLegal : E.Legal h.state joint)
    {target : E.State} (realized : target ∈ (E.step h.state ⟨joint, isLegal⟩).support)
    {fuel : ℕ} (later : E.History)
    (hreach : ExecutionProtocol.ReachesWithin E fuel (h.extend isLegal realized) later)
    (hlater : ¬ E.terminal later.state) (i : ι) :
    (β i).commit (M.infoOf i h.trace) (draw i) (M.infoOf i later.trace) =
      β i (M.infoOf i later.trace) := by
  by_cases hne : M.infoOf i later.trace ≠ M.infoOf i h.trace
  · exact BehavioralPolicy.commit_of_ne _ _ _ hne
  push Not at hne
  by_cases hactiveLater : E.active later.state i
  · by_cases hactiveHere : E.active h.state i
    · have hdisj : M.infoOf i later.trace ≠ M.infoOf i h.trace ∨
          Subsingleton (M.Choice i (M.infoOf i h.trace)) := by
        obtain ⟨laterJoint, hlaterJoint⟩ := E.progress later.state hlater
        have hlaterLegal : E.Legal later.state laterJoint := ⟨hlater, hlaterJoint⟩
        obtain ⟨laterTarget, hlaterRealized⟩ :=
          (E.step later.state ⟨laterJoint, hlaterLegal⟩).support_nonempty
        obtain ⟨_, hsome⟩ := LegalOption.exists_eq_some_of_active (joint i)
          (ExecutionProtocol.legalOption_of_legal isLegal i) hactiveHere
        obtain ⟨_, hlaterSome⟩ := LegalOption.exists_eq_some_of_active (laterJoint i)
          (ExecutionProtocol.legalOption_of_legal hlaterLegal i) hactiveLater
        exact M.infoOf_ne_or_subsingleton_of_actsOnce hactsOnce i isLegal realized
          (by rw [hsome]; rfl) hreach hlaterLegal hlaterRealized (by rw [hlaterSome]; rfl)
      rcases hdisj with hne' | hsubsingleton
      · exact absurd hne hne'
      · rw [hne, BehavioralPolicy.commit_self]
        exact (eq_pure_of_subsingleton _ (draw i)).symm
    · have : Subsingleton (M.Choice i (M.infoOf i h.trace)) :=
        M.subsingleton_choice_of_not_active h.trace hactiveHere
      rw [hne, BehavioralPolicy.commit_self]
      exact (eq_pure_of_subsingleton _ (draw i)).symm
  · exact M.behavioral_eq_of_not_active _ _ later.trace hactiveLater

/-! ### Finite partial predrawing -/

/-- A finite family of information sites covers every legal history that can
be reached from `start` within the supplied fuel. Unlike the support-local
construction below, this premise is independent of a particular policy and
therefore remains valid under unilateral deviations. -/
def CoversInformationSitesFrom
    (sites : (i : ι) → Finset (M.InfoState i))
    (fuel : ℕ) (start : E.History) : Prop :=
  ∀ later, E.ReachesWithin fuel start later →
    ¬ E.terminal later.state → ∀ i,
      M.infoOf i later.trace ∈ sites i

/-- Counterfactual finite-site coverage from the canonical initial history. -/
def CoversInformationSites
    (sites : (i : ι) → Finset (M.InfoState i)) (fuel : ℕ) : Prop :=
  M.CoversInformationSitesFrom sites fuel E.initHistory

/-- Information sites at nonterminal histories with positive probability at
some time up to the bounded horizon. Arbitrary PMF branching makes this a set,
not generally a finite set. -/
def behavioralSupportSitesFrom [Fintype ι]
    (policy : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ)
    (start : E.History) (i : ι) : Set (M.InfoState i) :=
  {info | ∃ elapsed ≤ fuel, ∃ later : E.History,
    later ∈ (M.runBehavioralFrom policy elapsed start).support ∧
      ¬ E.terminal later.state ∧ M.infoOf i later.trace = info}

theorem mem_behavioralSupportSitesFrom [Fintype ι]
    (policy : (i : ι) → M.BehavioralPolicy i) (fuel elapsed : ℕ)
    (helapsed : elapsed ≤ fuel) (start later : E.History)
    (hlater : later ∈ (M.runBehavioralFrom policy elapsed start).support)
    (hterm : ¬ E.terminal later.state) (i : ι) :
    M.infoOf i later.trace ∈
      M.behavioralSupportSitesFrom policy fuel start i :=
  ⟨elapsed, helapsed, later, hlater, hterm, rfl⟩

/-- Reachable behavioral information coordinates through a finite horizon
form a countable set, even when the chance and action carriers are infinite. -/
theorem behavioralSupportSitesFrom_countable [Fintype ι]
    (policy : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ)
    (start : E.History) (i : ι) :
    (M.behavioralSupportSitesFrom policy fuel start i).Countable := by
  have hcount : (⋃ elapsed : ℕ,
      (M.runBehavioralFrom policy elapsed start).support.image
        (fun h => M.infoOf i h.trace)).Countable := by
    apply Set.countable_iUnion
    intro elapsed
    exact (M.runBehavioralFrom policy elapsed start).support_countable.image _
  apply hcount.mono
  intro info hinfo
  obtain ⟨elapsed, _, later, hlater, _, rfl⟩ := hinfo
  exact Set.mem_iUnion.mpr ⟨elapsed, Set.mem_image_of_mem _ hlater⟩

/-- Under local full support, every nonterminal counterfactual history reached
within the horizon belongs to the support-site set. -/
theorem behavioralSupportSitesFrom_covers_of_fullSupport [Fintype ι]
    (policy : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ)
    (start : E.History)
    (hfull : ∀ i info (choice : M.Choice i info),
      choice ∈ (policy i info).support) :
    ∀ later, E.ReachesWithin fuel start later →
      ¬ E.terminal later.state → ∀ i,
        M.infoOf i later.trace ∈
          M.behavioralSupportSitesFrom policy fuel start i := by
  intro later hreach hterm i
  obtain ⟨elapsed, helapsed, hlater⟩ :=
    M.exists_mem_support_runBehavioralFrom_of_reachesWithin
      policy hfull hreach
  exact M.mem_behavioralSupportSitesFrom policy fuel elapsed helapsed
    start later hlater hterm i

/-- If every supported policy remains consistent with the current record,
the behavioral reading is the direct answer marginal. -/
theorem toBehavioralWith_eq_map_of_support_subset {i : ι}
    (mixed : M.MixedPolicy i) (fallback : M.Policy i)
    (info : M.InfoState i)
    (hsub : mixed.support ⊆ M.ConsistentAt i info) :
    mixed.toBehavioralWith fallback info =
      mixed.map (fun policy => policy info) := by
  classical
  obtain ⟨policy, hpolicy⟩ := mixed.support_nonempty
  rw [MixedPolicy.toBehavioralWith,
    dite_eq_left ⟨policy, hsub hpolicy, hpolicy⟩,
    filter_of_support_subset mixed _ _ hsub]

/-- The answer a drawn policy profile gives at one history. -/
def answerAt (h : E.History) (policies : (i : ι) → M.Policy i) :
    (i : ι) → M.Choice i (M.infoOf i h.trace) :=
  fun i => policies i (M.infoOf i h.trace)

/-- Player-specific policies answering a history as prescribed. -/
def AnsweredBy (h : E.History)
    (answer : (i : ι) → M.Choice i (M.infoOf i h.trace)) (i : ι) :
    Set (M.Policy i) :=
  {policy | policy (M.infoOf i h.trace) = answer i}

theorem answerAt_preimage_eq (h : E.History)
    (answer : (i : ι) → M.Choice i (M.infoOf i h.trace)) :
    M.answerAt h ⁻¹' {answer} =
      Set.pi Set.univ (M.AnsweredBy h answer) := by
  ext policies
  simp [answerAt, AnsweredBy, Set.mem_pi, funext_iff]

/-- Conditioning an independent policy profile on its joint answer filters
each player's policy law on that player's answer. -/
theorem filter_answerAt [Fintype ι]
    (mixed : (i : ι) → M.MixedPolicy i) (h : E.History)
    (answer : (i : ι) → M.Choice i (M.infoOf i h.trace))
    (hjoint : ∃ p ∈ M.answerAt h ⁻¹' {answer},
      p ∈ (independentProduct mixed).support)
    (hcoord : ∀ i, ∃ q ∈ M.AnsweredBy h answer i,
      q ∈ (mixed i).support) :
    (independentProduct mixed).filter
        (M.answerAt h ⁻¹' {answer}) hjoint =
      independentProduct (fun i =>
        (mixed i).filter (M.AnsweredBy h answer i) (hcoord i)) := by
  have hset := M.answerAt_preimage_eq h answer
  simpa only [← hset] using
    (filter_independentProduct mixed (M.AnsweredBy h answer)
      hcoord)

/-- Conditioning on the answer a step gave changes neither branch at a later history: where
consistent mass exists it survives the conditioning and the double conditioning
collapses, and where it does not, both readings fall back on the same policy. -/
theorem toBehavioralWith_condOn_answered (hconstrain : M.ConstrainsAlike) (i : ι) {h : E.History}
    {answer : (j : ι) → M.Choice j (M.infoOf j h.trace)}
    {joint : ∀ j, Option (E.Action j)} (isLegal : E.Legal h.state joint)
    (hanswer : ∀ j, joint j = (answer j).1)
    {target : E.State} (realized : target ∈ (E.step h.state ⟨joint, isLegal⟩).support)
    {action : E.Action i} (hact : joint i = some action)
    {fuel : ℕ} {later : E.History}
    (hreach : ExecutionProtocol.ReachesWithin E fuel (h.extend isLegal realized) later)
    (mixed : M.MixedPolicy i) (fallback : M.Policy i)
    (hmass : ∃ q ∈ M.AnsweredBy h answer i, q ∈ mixed.support) :
    MixedPolicy.toBehavioralWith (M := M) (mixed.filter (M.AnsweredBy h answer i) hmass)
        fallback (M.infoOf i later.trace) =
      mixed.toBehavioralWith fallback (M.infoOf i later.trace) := by
  classical
  have hnarrow : M.ConsistentAt i (M.infoOf i later.trace) ⊆ M.AnsweredBy h answer i := by
    intro policy hpolicy
    refine Subtype.ext ?_
    rw [M.consistentAt_subset_of_step hconstrain i isLegal realized hact hreach hpolicy,
      ← hanswer i, hact]
  simp only [MixedPolicy.toBehavioralWith]
  by_cases hex : ∃ policy ∈ M.ConsistentAt i (M.infoOf i later.trace), policy ∈ mixed.support
  · obtain ⟨policy, hpolicy, hmem⟩ := hex
    have hcond : ∃ p ∈ M.ConsistentAt i (M.infoOf i later.trace),
        p ∈ (mixed.filter (M.AnsweredBy h answer i) hmass).support :=
      ⟨policy, hpolicy,
        (PMF.mem_support_filter_iff hmass).2 ⟨hnarrow hpolicy, hmem⟩⟩
    rw [dite_eq_left hcond, dite_eq_left ⟨policy, hpolicy, hmem⟩,
      filter_filter_of_subset mixed _ _ hmass hcond hnarrow]
  · have hcond : ¬ ∃ p ∈ M.ConsistentAt i (M.infoOf i later.trace),
        p ∈ (mixed.filter (M.AnsweredBy h answer i) hmass).support := by
      rintro ⟨p, hp, hmem⟩
      exact hex ⟨p, hp, ((PMF.mem_support_filter_iff hmass).1 hmem).2⟩
    rw [dite_eq_right hcond, dite_eq_right hex]

/-- Conditioning on the answer changes nothing for a player that did not move:
its menu there was a single option, so every policy answered the same way. -/
theorem condOn_answeredBy_eq_self (i : ι) {h : E.History}
    {answer : (j : ι) → M.Choice j (M.infoOf j h.trace)}
    (hlegal : E.Legal h.state fun j => (answer j).1) (hidle : (answer i).1 = none)
    (mixed : M.MixedPolicy i) (hmass : ∃ q ∈ M.AnsweredBy h answer i, q ∈ mixed.support) :
    mixed.filter (M.AnsweredBy h answer i) hmass = mixed := by
  have hinactive : ¬ E.active h.state i := by
    have hopt := ExecutionProtocol.legalOption_of_legal hlegal i
    rw [hidle] at hopt
    exact hopt
  have := M.subsingleton_choice_of_not_active h.trace hinactive
  exact filter_of_support_subset mixed _ hmass
    (fun q _ => Subsingleton.elim _ _)

/-! ### Finite partial predrawing -/

/-- Finite predrawing agrees with behavioral play when laws outside the chosen
site sets are deterministic. Coordinate action carriers may be infinite. -/
theorem runMixedFrom_toMixedOn [Fintype ι] [∀ i, DecidableEq (M.InfoState i)]
    (hactsOnce : M.ActsOnceWhereItMatters) :
    ∀ (fuel : ℕ) (policy : (i : ι) → M.BehavioralPolicy i)
      (sites : (i : ι) → Finset (M.InfoState i))
      (fallback : (i : ι) → M.Policy i) (history : E.History),
      (∀ i info, info ∉ sites i →
        policy i info = PMF.pure (fallback i info)) →
      M.runMixedFrom
          (fun i => (policy i).toMixedOn (sites i) (fallback i))
          fuel history =
        M.runBehavioralFrom policy fuel history := by
  intro fuel
  induction fuel with
  | zero =>
    intro policy sites fallback history _
    exact PMF.bind_const _ _
  | succ fuel ih =>
    intro policy sites fallback history hfinite
    by_cases hterm : E.terminal history.state
    · rw [runMixedFrom, runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_of_terminal _ _ hterm]
      refine Eq.trans (bind_congr_on_support _ ?_) (PMF.bind_const _ _)
      intro policies _
      rw [runFrom, ExecutionProtocol.runHistoryFor_of_terminal _ _ hterm]
    · let info : (i : ι) → M.InfoState i :=
        fun i => M.infoOf i history.trace
      let committed : ((i : ι) → M.Choice i (info i)) →
          (i : ι) → M.BehavioralPolicy i :=
        fun draw i => (policy i).commit (info i) (draw i)
      have hfactor :
          independentProduct (fun i =>
            (policy i).toMixedOn (sites i) (fallback i)) =
          (independentProduct fun i => policy i (info i)).bind
            (fun draw => independentProduct (fun i =>
              (committed draw i).toMixedOn (sites i) (fallback i))) := by
        have hlocal : (fun i =>
            (policy i).toMixedOn (sites i) (fallback i)) =
            (fun i => (policy i (info i)).bind (fun choice =>
              ((policy i).commit (info i) choice).toMixedOn
                (sites i) (fallback i))) :=
          funext fun i => (policy i).toMixedOn_factor M (sites i)
            (fallback i) (hfinite i) (info i)
        rw [hlocal, ← independentProduct_bind]
      rw [runMixedFrom, hfactor, PMF.bind_bind,
        M.runBehavioralFrom_succ_of_not_terminal policy fuel hterm,
        behavioralJoint, PMF.bind_map]
      apply bind_congr_on_support
      intro draw hdraw
      let chosen :
          { joint : (i : ι) → Option (E.Action i) //
            E.Legal history.state joint } :=
        ⟨fun i => (draw i).1,
          ExecutionProtocol.legal_of_legalOption hterm fun i =>
            (M.menu_adequate i history.trace (draw i).1).mp
              (draw i).2⟩
      have hdrawi (i : ι) : draw i ∈ (policy i (info i)).support :=
        (independentProduct_support_iff (fun i => policy i (info i)) draw).1 hdraw i
      have hfinite' : ∀ i other, other ∉ sites i →
          committed draw i other = PMF.pure (fallback i other) := by
        intro i other hnot
        by_cases hsame : other = info i
        · subst other
          have hvalue : draw i = fallback i (info i) := by
            have hpure := hfinite i (info i) hnot
            have hs := hdrawi i
            rw [hpure] at hs
            simpa using hs
          rw [show committed draw i (info i) = PMF.pure (draw i) from
            (policy i).commit_self (info i) (draw i), hvalue]
        · exact (policy i).commit_of_ne (info i) (draw i) hsame |>.trans
            (hfinite i other hnot)
      have hchooser : ∀ policies ∈
          (independentProduct fun i =>
            (committed draw i).toMixedOn (sites i) (fallback i)).support,
          M.historyChooser policies history hterm = chosen := by
        intro policies hpolicies
        apply Subtype.ext
        funext i
        have hpoliciesi :=
          (independentProduct_support_iff
            (fun i => (committed draw i).toMixedOn (sites i) (fallback i))
            policies).1 hpolicies i
        have heval : ((committed draw i).toMixedOn (sites i) (fallback i)).map
            (fun p => p (info i)) = PMF.pure (draw i) := by
          by_cases hmem : info i ∈ sites i
          · rw [BehavioralPolicy.toMixedOn,
              FiniteAssignment.sampleOn_map_eval_of_mem _ _ _ hmem]
            exact (policy i).commit_self (info i) (draw i)
          · rw [BehavioralPolicy.toMixedOn,
              FiniteAssignment.sampleOn_map_eval_of_not_mem _ _ _ hmem]
            have hvalue : draw i = fallback i (info i) := by
              have hpure := hfinite i (info i) hmem
              have hs := hdrawi i
              rw [hpure] at hs
              simpa using hs
            rw [hvalue]
        have hmemEval : policies i (info i) ∈
            (((committed draw i).toMixedOn (sites i) (fallback i)).map
              (fun p => p (info i))).support :=
          (PMF.mem_support_map_iff _ _ _).2 ⟨policies i, hpoliciesi, rfl⟩
        rw [heval] at hmemEval
        have hvalue : policies i (info i) = draw i := by simpa using hmemEval
        exact congrArg Subtype.val hvalue
      have hstep :
          (independentProduct fun i =>
            (committed draw i).toMixedOn (sites i) (fallback i)).bind
              (fun policies => M.runFrom policies (fuel + 1) history) =
          (independentProduct fun i =>
            (committed draw i).toMixedOn (sites i) (fallback i)).bind
              (fun policies => (E.step history.state chosen).bindOnSupport
                fun _ realized =>
                  M.runFrom policies fuel (history.extend chosen.2 realized)) := by
        apply bind_congr_on_support
        intro policies hpolicies
        exact M.runFrom_succ_of_chooser_eq policies hterm chosen
          (hchooser policies hpolicies) fuel
      rw [hstep, bind_bindOnSupport_comm]
      apply bindOnSupport_congr
      intro target realized
      rw [show (independentProduct fun i =>
            (committed draw i).toMixedOn (sites i) (fallback i)).bind
          (fun policies => M.runFrom policies fuel
            (history.extend chosen.2 realized)) =
          M.runMixedFrom (fun i =>
            (committed draw i).toMixedOn (sites i) (fallback i)) fuel
            (history.extend chosen.2 realized) from rfl,
        ih (committed draw) sites fallback _ hfinite']
      apply M.runBehavioralFrom_congr fuel
      intro later hreach hlater i
      exact M.commit_agree_of_actsOnce hactsOnce policy draw chosen.2
        realized later hreach hlater i

/-- Choose one legal fallback answer from each local law. -/
noncomputable def BehavioralPolicy.supportFallback {i : ι}
    (policy : M.BehavioralPolicy i) : M.Policy i :=
  fun info => (policy info).support_nonempty.choose

/-- Keep local randomization at the selected sites and use a deterministic
fallback elsewhere. -/
noncomputable def BehavioralPolicy.restrictRandomization {i : ι}
    (policy : M.BehavioralPolicy i) (sites : Finset (M.InfoState i))
    (fallback : M.Policy i) : M.BehavioralPolicy i := by
  classical
  exact fun info => if info ∈ sites then policy info else PMF.pure (fallback info)

/-- Draw a behavioral policy at finitely many sites and fill all others with
the fallback policy. -/
noncomputable def BehavioralPolicy.toMixedWithin {i : ι}
    (policy : M.BehavioralPolicy i) (sites : Finset (M.InfoState i))
    (fallback : M.Policy i) : M.MixedPolicy i := by
  classical
  exact (policy.restrictRandomization M sites fallback).toMixedOn sites fallback

open Classical in
/-- Finite predrawing samples exactly the selected behavioral coordinates. -/
theorem BehavioralPolicy.toMixedWithin_eq_sampleOn {i : ι}
    (policy : M.BehavioralPolicy i) (sites : Finset (M.InfoState i))
    (fallback : M.Policy i) :
    policy.toMixedWithin M sites fallback =
      FiniteAssignment.sampleOn policy sites fallback := by
  classical
  have hlaws : (fun info : sites =>
      (policy.restrictRandomization M sites fallback) info) =
      (fun info : sites => policy info) := by
    funext info
    simp [BehavioralPolicy.restrictRandomization, info.2]
  simp only [BehavioralPolicy.toMixedWithin, BehavioralPolicy.toMixedOn,
    FiniteAssignment.sampleOn, hlaws]

/-- Finite predrawing of a deterministic policy returns its point mass. -/
theorem Policy.toBehavioral_toMixedWithin {i : ι}
    (policy : M.Policy i) (sites : Finset (M.InfoState i)) :
    policy.toBehavioral.toMixedWithin M sites policy = PMF.pure policy := by
  classical
  rw [BehavioralPolicy.toMixedWithin_eq_sampleOn]
  exact FiniteAssignment.sampleOn_pure policy sites

/-- Counterfactual finite-site coverage makes predrawing valid from any covered
history, including histories induced by deviations. -/
theorem runMixedFrom_toMixedWithin [Fintype ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (sites : (i : ι) → Finset (M.InfoState i))
    (policy : (i : ι) → M.BehavioralPolicy i)
    (fallback : (i : ι) → M.Policy i) (fuel : ℕ)
    (start : E.History)
    (hcover : M.CoversInformationSitesFrom sites fuel start) :
    M.runMixedFrom
        (fun i => (policy i).toMixedWithin M (sites i) (fallback i))
        fuel start =
      M.runBehavioralFrom policy fuel start := by
  classical
  let finitePolicy : (i : ι) → M.BehavioralPolicy i :=
    fun i => (policy i).restrictRandomization M (sites i) (fallback i)
  have hfinite : ∀ i info, info ∉ sites i →
      finitePolicy i info = PMF.pure (fallback i info) := by
    intro i info hinfo
    simp [finitePolicy, BehavioralPolicy.restrictRandomization, hinfo]
  refine (M.runMixedFrom_toMixedOn hactsOnce fuel finitePolicy
    sites fallback start hfinite).trans ?_
  apply M.runBehavioralFrom_congr
  intro later hreach hterm i
  have hmem := hcover later hreach hterm i
  simp [finitePolicy, BehavioralPolicy.restrictRandomization, hmem]

/-- A finite predraw agrees at one exact-depth target when its site sets
contain that target's queried coordinates. This needs no cover of other paths. -/
theorem runMixedFrom_toMixedWithin_apply_of_queriedInfos [Fintype ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (sites : (i : ι) → Finset (M.InfoState i))
    (policy : (i : ι) → M.BehavioralPolicy i)
    (fallback : (i : ι) → M.Policy i)
    (fuel : ℕ) (start target : E.History)
    (hdepth : target.trace.length = start.trace.length + fuel)
    (hcover : ∀ i info, info ∈ M.queriedInfos i target.trace → info ∈ sites i) :
    M.runMixedFrom
        (fun i => (policy i).toMixedWithin M (sites i) (fallback i))
        fuel start target =
      M.runBehavioralFrom policy fuel start target := by
  classical
  let finitePolicy : (i : ι) → M.BehavioralPolicy i :=
    fun i => (policy i).restrictRandomization M (sites i) (fallback i)
  have hfinite : ∀ i info, info ∉ sites i →
      finitePolicy i info = PMF.pure (fallback i info) := by
    intro i info hnot
    simp [finitePolicy, BehavioralPolicy.restrictRandomization, hnot]
  have hdraw : M.runMixedFrom
        (fun i => (policy i).toMixedWithin M (sites i) (fallback i))
        fuel start = M.runBehavioralFrom finitePolicy fuel start := by
    simpa only [BehavioralPolicy.toMixedWithin] using
      M.runMixedFrom_toMixedOn hactsOnce fuel finitePolicy sites fallback start hfinite
  have hlocal := M.runBehavioralFrom_apply_congr_of_queriedInfos
    finitePolicy policy fuel start target hdepth
    (by
      intro i info hmem
      simp [finitePolicy, BehavioralPolicy.restrictRandomization, hcover i info hmem])
  exact (congrArg (fun law : PMF E.History => law target) hdraw).trans hlocal

/-- From the initial history, the target's queried coordinates suffice for
finite predrawing at any fuel, including early terminal absorption. -/
theorem runMixed_toMixedWithin_apply_of_queriedInfos [Fintype ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (sites : (i : ι) → Finset (M.InfoState i))
    (policy : (i : ι) → M.BehavioralPolicy i)
    (fallback : (i : ι) → M.Policy i)
    (fuel : ℕ) (target : E.History)
    (hcover : ∀ i info, info ∈ M.queriedInfos i target.trace → info ∈ sites i) :
    M.runMixed
        (fun i => (policy i).toMixedWithin M (sites i) (fallback i))
        fuel target = M.runBehavioral policy fuel target := by
  classical
  let finitePolicy : (i : ι) → M.BehavioralPolicy i :=
    fun i => (policy i).restrictRandomization M (sites i) (fallback i)
  have hfinite : ∀ i info, info ∉ sites i →
      finitePolicy i info = PMF.pure (fallback i info) := by
    intro i info hnot
    simp [finitePolicy, BehavioralPolicy.restrictRandomization, hnot]
  have hdraw : M.runMixed
        (fun i => (policy i).toMixedWithin M (sites i) (fallback i))
        fuel = M.runBehavioral finitePolicy fuel := by
    simpa only [runMixed, runBehavioral, BehavioralPolicy.toMixedWithin] using
      M.runMixedFrom_toMixedOn hactsOnce fuel finitePolicy sites fallback
        E.initHistory hfinite
  have hlocal := M.runBehavioral_apply_congr_of_queriedInfos
    finitePolicy policy fuel target
    (by
      intro i info hmem
      simp [finitePolicy, BehavioralPolicy.restrictRandomization, hcover i info hmem])
  exact (congrArg (fun law : PMF E.History => law target) hdraw).trans hlocal

/-- Counterfactual finite-site realization from the initial history. -/
theorem runMixed_toMixedWithin [Fintype ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (sites : (i : ι) → Finset (M.InfoState i))
    (policy : (i : ι) → M.BehavioralPolicy i)
    (fallback : (i : ι) → M.Policy i) (fuel : ℕ)
    (hcover : M.CoversInformationSites sites fuel) :
    M.runMixed
        (fun i => (policy i).toMixedWithin M (sites i) (fallback i)) fuel =
      M.runBehavioral policy fuel :=
  M.runMixedFrom_toMixedWithin hactsOnce sites policy fallback fuel
    E.initHistory hcover

/-- A finite reachable-support certificate becomes a finite site cover under
full local support. -/
theorem behavioralSupportSitesFrom_finite_covers_of_fullSupport [Fintype ι]
    (policy : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ)
    (start : E.History)
    (hfinite : ∀ i, (M.behavioralSupportSitesFrom policy fuel start i).Finite)
    (hfull : ∀ i info (choice : M.Choice i info),
      choice ∈ (policy i info).support) :
    M.CoversInformationSitesFrom
      (fun i => (hfinite i).toFinset) fuel start := by
  intro later hreach hterm i
  exact (Set.Finite.mem_toFinset (hfinite i)).2
    (M.behavioralSupportSitesFrom_covers_of_fullSupport
      policy fuel start hfull later hreach hterm i)

/-- Finite reachable support sites suffice to realize one bounded behavioral
law as a mixed law without requiring a finite ambient information carrier. -/
theorem exists_mixed_runMixedFrom_eq_runBehavioralFrom [Fintype ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (policy : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ)
    (start : E.History)
    (hfinite : ∀ i, (M.behavioralSupportSitesFrom policy fuel start i).Finite) :
    ∃ mixed : (i : ι) → M.MixedPolicy i,
      M.runMixedFrom mixed fuel start =
        M.runBehavioralFrom policy fuel start := by
  classical
  let sites : (i : ι) → Finset (M.InfoState i) :=
    fun i => (hfinite i).toFinset
  let fallback : (i : ι) → M.Policy i :=
    fun i => (policy i).supportFallback M
  let finitePolicy : (i : ι) → M.BehavioralPolicy i :=
    fun i => (policy i).restrictRandomization M (sites i) (fallback i)
  refine ⟨fun i => (finitePolicy i).toMixedOn (sites i) (fallback i), ?_⟩
  have hoff : ∀ i info, info ∉ sites i →
      finitePolicy i info = PMF.pure (fallback i info) := by
    intro i info hinfo
    simp [finitePolicy, BehavioralPolicy.restrictRandomization, hinfo]
  refine (M.runMixedFrom_toMixedOn hactsOnce fuel finitePolicy
    sites fallback start hoff).trans ?_
  apply (M.runBehavioralFrom_congr_on_support fuel start ?_).symm
  intro elapsed helapsed later hlater hterm i
  have hmem : M.infoOf i later.trace ∈ sites i := by
    exact (Set.Finite.mem_toFinset (hfinite i)).2
      (M.mem_behavioralSupportSitesFrom policy fuel elapsed helapsed
        start later hlater hterm i)
  simp [finitePolicy, BehavioralPolicy.restrictRandomization, hmem]

/-- Initial-history form of finite reachable-support realization. -/
theorem exists_mixed_runMixed_eq_runBehavioral [Fintype ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (policy : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ)
    (hfinite : ∀ i,
      (M.behavioralSupportSitesFrom policy fuel E.initHistory i).Finite) :
    ∃ mixed : (i : ι) → M.MixedPolicy i,
      M.runMixed mixed fuel = M.runBehavioral policy fuel :=
  M.exists_mixed_runMixedFrom_eq_runBehavioralFrom
    hactsOnce policy fuel E.initHistory hfinite

/-- Full predrawing of every finite information-state carrier gives the same
bounded history law as local behavioral randomization. -/
theorem runMixedFrom_toMixed [Fintype ι]
    [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (fuel : ℕ) (policy : (i : ι) → M.BehavioralPolicy i)
    (start : E.History) :
    M.runMixedFrom (fun i => (policy i).toMixed) fuel start =
      M.runBehavioralFrom policy fuel start := by
  let sites : (i : ι) → Finset (M.InfoState i) := fun _ => Finset.univ
  let fallback : (i : ι) → M.Policy i :=
    fun i => (policy i).supportFallback M
  have hsame : (fun i => (policy i).toMixed) =
      (fun i => (policy i).toMixedOn (sites i) (fallback i)) := by
    funext i
    exact (FiniteAssignment.sampleOn_univ (policy i) (fallback i)).symm
  rw [hsame]
  exact M.runMixedFrom_toMixedOn hactsOnce fuel policy sites fallback start
    (fun i info hnot => (hnot (Finset.mem_univ info)).elim)

/-- Full finite-information predrawing from the initial history. -/
theorem runMixed_toMixed [Fintype ι]
    [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (policy : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ) :
    M.runMixed (fun i => (policy i).toMixed) fuel =
      M.runBehavioral policy fuel :=
  M.runMixedFrom_toMixed hactsOnce fuel policy E.initHistory

/-- Outcome-state laws agree because the history laws agree. -/
theorem map_state_runMixed_toMixed [Fintype ι]
    [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (policy : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ) :
    (M.runMixed (fun i => (policy i).toMixed) fuel).map
        ExecutionProtocol.History.state =
      (M.runBehavioral policy fuel).map ExecutionProtocol.History.state :=
  congrArg _ (M.runMixed_toMixed hactsOnce policy fuel)

theorem runMixedFrom_toBehavioralWith [Fintype ι]
    (hconstrain : M.ConstrainsAlike)
    (fallback : (i : ι) → M.Policy i) :
    ∀ (fuel : ℕ) (mixed : (i : ι) → M.MixedPolicy i) (h : E.History),
      (∀ i, (mixed i).support ⊆ M.ConsistentAt i (M.infoOf i h.trace)) →
      M.runMixedFrom mixed fuel h =
        M.runBehavioralFrom
          (fun i => (mixed i).toBehavioralWith (fallback i)) fuel h := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro mixed h _
    exact PMF.bind_const _ _
  | succ fuel ih =>
    intro mixed h hsub
    by_cases hterm : E.terminal h.state
    · rw [runMixedFrom, runBehavioralFrom,
        ExecutionProtocol.runRandomizedFor_of_terminal _ _ hterm]
      refine Eq.trans (bind_congr_on_support _ ?_) (PMF.bind_const _ _)
      intro policies _
      rw [runFrom, ExecutionProtocol.runHistoryFor_of_terminal _ _ hterm]
    · have hdraw : independentProduct (fun i =>
            (mixed i).toBehavioralWith (fallback i) (M.infoOf i h.trace)) =
          (independentProduct mixed).map (M.answerAt h) := by
        have hlocal : (fun i =>
            (mixed i).toBehavioralWith (fallback i) (M.infoOf i h.trace)) =
            (fun i => (mixed i).map
              (fun policy => policy (M.infoOf i h.trace))) :=
          funext fun i =>
            M.toBehavioralWith_eq_map_of_support_subset
              (mixed i) (fallback i) _ (hsub i)
        rw [hlocal, ← independentProduct_map]
        rfl
      conv_lhs =>
        rw [runMixedFrom,
          ← fiberPosterior_reconstruct (independentProduct mixed) (M.answerAt h),
          bindOnSupport_bind]
      rw [M.runBehavioralFrom_succ_of_not_terminal _ fuel hterm,
        behavioralJoint, hdraw]
      rw [PMF.bind_map]
      rw [← PMF.bindOnSupport_eq_bind]
      apply bindOnSupport_congr
      intro answer hanswer
      obtain ⟨p, hp, hpa⟩ :=
        (PMF.mem_support_map_iff (M.answerAt h)
          (independentProduct mixed) answer).1 hanswer
      have hfib : ∃ q ∈ M.answerAt h ⁻¹' {answer},
          q ∈ (independentProduct mixed).support :=
        ⟨p, hpa, hp⟩
      have hcoord : ∀ i,
          ∃ q ∈ M.AnsweredBy h answer i, q ∈ (mixed i).support := by
        intro i
        refine ⟨p i, ?_, ?_⟩
        · exact congrFun hpa i
        · exact (independentProduct_support_iff mixed p).1 hp i
      have hpost : fiberPosterior (independentProduct mixed)
          (M.answerAt h) answer hanswer =
          independentProduct (fun i =>
            (mixed i).filter (M.AnsweredBy h answer i) (hcoord i)) := by
        have hset : ({a | M.answerAt h a = answer} :
            Set ((i : ι) → M.Policy i)) =
            M.answerAt h ⁻¹' {answer} := by
          ext q
          rfl
        simpa only [fiberPosterior, hset] using
          (M.filter_answerAt mixed h answer hfib hcoord)
      rw [hpost]
      have hlegal : E.Legal h.state (fun i => (answer i).1) :=
        ExecutionProtocol.legal_of_legalOption hterm fun i =>
          (M.menu_adequate i h.trace (answer i).1).mp (answer i).2
      have hstep :
          (independentProduct (fun i =>
            (mixed i).filter (M.AnsweredBy h answer i) (hcoord i))).bind
              (fun q => M.runFrom q (fuel + 1) h) =
          (independentProduct (fun i =>
            (mixed i).filter (M.AnsweredBy h answer i) (hcoord i))).bind
              (fun q => (E.step h.state ⟨_, hlegal⟩).bindOnSupport
                fun _ realized => M.runFrom q fuel (h.extend hlegal realized)) := by
        apply bind_congr_on_support
        intro q hq
        apply M.runFrom_succ_of_chooser_eq q hterm ⟨_, hlegal⟩
          (Subtype.ext (funext fun i => by
            have hqi : q i ∈
                ((mixed i).filter (M.AnsweredBy h answer i) (hcoord i)).support :=
              (independentProduct_support_iff _ q).1 hq i
            have hanswered := ((PMF.mem_support_filter_iff (hcoord i)).1 hqi).1
            exact congrArg Subtype.val hanswered)) fuel
      rw [hstep, bind_bindOnSupport_comm]
      apply bindOnSupport_congr
      intro realized hrealized
      have hsub' : ∀ i,
          ((mixed i).filter (M.AnsweredBy h answer i) (hcoord i)).support ⊆
            M.ConsistentAt i (M.infoOf i (h.extend hlegal hrealized).trace) := by
        intro i q hq
        obtain ⟨hqanswer, hqmixed⟩ :=
          (PMF.mem_support_filter_iff (hcoord i)).1 hq
        have hprior := hsub i hqmixed
        rw [M.consistentAt_eq_consistent_ownPlay hconstrain i] at hprior ⊢
        intro step hstep
        rw [show M.ownPlay i (h.extend hlegal hrealized : E.History).trace =
            M.ownPlay i (Trace.extend h.trace
              (fun j => (answer j).1) hlegal hrealized) from rfl,
          InfoSignals.ownPlay_extend] at hstep
        revert hstep
        cases hcase : (answer i).1 with
        | none => exact fun hstep => hprior step hstep
        | some action =>
          intro hstep
          rcases List.mem_cons.mp hstep with hhead | htail
          · subst hhead
            show (q (M.infoOf i h.trace)).1 = _
            rw [hqanswer, hcase]
          · exact hprior step htail
      rw [show (independentProduct (fun i =>
              (mixed i).filter (M.AnsweredBy h answer i) (hcoord i))).bind
            (fun q => M.runFrom q fuel (h.extend hlegal hrealized)) =
          M.runMixedFrom
            (fun i => (mixed i).filter (M.AnsweredBy h answer i) (hcoord i)) fuel
            (h.extend hlegal hrealized) from rfl,
        ih _ _ hsub']
      apply M.runBehavioralFrom_congr fuel
      intro later hreach _ i
      cases hcase : (answer i).1 with
      | none =>
        rw [M.condOn_answeredBy_eq_self i hlegal hcase (mixed i) (hcoord i)]
      | some action =>
        exact M.toBehavioralWith_condOn_answered hconstrain i hlegal
          (fun _ => rfl) hrealized hcase hreach (mixed i) (fallback i) (hcoord i)

/-- A mixed policy and its conditional behavioral reading give the same law from the
initial history. -/
theorem runMixed_toBehavioralWith [Fintype ι] (hconstrain : M.ConstrainsAlike)
    (fallback : (i : ι) → M.Policy i) (fuel : ℕ)
    (mixed : (i : ι) → M.MixedPolicy i) :
    M.runMixed mixed fuel =
      M.runBehavioral (fun i => (mixed i).toBehavioralWith (fallback i)) fuel := by
  refine M.runMixedFrom_toBehavioralWith hconstrain fallback fuel mixed E.initHistory
    fun i q _ => ?_
  rw [M.consistentAt_eq_consistent_ownPlay hconstrain i,
    show M.ownPlay i (E.initHistory : E.History).trace = [] from rfl]
  exact fun step hstep => absurd hstep (by simp)

/-- Every mixed law has its canonical behavioral reading. -/
theorem runMixed_toBehavioral [Fintype ι] (hconstrain : M.ConstrainsAlike)
    (fuel : ℕ) (mixed : (i : ι) → M.MixedPolicy i) :
    M.runMixed mixed fuel = M.runBehavioral (fun i => (mixed i).toBehavioral) fuel :=
  M.runMixed_toBehavioralWith hconstrain
    (fun i => (mixed i).support_nonempty.choose) fuel mixed

/-- If each behavioral profile has only finitely many information sites in its
reachable support, behavioral and mixed profiles describe exactly the same
bounded laws. -/
theorem runBehavioral_image_eq_runMixed_image [Fintype ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (hconstrain : M.ConstrainsAlike) (fuel : ℕ)
    (hfinite : ∀ policy i,
      (M.behavioralSupportSitesFrom policy fuel E.initHistory i).Finite) :
    { law | ∃ policy : (i : ι) → M.BehavioralPolicy i,
        M.runBehavioral policy fuel = law } =
      { law | ∃ mixed : (i : ι) → M.MixedPolicy i,
        M.runMixed mixed fuel = law } := by
  ext law
  constructor
  · rintro ⟨policy, rfl⟩
    obtain ⟨mixed, hmixed⟩ := M.exists_mixed_runMixed_eq_runBehavioral
      hactsOnce policy fuel (hfinite policy)
    exact ⟨mixed, hmixed⟩
  · rintro ⟨mixed, rfl⟩
    exact ⟨fun i => (mixed i).toBehavioral,
      (M.runMixed_toBehavioral hconstrain fuel mixed).symm⟩

end InformationModel
end GameTheory.Protocol
