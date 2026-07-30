/-
# Arrow's impossibility theorem

The public statement uses the library's canonical weak-ranking vocabulary.
`Rank.Linear` says that an explicitly supplied weak comparison is reflexive,
transitive, total, and has no ties. Pareto, IIA, and dictatorship speak only
about its named strict part.

The proof privately changes representation between linear weak rankings and
strict linear rankings. The pivotal-voter argument is adapted from
`reference/GameTheory-v1/GameTheory/Mechanism/SocialChoice/Arrow.lean` at
commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`; unlike that source, this module
does not expose a second preference, profile, or social-welfare-function type.
-/

import GameTheory.Core.SocialChoice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.Order

namespace GameTheory

universe ua uα

namespace Aggregator

variable {Agent : Type ua} {α : Type uα}

/-- The aggregator returns a linear ranking whenever every agent supplies one. -/
def IsCollectivelyRational (aggregate : Aggregator Agent α) : Prop :=
  ∀ ranks, Preference.Linear ranks → Rank.Linear (aggregate ranks)

/-- Strict Pareto on the domain of linear rankings. -/
def IsPareto (aggregate : Aggregator Agent α) : Prop :=
  ∀ ranks, Preference.Linear ranks → ∀ preferred alternative,
    (∀ agent, Rank.strict (ranks agent) preferred alternative) →
      Rank.strict (aggregate ranks) preferred alternative

/-- Independence of irrelevant alternatives on the domain of linear rankings.
Both orientations are named because the public rankings are weak relations and
IIA concerns their strict parts. -/
def IsIIA (aggregate : Aggregator Agent α) : Prop :=
  ∀ ranks ranks', Preference.Linear ranks → Preference.Linear ranks' →
    ∀ preferred alternative,
      (∀ agent,
        (Rank.strict (ranks agent) preferred alternative ↔
          Rank.strict (ranks' agent) preferred alternative) ∧
        (Rank.strict (ranks agent) alternative preferred ↔
          Rank.strict (ranks' agent) alternative preferred)) →
        (Rank.strict (aggregate ranks) preferred alternative ↔
          Rank.strict (aggregate ranks') preferred alternative) ∧
        (Rank.strict (aggregate ranks) alternative preferred ↔
          Rank.strict (aggregate ranks') alternative preferred)

/-- An exact dictator on linear ranking profiles. -/
def IsDictator (aggregate : Aggregator Agent α) (dictator : Agent) : Prop :=
  ∀ ranks, Preference.Linear ranks → ∀ preferred alternative,
    Rank.strict (aggregate ranks) preferred alternative ↔
      Rank.strict (ranks dictator) preferred alternative

/-- The projection aggregator controlled by one named agent. -/
def dictator (agent : Agent) : Aggregator Agent α :=
  fun ranks => ranks agent

@[simp]
theorem dictator_apply (agent : Agent) (ranks : Ranking Agent α) :
    dictator agent ranks = ranks agent :=
  rfl

theorem dictator_collectivelyRational (agent : Agent) :
    IsCollectivelyRational (dictator agent : Aggregator Agent α) :=
  fun _ hlinear => hlinear agent

theorem dictator_pareto (agent : Agent) :
    IsPareto (dictator agent : Aggregator Agent α) :=
  fun _ _ _ _ hall => hall agent

theorem dictator_iia (agent : Agent) :
    IsIIA (dictator agent : Aggregator Agent α) :=
  fun _ _ _ _ _ _ hagree => hagree agent

theorem dictator_isDictator (agent : Agent) :
    IsDictator (dictator agent : Aggregator Agent α) agent :=
  fun _ _ _ _ => Iff.rfl

end Aggregator

namespace Arrow

variable {Agent : Type ua} {α : Type uα}

/-- There is an alternative outside every pair. This proof-oriented form does
not require the alternative type to be finite. -/
def HasAtLeastThree (α : Type uα) : Prop :=
  Nonempty α ∧ ∀ first second : α, ∃ third, third ≠ first ∧ third ≠ second

/-- Three pairwise distinct alternatives give the proof-oriented cardinality
condition used by the pivotal-voter argument. -/
theorem hasAtLeastThree_of_exists
    (h : ∃ first second third : α,
      first ≠ second ∧ first ≠ third ∧ second ≠ third) :
    HasAtLeastThree α := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc⟩ := h
  refine ⟨⟨a⟩, fun x y => ?_⟩
  by_contra hnone
  push Not at hnone
  have hsubset : ({a, b, c} : Finset α) ⊆ {x, y} := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz with hza | hzb | hzc
    · subst z
      exact (eq_or_ne a x).elim Or.inl (fun hax => Or.inr (hnone a hax))
    · subst z
      exact (eq_or_ne b x).elim Or.inl (fun hbx => Or.inr (hnone b hbx))
    · subst z
      exact (eq_or_ne c x).elim Or.inl (fun hcx => Or.inr (hnone c hcx))
  have hle := Finset.card_le_card hsubset
  have hthree : ({a, b, c} : Finset α).card = 3 := by simp [hab, hac, hbc]
  have htwo : ({x, y} : Finset α).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  omega

/-- A finite alternative type with cardinality at least three satisfies
`HasAtLeastThree`. -/
theorem hasAtLeastThree_of_card [Fintype α]
    (hcard : 2 < Fintype.card α) :
    HasAtLeastThree α := by
  classical
  constructor
  · exact Fintype.card_pos_iff.mp (by omega)
  · intro x y
    by_contra hnone
    push Not at hnone
    have hsubset : (Finset.univ : Finset α) ⊆ {x, y} := by
      intro z _
      rcases eq_or_ne z x with rfl | hzx
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (hnone z hzx))
    have hle := Finset.card_le_card hsubset
    rw [Finset.card_univ] at hle
    have htwo : ({x, y} : Finset α).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    omega

/-! ## Private strict-order proof representation -/

private abbrev StrictRelation (α : Type uα) := α → α → Prop

private abbrev StrictProfile (Agent : Type ua) (α : Type uα) :=
  Ranking Agent α

private abbrev StrictAggregator (Agent : Type ua) (α : Type uα) :=
  Aggregator Agent α

/-- The private invariant used by the pivotal proof. Its relation is read
strictly; no public declaration asks users to reinterpret a weak ranking this
way. -/
private structure StrictRanking (relation : StrictRelation α) : Prop where
  irrefl : ∀ item, ¬ relation item item
  trans : ∀ {preferred middle alternative},
    relation preferred middle → relation middle alternative →
      relation preferred alternative
  total : ∀ preferred alternative, preferred ≠ alternative →
    relation preferred alternative ∨ relation alternative preferred

private theorem StrictRanking.asymm
    {relation : StrictRelation α} (h : StrictRanking relation)
    {preferred alternative : α} (hpref : relation preferred alternative) :
    ¬ relation alternative preferred :=
  fun hreverse => h.irrefl preferred (h.trans hpref hreverse)

private theorem StrictRanking.not_iff
    {relation : StrictRelation α} (h : StrictRanking relation)
    {preferred alternative : α} (hne : preferred ≠ alternative) :
    ¬ relation preferred alternative ↔ relation alternative preferred := by
  constructor
  · intro hnot
    exact (h.total preferred alternative hne).resolve_left hnot
  · exact fun hreverse => h.asymm hreverse

private theorem strictRanking_lt [LinearOrder α] :
    StrictRanking ((· < ·) : StrictRelation α) :=
  ⟨lt_irrefl, fun hp hm => lt_trans hp hm,
    fun _ _ hne => lt_or_gt_of_ne hne⟩

private theorem exists_strictRanking (α : Type uα) :
    ∃ relation : StrictRelation α, StrictRanking relation := by
  letI : LinearOrder α := WellOrderingRel.isWellOrder.linearOrder
  exact ⟨(· < ·), strictRanking_lt⟩

/-- Reflexive closure changes a strict ranking into the corresponding weak
ranking. -/
private def weakOfStrict (relation : StrictRelation α) : α → α → Prop :=
  fun preferred alternative =>
    preferred = alternative ∨ relation preferred alternative

private theorem weakOfStrict_linear
    {relation : StrictRelation α} (h : StrictRanking relation) :
    Rank.Linear (weakOfStrict relation) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun item => Or.inl rfl
  · intro preferred middle alternative hpm hma
    rcases hpm with rfl | hpm
    · exact hma
    rcases hma with rfl | hma
    · exact Or.inr hpm
    · exact Or.inr (h.trans hpm hma)
  · intro preferred alternative
    rcases eq_or_ne preferred alternative with rfl | hne
    · exact Or.inl (Or.inl rfl)
    · rcases h.total preferred alternative hne with hp | ha
      · exact Or.inl (Or.inr hp)
      · exact Or.inr (Or.inr ha)
  · intro preferred alternative hpa hap
    rcases hpa with hEq | hp
    · exact hEq
    rcases hap with hEq | ha
    · exact hEq.symm
    · exact absurd ha (h.asymm hp)

private theorem strict_weakOfStrict
    {relation : StrictRelation α} (h : StrictRanking relation) :
    Rank.strict (weakOfStrict relation) = relation := by
  funext preferred alternative
  apply propext
  constructor
  · rintro ⟨hweak, hnot⟩
    exact hweak.resolve_left (fun hEq => hnot (Or.inl hEq.symm))
  · intro hpref
    refine ⟨Or.inr hpref, ?_⟩
    rintro (hEq | hreverse)
    · subst alternative
      exact h.irrefl preferred hpref
    · exact h.asymm hpref hreverse

private theorem strictRanking_strict_of_linear
    {ranks : α → α → Prop} (h : Rank.Linear ranks) :
    StrictRanking (Rank.strict ranks) := by
  refine ⟨Rank.strict_irrefl ranks, ?_, ?_⟩
  · rintro preferred middle alternative ⟨hpm, hnmp⟩ ⟨hma, hnam⟩
    refine ⟨h.2.1 preferred middle alternative hpm hma, ?_⟩
    intro hap
    exact hnmp (h.2.1 middle alternative preferred hma hap)
  · intro preferred alternative hne
    rcases h.2.2.1 preferred alternative with hpa | hap
    · by_cases hreverse : ranks alternative preferred
      · exact absurd (h.2.2.2 preferred alternative hpa hreverse) hne
      · exact Or.inl ⟨hpa, hreverse⟩
    · by_cases hreverse : ranks preferred alternative
      · exact absurd (h.2.2.2 preferred alternative hreverse hap) hne
      · exact Or.inr ⟨hap, hreverse⟩

private theorem weakOfStrict_strict_eq
    {ranks : α → α → Prop} (h : Rank.Linear ranks) :
    weakOfStrict (Rank.strict ranks) = ranks := by
  funext preferred alternative
  apply propext
  constructor
  · rintro (hEq | hpref)
    · subst alternative
      exact h.1 preferred
    · exact hpref.1
  · intro hpref
    rcases eq_or_ne preferred alternative with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr ⟨hpref, fun hreverse =>
        hne (h.2.2.2 preferred alternative hpref hreverse)⟩

private def weakProfileOfStrict
    (ranks : StrictProfile Agent α) : Ranking Agent α :=
  fun agent => weakOfStrict (ranks agent)

private def strictAggregatorOf
    (aggregate : Aggregator Agent α) : StrictAggregator Agent α :=
  fun ranks => Rank.strict (aggregate (weakProfileOfStrict ranks))

/-! ## Moving one alternative in a strict ranking -/

private def putTop
    (top : α) (relation : StrictRelation α) : StrictRelation α :=
  fun preferred alternative =>
    (preferred = top ∧ alternative ≠ top) ∨
      (preferred ≠ top ∧ alternative ≠ top ∧ relation preferred alternative)

private def putBottom
    (bottom : α) (relation : StrictRelation α) : StrictRelation α :=
  fun preferred alternative =>
    (alternative = bottom ∧ preferred ≠ bottom) ∨
      (preferred ≠ bottom ∧ alternative ≠ bottom ∧
        relation preferred alternative)

private theorem putTop_top
    {top preferred : α} {relation : StrictRelation α}
    (hne : preferred ≠ top) :
    putTop top relation top preferred :=
  Or.inl ⟨rfl, hne⟩

private theorem putTop_not_above
    {top preferred : α} {relation : StrictRelation α} :
    ¬ putTop top relation preferred top := by
  rintro (⟨_, hne⟩ | ⟨_, hne, _⟩) <;> exact hne rfl

private theorem putTop_others
    {top preferred alternative : α} {relation : StrictRelation α}
    (hp : preferred ≠ top) (ha : alternative ≠ top) :
    putTop top relation preferred alternative ↔
      relation preferred alternative := by
  constructor
  · rintro (⟨hEq, _⟩ | ⟨_, _, hrel⟩)
    · exact absurd hEq hp
    · exact hrel
  · exact fun hrel => Or.inr ⟨hp, ha, hrel⟩

private theorem putBottom_bottom
    {bottom preferred : α} {relation : StrictRelation α}
    (hne : preferred ≠ bottom) :
    putBottom bottom relation preferred bottom :=
  Or.inl ⟨rfl, hne⟩

private theorem putBottom_not_below
    {bottom alternative : α} {relation : StrictRelation α} :
    ¬ putBottom bottom relation bottom alternative := by
  rintro (⟨_, hne⟩ | ⟨hne, _, _⟩) <;> exact hne rfl

private theorem putBottom_others
    {bottom preferred alternative : α} {relation : StrictRelation α}
    (hp : preferred ≠ bottom) (ha : alternative ≠ bottom) :
    putBottom bottom relation preferred alternative ↔
      relation preferred alternative := by
  constructor
  · rintro (⟨hEq, _⟩ | ⟨_, _, hrel⟩)
    · exact absurd hEq ha
    · exact hrel
  · exact fun hrel => Or.inr ⟨hp, ha, hrel⟩

private theorem StrictRanking.putTop
    {relation : StrictRelation α} (h : StrictRanking relation) (top : α) :
    StrictRanking (putTop top relation) := by
  refine ⟨?_, ?_, ?_⟩
  · intro item
    rintro (⟨rfl, hne⟩ | ⟨_, _, hrel⟩)
    · exact hne rfl
    · exact h.irrefl item hrel
  · intro preferred middle alternative hpm hma
    rcases hpm with ⟨rfl, hm⟩ | ⟨hp, hm, hpm⟩
    · rcases hma with ⟨hEq, _⟩ | ⟨_, ha, _⟩
      · exact absurd hEq hm
      · exact Or.inl ⟨rfl, ha⟩
    · rcases hma with ⟨hEq, _⟩ | ⟨_, ha, hma⟩
      · exact absurd hEq hm
      · exact Or.inr ⟨hp, ha, h.trans hpm hma⟩
  · intro preferred alternative hne
    by_cases hp : preferred = top
    · subst preferred
      exact Or.inl (Or.inl ⟨rfl, fun hEq => hne hEq.symm⟩)
    · by_cases ha : alternative = top
      · subst alternative
        exact Or.inr (Or.inl ⟨rfl, hp⟩)
      · rw [putTop_others hp ha, putTop_others ha hp]
        exact h.total preferred alternative hne

private theorem StrictRanking.putBottom
    {relation : StrictRelation α} (h : StrictRanking relation) (bottom : α) :
    StrictRanking (putBottom bottom relation) := by
  refine ⟨?_, ?_, ?_⟩
  · intro item
    rintro (⟨rfl, hne⟩ | ⟨_, _, hrel⟩)
    · exact hne rfl
    · exact h.irrefl item hrel
  · intro preferred middle alternative hpm hma
    rcases hma with ⟨rfl, hm⟩ | ⟨hm, ha, hma⟩
    · rcases hpm with ⟨hEq, _⟩ | ⟨hp, _, _⟩
      · exact absurd hEq hm
      · exact Or.inl ⟨rfl, hp⟩
    · rcases hpm with ⟨hEq, _⟩ | ⟨hp, _, hpm⟩
      · exact absurd hEq hm
      · exact Or.inr ⟨hp, ha, h.trans hpm hma⟩
  · intro preferred alternative hne
    by_cases ha : alternative = bottom
    · subst alternative
      exact Or.inl (Or.inl ⟨rfl, hne⟩)
    · by_cases hp : preferred = bottom
      · subst preferred
        exact Or.inr (Or.inl ⟨rfl, fun hEq => hne hEq.symm⟩)
      · rw [putBottom_others hp ha, putBottom_others ha hp]
        exact h.total preferred alternative hne

/-! ## Extremal alternatives -/

private def IsExtremal
    (item : α) (relation : StrictRelation α) : Prop :=
  (∀ other, other ≠ item → relation item other) ∨
    (∀ other, other ≠ item → relation other item)

private theorem IsExtremal.compare
    {relation : StrictRelation α} {first item second : α}
    (hext : IsExtremal item relation) (h : StrictRanking relation)
    (hif : item ≠ first) (his : item ≠ second) :
    (relation second item ↔ relation first item) ∧
      (relation item second ↔ relation item first) := by
  rcases hext with htop | hbottom
  · exact
      ⟨iff_of_false (h.asymm (htop second (Ne.symm his)))
          (h.asymm (htop first (Ne.symm hif))),
        iff_of_true (htop second (Ne.symm his))
          (htop first (Ne.symm hif))⟩
  · exact
      ⟨iff_of_true (hbottom second (Ne.symm his))
          (hbottom first (Ne.symm hif)),
        iff_of_false (h.asymm (hbottom second (Ne.symm his)))
          (h.asymm (hbottom first (Ne.symm hif)))⟩

private def swapRelation [DecidableEq α]
    (first second : α) (relation : StrictRelation α) :
    StrictRelation α :=
  fun preferred alternative =>
    relation (Equiv.swap first second preferred)
      (Equiv.swap first second alternative)

private theorem StrictRanking.swapRelation [DecidableEq α]
    {relation : StrictRelation α} (h : StrictRanking relation)
    (first second : α) :
    StrictRanking (swapRelation first second relation) :=
  ⟨fun _ => h.irrefl _,
    fun hp hm => h.trans hp hm,
    fun _ _ hne =>
      h.total _ _ ((Equiv.swap first second).injective.ne hne)⟩

open Classical in
private noncomputable def forceAbove [DecidableEq α]
    (lower upper : α) (relation : StrictRelation α) :
    StrictRelation α :=
  if relation lower upper then
    swapRelation lower upper relation
  else
    relation

private theorem StrictRanking.forceAbove [DecidableEq α]
    {relation : StrictRelation α} (h : StrictRanking relation)
    (lower upper : α) :
    StrictRanking (forceAbove lower upper relation) := by
  unfold GameTheory.Arrow.forceAbove
  split
  · exact h.swapRelation lower upper
  · exact h

private theorem forceAbove_forces [DecidableEq α]
    {relation : StrictRelation α} {lower upper : α}
    (h : StrictRanking relation) (hne : lower ≠ upper) :
    forceAbove lower upper relation upper lower := by
  unfold GameTheory.Arrow.forceAbove
  split
  · rename_i hpref
    simp only [swapRelation, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact hpref
  · rename_i hnot
    exact (h.total upper lower hne.symm).resolve_right hnot

private theorem forceAbove_agree [DecidableEq α]
    {relation : StrictRelation α} {lower item upper : α}
    (h : StrictRanking relation) (hil : item ≠ lower)
    (hiu : item ≠ upper) (hext : IsExtremal item relation) :
    (forceAbove lower upper relation lower item ↔ relation lower item) ∧
    (forceAbove lower upper relation item lower ↔ relation item lower) ∧
    (forceAbove lower upper relation item upper ↔ relation item upper) ∧
    (forceAbove lower upper relation upper item ↔ relation upper item) := by
  obtain ⟨hui, hiu'⟩ := hext.compare h hil hiu
  unfold GameTheory.Arrow.forceAbove
  split
  · have hli :
        swapRelation lower upper relation lower item =
          relation upper item := by
        simp only [swapRelation, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne hil hiu]
    have hil' :
        swapRelation lower upper relation item lower =
          relation item upper := by
        simp only [swapRelation, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne hil hiu]
    have hiu'' :
        swapRelation lower upper relation item upper =
          relation item lower := by
        simp only [swapRelation, Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne hil hiu]
    have hui' :
        swapRelation lower upper relation upper item =
          relation lower item := by
        simp only [swapRelation, Equiv.swap_apply_right,
          Equiv.swap_apply_of_ne_of_ne hil hiu]
    rw [hli, hil', hiu'', hui']
    exact ⟨hui, hiu', hiu'.symm, hui.symm⟩
  · exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-! ## Strict-domain axioms used by the private proof -/

private def IsStrictCollectivelyRational
    (aggregate : StrictAggregator Agent α) : Prop :=
  ∀ ranks : StrictProfile Agent α,
    (∀ agent, StrictRanking (ranks agent)) →
      StrictRanking (aggregate ranks)

private def IsStrictPareto
    (aggregate : StrictAggregator Agent α) : Prop :=
  ∀ ranks : StrictProfile Agent α,
    (∀ agent, StrictRanking (ranks agent)) →
      ∀ preferred alternative,
        (∀ agent, ranks agent preferred alternative) →
          aggregate ranks preferred alternative

private def IsStrictIIA
    (aggregate : StrictAggregator Agent α) : Prop :=
  ∀ ranks ranks' : StrictProfile Agent α,
    (∀ agent, StrictRanking (ranks agent)) →
    (∀ agent, StrictRanking (ranks' agent)) →
    ∀ preferred alternative,
      (∀ agent,
        (ranks agent preferred alternative ↔
          ranks' agent preferred alternative) ∧
        (ranks agent alternative preferred ↔
          ranks' agent alternative preferred)) →
        (aggregate ranks preferred alternative ↔
          aggregate ranks' preferred alternative) ∧
        (aggregate ranks alternative preferred ↔
          aggregate ranks' alternative preferred)

private theorem extremal_lemma
    {aggregate : StrictAggregator Agent α}
    (hrational : IsStrictCollectivelyRational aggregate)
    (hpareto : IsStrictPareto aggregate)
    (hiia : IsStrictIIA aggregate)
    {item : α} {ranks : StrictProfile Agent α}
    (hlinear : ∀ agent, StrictRanking (ranks agent))
    (hextremal : ∀ agent, IsExtremal item (ranks agent)) :
    IsExtremal item (aggregate ranks) := by
  classical
  by_contra hnot
  have hsocial : StrictRanking (aggregate ranks) :=
    hrational ranks hlinear
  unfold IsExtremal at hnot
  push Not at hnot
  obtain ⟨⟨first, hif, hnif⟩, ⟨second, his, hnsi⟩⟩ := hnot
  have hfirst : aggregate ranks first item :=
    (hsocial.not_iff hif.symm).mp hnif
  have hsecond : aggregate ranks item second :=
    (hsocial.not_iff his).mp hnsi
  have hne : first ≠ second := by
    rintro rfl
    exact hsocial.asymm hfirst hsecond
  let ranks' : StrictProfile Agent α :=
    fun agent => forceAbove first second (ranks agent)
  have hlinear' : ∀ agent, StrictRanking (ranks' agent) :=
    fun agent => (hlinear agent).forceAbove first second
  have hforced : aggregate ranks' second first :=
    hpareto ranks' hlinear' second first
      (fun agent => forceAbove_forces (hlinear agent) hne)
  have hnreverse : ¬ aggregate ranks' first second :=
    (hrational ranks' hlinear').asymm hforced
  have hiiaFirst := hiia ranks ranks' hlinear hlinear'
    first item (fun agent => by
      obtain ⟨h₁, h₂, _, _⟩ :=
        forceAbove_agree (hlinear agent) hif.symm his.symm
          (hextremal agent)
      exact ⟨h₁.symm, h₂.symm⟩)
  have hiiaSecond := hiia ranks ranks' hlinear hlinear'
    item second (fun agent => by
      obtain ⟨_, _, h₃, h₄⟩ :=
        forceAbove_agree (hlinear agent) hif.symm his.symm
          (hextremal agent)
      exact ⟨h₃.symm, h₄.symm⟩)
  have hfirst' : aggregate ranks' first item :=
    hiiaFirst.1.mp hfirst
  have hsecond' : aggregate ranks' item second :=
    hiiaSecond.1.mp hsecond
  exact hnreverse ((hrational ranks' hlinear').trans hfirst' hsecond')

/-! ## Pivotal profiles -/

private def StrictDecides
    (aggregate : StrictAggregator Agent α) (agent : Agent)
    (preferred alternative : α) : Prop :=
  ∀ ranks : StrictProfile Agent α,
    (∀ other, StrictRanking (ranks other)) →
      ranks agent preferred alternative →
        aggregate ranks preferred alternative

private def IsStrictDictator
    (aggregate : StrictAggregator Agent α) (agent : Agent) : Prop :=
  ∀ preferred alternative,
    StrictDecides aggregate agent preferred alternative

private def pivotal [DecidableEq Agent]
    (item : α) (background : StrictRelation α) (coalition : Finset Agent) :
    StrictProfile Agent α :=
  fun agent =>
    if agent ∈ coalition then
      putTop item background
    else
      putBottom item background

private theorem pivotal_mem [DecidableEq Agent]
    {item : α} {background : StrictRelation α}
    {coalition : Finset Agent} {agent : Agent}
    (hmem : agent ∈ coalition) :
    pivotal item background coalition agent =
      putTop item background :=
  if_pos hmem

private theorem pivotal_not_mem [DecidableEq Agent]
    {item : α} {background : StrictRelation α}
    {coalition : Finset Agent} {agent : Agent}
    (hmem : agent ∉ coalition) :
    pivotal item background coalition agent =
      putBottom item background :=
  if_neg hmem

private theorem pivotal_ranking [DecidableEq Agent]
    {item : α} {background : StrictRelation α}
    (hbackground : StrictRanking background)
    (coalition : Finset Agent) (agent : Agent) :
    StrictRanking (pivotal item background coalition agent) := by
  unfold pivotal
  split
  · exact hbackground.putTop item
  · exact hbackground.putBottom item

private theorem pivotal_extremal [DecidableEq Agent]
    {item : α} {background : StrictRelation α}
    (coalition : Finset Agent) (agent : Agent) :
    IsExtremal item (pivotal item background coalition agent) := by
  unfold pivotal
  split
  · exact Or.inl fun _ hne => putTop_top hne
  · exact Or.inr fun _ hne => putBottom_bottom hne

private def starProfile [DecidableEq Agent]
    (item preferred alternative : α) (background : StrictRelation α)
    (ranks : StrictProfile Agent α) (pivot : Agent)
    (lowerCoalition : Finset Agent) :
    StrictProfile Agent α :=
  fun agent =>
    if agent = pivot then
      putBottom alternative (putTop preferred background)
    else if agent ∈ lowerCoalition then
      putTop item (ranks agent)
    else
      putBottom item (ranks agent)

private theorem starProfile_pivot [DecidableEq Agent]
    {item preferred alternative : α}
    {background : StrictRelation α}
    {ranks : StrictProfile Agent α} {pivot : Agent}
    {lowerCoalition : Finset Agent} :
    starProfile item preferred alternative background ranks pivot
        lowerCoalition pivot =
      putBottom alternative (putTop preferred background) :=
  if_pos rfl

private theorem starProfile_mem [DecidableEq Agent]
    {item preferred alternative : α}
    {background : StrictRelation α}
    {ranks : StrictProfile Agent α} {pivot agent : Agent}
    {lowerCoalition : Finset Agent}
    (hne : agent ≠ pivot) (hmem : agent ∈ lowerCoalition) :
    starProfile item preferred alternative background ranks pivot
        lowerCoalition agent =
      putTop item (ranks agent) := by
  rw [starProfile, if_neg hne, if_pos hmem]

private theorem starProfile_not_mem [DecidableEq Agent]
    {item preferred alternative : α}
    {background : StrictRelation α}
    {ranks : StrictProfile Agent α} {pivot agent : Agent}
    {lowerCoalition : Finset Agent}
    (hne : agent ≠ pivot) (hmem : agent ∉ lowerCoalition) :
    starProfile item preferred alternative background ranks pivot
        lowerCoalition agent =
      putBottom item (ranks agent) := by
  rw [starProfile, if_neg hne, if_neg hmem]

private theorem dictator_pair [DecidableEq Agent]
    {aggregate : StrictAggregator Agent α}
    (hrational : IsStrictCollectivelyRational aggregate)
    (hiia : IsStrictIIA aggregate)
    {item : α} {background : StrictRelation α}
    (hbackground : StrictRanking background)
    {pivot : Agent} {lowerCoalition : Finset Agent}
    (hpivot : pivot ∉ lowerCoalition)
    (hbottom : ∀ other, other ≠ item →
      aggregate (pivotal item background lowerCoalition) other item)
    (htop : ∀ other, other ≠ item →
      aggregate (pivotal item background
        (insert pivot lowerCoalition)) item other)
    {preferred alternative : α}
    (hpref : preferred ≠ item) (halt : alternative ≠ item)
    (hne : preferred ≠ alternative) :
    StrictDecides aggregate pivot preferred alternative := by
  intro ranks hlinear hpivotPref
  set witness :=
    starProfile item preferred alternative background ranks pivot
      lowerCoalition with hwitness
  have hwitnessPivot :
      witness pivot =
        putBottom alternative (putTop preferred background) := by
    rw [hwitness]
    exact starProfile_pivot
  have hpItem :
      putBottom alternative (putTop preferred background)
        preferred item :=
    (putBottom_others hne halt.symm).mpr
      (putTop_top hpref.symm)
  have hnItemP :
      ¬ putBottom alternative (putTop preferred background)
        item preferred :=
    fun hrel =>
      putTop_not_above
        ((putBottom_others halt.symm hne).mp hrel)
  have hItemA :
      putBottom alternative (putTop preferred background)
        item alternative :=
    putBottom_bottom halt.symm
  have hnAItem :
      ¬ putBottom alternative (putTop preferred background)
        alternative item :=
    putBottom_not_below
  have hpA :
      putBottom alternative (putTop preferred background)
        preferred alternative :=
    putBottom_bottom hne
  have hnAP :
      ¬ putBottom alternative (putTop preferred background)
        alternative preferred :=
    putBottom_not_below
  have hwitnessLinear :
      ∀ agent, StrictRanking (witness agent) := by
    intro agent
    by_cases hap : agent = pivot
    · rw [hap, hwitnessPivot]
      exact (hbackground.putTop preferred).putBottom alternative
    · by_cases hmem : agent ∈ lowerCoalition
      · rw [hwitness, starProfile_mem hap hmem]
        exact (hlinear agent).putTop item
      · rw [hwitness, starProfile_not_mem hap hmem]
        exact (hlinear agent).putBottom item
  have hagreePreferred :
      ∀ agent,
        (witness agent preferred item ↔
          pivotal item background lowerCoalition agent preferred item) ∧
        (witness agent item preferred ↔
          pivotal item background lowerCoalition agent item preferred) := by
    intro agent
    by_cases hap : agent = pivot
    · rw [hap, hwitnessPivot, pivotal_not_mem hpivot]
      exact
        ⟨iff_of_true hpItem (putBottom_bottom hpref),
          iff_of_false hnItemP putBottom_not_below⟩
    · by_cases hmem : agent ∈ lowerCoalition
      · rw [hwitness, starProfile_mem hap hmem, pivotal_mem hmem]
        exact
          ⟨iff_of_false putTop_not_above putTop_not_above,
            iff_of_true (putTop_top hpref) (putTop_top hpref)⟩
      · rw [hwitness, starProfile_not_mem hap hmem,
          pivotal_not_mem hmem]
        exact
          ⟨iff_of_true (putBottom_bottom hpref)
              (putBottom_bottom hpref),
            iff_of_false putBottom_not_below putBottom_not_below⟩
  have hagreeAlternative :
      ∀ agent,
        (witness agent item alternative ↔
          pivotal item background (insert pivot lowerCoalition)
            agent item alternative) ∧
        (witness agent alternative item ↔
          pivotal item background (insert pivot lowerCoalition)
            agent alternative item) := by
    intro agent
    by_cases hap : agent = pivot
    · rw [hap, hwitnessPivot,
          pivotal_mem (Finset.mem_insert_self pivot lowerCoalition)]
      exact
        ⟨iff_of_true hItemA (putTop_top halt),
          iff_of_false hnAItem putTop_not_above⟩
    · by_cases hmem : agent ∈ lowerCoalition
      · rw [hwitness, starProfile_mem hap hmem,
          pivotal_mem (Finset.mem_insert_of_mem hmem)]
        exact
          ⟨iff_of_true (putTop_top halt) (putTop_top halt),
            iff_of_false putTop_not_above putTop_not_above⟩
      · have hnot :
          agent ∉ insert pivot lowerCoalition := fun h =>
            (Finset.mem_insert.mp h).elim hap hmem
        rw [hwitness, starProfile_not_mem hap hmem,
          pivotal_not_mem hnot]
        exact
          ⟨iff_of_false putBottom_not_below putBottom_not_below,
            iff_of_true (putBottom_bottom halt)
              (putBottom_bottom halt)⟩
  have hagreePair :
      ∀ agent,
        (witness agent preferred alternative ↔
          ranks agent preferred alternative) ∧
        (witness agent alternative preferred ↔
          ranks agent alternative preferred) := by
    intro agent
    by_cases hap : agent = pivot
    · rw [hap, hwitnessPivot]
      exact
        ⟨iff_of_true hpA hpivotPref,
          iff_of_false hnAP ((hlinear pivot).asymm hpivotPref)⟩
    · by_cases hmem : agent ∈ lowerCoalition
      · rw [hwitness, starProfile_mem hap hmem]
        exact
          ⟨putTop_others hpref halt,
            putTop_others halt hpref⟩
      · rw [hwitness, starProfile_not_mem hap hmem]
        exact
          ⟨putBottom_others hpref halt,
            putBottom_others halt hpref⟩
  have hsocialPreferred :
      aggregate witness preferred item :=
    ((hiia witness (pivotal item background lowerCoalition)
      hwitnessLinear (pivotal_ranking hbackground lowerCoalition)
      preferred item hagreePreferred).1).mpr
        (hbottom preferred hpref)
  have hsocialAlternative :
      aggregate witness item alternative :=
    ((hiia witness
      (pivotal item background (insert pivot lowerCoalition))
      hwitnessLinear
      (pivotal_ranking hbackground (insert pivot lowerCoalition))
      item alternative hagreeAlternative).1).mpr
        (htop alternative halt)
  have hsocialPair :
      aggregate witness preferred alternative :=
    (hrational witness hwitnessLinear).trans
      hsocialPreferred hsocialAlternative
  exact
    ((hiia witness ranks hwitnessLinear hlinear
      preferred alternative hagreePair).1).mp hsocialPair

/-! ## Extending decisiveness to pairs involving the reference alternative -/

private def preferredReferenceProfile [DecidableEq Agent]
    (reference preferred bridge : α)
    (ranks : StrictProfile Agent α) (pivot : Agent) :
    StrictProfile Agent α :=
  fun agent =>
    if agent = pivot then
      putBottom reference (putTop preferred (ranks pivot))
    else
      putTop bridge (ranks agent)

private def referencePreferredProfile [DecidableEq Agent]
    (reference preferred bridge : α)
    (ranks : StrictProfile Agent α) (pivot : Agent) :
    StrictProfile Agent α :=
  fun agent =>
    if agent = pivot then
      putTop reference (putBottom preferred (ranks pivot))
    else
      putBottom bridge (ranks agent)

private theorem preferredReferenceProfile_pivot [DecidableEq Agent]
    {reference preferred bridge : α}
    {ranks : StrictProfile Agent α} {pivot : Agent} :
    preferredReferenceProfile reference preferred bridge ranks pivot pivot =
      putBottom reference (putTop preferred (ranks pivot)) :=
  if_pos rfl

private theorem preferredReferenceProfile_ne [DecidableEq Agent]
    {reference preferred bridge : α}
    {ranks : StrictProfile Agent α} {pivot agent : Agent}
    (hne : agent ≠ pivot) :
    preferredReferenceProfile reference preferred bridge ranks pivot agent =
      putTop bridge (ranks agent) :=
  if_neg hne

private theorem referencePreferredProfile_pivot [DecidableEq Agent]
    {reference preferred bridge : α}
    {ranks : StrictProfile Agent α} {pivot : Agent} :
    referencePreferredProfile reference preferred bridge ranks pivot pivot =
      putTop reference (putBottom preferred (ranks pivot)) :=
  if_pos rfl

private theorem referencePreferredProfile_ne [DecidableEq Agent]
    {reference preferred bridge : α}
    {ranks : StrictProfile Agent α} {pivot agent : Agent}
    (hne : agent ≠ pivot) :
    referencePreferredProfile reference preferred bridge ranks pivot agent =
      putBottom bridge (ranks agent) :=
  if_neg hne

private theorem dictator_preferred_reference
    {aggregate : StrictAggregator Agent α}
    (hrational : IsStrictCollectivelyRational aggregate)
    (hpareto : IsStrictPareto aggregate)
    (hiia : IsStrictIIA aggregate)
    {reference : α} {pivot : Agent}
    (hdecides : ∀ first second,
      first ≠ reference → second ≠ reference → first ≠ second →
        StrictDecides aggregate pivot first second)
    {preferred bridge : α}
    (hpref : preferred ≠ reference) (hbridge : bridge ≠ reference)
    (hne : bridge ≠ preferred) :
    StrictDecides aggregate pivot preferred reference := by
  classical
  intro ranks hlinear hpivot
  set witness :=
    preferredReferenceProfile reference preferred bridge ranks pivot
      with hwitness
  have hwitnessPivot :
      witness pivot =
        putBottom reference (putTop preferred (ranks pivot)) := by
    rw [hwitness]
    exact preferredReferenceProfile_pivot
  have hwitnessLinear :
      ∀ agent, StrictRanking (witness agent) := by
    intro agent
    by_cases hap : agent = pivot
    · rw [hap, hwitnessPivot]
      exact ((hlinear pivot).putTop preferred).putBottom reference
    · rw [hwitness, preferredReferenceProfile_ne hap]
      exact (hlinear agent).putTop bridge
  have hbridgeReference :
      ∀ agent, witness agent bridge reference := by
    intro agent
    by_cases hap : agent = pivot
    · rw [hap, hwitnessPivot]
      exact putBottom_bottom hbridge
    · rw [hwitness, preferredReferenceProfile_ne hap]
      exact putTop_top hbridge.symm
  have hprefBridge : witness pivot preferred bridge := by
    rw [hwitnessPivot]
    exact
      (putBottom_others hpref hbridge).mpr
        (putTop_top hne)
  have hsocialBridge :
      aggregate witness bridge reference :=
    hpareto witness hwitnessLinear bridge reference
      hbridgeReference
  have hsocialPreferred :
      aggregate witness preferred bridge :=
    hdecides preferred bridge hpref hbridge hne.symm
      witness hwitnessLinear hprefBridge
  have hsocial :
      aggregate witness preferred reference :=
    (hrational witness hwitnessLinear).trans
      hsocialPreferred hsocialBridge
  have hagree :
      ∀ agent,
        (witness agent preferred reference ↔
          ranks agent preferred reference) ∧
        (witness agent reference preferred ↔
          ranks agent reference preferred) := by
    intro agent
    by_cases hap : agent = pivot
    · rw [hap, hwitnessPivot]
      exact
        ⟨iff_of_true (putBottom_bottom hpref) hpivot,
          iff_of_false putBottom_not_below
            ((hlinear pivot).asymm hpivot)⟩
    · rw [hwitness, preferredReferenceProfile_ne hap]
      exact
        ⟨putTop_others hne.symm hbridge.symm,
          putTop_others hbridge.symm hne.symm⟩
  exact
    ((hiia witness ranks hwitnessLinear hlinear
      preferred reference hagree).1).mp hsocial

private theorem dictator_reference_preferred
    {aggregate : StrictAggregator Agent α}
    (hrational : IsStrictCollectivelyRational aggregate)
    (hpareto : IsStrictPareto aggregate)
    (hiia : IsStrictIIA aggregate)
    {reference : α} {pivot : Agent}
    (hdecides : ∀ first second,
      first ≠ reference → second ≠ reference → first ≠ second →
        StrictDecides aggregate pivot first second)
    {preferred bridge : α}
    (hpref : preferred ≠ reference) (hbridge : bridge ≠ reference)
    (hne : bridge ≠ preferred) :
    StrictDecides aggregate pivot reference preferred := by
  classical
  intro ranks hlinear hpivot
  set witness :=
    referencePreferredProfile reference preferred bridge ranks pivot
      with hwitness
  have hwitnessPivot :
      witness pivot =
        putTop reference (putBottom preferred (ranks pivot)) := by
    rw [hwitness]
    exact referencePreferredProfile_pivot
  have hwitnessLinear :
      ∀ agent, StrictRanking (witness agent) := by
    intro agent
    by_cases hap : agent = pivot
    · rw [hap, hwitnessPivot]
      exact ((hlinear pivot).putBottom preferred).putTop reference
    · rw [hwitness, referencePreferredProfile_ne hap]
      exact (hlinear agent).putBottom bridge
  have hreferenceBridge :
      ∀ agent, witness agent reference bridge := by
    intro agent
    by_cases hap : agent = pivot
    · rw [hap, hwitnessPivot]
      exact putTop_top hbridge
    · rw [hwitness, referencePreferredProfile_ne hap]
      exact putBottom_bottom hbridge.symm
  have hbridgePreferred : witness pivot bridge preferred := by
    rw [hwitnessPivot]
    exact
      (putTop_others hbridge hpref).mpr
        (putBottom_bottom hne)
  have hsocialReference :
      aggregate witness reference bridge :=
    hpareto witness hwitnessLinear reference bridge
      hreferenceBridge
  have hsocialBridge :
      aggregate witness bridge preferred :=
    hdecides bridge preferred hbridge hpref hne
      witness hwitnessLinear hbridgePreferred
  have hsocial :
      aggregate witness reference preferred :=
    (hrational witness hwitnessLinear).trans
      hsocialReference hsocialBridge
  have hagree :
      ∀ agent,
        (witness agent reference preferred ↔
          ranks agent reference preferred) ∧
        (witness agent preferred reference ↔
          ranks agent preferred reference) := by
    intro agent
    by_cases hap : agent = pivot
    · rw [hap, hwitnessPivot]
      exact
        ⟨iff_of_true (putTop_top hpref) hpivot,
          iff_of_false putTop_not_above
            ((hlinear pivot).asymm hpivot)⟩
    · rw [hwitness, referencePreferredProfile_ne hap]
      exact
        ⟨putBottom_others hbridge.symm hne.symm,
          putBottom_others hne.symm hbridge.symm⟩
  exact
    ((hiia witness ranks hwitnessLinear hlinear
      reference preferred hagree).1).mp hsocial

/-! ## The private strict-order theorem -/

private theorem strict_arrow_impossibility
    [Nonempty Agent] [Fintype Agent]
    {aggregate : StrictAggregator Agent α}
    (hrational : IsStrictCollectivelyRational aggregate)
    (hpareto : IsStrictPareto aggregate)
    (hiia : IsStrictIIA aggregate)
    (hα : HasAtLeastThree α) :
    ∃ dictator, IsStrictDictator aggregate dictator := by
  classical
  obtain ⟨hαNonempty, hthird⟩ := hα
  obtain ⟨reference⟩ := hαNonempty
  obtain ⟨background, hbackground⟩ := exists_strictRanking α
  let atTop : Finset Agent → Prop :=
    fun coalition =>
      ∀ alternative, alternative ≠ reference →
        aggregate (pivotal reference background coalition)
          reference alternative
  let atBottom : Finset Agent → Prop :=
    fun coalition =>
      ∀ alternative, alternative ≠ reference →
        aggregate (pivotal reference background coalition)
          alternative reference
  have htopUniv : atTop Finset.univ :=
    fun alternative hne =>
      hpareto (pivotal reference background Finset.univ)
        (pivotal_ranking hbackground Finset.univ)
        reference alternative (fun agent => by
          rw [pivotal_mem (Finset.mem_univ agent)]
          exact putTop_top hne)
  have hbottomEmpty : atBottom ∅ :=
    fun alternative hne =>
      hpareto (pivotal reference background ∅)
        (pivotal_ranking hbackground ∅)
        alternative reference (fun agent => by
          rw [pivotal_not_mem (by simp)]
          exact putBottom_bottom hne)
  have hnonempty :
      (Finset.univ.filter atTop).Nonempty :=
    ⟨Finset.univ,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, htopUniv⟩⟩
  obtain ⟨coalition, hcoalition, hminimal⟩ :=
    Finset.exists_min_image _ Finset.card hnonempty
  have hcoalitionTop : atTop coalition :=
    (Finset.mem_filter.mp hcoalition).2
  have hcoalitionNonempty : coalition.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    obtain ⟨alternative, hne, _⟩ :=
      hthird reference reference
    have htopEmpty : atTop ∅ := by
      simpa only [hempty] using hcoalitionTop
    exact
      (hrational _ (pivotal_ranking hbackground ∅)).asymm
        (htopEmpty alternative hne)
        (hbottomEmpty alternative hne)
  obtain ⟨pivot, hpivotMem⟩ := hcoalitionNonempty
  set lowerCoalition := coalition.erase pivot with hlower
  have hpivotNotMem : pivot ∉ lowerCoalition := by
    rw [hlower]
    simp
  have hinsert :
      insert pivot lowerCoalition = coalition := by
    rw [hlower]
    exact Finset.insert_erase hpivotMem
  have hlowerCard :
      lowerCoalition.card < coalition.card := by
    rw [hlower]
    exact Finset.card_erase_lt_of_mem hpivotMem
  have hlowerNotTop : ¬ atTop lowerCoalition :=
    fun hcontradiction => by
      have hle :=
        hminimal lowerCoalition
          (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, hcontradiction⟩)
      omega
  have hlowerBottom : atBottom lowerCoalition := by
    rcases
        extremal_lemma hrational hpareto hiia
          (pivotal_ranking hbackground lowerCoalition)
          (pivotal_extremal lowerCoalition) with
      htop | hbottom
    · exact absurd htop hlowerNotTop
    · exact hbottom
  have hdecides :
      ∀ first second,
        first ≠ reference → second ≠ reference → first ≠ second →
          StrictDecides aggregate pivot first second :=
    fun first second hfirst hsecond hne =>
      dictator_pair hrational hiia hbackground hpivotNotMem
        hlowerBottom
        (fun alternative halt => by
          rw [hinsert]
          exact hcoalitionTop alternative halt)
        hfirst hsecond hne
  refine ⟨pivot, ?_⟩
  intro preferred alternative
  by_cases hpref : preferred = reference
  · by_cases halt : alternative = reference
    · rw [hpref, halt]
      exact fun ranks hlinear hrel =>
        absurd hrel ((hlinear pivot).irrefl _)
    · rw [hpref]
      obtain ⟨bridge, hbridgeAlternative, hbridgeReference⟩ :=
        hthird alternative reference
      exact
        dictator_reference_preferred hrational hpareto hiia hdecides
          halt hbridgeReference hbridgeAlternative
  · by_cases halt : alternative = reference
    · rw [halt]
      obtain ⟨bridge, hbridgePreferred, hbridgeReference⟩ :=
        hthird preferred reference
      exact
        dictator_preferred_reference hrational hpareto hiia hdecides
          hpref hbridgeReference hbridgePreferred
    · by_cases hne : preferred = alternative
      · rw [hne]
        exact fun ranks hlinear hrel =>
          absurd hrel ((hlinear pivot).irrefl _)
      · exact hdecides preferred alternative hpref halt hne

private theorem strictDictator_exact
    {aggregate : StrictAggregator Agent α}
    (hrational : IsStrictCollectivelyRational aggregate)
    {dictator : Agent}
    (hdictator : IsStrictDictator aggregate dictator)
    {ranks : StrictProfile Agent α}
    (hlinear : ∀ agent, StrictRanking (ranks agent))
    (preferred alternative : α) :
    aggregate ranks preferred alternative ↔
      ranks dictator preferred alternative := by
  refine ⟨fun hsocial => ?_,
    hdictator preferred alternative ranks hlinear⟩
  by_contra hnot
  rcases eq_or_ne preferred alternative with hEq | hne
  · subst alternative
    exact (hrational ranks hlinear).irrefl preferred hsocial
  · exact
      (hrational ranks hlinear).asymm hsocial
        (hdictator alternative preferred ranks hlinear
          (((hlinear dictator).not_iff hne).mp hnot))

/-! ## Bridge back to the public weak-ranking statement -/

private theorem strictAggregator_collectivelyRational
    {aggregate : Aggregator Agent α}
    (h : aggregate.IsCollectivelyRational) :
    IsStrictCollectivelyRational (strictAggregatorOf aggregate) := by
  intro ranks hlinear
  apply strictRanking_strict_of_linear
  apply h
  exact fun agent => weakOfStrict_linear (hlinear agent)

private theorem strictAggregator_pareto
    {aggregate : Aggregator Agent α}
    (h : aggregate.IsPareto) :
    IsStrictPareto (strictAggregatorOf aggregate) := by
  intro ranks hlinear preferred alternative hall
  apply h (weakProfileOfStrict ranks)
    (fun agent => weakOfStrict_linear (hlinear agent))
    preferred alternative
  intro agent
  simpa only [weakProfileOfStrict,
    strict_weakOfStrict (hlinear agent)] using hall agent

private theorem strictAggregator_iia
    {aggregate : Aggregator Agent α}
    (h : aggregate.IsIIA) :
    IsStrictIIA (strictAggregatorOf aggregate) := by
  intro ranks ranks' hlinear hlinear' preferred alternative hagree
  apply h (weakProfileOfStrict ranks) (weakProfileOfStrict ranks')
    (fun agent => weakOfStrict_linear (hlinear agent))
    (fun agent => weakOfStrict_linear (hlinear' agent))
    preferred alternative
  intro agent
  simpa only [weakProfileOfStrict,
    strict_weakOfStrict (hlinear agent),
    strict_weakOfStrict (hlinear' agent)] using hagree agent

/-- **Arrow's impossibility theorem.** For a finite nonempty electorate and at
least three alternatives, every collectively rational aggregator satisfying
strict Pareto and independence of irrelevant alternatives on unrestricted
linear-ranking profiles has an exact dictator.

The alternative type need not be finite. The result quantifies over the
canonical weak `Ranking` relation; the strict-order pivotal proof is private and
connected to that relation by `Rank.strict`. -/
theorem impossibility [Nonempty Agent] [Fintype Agent]
    {aggregate : Aggregator Agent α}
    (hrational : aggregate.IsCollectivelyRational)
    (hpareto : aggregate.IsPareto)
    (hiia : aggregate.IsIIA)
    (hα : HasAtLeastThree α) :
    ∃ dictator, aggregate.IsDictator dictator := by
  let strictAggregate := strictAggregatorOf aggregate
  have hstrictRational :
      IsStrictCollectivelyRational strictAggregate :=
    strictAggregator_collectivelyRational hrational
  have hstrictPareto : IsStrictPareto strictAggregate :=
    strictAggregator_pareto hpareto
  have hstrictIIA : IsStrictIIA strictAggregate :=
    strictAggregator_iia hiia
  obtain ⟨dictator, hdictator⟩ :=
    strict_arrow_impossibility hstrictRational hstrictPareto
      hstrictIIA hα
  refine ⟨dictator, ?_⟩
  intro ranks hlinear preferred alternative
  let strictRanks : StrictProfile Agent α :=
    Preference.strict ranks
  have hstrictLinear :
      ∀ agent, StrictRanking (strictRanks agent) :=
    fun agent => strictRanking_strict_of_linear (hlinear agent)
  have hrecover :
      weakProfileOfStrict strictRanks = ranks := by
    funext agent
    exact weakOfStrict_strict_eq (hlinear agent)
  have hexact :=
    strictDictator_exact hstrictRational hdictator hstrictLinear
      preferred alternative
  dsimp only [strictAggregate, strictAggregatorOf] at hexact
  rw [hrecover] at hexact
  simpa only [strictRanks, Preference.strict] using hexact

/-- Finite-cardinality convenience form of Arrow's theorem. -/
theorem impossibility_of_card
    [Nonempty Agent] [Fintype Agent] [Fintype α]
    {aggregate : Aggregator Agent α}
    (hrational : aggregate.IsCollectivelyRational)
    (hpareto : aggregate.IsPareto)
    (hiia : aggregate.IsIIA)
    (hcard : 2 < Fintype.card α) :
    ∃ dictator, aggregate.IsDictator dictator :=
  impossibility hrational hpareto hiia
    (hasAtLeastThree_of_card hcard)

end Arrow

end GameTheory
