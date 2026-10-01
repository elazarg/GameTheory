/-
# von Neumann--Morgenstern representation

Preferences remain the canonical family of weak rankings over ordinary `PMF`.
This file adds the two mixture axioms and the expected-utility representation
theorem; it introduces no second lottery carrier or preference relation.

Primary reference: J. von Neumann and O. Morgenstern, *Theory of Games and
Economic Behavior*, Princeton University Press, 1944.
-/

import GameTheory.Core.ExpectedUtility
import GameTheory.Math.Probability.Conditioning
import Mathlib.Tactic

namespace GameTheory

open GameTheory.Math.Probability

universe ua uo

namespace Preference

variable {Agent : Type ua} {Outcome : Type uo}

/-- Mixing both sides with the same law at a positive weight preserves every
agent's weak comparison. -/
def MixtureIndependent (weaklyPrefers : WeakPreference Agent Outcome) : Prop :=
  ∀ agent first second common (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1),
    weaklyPrefers agent first second ↔
      weaklyPrefers agent
        (mix t hpos.le h1 first common)
        (mix t hpos.le h1 second common)

/-- Certainty-equivalent mixture solvability: every law ranked between two
others is indifferent to a mixture of them. This is the algebraic finite-law
axiom used by the representation proof; it is stronger in presentation than a
bare Archimedean or topological continuity condition, and no equivalence with
those formulations is claimed here. -/
def MixtureContinuous (weaklyPrefers : WeakPreference Agent Outcome) : Prop :=
  ∀ agent best middle worst,
    weaklyPrefers agent best middle → weaklyPrefers agent middle worst →
      ∃ (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1),
        Rank.Indifferent (weaklyPrefers agent) middle
          (mix t h0 h1 best worst)

/-- `utility` represents the weak preference by expected utility, possibly
infinite; a law without an expectation is never ranked. -/
def RepresentsExpectedUtility (weaklyPrefers : WeakPreference Agent Outcome)
    (utility : Outcome → Agent → ℝ) : Prop :=
  ∀ agent preferred alternative,
    weaklyPrefers agent preferred alternative ↔
      euPreference utility agent preferred alternative

namespace RepresentsExpectedUtility

variable {weaklyPrefers : WeakPreference Agent Outcome}
  {utility : Outcome → Agent → ℝ}

theorem total_of_integrable
    (hrep : RepresentsExpectedUtility weaklyPrefers utility)
    (agent : Agent) (first second : PMF Outcome)
    (hfirst : UtilityIntegrable utility agent first)
    (hsecond : UtilityIntegrable utility agent second) :
    weaklyPrefers agent first second ∨ weaklyPrefers agent second first := by
  rcases le_total (expectedUtility utility agent second)
      (expectedUtility utility agent first) with h | h
  · exact Or.inl ((hrep agent first second).mpr
      ((euPreference_iff utility agent first second hfirst hsecond).mpr h))
  · exact Or.inr ((hrep agent second first).mpr
      ((euPreference_iff utility agent second first hsecond hfirst).mpr h))

theorem total (hrep : RepresentsExpectedUtility weaklyPrefers utility)
    (hintegrable : ∀ agent law, UtilityIntegrable utility agent law) :
    Preference.Total weaklyPrefers := by
  intro agent first second
  exact hrep.total_of_integrable agent first second
    (hintegrable agent first) (hintegrable agent second)

theorem transitive (hrep : RepresentsExpectedUtility weaklyPrefers utility) :
    Preference.Transitive weaklyPrefers := by
  intro agent first middle last hfirst hmiddle
  exact (hrep agent first last).mpr
    (euPreference_transitive utility agent first middle last
      ((hrep agent first middle).mp hfirst)
      ((hrep agent middle last).mp hmiddle))

theorem mixtureIndependent_of_integrable
    (hrep : RepresentsExpectedUtility weaklyPrefers utility)
    (agent : Agent) (first second common : PMF Outcome)
    (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1)
    (hfirst : UtilityIntegrable utility agent first)
    (hsecond : UtilityIntegrable utility agent second)
    (hcommon : UtilityIntegrable utility agent common) :
    weaklyPrefers agent first second ↔
      weaklyPrefers agent
        (mix t hpos.le h1 first common)
        (mix t hpos.le h1 second common) := by
  let preferred := mix t hpos.le h1 first common
  let alternative := mix t hpos.le h1 second common
  have hguard (law : PMF Outcome)
      (hlaw : UtilityIntegrable utility agent law) :
      UtilityIntegrable utility agent (mix t hpos.le h1 law common) :=
    payoffIntegrable_mix t hpos.le h1 law common
      (fun outcome => utility outcome agent) hlaw hcommon
  have hvalue (law : PMF Outcome)
      (hlaw : UtilityIntegrable utility agent law) :
      expectedUtility utility agent (mix t hpos.le h1 law common) =
        t * expectedUtility utility agent law +
          (1 - t) * expectedUtility utility agent common :=
    expectedUtility_mix utility agent t hpos.le h1 law common hlaw hcommon
  rw [hrep agent first second, hrep agent preferred alternative]
  rw [euPreference_iff utility agent first second
    hfirst hsecond]
  rw [euPreference_iff utility agent preferred alternative
    (hguard first hfirst) (hguard second hsecond)]
  dsimp only [preferred, alternative]
  rw [hvalue first hfirst, hvalue second hsecond]
  constructor <;> intro h <;> nlinarith

theorem mixtureIndependent (hrep : RepresentsExpectedUtility weaklyPrefers utility)
    (hintegrable : ∀ agent law, UtilityIntegrable utility agent law) :
    MixtureIndependent weaklyPrefers := by
  intro agent first second common t hpos h1
  exact hrep.mixtureIndependent_of_integrable agent first second common t hpos h1
    (hintegrable agent first) (hintegrable agent second) (hintegrable agent common)

/-- Mixture continuity needs integrable laws: with unbounded utility, a best
law worth `+∞` cannot be mixed down to a finite middle law. -/
theorem mixtureContinuous (hrep : RepresentsExpectedUtility weaklyPrefers utility)
    (hintegrable : ∀ agent law, UtilityIntegrable utility agent law) :
    MixtureContinuous weaklyPrefers := by
  intro agent best middle worst hbest hworst
  have hbestGuard := hintegrable agent best
  have hmiddleGuard := hintegrable agent middle
  have hworstGuard := hintegrable agent worst
  have hba := (euPreference_iff utility agent best middle hbestGuard hmiddleGuard).mp
    ((hrep agent best middle).mp hbest)
  have hcb := (euPreference_iff utility agent middle worst hmiddleGuard hworstGuard).mp
    ((hrep agent middle worst).mp hworst)
  let a := expectedUtility utility agent best
  let b := expectedUtility utility agent middle
  let c := expectedUtility utility agent worst
  have hmixGuard (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      UtilityIntegrable utility agent (mix t ht0 ht1 best worst) :=
    payoffIntegrable_mix t ht0 ht1 best worst
      (fun outcome => utility outcome agent) hbestGuard hworstGuard
  have hmix (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      expectedUtility utility agent (mix t ht0 ht1 best worst)
           = t * a + (1 - t) * c :=
    expectedUtility_mix utility agent t ht0 ht1 best worst
      hbestGuard hworstGuard
  have hindiff (law : PMF Outcome) (hlaw : UtilityIntegrable utility agent law)
      (heq : expectedUtility utility agent law = b) :
      Rank.Indifferent (weaklyPrefers agent) middle law := by
    constructor
    · apply (hrep agent middle law).mpr
      apply (euPreference_iff utility agent middle law
        hmiddleGuard hlaw).mpr
      dsimp only [b] at heq
      rw [heq]
    · apply (hrep agent law middle).mpr
      apply (euPreference_iff utility agent law middle
        hlaw hmiddleGuard).mpr
      dsimp only [b] at heq
      rw [heq]
  have hcb' : c ≤ b := hcb
  by_cases hac : a = c
  · refine ⟨0, by norm_num, by norm_num, ?_⟩
    have hba' : b = a := le_antisymm hba (by linarith)
    apply hindiff _ (hmixGuard 0 (by norm_num) (by norm_num))
    rw [hmix]
    linarith
  · have hca : c < a := lt_of_le_of_ne (le_trans hcb' hba) (Ne.symm hac)
    let t := (b - c) / (a - c)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hcb') (sub_nonneg.mpr hca.le)
    have ht1 : t ≤ 1 := by
      dsimp [t]
      rw [div_le_one (sub_pos.mpr hca)]
      linarith
    refine ⟨t, ht0, ht1, ?_⟩
    have hcalc : t * a + (1 - t) * c = b := by
      dsimp [t]
      field_simp [ne_of_gt (sub_pos.mpr hca)]
      ring
    apply hindiff _ (hmixGuard t ht0 ht1)
    rw [hmix]
    exact hcalc

theorem vnmAxioms (hrep : RepresentsExpectedUtility weaklyPrefers utility)
    (hintegrable : ∀ agent law, UtilityIntegrable utility agent law) :
    Preference.Total weaklyPrefers ∧ Preference.Transitive weaklyPrefers ∧
      MixtureIndependent weaklyPrefers ∧ MixtureContinuous weaklyPrefers :=
  ⟨hrep.total hintegrable, hrep.transitive, hrep.mixtureIndependent hintegrable,
    hrep.mixtureContinuous hintegrable⟩

end RepresentsExpectedUtility

/-- Two nondegenerate expected-utility representations with common selected
best and worst outcomes differ by a positive affine transformation for each
agent. The bounds merely say that the selected endpoints bracket every pure
outcome; representation transfers the same ordering to the second utility. -/
theorem representsExpectedUtility_unique_positiveAffine
    {weaklyPrefers : WeakPreference Agent Outcome}
    {first second : Outcome → Agent → ℝ}
    (hfirst : RepresentsExpectedUtility weaklyPrefers first)
    (hsecond : RepresentsExpectedUtility weaklyPrefers second)
    (best worst : Agent → Outcome)
    (hnondegenerate : ∀ agent,
      first (worst agent) agent < first (best agent) agent)
    (hbounds : ∀ agent outcome,
      first (worst agent) agent ≤ first outcome agent ∧
        first outcome agent ≤ first (best agent) agent) :
    ∃ (scale shift : Agent → ℝ),
      (∀ agent, 0 < scale agent) ∧
        ∀ outcome agent,
          second outcome agent =
            scale agent * first outcome agent + shift agent := by
  let scale : Agent → ℝ := fun agent =>
    (second (best agent) agent - second (worst agent) agent) /
      (first (best agent) agent - first (worst agent) agent)
  let shift : Agent → ℝ := fun agent =>
    second (worst agent) agent - scale agent * first (worst agent) agent
  have hsecondGap (agent : Agent) :
      second (worst agent) agent < second (best agent) agent := by
    have hpref : weaklyPrefers agent
        (PMF.pure (best agent)) (PMF.pure (worst agent)) :=
      (hfirst agent _ _).mpr
        ((euPreference_pure_iff first agent _ _).mpr (hnondegenerate agent).le)
    have hnotReverse : ¬ weaklyPrefers agent
        (PMF.pure (worst agent)) (PMF.pure (best agent)) := by
      intro hreverse
      have hle := (euPreference_pure_iff first agent _ _).mp
        ((hfirst agent _ _).mp hreverse)
      exact (not_le_of_gt (hnondegenerate agent)) hle
    have hle := (euPreference_pure_iff second agent _ _).mp
      ((hsecond agent _ _).mp hpref)
    apply lt_of_le_of_ne hle
    intro heq
    apply hnotReverse
    exact (hsecond agent _ _).mpr
      ((euPreference_pure_iff second agent _ _).mpr heq.ge)
  refine ⟨scale, shift, ?_, ?_⟩
  · intro agent
    exact div_pos (sub_pos.mpr (hsecondGap agent))
      (sub_pos.mpr (hnondegenerate agent))
  · intro outcome agent
    let t :=
      (first outcome agent - first (worst agent) agent) /
        (first (best agent) agent - first (worst agent) agent)
    have ht0 : 0 ≤ t :=
      div_nonneg (sub_nonneg.mpr (hbounds agent outcome).1)
        (sub_nonneg.mpr (hnondegenerate agent).le)
    have ht1 : t ≤ 1 := by
      dsimp [t]
      rw [div_le_one (sub_pos.mpr (hnondegenerate agent))]
      linarith [(hbounds agent outcome).2]
    let lottery := mix t ht0 ht1
      (PMF.pure (best agent)) (PMF.pure (worst agent))
    let hfirstLottery : UtilityIntegrable first agent lottery :=
      payoffIntegrable_mix t ht0 ht1 _ _ _
        (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _)
    have hfirstEq :
        expectedUtility first agent lottery =
          first outcome agent := by
      dsimp [lottery]
      rw [expectedUtility_mix first agent t ht0 ht1
        (PMF.pure (best agent)) (PMF.pure (worst agent))
        (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _)]
      simp only [expectedUtility_pure]
      dsimp [t]
      field_simp [ne_of_gt (sub_pos.mpr (hnondegenerate agent))]
      ring
    have hpureLottery : weaklyPrefers agent (PMF.pure outcome) lottery := by
      apply (hfirst agent _ _).mpr
      apply (euPreference_iff first agent _ _
        (payoffIntegrable_pure _ _) hfirstLottery).mpr
      rw [hfirstEq, expectedUtility_pure]
    have hlotteryPure : weaklyPrefers agent lottery (PMF.pure outcome) := by
      apply (hfirst agent _ _).mpr
      apply (euPreference_iff first agent _ _
        hfirstLottery (payoffIntegrable_pure _ _)).mpr
      rw [expectedUtility_pure, hfirstEq]
    let hsecondLottery : UtilityIntegrable second agent lottery :=
      payoffIntegrable_mix t ht0 ht1 _ _ _
        (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _)
    have hsecondLe := (euPreference_iff second agent _ _
      (payoffIntegrable_pure _ _) hsecondLottery).mp
      ((hsecond agent _ _).mp hpureLottery)
    have hsecondGe := (euPreference_iff second agent _ _
      hsecondLottery (payoffIntegrable_pure _ _)).mp
      ((hsecond agent _ _).mp hlotteryPure)
    simp only [expectedUtility_pure] at hsecondLe hsecondGe
    have hsecondEq :
        expectedUtility second agent lottery =
          second outcome agent :=
      le_antisymm hsecondLe hsecondGe
    have hmixEq :
        t * second (best agent) agent +
            (1 - t) * second (worst agent) agent =
          second outcome agent := by
      dsimp only [lottery] at hsecondEq
      rw [expectedUtility_mix second agent t ht0 ht1
        (PMF.pure (best agent)) (PMF.pure (worst agent))
        (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _),
        expectedUtility_pure, expectedUtility_pure] at hsecondEq
      exact hsecondEq
    rw [← hmixEq]
    dsimp [scale, shift, t]
    field_simp [ne_of_gt (sub_pos.mpr (hnondegenerate agent))]
    ring

/-- On a finite nonempty outcome space, callers need only exhibit that the
first representation is nonconstant for each agent.  Global best and worst
endpoints are then selected automatically and the two representations differ
by a positive affine transformation. -/
theorem representsExpectedUtility_unique_positiveAffine_of_finite
    [Finite Outcome] [Nonempty Outcome]
    {weaklyPrefers : WeakPreference Agent Outcome}
    {first second : Outcome → Agent → ℝ}
    (hfirst : RepresentsExpectedUtility weaklyPrefers first)
    (hsecond : RepresentsExpectedUtility weaklyPrefers second)
    (hnonconstant : ∀ agent, ∃ low high,
      first low agent < first high agent) :
    ∃ (scale shift : Agent → ℝ),
      (∀ agent, 0 < scale agent) ∧
        ∀ outcome agent,
          second outcome agent =
            scale agent * first outcome agent + shift agent := by
  let bestWitness : ∀ agent, ∃ best, ∀ outcome,
      first outcome agent ≤ first best agent := fun agent =>
    Finite.exists_max fun outcome => first outcome agent
  let worstWitness : ∀ agent, ∃ worst, ∀ outcome,
      first worst agent ≤ first outcome agent := fun agent =>
    Finite.exists_min fun outcome => first outcome agent
  let best : Agent → Outcome := fun agent => (bestWitness agent).choose
  let worst : Agent → Outcome := fun agent => (worstWitness agent).choose
  apply representsExpectedUtility_unique_positiveAffine hfirst hsecond best worst
  · intro agent
    obtain ⟨low, high, hlowHigh⟩ := hnonconstant agent
    exact lt_of_le_of_lt ((worstWitness agent).choose_spec low)
      (lt_of_lt_of_le hlowHigh ((bestWitness agent).choose_spec high))
  · intro agent outcome
    exact ⟨(worstWitness agent).choose_spec outcome,
      (bestWitness agent).choose_spec outcome⟩

namespace VNMProof

variable {pref : PMF Outcome → PMF Outcome → Prop}

private theorem indifferent_mix_common
    (hindependent : ∀ first second common (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1),
      pref first second ↔
        pref (mix t hpos.le h1 first common)
          (mix t hpos.le h1 second common))
    {first second common : PMF Outcome} {t : ℝ}
    (hpos : 0 < t) (h1 : t ≤ 1) (h : Rank.Indifferent pref first second) :
    Rank.Indifferent pref (mix t hpos.le h1 first common)
      (mix t hpos.le h1 second common) :=
  ⟨(hindependent first second common t hpos h1).mp h.1,
    (hindependent second first common t hpos h1).mp h.2⟩

private theorem indifferent_mix
    (htrans : Rank.Transitive pref)
    (hindependent : ∀ first second common (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1),
      pref first second ↔
        pref (mix t hpos.le h1 first common)
          (mix t hpos.le h1 second common))
    {first first' second second' : PMF Outcome}
    {t : ℝ} (hpos : 0 < t) (hlt : t < 1)
    (hfirst : Rank.Indifferent pref first first')
    (hsecond : Rank.Indifferent pref second second') :
    Rank.Indifferent pref (mix t hpos.le hlt.le first second)
      (mix t hpos.le hlt.le first' second') := by
  have hchangeFirst := indifferent_mix_common hindependent hpos hlt.le
    (common := second) hfirst
  have hchangeSecond := indifferent_mix_common hindependent
    (t := 1 - t) (by linarith) (by linarith) (common := first') hsecond
  rw [mix_swap t hpos.le hlt.le first' second,
    mix_swap t hpos.le hlt.le first' second'] at hchangeSecond
  exact
    ⟨htrans _ _ _ hchangeFirst.1 hchangeSecond.1,
      htrans _ _ _ hchangeSecond.2 hchangeFirst.2⟩

/-- The support-induction consequence of binary independence. -/
private theorem compoundIndifferent
    {Index : Type*}
    (htrans : Rank.Transitive pref)
    (hindependent : ∀ first second common (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1),
      pref first second ↔
        pref (mix t hpos.le h1 first common)
          (mix t hpos.le h1 second common))
    (outer : PMF Index) (hfinite : outer.support.Finite)
    (first second : Index → PMF Outcome)
    (hlocal : ∀ outcome ∈ outer.support,
      Rank.Indifferent pref (first outcome) (second outcome)) :
    Rank.Indifferent pref (outer.bind first) (outer.bind second) := by
  classical
  have lift : ∀ support : Finset Index, ∀ law : PMF Index,
      law.support ⊆ (support : Set Index) →
      ∀ left right : Index → PMF Outcome,
        (∀ outcome ∈ law.support,
          Rank.Indifferent pref (left outcome) (right outcome)) →
        Rank.Indifferent pref (law.bind left) (law.bind right) := by
    intro support
    induction support using Finset.induction_on with
    | empty =>
        intro law hsupport
        obtain ⟨outcome, houtcome⟩ := law.support_nonempty
        exact False.elim (by simpa using hsupport houtcome)
    | @insert outcome support _ ih =>
        intro law hsupport left right hbranches
        by_cases houtcome : outcome ∈ law.support
        · by_cases hrest : ∃ other ∈ ({outcome}ᶜ : Set Index), other ∈ law.support
          · let tail := law.filter ({outcome}ᶜ : Set Index) hrest
            have htailSubset : tail.support ⊆ (support : Set Index) := by
              intro other hother
              have hkept := (PMF.mem_support_filter_iff hrest).mp hother
              have hinsert := hsupport hkept.2
              rw [Finset.coe_insert, Set.mem_insert_iff] at hinsert
              exact hinsert.resolve_left (by simpa using hkept.1)
            have htailBranches : ∀ other ∈ tail.support,
                Rank.Indifferent pref (left other) (right other) := by
              intro other hother
              exact hbranches other ((PMF.mem_support_filter_iff hrest).mp hother).2
            have htail := ih tail htailSubset left right htailBranches
            obtain ⟨t, ht0, ht1, hsplit⟩ :=
              exists_mix_pure_filter law outcome houtcome hrest
            rw [hsplit, mix_bind, PMF.pure_bind, mix_bind, PMF.pure_bind]
            exact indifferent_mix htrans hindependent ht0 ht1
              (hbranches outcome houtcome) htail
          · have hsingleton : law.support ⊆ ({outcome} : Set Index) := by
              intro other hother
              by_contra hne
              exact hrest ⟨other, by simpa using hne, hother⟩
            have hlaw : law = PMF.pure outcome := by
              have hsupp : law.support = {outcome} :=
                Set.Subset.antisymm hsingleton (Set.singleton_subset_iff.mpr houtcome)
              have hmass : law outcome = 1 := (law.apply_eq_one_iff outcome).mpr hsupp
              ext other
              by_cases hother : other = outcome
              · subst other
                simpa using hmass
              · have hzero : law other = 0 := by
                  apply not_ne_iff.mp
                  intro hne
                  exact hother (Set.mem_singleton_iff.mp (hsingleton
                    ((law.mem_support_iff other).mpr hne)))
                simp [hzero, PMF.pure_apply, hother]
            rw [hlaw, PMF.pure_bind, PMF.pure_bind]
            exact hbranches outcome houtcome
        · apply ih law _ left right hbranches
          intro other hother
          have hinsert := hsupport hother
          rw [Finset.coe_insert, Set.mem_insert_iff] at hinsert
          exact hinsert.resolve_left fun heq => by
            subst other
            exact houtcome hother
  exact lift hfinite.toFinset outer (by
    intro outcome houtcome
    simpa using houtcome) first second hlocal

private noncomputable def standardLottery (best worst : Outcome) (t : ℝ)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : PMF Outcome :=
  mix t h0 h1 (PMF.pure best) (PMF.pure worst)

private theorem standardLottery_zero (best worst : Outcome) :
    standardLottery best worst 0 le_rfl (by norm_num) = PMF.pure worst := by
  simp [standardLottery]

private theorem standardLottery_one (best worst : Outcome) :
    standardLottery best worst 1 (by norm_num) le_rfl = PMF.pure best := by
  simp [standardLottery]

private theorem standardLottery_eq_mix_best_standard
    (best worst : Outcome) {s t : ℝ}
    (ht0 : 0 ≤ t) (hst : t ≤ s) (hs1 : s ≤ 1) (ht1 : t < 1) :
    standardLottery best worst s (le_trans ht0 hst) hs1 =
      mix ((s - t) / (1 - t))
        (div_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr ht1.le))
        (by rw [div_le_one (sub_pos.mpr ht1)]; linarith)
        (PMF.pure best)
        (standardLottery best worst t ht0 ht1.le) := by
  let q := (s - t) / (1 - t)
  have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr ht1.le)
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [div_le_one (sub_pos.mpr ht1)]
    linarith
  have hsq : q + (1 - q) * t = s := by
    dsimp [q]
    field_simp [ne_of_gt (sub_pos.mpr ht1)]
    ring
  simpa only [standardLottery, hsq] using
    (mix_assoc_left q t hq0 hq1 ht0 ht1.le
      (PMF.pure best) (PMF.pure worst))

private theorem standardLottery_order
    (htotal : Rank.Total pref) (hindependent :
      ∀ first second common (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1),
        pref first second ↔
          pref (mix t hpos.le h1 first common)
            (mix t hpos.le h1 second common))
    {best worst : Outcome} (hbestWorst : pref (PMF.pure best) (PMF.pure worst))
    (hnotWorstBest : ¬ pref (PMF.pure worst) (PMF.pure best))
    (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    pref (standardLottery best worst s hs0 hs1)
      (standardLottery best worst t ht0 ht1) ↔ t ≤ s := by
  have hrefl : ∀ law : PMF Outcome, pref law law :=
    fun law => (htotal law law).elim id id
  have hbestStandard : ∀ (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1),
      pref (PMF.pure best) (standardLottery best worst q hq0 hq1) := by
    intro q hq0 hq1
    rcases hq1.eq_or_lt with hq | hq
    · subst q
      rw [standardLottery_one]
      exact hrefl _
    · have hweight : 0 < 1 - q := sub_pos.mpr hq
      have hmix : mix (1 - q) hweight.le (by linarith)
          (PMF.pure worst) (PMF.pure best) =
          standardLottery best worst q hq0 hq1 := by
        exact mix_swap q hq0 hq1
          (PMF.pure best) (PMF.pure worst)
      have h := (hindependent (PMF.pure best) (PMF.pure worst)
        (PMF.pure best) (1 - q) hweight (by linarith)).mp hbestWorst
      simpa [hmix] using h
  constructor
  · intro hpref
    by_contra hnot
    have hst : s < t := lt_of_not_ge hnot
    have hs1lt : s < 1 := lt_of_lt_of_le hst ht1
    let a := (t - s) / (1 - s)
    have haPos : 0 < a := div_pos (sub_pos.mpr hst) (sub_pos.mpr hs1lt)
    have ha1 : a ≤ 1 := by
      dsimp [a]
      rw [div_le_one (sub_pos.mpr hs1lt)]
      linarith
    have hmixT : standardLottery best worst t (le_trans hs0 hst.le) ht1 =
        mix a haPos.le ha1 (PMF.pure best)
          (standardLottery best worst s hs0 hs1lt.le) := by
      exact standardLottery_eq_mix_best_standard best worst hs0 hst.le ht1 hs1lt
    have hbase : pref (standardLottery best worst s hs0 hs1lt.le)
        (PMF.pure best) := by
      apply (hindependent (standardLottery best worst s hs0 hs1lt.le)
        (PMF.pure best) (standardLottery best worst s hs0 hs1lt.le)
        a haPos ha1).mpr
      simpa [hmixT] using hpref
    rcases hs0.eq_or_lt with hs | hs
    · subst s
      rw [standardLottery_zero] at hbase
      exact hnotWorstBest hbase
    · have hweight : 0 < 1 - s := sub_pos.mpr hs1lt
      have hmix : mix (1 - s) hweight.le (by linarith)
          (PMF.pure worst) (PMF.pure best) =
          standardLottery best worst s hs0 hs1 := by
        exact mix_swap s hs0 hs1
          (PMF.pure best) (PMF.pure worst)
      have hworstBest := (hindependent (PMF.pure worst) (PMF.pure best)
        (PMF.pure best) (1 - s) hweight (by linarith)).mpr (by
          simpa [hmix] using hbase)
      exact hnotWorstBest hworstBest
  · intro hts
    rcases hts.eq_or_lt with hts | hts
    · subst s
      exact hrefl _
    · have htlt : t < 1 := lt_of_lt_of_le hts hs1
      let a := (s - t) / (1 - t)
      have haPos : 0 < a := div_pos (sub_pos.mpr hts) (sub_pos.mpr htlt)
      have ha1 : a ≤ 1 := by
        dsimp [a]
        rw [div_le_one (sub_pos.mpr htlt)]
        linarith
      have hmixS : standardLottery best worst s (le_trans ht0 hts.le) hs1 =
          mix a haPos.le ha1 (PMF.pure best)
            (standardLottery best worst t ht0 htlt.le) := by
        exact standardLottery_eq_mix_best_standard best worst ht0 hts.le hs1 htlt
      have h := (hindependent (PMF.pure best)
        (standardLottery best worst t ht0 htlt.le)
        (standardLottery best worst t ht0 htlt.le) a haPos ha1).mp
          (hbestStandard t ht0 htlt.le)
      simpa [hmixS] using h

private theorem expect_nonneg_of_nonneg
    (law : PMF Outcome) {u : Outcome → ℝ}
    (hu : ∀ outcome, 0 ≤ u outcome) : 0 ≤ expect law u :=
  expect_nonneg law u
    (fun outcome _ => hu outcome)

private theorem expect_le_one_of_le_one [Finite Outcome]
    (law : PMF Outcome) {u : Outcome → ℝ}
    (hu : ∀ outcome, u outcome ≤ 1) : expect law u ≤ 1 :=
  expect_le_const law u (payoffIntegrable_of_finite law u) 1
    (fun outcome _ => hu outcome)

private theorem bind_standardLottery_eq_standard_expect
    [Finite Outcome] {best worst : Outcome}
    (law : PMF Outcome) (u : Outcome → ℝ)
    (hu0 : ∀ outcome, 0 ≤ u outcome) (hu1 : ∀ outcome, u outcome ≤ 1) :
    law.bind (fun outcome => standardLottery best worst (u outcome)
      (hu0 outcome) (hu1 outcome)) =
      standardLottery best worst (expect law u)
        (expect_nonneg_of_nonneg law hu0) (expect_le_one_of_le_one law hu1) := by
  simpa only [standardLottery] using
    (bind_mix_expect law u hu0 hu1 (PMF.pure best) (PMF.pure worst))

private theorem existsMaximalStrict {α : Type*} [Finite α] [Nonempty α]
    (strict : α → α → Prop)
    (htrans : ∀ a b c, strict a b → strict b c → strict a c)
    (hirrefl : ∀ a, ¬ strict a a) :
    ∃ maximal : α, ∀ other, ¬ strict other maximal := by
  classical
  let : IsTrans α strict := ⟨htrans⟩
  let : Std.Irrefl strict := ⟨hirrefl⟩
  have hwf : WellFounded strict := Finite.wellFounded_of_trans_of_irrefl strict
  let P : α → Prop := fun start =>
    ∃ maximal, (∀ other, ¬ strict other maximal) ∧
      (maximal = start ∨ strict maximal start)
  have hP : ∀ start, P start := fun start => hwf.induction start (C := P) fun current ih => by
    by_cases hbetter : ∃ other, strict other current
    · obtain ⟨other, hother⟩ := hbetter
      obtain ⟨maximal, hmaximal, hrelation⟩ := ih other hother
      refine ⟨maximal, hmaximal, ?_⟩
      rcases hrelation with rfl | hrelation
      · exact Or.inr hother
      · exact Or.inr (htrans maximal other current hrelation hother)
    · exact ⟨current, fun other h => hbetter ⟨other, h⟩, Or.inl rfl⟩
  obtain ⟨start⟩ := (inferInstance : Nonempty α)
  obtain ⟨maximal, hmaximal, _⟩ := hP start
  exact ⟨maximal, hmaximal⟩

private theorem existsGreatestFinite {α : Type*} [Finite α] [Nonempty α]
    (ranks : α → α → Prop)
    (htotal : Rank.Total ranks) (htrans : Rank.Transitive ranks) :
    ∃ greatest, ∀ other, ranks greatest other := by
  obtain ⟨greatest, hgreatest⟩ := existsMaximalStrict (Rank.strict ranks)
    (fun _ _ _ hfirst hsecond => Rank.strict_trans htrans hfirst hsecond.1)
    (Rank.strict_irrefl ranks)
  refine ⟨greatest, fun other => ?_⟩
  rcases htotal greatest other with h | h
  · exact h
  · by_contra hnot
    exact hgreatest other ⟨h, hnot⟩

private theorem existsLeastFinite {α : Type*} [Finite α] [Nonempty α]
    (ranks : α → α → Prop)
    (htotal : Rank.Total ranks) (htrans : Rank.Transitive ranks) :
    ∃ least, ∀ other, ranks other least := by
  let reverse : α → α → Prop := fun first second => ranks second first
  have htotalReverse : Rank.Total reverse := fun first second => (htotal first second).symm
  have htransReverse : Rank.Transitive reverse :=
    fun first middle last hfirst hmiddle => htrans last middle first hmiddle hfirst
  simpa [reverse] using existsGreatestFinite reverse htotalReverse htransReverse

private theorem representsExpectedUtility_of_certaintyEquivalents
    [Finite Outcome]
    (htrans : Rank.Transitive pref)
    (hindependent : ∀ first second common (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1),
      pref first second ↔
        pref (mix t hpos.le h1 first common)
          (mix t hpos.le h1 second common))
    {best worst : Outcome} (u : Outcome → ℝ)
    (hu0 : ∀ outcome, 0 ≤ u outcome) (hu1 : ∀ outcome, u outcome ≤ 1)
    (hpure : ∀ outcome, Rank.Indifferent pref (PMF.pure outcome)
      (standardLottery best worst (u outcome) (hu0 outcome) (hu1 outcome)))
    (hstandard : ∀ (s t : ℝ)
      (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
        pref (standardLottery best worst s hs0 hs1)
          (standardLottery best worst t ht0 ht1) ↔ t ≤ s) :
    ∀ preferred alternative, pref preferred alternative ↔
      expect alternative u ≤ expect preferred u := by
  intro preferred alternative
  let std (law : PMF Outcome) := standardLottery best worst (expect law u)
    (expect_nonneg_of_nonneg law hu0) (expect_le_one_of_le_one law hu1)
  have hstdIndifferent : ∀ law : PMF Outcome, Rank.Indifferent pref law (std law) := by
    intro law
    have h := compoundIndifferent htrans hindependent law (Set.toFinite _)
      (fun outcome => PMF.pure outcome)
      (fun outcome => standardLottery best worst (u outcome) (hu0 outcome) (hu1 outcome))
      (fun outcome _ => hpure outcome)
    simpa [std, bind_standardLottery_eq_standard_expect] using h
  constructor
  · intro hpref
    have hpreferred := hstdIndifferent preferred
    have halternative := hstdIndifferent alternative
    have hstd : pref (std preferred) (std alternative) :=
      htrans _ preferred _ hpreferred.2
        (htrans preferred alternative _ hpref halternative.1)
    exact (hstandard (expect preferred u) (expect alternative u)
      (expect_nonneg_of_nonneg preferred hu0) (expect_le_one_of_le_one preferred hu1)
      (expect_nonneg_of_nonneg alternative hu0) (expect_le_one_of_le_one alternative hu1)).mp hstd
  · intro hexpect
    have hpreferred := hstdIndifferent preferred
    have halternative := hstdIndifferent alternative
    have hstd : pref (std preferred) (std alternative) :=
      (hstandard (expect preferred u) (expect alternative u)
        (expect_nonneg_of_nonneg preferred hu0) (expect_le_one_of_le_one preferred hu1)
        (expect_nonneg_of_nonneg alternative hu0)
        (expect_le_one_of_le_one alternative hu1)).mpr hexpect
    exact htrans preferred (std preferred) alternative hpreferred.1
      (htrans (std preferred) (std alternative) alternative hstd halternative.2)

private theorem exists_representsExpectedUtility_pointwise
    [Finite Outcome] [Nonempty Outcome]
    (htotal : Rank.Total pref) (htrans : Rank.Transitive pref)
    (hindependent : ∀ first second common (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1),
      pref first second ↔
        pref (mix t hpos.le h1 first common)
          (mix t hpos.le h1 second common))
    (hcontinuous : ∀ best middle worst,
      pref best middle → pref middle worst →
        ∃ (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1),
          Rank.Indifferent pref middle (mix t h0 h1 best worst)) :
    ∃ u : Outcome → ℝ, ∀ preferred alternative,
      pref preferred alternative ↔
        expect alternative u ≤ expect preferred u := by
  classical
  let pureRanks : Outcome → Outcome → Prop :=
    fun first second => pref (PMF.pure first) (PMF.pure second)
  have hpureTotal : Rank.Total pureRanks := fun first second =>
    htotal (PMF.pure first) (PMF.pure second)
  have hpureTransitive : Rank.Transitive pureRanks :=
    fun first middle last => htrans (PMF.pure first) (PMF.pure middle)
      (PMF.pure last)
  obtain ⟨best, hbest⟩ := existsGreatestFinite pureRanks hpureTotal hpureTransitive
  obtain ⟨worst, hworst⟩ := existsLeastFinite pureRanks hpureTotal hpureTransitive
  by_cases hdegenerate : pref (PMF.pure worst) (PMF.pure best)
  · refine ⟨fun _ => 0, ?_⟩
    have hpureBest : ∀ outcome,
        Rank.Indifferent pref (PMF.pure outcome) (PMF.pure best) := by
      intro outcome
      exact ⟨htrans _ (PMF.pure worst) _ (hworst outcome) hdegenerate,
        hbest outcome⟩
    have hlawBest : ∀ law : PMF Outcome,
        Rank.Indifferent pref law (PMF.pure best) := by
      intro law
      have h := compoundIndifferent htrans hindependent law (Set.toFinite _)
        (fun outcome => PMF.pure outcome) (fun _ => PMF.pure best)
        (fun outcome _ => hpureBest outcome)
      simpa using h
    have hzero (law : PMF Outcome) : expect law (fun _ => 0) = 0 :=
      expect_constant law 0
    intro preferred alternative
    constructor
    · intro _
      simp [hzero]
    · intro _
      exact htrans preferred (PMF.pure best) alternative
        (hlawBest preferred).1 (hlawBest alternative).2
  · have hbestWorst : pref (PMF.pure best) (PMF.pure worst) := hbest worst
    have hce : ∀ outcome : Outcome,
        ∃ (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1),
          Rank.Indifferent pref (PMF.pure outcome)
            (standardLottery best worst t h0 h1) := by
      intro outcome
      exact hcontinuous (PMF.pure best) (PMF.pure outcome)
        (PMF.pure worst) (hbest outcome) (hworst outcome)
    let u : Outcome → ℝ := fun outcome => (hce outcome).choose
    have hu0 : ∀ outcome, 0 ≤ u outcome := fun outcome =>
      (hce outcome).choose_spec.choose
    have hu1 : ∀ outcome, u outcome ≤ 1 := fun outcome =>
      (hce outcome).choose_spec.choose_spec.choose
    have hpure : ∀ outcome, Rank.Indifferent pref (PMF.pure outcome)
        (standardLottery best worst (u outcome) (hu0 outcome) (hu1 outcome)) :=
      fun outcome => (hce outcome).choose_spec.choose_spec.choose_spec
    exact ⟨u, representsExpectedUtility_of_certaintyEquivalents htrans hindependent
      u hu0 hu1 hpure
      (standardLottery_order htotal hindependent hbestWorst hdegenerate)⟩

/-! ### Finitely supported lotteries over an arbitrary outcome type -/

/-- `utility` represents `pref` on the lotteries supported in `support`. -/
private def RepresentsOn (pref : PMF Outcome → PMF Outcome → Prop)
    (support : Finset Outcome) (utility : Outcome → ℝ) : Prop :=
  ∀ preferred alternative : PMF Outcome,
    preferred.support ⊆ support → alternative.support ⊆ support →
      (pref preferred alternative ↔ expect alternative utility ≤ expect preferred utility)

private theorem RepresentsOn.mono {support larger : Finset Outcome} {utility : Outcome → ℝ}
    (hrep : RepresentsOn pref larger utility) (hsubset : support ⊆ larger) :
    RepresentsOn pref support utility :=
  fun preferred alternative hpreferred halternative =>
    hrep preferred alternative (hpreferred.trans (Finset.coe_subset.2 hsubset))
      (halternative.trans (Finset.coe_subset.2 hsubset))

private theorem support_mix_pure_subset {first second : Outcome} (t : ℝ) (h0 : 0 ≤ t)
    (h1 : t ≤ 1) :
    (mix t h0 h1 (PMF.pure first) (PMF.pure second)).support ⊆ {first, second} := by
  intro outcome houtcome
  rw [PMF.mem_support_iff, mix_apply] at houtcome
  by_contra hnot
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
  simp [PMF.pure_apply, hnot.1, hnot.2] at houtcome

private theorem expect_mix_pure (f : Outcome → ℝ) (first second : Outcome) (t : ℝ)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    expect (mix t h0 h1 (PMF.pure first) (PMF.pure second)) f =
      t * f first + (1 - t) * f second := by
  rw [expect_mix t h0 h1 _ _ f (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _),
    expect_pure, expect_pure]

/-- On every finite nonempty outcome set the axioms give a representation of
the lotteries supported there. -/
private theorem exists_representsOn
    (htotal : Rank.Total pref) (htrans : Rank.Transitive pref)
    (hindependent : ∀ first second common (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1),
      pref first second ↔
        pref (mix t hpos.le h1 first common)
          (mix t hpos.le h1 second common))
    (hcontinuous : ∀ best middle worst,
      pref best middle → pref middle worst →
        ∃ (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1),
          Rank.Indifferent pref middle (mix t h0 h1 best worst))
    (support : Finset Outcome) (hnonempty : support.Nonempty) :
    ∃ utility : Outcome → ℝ, RepresentsOn pref support utility := by
  classical
  obtain ⟨point, hpoint⟩ := hnonempty
  let restricted : PMF support → PMF support → Prop := fun first second =>
    pref (first.map Subtype.val) (second.map Subtype.val)
  have : Nonempty support := ⟨⟨point, hpoint⟩⟩
  obtain ⟨siteUtility, hsite⟩ := exists_representsExpectedUtility_pointwise (pref := restricted)
    (fun first second => htotal _ _)
    (fun first middle last hfirst hlast => htrans _ _ _ hfirst hlast)
    (fun first second common t hpos h1 => by
      simp only [restricted, mix_map]
      exact hindependent _ _ _ t hpos h1)
    (fun best middle worst hbest hworst => by
      obtain ⟨t, h0, h1, hindifferent⟩ := hcontinuous _ _ _ hbest hworst
      exact ⟨t, h0, h1, by simpa only [Rank.Indifferent, restricted, mix_map] using hindifferent⟩)
  let project : Outcome → support := fun outcome =>
    if houtcome : outcome ∈ support then ⟨outcome, houtcome⟩ else ⟨point, hpoint⟩
  have hround (law : PMF Outcome) (hlaw : law.support ⊆ support) :
      (law.map project).map Subtype.val = law := by
    rw [PMF.map_comp]
    conv_rhs => rw [← PMF.map_id law]
    apply map_congr_on_support
    intro outcome houtcome
    have hmem : outcome ∈ support := hlaw houtcome
    simp [project, hmem]
  refine ⟨fun outcome => siteUtility (project outcome), fun preferred alternative hpreferred
    halternative => ?_⟩
  have h := hsite (preferred.map project) (alternative.map project)
  simp only [restricted, hround preferred hpreferred, hround alternative halternative,
    expect_map] at h
  exact h

/-- Two representations of the lotteries over a set holding a strictly ranked
pair normalize every outcome of the set alike. -/
private theorem normalized_eq_of_representsOn {support : Finset Outcome}
    {first second : Outcome → ℝ}
    (hfirst : RepresentsOn pref support first) (hsecond : RepresentsOn pref support second)
    {best worst outcome : Outcome} (hbest : best ∈ support) (hworst : worst ∈ support)
    (houtcome : outcome ∈ support)
    (hstrict : ¬ pref (PMF.pure worst) (PMF.pure best)) :
    (first outcome - first worst) / (first best - first worst) =
      (second outcome - second worst) / (second best - second worst) := by
  have hpure (point : Outcome) (hmem : point ∈ support) :
      (PMF.pure point).support ⊆ support := by
    rw [PMF.support_pure, Set.singleton_subset_iff]
    exact hmem
  have hmix {left right : Outcome} (hleft : left ∈ support) (hright : right ∈ support)
      (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
      (mix t h0 h1 (PMF.pure left) (PMF.pure right)).support ⊆ support := by
    refine (support_mix_pure_subset t h0 h1).trans ?_
    intro point hpoint
    rcases hpoint with rfl | rfl
    · exact hleft
    · exact hright
  have htransfer {preferred alternative : PMF Outcome} (hpreferred : preferred.support ⊆ support)
      (halternative : alternative.support ⊆ support)
      (hequal : expect preferred first = expect alternative first) :
      expect preferred second = expect alternative second := by
    have hforward := (hfirst preferred alternative hpreferred halternative).2 hequal.ge
    have hbackward := (hfirst alternative preferred halternative hpreferred).2 hequal.le
    exact le_antisymm ((hsecond alternative preferred halternative hpreferred).1 hbackward)
      ((hsecond preferred alternative hpreferred halternative).1 hforward)
  have hgap (utility : Outcome → ℝ) (hrep : RepresentsOn pref support utility) :
      utility worst < utility best := by
    by_contra hle
    apply hstrict
    rw [hrep _ _ (hpure worst hworst) (hpure best hbest), expect_pure, expect_pure]
    exact not_lt.1 hle
  have hfirstGap := sub_pos.2 (hgap first hfirst)
  have hsecondGap := sub_pos.2 (hgap second hsecond)
  set t := (first outcome - first worst) / (first best - first worst) with ht
  have hfirstOutcome : first outcome = first worst + t * (first best - first worst) := by
    rw [ht]
    field_simp
    ring
  rcases le_or_gt t 1 with hle | hgt
  · rcases le_or_gt 0 t with hge | hlt
    · -- `outcome` is indifferent to the mixture of `best` and `worst` at `t`.
      have h := htransfer (hpure outcome houtcome) (hmix hbest hworst t hge hle)
        (by rw [expect_pure, expect_mix_pure, hfirstOutcome]; ring)
      rw [expect_pure, expect_mix_pure] at h
      rw [h]
      field_simp
      ring
    · -- `worst` is indifferent to a mixture of `best` and `outcome`.
      have hone : 0 < 1 - t := by linarith
      set s := -t / (1 - t) with hs
      have hs0 : 0 ≤ s := div_nonneg (by linarith) hone.le
      have hs1 : s ≤ 1 := by rw [hs, div_le_one hone]; linarith
      have h := htransfer (hmix hbest houtcome s hs0 hs1) (hpure worst hworst)
        (by rw [expect_pure, expect_mix_pure, hfirstOutcome, hs]; field_simp; ring)
      rw [expect_pure, expect_mix_pure] at h
      have hsecondOutcome : second outcome =
          second worst - s * (second best - second worst) / (1 - s) := by
        have hslt : s < 1 := by rw [hs, div_lt_one hone]; linarith
        have hsone : 1 - s ≠ 0 := (sub_pos.2 hslt).ne'
        field_simp
        linarith
      rw [hsecondOutcome, hs]
      field_simp
      ring
  · -- `best` is indifferent to a mixture of `outcome` and `worst`.
    have htpos : 0 < t := by linarith
    set s := 1 / t with hs
    have hs0 : 0 ≤ s := by positivity
    have hs1 : s ≤ 1 := by rw [hs, div_le_one htpos]; exact hgt.le
    have h := htransfer (hmix houtcome hworst s hs0 hs1) (hpure best hbest)
      (by rw [expect_pure, expect_mix_pure, hfirstOutcome, hs]; field_simp; ring)
    rw [expect_pure, expect_mix_pure] at h
    have hsecondOutcome : second outcome =
        second worst + (second best - second worst) / s := by
      have hspos : 0 < s := by positivity
      field_simp
      linarith
    rw [hsecondOutcome, hs]
    field_simp
    ring

/-- The vNM axioms represent the preference on every finitely supported
lottery, whatever the outcome type. -/
private theorem exists_representsOnFiniteSupport_pointwise
    (htotal : Rank.Total pref) (htrans : Rank.Transitive pref)
    (hindependent : ∀ first second common (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1),
      pref first second ↔
        pref (mix t hpos.le h1 first common)
          (mix t hpos.le h1 second common))
    (hcontinuous : ∀ best middle worst,
      pref best middle → pref middle worst →
        ∃ (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1),
          Rank.Indifferent pref middle (mix t h0 h1 best worst)) :
    ∃ utility : Outcome → ℝ, ∀ preferred alternative : PMF Outcome,
      preferred.support.Finite → alternative.support.Finite →
        (pref preferred alternative ↔
          expect alternative utility ≤ expect preferred utility) := by
  classical
  by_cases hdegenerate : ∀ best worst : Outcome, pref (PMF.pure worst) (PMF.pure best)
  · refine ⟨fun _ => 0, fun preferred alternative hpreferred halternative => ?_⟩
    obtain ⟨anchor, -⟩ := preferred.support_nonempty
    have hanchor (law : PMF Outcome) (hlaw : law.support.Finite) :
        Rank.Indifferent pref law (PMF.pure anchor) := by
      have h := compoundIndifferent htrans hindependent law hlaw
        (fun outcome => PMF.pure outcome) (fun _ => PMF.pure anchor)
        (fun outcome _ => ⟨hdegenerate anchor outcome, hdegenerate outcome anchor⟩)
      simpa using h
    simp only [expect_constant, le_refl, iff_true]
    exact htrans _ _ _ (hanchor preferred hpreferred).1 (hanchor alternative halternative).2
  push Not at hdegenerate
  obtain ⟨best, worst, hstrict⟩ := hdegenerate
  have hlocal (outcome : Outcome) : ∃ utility : Outcome → ℝ,
      RepresentsOn pref {best, worst, outcome} utility :=
    exists_representsOn htotal htrans hindependent hcontinuous _ ⟨best, by simp⟩
  choose triple htriple using hlocal
  refine ⟨fun outcome => (triple outcome outcome - triple outcome worst) /
    (triple outcome best - triple outcome worst), fun preferred alternative hpreferred
      halternative => ?_⟩
  let support : Finset Outcome :=
    hpreferred.toFinset ∪ halternative.toFinset ∪ {best, worst}
  have hbest : best ∈ support := by simp [support]
  have hworst : worst ∈ support := by simp [support]
  obtain ⟨joint, hjoint⟩ :=
    exists_representsOn htotal htrans hindependent hcontinuous support ⟨best, hbest⟩
  have hpreferredSub : preferred.support ⊆ support := by
    intro outcome houtcome
    simp [support, houtcome]
  have halternativeSub : alternative.support ⊆ support := by
    intro outcome houtcome
    simp [support, houtcome]
  have hgap : 0 < joint best - joint worst := by
    apply sub_pos.2
    by_contra hle
    apply hstrict
    have hpure (point : Outcome) (hmem : point ∈ support) :
        (PMF.pure point).support ⊆ support := by
      rw [PMF.support_pure, Set.singleton_subset_iff]
      exact hmem
    rw [hjoint _ _ (hpure worst hworst) (hpure best hbest), expect_pure, expect_pure]
    exact not_lt.1 hle
  let normalized : Outcome → ℝ := fun outcome =>
    (joint best - joint worst)⁻¹ * (joint outcome - joint worst)
  have hagree (outcome : Outcome) (houtcome : outcome ∈ support) :
      (triple outcome outcome - triple outcome worst) /
          (triple outcome best - triple outcome worst) = normalized outcome := by
    have hsub : ({best, worst, outcome} : Finset Outcome) ⊆ support := by
      intro point hpoint
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpoint
      rcases hpoint with rfl | rfl | rfl
      · exact hbest
      · exact hworst
      · exact houtcome
    rw [normalized_eq_of_representsOn (htriple outcome) ((hjoint).mono hsub)
      (by simp) (by simp) (by simp) hstrict]
    simp only [normalized]
    field_simp
  have hexpect (law : PMF Outcome) (hlaw : law.support ⊆ support) :
      expect law (fun outcome => (triple outcome outcome - triple outcome worst) /
        (triple outcome best - triple outcome worst)) =
        (joint best - joint worst)⁻¹ * (expect law joint - joint worst) := by
    have hfinite : law.support.Finite := (Finset.finite_toSet support).subset hlaw
    rw [expect_congr_on_support (fun outcome houtcome => hagree outcome (hlaw houtcome)),
      expect_const_mul, expect_sub (payoffIntegrable_of_finite_support law _ hfinite)
        (payoffIntegrable_constant law _), expect_constant]
  rw [hjoint preferred alternative hpreferredSub halternativeSub,
    hexpect preferred hpreferredSub, hexpect alternative halternativeSub]
  constructor
  · intro hle
    exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hgap.le)
  · intro hle
    have := le_of_mul_le_mul_left hle (inv_pos.2 hgap)
    linarith

end VNMProof

/-- Binary mixture independence permits substitution of indifferent branches
under a finitely supported outer lottery. Branch laws need no finite support. -/
theorem MixtureIndependent.indifferent_bind_of_finite_support
    {Index : Type*} {weaklyPrefers : WeakPreference Agent Outcome}
    (hindependent : MixtureIndependent weaklyPrefers) (agent : Agent)
    (htrans : Rank.Transitive (weaklyPrefers agent))
    (outer : PMF Index) (hfinite : outer.support.Finite)
    (first second : Index → PMF Outcome)
    (hlocal : ∀ index ∈ outer.support,
      Rank.Indifferent (weaklyPrefers agent) (first index) (second index)) :
    Rank.Indifferent (weaklyPrefers agent) (outer.bind first) (outer.bind second) :=
  VNMProof.compoundIndifferent htrans (hindependent agent)
    outer hfinite first second hlocal

/-- `utility` represents the weak preference by expected utility on every
finitely supported lottery. -/
def RepresentsExpectedUtilityOnFiniteSupport
    (weaklyPrefers : WeakPreference Agent Outcome)
    (utility : Outcome → Agent → ℝ) : Prop :=
  ∀ agent (preferred alternative : PMF Outcome),
    preferred.support.Finite → alternative.support.Finite →
      (weaklyPrefers agent preferred alternative ↔
        expect alternative (utility · agent) ≤ expect preferred (utility · agent))

/-- **von Neumann--Morgenstern on any outcome type.** The vNM axioms give one
expected-utility index per agent representing the preference on every
finitely supported lottery. The outcome type may be infinite; the axioms are
stated through finite mixtures, and the representation covers the lotteries
that finite mixtures of outcomes reach. -/
theorem exists_representsExpectedUtilityOnFiniteSupport
    (weaklyPrefers : WeakPreference Agent Outcome)
    (htotal : Preference.Total weaklyPrefers)
    (htrans : Preference.Transitive weaklyPrefers)
    (hindependent : MixtureIndependent weaklyPrefers)
    (hcontinuous : MixtureContinuous weaklyPrefers) :
    ∃ utility : Outcome → Agent → ℝ,
      RepresentsExpectedUtilityOnFiniteSupport weaklyPrefers utility := by
  choose utility hutility using fun agent =>
    VNMProof.exists_representsOnFiniteSupport_pointwise (htotal agent) (htrans agent)
      (fun first second common t hpos h1 =>
        hindependent agent first second common t hpos h1)
      (fun best middle worst => hcontinuous agent best middle worst)
  exact ⟨fun outcome agent => utility agent outcome, hutility⟩

/-- Finite-outcome vNM axioms produce one expected-utility index per agent. -/
theorem exists_representsExpectedUtility [Finite Outcome]
    (weaklyPrefers : WeakPreference Agent Outcome)
    (htotal : Preference.Total weaklyPrefers)
    (htrans : Preference.Transitive weaklyPrefers)
    (hindependent : MixtureIndependent weaklyPrefers)
    (hcontinuous : MixtureContinuous weaklyPrefers) :
    ∃ utility : Outcome → Agent → ℝ,
      RepresentsExpectedUtility weaklyPrefers utility := by
  classical
  cases isEmpty_or_nonempty Outcome with
  | inl hempty =>
      let : IsEmpty Outcome := hempty
      refine ⟨fun outcome => isEmptyElim outcome, ?_⟩
      intro _ preferred _
      obtain ⟨outcome, _⟩ := preferred.support_nonempty
      exact isEmptyElim outcome
  | inr hnonempty =>
      let : Nonempty Outcome := hnonempty
      have hagent : ∀ agent : Agent, ∃ u : Outcome → ℝ,
          ∀ preferred alternative,
            weaklyPrefers agent preferred alternative ↔
              expect alternative u ≤
                expect preferred u := by
        intro agent
        exact VNMProof.exists_representsExpectedUtility_pointwise
          (htotal agent) (htrans agent)
          (fun first second common t hpos h1 =>
            hindependent agent first second common t hpos h1)
          (fun best middle worst => hcontinuous agent best middle worst)
      let utilityFor : Agent → Outcome → ℝ := fun agent => (hagent agent).choose
      refine ⟨fun outcome agent => utilityFor agent outcome, ?_⟩
      intro agent preferred alternative
      have hp : UtilityIntegrable (fun outcome agent => utilityFor agent outcome)
          agent preferred := payoffIntegrable_of_finite preferred _
      have ha : UtilityIntegrable (fun outcome agent => utilityFor agent outcome)
          agent alternative := payoffIntegrable_of_finite alternative _
      have hpoint := (hagent agent).choose_spec preferred alternative
      exact hpoint.trans (by
        simpa only [expectedUtility, utilityFor] using
          (euPreference_iff
            (fun outcome agent => utilityFor agent outcome)
            agent preferred alternative hp ha).symm)

/-- Finite-outcome von Neumann--Morgenstern characterization over ordinary
PMFs on the finite outcome carrier. -/
theorem vnmAxioms_iff_exists_representsExpectedUtility [Finite Outcome]
    (weaklyPrefers : WeakPreference Agent Outcome) :
    (Preference.Total weaklyPrefers ∧ Preference.Transitive weaklyPrefers ∧
      MixtureIndependent weaklyPrefers ∧ MixtureContinuous weaklyPrefers) ↔
      ∃ utility : Outcome → Agent → ℝ,
        RepresentsExpectedUtility weaklyPrefers utility := by
  constructor
  · rintro ⟨htotal, htrans, hindependent, hcontinuous⟩
    exact exists_representsExpectedUtility weaklyPrefers htotal htrans
      hindependent hcontinuous
  · rintro ⟨utility, hrep⟩
    exact hrep.vnmAxioms (fun agent law => payoffIntegrable_of_finite law _)

/-- The strict comparison between two positive-weight mixtures is independent
of their common branch. -/
theorem MixtureIndependent.strict_mix_common_iff
    {weaklyPrefers : WeakPreference Agent Outcome}
    (hindependent : MixtureIndependent weaklyPrefers)
    (agent : Agent) (first second common common' : PMF Outcome)
    (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1) :
    Preference.strict weaklyPrefers agent
        (mix t hpos.le h1 first common)
        (mix t hpos.le h1 second common) ↔
      Preference.strict weaklyPrefers agent
        (mix t hpos.le h1 first common')
        (mix t hpos.le h1 second common') := by
  constructor
  · intro h
    exact ⟨(hindependent agent first second common' t hpos h1).mp
        ((hindependent agent first second common t hpos h1).mpr h.1),
      fun hreverse => h.2 ((hindependent agent second first common t hpos h1).mp
        ((hindependent agent second first common' t hpos h1).mpr hreverse))⟩
  · intro h
    exact ⟨(hindependent agent first second common t hpos h1).mp
        ((hindependent agent first second common' t hpos h1).mpr h.1),
      fun hreverse => h.2 ((hindependent agent second first common' t hpos h1).mp
        ((hindependent agent second first common t hpos h1).mpr hreverse))⟩

end Preference

end GameTheory
