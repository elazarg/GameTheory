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

/-- `utility` represents the weak preference by guarded expected utility.
Only the compared laws need integration certificates. -/
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
  rcases le_total (expectedUtility utility agent second hsecond)
      (expectedUtility utility agent first hfirst) with h | h
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
      expectedUtility utility agent (mix t hpos.le h1 law common)
          (hguard law hlaw) =
        t * expectedUtility utility agent law hlaw +
          (1 - t) * expectedUtility utility agent common hcommon :=
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

theorem mixtureContinuous (hrep : RepresentsExpectedUtility weaklyPrefers utility) :
    MixtureContinuous weaklyPrefers := by
  intro agent best middle worst hbest hworst
  obtain ⟨hbestGuard, hmiddleGuard, hba⟩ := (hrep agent best middle).mp hbest
  obtain ⟨_, hworstGuard, hcb⟩ := (hrep agent middle worst).mp hworst
  let a := expectedUtility utility agent best hbestGuard
  let b := expectedUtility utility agent middle hmiddleGuard
  let c := expectedUtility utility agent worst hworstGuard
  have hmixGuard (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      UtilityIntegrable utility agent (mix t ht0 ht1 best worst) :=
    payoffIntegrable_mix t ht0 ht1 best worst
      (fun outcome => utility outcome agent) hbestGuard hworstGuard
  have hmix (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      expectedUtility utility agent (mix t ht0 ht1 best worst)
          (hmixGuard t ht0 ht1) = t * a + (1 - t) * c :=
    expectedUtility_mix utility agent t ht0 ht1 best worst
      hbestGuard hworstGuard
  have hindiff (law : PMF Outcome) (hlaw : UtilityIntegrable utility agent law)
      (heq : expectedUtility utility agent law hlaw = b) :
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
    hrep.mixtureContinuous⟩

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
        expectedUtility first agent lottery hfirstLottery =
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
        expectedUtility second agent lottery hsecondLottery =
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

private noncomputable def finiteValue [Finite Outcome]
    (law : PMF Outcome) (u : Outcome → ℝ) : ℝ :=
  expect law u (payoffIntegrable_of_finite law u)

private theorem finiteValue_nonneg [Finite Outcome]
    (law : PMF Outcome) {u : Outcome → ℝ}
    (hu : ∀ outcome, 0 ≤ u outcome) : 0 ≤ finiteValue law u :=
  expect_nonneg law u (payoffIntegrable_of_finite law u)
    (fun outcome _ => hu outcome)

private theorem finiteValue_le_one [Finite Outcome]
    (law : PMF Outcome) {u : Outcome → ℝ}
    (hu : ∀ outcome, u outcome ≤ 1) : finiteValue law u ≤ 1 :=
  expect_le_const law u (payoffIntegrable_of_finite law u) 1
    (fun outcome _ => hu outcome)

private theorem bind_standardLottery_eq_standard_expect
    [Finite Outcome] {best worst : Outcome}
    (law : PMF Outcome) (u : Outcome → ℝ)
    (hu0 : ∀ outcome, 0 ≤ u outcome) (hu1 : ∀ outcome, u outcome ≤ 1) :
    law.bind (fun outcome => standardLottery best worst (u outcome)
      (hu0 outcome) (hu1 outcome)) =
      standardLottery best worst (finiteValue law u)
        (finiteValue_nonneg law hu0) (finiteValue_le_one law hu1) := by
  simpa only [standardLottery, finiteValue] using
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
      finiteValue alternative u ≤ finiteValue preferred u := by
  intro preferred alternative
  let std (law : PMF Outcome) := standardLottery best worst (finiteValue law u)
    (finiteValue_nonneg law hu0) (finiteValue_le_one law hu1)
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
    exact (hstandard (finiteValue preferred u) (finiteValue alternative u)
      (finiteValue_nonneg preferred hu0) (finiteValue_le_one preferred hu1)
      (finiteValue_nonneg alternative hu0) (finiteValue_le_one alternative hu1)).mp hstd
  · intro hexpect
    have hpreferred := hstdIndifferent preferred
    have halternative := hstdIndifferent alternative
    have hstd : pref (std preferred) (std alternative) :=
      (hstandard (finiteValue preferred u) (finiteValue alternative u)
        (finiteValue_nonneg preferred hu0) (finiteValue_le_one preferred hu1)
        (finiteValue_nonneg alternative hu0)
        (finiteValue_le_one alternative hu1)).mpr hexpect
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
        finiteValue alternative u ≤ finiteValue preferred u := by
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
    have hzero (law : PMF Outcome) : finiteValue law (fun _ => 0) = 0 :=
      expect_constant law 0 (payoffIntegrable_of_finite law (fun _ => 0))
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
              VNMProof.finiteValue alternative u ≤
                VNMProof.finiteValue preferred u := by
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
        simpa only [VNMProof.finiteValue, expectedUtility, utilityFor] using
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
