/-
# Finite-law von Neumann--Morgenstern representation

Preferences remain the canonical family of weak rankings over `FinDist`.
This file adds the two mixture axioms and the expected-utility representation
theorem; it introduces no second lottery carrier or preference relation.

The finite-outcome converse adapts the proof from
`Concepts/Foundations/VNM/Basic.lean` in the pinned v1 snapshot at commit
`a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
-/

import GameTheory.Core.Preference

namespace GameTheory

open Probability

universe ua uo

namespace Preference

variable {Agent : Type ua} {Outcome : Type uo}

/-- Mixing both sides with the same law at a positive weight preserves every
agent's weak comparison. -/
def MixtureIndependent (weaklyPrefers : WeakPreference Agent Outcome) : Prop :=
  ∀ agent first second common (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1),
    weaklyPrefers agent first second ↔
      weaklyPrefers agent
        (FinDist.mix t hpos.le h1 first common)
        (FinDist.mix t hpos.le h1 second common)

/-- Every law ranked between two others is indifferent to a mixture of them. -/
def MixtureContinuous (weaklyPrefers : WeakPreference Agent Outcome) : Prop :=
  ∀ agent best middle worst,
    weaklyPrefers agent best middle → weaklyPrefers agent middle worst →
      ∃ (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1),
        Rank.Indifferent (weaklyPrefers agent) middle
          (FinDist.mix t h0 h1 best worst)

/-- `utility` represents the weak preference exactly by finite-law expected
utility, for every agent. -/
def RepresentsExpectedUtility (weaklyPrefers : WeakPreference Agent Outcome)
    (utility : Outcome → Agent → ℝ) : Prop :=
  ∀ agent preferred alternative,
    weaklyPrefers agent preferred alternative ↔
      alternative.expect (fun outcome => utility outcome agent) ≤
        preferred.expect (fun outcome => utility outcome agent)

namespace RepresentsExpectedUtility

variable {weaklyPrefers : WeakPreference Agent Outcome}
  {utility : Outcome → Agent → ℝ}

theorem total (hrep : RepresentsExpectedUtility weaklyPrefers utility) :
    Preference.Total weaklyPrefers := by
  intro agent first second
  rcases le_total
      (second.expect fun outcome => utility outcome agent)
      (first.expect fun outcome => utility outcome agent) with h | h
  · exact Or.inl ((hrep agent first second).mpr h)
  · exact Or.inr ((hrep agent second first).mpr h)

theorem transitive (hrep : RepresentsExpectedUtility weaklyPrefers utility) :
    Preference.Transitive weaklyPrefers := by
  intro agent first middle last hfirst hmiddle
  exact (hrep agent first last).mpr
    (le_trans ((hrep agent middle last).mp hmiddle)
      ((hrep agent first middle).mp hfirst))

theorem mixtureIndependent (hrep : RepresentsExpectedUtility weaklyPrefers utility) :
    MixtureIndependent weaklyPrefers := by
  intro agent first second common t hpos h1
  constructor
  · intro h
    apply (hrep agent (FinDist.mix t hpos.le h1 first common)
      (FinDist.mix t hpos.le h1 second common)).mpr
    rw [FinDist.expect_mix, FinDist.expect_mix]
    nlinarith [(hrep agent first second).mp h]
  · intro h
    apply (hrep agent first second).mpr
    have hvalue := (hrep agent (FinDist.mix t hpos.le h1 first common)
      (FinDist.mix t hpos.le h1 second common)).mp h
    rw [FinDist.expect_mix, FinDist.expect_mix] at hvalue
    nlinarith

theorem mixtureContinuous (hrep : RepresentsExpectedUtility weaklyPrefers utility) :
    MixtureContinuous weaklyPrefers := by
  intro agent best middle worst hbest hworst
  let a := best.expect fun outcome => utility outcome agent
  let b := middle.expect fun outcome => utility outcome agent
  let c := worst.expect fun outcome => utility outcome agent
  have hba : b ≤ a := (hrep agent best middle).mp hbest
  have hcb : c ≤ b := (hrep agent middle worst).mp hworst
  by_cases hac : a = c
  · refine ⟨0, by norm_num, by norm_num, ?_⟩
    have hba' : b = a := le_antisymm hba (by linarith)
    have hmix : (FinDist.mix 0 (by norm_num) (by norm_num) best worst).expect
        (fun outcome => utility outcome agent) = b := by
      rw [FinDist.expect_mix]
      dsimp [a, b, c] at hac hba' ⊢
      linarith
    exact ⟨(hrep agent middle _).mpr (by rw [hmix]),
      (hrep agent _ middle).mpr (by rw [hmix])⟩
  · have hca : c < a := lt_of_le_of_ne (le_trans hcb hba) (Ne.symm hac)
    let t := (b - c) / (a - c)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hcb) (sub_nonneg.mpr hca.le)
    have ht1 : t ≤ 1 := by
      dsimp [t]
      rw [div_le_one (sub_pos.mpr hca)]
      linarith
    refine ⟨t, ht0, ht1, ?_⟩
    have hcalc : t * a + (1 - t) * c = b := by
      dsimp [t]
      field_simp [ne_of_gt (sub_pos.mpr hca)]
      ring
    have hmix : (FinDist.mix t ht0 ht1 best worst).expect
        (fun outcome => utility outcome agent) = b := by
      rw [FinDist.expect_mix]
      simpa [a, c] using hcalc
    exact ⟨(hrep agent middle _).mpr (by rw [hmix]),
      (hrep agent _ middle).mpr (by rw [hmix])⟩

theorem vnmAxioms (hrep : RepresentsExpectedUtility weaklyPrefers utility) :
    Preference.Total weaklyPrefers ∧ Preference.Transitive weaklyPrefers ∧
      MixtureIndependent weaklyPrefers ∧ MixtureContinuous weaklyPrefers :=
  ⟨hrep.total, hrep.transitive, hrep.mixtureIndependent, hrep.mixtureContinuous⟩

end RepresentsExpectedUtility

namespace VNMProof

variable {pref : FinDist Outcome → FinDist Outcome → Prop}

private theorem indifferent_mix_common
    (hindependent : ∀ first second common (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1),
      pref first second ↔
        pref (FinDist.mix t hpos.le h1 first common)
          (FinDist.mix t hpos.le h1 second common))
    {first second common : FinDist Outcome} {t : ℝ}
    (hpos : 0 < t) (h1 : t ≤ 1) (h : Rank.Indifferent pref first second) :
    Rank.Indifferent pref (FinDist.mix t hpos.le h1 first common)
      (FinDist.mix t hpos.le h1 second common) :=
  ⟨(hindependent first second common t hpos h1).mp h.1,
    (hindependent second first common t hpos h1).mp h.2⟩

private theorem indifferent_mix
    (htrans : Rank.Transitive pref)
    (hindependent : ∀ first second common (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1),
      pref first second ↔
        pref (FinDist.mix t hpos.le h1 first common)
          (FinDist.mix t hpos.le h1 second common))
    {first first' second second' : FinDist Outcome}
    {t : ℝ} (hpos : 0 < t) (hlt : t < 1)
    (hfirst : Rank.Indifferent pref first first')
    (hsecond : Rank.Indifferent pref second second') :
    Rank.Indifferent pref (FinDist.mix t hpos.le hlt.le first second)
      (FinDist.mix t hpos.le hlt.le first' second') := by
  have hchangeFirst := indifferent_mix_common hindependent hpos hlt.le
    (common := second) hfirst
  have hchangeSecond := indifferent_mix_common hindependent
    (t := 1 - t) (by linarith) (by linarith) (common := first') hsecond
  rw [← FinDist.mix_swap t hpos.le hlt.le first' second,
    ← FinDist.mix_swap t hpos.le hlt.le first' second'] at hchangeSecond
  exact
    ⟨htrans _ _ _ hchangeFirst.1 hchangeSecond.1,
      htrans _ _ _ hchangeSecond.2 hchangeFirst.2⟩

private theorem probOf_compl_singleton [DecidableEq Outcome]
    (outer : FinDist Outcome) (outcome : Outcome) :
    outer.probOf ({outcome}ᶜ : Set Outcome) = 1 - outer.prob outcome := by
  rw [← FinDist.expect_indicator_eq_probOf]
  calc
    outer.expect (fun x => if x ∈ ({outcome}ᶜ : Set Outcome) then 1 else 0) =
        outer.expect (fun x => 1 - (FinDist.pure x).prob outcome) := by
          apply FinDist.expect_congr
          intro x _
          by_cases hxo : x = outcome
          · subst hxo
            simp
          · rw [if_pos (by simpa using hxo),
              FinDist.prob_pure_of_ne (Ne.symm hxo)]
            ring
    _ = outer.expect (fun _ => 1) -
        outer.expect (fun x => (FinDist.pure x).prob outcome) :=
          FinDist.expect_sub outer _ _
    _ = 1 - outer.prob outcome := by
          rw [FinDist.expect_const, FinDist.expect_prob_pure]

private theorem eq_mix_pure_condOn_compl (outer : FinDist Outcome) (outcome : Outcome)
    (hrest : ∃ other ∈ ({outcome}ᶜ : Set Outcome), other ∈ outer.support) :
    outer = FinDist.mix (outer.prob outcome) (FinDist.prob_nonneg outer outcome)
      (FinDist.prob_le_one outer outcome) (FinDist.pure outcome)
      (outer.condOn ({outcome}ᶜ : Set Outcome) hrest) := by
  classical
  apply FinDist.ext_of_prob
  intro x
  rw [FinDist.prob_mix]
  by_cases hxo : x = outcome
  · subst hxo
    rw [FinDist.prob_pure_self, FinDist.prob_condOn,
      if_neg (by simp), mul_one, mul_zero, add_zero]
  · rw [FinDist.prob_pure_of_ne hxo, mul_zero, zero_add,
      FinDist.prob_condOn, if_pos (by simpa using hxo),
      probOf_compl_singleton]
    have hpositive : 0 < 1 - outer.prob outcome := by
      rw [← probOf_compl_singleton]
      exact FinDist.probOf_pos hrest
    field_simp

/-- The support-induction consequence of binary independence. -/
private theorem compoundIndifferent
    (htrans : Rank.Transitive pref)
    (hindependent : ∀ first second common (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1),
      pref first second ↔
        pref (FinDist.mix t hpos.le h1 first common)
          (FinDist.mix t hpos.le h1 second common))
    (outer : FinDist Outcome) (first second : Outcome → FinDist Outcome)
    (hlocal : ∀ outcome ∈ outer.support,
      Rank.Indifferent pref (first outcome) (second outcome)) :
    Rank.Indifferent pref (outer.bind first) (outer.bind second) := by
  classical
  have lift : ∀ support : Finset Outcome, ∀ law : FinDist Outcome,
      law.support ⊆ (support : Set Outcome) →
      ∀ left right : Outcome → FinDist Outcome,
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
        · by_cases hrest : ∃ other ∈ ({outcome}ᶜ : Set Outcome), other ∈ law.support
          · let tail := law.condOn ({outcome}ᶜ : Set Outcome) hrest
            have htailSubset : tail.support ⊆ (support : Set Outcome) := by
              intro other hother
              have hkept := FinDist.support_condOn law _ hrest hother
              have hinsert := hsupport hkept.2
              rw [Finset.coe_insert, Set.mem_insert_iff] at hinsert
              exact hinsert.resolve_left (by simpa using hkept.1)
            have htailBranches : ∀ other ∈ tail.support,
                Rank.Indifferent pref (left other) (right other) := by
              intro other hother
              exact hbranches other (FinDist.support_condOn law _ hrest hother).2
            have htail := ih tail htailSubset left right htailBranches
            have hweightPos : 0 < law.prob outcome :=
              FinDist.prob_pos_iff.mpr houtcome
            have hweightLt : law.prob outcome < 1 := by
              have hcomplement : 0 < 1 - law.prob outcome := by
                rw [← probOf_compl_singleton]
                exact FinDist.probOf_pos hrest
              linarith
            rw [eq_mix_pure_condOn_compl law outcome hrest,
              FinDist.mix_bind, FinDist.pure_bind,
              FinDist.mix_bind, FinDist.pure_bind]
            exact indifferent_mix htrans hindependent hweightPos hweightLt
              (hbranches outcome houtcome) htail
          · have hsingleton : law.support ⊆ ({outcome} : Set Outcome) := by
              intro other hother
              by_contra hne
              exact hrest ⟨other, by simpa using hne, hother⟩
            rw [FinDist.eq_pure_of_support_subset_singleton law outcome hsingleton,
              FinDist.pure_bind, FinDist.pure_bind]
            exact hbranches outcome houtcome
        · apply ih law _ left right hbranches
          intro other hother
          have hinsert := hsupport hother
          rw [Finset.coe_insert, Set.mem_insert_iff] at hinsert
          exact hinsert.resolve_left fun heq => by
            subst other
            exact houtcome hother
  exact lift outer.supportFinset outer (by
    intro outcome houtcome
    exact FinDist.mem_supportFinset.mpr houtcome) first second hlocal

private noncomputable def standardLottery (best worst : Outcome) (t : ℝ)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : FinDist Outcome :=
  FinDist.mix t h0 h1 (FinDist.pure best) (FinDist.pure worst)

private theorem standardLottery_zero (best worst : Outcome) :
    standardLottery best worst 0 le_rfl (by norm_num) = FinDist.pure worst := by
  simp [standardLottery]

private theorem standardLottery_one (best worst : Outcome) :
    standardLottery best worst 1 (by norm_num) le_rfl = FinDist.pure best := by
  simp [standardLottery]

private theorem standardLottery_eq_mix_best_standard
    (best worst : Outcome) {s t : ℝ}
    (ht0 : 0 ≤ t) (hst : t ≤ s) (hs1 : s ≤ 1) (ht1 : t < 1) :
    standardLottery best worst s (le_trans ht0 hst) hs1 =
      FinDist.mix ((s - t) / (1 - t))
        (div_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr ht1.le))
        (by rw [div_le_one (sub_pos.mpr ht1)]; linarith)
        (FinDist.pure best)
        (standardLottery best worst t ht0 ht1.le) := by
  apply FinDist.ext_of_prob
  intro outcome
  simp only [standardLottery, FinDist.prob_mix]
  field_simp [ne_of_gt (sub_pos.mpr ht1)]
  ring

private theorem standardLottery_order
    (htotal : Rank.Total pref) (hindependent :
      ∀ first second common (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1),
        pref first second ↔
          pref (FinDist.mix t hpos.le h1 first common)
            (FinDist.mix t hpos.le h1 second common))
    {best worst : Outcome} (hbestWorst : pref (FinDist.pure best) (FinDist.pure worst))
    (hnotWorstBest : ¬ pref (FinDist.pure worst) (FinDist.pure best))
    (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    pref (standardLottery best worst s hs0 hs1)
      (standardLottery best worst t ht0 ht1) ↔ t ≤ s := by
  have hrefl : ∀ law : FinDist Outcome, pref law law :=
    fun law => (htotal law law).elim id id
  have hbestStandard : ∀ (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1),
      pref (FinDist.pure best) (standardLottery best worst q hq0 hq1) := by
    intro q hq0 hq1
    rcases hq1.eq_or_lt with hq | hq
    · subst q
      rw [standardLottery_one]
      exact hrefl _
    · have hweight : 0 < 1 - q := sub_pos.mpr hq
      have hmix : FinDist.mix (1 - q) hweight.le (by linarith)
          (FinDist.pure worst) (FinDist.pure best) =
          standardLottery best worst q hq0 hq1 := by
        exact (FinDist.mix_swap q hq0 hq1
          (FinDist.pure best) (FinDist.pure worst)).symm
      have h := (hindependent (FinDist.pure best) (FinDist.pure worst)
        (FinDist.pure best) (1 - q) hweight (by linarith)).mp hbestWorst
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
        FinDist.mix a haPos.le ha1 (FinDist.pure best)
          (standardLottery best worst s hs0 hs1lt.le) := by
      exact standardLottery_eq_mix_best_standard best worst hs0 hst.le ht1 hs1lt
    have hbase : pref (standardLottery best worst s hs0 hs1lt.le)
        (FinDist.pure best) := by
      apply (hindependent (standardLottery best worst s hs0 hs1lt.le)
        (FinDist.pure best) (standardLottery best worst s hs0 hs1lt.le)
        a haPos ha1).mpr
      simpa [hmixT] using hpref
    rcases hs0.eq_or_lt with hs | hs
    · subst s
      rw [standardLottery_zero] at hbase
      exact hnotWorstBest hbase
    · have hweight : 0 < 1 - s := sub_pos.mpr hs1lt
      have hmix : FinDist.mix (1 - s) hweight.le (by linarith)
          (FinDist.pure worst) (FinDist.pure best) =
          standardLottery best worst s hs0 hs1 := by
        exact (FinDist.mix_swap s hs0 hs1
          (FinDist.pure best) (FinDist.pure worst)).symm
      have hworstBest := (hindependent (FinDist.pure worst) (FinDist.pure best)
        (FinDist.pure best) (1 - s) hweight (by linarith)).mpr (by
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
          FinDist.mix a haPos.le ha1 (FinDist.pure best)
            (standardLottery best worst t ht0 htlt.le) := by
        exact standardLottery_eq_mix_best_standard best worst ht0 hts.le hs1 htlt
      have h := (hindependent (FinDist.pure best)
        (standardLottery best worst t ht0 htlt.le)
        (standardLottery best worst t ht0 htlt.le) a haPos ha1).mp
          (hbestStandard t ht0 htlt.le)
      simpa [hmixS] using h

private theorem expect_nonneg_of_nonneg (law : FinDist Outcome) {u : Outcome → ℝ}
    (hu : ∀ outcome, 0 ≤ u outcome) : 0 ≤ law.expect u := by
  have h := FinDist.expect_mono (u := fun _ : Outcome => 0) (v := u)
    (fun outcome _ => hu outcome) (μ := law)
  simpa using h

private theorem expect_le_one_of_le_one (law : FinDist Outcome) {u : Outcome → ℝ}
    (hu : ∀ outcome, u outcome ≤ 1) : law.expect u ≤ 1 := by
  have h := FinDist.expect_mono (u := u) (v := fun _ : Outcome => 1)
    (fun outcome _ => hu outcome) (μ := law)
  simpa using h

private theorem bind_standardLottery_eq_standard_expect
    {best worst : Outcome} (law : FinDist Outcome) (u : Outcome → ℝ)
    (hu0 : ∀ outcome, 0 ≤ u outcome) (hu1 : ∀ outcome, u outcome ≤ 1) :
    law.bind (fun outcome => standardLottery best worst (u outcome)
      (hu0 outcome) (hu1 outcome)) =
      standardLottery best worst (law.expect u)
        (expect_nonneg_of_nonneg law hu0) (expect_le_one_of_le_one law hu1) := by
  classical
  apply FinDist.ext_of_prob
  intro outcome
  rw [FinDist.prob_bind]
  simp only [standardLottery, FinDist.prob_mix]
  let bestMass := (FinDist.pure best).prob outcome
  let worstMass := (FinDist.pure worst).prob outcome
  calc
    law.expect (fun x => u x * bestMass + (1 - u x) * worstMass) =
        law.expect (fun x => (bestMass - worstMass) * u x + worstMass) := by
          apply FinDist.expect_congr
          intro x _
          ring
    _ = (bestMass - worstMass) * law.expect u + worstMass := by
          rw [FinDist.expect_add, FinDist.expect_smul, FinDist.expect_const]
    _ = law.expect u * bestMass + (1 - law.expect u) * worstMass := by ring

private theorem existsMaximalStrict {α : Type*} [Finite α] [Nonempty α]
    (strict : α → α → Prop)
    (htrans : ∀ a b c, strict a b → strict b c → strict a c)
    (hirrefl : ∀ a, ¬ strict a a) :
    ∃ maximal : α, ∀ other, ¬ strict other maximal := by
  classical
  letI : IsTrans α strict := ⟨htrans⟩
  letI : Std.Irrefl strict := ⟨hirrefl⟩
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
    (htrans : Rank.Transitive pref)
    (hindependent : ∀ first second common (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1),
      pref first second ↔
        pref (FinDist.mix t hpos.le h1 first common)
          (FinDist.mix t hpos.le h1 second common))
    {best worst : Outcome} (u : Outcome → ℝ)
    (hu0 : ∀ outcome, 0 ≤ u outcome) (hu1 : ∀ outcome, u outcome ≤ 1)
    (hpure : ∀ outcome, Rank.Indifferent pref (FinDist.pure outcome)
      (standardLottery best worst (u outcome) (hu0 outcome) (hu1 outcome)))
    (hstandard : ∀ (s t : ℝ)
      (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
        pref (standardLottery best worst s hs0 hs1)
          (standardLottery best worst t ht0 ht1) ↔ t ≤ s) :
    ∀ preferred alternative, pref preferred alternative ↔
      alternative.expect u ≤ preferred.expect u := by
  intro preferred alternative
  let std (law : FinDist Outcome) := standardLottery best worst (law.expect u)
    (expect_nonneg_of_nonneg law hu0) (expect_le_one_of_le_one law hu1)
  have hstdIndifferent : ∀ law : FinDist Outcome, Rank.Indifferent pref law (std law) := by
    intro law
    have h := compoundIndifferent htrans hindependent law
      (fun outcome => FinDist.pure outcome)
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
    exact (hstandard (preferred.expect u) (alternative.expect u)
      (expect_nonneg_of_nonneg preferred hu0) (expect_le_one_of_le_one preferred hu1)
      (expect_nonneg_of_nonneg alternative hu0) (expect_le_one_of_le_one alternative hu1)).mp hstd
  · intro hexpect
    have hpreferred := hstdIndifferent preferred
    have halternative := hstdIndifferent alternative
    have hstd : pref (std preferred) (std alternative) :=
      (hstandard (preferred.expect u) (alternative.expect u)
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
        pref (FinDist.mix t hpos.le h1 first common)
          (FinDist.mix t hpos.le h1 second common))
    (hcontinuous : ∀ best middle worst,
      pref best middle → pref middle worst →
        ∃ (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1),
          Rank.Indifferent pref middle (FinDist.mix t h0 h1 best worst)) :
    ∃ u : Outcome → ℝ, ∀ preferred alternative,
      pref preferred alternative ↔ alternative.expect u ≤ preferred.expect u := by
  classical
  let pureRanks : Outcome → Outcome → Prop :=
    fun first second => pref (FinDist.pure first) (FinDist.pure second)
  have hpureTotal : Rank.Total pureRanks := fun first second =>
    htotal (FinDist.pure first) (FinDist.pure second)
  have hpureTransitive : Rank.Transitive pureRanks :=
    fun first middle last => htrans (FinDist.pure first) (FinDist.pure middle)
      (FinDist.pure last)
  obtain ⟨best, hbest⟩ := existsGreatestFinite pureRanks hpureTotal hpureTransitive
  obtain ⟨worst, hworst⟩ := existsLeastFinite pureRanks hpureTotal hpureTransitive
  by_cases hdegenerate : pref (FinDist.pure worst) (FinDist.pure best)
  · refine ⟨fun _ => 0, ?_⟩
    have hpureBest : ∀ outcome,
        Rank.Indifferent pref (FinDist.pure outcome) (FinDist.pure best) := by
      intro outcome
      exact ⟨htrans _ (FinDist.pure worst) _ (hworst outcome) hdegenerate,
        hbest outcome⟩
    have hlawBest : ∀ law : FinDist Outcome,
        Rank.Indifferent pref law (FinDist.pure best) := by
      intro law
      have h := compoundIndifferent htrans hindependent law
        (fun outcome => FinDist.pure outcome) (fun _ => FinDist.pure best)
        (fun outcome _ => hpureBest outcome)
      simpa using h
    intro preferred alternative
    constructor
    · intro _
      simp
    · intro _
      exact htrans preferred (FinDist.pure best) alternative
        (hlawBest preferred).1 (hlawBest alternative).2
  · have hbestWorst : pref (FinDist.pure best) (FinDist.pure worst) := hbest worst
    have hce : ∀ outcome : Outcome,
        ∃ (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1),
          Rank.Indifferent pref (FinDist.pure outcome)
            (standardLottery best worst t h0 h1) := by
      intro outcome
      exact hcontinuous (FinDist.pure best) (FinDist.pure outcome)
        (FinDist.pure worst) (hbest outcome) (hworst outcome)
    let u : Outcome → ℝ := fun outcome => (hce outcome).choose
    have hu0 : ∀ outcome, 0 ≤ u outcome := fun outcome =>
      (hce outcome).choose_spec.choose
    have hu1 : ∀ outcome, u outcome ≤ 1 := fun outcome =>
      (hce outcome).choose_spec.choose_spec.choose
    have hpure : ∀ outcome, Rank.Indifferent pref (FinDist.pure outcome)
        (standardLottery best worst (u outcome) (hu0 outcome) (hu1 outcome)) :=
      fun outcome => (hce outcome).choose_spec.choose_spec.choose_spec
    exact ⟨u, representsExpectedUtility_of_certaintyEquivalents htrans hindependent
      u hu0 hu1 hpure
      (standardLottery_order htotal hindependent hbestWorst hdegenerate)⟩

end VNMProof

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
      letI : IsEmpty Outcome := hempty
      refine ⟨fun outcome => isEmptyElim outcome, ?_⟩
      intro _ preferred _
      obtain ⟨outcome, _⟩ := preferred.support_nonempty
      exact isEmptyElim outcome
  | inr hnonempty =>
      letI : Nonempty Outcome := hnonempty
      have hagent : ∀ agent : Agent, ∃ u : Outcome → ℝ,
          ∀ preferred alternative,
            weaklyPrefers agent preferred alternative ↔
              alternative.expect u ≤ preferred.expect u := by
        intro agent
        exact VNMProof.exists_representsExpectedUtility_pointwise
          (htotal agent) (htrans agent)
          (fun first second common t hpos h1 =>
            hindependent agent first second common t hpos h1)
          (fun best middle worst => hcontinuous agent best middle worst)
      let utilityFor : Agent → Outcome → ℝ := fun agent => (hagent agent).choose
      refine ⟨fun outcome agent => utilityFor agent outcome, ?_⟩
      intro agent preferred alternative
      exact (hagent agent).choose_spec preferred alternative

/-- Finite-outcome von Neumann--Morgenstern characterization over canonical
finite laws. -/
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
    exact hrep.vnmAxioms

/-- The strict comparison between two positive-weight mixtures is independent
of their common branch. -/
theorem MixtureIndependent.strict_mix_common_iff
    {weaklyPrefers : WeakPreference Agent Outcome}
    (hindependent : MixtureIndependent weaklyPrefers)
    (agent : Agent) (first second common common' : FinDist Outcome)
    (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1) :
    Preference.strict weaklyPrefers agent
        (FinDist.mix t hpos.le h1 first common)
        (FinDist.mix t hpos.le h1 second common) ↔
      Preference.strict weaklyPrefers agent
        (FinDist.mix t hpos.le h1 first common')
        (FinDist.mix t hpos.le h1 second common') := by
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
