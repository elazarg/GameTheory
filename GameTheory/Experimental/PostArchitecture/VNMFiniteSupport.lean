/-
# EXP-074: finite-support compound-indifference boundary

This spike keeps the VNM axioms unbundled over the canonical finite law.  It
tests the decisive claim that binary independence extends to arbitrary finite
compound substitution by an exact support-decreasing law decomposition.
-/

import GameTheory.Core.Preference

namespace GameTheory.Experimental.PostArchitecture.VNMFiniteSupport

open GameTheory Probability

universe u

variable {Outcome : Type u}

/-- Mutual weak preference (indifference) for an unbundled lottery relation. -/
def Indifferent (pref : FinDist Outcome → FinDist Outcome → Prop)
    (first second : FinDist Outcome) : Prop :=
  pref first second ∧ pref second first

/-- The binary VNM independence axiom over canonical finite laws. -/
def BinaryIndependent (pref : FinDist Outcome → FinDist Outcome → Prop) : Prop :=
  ∀ (t : ℝ) (hpos : 0 < t) (h1 : t ≤ 1) (first second common : FinDist Outcome),
    pref first second ↔
      pref (FinDist.mix t hpos.le h1 first common) (FinDist.mix t hpos.le h1 second common)

/-- The finite compound-substitution target for a fixed outer law. -/
def CompoundIndifferent (pref : FinDist Outcome → FinDist Outcome → Prop)
    (outer : FinDist Outcome) (first second : Outcome → FinDist Outcome) : Prop :=
  (∀ outcome ∈ outer.support, Indifferent pref (first outcome) (second outcome)) →
    Indifferent pref (outer.bind first) (outer.bind second)

/-- Binary independence transports indifference through a common binary branch. -/
theorem indifferent_mix_common
    {pref : FinDist Outcome → FinDist Outcome → Prop}
    (hindependent : BinaryIndependent pref) {first second common : FinDist Outcome}
    {t : ℝ} (hpos : 0 < t) (h1 : t ≤ 1)
    (h : Indifferent pref first second) :
    Indifferent pref (FinDist.mix t hpos.le h1 first common)
      (FinDist.mix t hpos.le h1 second common) :=
  ⟨(hindependent t hpos h1 first second common).mp h.1,
    (hindependent t hpos h1 second first common).mp h.2⟩

/-- Compound substitution is immediate for a point-mass outer law. -/
theorem compoundIndifferent_pure
    {pref : FinDist Outcome → FinDist Outcome → Prop} (outcome : Outcome)
    (first second : Outcome → FinDist Outcome) :
    CompoundIndifferent pref (FinDist.pure outcome) first second := by
  intro hlocal
  simpa using hlocal outcome (FinDist.mem_support_pure.mpr rfl)

/-- The support-side hypothesis needed by compound substitution is invariant
under extensional replacement of the branches. -/
theorem compoundIndifferent_congr
    {pref : FinDist Outcome → FinDist Outcome → Prop} {outer : FinDist Outcome}
    {first first' second second' : Outcome → FinDist Outcome}
    (hfirst : ∀ outcome ∈ outer.support, first outcome = first' outcome)
    (hsecond : ∀ outcome ∈ outer.support, second outcome = second' outcome)
    (h : CompoundIndifferent pref outer first second) :
    CompoundIndifferent pref outer first' second' := by
  intro hlocal
  have hbase := h fun outcome hmem => by
    simpa [hfirst outcome hmem, hsecond outcome hmem] using hlocal outcome hmem
  have hbindFirst : outer.bind first = outer.bind first' := FinDist.bind_congr hfirst
  have hbindSecond : outer.bind second = outer.bind second' := FinDist.bind_congr hsecond
  rw [← hbindFirst, ← hbindSecond]
  exact hbase

private theorem mix_swap (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (first second : FinDist Outcome) :
    FinDist.mix t h0 h1 first second =
      FinDist.mix (1 - t) (by linarith) (by linarith) second first := by
  apply FinDist.ext_of_prob
  intro outcome
  simp only [FinDist.prob_mix]
  ring

private theorem indifferent_mix
    {pref : FinDist Outcome → FinDist Outcome → Prop}
    (htrans : Rank.Transitive pref) (hindependent : BinaryIndependent pref)
    {first first' second second' : FinDist Outcome}
    {t : ℝ} (hpos : 0 < t) (hlt : t < 1)
    (hfirst : Indifferent pref first first')
    (hsecond : Indifferent pref second second') :
    Indifferent pref (FinDist.mix t hpos.le hlt.le first second)
      (FinDist.mix t hpos.le hlt.le first' second') := by
  have hchangeFirst := indifferent_mix_common hindependent hpos hlt.le
    (common := second) hfirst
  have hchangeSecond := indifferent_mix_common hindependent
    (t := 1 - t) (by linarith) (by linarith) (common := first') hsecond
  rw [← mix_swap t hpos.le hlt.le first' second,
    ← mix_swap t hpos.le hlt.le first' second'] at hchangeSecond
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

private theorem card_support_condOn_compl_lt (outer : FinDist Outcome) (outcome : Outcome)
    (houtcome : outcome ∈ outer.support)
    (hrest : ∃ other ∈ ({outcome}ᶜ : Set Outcome), other ∈ outer.support) :
    (outer.condOn ({outcome}ᶜ : Set Outcome) hrest).supportFinset.card <
      outer.supportFinset.card := by
  classical
  have hsubset : (outer.condOn ({outcome}ᶜ : Set Outcome) hrest).supportFinset ⊆
      outer.supportFinset := by
    intro x hx
    rw [FinDist.mem_supportFinset] at hx ⊢
    exact (FinDist.support_condOn outer _ hrest hx).2
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset hsubset]
  refine ⟨outcome, FinDist.mem_supportFinset.mpr houtcome, ?_⟩
  intro hmem
  have hcond := FinDist.support_condOn outer _ hrest
    (FinDist.mem_supportFinset.mp hmem)
  exact hcond.1 (by simp)

/-- Binary independence extends to simultaneous substitution in every branch
of an arbitrary finite compound law.  This is the decomposition boundary that
the experiment is intended to test. -/
theorem binaryIndependent_compoundIndifferent
    {pref : FinDist Outcome → FinDist Outcome → Prop}
    (htrans : Rank.Transitive pref) (hindependent : BinaryIndependent pref)
    (outer : FinDist Outcome) (first second : Outcome → FinDist Outcome) :
    CompoundIndifferent pref outer first second := by
  classical
  intro hlocal
  have lift : ∀ support : Finset Outcome, ∀ law : FinDist Outcome,
      law.support ⊆ (support : Set Outcome) →
      ∀ left right : Outcome → FinDist Outcome,
        (∀ outcome ∈ law.support, Indifferent pref (left outcome) (right outcome)) →
        Indifferent pref (law.bind left) (law.bind right) := by
    intro support
    induction support using Finset.induction_on with
    | empty =>
        intro law hsupport
        obtain ⟨outcome, houtcome⟩ := law.support_nonempty
        exact False.elim (by simpa using hsupport houtcome)
    | @insert outcome support hnotmem ih =>
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
                Indifferent pref (left other) (right other) := by
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

end GameTheory.Experimental.PostArchitecture.VNMFiniteSupport
