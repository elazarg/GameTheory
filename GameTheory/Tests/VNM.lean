/-
Hostile finite-law VNM fixture.

The positive example has three distinct utility levels and an interior
standard-lottery indifference.  The lexicographic control keeps completeness,
transitivity, and mixture independence while rejecting mixture continuity, so
the representation theorem cannot omit its continuity premise.
-/

import GameTheory.Core.VNM
import GameTheory.Core.Utility
import Mathlib.Tactic

noncomputable section

namespace GameTheory.Tests.VNM

open GameTheory.Math.Probability

def utility : Fin 3 → Unit → ℝ := fun outcome _ =>
  if outcome = 0 then 3 else if outcome = 1 then 1 else -1

def high : FinDist (Fin 3) := FinDist.pure 0
def middle : FinDist (Fin 3) := FinDist.pure 1
def low : FinDist (Fin 3) := FinDist.pure 2

def middleMix : FinDist (Fin 3) :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) high low

theorem eu_represents :
    Preference.RepresentsExpectedUtility (euPreference utility) utility := by
  intro agent preferred alternative
  rfl

theorem high_strict_middle : Rank.strict (euPreference utility ()) high middle := by
  constructor <;> norm_num [euPreference_apply, utility, high, middle, Fin.ext_iff]

theorem middle_strict_low : Rank.strict (euPreference utility ()) middle low := by
  constructor <;> norm_num [euPreference_apply, utility, middle, low, Fin.ext_iff]

theorem middle_indifferent_middleMix :
    Rank.Indifferent (euPreference utility ()) middle middleMix := by
  have hmiddle : expectedUtility utility () middle = 1 := by
    calc
      expectedUtility utility () middle = utility 1 () := expectedUtility_pure ..
      _ = 1 := by norm_num [utility, Fin.ext_iff]
  have hmix : expectedUtility utility () middleMix = 1 := by
    calc
      expectedUtility utility () middleMix =
          (1 / 2) * expectedUtility utility () high +
            (1 - 1 / 2) * expectedUtility utility () low := by
        show
          (FinDist.mix (1 / 2) (by norm_num) (by norm_num) high low).expect
              (fun outcome => utility outcome ()) =
            (1 / 2) * high.expect (fun outcome => utility outcome ()) +
              (1 - 1 / 2) * low.expect (fun outcome => utility outcome ())
        rw [FinDist.expect_mix]
      _ = 1 := by
        rw [high, low, expectedUtility_pure, expectedUtility_pure]
        norm_num [utility, high, low, Fin.ext_iff]
  constructor <;> rw [euPreference_apply, hmiddle, hmix]

theorem eu_vnm_axioms :
    Preference.Total (euPreference utility) ∧ Preference.Transitive (euPreference utility) ∧
      Preference.MixtureIndependent (euPreference utility) ∧
        Preference.MixtureContinuous (euPreference utility) :=
  eu_represents.vnmAxioms

theorem eu_characterization_produces_representation :
    ∃ represented : Fin 3 → Unit → ℝ,
      Preference.RepresentsExpectedUtility (euPreference utility) represented :=
  (Preference.vnmAxioms_iff_exists_representsExpectedUtility
    (euPreference utility)).mp eu_vnm_axioms

def twoAgentUtility : Fin 3 → Fin 2 → ℝ := fun outcome agent =>
  if agent = 0 then utility outcome () else -utility outcome ()

theorem two_agent_characterization_produces_family :
    ∃ represented : Fin 3 → Fin 2 → ℝ,
      Preference.RepresentsExpectedUtility
        (euPreference twoAgentUtility) represented := by
  apply (Preference.vnmAxioms_iff_exists_representsExpectedUtility
    (euPreference twoAgentUtility)).mp
  exact (show Preference.RepresentsExpectedUtility
    (euPreference twoAgentUtility) twoAgentUtility from fun _ _ _ => Iff.rfl).vnmAxioms

def emptyPreference : WeakPreference Unit Empty := fun _ _ _ => True

theorem empty_outcome_characterization_has_no_nonempty_assumption :
    (Preference.Total emptyPreference ∧ Preference.Transitive emptyPreference ∧
      Preference.MixtureIndependent emptyPreference ∧
        Preference.MixtureContinuous emptyPreference) ↔
      ∃ represented : Empty → Unit → ℝ,
        Preference.RepresentsExpectedUtility emptyPreference represented :=
  Preference.vnmAxioms_iff_exists_representsExpectedUtility emptyPreference

theorem zero_weight_independence_would_trivialize_preference :
    ¬ (∀ first second common : FinDist (Fin 3),
      euPreference utility () first second ↔
        euPreference utility ()
          (FinDist.mix 0 le_rfl (by norm_num) first common)
          (FinDist.mix 0 le_rfl (by norm_num) second common)) := by
  intro hzero
  have hbad : euPreference utility () middle high :=
    (hzero middle high low).mpr (by simp)
  exact high_strict_middle.2 hbad

theorem eu_independence_two_thirds :
    euPreference utility () high middle ↔
      euPreference utility ()
        (FinDist.mix (2 / 3) (by norm_num) (by norm_num) high low)
        (FinDist.mix (2 / 3) (by norm_num) (by norm_num) middle low) :=
  eu_represents.mixtureIndependent () high middle low (2 / 3) (by norm_num) (by norm_num)

theorem positive_affine_same_preference (preferred alternative : FinDist (Fin 3)) :
    euPreference (affineUtility utility (fun _ => 2) (fun _ => 5)) () preferred alternative ↔
      euPreference utility () preferred alternative :=
  euPreference_affine utility (fun _ => by norm_num) () preferred alternative

def rescaledUtility : Fin 3 → Unit → ℝ :=
  affineUtility utility (fun _ => 2) (fun _ => 5)

theorem rescaled_represents :
    Preference.RepresentsExpectedUtility
      (euPreference utility) rescaledUtility := by
  intro agent preferred alternative
  exact (euPreference_affine utility (fun _ => by norm_num)
    agent preferred alternative).symm

/-- The uniqueness theorem is usable with concrete endpoint witnesses, rather
than merely asserting existence of some unrelated representation. -/
theorem rescaled_is_positiveAffine :
    ∃ (scale shift : Unit → ℝ),
      (∀ agent, 0 < scale agent) ∧
        ∀ outcome agent,
          rescaledUtility outcome agent =
            scale agent * utility outcome agent + shift agent := by
  apply Preference.representsExpectedUtility_unique_positiveAffine
    eu_represents rescaled_represents (fun _ => 0) (fun _ => 2)
  · intro agent
    norm_num [utility, Fin.ext_iff]
  · intro agent outcome
    fin_cases outcome <;> norm_num [utility, Fin.ext_iff]

/-- The finite convenience theorem selects its own extrema; the caller only
supplies a strict comparison witnessing nonconstant utility. -/
theorem rescaled_is_positiveAffine_without_endpoint_arguments :
    ∃ (scale shift : Unit → ℝ),
      (∀ agent, 0 < scale agent) ∧
        ∀ outcome agent,
          rescaledUtility outcome agent =
            scale agent * utility outcome agent + shift agent := by
  apply Preference.representsExpectedUtility_unique_positiveAffine_of_finite
    eu_represents rescaled_represents
  intro agent
  exact ⟨2, 0, by norm_num [utility, Fin.ext_iff]⟩

def lexicographic : WeakPreference Unit (Fin 3) := fun _ first second =>
  first.prob 0 > second.prob 0 ∨
    first.prob 0 = second.prob 0 ∧ first.prob 1 ≥ second.prob 1

theorem lexicographic_total : Preference.Total lexicographic := by
  intro agent first second
  rcases agent with ⟨⟩
  rcases lt_trichotomy (first.prob 0) (second.prob 0) with h | h | h
  · exact Or.inr (Or.inl h)
  · rcases le_total (second.prob 1) (first.prob 1) with h1 | h1
    · exact Or.inl (Or.inr ⟨h, h1⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h1⟩)
  · exact Or.inl (Or.inl h)

theorem lexicographic_transitive : Preference.Transitive lexicographic := by
  intro agent first second third hfirst hsecond
  rcases agent with ⟨⟩
  rcases hfirst with hfirst | ⟨hfirst0, hfirst1⟩ <;>
    rcases hsecond with hsecond | ⟨hsecond0, hsecond1⟩
  · exact Or.inl (lt_trans hsecond hfirst)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨hfirst0.trans hsecond0, le_trans hsecond1 hfirst1⟩

theorem lexicographic_mixtureIndependent :
    Preference.MixtureIndependent lexicographic := by
  intro agent first second common t hpos h1
  rcases agent with ⟨⟩
  simp only [lexicographic, FinDist.prob_mix]
  constructor
  · rintro (hfirst | ⟨hfirst0, hfirst1⟩)
    · left
      nlinarith
    · right
      constructor <;> nlinarith
  · rintro (hmix | ⟨hmix0, hmix1⟩)
    · left
      nlinarith
    · right
      constructor <;> nlinarith

theorem lexicographic_no_middle_indifferent_highLowMix
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ¬ Rank.Indifferent (lexicographic ()) middle
      (FinDist.mix t h0 h1 high low) := by
  rintro ⟨hmiddle, hmix⟩
  simp [lexicographic, FinDist.prob_mix, FinDist.prob_pure_eq_ite,
    high, middle, low, Fin.ext_iff] at hmiddle hmix
  rcases hmiddle with hmiddle | ⟨hmiddle0, _⟩
  · linarith
  · rcases hmix with hmix | ⟨hmix0, hmix1⟩
    · linarith
    · norm_num at hmix1

theorem lexicographic_not_mixtureContinuous :
    ¬ Preference.MixtureContinuous lexicographic := by
  intro hcontinuous
  obtain ⟨t, h0, h1, hindifferent⟩ := hcontinuous () high middle low
    (by left; norm_num [lexicographic, high, middle, FinDist.prob_pure_eq_ite, Fin.ext_iff])
    (by right; constructor <;>
      norm_num [lexicographic, middle, low, FinDist.prob_pure_eq_ite, Fin.ext_iff])
  exact lexicographic_no_middle_indifferent_highLowMix t h0 h1 hindifferent

theorem lexicographic_not_representsExpectedUtility :
    ¬ ∃ represented : Fin 3 → Unit → ℝ,
      Preference.RepresentsExpectedUtility lexicographic represented := by
  rintro ⟨represented, hrepresentation⟩
  exact lexicographic_not_mixtureContinuous hrepresentation.mixtureContinuous

theorem lexicographic_characterization_fails :
    ¬ (Preference.Total lexicographic ∧ Preference.Transitive lexicographic ∧
      Preference.MixtureIndependent lexicographic ∧
        Preference.MixtureContinuous lexicographic) := by
  intro haxioms
  obtain ⟨represented, hrepresentation⟩ :=
    (Preference.vnmAxioms_iff_exists_representsExpectedUtility lexicographic).mp haxioms
  exact lexicographic_not_representsExpectedUtility ⟨represented, hrepresentation⟩

end GameTheory.Tests.VNM
