/-
# Dominance and Nash as preservation targets

A dominant profile compares each player's prescribed strategy with every
alternative at every opponent profile. Nash makes the same comparisons at the
prescribed opponents only, so dominance refines Nash. The extra comparisons sit
at opponent behaviour the deviator cannot condition on: a Nash deviation never
reaches another opponent profile, so no localization links the two families
and preserving Nash says nothing about dominance at other opponent profiles.
-/

import GameTheory.Analysis.IncentiveHierarchy
import GameTheory.Core.Response

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo uv

variable {ι : Type uι} [DecidableEq ι] {Observation : Type uv}

namespace GameForm

variable (F : GameForm.{uι, us, uo} ι)

/-- The comparison behind dominance of a prescribed strategy over one
alternative at one opponent profile. -/
def dominanceComparison (profile : Profile F.sig) (observe : F.sig.Outcome → Observation)
    (who : ι) (deviation : Profile F.sig × F.sig.Strategy who) :
    IncentiveComparison Observation where
  prescribed := (F.play (Profile.update deviation.1 who (profile who))).map observe
  alternative := (F.play (Profile.update deviation.1 who deviation.2)).map observe

/-- A dominant profile of observed payoffs is its comparison family. -/
theorem isDominantProfile_iff_holds (profile : Profile F.sig)
    (observe : F.sig.Outcome → Observation) (utility : Observation → ι → ℝ) :
    IsDominantProfile F (euPreference fun outcome who => utility (observe outcome) who)
        profile ↔
      ∀ who deviation,
        (F.dominanceComparison profile observe who deviation).Holds (utility · who) := by
  simp only [IsDominantProfile, IsDominant, VeryWeaklyDominates, dominanceComparison,
    IncentiveComparison.holds_map_iff, Prod.forall]
  exact ⟨fun dominant who opponents alternative => dominant who alternative opponents,
    fun holds who alternative opponents => holds who opponents alternative⟩

/-- A Nash comparison is the dominance comparison at the prescribed
opponents. -/
theorem equilibriumComparison_eq_dominanceComparison (profile : Profile F.sig)
    (observe : F.sig.Outcome → Observation) (who : ι) (alternative : F.sig.Strategy who) :
    equilibriumComparison F (PMF.pure profile) (DeviationScheme.unilateralConstant F.sig)
        observe who alternative =
      F.dominanceComparison profile observe who (profile, alternative) := by
  simp [equilibriumComparison, dominanceComparison, GameForm.outcomeLaw, PMF.pure_map]

/-- Dominance refines Nash for every utility. -/
theorem implies_equilibriumComparison (profile : Profile F.sig)
    (observe : F.sig.Outcome → Observation) :
    IncentiveComparison.Implies (F.dominanceComparison profile observe)
      (equilibriumComparison F (PMF.pure profile) (DeviationScheme.unilateralConstant F.sig)
        observe) :=
  fun _ holds who alternative =>
    (IncentiveComparison.holds_iff_of_eq
      (F.equilibriumComparison_eq_dominanceComparison profile observe who alternative) _).2
        (holds who _)

/-! ## The revealing form

Chance selects a player and an opponent profile, reveals the profile to that
player, and only that player acts. A response confined to one revealed profile
localizes the dominance comparison there with weight its selection
probability, so under full support the revealing form's Nash comparisons are
the base game's dominance comparisons. -/

section Revealing

variable (selector : PMF (ι × Profile F.sig))

/-- The revealing form: the selected player responds to the revealed opponents. -/
@[reducible]
def revealing : GameForm ι where
  sig := { Strategy := fun who => Profile F.sig → F.sig.Strategy who
           Outcome := F.sig.Outcome }
  play responses := selector.bind fun selected =>
    F.play (Profile.update selected.2 selected.1 (responses selected.1 selected.2))

/-- Every player ignores the revealed profile and plays its prescribed strategy. -/
def ignoring (profile : Profile F.sig) : Profile (F.revealing selector).sig :=
  fun who _ => profile who

open Classical in
/-- The response that deviates only at one revealed opponent profile. -/
def confine (profile : Profile F.sig) (who : ι) (opponents : Profile F.sig)
    (action : F.sig.Strategy who) : Profile F.sig → F.sig.Strategy who :=
  fun revealed => if revealed = opponents then action else profile who

private theorem revealing_play_map (responses : Profile (F.revealing selector).sig)
    (observe : F.sig.Outcome → Observation) (outcome : Observation) :
    ((F.revealing selector).play responses).map observe outcome =
      ∑' selected, selector selected * (F.play (Profile.update selected.2 selected.1
        (responses selected.1 selected.2))).map observe outcome := by
  rw [PMF.map_bind, PMF.bind_apply]

/-- **Localization at a revealed profile.** -/
theorem dominanceComparison_isLocalizedIn (profile : Profile F.sig)
    (observe : F.sig.Outcome → Observation) (who : ι) (opponents : Profile F.sig)
    (action : F.sig.Strategy who) :
    (F.dominanceComparison profile observe who (opponents, action)).IsLocalizedIn
      (equilibriumComparison (F.revealing selector) (PMF.pure (F.ignoring selector profile))
        (DeviationScheme.unilateralConstant _) observe who
        (F.confine profile who opponents action))
      (selector (who, opponents)).toReal := by
  classical
  apply IncentiveComparison.isLocalizedIn_of_mass ENNReal.toReal_nonneg
  intro outcome
  rw [ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
  let deviated := Profile.update (sig := (F.revealing selector).sig)
    (F.ignoring selector profile) who (F.confine profile who opponents action)
  have hstatus : (DeviationScheme.unilateralConstant (F.revealing selector).sig).apply
      (PMF.pure (F.ignoring selector profile)) who (F.confine profile who opponents action) =
        PMF.pure deviated :=
    (DeviationScheme.unilateralConstant_apply _ _ _ _).trans (PMF.pure_map _ _)
  let term (responses : Profile (F.revealing selector).sig) (selected : ι × Profile F.sig) :=
    (F.play (Profile.update selected.2 selected.1 (responses selected.1 selected.2))).map
      observe outcome
  have hsame (selected : ι × Profile F.sig) (hne : selected ≠ (who, opponents)) :
      term deviated selected = term (F.ignoring selector profile) selected := by
    obtain ⟨player, revealed⟩ := selected
    by_cases hplayer : player = who
    · subst player
      have hrevealed : revealed ≠ opponents := fun h => hne (by rw [h])
      simp [term, deviated, confine, hrevealed, ignoring]
    · simp [term, deviated, Profile.update_of_ne _ _ hplayer]
  have hat : term deviated (who, opponents) =
      (F.play (Profile.update opponents who action)).map observe outcome := by
    simp [term, deviated, confine]
  have hbase : term (F.ignoring selector profile) (who, opponents) =
      (F.play (Profile.update opponents who (profile who))).map observe outcome := rfl
  have hsplit (value : ι × Profile F.sig → ENNReal) (extra : ENNReal) :
      ∑' selected, value selected + extra =
        ∑' selected, (value selected + if selected = (who, opponents) then extra else 0) := by
    rw [ENNReal.tsum_add, tsum_ite_eq]
  simp only [dominanceComparison, equilibriumComparison, hstatus, GameForm.outcomeLaw,
    PMF.pure_bind]
  rw [revealing_play_map, revealing_play_map]
  change ∑' selected, selector selected * term (F.ignoring selector profile) selected + _ =
    ∑' selected, selector selected * term deviated selected + _
  rw [← hat, ← hbase, hsplit, hsplit]
  refine tsum_congr fun selected => ?_
  by_cases hselected : selected = (who, opponents)
  · subst selected
    simp only [↓reduceIte]
    exact add_comm _ _
  · simp only [hselected, ↓reduceIte, hsame selected hselected]

/-- Under full support the revealing form's Nash comparisons imply the base
game's dominance comparisons. -/
theorem revealing_implies_dominance [Fintype Observation]
    (hfull : ∀ selected, selector selected ≠ 0) (profile : Profile F.sig)
    (observe : F.sig.Outcome → Observation) :
    IncentiveComparison.Implies
      (equilibriumComparison (F.revealing selector) (PMF.pure (F.ignoring selector profile))
        (DeviationScheme.unilateralConstant _) observe)
      (F.dominanceComparison profile observe) :=
  IncentiveComparison.implies_of_localized _ _ fun who deviation =>
    ⟨F.confine profile who deviation.1 deviation.2, (selector (who, deviation.1)).toReal,
      ENNReal.toReal_pos (hfull _) (PMF.apply_ne_top _ _),
      F.dominanceComparison_isLocalizedIn selector profile observe who deviation.1 deviation.2⟩

/-- The base game's dominance comparisons imply the revealing form's dominance
comparisons: each is a selection-weighted mixture of them. -/
theorem dominance_implies_revealing_dominance [Fintype Observation] (profile : Profile F.sig)
    (observe : F.sig.Outcome → Observation) :
    IncentiveComparison.Implies (F.dominanceComparison profile observe)
      ((F.revealing selector).dominanceComparison (F.ignoring selector profile) observe) := by
  intro utility holds who deviation
  obtain ⟨others, response⟩ := deviation
  change euPreference _ () _ _
  refine ⟨hasExpectation_of_payoffIntegrable (payoffIntegrable_of_finite _ _),
    hasExpectation_of_payoffIntegrable (payoffIntegrable_of_finite _ _), ?_⟩
  change extendedExpect (((F.revealing selector).play _).map observe) _ ≤
    extendedExpect (((F.revealing selector).play _).map observe) _
  simp only [GameForm.revealing, PMF.map_bind]
  refine extendedExpect_bind_mono (fun selected _ => ?_)
    (hasExpectation_of_payoffIntegrable (payoffIntegrable_of_finite _ _))
  obtain ⟨player, revealed⟩ := selected
  by_cases hplayer : player = who
  · subst player
    simp only [Profile.update_same]
    exact (holds who (revealed, response revealed)).2.2
  · simp only [Profile.update_of_ne _ _ hplayer]
    exact le_rfl

/-- **Dominance is Nash of the revealing form.** Under full support, the base
game's dominance, the revealing form's dominance, and the revealing form's Nash
imply one another for every utility. -/
theorem revealing_equivalence [Fintype Observation]
    (hfull : ∀ selected, selector selected ≠ 0) (profile : Profile F.sig)
    (observe : F.sig.Outcome → Observation) :
    IncentiveComparison.Implies (F.dominanceComparison profile observe)
        ((F.revealing selector).dominanceComparison (F.ignoring selector profile) observe) ∧
      IncentiveComparison.Implies
        ((F.revealing selector).dominanceComparison (F.ignoring selector profile) observe)
        (equilibriumComparison (F.revealing selector) (PMF.pure (F.ignoring selector profile))
          (DeviationScheme.unilateralConstant _) observe) ∧
      IncentiveComparison.Implies
        (equilibriumComparison (F.revealing selector) (PMF.pure (F.ignoring selector profile))
          (DeviationScheme.unilateralConstant _) observe)
        (F.dominanceComparison profile observe) :=
  ⟨F.dominance_implies_revealing_dominance selector profile observe,
    (F.revealing selector).implies_equilibriumComparison _ observe,
    F.revealing_implies_dominance selector hfull profile observe⟩

/-- **Descent fails through the revealing form.** Compiling a profile into the
revealing form preserves dominance for every utility, and preserves Nash exactly
when Nash already implies dominance in the base game. -/
theorem revealing_preservation [Fintype Observation]
    (hfull : ∀ selected, selector selected ≠ 0) (profile : Profile F.sig)
    (observe : F.sig.Outcome → Observation) :
    IncentiveComparison.Implies (F.dominanceComparison profile observe)
        ((F.revealing selector).dominanceComparison (F.ignoring selector profile) observe) ∧
      (IncentiveComparison.Implies
          (equilibriumComparison F (PMF.pure profile) (DeviationScheme.unilateralConstant F.sig)
            observe)
          (equilibriumComparison (F.revealing selector) (PMF.pure (F.ignoring selector profile))
            (DeviationScheme.unilateralConstant _) observe) ↔
        IncentiveComparison.Implies
          (equilibriumComparison F (PMF.pure profile) (DeviationScheme.unilateralConstant F.sig)
            observe)
          (F.dominanceComparison profile observe)) := by
  obtain ⟨hdominance, hrevealed, hnash⟩ := F.revealing_equivalence selector hfull profile observe
  exact ⟨hdominance, ⟨fun h => h.trans hnash, fun h => (h.trans hdominance).trans hrevealed⟩⟩

end Revealing

end GameForm

end GameTheory
