/-
# Retained decision laws and their perturbations

An information value of the larger protocol is retained when it embeds a
decision site of the smaller one. Only retained values are pinned by a
profile of the smaller protocol; values created by new actions stay free.
Perturbations mix the pinned laws with a reference law of the larger protocol.
-/

import GameTheory.Math.Probability.Mixture
import GameTheory.Protocol.ActionRestriction

noncomputable section

namespace GameTheory.Protocol.InformationModel.ActionRestriction

open GameTheory.Math.Probability

variable {ι : Type*} {E T : ExecutionProtocol ι}
  {M : InformationModel E} {N : InformationModel T} (restriction : M.ActionRestriction N)

private theorem apply_transport {Index : Type*} {Value : Index → Type*}
    (values : ∀ index, Value index) {first second : Index} (same : first = second) :
    Eq.mp (congrArg Value same) (values first) = values second := by
  subst second
  rfl

/-- An information value of the larger protocol that embeds a decision site. -/
def Retained (who : ι) (info : N.InfoState who) : Prop :=
  ∃ site : M.InformationSite who, restriction.information who site.1 = info

theorem retained_site (who : ι) (site : M.InformationSite who) :
    restriction.Retained who (restriction.information who site.1) := ⟨site, rfl⟩

/-- The embedded law of the smaller protocol at a retained value. -/
def retainedLaw (source : (i : ι) → M.BehavioralPolicy i) (who : ι)
    (info : N.InfoState who) (retained : restriction.Retained who info) :
    PMF (N.Choice who info) :=
  Eq.mp (congrArg (fun value => PMF (N.Choice who value)) retained.choose_spec)
    ((source who retained.choose.1).map (restriction.choice who retained.choose.1))

@[simp] theorem retainedLaw_at (source : (i : ι) → M.BehavioralPolicy i)
    (who : ι) (site : M.InformationSite who)
    (retained : restriction.Retained who (restriction.information who site.1)) :
    restriction.retainedLaw source who (restriction.information who site.1) retained =
      (source who site.1).map (restriction.choice who site.1) := by
  have chosen : retained.choose = site :=
    Subtype.ext ((restriction.information who).injective retained.choose_spec)
  exact apply_transport
    (fun original : M.InformationSite who =>
      (source who original.1).map (restriction.choice who original.1)) chosen

/-- Extend a profile by a fallback profile at the values that are not retained. -/
def extendProfile (source : (i : ι) → M.BehavioralPolicy i)
    (fallback : (i : ι) → N.BehavioralPolicy i) : (i : ι) → N.BehavioralPolicy i := by
  classical
  exact fun who info => if retained : restriction.Retained who info then
    restriction.retainedLaw source who info retained else fallback who info

theorem extendProfile_extends (source : (i : ι) → M.BehavioralPolicy i)
    (fallback : (i : ι) → N.BehavioralPolicy i) :
    restriction.ExtendsProfile source (restriction.extendProfile source fallback) := by
  intro who site
  simp only [extendProfile, dite_eq_left (restriction.retained_site who site), retainedLaw_at]

/-- Mix the retained laws with a reference, and play the reference elsewhere. -/
def perturbProfile (source : (i : ι) → M.BehavioralPolicy i)
    (reference : (i : ι) → N.BehavioralPolicy i)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) :
    (i : ι) → N.BehavioralPolicy i := by
  classical
  exact fun who info => if retained : restriction.Retained who info then
    mix epsilon nonnegative small (reference who info)
      (restriction.retainedLaw source who info retained)
    else reference who info

/-- A profile perturbs the embedded laws at every retained decision site. -/
def PerturbsProfile (source : (i : ι) → M.BehavioralPolicy i)
    (reference target : (i : ι) → N.BehavioralPolicy i)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) : Prop :=
  ∀ who (site : M.InformationSite who),
    target who (restriction.information who site.1) =
      mix epsilon nonnegative small
        (reference who (restriction.information who site.1))
        ((source who site.1).map (restriction.choice who site.1))

theorem perturbProfile_perturbs (source : (i : ι) → M.BehavioralPolicy i)
    (reference : (i : ι) → N.BehavioralPolicy i)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) :
    restriction.PerturbsProfile source reference
      (restriction.perturbProfile source reference epsilon nonnegative small)
      epsilon nonnegative small := by
  intro who site
  simp only [perturbProfile, dite_eq_left (restriction.retained_site who site), retainedLaw_at]

theorem perturbProfile_fullSupport (source : (i : ι) → M.BehavioralPolicy i)
    (reference : (i : ι) → N.BehavioralPolicy i)
    (epsilon : ℝ) (positive : 0 < epsilon) (small : epsilon ≤ 1)
    (who : ι) (info : N.InfoState who) (full : FullSupport (reference who info)) :
    FullSupport (restriction.perturbProfile source reference epsilon positive.le small
      who info) := by
  classical
  intro choice
  unfold perturbProfile
  split
  · exact mem_support_mix_left epsilon positive.le small positive (full choice)
  · exact full choice

private theorem transport_map {Index : Type*} {Value : Index → Type*}
    (laws : ∀ index, PMF (Value index)) {first second : Index} (same : first = second) :
    (laws first).map (fun value => Eq.mp (congrArg Value same) value) = laws second := by
  subst second
  exact PMF.map_id _

/-- A perturbing profile mixes the reference with the embedded law at every
embedded nonterminal history. -/
theorem perturbs_at_history (source : (i : ι) → M.BehavioralPolicy i)
    (reference target : (i : ι) → N.BehavioralPolicy i)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (perturbs : restriction.PerturbsProfile source reference target epsilon nonnegative small)
    (original : E.History) (running : ¬ E.terminal original.state) (who : ι) :
    target who (N.infoOf who (restriction.history original).trace) =
      mix epsilon nonnegative small
        (reference who (N.infoOf who (restriction.history original).trace))
        ((source who (M.infoOf who original.trace)).map (restriction.choiceAt who original)) := by
  by_cases active : E.active original.state who
  · obtain ⟨decision, observed⟩ := M.exists_informationSite_of_active who original running active
    have indexed : target who (restriction.information who (M.infoOf who original.trace)) =
        mix epsilon nonnegative small
          (reference who (restriction.information who (M.infoOf who original.trace)))
          ((source who (M.infoOf who original.trace)).map
            (restriction.choice who (M.infoOf who original.trace))) := by
      rcases decision with ⟨info, permitted⟩
      dsimp only at observed
      subst info
      exact perturbs who ⟨_, permitted⟩
    calc
      _ = (target who (restriction.information who (M.infoOf who original.trace))).map
          (fun action => Eq.mp
            (congrArg (N.Choice who) (restriction.observed who original).symm) action) :=
        (transport_map (target who) (restriction.observed who original).symm).symm
      _ = _ := by
        rw [indexed, mix_map,
          transport_map (reference who) (restriction.observed who original).symm,
          PMF.map_comp]
        rfl
  · have inactive : ¬ T.active (restriction.history original).state who :=
      fun enabled => active ((restriction.active original who).mp enabled)
    let _ := N.subsingleton_choice_of_not_active (restriction.history original).trace inactive
    obtain ⟨witness, _⟩ :=
      (target who (N.infoOf who (restriction.history original).trace)).support_nonempty
    exact (eq_pure_of_subsingleton _ witness).trans
      (eq_pure_of_subsingleton _ witness).symm

end GameTheory.Protocol.InformationModel.ActionRestriction
