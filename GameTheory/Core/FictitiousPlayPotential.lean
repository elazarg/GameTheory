/-
# Empirical potential recurrences

Advancing one empirical marginal is an affine update of the multilinear
potential.  In an exact-potential game, its first-order increment is precisely
the step size times the action's current deviation gain.  These identities are
finite-law algebra; asymptotic estimates live in `Analysis`.
-/

import GameTheory.Core.FictitiousPlay
import GameTheory.Core.MixedPotential

noncomputable section

namespace GameTheory

open Probability

universe uι us uo

namespace UtilityGame

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable (G : UtilityGame.{uι, us, uo} ι)

/-- Advancing one coordinate to its next empirical marginal is affine for the
mixed extension of every pure-profile observable. -/
theorem mixedPotential_update_empiricalMarginal_succ
    (potential : Profile G.form.sig → ℝ)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ) :
    G.mixedPotential potential
        (Profile.update mixedProfile who
          (G.empiricalMarginal history who (t + 2))) =
      ((t + 1 : ℝ) / (t + 2 : ℝ)) *
          G.mixedPotential potential
            (Profile.update mixedProfile who
              (G.empiricalMarginal history who (t + 1))) +
        (1 / (t + 2 : ℝ)) *
          G.mixedPotential potential
            (Profile.update mixedProfile who
              (FinDist.pure (history (t + 1) who))) := by
  rw [G.mixedPotential_update potential mixedProfile who
      (G.empiricalMarginal history who (t + 2)),
    G.empiricalMarginal_succ_expect history who t
      (fun action => G.mixedPotential potential
        (Profile.update mixedProfile who (FinDist.pure action))),
    ← G.mixedPotential_update potential mixedProfile who
      (G.empiricalMarginal history who (t + 1))]

/-- Difference form of the one-coordinate empirical-potential recurrence. -/
theorem mixedPotential_update_empiricalMarginal_succ_sub
    (potential : Profile G.form.sig → ℝ)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ) :
    G.mixedPotential potential
        (Profile.update mixedProfile who
          (G.empiricalMarginal history who (t + 2))) -
      G.mixedPotential potential
        (Profile.update mixedProfile who
          (G.empiricalMarginal history who (t + 1))) =
      (1 / (t + 2 : ℝ)) *
        (G.mixedPotential potential
            (Profile.update mixedProfile who
              (FinDist.pure (history (t + 1) who))) -
          G.mixedPotential potential
            (Profile.update mixedProfile who
              (G.empiricalMarginal history who (t + 1)))) := by
  rw [G.mixedPotential_update_empiricalMarginal_succ potential history
    mixedProfile who t]
  have hnonzero : (t + 2 : ℝ) ≠ 0 := by positivity
  field_simp [hnonzero]
  ring

/-- The gain in mixed potential from replacing one marginal by a pure action. -/
def mixedPotentialGain (potential : Profile G.form.sig → ℝ)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who) : ℝ :=
  G.mixedPotential potential
      (Profile.update mixedProfile who (FinDist.pure action)) -
    G.mixedPotential potential mixedProfile

/-- If the updated coordinate is still the old empirical marginal, the
potential increment is the step size times the matching pure gain. -/
theorem mixedPotential_update_empiricalMarginal_succ_sub_of_eq
    (potential : Profile G.form.sig → ℝ)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ)
    (hcoordinate : mixedProfile who =
      G.empiricalMarginal history who (t + 1)) :
    G.mixedPotential potential
        (Profile.update mixedProfile who
          (G.empiricalMarginal history who (t + 2))) -
      G.mixedPotential potential mixedProfile =
      (1 / (t + 2 : ℝ)) *
        G.mixedPotentialGain potential mixedProfile who
          (history (t + 1) who) := by
  have hupdate :
      Profile.update mixedProfile who
          (G.empiricalMarginal history who (t + 1)) = mixedProfile := by
    rw [← hcoordinate]
    exact Profile.update_eq_self mixedProfile who
  have hrecurrence :=
    G.mixedPotential_update_empiricalMarginal_succ_sub
      potential history mixedProfile who t
  rw [hupdate] at hrecurrence
  exact hrecurrence

/-- Exact potential identifies every pure mixed-potential gain with the
corresponding expected-utility gain. -/
theorem IsExactPotential.mixedPotentialGain_eq_mixedGain
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who) :
    G.mixedPotentialGain potential mixedProfile who action =
      G.mixedGain mixedProfile who action := by
  exact (UtilityGame.IsExactPotential.mixed_pure_diff
    (G := G) hpotential mixedProfile who action).symm

/-- In an exact-potential game, advancing one empirical-belief coordinate has
increment equal to the step size times that player's played gain. -/
theorem IsExactPotential.mixedPotential_belief_update_empiricalMarginal_succ_sub
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    (history : ℕ → Profile G.form.sig) (who : ι) (t : ℕ) :
    G.mixedPotential potential
        (Profile.update (G.empiricalBelief history (t + 1)) who
          (G.empiricalMarginal history who (t + 2))) -
      G.mixedPotential potential (G.empiricalBelief history (t + 1)) =
      (1 / (t + 2 : ℝ)) * G.playedGain history t who := by
  have hcoordinate :
      G.empiricalBelief history (t + 1) who =
        G.empiricalMarginal history who (t + 1) := rfl
  rw [G.mixedPotential_update_empiricalMarginal_succ_sub_of_eq
      potential history (G.empiricalBelief history (t + 1)) who t hcoordinate,
    UtilityGame.IsExactPotential.mixedPotentialGain_eq_mixedGain
      (G := G) hpotential]
  rfl

omit [DecidableEq ι] in
/-- A uniform absolute bound on pure profiles also bounds the multilinear
mixed potential. -/
theorem mixedPotential_abs_le_of_abs_bound
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (mixedProfile : Profile G.form.sig.mixed) :
    |G.mixedPotential potential mixedProfile| ≤ C := by
  unfold mixedPotential
  exact FinDist.abs_expect_le_of_abs_bound _ _ fun profile _ => hbound profile

/-- Every real observable on a finite pure-profile space has a uniform
absolute bound. -/
theorem exists_profile_abs_bound
    [∀ who, Fintype (G.form.sig.Strategy who)]
    (potential : Profile G.form.sig → ℝ) :
    ∃ C : ℝ, ∀ profile, |potential profile| ≤ C := by
  refine ⟨∑ profile : Profile G.form.sig, |potential profile|, ?_⟩
  intro profile
  exact Finset.single_le_sum
    (fun candidate _ => abs_nonneg (potential candidate))
    (Finset.mem_univ profile)

/-- Advancing one marginal by one empirical step changes a bounded mixed
potential by at most `2C/(t+2)`. -/
theorem mixedPotential_update_empiricalMarginal_succ_abs_sub_le
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ)
    (hcoordinate : mixedProfile who =
      G.empiricalMarginal history who (t + 1)) :
    |G.mixedPotential potential
          (Profile.update mixedProfile who
            (G.empiricalMarginal history who (t + 2))) -
        G.mixedPotential potential mixedProfile| ≤
      (1 / (t + 2 : ℝ)) * (2 * C) := by
  have hrecurrence :=
    G.mixedPotential_update_empiricalMarginal_succ_sub_of_eq
      potential history mixedProfile who t hcoordinate
  have hpure := G.mixedPotential_abs_le_of_abs_bound potential hbound
    (Profile.update mixedProfile who
      (FinDist.pure (history (t + 1) who)))
  have hbase :=
    G.mixedPotential_abs_le_of_abs_bound potential hbound mixedProfile
  have hdiff :
      |G.mixedPotential potential
          (Profile.update mixedProfile who
            (FinDist.pure (history (t + 1) who))) -
        G.mixedPotential potential mixedProfile| ≤ 2 * C := by
    have htriangle := abs_sub
      (G.mixedPotential potential
        (Profile.update mixedProfile who
          (FinDist.pure (history (t + 1) who))))
      (G.mixedPotential potential mixedProfile)
    linarith
  have hstep : 0 ≤ (1 / (t + 2 : ℝ)) := by positivity
  calc
    |G.mixedPotential potential
          (Profile.update mixedProfile who
            (G.empiricalMarginal history who (t + 2))) -
        G.mixedPotential potential mixedProfile| =
        |(1 / (t + 2 : ℝ)) *
          G.mixedPotentialGain potential mixedProfile who
            (history (t + 1) who)| := by rw [hrecurrence]
    _ = (1 / (t + 2 : ℝ)) *
        |G.mixedPotentialGain potential mixedProfile who
          (history (t + 1) who)| := by
      rw [abs_mul, abs_of_nonneg hstep]
    _ ≤ (1 / (t + 2 : ℝ)) * (2 * C) :=
      mul_le_mul_of_nonneg_left hdiff hstep

/-- Advancing another player's marginal changes a fixed pure potential gain by
at most `4C/(t+2)`. -/
theorem mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le_of_ne
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed)
    {changed who : ι} (action : G.form.sig.Strategy who)
    (hne : changed ≠ who) (t : ℕ)
    (hcoordinate : mixedProfile changed =
      G.empiricalMarginal history changed (t + 1)) :
    |G.mixedPotentialGain potential
          (Profile.update mixedProfile changed
            (G.empiricalMarginal history changed (t + 2))) who action -
        G.mixedPotentialGain potential mixedProfile who action| ≤
      (1 / (t + 2 : ℝ)) * (4 * C) := by
  have hcommute :
      Profile.update
          (Profile.update mixedProfile changed
            (G.empiricalMarginal history changed (t + 2)))
          who (FinDist.pure action) =
        Profile.update
          (Profile.update mixedProfile who (FinDist.pure action))
          changed (G.empiricalMarginal history changed (t + 2)) :=
    Profile.update_comm mixedProfile hne
      (G.empiricalMarginal history changed (t + 2)) (FinDist.pure action)
  have hpureCoordinate :
      Profile.update mixedProfile who (FinDist.pure action) changed =
        G.empiricalMarginal history changed (t + 1) := by
    rw [Profile.update_of_ne _ _ hne]
    exact hcoordinate
  have hpureStep :=
    G.mixedPotential_update_empiricalMarginal_succ_abs_sub_le
      potential hbound history
      (Profile.update mixedProfile who (FinDist.pure action)) changed t
      hpureCoordinate
  have hbaseStep :=
    G.mixedPotential_update_empiricalMarginal_succ_abs_sub_le
      potential hbound history mixedProfile changed t hcoordinate
  rw [mixedPotentialGain, mixedPotentialGain, hcommute]
  have hrewrite :
      G.mixedPotential potential
          (Profile.update
            (Profile.update mixedProfile who (FinDist.pure action)) changed
            (G.empiricalMarginal history changed (t + 2))) -
        G.mixedPotential potential
          (Profile.update mixedProfile changed
            (G.empiricalMarginal history changed (t + 2))) -
        (G.mixedPotential potential
          (Profile.update mixedProfile who (FinDist.pure action)) -
          G.mixedPotential potential mixedProfile) =
      (G.mixedPotential potential
          (Profile.update
            (Profile.update mixedProfile who (FinDist.pure action)) changed
            (G.empiricalMarginal history changed (t + 2))) -
        G.mixedPotential potential
          (Profile.update mixedProfile who (FinDist.pure action))) -
      (G.mixedPotential potential
          (Profile.update mixedProfile changed
            (G.empiricalMarginal history changed (t + 2))) -
        G.mixedPotential potential mixedProfile) := by ring
  rw [hrewrite]
  calc
    _ ≤ |G.mixedPotential potential
          (Profile.update
            (Profile.update mixedProfile who (FinDist.pure action)) changed
            (G.empiricalMarginal history changed (t + 2))) -
        G.mixedPotential potential
          (Profile.update mixedProfile who (FinDist.pure action))| +
      |G.mixedPotential potential
          (Profile.update mixedProfile changed
            (G.empiricalMarginal history changed (t + 2))) -
        G.mixedPotential potential mixedProfile| := abs_sub _ _
    _ ≤ (1 / (t + 2 : ℝ)) * (2 * C) +
        (1 / (t + 2 : ℝ)) * (2 * C) := add_le_add hpureStep hbaseStep
    _ = (1 / (t + 2 : ℝ)) * (4 * C) := by ring

/-- Advancing a player's own marginal changes its fixed pure potential gain by
at most `2C/(t+2)`. -/
theorem mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le_self
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed)
    {who : ι} (action : G.form.sig.Strategy who) (t : ℕ)
    (hcoordinate : mixedProfile who =
      G.empiricalMarginal history who (t + 1)) :
    |G.mixedPotentialGain potential
          (Profile.update mixedProfile who
            (G.empiricalMarginal history who (t + 2))) who action -
        G.mixedPotentialGain potential mixedProfile who action| ≤
      (1 / (t + 2 : ℝ)) * (2 * C) := by
  have hstep := G.mixedPotential_update_empiricalMarginal_succ_abs_sub_le
    potential hbound history mixedProfile who t hcoordinate
  rw [mixedPotentialGain, mixedPotentialGain,
    Profile.update_idem]
  have hrewrite :
      G.mixedPotential potential
          (Profile.update mixedProfile who (FinDist.pure action)) -
        G.mixedPotential potential
          (Profile.update mixedProfile who
            (G.empiricalMarginal history who (t + 2))) -
        (G.mixedPotential potential
          (Profile.update mixedProfile who (FinDist.pure action)) -
          G.mixedPotential potential mixedProfile) =
      -(G.mixedPotential potential
          (Profile.update mixedProfile who
            (G.empiricalMarginal history who (t + 2))) -
        G.mixedPotential potential mixedProfile) := by ring
  rw [hrewrite, abs_neg]
  exact hstep

/-- Advancing any one marginal changes any fixed pure potential gain by at
most `4C/(t+2)`. -/
theorem mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed)
    {changed who : ι} (action : G.form.sig.Strategy who) (t : ℕ)
    (hcoordinate : mixedProfile changed =
      G.empiricalMarginal history changed (t + 1)) :
    |G.mixedPotentialGain potential
          (Profile.update mixedProfile changed
            (G.empiricalMarginal history changed (t + 2))) who action -
        G.mixedPotentialGain potential mixedProfile who action| ≤
      (1 / (t + 2 : ℝ)) * (4 * C) := by
  by_cases hsame : changed = who
  · subst changed
    have hself :=
      G.mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le_self
        potential hbound history mixedProfile action t hcoordinate
    have hC : 0 ≤ C := by
      have hprofile := hbound (history 0)
      exact (abs_nonneg _).trans hprofile
    have hstep : 0 ≤ (1 / (t + 2 : ℝ)) := by positivity
    nlinarith
  · exact G.mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le_of_ne
      potential hbound history mixedProfile action hsame t hcoordinate

/-- Advance the listed empirical marginals from horizon `t+1` to `t+2`. -/
def advanceMarginals (history : ℕ → Profile G.form.sig) (t : ℕ)
    (players : List ι) (mixedProfile : Profile G.form.sig.mixed) :
    Profile G.form.sig.mixed :=
  players.foldl (fun current changed =>
    Profile.update current changed
      (G.empiricalMarginal history changed (t + 2))) mixedProfile

/-- Sweeping a duplicate-free list of empirical updates changes any fixed
pure potential gain by at most the list length times the one-step bound. -/
theorem mixedPotentialGain_advanceMarginals_abs_sub_le
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (history : ℕ → Profile G.form.sig) (t : ℕ) :
    ∀ (players : List ι) (mixedProfile : Profile G.form.sig.mixed),
      players.Nodup →
      (∀ changed, changed ∈ players → mixedProfile changed =
        G.empiricalMarginal history changed (t + 1)) →
      ∀ (who : ι) (action : G.form.sig.Strategy who),
        |G.mixedPotentialGain potential
            (G.advanceMarginals history t players mixedProfile) who action -
          G.mixedPotentialGain potential mixedProfile who action| ≤
          (players.length : ℝ) *
            ((1 / (t + 2 : ℝ)) * (4 * C)) := by
  intro players
  induction players with
  | nil =>
      intro mixedProfile _ _ who action
      simp [advanceMarginals]
  | cons first rest ih =>
      intro mixedProfile hnodup hcoordinates who action
      have hrest : rest.Nodup := List.Nodup.of_cons hnodup
      have hfirst : first ∉ rest := (List.nodup_cons.mp hnodup).1
      let stepError : ℝ := (1 / (t + 2 : ℝ)) * (4 * C)
      let nextProfile : Profile G.form.sig.mixed :=
        Profile.update mixedProfile first
          (G.empiricalMarginal history first (t + 2))
      have hfirstCoordinate : mixedProfile first =
          G.empiricalMarginal history first (t + 1) :=
        hcoordinates first (by simp)
      have hrestCoordinates :
          ∀ changed, changed ∈ rest → nextProfile changed =
            G.empiricalMarginal history changed (t + 1) := by
        intro changed hchanged
        have hne : changed ≠ first := by
          intro heq
          subst changed
          exact hfirst hchanged
        dsimp [nextProfile]
        rw [Profile.update_of_ne _ _ hne]
        exact hcoordinates changed (by simp [hchanged])
      have htail := ih nextProfile hrest hrestCoordinates who action
      have hone :=
        G.mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le
          potential hbound history mixedProfile action t hfirstCoordinate
      have htriangle := abs_sub_le
        (G.mixedPotentialGain potential
          (G.advanceMarginals history t rest nextProfile) who action)
        (G.mixedPotentialGain potential nextProfile who action)
        (G.mixedPotentialGain potential mixedProfile who action)
      calc
        |G.mixedPotentialGain potential
              (G.advanceMarginals history t (first :: rest) mixedProfile)
              who action -
            G.mixedPotentialGain potential mixedProfile who action| =
            |G.mixedPotentialGain potential
                (G.advanceMarginals history t rest nextProfile) who action -
              G.mixedPotentialGain potential mixedProfile who action| := by
          rfl
        _ ≤ |G.mixedPotentialGain potential
                (G.advanceMarginals history t rest nextProfile) who action -
              G.mixedPotentialGain potential nextProfile who action| +
            |G.mixedPotentialGain potential nextProfile who action -
              G.mixedPotentialGain potential mixedProfile who action| :=
          htriangle
        _ ≤ (rest.length : ℝ) * stepError + stepError :=
          add_le_add htail hone
        _ = ((first :: rest).length : ℝ) * stepError := by
          simp [stepError]
          ring

/-- Sweeping a duplicate-free list of players increases mixed potential by
the first-order sum of their pure gains, up to a quadratic Cesàro error. -/
theorem mixedPotential_advanceMarginals_sub_ge
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (history : ℕ → Profile G.form.sig) (t : ℕ) :
    ∀ (players : List ι) (mixedProfile : Profile G.form.sig.mixed),
      players.Nodup →
      (∀ who, who ∈ players → mixedProfile who =
        G.empiricalMarginal history who (t + 1)) →
      (1 / (t + 2 : ℝ)) *
          (∑ who ∈ players.toFinset,
            G.mixedPotentialGain potential mixedProfile who
              (history (t + 1) who)) -
        ((players.length : ℝ) * (players.length : ℝ)) *
          ((1 / (t + 2 : ℝ)) ^ 2 * (4 * C)) ≤
        G.mixedPotential potential
            (G.advanceMarginals history t players mixedProfile) -
          G.mixedPotential potential mixedProfile := by
  intro players
  induction players with
  | nil =>
      intro mixedProfile _ _
      simp [advanceMarginals]
  | cons first rest ih =>
      intro mixedProfile hnodup hcoordinates
      have hrest : rest.Nodup := List.Nodup.of_cons hnodup
      have hfirst : first ∉ rest := (List.nodup_cons.mp hnodup).1
      let step : ℝ := 1 / (t + 2 : ℝ)
      let error : ℝ := step ^ 2 * (4 * C)
      let nextProfile : Profile G.form.sig.mixed :=
        Profile.update mixedProfile first
          (G.empiricalMarginal history first (t + 2))
      have hfirstCoordinate : mixedProfile first =
          G.empiricalMarginal history first (t + 1) :=
        hcoordinates first (by simp)
      have hrestCoordinates :
          ∀ who, who ∈ rest → nextProfile who =
            G.empiricalMarginal history who (t + 1) := by
        intro who hwho
        have hne : who ≠ first := by
          intro heq
          subst who
          exact hfirst hwho
        dsimp [nextProfile]
        rw [Profile.update_of_ne _ _ hne]
        exact hcoordinates who (by simp [hwho])
      have hinductionRaw := ih nextProfile hrest hrestCoordinates
      have hinduction :
          step * (∑ who ∈ rest.toFinset,
              G.mixedPotentialGain potential nextProfile who
                (history (t + 1) who)) -
            ((rest.length : ℝ) * (rest.length : ℝ)) * error ≤
          G.mixedPotential potential
              (G.advanceMarginals history t rest nextProfile) -
            G.mixedPotential potential nextProfile := by
        simpa [step, error] using hinductionRaw
      have hstep : 0 ≤ step := by positivity
      have hC : 0 ≤ C := by
        have hprofile := hbound (history 0)
        exact (abs_nonneg _).trans hprofile
      have herror : 0 ≤ error := by
        dsimp [error]
        positivity
      have hgainPoint : ∀ who ∈ rest.toFinset,
          G.mixedPotentialGain potential mixedProfile who
              (history (t + 1) who) ≤
            G.mixedPotentialGain potential nextProfile who
                (history (t + 1) who) + step * (4 * C) := by
        intro who hwhoFinset
        have hwho : who ∈ rest := by simpa using hwhoFinset
        have hboundStep :=
          G.mixedPotentialGain_update_empiricalMarginal_succ_abs_sub_le
            potential hbound history mixedProfile (history (t + 1) who) t
            hfirstCoordinate
        have hlower := (abs_le.mp hboundStep).1
        dsimp [nextProfile, step]
        linarith
      have hsum :
          (∑ who ∈ rest.toFinset,
              G.mixedPotentialGain potential mixedProfile who
                (history (t + 1) who)) ≤
            (∑ who ∈ rest.toFinset,
              G.mixedPotentialGain potential nextProfile who
                (history (t + 1) who)) +
              (rest.length : ℝ) * (step * (4 * C)) := by
        calc
          (∑ who ∈ rest.toFinset,
              G.mixedPotentialGain potential mixedProfile who
                (history (t + 1) who)) ≤
              ∑ who ∈ rest.toFinset,
                (G.mixedPotentialGain potential nextProfile who
                    (history (t + 1) who) + step * (4 * C)) :=
            Finset.sum_le_sum fun who hwho => hgainPoint who hwho
          _ = (∑ who ∈ rest.toFinset,
                G.mixedPotentialGain potential nextProfile who
                  (history (t + 1) who)) +
              (rest.toFinset.card : ℝ) * (step * (4 * C)) := by
            rw [Finset.sum_add_distrib]
            simp [Finset.sum_const, nsmul_eq_mul]
          _ = (∑ who ∈ rest.toFinset,
                G.mixedPotentialGain potential nextProfile who
                  (history (t + 1) who)) +
              (rest.length : ℝ) * (step * (4 * C)) := by
            rw [List.toFinset_card_of_nodup hrest]
      have hgainComparison :
          step * (∑ who ∈ rest.toFinset,
              G.mixedPotentialGain potential mixedProfile who
                (history (t + 1) who)) -
            (rest.length : ℝ) * error ≤
          step * (∑ who ∈ rest.toFinset,
              G.mixedPotentialGain potential nextProfile who
                (history (t + 1) who)) := by
        dsimp [error]
        nlinarith [mul_le_mul_of_nonneg_left hsum hstep]
      have hincrement :
          G.mixedPotential potential nextProfile -
              G.mixedPotential potential mixedProfile =
            step * G.mixedPotentialGain potential mixedProfile first
              (history (t + 1) first) := by
        simpa [nextProfile, step] using
          (G.mixedPotential_update_empiricalMarginal_succ_sub_of_eq
            potential history mixedProfile first t hfirstCoordinate)
      have hsumCons :
          (∑ who ∈ (first :: rest).toFinset,
              G.mixedPotentialGain potential mixedProfile who
                (history (t + 1) who)) =
            G.mixedPotentialGain potential mixedProfile first
                (history (t + 1) first) +
              ∑ who ∈ rest.toFinset,
                G.mixedPotentialGain potential mixedProfile who
                  (history (t + 1) who) := by
        simp [hfirst]
      rw [hsumCons]
      have htail :
          step * (∑ who ∈ rest.toFinset,
              G.mixedPotentialGain potential mixedProfile who
                (history (t + 1) who)) -
            (((rest.length : ℝ) * (rest.length : ℝ)) * error +
              (rest.length : ℝ) * error) ≤
          G.mixedPotential potential
              (G.advanceMarginals history t rest nextProfile) -
            G.mixedPotential potential nextProfile := by
        nlinarith [hgainComparison, hinduction]
      have hlengthError :
          (((rest.length : ℝ) * (rest.length : ℝ)) * error +
              (rest.length : ℝ) * error) ≤
            (((first :: rest).length : ℝ) *
              ((first :: rest).length : ℝ)) * error := by
        have hlength : (0 : ℝ) ≤ rest.length := by positivity
        simp only [List.length_cons]
        push_cast
        nlinarith
      calc
        step * (G.mixedPotentialGain potential mixedProfile first
              (history (t + 1) first) +
            ∑ who ∈ rest.toFinset,
              G.mixedPotentialGain potential mixedProfile who
                (history (t + 1) who)) -
          (((first :: rest).length : ℝ) *
            ((first :: rest).length : ℝ)) * error ≤
            (G.mixedPotential potential nextProfile -
                G.mixedPotential potential mixedProfile) +
              (G.mixedPotential potential
                  (G.advanceMarginals history t rest nextProfile) -
                G.mixedPotential potential nextProfile) := by
          nlinarith [hincrement, htail, hlengthError]
        _ = G.mixedPotential potential
              (G.advanceMarginals history t (first :: rest) mixedProfile) -
            G.mixedPotential potential mixedProfile := by
          show G.mixedPotential potential nextProfile -
                G.mixedPotential potential mixedProfile +
              (G.mixedPotential potential
                  (G.advanceMarginals history t rest nextProfile) -
                G.mixedPotential potential nextProfile) =
            G.mixedPotential potential
                (G.advanceMarginals history t rest nextProfile) -
              G.mixedPotential potential mixedProfile
          ring

/-- Advancing every player's coordinate turns the empirical belief at `t+1`
into the empirical belief at `t+2`. -/
theorem advanceMarginals_univ_eq_empiricalBelief_succ
    (history : ℕ → Profile G.form.sig) (t : ℕ) :
    G.advanceMarginals history t Finset.univ.toList
        (G.empiricalBelief history (t + 1)) =
      G.empiricalBelief history (t + 2) := by
  unfold advanceMarginals
  rw [Profile.foldl_update_eq _ _ _ Finset.univ.nodup_toList]
  funext who
  simp [empiricalBelief]

/-- Consecutive empirical beliefs change every fixed pure potential gain by at
most the player count times the one-coordinate bound. -/
theorem mixedPotentialGain_empiricalBelief_succ_abs_sub_le
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (history : ℕ → Profile G.form.sig) (who : ι)
    (action : G.form.sig.Strategy who) (t : ℕ) :
    |G.mixedPotentialGain potential (G.empiricalBelief history (t + 2))
          who action -
        G.mixedPotentialGain potential (G.empiricalBelief history (t + 1))
          who action| ≤
      (Fintype.card ι : ℝ) * ((1 / (t + 2 : ℝ)) * (4 * C)) := by
  have hsweep := G.mixedPotentialGain_advanceMarginals_abs_sub_le
    potential hbound history t Finset.univ.toList
    (G.empiricalBelief history (t + 1)) Finset.univ.nodup_toList
    (by intro changed _; rfl) who action
  rw [G.advanceMarginals_univ_eq_empiricalBelief_succ history t] at hsweep
  simpa using hsweep

/-- Exact potential transfers the consecutive-belief stability estimate to
canonical mixed expected-utility gains. -/
theorem IsExactPotential.mixedGain_empiricalBelief_succ_abs_sub_le
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    {C : ℝ} (hbound : ∀ profile, |potential profile| ≤ C)
    (history : ℕ → Profile G.form.sig) (who : ι)
    (action : G.form.sig.Strategy who) (t : ℕ) :
    |G.mixedGain (G.empiricalBelief history (t + 2)) who action -
        G.mixedGain (G.empiricalBelief history (t + 1)) who action| ≤
      (Fintype.card ι : ℝ) * ((1 / (t + 2 : ℝ)) * (4 * C)) := by
  have hboundGain := G.mixedPotentialGain_empiricalBelief_succ_abs_sub_le
    potential hbound history who action t
  rw [UtilityGame.IsExactPotential.mixedPotentialGain_eq_mixedGain
      (G := G) hpotential,
    UtilityGame.IsExactPotential.mixedPotentialGain_eq_mixedGain
      (G := G) hpotential] at hboundGain
  exact hboundGain

/-- Consecutive aggregate played gains along fictitious play differ by
`O(1/t)` in a bounded exact-potential game. -/
theorem IsExactPotential.aggregatePlayedGain_succ_abs_sub_le
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    {C : ℝ} (hbound : ∀ profile, |potential profile| ≤ C)
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) :
    |G.aggregatePlayedGain history (t + 1) -
        G.aggregatePlayedGain history t| ≤
      ((Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)) *
        ((1 / (t + 2 : ℝ)) * (4 * C)) := by
  let coordinateBound : ℝ :=
    (Fintype.card ι : ℝ) * ((1 / (t + 2 : ℝ)) * (4 * C))
  have hpoint : ∀ who : ι,
      |G.mixedGain (G.empiricalBelief history (t + 2)) who
            (history (t + 2) who) -
          G.mixedGain (G.empiricalBelief history (t + 1)) who
            (history (t + 1) who)| ≤ coordinateBound := by
    intro who
    have hnewBound :=
      UtilityGame.IsExactPotential.mixedGain_empiricalBelief_succ_abs_sub_le
        (G := G) hpotential hbound history who (history (t + 2) who) t
    have holdBound :=
      UtilityGame.IsExactPotential.mixedGain_empiricalBelief_succ_abs_sub_le
        (G := G) hpotential hbound history who (history (t + 1) who) t
    have hbestOld :=
      UtilityGame.IsFictitiousPlay.isBestResponse (G := G) hplay t who
        (FinDist.pure (history (t + 2) who))
    have hbestNew :=
      UtilityGame.IsFictitiousPlay.isBestResponse (G := G) hplay (t + 1) who
        (FinDist.pure (history (t + 1) who))
    rw [euPreference_apply] at hbestOld hbestNew
    have holdComparison :
        G.mixedGain (G.empiricalBelief history (t + 1)) who
            (history (t + 2) who) ≤
          G.mixedGain (G.empiricalBelief history (t + 1)) who
            (history (t + 1) who) := by
      unfold mixedGain
      linarith
    have hnewComparison :
        G.mixedGain (G.empiricalBelief history (t + 2)) who
            (history (t + 1) who) ≤
          G.mixedGain (G.empiricalBelief history (t + 2)) who
            (history (t + 2) who) := by
      unfold mixedGain
      linarith
    apply abs_le.mpr
    constructor
    · have hlower := (abs_le.mp holdBound).1
      linarith
    · have hupper := (abs_le.mp hnewBound).2
      linarith
  rw [aggregatePlayedGain, aggregatePlayedGain]
  have hsumSub :
      (∑ who : ι, G.playedGain history (t + 1) who) -
          (∑ who : ι, G.playedGain history t who) =
        ∑ who : ι,
          (G.playedGain history (t + 1) who -
            G.playedGain history t who) := by
    rw [Finset.sum_sub_distrib]
  rw [hsumSub]
  calc
    |∑ who : ι,
        (G.playedGain history (t + 1) who -
          G.playedGain history t who)| ≤
        ∑ who : ι,
          |G.playedGain history (t + 1) who -
            G.playedGain history t who| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _who : ι, coordinateBound :=
      Finset.sum_le_sum fun who _ => hpoint who
    _ = (Fintype.card ι : ℝ) * coordinateBound := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = ((Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)) *
        ((1 / (t + 2 : ℝ)) * (4 * C)) := by
      dsimp [coordinateBound]
      ring

/-- The all-player empirical update increases mixed potential by the played
gain's first-order term, up to the quadratic Cesàro error. -/
theorem IsExactPotential.mixedPotential_empiricalBelief_succ_sub_ge
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    {C : ℝ} (hbound : ∀ profile, |potential profile| ≤ C)
    (history : ℕ → Profile G.form.sig) (t : ℕ) :
    (1 / (t + 2 : ℝ)) * G.aggregatePlayedGain history t -
        ((Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)) *
          ((1 / (t + 2 : ℝ)) ^ 2 * (4 * C)) ≤
      G.mixedPotential potential (G.empiricalBelief history (t + 2)) -
        G.mixedPotential potential (G.empiricalBelief history (t + 1)) := by
  have hsweep := G.mixedPotential_advanceMarginals_sub_ge
    potential hbound history t Finset.univ.toList
    (G.empiricalBelief history (t + 1)) Finset.univ.nodup_toList
    (by intro who _; rfl)
  rw [G.advanceMarginals_univ_eq_empiricalBelief_succ history t] at hsweep
  have hsum :
      (∑ who ∈ (Finset.univ.toList : List ι).toFinset,
        G.mixedPotentialGain potential (G.empiricalBelief history (t + 1))
          who (history (t + 1) who)) =
        G.aggregatePlayedGain history t := by
    rw [aggregatePlayedGain]
    apply Finset.sum_congr
    · simp
    · intro who _
      simpa [playedGain] using
        (UtilityGame.IsExactPotential.mixedPotentialGain_eq_mixedGain
          (G := G) hpotential (G.empiricalBelief history (t + 1)) who
          (history (t + 1) who))
  have hlength :
      ((Finset.univ.toList : List ι).length : ℝ) =
        (Fintype.card ι : ℝ) := by simp
  rw [hsum, hlength] at hsweep
  exact hsweep

end UtilityGame

end GameTheory
