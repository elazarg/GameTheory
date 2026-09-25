/-
# Guarded empirical potential recurrences

Advancing one empirical marginal is an affine update of the multilinear
potential when the compared profile laws are integrable. In an exact-potential
game, its first-order increment is precisely the step size times the action's
current deviation gain. Asymptotic estimates live in `Analysis`.
-/

import GameTheory.Core.FictitiousPlay
import GameTheory.Core.MixedPotential

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo

namespace UtilityGame

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable (G : UtilityGame.{uι, us, uo} ι)

/-- Advancing one coordinate to its next empirical marginal is affine for the
mixed extension of every pure-profile observable. -/
theorem mixedPotential_update_empiricalMarginal_succ
    (potential : Profile G.form.sig → ℝ)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ)
    (hprev : PayoffIntegrable
      (independentProduct (Profile.update mixedProfile who
        (G.form.empiricalMarginal history who (t + 1)))) potential)
    (hpure : PayoffIntegrable
      (independentProduct (Profile.update mixedProfile who
        (PMF.pure (history (t + 1) who)))) potential) :
    ∃ hnext : PayoffIntegrable
      (independentProduct (Profile.update mixedProfile who
        (G.form.empiricalMarginal history who (t + 2)))) potential,
    G.form.mixedPotential potential
        (Profile.update mixedProfile who
          (G.form.empiricalMarginal history who (t + 2))) hnext =
      ((t + 1 : ℝ) / (t + 2 : ℝ)) *
          G.form.mixedPotential potential
            (Profile.update mixedProfile who
              (G.form.empiricalMarginal history who (t + 1))) hprev +
        (1 / (t + 2 : ℝ)) *
          G.form.mixedPotential potential
            (Profile.update mixedProfile who
              (PMF.pure (history (t + 1) who))) hpure := by
  let w := (t + 1 : ℝ) / (t + 2 : ℝ)
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hw1 : w ≤ 1 := by
    dsimp [w]
    have hn : (0 : ℝ) < t + 2 := by positivity
    rw [div_le_iff₀ hn]
    norm_num
  have hlaw := G.form.empiricalProduct_succ_mix history mixedProfile who t
  let hmix := payoffIntegrable_mix w hw0 hw1 _ _ potential hprev hpure
  have hnext := payoffIntegrable_congr_law hlaw.symm hmix
  refine ⟨hnext, ?_⟩
  calc
    G.form.mixedPotential potential
        (Profile.update mixedProfile who
          (G.form.empiricalMarginal history who (t + 2))) hnext =
      expect (mix w hw0 hw1
        (independentProduct (Profile.update mixedProfile who
          (G.form.empiricalMarginal history who (t + 1))))
        (independentProduct (Profile.update mixedProfile who
          (PMF.pure (history (t + 1) who))))) potential hmix :=
      expect_congr_law hlaw _ _ _
    _ = w * G.form.mixedPotential potential
          (Profile.update mixedProfile who
            (G.form.empiricalMarginal history who (t + 1))) hprev +
        (1 - w) * G.form.mixedPotential potential
          (Profile.update mixedProfile who
            (PMF.pure (history (t + 1) who))) hpure :=
      expect_mix w hw0 hw1 _ _ potential hprev hpure
    _ = _ := by
      dsimp [w]
      rw [show 1 - (t + 1 : ℝ) / (t + 2) = 1 / (t + 2) by
        field_simp; ring]

/-- Difference form of the one-coordinate empirical-potential recurrence. -/
theorem mixedPotential_update_empiricalMarginal_succ_sub
    (potential : Profile G.form.sig → ℝ)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ)
    (hprev : PayoffIntegrable
      (independentProduct (Profile.update mixedProfile who
        (G.form.empiricalMarginal history who (t + 1)))) potential)
    (hpure : PayoffIntegrable
      (independentProduct (Profile.update mixedProfile who
        (PMF.pure (history (t + 1) who)))) potential) :
    ∃ hnext : PayoffIntegrable
      (independentProduct (Profile.update mixedProfile who
        (G.form.empiricalMarginal history who (t + 2)))) potential,
    G.form.mixedPotential potential
        (Profile.update mixedProfile who
          (G.form.empiricalMarginal history who (t + 2))) hnext -
      G.form.mixedPotential potential
        (Profile.update mixedProfile who
          (G.form.empiricalMarginal history who (t + 1))) hprev =
      (1 / (t + 2 : ℝ)) *
        (G.form.mixedPotential potential
            (Profile.update mixedProfile who
              (PMF.pure (history (t + 1) who))) hpure -
          G.form.mixedPotential potential
            (Profile.update mixedProfile who
              (G.form.empiricalMarginal history who (t + 1))) hprev) := by
  obtain ⟨hnext, hrecurrence⟩ :=
    G.mixedPotential_update_empiricalMarginal_succ potential history
      mixedProfile who t hprev hpure
  refine ⟨hnext, ?_⟩
  rw [hrecurrence]
  have hnonzero : (t + 2 : ℝ) ≠ 0 := by positivity
  field_simp [hnonzero]
  ring

/-- The gain in mixed potential from replacing one marginal by a pure action. -/
def mixedPotentialGain (potential : Profile G.form.sig → ℝ)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who)
    (hbase : PayoffIntegrable (independentProduct mixedProfile) potential)
    (hupdated : PayoffIntegrable
      (independentProduct
        (Profile.update mixedProfile who (PMF.pure action))) potential) : ℝ :=
  G.form.mixedPotential potential
      (Profile.update mixedProfile who (PMF.pure action)) hupdated -
    G.form.mixedPotential potential mixedProfile hbase

/-- A bounded pure-profile potential induces integrable actual laws for each
mixed gain, so the guarded gain has a canonical scalar specialization. -/
abbrev mixedPotentialGainOfAbsBound
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who) : ℝ :=
  G.mixedPotentialGain potential mixedProfile who action
    (payoffIntegrable_of_bounded (independentProduct mixedProfile)
      potential hbound)
    (payoffIntegrable_of_bounded (independentProduct
      (Profile.update mixedProfile who (PMF.pure action))) potential hbound)

/-- If the updated coordinate is still the old empirical marginal, the
potential increment is the step size times the matching pure gain. -/
theorem mixedPotential_update_empiricalMarginal_succ_sub_of_eq
    (potential : Profile G.form.sig → ℝ)
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ)
    (hcoordinate : mixedProfile who =
      G.form.empiricalMarginal history who (t + 1))
    (hprev : PayoffIntegrable
      (independentProduct (Profile.update mixedProfile who
        (G.form.empiricalMarginal history who (t + 1)))) potential)
    (hpure : PayoffIntegrable
      (independentProduct (Profile.update mixedProfile who
        (PMF.pure (history (t + 1) who)))) potential)
    (hbasePotential : PayoffIntegrable
      (independentProduct mixedProfile) potential) :
    ∃ hnext : PayoffIntegrable
      (independentProduct (Profile.update mixedProfile who
        (G.form.empiricalMarginal history who (t + 2)))) potential,
    G.form.mixedPotential potential
        (Profile.update mixedProfile who
          (G.form.empiricalMarginal history who (t + 2))) hnext -
      G.form.mixedPotential potential mixedProfile hbasePotential =
      (1 / (t + 2 : ℝ)) *
        G.mixedPotentialGain potential mixedProfile who
          (history (t + 1) who) hbasePotential hpure := by
  have hupdate :
      Profile.update mixedProfile who
          (G.form.empiricalMarginal history who (t + 1)) = mixedProfile := by
    rw [← hcoordinate]
    exact Profile.update_eq_self mixedProfile who
  have hbaseLaw :
      independentProduct (Profile.update mixedProfile who
        (G.form.empiricalMarginal history who (t + 1))) =
      independentProduct mixedProfile := by
    rw [hupdate]
  have hprevBase : PayoffIntegrable
      (independentProduct mixedProfile) potential :=
    payoffIntegrable_congr_law hbaseLaw hprev
  have hprevValue :
      G.form.mixedPotential potential
          (Profile.update mixedProfile who
            (G.form.empiricalMarginal history who (t + 1))) hprev =
        G.form.mixedPotential potential mixedProfile hbasePotential := by
    unfold GameForm.mixedPotential
    calc
      expect (independentProduct
          (Profile.update mixedProfile who
            (G.form.empiricalMarginal history who (t + 1)))) potential hprev =
        expect (independentProduct mixedProfile) potential hprevBase :=
          expect_congr_law hbaseLaw potential hprev hprevBase
      _ = expect (independentProduct mixedProfile) potential hbasePotential :=
        expect_proof_irrel _ _ _ _
  obtain ⟨hnext, hrecurrence⟩ :=
    G.mixedPotential_update_empiricalMarginal_succ_sub
      potential history mixedProfile who t hprev hpure
  refine ⟨hnext, ?_⟩
  have hgain := hrecurrence
  rw [hprevValue] at hgain
  simpa only [mixedPotentialGain] using hgain

/-- Exact potential identifies every pure mixed-potential gain with the
corresponding expected-utility gain. -/
theorem IsExactPotential.mixedPotentialGain_eq_mixedGain
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who)
    (hbaseUtility : UtilityIntegrable G.utility who
      (G.form.mixed.play mixedProfile))
    (hnewUtility : UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who (PMF.pure action))))
    (hbasePotential : PayoffIntegrable
      (independentProduct mixedProfile) potential)
    (hnewPotential : PayoffIntegrable
      (independentProduct
        (Profile.update mixedProfile who (PMF.pure action))) potential) :
    G.mixedPotentialGain potential mixedProfile who action
        hbasePotential hnewPotential =
      G.mixedGain mixedProfile who action hbaseUtility hnewUtility := by
  exact (UtilityGame.IsExactPotential.mixed_pure_diff
    (G := G) hpotential mixedProfile who action hbaseUtility hnewUtility
      hbasePotential hnewPotential).symm

/-- In an exact-potential game, advancing one empirical-belief coordinate has
increment equal to the step size times that player's played gain. -/
theorem IsExactPotential.mixedPotential_belief_update_empiricalMarginal_succ_sub
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    (history : ℕ → Profile G.form.sig) (who : ι) (t : ℕ)
    (hbaseUtility : UtilityIntegrable G.utility who
      (G.form.mixed.play (G.form.empiricalBelief history (t + 1))))
    (hplayedUtility : UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update (G.form.empiricalBelief history (t + 1)) who
          (PMF.pure (history (t + 1) who)))))
    (hbasePotential : PayoffIntegrable
      (independentProduct (G.form.empiricalBelief history (t + 1))) potential)
    (hplayedPotential : PayoffIntegrable
      (independentProduct
        (Profile.update (G.form.empiricalBelief history (t + 1)) who
          (PMF.pure (history (t + 1) who)))) potential) :
    ∃ hnext : PayoffIntegrable
      (independentProduct
        (Profile.update (G.form.empiricalBelief history (t + 1)) who
          (G.form.empiricalMarginal history who (t + 2)))) potential,
    G.form.mixedPotential potential
        (Profile.update (G.form.empiricalBelief history (t + 1)) who
          (G.form.empiricalMarginal history who (t + 2))) hnext -
      G.form.mixedPotential potential (G.form.empiricalBelief history (t + 1))
        hbasePotential =
      (1 / (t + 2 : ℝ)) *
        G.playedGain history t who hbaseUtility hplayedUtility := by
  have hcoordinate :
      G.form.empiricalBelief history (t + 1) who =
        G.form.empiricalMarginal history who (t + 1) := rfl
  have hupdate :
      Profile.update (G.form.empiricalBelief history (t + 1)) who
          (G.form.empiricalMarginal history who (t + 1)) =
        G.form.empiricalBelief history (t + 1) := by
    rw [← hcoordinate]
    exact Profile.update_eq_self _ _
  have hprevLaw := congrArg independentProduct hupdate
  have hprevPotential : PayoffIntegrable
      (independentProduct
        (Profile.update (G.form.empiricalBelief history (t + 1)) who
          (G.form.empiricalMarginal history who (t + 1)))) potential := by
    exact payoffIntegrable_congr_law hprevLaw.symm hbasePotential
  obtain ⟨hnextPotential, hincrement⟩ :=
    G.mixedPotential_update_empiricalMarginal_succ_sub_of_eq
      potential history (G.form.empiricalBelief history (t + 1)) who t
      hcoordinate hprevPotential hplayedPotential hbasePotential
  have hgain := IsExactPotential.mixedPotentialGain_eq_mixedGain
    (G := G) hpotential (G.form.empiricalBelief history (t + 1)) who
    (history (t + 1) who) hbaseUtility hplayedUtility hbasePotential
    hplayedPotential
  refine ⟨hnextPotential, ?_⟩
  calc
    _ = (1 / (t + 2 : ℝ)) *
        G.mixedPotentialGain potential
          (G.form.empiricalBelief history (t + 1)) who
          (history (t + 1) who) hbasePotential hplayedPotential := by
      simpa only [hupdate] using hincrement
    _ = (1 / (t + 2 : ℝ)) *
        G.playedGain history t who hbaseUtility hplayedUtility := by
      rw [hgain]
      rfl

omit [DecidableEq ι] in
/-- A uniform absolute bound on pure profiles also bounds the multilinear
mixed potential. -/
theorem mixedPotential_abs_le_of_abs_bound
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (mixedProfile : Profile G.form.sig.mixed) :
    |G.form.mixedPotential potential mixedProfile
      (payoffIntegrable_of_bounded (independentProduct mixedProfile)
        potential hbound)| ≤ C := by
  let μ := independentProduct mixedProfile
  let hp := payoffIntegrable_of_bounded μ potential hbound
  obtain ⟨profile, _⟩ := μ.support_nonempty
  have hC : 0 ≤ C := (abs_nonneg _).trans (hbound profile)
  have hplus : PayoffIntegrable μ (fun _ => C) :=
    payoffIntegrable_of_bounded μ (fun _ => C) (C := C) (fun _ => by
      simp [abs_of_nonneg hC])
  have hminus : PayoffIntegrable μ (fun _ => -C) :=
    payoffIntegrable_of_bounded μ (fun _ => -C) (C := C) (fun _ => by
      simp [abs_of_nonpos (neg_nonpos.mpr hC)])
  have hupper : expect μ potential hp ≤ expect μ (fun _ => C) hplus :=
    expect_mono (fun a _ => (abs_le.mp (hbound a)).2) hp hplus
  have hlower : expect μ (fun _ => -C) hminus ≤ expect μ potential hp :=
    expect_mono (fun a _ => (abs_le.mp (hbound a)).1) hminus hp
  rw [expect_constant μ C hplus] at hupper
  rw [expect_constant μ (-C) hminus] at hlower
  simpa only [GameForm.mixedPotential, μ, hp] using
    (abs_le.mpr ⟨by linarith, by linarith⟩)

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
      G.form.empiricalMarginal history who (t + 1)) :
    |G.form.mixedPotential potential
          (Profile.update mixedProfile who
            (G.form.empiricalMarginal history who (t + 2)))
          (payoffIntegrable_of_bounded
            (independentProduct (Profile.update mixedProfile who
              (G.form.empiricalMarginal history who (t + 2))))
            potential hbound) -
        G.form.mixedPotential potential mixedProfile
          (payoffIntegrable_of_bounded
            (independentProduct mixedProfile) potential hbound)| ≤
      (1 / (t + 2 : ℝ)) * (2 * C) := by
  let hprev := payoffIntegrable_of_bounded
    (independentProduct (Profile.update mixedProfile who
      (G.form.empiricalMarginal history who (t + 1)))) potential hbound
  let hpure := payoffIntegrable_of_bounded
    (independentProduct (Profile.update mixedProfile who
      (PMF.pure (history (t + 1) who)))) potential hbound
  let hbase := payoffIntegrable_of_bounded
    (independentProduct mixedProfile) potential hbound
  obtain ⟨hnext, hrecurrence⟩ :=
    G.mixedPotential_update_empiricalMarginal_succ_sub_of_eq
      potential history mixedProfile who t hcoordinate hprev hpure hbase
  have hpureBound := G.mixedPotential_abs_le_of_abs_bound potential hbound
    (Profile.update mixedProfile who (PMF.pure (history (t + 1) who)))
  have hbaseBound := G.mixedPotential_abs_le_of_abs_bound potential hbound
    mixedProfile
  have hdiff :
      |G.form.mixedPotential potential
          (Profile.update mixedProfile who
            (PMF.pure (history (t + 1) who))) hpure -
        G.form.mixedPotential potential mixedProfile hbase| ≤ 2 * C := by
    have htriangle := abs_sub
      (G.form.mixedPotential potential
        (Profile.update mixedProfile who
          (PMF.pure (history (t + 1) who))) hpure)
      (G.form.mixedPotential potential mixedProfile hbase)
    linarith
  have hstep : 0 ≤ (1 / (t + 2 : ℝ)) := by positivity
  calc
    |G.form.mixedPotential potential
          (Profile.update mixedProfile who
            (G.form.empiricalMarginal history who (t + 2)))
          (payoffIntegrable_of_bounded
            (independentProduct (Profile.update mixedProfile who
              (G.form.empiricalMarginal history who (t + 2))))
            potential hbound) -
        G.form.mixedPotential potential mixedProfile
          (payoffIntegrable_of_bounded
            (independentProduct mixedProfile) potential hbound)| =
        |(1 / (t + 2 : ℝ)) *
          G.mixedPotentialGain potential mixedProfile who
            (history (t + 1) who) hbase hpure| := by rw [hrecurrence]
    _ = (1 / (t + 2 : ℝ)) *
        |G.mixedPotentialGain potential mixedProfile who
          (history (t + 1) who) hbase hpure| := by
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
      G.form.empiricalMarginal history changed (t + 1)) :
    |G.mixedPotentialGainOfAbsBound potential hbound
          (Profile.update mixedProfile changed
            (G.form.empiricalMarginal history changed (t + 2))) who action -
        G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who
          action| ≤
      (1 / (t + 2 : ℝ)) * (4 * C) := by
  have hpureCoordinate :
      Profile.update mixedProfile who (PMF.pure action) changed =
        G.form.empiricalMarginal history changed (t + 1) := by
    rw [Profile.update_of_ne _ _ hne]
    exact hcoordinate
  have hpureStep :=
    G.mixedPotential_update_empiricalMarginal_succ_abs_sub_le
      potential hbound history
      (Profile.update mixedProfile who (PMF.pure action)) changed t
      hpureCoordinate
  have hbaseStep :=
    G.mixedPotential_update_empiricalMarginal_succ_abs_sub_le
      potential hbound history mixedProfile changed t hcoordinate
  simp only [mixedPotentialGainOfAbsBound, mixedPotentialGain]
  have hcommute :
      Profile.update
          (Profile.update mixedProfile changed
            (G.form.empiricalMarginal history changed (t + 2)))
          who (PMF.pure action) =
        Profile.update
          (Profile.update mixedProfile who (PMF.pure action))
          changed (G.form.empiricalMarginal history changed (t + 2)) :=
    Profile.update_comm mixedProfile hne
      (G.form.empiricalMarginal history changed (t + 2)) (PMF.pure action)
  let hp (profile : Profile G.form.sig.mixed) :
      PayoffIntegrable (independentProduct profile) potential :=
    payoffIntegrable_of_bounded (independentProduct profile) potential hbound
  have hcross :
      G.form.mixedPotential potential
          (Profile.update
            (Profile.update mixedProfile changed
              (G.form.empiricalMarginal history changed (t + 2)))
            who (PMF.pure action))
          (hp (Profile.update
            (Profile.update mixedProfile changed
              (G.form.empiricalMarginal history changed (t + 2)))
            who (PMF.pure action))) =
        G.form.mixedPotential potential
          (Profile.update
            (Profile.update mixedProfile who (PMF.pure action)) changed
            (G.form.empiricalMarginal history changed (t + 2)))
          (hp (Profile.update
            (Profile.update mixedProfile who (PMF.pure action)) changed
            (G.form.empiricalMarginal history changed (t + 2)))) := by
    unfold GameForm.mixedPotential
    exact expect_congr_law (congrArg independentProduct hcommute) potential
      _ _
  have hrewrite :
      G.form.mixedPotential potential
          (Profile.update
            (Profile.update mixedProfile who (PMF.pure action)) changed
            (G.form.empiricalMarginal history changed (t + 2)))
          (hp (Profile.update
            (Profile.update mixedProfile who (PMF.pure action)) changed
            (G.form.empiricalMarginal history changed (t + 2)))) -
        G.form.mixedPotential potential
          (Profile.update mixedProfile changed
            (G.form.empiricalMarginal history changed (t + 2)))
          (hp (Profile.update mixedProfile changed
            (G.form.empiricalMarginal history changed (t + 2)))) -
        (G.form.mixedPotential potential
          (Profile.update mixedProfile who (PMF.pure action))
          (hp (Profile.update mixedProfile who (PMF.pure action))) -
          G.form.mixedPotential potential mixedProfile (hp mixedProfile)) =
      (G.form.mixedPotential potential
          (Profile.update
            (Profile.update mixedProfile who (PMF.pure action)) changed
            (G.form.empiricalMarginal history changed (t + 2)))
          (hp (Profile.update
            (Profile.update mixedProfile who (PMF.pure action)) changed
            (G.form.empiricalMarginal history changed (t + 2)))) -
        G.form.mixedPotential potential
          (Profile.update mixedProfile who (PMF.pure action))
          (hp (Profile.update mixedProfile who (PMF.pure action)))) -
      (G.form.mixedPotential potential
          (Profile.update mixedProfile changed
            (G.form.empiricalMarginal history changed (t + 2)))
          (hp (Profile.update mixedProfile changed
            (G.form.empiricalMarginal history changed (t + 2)))) -
        G.form.mixedPotential potential mixedProfile (hp mixedProfile)) := by ring
  rw [hcross, hrewrite]
  calc
    _ ≤ |G.form.mixedPotential potential
          (Profile.update
            (Profile.update mixedProfile who (PMF.pure action)) changed
             (G.form.empiricalMarginal history changed (t + 2)))
          (hp ((Profile.update
            (Profile.update mixedProfile who (PMF.pure action)) changed
            (G.form.empiricalMarginal history changed (t + 2))))) -
        G.form.mixedPotential potential
          (Profile.update mixedProfile who (PMF.pure action))
          (hp (Profile.update mixedProfile who (PMF.pure action)))| +
      |G.form.mixedPotential potential
          (Profile.update mixedProfile changed
            (G.form.empiricalMarginal history changed (t + 2)))
          (hp (Profile.update mixedProfile changed
            (G.form.empiricalMarginal history changed (t + 2)))) -
        G.form.mixedPotential potential mixedProfile (hp mixedProfile)| :=
          abs_sub _ _
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
      G.form.empiricalMarginal history who (t + 1)) :
    |G.mixedPotentialGainOfAbsBound potential hbound
          (Profile.update mixedProfile who
            (G.form.empiricalMarginal history who (t + 2))) who action -
        G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who
          action| ≤
      (1 / (t + 2 : ℝ)) * (2 * C) := by
  have hstep := G.mixedPotential_update_empiricalMarginal_succ_abs_sub_le
    potential hbound history mixedProfile who t hcoordinate
  let hp (profile : Profile G.form.sig.mixed) :
      PayoffIntegrable (independentProduct profile) potential :=
    payoffIntegrable_of_bounded (independentProduct profile) potential hbound
  simp only [mixedPotentialGainOfAbsBound, mixedPotentialGain,
    Profile.update_idem]
  have hrewrite :
      G.form.mixedPotential potential
          (Profile.update mixedProfile who (PMF.pure action))
          (hp (Profile.update mixedProfile who (PMF.pure action))) -
        G.form.mixedPotential potential
          (Profile.update mixedProfile who
            (G.form.empiricalMarginal history who (t + 2)))
          (hp (Profile.update mixedProfile who
            (G.form.empiricalMarginal history who (t + 2)))) -
        (G.form.mixedPotential potential
          (Profile.update mixedProfile who (PMF.pure action))
          (hp (Profile.update mixedProfile who (PMF.pure action))) -
          G.form.mixedPotential potential mixedProfile (hp mixedProfile)) =
      -(G.form.mixedPotential potential
          (Profile.update mixedProfile who
            (G.form.empiricalMarginal history who (t + 2)))
          (hp (Profile.update mixedProfile who
            (G.form.empiricalMarginal history who (t + 2)))) -
        G.form.mixedPotential potential mixedProfile (hp mixedProfile)) := by
    ring
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
      G.form.empiricalMarginal history changed (t + 1)) :
    |G.mixedPotentialGain potential
          (Profile.update mixedProfile changed
            (G.form.empiricalMarginal history changed (t + 2))) who action
          (payoffIntegrable_of_bounded (independentProduct
            (Profile.update mixedProfile changed
              (G.form.empiricalMarginal history changed (t + 2))))
            potential hbound)
          (payoffIntegrable_of_bounded (independentProduct
            ((Profile.update mixedProfile changed
              (G.form.empiricalMarginal history changed (t + 2))).update
                who (PMF.pure action))) potential hbound) -
        G.mixedPotentialGain potential mixedProfile who action
          (payoffIntegrable_of_bounded (independentProduct mixedProfile)
            potential hbound)
          (payoffIntegrable_of_bounded (independentProduct
            (Profile.update mixedProfile who (PMF.pure action)))
            potential hbound)| ≤
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
      (G.form.empiricalMarginal history changed (t + 2))) mixedProfile

/-- Sweeping a duplicate-free list of empirical updates changes any fixed
pure potential gain by at most the list length times the one-step bound. -/
theorem mixedPotentialGain_advanceMarginals_abs_sub_le
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (history : ℕ → Profile G.form.sig) (t : ℕ) :
    ∀ (players : List ι) (mixedProfile : Profile G.form.sig.mixed),
      players.Nodup →
      (∀ changed, changed ∈ players → mixedProfile changed =
        G.form.empiricalMarginal history changed (t + 1)) →
        ∀ (who : ι) (action : G.form.sig.Strategy who),
        |G.mixedPotentialGainOfAbsBound potential hbound
            (G.advanceMarginals history t players mixedProfile) who action -
          G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who
            action| ≤
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
          (G.form.empiricalMarginal history first (t + 2))
      have hfirstCoordinate : mixedProfile first =
          G.form.empiricalMarginal history first (t + 1) :=
        hcoordinates first (by simp)
      have hrestCoordinates :
          ∀ changed, changed ∈ rest → nextProfile changed =
            G.form.empiricalMarginal history changed (t + 1) := by
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
        (G.mixedPotentialGainOfAbsBound potential hbound
          (G.advanceMarginals history t rest nextProfile) who action)
        (G.mixedPotentialGainOfAbsBound potential hbound nextProfile who action)
        (G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who action)
      calc
        |G.mixedPotentialGainOfAbsBound potential hbound
              (G.advanceMarginals history t (first :: rest) mixedProfile)
              who action -
            G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who
              action| =
            |G.mixedPotentialGainOfAbsBound potential hbound
                (G.advanceMarginals history t rest nextProfile) who action -
              G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who
                action| := by
          rfl
        _ ≤ |G.mixedPotentialGainOfAbsBound potential hbound
                (G.advanceMarginals history t rest nextProfile) who action -
              G.mixedPotentialGainOfAbsBound potential hbound nextProfile who
                action| +
            |G.mixedPotentialGainOfAbsBound potential hbound nextProfile who
                action -
              G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who
                action| :=
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
        G.form.empiricalMarginal history who (t + 1)) →
      (1 / (t + 2 : ℝ)) *
          (∑ who ∈ players.toFinset,
            G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who
              (history (t + 1) who)) -
        ((players.length : ℝ) * (players.length : ℝ)) *
          ((1 / (t + 2 : ℝ)) ^ 2 * (4 * C)) ≤
        G.form.mixedPotential potential
            (G.advanceMarginals history t players mixedProfile)
            (payoffIntegrable_of_bounded (independentProduct
              (G.advanceMarginals history t players mixedProfile))
              potential hbound) -
          G.form.mixedPotential potential mixedProfile
            (payoffIntegrable_of_bounded (independentProduct mixedProfile)
              potential hbound) := by
  let V (profile : Profile G.form.sig.mixed) : ℝ :=
    G.form.mixedPotential potential profile
      (payoffIntegrable_of_bounded (independentProduct profile)
        potential hbound)
  intro players
  induction players with
  | nil =>
      intro mixedProfile _ _
      simp [advanceMarginals, List.foldl_nil]
  | cons first rest ih =>
      intro mixedProfile hnodup hcoordinates
      have hrest : rest.Nodup := List.Nodup.of_cons hnodup
      have hfirst : first ∉ rest := (List.nodup_cons.mp hnodup).1
      let step : ℝ := 1 / (t + 2 : ℝ)
      let error : ℝ := step ^ 2 * (4 * C)
      let nextProfile : Profile G.form.sig.mixed :=
        Profile.update mixedProfile first
          (G.form.empiricalMarginal history first (t + 2))
      have hfirstCoordinate : mixedProfile first =
          G.form.empiricalMarginal history first (t + 1) :=
        hcoordinates first (by simp)
      have hrestCoordinates :
          ∀ who, who ∈ rest → nextProfile who =
            G.form.empiricalMarginal history who (t + 1) := by
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
              G.mixedPotentialGainOfAbsBound potential hbound nextProfile who
                (history (t + 1) who)) -
            ((rest.length : ℝ) * (rest.length : ℝ)) * error ≤
          V
              (G.advanceMarginals history t rest nextProfile) -
            V nextProfile := by
        simpa [step, error, V] using hinductionRaw
      have hstep : 0 ≤ step := by positivity
      have hC : 0 ≤ C := by
        have hprofile := hbound (history 0)
        exact (abs_nonneg _).trans hprofile
      have herror : 0 ≤ error := by
        dsimp [error]
        positivity
      have hgainPoint : ∀ who ∈ rest.toFinset,
          G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who
              (history (t + 1) who) ≤
            G.mixedPotentialGainOfAbsBound potential hbound nextProfile who
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
              G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who
                (history (t + 1) who)) ≤
            (∑ who ∈ rest.toFinset,
              G.mixedPotentialGainOfAbsBound potential hbound nextProfile who
                (history (t + 1) who)) +
              (rest.length : ℝ) * (step * (4 * C)) := by
        calc
          (∑ who ∈ rest.toFinset,
              G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who
                (history (t + 1) who)) ≤
              ∑ who ∈ rest.toFinset,
                (G.mixedPotentialGainOfAbsBound potential hbound nextProfile who
                    (history (t + 1) who) + step * (4 * C)) :=
            Finset.sum_le_sum fun who hwho => hgainPoint who hwho
          _ = (∑ who ∈ rest.toFinset,
                G.mixedPotentialGainOfAbsBound potential hbound nextProfile who
                  (history (t + 1) who)) +
              (rest.toFinset.card : ℝ) * (step * (4 * C)) := by
            rw [Finset.sum_add_distrib]
            simp [Finset.sum_const, nsmul_eq_mul]
          _ = (∑ who ∈ rest.toFinset,
                G.mixedPotentialGainOfAbsBound potential hbound nextProfile who
                  (history (t + 1) who)) +
              (rest.length : ℝ) * (step * (4 * C)) := by
            rw [List.toFinset_card_of_nodup hrest]
      have hgainComparison :
          step * (∑ who ∈ rest.toFinset,
              G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who
                (history (t + 1) who)) -
            (rest.length : ℝ) * error ≤
          step * (∑ who ∈ rest.toFinset,
              G.mixedPotentialGainOfAbsBound potential hbound nextProfile who
                (history (t + 1) who)) := by
        dsimp [error]
        nlinarith [mul_le_mul_of_nonneg_left hsum hstep]
      have hincrement :
          V nextProfile -
              V mixedProfile =
            step * G.mixedPotentialGainOfAbsBound potential hbound mixedProfile first
              (history (t + 1) first) := by
        obtain ⟨hnext, hrecurrence⟩ :=
          G.mixedPotential_update_empiricalMarginal_succ_sub_of_eq
            potential history mixedProfile first t hfirstCoordinate
            (payoffIntegrable_of_bounded (independentProduct
              (Profile.update mixedProfile first
                (G.form.empiricalMarginal history first (t + 1))))
              potential hbound)
            (payoffIntegrable_of_bounded (independentProduct
              (Profile.update mixedProfile first
                (PMF.pure (history (t + 1) first)))) potential hbound)
            (payoffIntegrable_of_bounded (independentProduct mixedProfile)
              potential hbound)
        simpa [nextProfile, step, V] using hrecurrence
      have hsumCons :
          (∑ who ∈ (first :: rest).toFinset,
              G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who
                (history (t + 1) who)) =
            G.mixedPotentialGainOfAbsBound potential hbound mixedProfile first
                (history (t + 1) first) +
              ∑ who ∈ rest.toFinset,
                G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who
                  (history (t + 1) who) := by
        simp [hfirst]
      rw [hsumCons]
      have htail :
          step * (∑ who ∈ rest.toFinset,
              G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who
                (history (t + 1) who)) -
            (((rest.length : ℝ) * (rest.length : ℝ)) * error +
              (rest.length : ℝ) * error) ≤
          V
              (G.advanceMarginals history t rest nextProfile) -
            V nextProfile := by
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
        step * (G.mixedPotentialGainOfAbsBound potential hbound mixedProfile first
              (history (t + 1) first) +
            ∑ who ∈ rest.toFinset,
              G.mixedPotentialGainOfAbsBound potential hbound mixedProfile who
                (history (t + 1) who)) -
          (((first :: rest).length : ℝ) *
            ((first :: rest).length : ℝ)) * error ≤
            (V nextProfile -
                V mixedProfile) +
              (V
                  (G.advanceMarginals history t rest nextProfile) -
                V nextProfile) := by
          nlinarith [hincrement, htail, hlengthError]
        _ = V
              (G.advanceMarginals history t (first :: rest) mixedProfile) -
            V mixedProfile := by
          show V nextProfile -
                V mixedProfile +
              (V
                  (G.advanceMarginals history t rest nextProfile) -
                V nextProfile) =
            V
                (G.advanceMarginals history t rest nextProfile) -
              V mixedProfile
          ring

/-- Advancing every player's coordinate turns the empirical belief at `t+1`
into the empirical belief at `t+2`. -/
theorem advanceMarginals_univ_eq_empiricalBelief_succ
    (history : ℕ → Profile G.form.sig) (t : ℕ) :
    G.advanceMarginals history t Finset.univ.toList
        (G.form.empiricalBelief history (t + 1)) =
      G.form.empiricalBelief history (t + 2) := by
  unfold advanceMarginals
  rw [Profile.foldl_update_eq _ _ _ Finset.univ.nodup_toList]
  funext who
  simp [GameForm.empiricalBelief]

/-- Consecutive empirical beliefs change every fixed pure potential gain by at
most the player count times the one-coordinate bound. -/
theorem mixedPotentialGain_empiricalBelief_succ_abs_sub_le
    (potential : Profile G.form.sig → ℝ) {C : ℝ}
    (hbound : ∀ profile, |potential profile| ≤ C)
    (history : ℕ → Profile G.form.sig) (who : ι)
    (action : G.form.sig.Strategy who) (t : ℕ) :
    |G.mixedPotentialGainOfAbsBound potential hbound (G.form.empiricalBelief history (t + 2))
          who action -
        G.mixedPotentialGainOfAbsBound potential hbound (G.form.empiricalBelief history (t + 1))
          who action| ≤
      (Fintype.card ι : ℝ) * ((1 / (t + 2 : ℝ)) * (4 * C)) := by
  have hsweep := G.mixedPotentialGain_advanceMarginals_abs_sub_le
    potential hbound history t Finset.univ.toList
    (G.form.empiricalBelief history (t + 1)) Finset.univ.nodup_toList
    (by intro changed _; rfl) who action
  rw [G.advanceMarginals_univ_eq_empiricalBelief_succ history t] at hsweep
  simpa using hsweep

/-- Exact potential transfers the consecutive-belief stability estimate to
canonical mixed expected-utility gains. -/
theorem IsExactPotential.mixedGain_empiricalBelief_succ_abs_sub_le
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    {C : ℝ} (hbound : ∀ profile, |potential profile| ≤ C)
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (who : ι)
    (action : G.form.sig.Strategy who) (t : ℕ) :
    |G.mixedGain (G.form.empiricalBelief history (t + 2)) who action
          (IsFictitiousPlay.incumbent_integrable (G := G) hplay (t + 1) who)
          (IsFictitiousPlay.deviation_integrable (G := G) hplay (t + 1) who
            (PMF.pure action)) -
        G.mixedGain (G.form.empiricalBelief history (t + 1)) who action
          (IsFictitiousPlay.incumbent_integrable (G := G) hplay t who)
          (IsFictitiousPlay.deviation_integrable (G := G) hplay t who
            (PMF.pure action))| ≤
      (Fintype.card ι : ℝ) * ((1 / (t + 2 : ℝ)) * (4 * C)) := by
  have hboundGain := G.mixedPotentialGain_empiricalBelief_succ_abs_sub_le
    potential hbound history who action t
  simp only [mixedPotentialGainOfAbsBound] at hboundGain
  have hnew := UtilityGame.IsExactPotential.mixedPotentialGain_eq_mixedGain
    (G := G) hpotential (G.form.empiricalBelief history (t + 2)) who action
    (IsFictitiousPlay.incumbent_integrable (G := G) hplay (t + 1) who)
    (IsFictitiousPlay.deviation_integrable (G := G) hplay (t + 1) who
      (PMF.pure action))
    (payoffIntegrable_of_bounded (independentProduct
      (G.form.empiricalBelief history (t + 2))) potential hbound)
    (payoffIntegrable_of_bounded (independentProduct
      ((G.form.empiricalBelief history (t + 2)).update who
        (PMF.pure action))) potential hbound)
  have hold := UtilityGame.IsExactPotential.mixedPotentialGain_eq_mixedGain
    (G := G) hpotential (G.form.empiricalBelief history (t + 1)) who action
    (IsFictitiousPlay.incumbent_integrable (G := G) hplay t who)
    (IsFictitiousPlay.deviation_integrable (G := G) hplay t who
      (PMF.pure action))
    (payoffIntegrable_of_bounded (independentProduct
      (G.form.empiricalBelief history (t + 1))) potential hbound)
    (payoffIntegrable_of_bounded (independentProduct
      ((G.form.empiricalBelief history (t + 1)).update who
        (PMF.pure action))) potential hbound)
  rw [hnew, hold] at hboundGain
  exact hboundGain

/-- Consecutive aggregate played gains along fictitious play differ by
`O(1/t)` in a bounded exact-potential game. -/
theorem IsExactPotential.aggregatePlayedGain_succ_abs_sub_le
    {potential : Profile G.form.sig → ℝ}
    (hpotential : IsExactPotential G.form G.utility potential)
    {C : ℝ} (hbound : ∀ profile, |potential profile| ≤ C)
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) :
    |G.aggregatePlayedGain history (t + 1)
          (fun who => IsFictitiousPlay.incumbent_integrable
            (G := G) hplay (t + 1) who)
          (fun who => IsFictitiousPlay.deviation_integrable
            (G := G) hplay (t + 1) who
            (PMF.pure (history (t + 2) who))) -
        G.aggregatePlayedGain history t
          (fun who => IsFictitiousPlay.incumbent_integrable
            (G := G) hplay t who)
          (fun who => IsFictitiousPlay.deviation_integrable
            (G := G) hplay t who
            (PMF.pure (history (t + 1) who)))| ≤
      ((Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)) *
        ((1 / (t + 2 : ℝ)) * (4 * C)) := by
  let coordinateBound : ℝ :=
    (Fintype.card ι : ℝ) * ((1 / (t + 2 : ℝ)) * (4 * C))
  have hpoint : ∀ who : ι,
      |G.mixedGain (G.form.empiricalBelief history (t + 2)) who
            (history (t + 2) who)
            (IsFictitiousPlay.incumbent_integrable (G := G) hplay
              (t + 1) who)
            (IsFictitiousPlay.deviation_integrable (G := G) hplay
              (t + 1) who (PMF.pure (history (t + 2) who))) -
          G.mixedGain (G.form.empiricalBelief history (t + 1)) who
            (history (t + 1) who)
            (IsFictitiousPlay.incumbent_integrable (G := G) hplay t who)
            (IsFictitiousPlay.deviation_integrable (G := G) hplay t who
              (PMF.pure (history (t + 1) who)))| ≤ coordinateBound := by
    intro who
    have hnewBound :=
      UtilityGame.IsExactPotential.mixedGain_empiricalBelief_succ_abs_sub_le
        (G := G) hpotential hbound (history := history) hplay who
        (history (t + 2) who) t
    have holdBound :=
      UtilityGame.IsExactPotential.mixedGain_empiricalBelief_succ_abs_sub_le
        (G := G) hpotential hbound (history := history) hplay who
        (history (t + 1) who) t
    have hbestOld :=
      UtilityGame.IsFictitiousPlay.isBestResponse (G := G) hplay t who
      (PMF.pure (history (t + 2) who))
    have hbestNew :=
      UtilityGame.IsFictitiousPlay.isBestResponse (G := G) hplay (t + 1) who
        (PMF.pure (history (t + 1) who))
    rw [euPreference_apply] at hbestOld hbestNew
    rcases hbestOld with ⟨_, _, hpreferOld⟩
    rcases hbestNew with ⟨_, _, hpreferNew⟩
    have holdComparison :
        G.mixedGain (G.form.empiricalBelief history (t + 1)) who
            (history (t + 2) who)
            (IsFictitiousPlay.incumbent_integrable (G := G) hplay t who)
            (IsFictitiousPlay.deviation_integrable (G := G) hplay t who
              (PMF.pure (history (t + 2) who))) ≤
          G.mixedGain (G.form.empiricalBelief history (t + 1)) who
            (history (t + 1) who)
            (IsFictitiousPlay.incumbent_integrable (G := G) hplay t who)
            (IsFictitiousPlay.deviation_integrable (G := G) hplay t who
              (PMF.pure (history (t + 1) who))) := by
      unfold mixedGain
      linarith
    have hnewComparison :
        G.mixedGain (G.form.empiricalBelief history (t + 2)) who
            (history (t + 1) who)
            (IsFictitiousPlay.incumbent_integrable (G := G) hplay (t + 1) who)
            (IsFictitiousPlay.deviation_integrable (G := G) hplay (t + 1) who
              (PMF.pure (history (t + 1) who))) ≤
          G.mixedGain (G.form.empiricalBelief history (t + 2)) who
            (history (t + 2) who)
            (IsFictitiousPlay.incumbent_integrable (G := G) hplay (t + 1) who)
            (IsFictitiousPlay.deviation_integrable (G := G) hplay (t + 1) who
              (PMF.pure (history (t + 2) who))) := by
      unfold mixedGain
      linarith
    apply abs_le.mpr
    constructor
    · have hlower := (abs_le.mp holdBound).1
      linarith
    · have hupper := (abs_le.mp hnewBound).2
      linarith
  simp only [aggregatePlayedGain, playedGain]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ who : ι,
        (G.mixedGain (G.form.empiricalBelief history (t + 2)) who
            (history (t + 2) who)
            (IsFictitiousPlay.incumbent_integrable (G := G) hplay
              (t + 1) who)
            (IsFictitiousPlay.deviation_integrable (G := G) hplay
              (t + 1) who (PMF.pure (history (t + 2) who))) -
          G.mixedGain (G.form.empiricalBelief history (t + 1)) who
            (history (t + 1) who)
            (IsFictitiousPlay.incumbent_integrable (G := G) hplay t who)
            (IsFictitiousPlay.deviation_integrable (G := G) hplay t who
              (PMF.pure (history (t + 1) who))))| ≤
        ∑ who : ι,
          |G.mixedGain (G.form.empiricalBelief history (t + 2)) who
              (history (t + 2) who)
              (IsFictitiousPlay.incumbent_integrable (G := G) hplay
                (t + 1) who)
              (IsFictitiousPlay.deviation_integrable (G := G) hplay
                (t + 1) who (PMF.pure (history (t + 2) who))) -
            G.mixedGain (G.form.empiricalBelief history (t + 1)) who
              (history (t + 1) who)
              (IsFictitiousPlay.incumbent_integrable (G := G) hplay t who)
              (IsFictitiousPlay.deviation_integrable (G := G) hplay t who
                (PMF.pure (history (t + 1) who)))| :=
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
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) :
    (1 / (t + 2 : ℝ)) * G.aggregatePlayedGain history t
        (fun who => IsFictitiousPlay.incumbent_integrable
          (G := G) hplay t who)
        (fun who => IsFictitiousPlay.deviation_integrable
          (G := G) hplay t who
          (PMF.pure (history (t + 1) who))) -
        ((Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)) *
          ((1 / (t + 2 : ℝ)) ^ 2 * (4 * C)) ≤
      G.form.mixedPotential potential (G.form.empiricalBelief history (t + 2))
          (payoffIntegrable_of_bounded
            (independentProduct (G.form.empiricalBelief history (t + 2)))
            potential hbound) -
        G.form.mixedPotential potential (G.form.empiricalBelief history (t + 1))
          (payoffIntegrable_of_bounded
            (independentProduct (G.form.empiricalBelief history (t + 1)))
            potential hbound) := by
  have hsweep := G.mixedPotential_advanceMarginals_sub_ge
    potential hbound history t Finset.univ.toList
    (G.form.empiricalBelief history (t + 1)) Finset.univ.nodup_toList
    (by intro who _; rfl)
  rw [G.advanceMarginals_univ_eq_empiricalBelief_succ history t] at hsweep
  have hsum :
      (∑ who ∈ (Finset.univ.toList : List ι).toFinset,
        G.mixedPotentialGainOfAbsBound potential hbound (G.form.empiricalBelief history (t + 1))
          who (history (t + 1) who)) =
        G.aggregatePlayedGain history t
          (fun who => IsFictitiousPlay.incumbent_integrable
            (G := G) hplay t who)
          (fun who => IsFictitiousPlay.deviation_integrable
            (G := G) hplay t who
            (PMF.pure (history (t + 1) who))) := by
    simp only [aggregatePlayedGain]
    apply Finset.sum_congr
    · simp
    · intro who _
      simp only [mixedPotentialGainOfAbsBound, mixedPotentialGain]
      exact UtilityGame.IsExactPotential.mixedPotentialGain_eq_mixedGain
        (G := G) hpotential (G.form.empiricalBelief history (t + 1)) who
        (history (t + 1) who)
        (IsFictitiousPlay.incumbent_integrable (G := G) hplay t who)
        (IsFictitiousPlay.deviation_integrable (G := G) hplay t who
          (PMF.pure (history (t + 1) who)))
        (payoffIntegrable_of_bounded (independentProduct
          (G.form.empiricalBelief history (t + 1))) potential hbound)
        (payoffIntegrable_of_bounded (independentProduct
          ((G.form.empiricalBelief history (t + 1)).update who
            (PMF.pure (history (t + 1) who)))) potential hbound)
  have hlength :
      ((Finset.univ.toList : List ι).length : ℝ) =
        (Fintype.card ι : ℝ) := by simp
  rw [hsum, hlength] at hsweep
  exact hsweep

end UtilityGame

end GameTheory
