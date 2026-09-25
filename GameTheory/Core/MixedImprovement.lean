/-
# Mixed deviation gains

Mixed gains are guarded by the expected utilities they compare. Finite-action
aggregates derive randomized-deviation integrability by finite bind closure.
-/

import GameTheory.Core.Approximate
import GameTheory.Core.Mixed

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

namespace UtilityGame

variable (G : UtilityGame.{uι, us, uo} ι)

/-- The expected-utility gain from a pure replacement. Both compared laws are
explicitly required to have defined expected utilities. -/
def mixedGain (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who)
    (hbase : UtilityIntegrable G.utility who (G.form.mixed.play mixedProfile))
    (hpure : UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who (PMF.pure action)))) : ℝ :=
  expectedUtility G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who (PMF.pure action))) hpure -
    expectedUtility G.utility who (G.form.mixed.play mixedProfile) hbase

/-- Pure-action gains are integrable under the player's mixed action when the
status quo and every pure replacement are integrable. -/
theorem mixedGain_integrable
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (hbase : UtilityIntegrable G.utility who (G.form.mixed.play mixedProfile))
    (hpure : ∀ action, UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who (PMF.pure action)))) :
    PayoffIntegrable (mixedProfile who)
      (fun action => G.mixedGain mixedProfile who action hbase (hpure action)) := by
  let q := fun action => G.form.mixed.play
    (Profile.update mixedProfile who (PMF.pure action))
  have hlaw : G.form.mixed.play mixedProfile = (mixedProfile who).bind q := by
    calc
      G.form.mixed.play mixedProfile = G.form.mixed.play
          (Profile.update mixedProfile who (mixedProfile who)) := by
            rw [Profile.update_eq_self]
      _ = _ := GameForm.mixed_play_update G.form mixedProfile who
        (mixedProfile who)
  have hbind : UtilityIntegrable G.utility who ((mixedProfile who).bind q) := by
    exact payoffIntegrable_congr_law hlaw hbase
  have houter := payoffIntegrable_bind_conditionalExpectation
    (mixedProfile who) q (fun outcome => G.utility outcome who) hbind hpure
  let baseline := expectedUtility G.utility who
    (G.form.mixed.play mixedProfile) hbase
  have hconstant : PayoffIntegrable (mixedProfile who) (fun _ => baseline) :=
    payoffIntegrable_constant (mixedProfile who) baseline
  have houter' : PayoffIntegrable (mixedProfile who)
      (fun action => expectedUtility G.utility who (q action) (hpure action)) := by
    simpa only [expectedUtility] using houter
  have hgain := payoffIntegrable_sub houter' hconstant
  simpa [mixedGain, baseline, q] using hgain

/-- A player's own strategy averages its guarded pure-deviation gains to zero. -/
theorem expect_mixedGain_self_zero
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (hbase : UtilityIntegrable G.utility who (G.form.mixed.play mixedProfile))
    (hpure : ∀ action, UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who (PMF.pure action)))) :
    expect (mixedProfile who)
      (fun action => G.mixedGain mixedProfile who action hbase (hpure action))
      (mixedGain_integrable G mixedProfile who hbase hpure) = 0 := by
  let q := fun action => G.form.mixed.play
    (Profile.update mixedProfile who (PMF.pure action))
  have hlaw : G.form.mixed.play mixedProfile = (mixedProfile who).bind q := by
    calc
      G.form.mixed.play mixedProfile = G.form.mixed.play
          (Profile.update mixedProfile who (mixedProfile who)) := by
            rw [Profile.update_eq_self]
      _ = _ := GameForm.mixed_play_update G.form mixedProfile who
        (mixedProfile who)
  have hbind : UtilityIntegrable G.utility who ((mixedProfile who).bind q) := by
    exact payoffIntegrable_congr_law hlaw hbase
  have houter := payoffIntegrable_bind_conditionalExpectation
    (mixedProfile who) q (fun outcome => G.utility outcome who) hbind hpure
  let values := fun action => expectedUtility G.utility who (q action) (hpure action)
  let baseline := expectedUtility G.utility who
    (G.form.mixed.play mixedProfile) hbase
  have hconstant : PayoffIntegrable (mixedProfile who) (fun _ => baseline) :=
    payoffIntegrable_constant (mixedProfile who) baseline
  have houter' : PayoffIntegrable (mixedProfile who) values := by
    simpa only [values, expectedUtility] using houter
  have hgain : PayoffIntegrable (mixedProfile who)
      (fun action => values action - baseline) :=
    payoffIntegrable_sub houter' hconstant
  have hmean := expectedUtility_mixed_eq_expect G.form G.utility
    mixedProfile who hbase hpure
  have hvalue : expect (mixedProfile who) values houter' = baseline := by
    simpa only [values, expectedUtility, baseline] using hmean.symm
  calc
    expect (mixedProfile who)
        (fun action => G.mixedGain mixedProfile who action hbase (hpure action))
        (mixedGain_integrable G mixedProfile who hbase hpure) =
      expect (mixedProfile who) (fun action => values action - baseline) hgain := by
        exact expect_congr_on_support
          (fun action _ => rfl)
          (mixedGain_integrable G mixedProfile who hbase hpure) hgain
    _ = expect (mixedProfile who) values houter' - baseline := by
      calc
        _ = expect (mixedProfile who) values houter' -
            expect (mixedProfile who) (fun _ => baseline) hconstant := by
              simpa only [values, baseline] using
                expect_sub houter' hconstant
        _ = expect (mixedProfile who) values houter' - baseline := by
          rw [expect_constant]
    _ = 0 := by simp [hvalue]

/-- Mixed Nash is equivalent to nonpositive pure gains once every randomized
deviation has an expected utility. The guard is essential for the reverse
direction because divergent randomized candidates cannot be discarded. -/
theorem isNash_iff_mixedGain_nonpos
    (mixedProfile : Profile G.form.sig.mixed)
    (hbase : ∀ who, UtilityIntegrable G.utility who
      (G.form.mixed.play mixedProfile))
    (hdeviation : ∀ who (replacement : PMF (G.form.sig.Strategy who)),
      UtilityIntegrable G.utility who
        (G.form.mixed.play (Profile.update mixedProfile who replacement))) :
    IsNash G.form.mixed (euPreference G.utility) mixedProfile ↔
      ∀ who (action : G.form.sig.Strategy who),
        G.mixedGain mixedProfile who action (hbase who)
          (hdeviation who (PMF.pure action)) ≤ 0 := by
  constructor
  · intro hnash who action
    rw [isNash_iff] at hnash
    have hpref := hnash who (PMF.pure action)
    apply (euPreference_iff G.utility who
      (G.form.mixed.play mixedProfile)
      (G.form.mixed.play
        (Profile.update mixedProfile who (PMF.pure action)))
      (hbase who) (hdeviation who (PMF.pure action))).mp at hpref
    exact sub_nonpos.mpr hpref
  · intro hgain
    rw [isNash_iff]
    intro who replacement
    apply (euPreference_iff G.utility who
      (G.form.mixed.play mixedProfile)
      (G.form.mixed.play (Profile.update mixedProfile who replacement))
      (hbase who) (hdeviation who replacement)).2
    let q := fun action => G.form.mixed.play
      (Profile.update mixedProfile who (PMF.pure action))
    have hlaw : G.form.mixed.play (Profile.update mixedProfile who replacement) =
        replacement.bind q := by
      simpa only [q] using
        GameForm.mixed_play_update G.form mixedProfile who replacement
    have hbind : UtilityIntegrable G.utility who (replacement.bind q) := by
      exact payoffIntegrable_congr_law hlaw (hdeviation who replacement)
    have hpure : ∀ action, UtilityIntegrable G.utility who (q action) :=
      fun action => hdeviation who (PMF.pure action)
    have houter := payoffIntegrable_bind_conditionalExpectation replacement q
      (fun outcome => G.utility outcome who) hbind hpure
    let values := fun action => expectedUtility G.utility who (q action) (hpure action)
    let baseline := expectedUtility G.utility who
      (G.form.mixed.play mixedProfile) (hbase who)
    have hconstant : PayoffIntegrable replacement (fun _ => baseline) :=
      payoffIntegrable_constant replacement baseline
    have houter' : PayoffIntegrable replacement values := by
      simpa only [values, expectedUtility] using houter
    have hle : expect replacement values houter' ≤ baseline := by
      calc
        expect replacement values houter' ≤
            expect replacement (fun _ => baseline) hconstant :=
          expect_mono (μ := replacement) (f := values)
            (g := fun _ => baseline)
            (fun action _ => sub_nonpos.mp (hgain who action)) houter' hconstant
        _ = baseline := expect_constant replacement baseline hconstant
    have htower := expectedUtility_bind G.utility who replacement q hbind hpure
    calc
      expectedUtility G.utility who
          (G.form.mixed.play (Profile.update mixedProfile who replacement))
          (hdeviation who replacement) =
        expectedUtility G.utility who (replacement.bind q) hbind :=
          expectedUtility_congr_law G.utility who hlaw
            (hdeviation who replacement) hbind
      _ =
          expect replacement values houter' := by
        simpa only [values] using htower
      _ ≤ baseline := hle

/-- Finite support of a player's action law combines pure-replacement
certificates into an incumbent mixed-play certificate. -/
theorem mixedUtilityIntegrable_of_finite_actions
    [∀ who, Finite (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed)
    (hpure : ∀ who (action : G.form.sig.Strategy who),
      UtilityIntegrable G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action)))) :
    ∀ who, UtilityIntegrable G.utility who (G.form.mixed.play mixedProfile) := by
  intro who
  let q := fun action => G.form.mixed.play
    (Profile.update mixedProfile who (PMF.pure action))
  have hbind : UtilityIntegrable G.utility who ((mixedProfile who).bind q) :=
    payoffIntegrable_bind_of_finite (mixedProfile who) q
      (fun outcome => G.utility outcome who) (fun action => hpure who action)
  have hlaw : G.form.mixed.play mixedProfile = (mixedProfile who).bind q := by
    calc
      G.form.mixed.play mixedProfile = G.form.mixed.play
          (Profile.update mixedProfile who (mixedProfile who)) := by
            rw [Profile.update_eq_self]
      _ = _ := GameForm.mixed_play_update G.form mixedProfile who
        (mixedProfile who)
  exact payoffIntegrable_congr_law hlaw.symm hbind

/-- Finite support of a replacement law combines pure-replacement
certificates into an actual randomized-deviation certificate. -/
theorem mixedDeviationIntegrable_of_finite_actions
    [∀ who, Finite (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed)
    (hpure : ∀ who (action : G.form.sig.Strategy who),
      UtilityIntegrable G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action)))) :
    ∀ who (replacement : PMF (G.form.sig.Strategy who)),
      UtilityIntegrable G.utility who
        (G.form.mixed.play (Profile.update mixedProfile who replacement)) := by
  intro who replacement
  let q := fun action => G.form.mixed.play
    (Profile.update mixedProfile who (PMF.pure action))
  have hbind : UtilityIntegrable G.utility who (replacement.bind q) :=
    payoffIntegrable_bind_of_finite replacement q
      (fun outcome => G.utility outcome who) (fun action => hpure who action)
  have hlaw : G.form.mixed.play (Profile.update mixedProfile who replacement) =
      replacement.bind q := by
    simpa only [q] using
      GameForm.mixed_play_update G.form mixedProfile who replacement
  exact payoffIntegrable_congr_law hlaw.symm hbind

/-! ## Finite-action aggregates -/

/-- Sum of positive pure-deviation gains over every player and finite action menu. -/
def mixedImprovement [∀ who, Fintype (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed)
    (hpure : ∀ who (action : G.form.sig.Strategy who),
      UtilityIntegrable G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action)))) : ℝ :=
  ∑ who, ∑ action : G.form.sig.Strategy who,
    max (G.mixedGain mixedProfile who action
      (mixedUtilityIntegrable_of_finite_actions G mixedProfile hpure who)
      (hpure who action)) 0

theorem mixedImprovement_nonneg
    [∀ who, Fintype (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed)
    (hpure : ∀ who (action : G.form.sig.Strategy who),
      UtilityIntegrable G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action)))) :
    0 ≤ G.mixedImprovement mixedProfile hpure := by
  rw [mixedImprovement]
  exact Finset.sum_nonneg fun who _ =>
    Finset.sum_nonneg fun action _ => le_max_right _ _

theorem mixedGain_pospart_le_mixedImprovement
    [∀ who, Fintype (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed)
    (hpure : ∀ who (action : G.form.sig.Strategy who),
      UtilityIntegrable G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action))))
    (who : ι) (action : G.form.sig.Strategy who) :
    max (G.mixedGain mixedProfile who action
      (mixedUtilityIntegrable_of_finite_actions G mixedProfile hpure who)
      (hpure who action)) 0 ≤ G.mixedImprovement mixedProfile hpure := by
  have haction :
      max (G.mixedGain mixedProfile who action
        (mixedUtilityIntegrable_of_finite_actions G mixedProfile hpure who)
        (hpure who action)) 0 ≤
        ∑ candidate : G.form.sig.Strategy who,
          max (G.mixedGain mixedProfile who candidate
            (mixedUtilityIntegrable_of_finite_actions G mixedProfile hpure who)
            (hpure who candidate)) 0 :=
    Finset.single_le_sum
      (f := fun candidate =>
        max (G.mixedGain mixedProfile who candidate
          (mixedUtilityIntegrable_of_finite_actions G mixedProfile hpure who)
          (hpure who candidate)) 0)
      (fun candidate _ => le_max_right _ _)
      (Finset.mem_univ action)
  have hplayer :
      (∑ candidate : G.form.sig.Strategy who,
          max (G.mixedGain mixedProfile who candidate
            (mixedUtilityIntegrable_of_finite_actions G mixedProfile hpure who)
            (hpure who candidate)) 0) ≤
        G.mixedImprovement mixedProfile hpure := by
    have hnonneg :
        ∀ player ∈ (Finset.univ : Finset ι),
          0 ≤ ∑ candidate : G.form.sig.Strategy player,
            max (G.mixedGain mixedProfile player candidate
              (mixedUtilityIntegrable_of_finite_actions G mixedProfile hpure player)
              (hpure player candidate)) 0 := by
      intro player _
      exact Finset.sum_nonneg fun candidate _ => le_max_right _ _
    rw [mixedImprovement]
    exact Finset.single_le_sum hnonneg (Finset.mem_univ who)
  exact haction.trans hplayer

theorem mixedGain_le_mixedImprovement
    [∀ who, Fintype (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed)
    (hpure : ∀ who (action : G.form.sig.Strategy who),
      UtilityIntegrable G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action))))
    (who : ι) (action : G.form.sig.Strategy who) :
    G.mixedGain mixedProfile who action
        (mixedUtilityIntegrable_of_finite_actions G mixedProfile hpure who)
        (hpure who action) ≤ G.mixedImprovement mixedProfile hpure :=
  (le_max_left _ _).trans
    (G.mixedGain_pospart_le_mixedImprovement mixedProfile hpure who action)

theorem mixedGain_le_of_mixedImprovement_le
    [∀ who, Fintype (G.form.sig.Strategy who)]
    {mixedProfile : Profile G.form.sig.mixed} {ε : ℝ}
    (hpure : ∀ who (action : G.form.sig.Strategy who),
      UtilityIntegrable G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action))))
    (hε : G.mixedImprovement mixedProfile hpure ≤ ε) (who : ι)
    (action : G.form.sig.Strategy who) :
    G.mixedGain mixedProfile who action
        (mixedUtilityIntegrable_of_finite_actions G mixedProfile hpure who)
        (hpure who action) ≤ ε :=
  (G.mixedGain_le_mixedImprovement mixedProfile hpure who action).trans hε

private theorem max_zero_eq_zero_iff {x : ℝ} : max x 0 = 0 ↔ x ≤ 0 := by
  constructor
  · intro h
    exact (le_max_left x 0).trans_eq h
  · exact max_eq_right

theorem mixedImprovement_eq_zero_iff_gains_nonpos
    [∀ who, Fintype (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed)
    (hpure : ∀ who (action : G.form.sig.Strategy who),
      UtilityIntegrable G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action)))) :
    G.mixedImprovement mixedProfile hpure = 0 ↔
      ∀ who (action : G.form.sig.Strategy who),
        G.mixedGain mixedProfile who action
          (mixedUtilityIntegrable_of_finite_actions G mixedProfile hpure who)
          (hpure who action) ≤ 0 := by
  constructor
  · intro hzero who action
    have hpos : max (G.mixedGain mixedProfile who action
        (mixedUtilityIntegrable_of_finite_actions G mixedProfile hpure who)
        (hpure who action)) 0 ≤ 0 := by
      simpa [hzero] using
        G.mixedGain_pospart_le_mixedImprovement mixedProfile hpure who action
    exact max_zero_eq_zero_iff.mp
      (le_antisymm hpos (le_max_right _ _))
  · intro hgain
    rw [mixedImprovement]
    simp [hgain]

theorem mixedImprovement_eq_zero_iff_isNash
    [∀ who, Fintype (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed)
    (hpure : ∀ who (action : G.form.sig.Strategy who),
      UtilityIntegrable G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action)))) :
    G.mixedImprovement mixedProfile hpure = 0 ↔
      IsNash G.form.mixed (euPreference G.utility) mixedProfile := by
  have hbase : ∀ who, UtilityIntegrable G.utility who
      (G.form.mixed.play mixedProfile) :=
    mixedUtilityIntegrable_of_finite_actions G mixedProfile hpure
  have hdeviation : ∀ who (replacement : PMF (G.form.sig.Strategy who)),
      UtilityIntegrable G.utility who
        (G.form.mixed.play (Profile.update mixedProfile who replacement)) :=
    mixedDeviationIntegrable_of_finite_actions G mixedProfile hpure
  rw [G.mixedImprovement_eq_zero_iff_gains_nonpos mixedProfile hpure,
    G.isNash_iff_mixedGain_nonpos mixedProfile hbase hdeviation]

theorem isNash_iff_mixedImprovement_eq_zero
    [∀ who, Fintype (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed)
    (hpure : ∀ who (action : G.form.sig.Strategy who),
      UtilityIntegrable G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action)))) :
    IsNash G.form.mixed (euPreference G.utility) mixedProfile ↔
      G.mixedImprovement mixedProfile hpure = 0 :=
  (G.mixedImprovement_eq_zero_iff_isNash mixedProfile hpure).symm

theorem isεNash_of_mixedImprovement_le
    [∀ who, Fintype (G.form.sig.Strategy who)]
    {mixedProfile : Profile G.form.sig.mixed} {ε : ℝ}
    (hpure : ∀ who (action : G.form.sig.Strategy who),
      UtilityIntegrable G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action))))
    (hε : G.mixedImprovement mixedProfile hpure ≤ ε) :
    IsεNash G.form.mixed G.utility ε mixedProfile := by
  have hbase : ∀ who, UtilityIntegrable G.utility who
      (G.form.mixed.play mixedProfile) :=
    mixedUtilityIntegrable_of_finite_actions G mixedProfile hpure
  have hdeviation : ∀ who (replacement : PMF (G.form.sig.Strategy who)),
      UtilityIntegrable G.utility who
        (G.form.mixed.play (Profile.update mixedProfile who replacement)) :=
    mixedDeviationIntegrable_of_finite_actions G mixedProfile hpure
  rw [isεNash_iff]
  intro who replacement
  refine ⟨hbase who, hdeviation who replacement, ?_⟩
  let q := fun action => G.form.mixed.play
    (Profile.update mixedProfile who (PMF.pure action))
  have hlaw : G.form.mixed.play (Profile.update mixedProfile who replacement) =
      replacement.bind q := by
    simpa only [q] using
      GameForm.mixed_play_update G.form mixedProfile who replacement
  have hbind : UtilityIntegrable G.utility who (replacement.bind q) :=
    payoffIntegrable_congr_law hlaw (hdeviation who replacement)
  have hpure' : ∀ action, UtilityIntegrable G.utility who (q action) :=
    fun action => hpure who action
  have houter := payoffIntegrable_bind_conditionalExpectation replacement q
    (fun outcome => G.utility outcome who) hbind hpure'
  let values := fun action => expectedUtility G.utility who (q action) (hpure' action)
  let baseline := expectedUtility G.utility who (G.form.mixed.play mixedProfile)
    (hbase who)
  have houter' : PayoffIntegrable replacement values := by
    simpa only [values, expectedUtility] using houter
  have hconstant : PayoffIntegrable replacement (fun _ => baseline + ε) :=
    payoffIntegrable_constant replacement (baseline + ε)
  have hvalues : expect replacement values houter' ≤ baseline + ε := by
    calc
      expect replacement values houter' ≤
          expect replacement (fun _ => baseline + ε) hconstant :=
        expect_mono (μ := replacement) (f := values)
          (g := fun _ => baseline + ε)
          (fun action _ => by
            have hgain := G.mixedGain_le_of_mixedImprovement_le
              hpure hε who action
            have h := hgain
            unfold mixedGain at h
            linarith)
          houter' hconstant
      _ = baseline + ε := expect_constant replacement _ hconstant
  have htower := expectedUtility_bind G.utility who replacement q hbind hpure'
  calc
    expectedUtility G.utility who
        (G.form.mixed.play (Profile.update mixedProfile who replacement))
        (hdeviation who replacement) =
      expectedUtility G.utility who (replacement.bind q) hbind :=
        expectedUtility_congr_law G.utility who hlaw
          (hdeviation who replacement) hbind
    _ = expect replacement values houter' := by
      simpa only [values] using htower
    _ ≤ baseline + ε := hvalues

end UtilityGame

end GameTheory
