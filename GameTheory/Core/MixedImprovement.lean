/-
# Mixed deviation gains

Pure-deviation gains and their aggregate positive part give a finite,
topology-free certificate for approximate mixed equilibrium.  Convergence of
that certificate belongs in `Analysis`; this file owns only the algebraic
endpoint consumed by learning dynamics and finite algorithms.
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

/-- The expected-utility gain from replacing one mixed coordinate by a pure
action. -/
def mixedGain (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who) : ℝ :=
  expectedUtility G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who (FinDist.pure action))) -
    expectedUtility G.utility who (G.form.mixed.play mixedProfile)

/-- A player's own mixed strategy averages its pure-deviation gains to zero. -/
theorem expect_mixedGain_self_zero (mixedProfile : Profile G.form.sig.mixed)
    (who : ι) :
    (mixedProfile who).expect (G.mixedGain mixedProfile who) = 0 := by
  unfold mixedGain
  rw [FinDist.expect_sub, FinDist.expect_const,
    ← expectedUtility_mixed_eq_expect G.form G.utility mixedProfile who]
  ring

/-- Mixed Nash is equivalent to every pure-deviation gain being nonpositive. -/
theorem isNash_iff_mixedGain_nonpos (mixedProfile : Profile G.form.sig.mixed) :
    IsNash G.form.mixed (euPreference G.utility) mixedProfile ↔
      ∀ who (action : G.form.sig.Strategy who),
        G.mixedGain mixedProfile who action ≤ 0 := by
  constructor
  · intro hnash who action
    rw [isNash_iff] at hnash
    have hdeviation := hnash who (FinDist.pure action)
    rw [euPreference_apply] at hdeviation
    exact sub_nonpos.mpr hdeviation
  · intro hgain
    rw [isNash_iff]
    intro who replacement
    rw [euPreference_apply, GameForm.mixed_play_update,
      expectedUtility_bind]
    refine FinDist.expect_le_of_forall replacement _ _ fun action _ => ?_
    exact sub_nonpos.mp (hgain who action)

/-- The aggregate positive pure-deviation gain at a mixed profile. -/
def mixedImprovement [∀ who, Fintype (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed) : ℝ :=
  ∑ who, ∑ action : G.form.sig.Strategy who,
    max (G.mixedGain mixedProfile who action) 0

theorem mixedImprovement_nonneg [∀ who, Fintype (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed) :
    0 ≤ G.mixedImprovement mixedProfile := by
  rw [mixedImprovement]
  exact Finset.sum_nonneg fun who _ =>
    Finset.sum_nonneg fun action _ => le_max_right _ _

theorem mixedGain_pospart_le_mixedImprovement
    [∀ who, Fintype (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who) :
    max (G.mixedGain mixedProfile who action) 0 ≤
      G.mixedImprovement mixedProfile := by
  have haction :
      max (G.mixedGain mixedProfile who action) 0 ≤
        ∑ candidate : G.form.sig.Strategy who,
          max (G.mixedGain mixedProfile who candidate) 0 :=
    Finset.single_le_sum
      (fun candidate _ => le_max_right (G.mixedGain mixedProfile who candidate) 0)
      (Finset.mem_univ action)
  have hplayer :
      (∑ candidate : G.form.sig.Strategy who,
          max (G.mixedGain mixedProfile who candidate) 0) ≤
        G.mixedImprovement mixedProfile := by
    have hplayer_nonneg :
        ∀ player ∈ (Finset.univ : Finset ι),
          0 ≤ ∑ candidate : G.form.sig.Strategy player,
            max (G.mixedGain mixedProfile player candidate) 0 := by
      intro player _
      exact Finset.sum_nonneg fun candidate _ =>
        le_max_right (G.mixedGain mixedProfile player candidate) 0
    rw [mixedImprovement]
    exact Finset.single_le_sum hplayer_nonneg (Finset.mem_univ who)
  exact haction.trans hplayer

theorem mixedGain_le_mixedImprovement
    [∀ who, Fintype (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who) :
    G.mixedGain mixedProfile who action ≤ G.mixedImprovement mixedProfile :=
  (le_max_left _ _).trans
    (G.mixedGain_pospart_le_mixedImprovement mixedProfile who action)

theorem mixedGain_le_of_mixedImprovement_le
    [∀ who, Fintype (G.form.sig.Strategy who)]
    {mixedProfile : Profile G.form.sig.mixed} {ε : ℝ}
    (hε : G.mixedImprovement mixedProfile ≤ ε) (who : ι)
    (action : G.form.sig.Strategy who) :
    G.mixedGain mixedProfile who action ≤ ε :=
  (G.mixedGain_le_mixedImprovement mixedProfile who action).trans hε

private theorem max_zero_eq_zero_iff {x : ℝ} : max x 0 = 0 ↔ x ≤ 0 := by
  constructor
  · intro h
    exact (le_max_left x 0).trans_eq h
  · exact max_eq_right

theorem mixedImprovement_eq_zero_iff_gains_nonpos
    [∀ who, Fintype (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed) :
    G.mixedImprovement mixedProfile = 0 ↔
      ∀ who (action : G.form.sig.Strategy who),
        G.mixedGain mixedProfile who action ≤ 0 := by
  constructor
  · intro hzero who action
    have hpos : max (G.mixedGain mixedProfile who action) 0 ≤ 0 := by
      simpa [hzero] using
        G.mixedGain_pospart_le_mixedImprovement mixedProfile who action
    exact max_zero_eq_zero_iff.mp
      (le_antisymm hpos (le_max_right _ _))
  · intro hgain
    rw [mixedImprovement]
    simp [hgain]

theorem mixedImprovement_eq_zero_iff_isNash
    [∀ who, Fintype (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed) :
    G.mixedImprovement mixedProfile = 0 ↔
      IsNash G.form.mixed (euPreference G.utility) mixedProfile := by
  rw [G.mixedImprovement_eq_zero_iff_gains_nonpos,
    G.isNash_iff_mixedGain_nonpos]

theorem isNash_iff_mixedImprovement_eq_zero
    [∀ who, Fintype (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed) :
    IsNash G.form.mixed (euPreference G.utility) mixedProfile ↔
      G.mixedImprovement mixedProfile = 0 :=
  (G.mixedImprovement_eq_zero_iff_isNash mixedProfile).symm

/-- A small aggregate positive gain certifies approximate mixed Nash. -/
theorem isεNash_of_mixedImprovement_le
    [∀ who, Fintype (G.form.sig.Strategy who)]
    {mixedProfile : Profile G.form.sig.mixed} {ε : ℝ}
    (hε : G.mixedImprovement mixedProfile ≤ ε) :
    IsεNash G.form.mixed G.utility ε mixedProfile := by
  rw [isεNash_iff]
  intro who replacement
  rw [GameForm.mixed_play_update, expectedUtility_bind]
  refine FinDist.expect_le_of_forall replacement _ _ fun action _ => ?_
  have hgain := G.mixedGain_le_of_mixedImprovement_le hε who action
  unfold mixedGain at hgain
  linarith

end UtilityGame

end GameTheory
