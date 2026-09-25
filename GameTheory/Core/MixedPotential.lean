/-
# Mixed extensions of exact potential games

The multilinear extension of a pure-profile potential is its guarded
expectation under the canonical independent PMF profile law. Exact potential
differences survive pure and randomized unilateral changes when the compared
outcome laws are integrable.
-/

import GameTheory.Core.Mixed
import GameTheory.Core.Potential

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

namespace GameForm

omit [DecidableEq ι] in
/-- Independent pure strategies produce the corresponding pure profile law. -/
theorem independentProduct_purify (G : GameForm ι)
    (profile : Profile G.sig) :
    independentProduct (G.purify profile) = PMF.pure profile := by
  show independentProduct (fun i => PMF.pure (profile i)) = PMF.pure profile
  exact independentProduct_pure profile

/-- The multilinear extension of a pure-profile potential, when its profile
law is integrable. -/
def mixedPotential (G : GameForm ι) (potential : Profile G.sig → ℝ)
    (mixedProfile : Profile G.sig.mixed)
    (hpotential : PayoffIntegrable (independentProduct mixedProfile) potential) : ℝ :=
  expect (independentProduct mixedProfile) potential hpotential

omit [DecidableEq ι] in
/-- The mixed potential agrees with the original potential on the canonical
pure embedding. -/
@[simp]
theorem mixedPotential_purify (G : GameForm ι)
    (potential : Profile G.sig → ℝ) (profile : Profile G.sig) :
    G.mixedPotential potential (G.purify profile)
      (by
        exact payoffIntegrable_congr_law
          (independentProduct_purify G profile).symm
          (payoffIntegrable_pure profile potential)) = potential profile := by
  have hlaw := independentProduct_purify G profile
  calc
    _ = expect (PMF.pure profile) potential
        (payoffIntegrable_pure profile potential) :=
      expect_congr_law hlaw potential _ _
    _ = potential profile := expect_pure profile potential _

/-- The mixed potential is affine in every player's own mixed strategy. -/
private theorem mixedPotential_update_exists (G : GameForm ι)
    (potential : Profile G.sig → ℝ)
    (mixedProfile : Profile G.sig.mixed) (who : ι)
    (replacement : PMF (G.sig.Strategy who))
    (hpotential : PayoffIntegrable
      (independentProduct (Profile.update mixedProfile who replacement)) potential)
    (g : G.sig.Strategy who → ℝ)
    (hconditional : ∀ action, ∀ _ha : action ∈ replacement.support,
      ∃ h : PayoffIntegrable
        (independentProduct
          (Profile.update mixedProfile who (PMF.pure action))) potential,
        g action = expect
          (independentProduct
            (Profile.update mixedProfile who (PMF.pure action))) potential h) :
    ∃ houter : PayoffIntegrable replacement g,
      G.mixedPotential potential (Profile.update mixedProfile who replacement)
          hpotential = expect replacement g houter := by
  let q := fun action => independentProduct
    (Profile.update mixedProfile who (PMF.pure action))
  have hlaw : independentProduct (Profile.update mixedProfile who replacement) =
      replacement.bind q := by
    simpa only [q] using
      GameForm.pi_update_mixed G.sig mixedProfile who replacement
  have hbind : PayoffIntegrable (replacement.bind q) potential := by
    simpa only [hlaw] using hpotential
  have hcond' : ∀ action, ∀ ha : action ∈ replacement.support,
      g action = expect (q action) potential
        (payoffIntegrable_bind_conditional_on_support
          replacement q potential hbind action ha) := by
    intro action ha
    obtain ⟨h, heq⟩ := hconditional action ha
    rw [heq]
  refine ⟨payoffIntegrable_bind_conditionalValue_on_support
    replacement q potential hbind g hcond', ?_⟩
  calc
    _ = expect (replacement.bind q) potential hbind :=
      expect_congr_law hlaw potential hpotential hbind
    _ = expect replacement g
        (payoffIntegrable_bind_conditionalValue_on_support
          replacement q potential hbind g hcond') :=
      expect_bind_tower_on_support replacement q potential hbind g hcond'

/-- The conditional potential values are integrable under the replacement
law whenever the actual updated profile law is integrable. -/
theorem mixedPotential_update_integrable (G : GameForm ι)
    (potential : Profile G.sig → ℝ)
    (mixedProfile : Profile G.sig.mixed) (who : ι)
    (replacement : PMF (G.sig.Strategy who))
    (hpotential : PayoffIntegrable
      (independentProduct (Profile.update mixedProfile who replacement)) potential)
    (g : G.sig.Strategy who → ℝ)
    (hconditional : ∀ action, ∀ _ha : action ∈ replacement.support,
      ∃ h : PayoffIntegrable
        (independentProduct
          (Profile.update mixedProfile who (PMF.pure action))) potential,
        g action = expect
          (independentProduct
            (Profile.update mixedProfile who (PMF.pure action))) potential h) :
    PayoffIntegrable replacement g :=
  (G.mixedPotential_update_exists potential mixedProfile who replacement
    hpotential g hconditional).choose

/-- A player's replacement expectation directly equals the mixed potential
of the updated profile, using any equivalent integrability certificate. -/
theorem mixedPotential_update (G : GameForm ι)
    (potential : Profile G.sig → ℝ)
    (mixedProfile : Profile G.sig.mixed) (who : ι)
    (replacement : PMF (G.sig.Strategy who))
    (hpotential : PayoffIntegrable
      (independentProduct (Profile.update mixedProfile who replacement)) potential)
    (g : G.sig.Strategy who → ℝ)
    (hconditional : ∀ action, ∀ _ha : action ∈ replacement.support,
      ∃ h : PayoffIntegrable
        (independentProduct
          (Profile.update mixedProfile who (PMF.pure action))) potential,
        g action = expect
          (independentProduct
            (Profile.update mixedProfile who (PMF.pure action))) potential h)
    (houter : PayoffIntegrable replacement g) :
    G.mixedPotential potential (Profile.update mixedProfile who replacement)
        hpotential = expect replacement g houter := by
  obtain ⟨h, heq⟩ := G.mixedPotential_update_exists potential mixedProfile who
    replacement hpotential g hconditional
  exact heq

end GameForm

namespace UtilityGame

variable {G : UtilityGame.{uι, us, uo} ι}
variable {potential : Profile G.form.sig → ℝ}

private def selectProfile (anchor profile : Profile G.form.sig)
    (players : Finset ι) : Profile G.form.sig :=
  fun i => if i ∈ players then profile i else anchor i

private def selectMixed (anchor : Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (players : Finset ι) :
    Profile G.form.sig.mixed :=
  fun i => if i ∈ players then mixedProfile i else PMF.pure (anchor i)

omit [Fintype ι] in
private theorem selectProfile_insert (anchor profile : Profile G.form.sig)
    (players : Finset ι) {who : ι} :
    selectProfile anchor profile (insert who players) =
      Profile.update (selectProfile anchor profile players) who (profile who) := by
  classical
  funext i
  by_cases hi : i = who
  · subst i
    simp [selectProfile, Profile.update_same]
  · simp [selectProfile, Profile.update_of_ne, hi]

private theorem selectProfile_law (anchor : Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (players : Finset ι) :
    (independentProduct mixedProfile).map
        (fun profile => selectProfile anchor profile players) =
      independentProduct (selectMixed anchor mixedProfile players) := by
  classical
  let f : ∀ i, G.form.sig.Strategy i → G.form.sig.Strategy i :=
    fun i action => if i ∈ players then action else anchor i
  calc
    _ = (independentProduct mixedProfile).map
          (fun profile i => f i (profile i)) := rfl
    _ = independentProduct (fun i =>
          (mixedProfile i).map (f i)) :=
      independentProduct_map mixedProfile f
    _ = _ := by
      congr 1
      funext i
      by_cases hi : i ∈ players
      · simp only [f, selectMixed, hi, ite_true]
        exact PMF.map_id (mixedProfile i)
      · simp only [f, selectMixed, hi, ite_false]
        exact PMF.map_const (p := mixedProfile i) (b := anchor i)

private theorem pureExpectedUtility_integrable
    (hpotential : IsExactPotential G.form G.utility potential)
    (hactual : ∀ (mixedProfile : Profile G.form.sig.mixed) (who : ι),
      UtilityIntegrable G.utility who (G.form.mixed.play mixedProfile))
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) :
    PayoffIntegrable (independentProduct mixedProfile)
      (fun profile => expectedUtility G.utility who (G.form.play profile)
        (hpotential.integrable profile who)) := by
  have hbind : UtilityIntegrable G.utility who
      ((independentProduct mixedProfile).bind G.form.play) := by
    exact hactual mixedProfile who
  exact payoffIntegrable_bind_conditionalExpectation
    (independentProduct mixedProfile) G.form.play
    (fun outcome => G.utility outcome who) hbind
    (fun profile => hpotential.integrable profile who)

set_option maxHeartbeats 1500000 in
private theorem selectedPureUtility_integrable
    (hpotential : IsExactPotential G.form G.utility potential)
    (hactual : ∀ (mixedProfile : Profile G.form.sig.mixed) (who : ι),
      UtilityIntegrable G.utility who (G.form.mixed.play mixedProfile))
    (anchor : Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed)
    (players : Finset ι) (who : ι) :
    PayoffIntegrable (independentProduct mixedProfile)
      (fun profile => expectedUtility G.utility who
        (G.form.play (selectProfile anchor profile players))
        (hpotential.integrable (selectProfile anchor profile players) who)) := by
  have hselected := pureExpectedUtility_integrable hpotential hactual
    (selectMixed anchor mixedProfile players) who
  have hmapped : PayoffIntegrable
      ((independentProduct mixedProfile).map
        (fun profile => selectProfile anchor profile players))
      (fun profile => expectedUtility G.utility who (G.form.play profile)
        (hpotential.integrable profile who)) := by
    rw [selectProfile_law]
    exact hselected
  exact (payoffIntegrable_map_iff _ _ _).mp hmapped

set_option maxHeartbeats 1500000 in
/-- Integrability of every actual mixed outcome/player law implies
integrability of the potential under each independent profile law. The proof
replaces the coordinates of a pure anchor one at a time. -/
theorem IsExactPotential.mixedPotentialIntegrable
    (hpotential : IsExactPotential G.form G.utility potential)
    (hactual : ∀ (mixedProfile : Profile G.form.sig.mixed) (who : ι),
      UtilityIntegrable G.utility who (G.form.mixed.play mixedProfile))
    (mixedProfile : Profile G.form.sig.mixed) :
    PayoffIntegrable (independentProduct mixedProfile) potential := by
  classical
  let anchor : Profile G.form.sig := fun i =>
    Classical.choose (mixedProfile i).support_nonempty
  let law := independentProduct mixedProfile
  have hind : ∀ players : Finset ι,
      PayoffIntegrable law (fun profile =>
        potential (selectProfile anchor profile players)) := by
    intro players
    induction players using Finset.induction_on with
    | empty =>
        have hconst := payoffIntegrable_of_bounded law
          (fun _ => potential anchor) (C := |potential anchor|)
          (fun _ => by simp)
        have heq : (fun profile => potential (selectProfile anchor profile ∅)) =
            (fun _ => potential anchor) := by
          funext profile
          congr 1
        rw [heq]
        exact hconst
    | @insert who players hwho ih =>
        let oldProfile := fun profile : Profile G.form.sig =>
          selectProfile anchor profile players
        let newProfile := fun profile : Profile G.form.sig =>
          selectProfile anchor profile (insert who players)
        let ownValue := fun profile : Profile G.form.sig =>
          expectedUtility G.utility who (G.form.play profile)
            (hpotential.integrable profile who)
        have hnew : PayoffIntegrable law (fun profile => ownValue (newProfile profile)) :=
          selectedPureUtility_integrable hpotential hactual anchor mixedProfile
            (insert who players) who
        have hold : PayoffIntegrable law (fun profile => ownValue (oldProfile profile)) :=
          selectedPureUtility_integrable hpotential hactual anchor mixedProfile
            players who
        have hsum := payoffIntegrable_add ih hnew
        have hdiff := payoffIntegrable_add hsum (payoffIntegrable_neg hold)
        apply payoffIntegrable_congr_on_support (μ := law)
          (f := fun profile =>
            (potential (oldProfile profile) + ownValue (newProfile profile)) +
              -ownValue (oldProfile profile))
          (g := fun profile => potential (newProfile profile)) ?_ hdiff
        intro profile _
        have hprofile : Profile.update (oldProfile profile) who (profile who) =
            newProfile profile :=
          (selectProfile_insert anchor profile players).symm
        have hdiffPoint := hpotential.difference who (oldProfile profile)
          (profile who)
        rw [hprofile] at hdiffPoint
        linarith
  have hfull := hind Finset.univ
  have heq : (fun profile => potential (selectProfile anchor profile Finset.univ)) =
      potential := by
    funext profile
    congr 1
    funext i
    simp [selectProfile]
  rw [heq] at hfull
  exact hfull

/-- A pure unilateral change preserves the exact expected-utility/potential
difference under arbitrary opponent randomization, provided the compared
actual laws are integrable. -/
theorem IsExactPotential.mixed_pure_diff
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
    expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action))) hnewUtility -
      expectedUtility G.utility who (G.form.mixed.play mixedProfile)
        hbaseUtility =
    G.form.mixedPotential potential
        (Profile.update mixedProfile who (PMF.pure action)) hnewPotential -
      G.form.mixedPotential potential mixedProfile hbasePotential := by
  let μ := independentProduct mixedProfile
  let respond : Profile G.form.sig → Profile G.form.sig :=
    fun profile => Profile.update profile who action
  let updated := Profile.update mixedProfile who (PMF.pure action)
  let u : Profile G.form.sig → ℝ := fun profile =>
    expectedUtility G.utility who (G.form.play profile)
      (hpotential.integrable profile who)
  have hmap : μ.map respond = independentProduct updated := by
    have h := GameForm.pi_map_recommendation G.form.sig mixedProfile who
      (fun _ => action)
    have hconst : (mixedProfile who).map (fun _ => action) =
        PMF.pure action := by
      rw [show (fun _ : G.form.sig.Strategy who => action) =
        Function.const _ action from rfl, PMF.map_const]
    rw [hconst] at h
    exact h
  have hbaseBind : UtilityIntegrable G.utility who (G.form.outcomeLaw μ) :=
    hbaseUtility
  have hnewBind : UtilityIntegrable G.utility who
      (G.form.outcomeLaw (μ.map respond)) := by
    rw [GameForm.outcomeLaw, hmap]
    exact hnewUtility
  have hcond (profile : Profile G.form.sig) :
      UtilityIntegrable G.utility who (G.form.play profile) :=
    hpotential.integrable profile who
  have hbaseU : PayoffIntegrable μ u := by
    exact payoffIntegrable_bind_conditionalExpectation μ G.form.play
      (fun outcome => G.utility outcome who) hbaseBind hcond
  have hnewUMap : PayoffIntegrable (μ.map respond) u := by
    exact payoffIntegrable_bind_conditionalExpectation
      (μ.map respond) G.form.play
      (fun outcome => G.utility outcome who) hnewBind hcond
  have hnewU : PayoffIntegrable μ (fun profile => u (respond profile)) :=
    (payoffIntegrable_map_iff respond μ u).mp hnewUMap
  have hnewPMap : PayoffIntegrable (μ.map respond) potential := by
    rw [hmap]
    exact hnewPotential
  have hnewP : PayoffIntegrable μ
      (fun profile => potential (respond profile)) :=
    (payoffIntegrable_map_iff respond μ potential).mp hnewPMap
  have hbaseValue :
      expectedUtility G.utility who (G.form.mixed.play mixedProfile)
          hbaseUtility = expect μ u hbaseU := by
    exact expectedUtility_outcomeLaw G.form G.utility who μ hbaseBind hcond
  have hnewValue :
      expectedUtility G.utility who (G.form.mixed.play updated)
          hnewUtility =
        expect μ (fun profile => u (respond profile)) hnewU := by
    have hread := expectedUtility_outcomeLaw_map G.form
      G.utility who μ respond hnewBind (fun profile => hcond (respond profile))
    have hlaw : G.form.mixed.play updated =
        G.form.outcomeLaw (μ.map respond) := by
      simp only [GameForm.outcomeLaw, hmap]
    calc
      _ = expectedUtility G.utility who
            (G.form.outcomeLaw (μ.map respond)) hnewBind :=
        expectedUtility_congr_law G.utility who hlaw hnewUtility hnewBind
      _ = expect μ (fun profile => u (respond profile)) hnewU := hread
  have hnewPotentialValue :
      G.form.mixedPotential potential updated hnewPotential =
        expect μ (fun profile => potential (respond profile)) hnewP := by
    unfold GameForm.mixedPotential
    calc
      _ = expect (μ.map respond) potential hnewPMap :=
        expect_congr_law hmap.symm potential _ _
      _ = _ := expect_map respond μ potential hnewP hnewPMap
  have hpoint (profile : Profile G.form.sig) :
      u (respond profile) - u profile =
        potential (respond profile) - potential profile :=
    hpotential.difference who profile action
  calc
    expectedUtility G.utility who (G.form.mixed.play updated) hnewUtility -
        expectedUtility G.utility who (G.form.mixed.play mixedProfile)
          hbaseUtility =
        expect μ (fun profile => u (respond profile)) hnewU -
          expect μ u hbaseU := by rw [hnewValue, hbaseValue]
    _ = expect μ (fun profile => u (respond profile) - u profile)
          (payoffIntegrable_sub hnewU hbaseU) :=
      (expect_sub hnewU hbaseU).symm
    _ = expect μ (fun profile =>
          potential (respond profile) - potential profile)
          (payoffIntegrable_sub hnewP hbasePotential) :=
      expect_congr_on_support (fun profile _ => hpoint profile) _ _
    _ = expect μ (fun profile => potential (respond profile)) hnewP -
          expect μ potential hbasePotential :=
      expect_sub hnewP hbasePotential
    _ = G.form.mixedPotential potential updated hnewPotential -
          G.form.mixedPotential potential mixedProfile hbasePotential := by
      rw [hnewPotentialValue]
      rfl

/-- Arbitrary unilateral randomization preserves the exact difference when
the two actual outcome laws and two profile-potential laws are integrable. -/
theorem IsExactPotential.mixed_update_diff
    (hpotential : IsExactPotential G.form G.utility potential)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (replacement : PMF (G.form.sig.Strategy who))
    (hbaseUtility : UtilityIntegrable G.utility who
      (G.form.mixed.play mixedProfile))
    (hnewUtility : UtilityIntegrable G.utility who
      (G.form.mixed.play (Profile.update mixedProfile who replacement)))
    (hbasePotential : PayoffIntegrable
      (independentProduct mixedProfile) potential)
    (hnewPotential : PayoffIntegrable
      (independentProduct (Profile.update mixedProfile who replacement)) potential) :
    expectedUtility G.utility who
        (G.form.mixed.play (Profile.update mixedProfile who replacement))
        hnewUtility -
      expectedUtility G.utility who (G.form.mixed.play mixedProfile)
        hbaseUtility =
    G.form.mixedPotential potential
        (Profile.update mixedProfile who replacement) hnewPotential -
      G.form.mixedPotential potential mixedProfile hbasePotential := by
  classical
  let qU : G.form.sig.Strategy who → PMF G.form.sig.Outcome := fun action =>
    G.form.mixed.play (Profile.update mixedProfile who (PMF.pure action))
  let qP : G.form.sig.Strategy who → PMF (Profile G.form.sig) := fun action =>
    independentProduct (Profile.update mixedProfile who (PMF.pure action))
  have hUlaw : G.form.mixed.play
      (Profile.update mixedProfile who replacement) = replacement.bind qU :=
    GameForm.mixed_play_update G.form mixedProfile who replacement
  have hPlaw : independentProduct
      (Profile.update mixedProfile who replacement) = replacement.bind qP :=
    GameForm.pi_update_mixed G.form.sig mixedProfile who replacement
  have hUbind : UtilityIntegrable G.utility who (replacement.bind qU) := by
    rw [← hUlaw]
    exact hnewUtility
  have hPbind : PayoffIntegrable (replacement.bind qP) potential := by
    rw [← hPlaw]
    exact hnewPotential
  let hUc (action : G.form.sig.Strategy who)
      (ha : action ∈ replacement.support) :=
    payoffIntegrable_bind_conditional_on_support replacement qU
      (fun outcome => G.utility outcome who) hUbind action ha
  let hPc (action : G.form.sig.Strategy who)
      (ha : action ∈ replacement.support) :=
    payoffIntegrable_bind_conditional_on_support replacement qP
      potential hPbind action ha
  let gU : G.form.sig.Strategy who → ℝ := fun action =>
    if ha : action ∈ replacement.support then
      expectedUtility G.utility who (qU action) (hUc action ha) else 0
  let gP : G.form.sig.Strategy who → ℝ := fun action =>
    if ha : action ∈ replacement.support then
      expect (qP action) potential (hPc action ha) else 0
  have hcondU : ∀ action, ∀ ha : action ∈ replacement.support,
      gU action = expect (qU action)
        (fun outcome => G.utility outcome who) (hUc action ha) := by
    intro action ha
    have hne : replacement action ≠ 0 := (replacement.mem_support_iff action).mp ha
    simp [gU, hne, expectedUtility]
  have hcondP : ∀ action, ∀ ha : action ∈ replacement.support,
      ∃ h : PayoffIntegrable (qP action) potential,
        gP action = expect (qP action) potential h := by
    intro action ha
    have hne : replacement action ≠ 0 := (replacement.mem_support_iff action).mp ha
    exact ⟨hPc action ha, by simp [gP, hne]⟩
  have houterU : PayoffIntegrable replacement gU :=
    payoffIntegrable_bind_conditionalValue_on_support replacement qU
      (fun outcome => G.utility outcome who) hUbind gU hcondU
  have houterP : PayoffIntegrable replacement gP :=
    G.form.mixedPotential_update_integrable potential mixedProfile who
      replacement hnewPotential gP hcondP
  have hEUupdate :
      expectedUtility G.utility who
          (G.form.mixed.play (Profile.update mixedProfile who replacement))
          hnewUtility = expect replacement gU houterU := by
    calc
      _ = expectedUtility G.utility who (replacement.bind qU) hUbind :=
        expectedUtility_congr_law G.utility who hUlaw hnewUtility hUbind
      _ = expect replacement gU houterU := by
        unfold expectedUtility
        exact expect_bind_tower_on_support replacement qU
          (fun outcome => G.utility outcome who) hUbind gU hcondU
  have hPupdate :
      G.form.mixedPotential potential
          (Profile.update mixedProfile who replacement) hnewPotential =
        expect replacement gP houterP :=
    G.form.mixedPotential_update potential mixedProfile who replacement
      hnewPotential gP hcondP houterP
  let baseU := expectedUtility G.utility who
    (G.form.mixed.play mixedProfile) hbaseUtility
  let baseP := G.form.mixedPotential potential mixedProfile hbasePotential
  have hpoint (action : G.form.sig.Strategy who)
      (ha : action ∈ replacement.support) :
      gU action - baseU = gP action - baseP := by
    have hpure := IsExactPotential.mixed_pure_diff hpotential mixedProfile who action
      hbaseUtility (hUc action ha) hbasePotential (hPc action ha)
    have hne : replacement action ≠ 0 := (replacement.mem_support_iff action).mp ha
    have hgu := hcondU action ha
    have hgp : gP action = expect (qP action) potential (hPc action ha) := by
      simp [gP, hne]
    simpa only [hgu, hgp, qU, qP, baseU, baseP, GameForm.mixedPotential,
      expectedUtility]
      using hpure
  have hconstU := payoffIntegrable_constant replacement baseU
  have hconstP := payoffIntegrable_constant replacement baseP
  calc
    expectedUtility G.utility who
        (G.form.mixed.play (Profile.update mixedProfile who replacement))
        hnewUtility - baseU =
        expect replacement gU houterU - baseU := by rw [hEUupdate]
    _ = expect replacement (fun action => gU action - baseU)
          (payoffIntegrable_sub houterU hconstU) := by
      rw [expect_sub houterU hconstU,
        expect_constant replacement baseU hconstU]
    _ = expect replacement (fun action => gP action - baseP)
          (payoffIntegrable_sub houterP hconstP) :=
      expect_congr_on_support hpoint _ _
    _ = expect replacement gP houterP - baseP := by
      rw [expect_sub houterP hconstP,
        expect_constant replacement baseP hconstP]
    _ = G.form.mixedPotential potential
          (Profile.update mixedProfile who replacement) hnewPotential -
          baseP := by rw [hPupdate]

/-- Actual mixed utility integrability suffices to extend an exact potential:
potential integrability follows from unilateral coupling to a pure anchor. -/
theorem IsExactPotential.mixed
    (hpotential : IsExactPotential G.form G.utility potential)
    (hactual : ∀ (mixedProfile : Profile G.form.sig.mixed) (who : ι),
      UtilityIntegrable G.utility who (G.form.mixed.play mixedProfile)) :
    IsExactPotential G.form.mixed G.utility
      (fun mixedProfile => G.form.mixedPotential potential mixedProfile
        (IsExactPotential.mixedPotentialIntegrable hpotential hactual mixedProfile)) := by
  refine ⟨hactual, ?_⟩
  intro who mixedProfile replacement
  exact IsExactPotential.mixed_update_diff hpotential mixedProfile who replacement
    (hactual mixedProfile who)
    (hactual (Profile.update mixedProfile who replacement) who)
    (IsExactPotential.mixedPotentialIntegrable hpotential hactual mixedProfile)
    (IsExactPotential.mixedPotentialIntegrable hpotential hactual
      (Profile.update mixedProfile who replacement))

/-- Finite player and action carriers derive mixed-utility integrability from
the exact potential's pure-play integration family. -/
theorem mixedUtilityIntegrable_of_finite
    [∀ i, Finite (G.form.sig.Strategy i)]
    (hpotential : IsExactPotential G.form G.utility potential)
    (profile : Profile G.form.sig.mixed) (who : ι) :
    UtilityIntegrable G.utility who (G.form.mixed.play profile) := by
  simpa only [GameForm.mixed_play] using
    (payoffIntegrable_bind_of_finite
      (independentProduct profile) G.form.play
      (fun outcome => G.utility outcome who)
      (fun pureProfile => hpotential.integrable pureProfile who))

/-- Finite pure strategy carriers make every actual mixed utility law
integrable from pure-profile integrability, even with an infinite outcome type. -/
theorem IsExactPotential.mixed_of_finite
    [∀ i, Finite (G.form.sig.Strategy i)]
    (hpotential : IsExactPotential G.form G.utility potential) :
    IsExactPotential G.form.mixed G.utility
      (fun mixedProfile => G.form.mixedPotential potential mixedProfile
        (IsExactPotential.mixedPotentialIntegrable hpotential
          (mixedUtilityIntegrable_of_finite hpotential) mixedProfile)) :=
  IsExactPotential.mixed hpotential (mixedUtilityIntegrable_of_finite hpotential)

end UtilityGame

end GameTheory
