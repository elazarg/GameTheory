/-
# Uniform equilibrium

The finite-average form samples one of the finitely many stages, then samples
its actual outcome. Its ordinary guarded expected utility is the finite
average of stage expected payoffs. At horizon zero the outcome is `none` and
has zero utility. This makes finite-horizon approximate Nash exactly the
canonical `IsεNash`, with integration required only on compared laws.
-/

import GameTheory.Core.Approximate
import GameTheory.Repeated.Basic
import GameTheory.Math.Eventually
import GameTheory.Math.Probability.Uniform

noncomputable section

namespace GameTheory.UtilityGame

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι}

/-- The repeated strategies with one sampled stage outcome. -/
@[reducible]
def finiteAverageSignature (G : UtilityGame ι) : GameSignature ι where
  Strategy := G.RepeatedStrategy
  Outcome := Option G.form.sig.Outcome

/-- The sampled finite-horizon form. A zero-length horizon has the sole
outcome `none`; positive horizons sample a stage uniformly. -/
@[reducible]
def finiteAverageForm (G : UtilityGame ι) (horizon : ℕ) : GameForm ι where
  sig := G.finiteAverageSignature
  play profile :=
    if hzero : horizon = 0 then PMF.pure none
    else
      letI : NeZero horizon := ⟨hzero⟩
      (PMF.uniformOfFintype (Fin horizon)).bind fun t =>
        (G.form.play (G.repeatedPlay profile t)).map some

/-- Payoff of a sampled stage outcome; the empty horizon pays zero. -/
def finiteAverageOutcomeUtility (G : UtilityGame ι) :
    Option G.form.sig.Outcome → ι → ℝ
  | none, _ => 0
  | some outcome, who => G.utility outcome who

private theorem finiteAverageForm_play_zero (G : UtilityGame ι)
    (profile : G.RepeatedProfile) :
    (G.finiteAverageForm 0).play profile = PMF.pure none := by
  simp [finiteAverageForm]

private theorem finiteAverageForm_play_pos (G : UtilityGame ι)
    {horizon : ℕ} [NeZero horizon]
    (profile : G.RepeatedProfile) :
    (G.finiteAverageForm horizon).play profile =
      (PMF.uniformOfFintype (Fin horizon)).bind (fun t =>
        (G.form.play (G.repeatedPlay profile t)).map some) := by
  simp [finiteAverageForm, NeZero.ne horizon]

/-- Integration of the finite-average law is exactly integration at its
sampled stages. No unrelated repeated profile is involved. -/
theorem finiteAverageForm_integrable_iff (G : UtilityGame ι)
    (horizon : ℕ) (profile : G.RepeatedProfile) (who : ι) :
    UtilityIntegrable G.finiteAverageOutcomeUtility who
        ((G.finiteAverageForm horizon).play profile) ↔
      ∀ t : Fin horizon,
        UtilityIntegrable G.utility who
          (G.form.play (G.repeatedPlay profile t)) := by
  by_cases hzero : horizon = 0
  · subst hzero
    constructor
    · intro _ t
      exact Fin.elim0 t
    · intro _
      rw [finiteAverageForm_play_zero]
      exact payoffIntegrable_pure none _
  · let : NeZero horizon := ⟨hzero⟩
    rw [G.finiteAverageForm_play_pos]
    constructor
    · intro h t
      have hrow := payoffIntegrable_bind_conditional_on_support
        (PMF.uniformOfFintype (Fin horizon))
        (fun s => (G.form.play (G.repeatedPlay profile s)).map some)
        (fun outcome => G.finiteAverageOutcomeUtility outcome who)
        h t (PMF.mem_support_uniformOfFintype t)
      exact (payoffIntegrable_map_iff some
        (G.form.play (G.repeatedPlay profile t))
        (fun outcome => G.finiteAverageOutcomeUtility outcome who)).mp hrow
    · intro h
      apply payoffIntegrable_bind_of_finite
      intro t
      exact (payoffIntegrable_map_iff some
        (G.form.play (G.repeatedPlay profile t))
        (fun outcome => G.finiteAverageOutcomeUtility outcome who)).mpr (h t)

/-- Expected utility of the sampled finite-horizon form is the existing
guarded arithmetic average of expected stage payoffs. -/
theorem finiteAverageForm_expectedUtility_eq (G : UtilityGame ι)
    (horizon : ℕ) (profile : G.RepeatedProfile) (who : ι)
    (hstage : ∀ t < horizon,
      UtilityIntegrable G.utility who
        (G.form.play (G.repeatedPlay profile t))) :
    expectedUtility G.finiteAverageOutcomeUtility who
        ((G.finiteAverageForm horizon).play profile)
        ((G.finiteAverageForm_integrable_iff horizon profile who).2
          (fun t => hstage t t.isLt)) =
      G.finiteAveragePayoff horizon profile who hstage := by
  by_cases hzero : horizon = 0
  · subst hzero
    calc
      expectedUtility G.finiteAverageOutcomeUtility who
          ((G.finiteAverageForm 0).play profile)
          ((G.finiteAverageForm_integrable_iff 0 profile who).2
            (fun t => hstage t t.isLt)) =
          expectedUtility G.finiteAverageOutcomeUtility who
            (PMF.pure none) (payoffIntegrable_pure none _) := by
        apply expectedUtility_congr_law
        exact G.finiteAverageForm_play_zero profile
      _ = G.finiteAveragePayoff 0 profile who hstage := by
        simp [finiteAveragePayoff, finiteAverageOutcomeUtility]
  · let : NeZero horizon := ⟨hzero⟩
    let p : PMF (Fin horizon) := PMF.uniformOfFintype (Fin horizon)
    let q : Fin horizon → PMF (Option G.form.sig.Outcome) :=
      fun t => (G.form.play (G.repeatedPlay profile t)).map some
    let u : Option G.form.sig.Outcome → ℝ :=
      fun outcome => G.finiteAverageOutcomeUtility outcome who
    have hcond (t : Fin horizon) : PayoffIntegrable (q t) u :=
      (payoffIntegrable_map_iff some
        (G.form.play (G.repeatedPlay profile t)) u).2
          (hstage t t.isLt)
    have hbind : PayoffIntegrable (p.bind q) u :=
      payoffIntegrable_bind_of_finite p q u hcond
    have hrow (t : Fin horizon) :
        expect (q t) u (hcond t) =
          G.stagePayoff (G.repeatedPlay profile t) who
            (hstage t t.isLt) := by
      simpa only [q, u, stagePayoff, expectedUtility,
        finiteAverageOutcomeUtility,
        Function.comp_def] using
        expect_map some (G.form.play (G.repeatedPlay profile t)) u
          (hstage t t.isLt) (hcond t)
    calc
      expectedUtility G.finiteAverageOutcomeUtility who
          ((G.finiteAverageForm horizon).play profile)
          ((G.finiteAverageForm_integrable_iff horizon profile who).2
            (fun t => hstage t t.isLt)) =
          expectedUtility G.finiteAverageOutcomeUtility who
            (p.bind q) hbind := by
        apply expectedUtility_congr_law
        exact G.finiteAverageForm_play_pos profile
      _ =
          expect p (fun t => expect (q t) u (hcond t))
            (payoffIntegrable_bind_conditionalExpectation p q u hbind hcond) := by
        simpa only [expectedUtility, p, q, u] using
          expect_bind_tower p q u hbind hcond
      _ = expect p
          (fun t => G.stagePayoff (G.repeatedPlay profile t) who
            (hstage t t.isLt))
          (payoffIntegrable_of_finite _ _) := by
        apply expect_congr_on_support
        intro t _
        exact hrow t
      _ = G.finiteAveragePayoff horizon profile who hstage := by
        rw [expect_uniformFin]
        simp only [finiteAveragePayoff, div_eq_mul_inv]
        ring

/-- Approximate Nash for the sampled finite-average form is canonical
`IsεNash`, so undefined deviation laws cannot satisfy it vacuously. -/
def IsεFiniteRepeatedNash (G : UtilityGame ι) [DecidableEq ι]
    (horizon : ℕ) (epsilon : ℝ) (profile : G.RepeatedProfile) : Prop :=
  IsεNash (G.finiteAverageForm horizon) G.finiteAverageOutcomeUtility
    epsilon profile

/-- Approximate Nash in the sampled form compares the guarded averages of
the incumbent and each unilateral deviation. -/
theorem isεFiniteRepeatedNash_iff
    (G : UtilityGame ι) [DecidableEq ι]
    {horizon : ℕ} {epsilon : ℝ} {profile : G.RepeatedProfile} :
    G.IsεFiniteRepeatedNash horizon epsilon profile ↔
      ∀ who deviation,
        ∃ hincumbent : ∀ t < horizon,
            UtilityIntegrable G.utility who
              (G.form.play (G.repeatedPlay profile t)),
          ∃ hdeviation : ∀ t < horizon,
              UtilityIntegrable G.utility who
                (G.form.play (G.repeatedPlay
                  (Profile.update profile who deviation) t)),
            G.finiteAveragePayoff horizon
                (Profile.update profile who deviation) who hdeviation ≤
              G.finiteAveragePayoff horizon profile who hincumbent + epsilon := by
  rw [IsεFiniteRepeatedNash, isεNash_iff]
  constructor
  · intro h who deviation
    rcases h who deviation with ⟨hincumbent, hdeviation, hle⟩
    let hi : ∀ t < horizon, UtilityIntegrable G.utility who
        (G.form.play (G.repeatedPlay profile t)) :=
      fun t ht => (G.finiteAverageForm_integrable_iff
        horizon profile who).1 hincumbent ⟨t, ht⟩
    let hd : ∀ t < horizon, UtilityIntegrable G.utility who
        (G.form.play (G.repeatedPlay
          (Profile.update profile who deviation) t)) :=
      fun t ht => (G.finiteAverageForm_integrable_iff
        horizon (Profile.update profile who deviation) who).1
          hdeviation ⟨t, ht⟩
    refine ⟨hi, hd, ?_⟩
    calc
      G.finiteAveragePayoff horizon
          (Profile.update profile who deviation) who hd =
          expectedUtility G.finiteAverageOutcomeUtility who
            ((G.finiteAverageForm horizon).play
              (Profile.update profile who deviation)) hdeviation :=
        (G.finiteAverageForm_expectedUtility_eq horizon
          (Profile.update profile who deviation) who hd).symm
      _ ≤ expectedUtility G.finiteAverageOutcomeUtility who
          ((G.finiteAverageForm horizon).play profile) hincumbent +
          epsilon := hle
      _ = G.finiteAveragePayoff horizon profile who hi + epsilon := by
        rw [G.finiteAverageForm_expectedUtility_eq horizon profile who hi]
  · intro h who deviation
    rcases h who deviation with ⟨hi, hd, hle⟩
    refine ⟨(G.finiteAverageForm_integrable_iff
        horizon profile who).2 (fun t => hi t t.isLt),
      (G.finiteAverageForm_integrable_iff
        horizon (Profile.update profile who deviation) who).2
          (fun t => hd t t.isLt), ?_⟩
    calc
      expectedUtility G.finiteAverageOutcomeUtility who
          ((G.finiteAverageForm horizon).play
            (Profile.update profile who deviation)) _ =
          G.finiteAveragePayoff horizon
            (Profile.update profile who deviation) who hd :=
        G.finiteAverageForm_expectedUtility_eq horizon
          (Profile.update profile who deviation) who hd
      _ ≤ G.finiteAveragePayoff horizon profile who hi + epsilon := hle
      _ = expectedUtility G.finiteAverageOutcomeUtility who
          ((G.finiteAverageForm horizon).play profile) _ + epsilon := by
        rw [G.finiteAverageForm_expectedUtility_eq horizon profile who hi]

/-- A single horizon threshold makes the profile approximately Nash at every
longer truncation. -/
abbrev IsUniformεEquilibrium (G : UtilityGame ι) [DecidableEq ι]
    (epsilon : ℝ) (profile : G.RepeatedProfile) : Prop :=
  GameTheory.Math.EventuallyAtAll fun horizon =>
    G.IsεFiniteRepeatedNash horizon epsilon profile

/-- A uniform equilibrium has an actually integrable long-run average and
satisfies every positive uniform approximation tolerance. -/
def IsUniformEquilibrium (G : UtilityGame ι) [DecidableEq ι]
    (profile : G.RepeatedProfile) : Prop :=
  (∃ (hstage : ∀ t who,
      UtilityIntegrable G.utility who
        (G.form.play (G.repeatedPlay profile t)))
      (value : ι → ℝ),
      G.HasLongRunAveragePayoff profile hstage value) ∧
    ∀ epsilon : ℝ, 0 < epsilon → G.IsUniformεEquilibrium epsilon profile

/-- Finite-horizon approximate Nash is monotone in the error allowance. -/
theorem IsεFiniteRepeatedNash.mono
    {G : UtilityGame ι} [DecidableEq ι]
    {horizon : ℕ} {epsilon epsilon' : ℝ} {profile : G.RepeatedProfile}
    (h : G.IsεFiniteRepeatedNash horizon epsilon profile)
    (hle : epsilon ≤ epsilon') :
    G.IsεFiniteRepeatedNash horizon epsilon' profile :=
  IsεNash.mono (G.finiteAverageForm horizon)
    G.finiteAverageOutcomeUtility h hle

/-- Uniform approximate equilibrium is monotone in the error allowance. -/
theorem IsUniformεEquilibrium.mono
    {G : UtilityGame ι} [DecidableEq ι]
    {epsilon epsilon' : ℝ} {profile : G.RepeatedProfile}
    (h : G.IsUniformεEquilibrium epsilon profile)
    (hle : epsilon ≤ epsilon') :
    G.IsUniformεEquilibrium epsilon' profile :=
  GameTheory.Math.EventuallyAtAll.mono h fun _ hhorizon => hhorizon.mono hle

/-- Stationary repetition of a stage Nash equilibrium is uniform: every
nonempty finite truncation is exact Nash and its average is constant. -/
theorem stationaryRepeatedProfile_isUniformEquilibrium_of_isNash
    (G : UtilityGame ι) [DecidableEq ι]
    {profile : Profile G.form.sig}
    (hnash : IsNash G.form (euPreference G.utility) profile) :
    G.IsUniformEquilibrium (G.stationaryRepeatedProfile profile) := by
  have hinc (who : ι) :
      UtilityIntegrable G.utility who (G.form.play profile) := by
    rcases (isNash_iff profile).1 hnash who (profile who) with ⟨hi, _, _⟩
    exact hi
  refine ⟨⟨(fun t who => by simpa using hinc who),
    (fun who => G.stagePayoff profile who (hinc who)),
    G.hasLongRunAveragePayoff_stationaryRepeatedProfile profile hinc⟩, ?_⟩
  intro epsilon hepsilon
  refine ⟨1, fun horizon hhorizon => ?_⟩
  show G.IsεFiniteRepeatedNash horizon epsilon
    (G.stationaryRepeatedProfile profile)
  rw [G.isεFiniteRepeatedNash_iff]
  intro who deviation
  have hhorizon0 : horizon ≠ 0 := by omega
  let updated := Profile.update
    (G.stationaryRepeatedProfile profile) who deviation
  let own (t : ℕ) : G.form.sig.Strategy who :=
    deviation (List.ofFn fun k : Fin t => G.repeatedPlay updated k)
  have hstageNash (t : ℕ) :=
    (isNash_iff profile).1 hnash who (own t)
  have hupdated (t : ℕ) :
      G.repeatedPlay updated t = Profile.update profile who (own t) := by
    exact G.repeatedPlay_update_stationaryRepeatedProfile
      profile who deviation t
  let hi : ∀ t < horizon,
      UtilityIntegrable G.utility who
        (G.form.play (G.repeatedPlay
          (G.stationaryRepeatedProfile profile) t)) :=
    fun t _ => by simpa using hinc who
  let hd : ∀ t < horizon,
      UtilityIntegrable G.utility who
        (G.form.play (G.repeatedPlay updated t)) := by
    intro t _
    rw [hupdated t]
    exact (hstageNash t).2.1
  refine ⟨hi, hd, ?_⟩
  have hdeviation : G.finiteAveragePayoff horizon updated who hd ≤
      G.stagePayoff profile who (hinc who) := by
    apply G.finiteAveragePayoff_le_of_forall_stagePayoff_le
      hd (fun t => ?_) hhorizon0
    simpa only [hupdated t, stagePayoff] using (hstageNash t).2.2
  rw [G.finiteAveragePayoff_stationaryRepeatedProfile
    hhorizon0 profile who (hinc who)]
  exact hdeviation.trans (le_add_of_nonneg_right hepsilon.le)

end GameTheory.UtilityGame
