/-
# Realization of randomized information-local policies

Law transfer between mixed and behavioral presentations, including unilateral
and bounded counterfactual realizations. This is a one-way consumer of the
strategic compiler and the focused policy-randomization mathematics.
-/

import GameTheory.Protocol.Strategic
import GameTheory.Protocol.PolicyRandomization

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability GameTheory

universe uι us ua

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace InformationModel

variable (M : InformationModel E)
variable [Fintype ι]
/-- If no player is asked twice at an information state where its answer can
vary, pre-drawing every behavioral choice commutes with compilation. -/
theorem toGameForm_mixed_play_toMixed
    [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (behavioral : Profile M.behavioralSignature) (horizon : ℕ) :
    ((M.toGameForm horizon).mixed).play (fun i => (behavioral i).toMixed) =
      (M.toBehavioralGameForm horizon).play behavioral := by
  rw [toGameForm_mixed_play, toBehavioralGameForm_play]
  exact M.runMixed_toMixed hactsOnce behavioral horizon

/-- If histories with the same information state constrain a player's drawn
policy alike, reading a mixed policy behaviorally commutes with compilation. -/
theorem toGameForm_mixed_play_toBehavioral
    (hconstrain : M.ConstrainsAlike) (mixed : (i : ι) → M.MixedPolicy i)
    (horizon : ℕ) :
    ((M.toGameForm horizon).mixed).play mixed =
      (M.toBehavioralGameForm horizon).play
        (fun i => (mixed i).toBehavioral) := by
  rw [toGameForm_mixed_play, toBehavioralGameForm_play]
  exact M.runMixed_toBehavioral hconstrain horizon mixed

/-- Under both sharp hypotheses, behavioral profiles and static mixed profiles
describe exactly the same set of compiled history laws. -/
theorem toBehavioralGameForm_play_image_eq_mixed_play_image
    (hactsOnce : M.ActsOnceWhereItMatters) (hconstrain : M.ConstrainsAlike)
    (horizon : ℕ)
    (hfinite : ∀ behavioral : Profile M.behavioralSignature,
      ∀ i, (M.behavioralSupportSitesFrom behavioral horizon E.initHistory i).Finite) :
    { law | ∃ behavioral : Profile M.behavioralSignature,
        (M.toBehavioralGameForm horizon).play behavioral = law } =
      { law | ∃ mixed : (i : ι) → M.MixedPolicy i,
        ((M.toGameForm horizon).mixed).play mixed = law } := by
  show
    { law | ∃ behavioral : (i : ι) → M.BehavioralPolicy i,
        M.runBehavioral behavioral horizon = law } =
      { law | ∃ mixed : (i : ι) → M.MixedPolicy i,
        M.runMixed mixed horizon = law }
  ext law
  constructor
  · rintro ⟨behavioral, hbehavioral⟩
    obtain ⟨mixed, hmixed⟩ := M.exists_mixed_runMixed_eq_runBehavioral
      hactsOnce behavioral horizon (hfinite behavioral)
    exact ⟨mixed, hmixed.trans hbehavioral⟩
  · rintro ⟨mixed, hmixed⟩
    exact ⟨fun i => (mixed i).toBehavioral,
      (M.runMixed_toBehavioral hconstrain horizon mixed).symm.trans hmixed⟩

/-! ## Unilateral realization

Whole-profile law equality is insufficient for strategic transfer: a
unilateral theorem must keep every opponent coordinate fixed. The proof
factors the independent pure-policy draw at the deviator, establishes the
round trip against pure opponents, and integrates over arbitrary opponent
laws. -/

section UnilateralRealization

variable [DecidableEq ι]
  [∀ i, Fintype (M.InfoState i)] [∀ i, DecidableEq (M.InfoState i)]

omit [∀ i, Fintype (M.InfoState i)]
  [∀ i, DecidableEq (M.InfoState i)] in
private theorem runMixed_update_eq_opponents_bind
    (mixed : Profile M.strategicSignature.mixed) (who : ι)
    (replacement : M.MixedPolicy who) (horizon : ℕ) :
    M.runMixed (Profile.update mixed who replacement) horizon =
      (independentProduct fun other : {other // other ≠ who} => mixed other.1).bind
        fun opponents =>
          replacement.bind fun policy =>
            M.run
              ((Equiv.piSplitAt who fun i => M.Policy i).symm
                (policy, opponents)) horizon := by
  rw [runMixed, runMixedFrom]
  rw [independentProduct_splitAt
    (fun i => Profile.update mixed who replacement i) who]
  rw [Profile.update_same]
  have hothers :
      (fun other : {other // other ≠ who} =>
          Profile.update mixed who replacement other.1) =
        (fun other : {other // other ≠ who} => mixed other.1) := by
    funext other
    exact Profile.update_of_ne mixed replacement other.2
  rw [hothers, PMF.bind_bind]
  simp_rw [PMF.bind_map]
  rw [PMF.bind_comm]
  rfl

private theorem kuhn_mixed_roundTrip_against_pure
    (hrecall : M.PerfectRecall) (who : ι)
    (replacement : M.MixedPolicy who)
    (opponents : ∀ other : {other // other ≠ who}, M.Policy other.1)
    (horizon : ℕ) :
    (((InformationModel.MixedPolicy.toBehavioral
        (M := M) replacement).toMixed).bind fun policy =>
        M.run
          ((Equiv.piSplitAt who fun i => M.Policy i).symm
            (policy, opponents)) horizon) =
      (replacement.bind fun policy =>
        M.run
          ((Equiv.piSplitAt who fun i => M.Policy i).symm
            (policy, opponents)) horizon) := by
  let pureProfile : Profile M.strategicSignature :=
    (Equiv.piSplitAt who fun i => M.Policy i).symm
      (replacement.support_nonempty.choose, opponents)
  let pureMixed : Profile M.strategicSignature.mixed :=
    fun i => PMF.pure (pureProfile i)
  let roundTrip : M.MixedPolicy who :=
    (InformationModel.MixedPolicy.toBehavioral
      (M := M) replacement).toMixed
  let mixedProfile : Profile M.strategicSignature.mixed :=
    Profile.update (sig := M.strategicSignature.mixed)
      pureMixed who replacement
  let behavioral : Profile M.behavioralSignature :=
    fun i => InformationModel.MixedPolicy.toBehavioral
      (M := M) (mixedProfile i)
  have hroundTrip :=
    (M.runMixed_toMixed
      (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
      behavioral horizon).trans
      (M.runMixed_toBehavioral
        (InformationModel.constrainsAlike_of_perfectRecall hrecall)
        horizon mixedProfile).symm
  have hroundProfile :
      (fun i =>
        (InformationModel.MixedPolicy.toBehavioral
          (M := M) (mixedProfile i)).toMixed) =
        Profile.update (sig := M.strategicSignature.mixed)
          pureMixed who roundTrip := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [mixedProfile, pureMixed, roundTrip]
    · simp [mixedProfile, pureMixed, roundTrip, hi,
        InformationModel.MixedPolicy.toBehavioral_pure,
        InformationModel.Policy.toBehavioral_toMixed]
  have hpureProfile :
      (fun other : {other // other ≠ who} => pureProfile other.1) =
        opponents := by
    funext other
    simp [pureProfile, other.2]
  rw [hroundProfile,
    runMixed_update_eq_opponents_bind (M := M)
      pureMixed who roundTrip horizon,
    runMixed_update_eq_opponents_bind (M := M)
      pureMixed who replacement horizon,
    independentProduct_pure] at hroundTrip
  simp only [PMF.pure_bind] at hroundTrip
  rw [hpureProfile] at hroundTrip
  simpa [roundTrip] using hroundTrip

/-- A player's mixed strategy may be read behaviorally and redrawn as mixed
without changing the history law against the other players' fixed mixed
strategies. -/
theorem kuhn_mixed_roundTrip_update
    (hrecall : M.PerfectRecall)
    (mixed : Profile M.strategicSignature.mixed) (who : ι)
    (replacement : M.MixedPolicy who) (horizon : ℕ) :
    M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed) mixed who
          (InformationModel.MixedPolicy.toBehavioral
            (M := M) replacement).toMixed) horizon =
      M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed)
          mixed who replacement) horizon := by
  rw [runMixed_update_eq_opponents_bind (M := M)
      mixed who (InformationModel.MixedPolicy.toBehavioral
        (M := M) replacement).toMixed horizon,
    runMixed_update_eq_opponents_bind (M := M)
      mixed who replacement horizon]
  refine bind_congr_on_support _ fun opponents _ => ?_
  exact kuhn_mixed_roundTrip_against_pure
    (M := M) hrecall who replacement opponents horizon

omit [Fintype ι] [∀ i, DecidableEq (M.InfoState i)] in
private theorem toMixed_update
    (behavioral : Profile M.behavioralSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) :
    (fun i => ((Profile.update behavioral who replacement) i).toMixed) =
      Profile.update (sig := M.strategicSignature.mixed)
        (fun i => (behavioral i).toMixed) who
        replacement.toMixed := by
  funext i
  by_cases hi : i = who
  · subst i
    rw [Profile.update_same, Profile.update_same]
  · rw [Profile.update_of_ne _ _ hi, Profile.update_of_ne _ _ hi]

omit [Fintype ι] [∀ i, Fintype (M.InfoState i)]
  [∀ i, DecidableEq (M.InfoState i)] in
private theorem toBehavioral_update
    (mixed : Profile M.strategicSignature.mixed) (who : ι)
    (replacement : M.MixedPolicy who) :
    (fun i => InformationModel.MixedPolicy.toBehavioral
        (M := M) (Profile.update mixed who replacement i)) =
      Profile.update (sig := M.behavioralSignature)
        (fun i => InformationModel.MixedPolicy.toBehavioral
          (M := M) (mixed i)) who
        (InformationModel.MixedPolicy.toBehavioral
          (M := M) replacement) := by
  funext i
  by_cases hi : i = who
  · subst i
    rw [Profile.update_same, Profile.update_same]
  · rw [Profile.update_of_ne _ _ hi, Profile.update_of_ne _ _ hi]

/-- A behavioral policy and its behavioral-to-mixed-to-behavioral round trip
are realization-equivalent for one player while every other behavioral policy
is held fixed. -/
theorem kuhn_behavioral_roundTrip_update
    (hrecall : M.PerfectRecall)
    (behavioral : Profile M.behavioralSignature) (who : ι)
    (replacement : M.BehavioralPolicy who) (horizon : ℕ) :
    M.runBehavioral
        (Profile.update behavioral who
          (InformationModel.MixedPolicy.toBehavioral
            (M := M) replacement.toMixed))
        horizon =
      M.runBehavioral (Profile.update behavioral who replacement) horizon := by
  let roundTrip : M.BehavioralPolicy who :=
    InformationModel.MixedPolicy.toBehavioral
      (M := M) replacement.toMixed
  have hleft := M.runMixed_toMixed
    (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    (Profile.update behavioral who roundTrip) horizon
  have hright := M.runMixed_toMixed
    (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    (Profile.update behavioral who replacement) horizon
  rw [toMixed_update (M := M) behavioral who roundTrip] at hleft
  rw [toMixed_update (M := M) behavioral who replacement] at hright
  have hlocal := M.kuhn_mixed_roundTrip_update hrecall
    (fun i => (behavioral i).toMixed) who replacement.toMixed horizon
  have hresult := hleft.symm.trans (hlocal.trans hright)
  simpa [roundTrip] using hresult

/-- Replacing one player's mixed strategy by an arbitrary behavioral strategy
commutes with the conditional behavioral reading while every nondeviator keeps
its induced behavior. -/
theorem kuhn_mixed_update_toBehavioral
    (hrecall : M.PerfectRecall)
    (mixed : Profile M.strategicSignature.mixed) (who : ι)
    (replacement : M.BehavioralPolicy who) (horizon : ℕ) :
    M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          (fun i => InformationModel.MixedPolicy.toBehavioral
            (M := M) (mixed i)) who replacement)
        horizon =
      M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed)
          mixed who replacement.toMixed) horizon := by
  let behavioral : Profile M.behavioralSignature :=
    fun i => InformationModel.MixedPolicy.toBehavioral
      (M := M) (mixed i)
  have hback := M.runMixed_toBehavioral
    (InformationModel.constrainsAlike_of_perfectRecall hrecall) horizon
    (Profile.update mixed who replacement.toMixed)
  rw [toBehavioral_update (M := M)
    mixed who replacement.toMixed] at hback
  have hround := M.kuhn_behavioral_roundTrip_update
    hrecall behavioral who replacement horizon
  exact hround.symm.trans hback.symm

/-- Starting from a behavioral profile, an arbitrary mixed deviation is
realized by its behavioral reading without changing any nondeviator's
behavioral policy. -/
theorem kuhn_behavioral_update_toMixed
    (hrecall : M.PerfectRecall)
    (behavioral : Profile M.behavioralSignature) (who : ι)
    (replacement : M.MixedPolicy who) (horizon : ℕ) :
    M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed)
          (fun i => (behavioral i).toMixed) who replacement)
        horizon =
      M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          behavioral who
            (InformationModel.MixedPolicy.toBehavioral
              (M := M) replacement)) horizon := by
  let deviation : M.BehavioralPolicy who :=
    InformationModel.MixedPolicy.toBehavioral (M := M) replacement
  let roundBehavioral : Profile M.behavioralSignature :=
    fun i => InformationModel.MixedPolicy.toBehavioral
      (M := M) (behavioral i).toMixed
  have hforward := M.runMixed_toMixed
    (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    (Profile.update behavioral who deviation) horizon
  rw [toMixed_update (M := M) behavioral who deviation] at hforward
  have hbackBase := M.runMixed_toBehavioral
    (InformationModel.constrainsAlike_of_perfectRecall hrecall) horizon
    (Profile.update (sig := M.strategicSignature.mixed)
      (fun i => (behavioral i).toMixed) who deviation.toMixed)
  rw [toBehavioral_update (M := M)
    (fun i => (behavioral i).toMixed) who deviation.toMixed] at hbackBase
  have hbaseToRound :
      M.runBehavioral (Profile.update behavioral who deviation) horizon =
        M.runBehavioral
          (Profile.update roundBehavioral who
            (InformationModel.MixedPolicy.toBehavioral
              (M := M) deviation.toMixed))
          horizon :=
    hforward.symm.trans hbackBase
  have hplayer := M.kuhn_behavioral_roundTrip_update
    hrecall roundBehavioral who deviation horizon
  have hbaseToDeviation := hbaseToRound.trans hplayer
  have hbackDeviation := M.runMixed_toBehavioral
    (InformationModel.constrainsAlike_of_perfectRecall hrecall) horizon
    (Profile.update (sig := M.strategicSignature.mixed)
      (fun i => (behavioral i).toMixed) who replacement)
  rw [toBehavioral_update (M := M)
    (fun i => (behavioral i).toMixed) who replacement] at hbackDeviation
  have hresult := hbackDeviation.trans hbaseToDeviation.symm
  simpa [deviation, roundBehavioral] using hresult

end UnilateralRealization

/-! ## Bounded unilateral realization

The ambient information-state carriers need not be finite when one finite
family of sites covers every legal history through the chosen horizon.  The
same sites can then be used before and after a unilateral update, which is the
counterfactual strength needed by equilibrium transfer.
-/

section BoundedUnilateralRealization

variable [DecidableEq ι]

private theorem kuhn_mixed_roundTripWithin_against_pure
    (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i))
    (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon)
    (who : ι) (replacement : M.MixedPolicy who)
    (replacementFallback : M.Policy who)
    (opponents : ∀ other : {other // other ≠ who}, M.Policy other.1) :
    (((InformationModel.MixedPolicy.toBehavioral
        (M := M) replacement).toMixedWithin M (sites who) replacementFallback).bind fun policy =>
        M.run
          ((Equiv.piSplitAt who fun i => M.Policy i).symm
            (policy, opponents)) horizon) =
      (replacement.bind fun policy =>
        M.run
          ((Equiv.piSplitAt who fun i => M.Policy i).symm
            (policy, opponents)) horizon) := by
  let pureProfile : Profile M.strategicSignature :=
    (Equiv.piSplitAt who fun i => M.Policy i).symm
      (replacement.support_nonempty.choose, opponents)
  let fallbackProfile : Profile M.strategicSignature :=
    Profile.update pureProfile who replacementFallback
  let pureMixed : Profile M.strategicSignature.mixed :=
    fun i => PMF.pure (pureProfile i)
  let roundTrip : M.MixedPolicy who :=
    (InformationModel.MixedPolicy.toBehavioral
      (M := M) replacement).toMixedWithin M (sites who) replacementFallback
  let mixedProfile : Profile M.strategicSignature.mixed :=
    Profile.update (sig := M.strategicSignature.mixed)
      pureMixed who replacement
  let behavioral : Profile M.behavioralSignature :=
    fun i => InformationModel.MixedPolicy.toBehavioral
      (M := M) (mixedProfile i)
  have hroundTrip :=
    (M.runMixed_toMixedWithin (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
      sites behavioral fallbackProfile horizon hcover).trans
      (M.runMixed_toBehavioral
        (InformationModel.constrainsAlike_of_perfectRecall hrecall)
        horizon mixedProfile).symm
  have hroundProfile :
      (fun i =>
        (InformationModel.MixedPolicy.toBehavioral
          (M := M) (mixedProfile i)).toMixedWithin M (sites i) (fallbackProfile i)) =
        Profile.update (sig := M.strategicSignature.mixed)
          pureMixed who roundTrip := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [mixedProfile, fallbackProfile, roundTrip]
    · simp [mixedProfile, fallbackProfile, pureMixed, roundTrip, hi,
        InformationModel.MixedPolicy.toBehavioral_pure,
        InformationModel.Policy.toBehavioral_toMixedWithin]
  have hpureProfile :
      (fun other : {other // other ≠ who} => pureProfile other.1) =
        opponents := by
    funext other
    simp [pureProfile, other.2]
  rw [hroundProfile,
    runMixed_update_eq_opponents_bind (M := M)
      pureMixed who roundTrip horizon,
    runMixed_update_eq_opponents_bind (M := M)
      pureMixed who replacement horizon,
    independentProduct_pure] at hroundTrip
  simp only [PMF.pure_bind] at hroundTrip
  rw [hpureProfile] at hroundTrip
  simpa [roundTrip] using hroundTrip

private theorem kuhn_mixed_roundTripWithinWith_against_pure
    (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i))
    (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon)
    (who : ι) (replacement : M.MixedPolicy who)
    (replacementFallback : M.Policy who)
    (opponents : ∀ other : {other // other ≠ who}, M.Policy other.1) :
    (((InformationModel.MixedPolicy.toBehavioralWith (M := M)
        replacement replacementFallback).toMixedWithin M (sites who)
        replacementFallback).bind fun policy =>
        M.run
          ((Equiv.piSplitAt who fun i => M.Policy i).symm
            (policy, opponents)) horizon) =
      (replacement.bind fun policy =>
        M.run
          ((Equiv.piSplitAt who fun i => M.Policy i).symm
            (policy, opponents)) horizon) := by
  let pureProfile : Profile M.strategicSignature :=
    (Equiv.piSplitAt who fun i => M.Policy i).symm
      (replacement.support_nonempty.choose, opponents)
  let fallbackProfile : Profile M.strategicSignature :=
    Profile.update pureProfile who replacementFallback
  let pureMixed : Profile M.strategicSignature.mixed :=
    fun i => PMF.pure (pureProfile i)
  let roundTrip : M.MixedPolicy who :=
    (InformationModel.MixedPolicy.toBehavioralWith (M := M)
      replacement replacementFallback).toMixedWithin M (sites who) replacementFallback
  let mixedProfile : Profile M.strategicSignature.mixed :=
    Profile.update (sig := M.strategicSignature.mixed)
      pureMixed who replacement
  let behavioral : Profile M.behavioralSignature :=
    fun i => InformationModel.MixedPolicy.toBehavioralWith
      (M := M) (mixedProfile i) (fallbackProfile i)
  have hroundTrip :=
    (M.runMixed_toMixedWithin (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
      sites behavioral fallbackProfile horizon hcover).trans
      (M.runMixed_toBehavioralWith
        (InformationModel.constrainsAlike_of_perfectRecall hrecall)
        fallbackProfile horizon mixedProfile).symm
  have hroundProfile :
      (fun i => (InformationModel.MixedPolicy.toBehavioralWith
        (M := M) (mixedProfile i) (fallbackProfile i)).toMixedWithin M
        (sites i) (fallbackProfile i)) =
        Profile.update (sig := M.strategicSignature.mixed)
          pureMixed who roundTrip := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [mixedProfile, fallbackProfile, roundTrip]
    · simp [mixedProfile, fallbackProfile, pureMixed, roundTrip, hi,
        InformationModel.MixedPolicy.toBehavioralWith_pure_self,
        InformationModel.Policy.toBehavioral_toMixedWithin]
  have hpureProfile :
      (fun other : {other // other ≠ who} => pureProfile other.1) =
        opponents := by
    funext other
    simp [pureProfile, other.2]
  rw [hroundProfile,
    runMixed_update_eq_opponents_bind (M := M)
      pureMixed who roundTrip horizon,
    runMixed_update_eq_opponents_bind (M := M)
      pureMixed who replacement horizon,
    independentProduct_pure] at hroundTrip
  simp only [PMF.pure_bind] at hroundTrip
  rw [hpureProfile] at hroundTrip
  simpa [roundTrip] using hroundTrip

/-- A finite counterfactual site cover makes the mixed–behavioral–mixed
round trip realization-equivalent for one player against arbitrary fixed
mixed opponents. -/
theorem kuhn_mixed_roundTrip_updateWithin
    (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i))
    (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon)
    (mixed : Profile M.strategicSignature.mixed) (who : ι)
    (replacement : M.MixedPolicy who)
    (replacementFallback : M.Policy who) :
    M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed) mixed who
          ((InformationModel.MixedPolicy.toBehavioral
            (M := M) replacement).toMixedWithin M (sites who) replacementFallback)) horizon =
      M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed)
          mixed who replacement) horizon := by
  rw [runMixed_update_eq_opponents_bind (M := M)
      mixed who ((InformationModel.MixedPolicy.toBehavioral
        (M := M) replacement).toMixedWithin M (sites who) replacementFallback) horizon,
    runMixed_update_eq_opponents_bind (M := M)
      mixed who replacement horizon]
  refine bind_congr_on_support _ fun opponents _ => ?_
  exact kuhn_mixed_roundTripWithin_against_pure
    (M := M) hrecall sites horizon hcover who replacement replacementFallback
      opponents

/-- A fixed zero-mass fallback can be retained while a finite
mixed–behavioral–mixed round trip replaces one player against arbitrary mixed
opponents. -/
theorem kuhn_mixed_roundTrip_updateWithinWith
    (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i))
    (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon)
    (mixed : Profile M.strategicSignature.mixed) (who : ι)
    (replacement : M.MixedPolicy who)
    (replacementFallback : M.Policy who) :
    M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed) mixed who
          ((InformationModel.MixedPolicy.toBehavioralWith (M := M)
             replacement replacementFallback).toMixedWithin M (sites who)
             replacementFallback)) horizon =
      M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed)
          mixed who replacement) horizon := by
  rw [runMixed_update_eq_opponents_bind (M := M)
      mixed who ((InformationModel.MixedPolicy.toBehavioralWith (M := M)
        replacement replacementFallback).toMixedWithin M (sites who) replacementFallback) horizon,
    runMixed_update_eq_opponents_bind (M := M)
      mixed who replacement horizon]
  refine bind_congr_on_support _ fun opponents _ => ?_
  exact kuhn_mixed_roundTripWithinWith_against_pure
    (M := M) hrecall sites horizon hcover who replacement
      replacementFallback opponents

/-- At one target history, the mixed-policy round trip needs only that
history's finitely many queried information sites. -/
private theorem kuhn_mixed_roundTripWithinWith_against_pure_apply
    (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i)) (horizon : ℕ)
    (target : E.History)
    (hqueried : ∀ i info, info ∈ M.queriedInfos i target.trace → info ∈ sites i)
    (who : ι) (replacement : M.MixedPolicy who)
    (replacementFallback : M.Policy who)
    (opponents : ∀ other : {other // other ≠ who}, M.Policy other.1) :
    (((InformationModel.MixedPolicy.toBehavioralWith (M := M)
        replacement replacementFallback).toMixedWithin M (sites who)
        replacementFallback).bind fun policy =>
        M.run ((Equiv.piSplitAt who fun i => M.Policy i).symm
          (policy, opponents)) horizon) target =
      (replacement.bind fun policy =>
        M.run ((Equiv.piSplitAt who fun i => M.Policy i).symm
          (policy, opponents)) horizon) target := by
  let pureProfile : Profile M.strategicSignature :=
    (Equiv.piSplitAt who fun i => M.Policy i).symm
      (replacement.support_nonempty.choose, opponents)
  let fallbackProfile : Profile M.strategicSignature :=
    Profile.update pureProfile who replacementFallback
  let pureMixed : Profile M.strategicSignature.mixed :=
    fun i => PMF.pure (pureProfile i)
  let roundTrip : M.MixedPolicy who :=
    (InformationModel.MixedPolicy.toBehavioralWith (M := M)
      replacement replacementFallback).toMixedWithin M (sites who)
      replacementFallback
  let mixedProfile : Profile M.strategicSignature.mixed :=
    Profile.update (sig := M.strategicSignature.mixed)
      pureMixed who replacement
  let behavioral : Profile M.behavioralSignature :=
    fun i => InformationModel.MixedPolicy.toBehavioralWith
      (M := M) (mixedProfile i) (fallbackProfile i)
  have hroundTrip :=
    (M.runMixed_toMixedWithin_apply_of_queriedInfos
      (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
      sites behavioral fallbackProfile horizon target hqueried).trans
      (congrArg (fun law : PMF E.History => law target)
        (M.runMixed_toBehavioralWith
          (InformationModel.constrainsAlike_of_perfectRecall hrecall)
          fallbackProfile horizon mixedProfile)).symm
  have hroundProfile :
      (fun i => (InformationModel.MixedPolicy.toBehavioralWith
        (M := M) (mixedProfile i) (fallbackProfile i)).toMixedWithin M
        (sites i) (fallbackProfile i)) =
        Profile.update (sig := M.strategicSignature.mixed)
          pureMixed who roundTrip := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [mixedProfile, fallbackProfile, roundTrip]
    · simp [mixedProfile, fallbackProfile, pureMixed, roundTrip, hi,
        InformationModel.MixedPolicy.toBehavioralWith_pure_self,
        InformationModel.Policy.toBehavioral_toMixedWithin]
  have hpureProfile :
      (fun other : {other // other ≠ who} => pureProfile other.1) =
        opponents := by
    funext other
    simp [pureProfile, other.2]
  rw [hroundProfile,
    runMixed_update_eq_opponents_bind (M := M)
      pureMixed who roundTrip horizon,
    runMixed_update_eq_opponents_bind (M := M)
      pureMixed who replacement horizon,
    independentProduct_pure] at hroundTrip
  simp only [PMF.pure_bind] at hroundTrip
  rw [hpureProfile] at hroundTrip
  simpa [roundTrip] using hroundTrip

/-- A mixed round trip preserves the mass of one target whenever the sampled
sites include exactly the information coordinates queried by its trace. -/
theorem kuhn_mixed_roundTrip_updateWithinWith_apply_of_queriedInfos
    (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i)) (horizon : ℕ)
    (target : E.History)
    (hqueried : ∀ i info, info ∈ M.queriedInfos i target.trace → info ∈ sites i)
    (mixed : Profile M.strategicSignature.mixed) (who : ι)
    (replacement : M.MixedPolicy who)
    (replacementFallback : M.Policy who) :
    M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed) mixed who
          ((InformationModel.MixedPolicy.toBehavioralWith (M := M)
            replacement replacementFallback).toMixedWithin M (sites who)
            replacementFallback)) horizon target =
      M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed)
          mixed who replacement) horizon target := by
  rw [runMixed_update_eq_opponents_bind (M := M),
    runMixed_update_eq_opponents_bind (M := M), PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro opponents
  exact congrArg (fun weight : ENNReal =>
    (independentProduct fun other : {other // other ≠ who} =>
      mixed other.1) opponents * weight)
    (M.kuhn_mixed_roundTripWithinWith_against_pure_apply
      hrecall sites horizon target hqueried who replacement
      replacementFallback opponents)

omit [Fintype ι] in
private theorem toMixedWithin_update
    (sites : (i : ι) → Finset (M.InfoState i))
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who)
    (replacementFallback : M.Policy who) :
    (fun i =>
      ((Profile.update behavioral who replacement) i).toMixedWithin M (sites i)
        ((Profile.update fallback who replacementFallback) i)) =
      Profile.update (sig := M.strategicSignature.mixed)
        (fun i => (behavioral i).toMixedWithin M (sites i) (fallback i)) who
        (replacement.toMixedWithin M (sites who) replacementFallback) := by
  funext i
  by_cases hi : i = who
  · subst i
    rw [Profile.update_same, Profile.update_same, Profile.update_same]
  · rw [Profile.update_of_ne _ _ hi, Profile.update_of_ne _ _ hi,
      Profile.update_of_ne _ _ hi]

/-- A behavioral policy and its finite-site mixed round trip are
realization-equivalent under arbitrary fixed behavioral opponents. -/
theorem kuhn_behavioral_roundTrip_updateWithin
    (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i))
    (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who)
    (replacementFallback : M.Policy who) :
    M.runBehavioral
        (Profile.update behavioral who
          (InformationModel.MixedPolicy.toBehavioral
            (M := M) (replacement.toMixedWithin M (sites who) replacementFallback))) horizon =
      M.runBehavioral
        (Profile.update behavioral who replacement) horizon := by
  let replacementMixed : M.MixedPolicy who :=
    replacement.toMixedWithin M (sites who) replacementFallback
  let roundTrip : M.BehavioralPolicy who :=
    InformationModel.MixedPolicy.toBehavioral
      (M := M) replacementMixed
  let updatedFallback : Profile M.strategicSignature :=
    Profile.update fallback who replacementFallback
  have hleft := M.runMixed_toMixedWithin (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    sites (Profile.update behavioral who roundTrip) updatedFallback
      horizon hcover
  have hright := M.runMixed_toMixedWithin (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    sites (Profile.update behavioral who replacement) updatedFallback
      horizon hcover
  rw [toMixedWithin_update (M := M) sites behavioral fallback who
      roundTrip replacementFallback] at hleft
  rw [toMixedWithin_update (M := M) sites behavioral fallback who
      replacement replacementFallback] at hright
  have hlocal := M.kuhn_mixed_roundTrip_updateWithin hrecall sites horizon hcover
    (fun i => (behavioral i).toMixedWithin M (sites i) (fallback i)) who
      replacementMixed replacementFallback
  have hresult := hleft.symm.trans (hlocal.trans hright)
  simpa [replacementMixed, roundTrip] using hresult

/-- A behavioral policy and its finite-site predraw read with the same fixed
fallback are realization-equivalent under arbitrary fixed behavioral
opponents. -/
theorem kuhn_behavioral_roundTrip_updateWithinWith
    (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i))
    (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who)
    (replacementFallback : M.Policy who) :
    M.runBehavioral
        (Profile.update behavioral who
          (InformationModel.MixedPolicy.toBehavioralWith (M := M)
            (replacement.toMixedWithin M (sites who) replacementFallback)
            replacementFallback)) horizon =
      M.runBehavioral
        (Profile.update behavioral who replacement) horizon := by
  let replacementMixed : M.MixedPolicy who :=
    replacement.toMixedWithin M (sites who) replacementFallback
  let roundTrip : M.BehavioralPolicy who :=
    InformationModel.MixedPolicy.toBehavioralWith
      (M := M) replacementMixed replacementFallback
  let updatedFallback : Profile M.strategicSignature :=
    Profile.update fallback who replacementFallback
  have hleft := M.runMixed_toMixedWithin (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    sites (Profile.update behavioral who roundTrip) updatedFallback
      horizon hcover
  have hright := M.runMixed_toMixedWithin (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    sites (Profile.update behavioral who replacement) updatedFallback
      horizon hcover
  rw [toMixedWithin_update (M := M) sites behavioral fallback who
      roundTrip replacementFallback] at hleft
  rw [toMixedWithin_update (M := M) sites behavioral fallback who
      replacement replacementFallback] at hright
  have hlocal := M.kuhn_mixed_roundTrip_updateWithinWith
    hrecall sites horizon hcover
    (fun i => (behavioral i).toMixedWithin M (sites i) (fallback i)) who
      replacementMixed replacementFallback
  have hresult := hleft.symm.trans (hlocal.trans hright)
  simpa [replacementMixed, roundTrip] using hresult

/-- A finite-site behavioral round trip preserves one target mass when the
site family contains that target's queried coordinates. -/
theorem kuhn_behavioral_roundTrip_updateWithinWith_apply_of_queriedInfos
    (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i)) (horizon : ℕ)
    (target : E.History)
    (hqueried : ∀ i info, info ∈ M.queriedInfos i target.trace → info ∈ sites i)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who)
    (replacementFallback : M.Policy who) :
    M.runBehavioral
        (Profile.update behavioral who
          (InformationModel.MixedPolicy.toBehavioralWith (M := M)
            (replacement.toMixedWithin M (sites who) replacementFallback)
            replacementFallback)) horizon target =
      M.runBehavioral
        (Profile.update behavioral who replacement) horizon target := by
  let replacementMixed : M.MixedPolicy who :=
    replacement.toMixedWithin M (sites who) replacementFallback
  let roundTrip : M.BehavioralPolicy who :=
    InformationModel.MixedPolicy.toBehavioralWith
      (M := M) replacementMixed replacementFallback
  let updatedFallback : Profile M.strategicSignature :=
    Profile.update fallback who replacementFallback
  have hleft := M.runMixed_toMixedWithin_apply_of_queriedInfos
    (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    sites (Profile.update behavioral who roundTrip) updatedFallback
      horizon target hqueried
  have hright := M.runMixed_toMixedWithin_apply_of_queriedInfos
    (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    sites (Profile.update behavioral who replacement) updatedFallback
      horizon target hqueried
  rw [toMixedWithin_update (M := M) sites behavioral fallback who
      roundTrip replacementFallback] at hleft
  rw [toMixedWithin_update (M := M) sites behavioral fallback who
      replacement replacementFallback] at hright
  have hlocal := M.kuhn_mixed_roundTrip_updateWithinWith_apply_of_queriedInfos
    hrecall sites horizon target hqueried
    (fun i => (behavioral i).toMixedWithin M (sites i) (fallback i)) who
      replacementMixed replacementFallback
  have hresult := hleft.symm.trans (hlocal.trans hright)
  simpa [replacementMixed, roundTrip] using hresult

/-- Mixed opponents and a behavioral deviation agree at one target with the
finite mixed predraw when only that target's sites are sampled. -/
theorem kuhn_mixed_update_toBehavioralWithinWith_apply_of_queriedInfos
    (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i)) (horizon : ℕ)
    (target : E.History)
    (hqueried : ∀ i info, info ∈ M.queriedInfos i target.trace → info ∈ sites i)
    (mixed : Profile M.strategicSignature.mixed)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who)
    (replacementFallback : M.Policy who) :
    M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          (fun i => InformationModel.MixedPolicy.toBehavioralWith
            (M := M) (mixed i) (fallback i)) who replacement)
        horizon target =
      M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed)
          mixed who
            (replacement.toMixedWithin M (sites who) replacementFallback))
        horizon target := by
  let behavioral : Profile M.behavioralSignature :=
    fun i => InformationModel.MixedPolicy.toBehavioralWith
      (M := M) (mixed i) (fallback i)
  let replacementMixed : M.MixedPolicy who :=
    replacement.toMixedWithin M (sites who) replacementFallback
  let updatedFallback : Profile M.strategicSignature :=
    Profile.update fallback who replacementFallback
  have hback := congrArg (fun law : PMF E.History => law target)
    (M.runMixed_toBehavioralWith
      (InformationModel.constrainsAlike_of_perfectRecall hrecall)
      updatedFallback horizon
      (Profile.update (sig := M.strategicSignature.mixed)
        mixed who replacementMixed))
  have hprofile :
      (fun i => InformationModel.MixedPolicy.toBehavioralWith (M := M)
        ((Profile.update (sig := M.strategicSignature.mixed)
          mixed who replacementMixed) i) (updatedFallback i)) =
        Profile.update (sig := M.behavioralSignature) behavioral who
          (InformationModel.MixedPolicy.toBehavioralWith (M := M)
            replacementMixed replacementFallback) := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [updatedFallback]
    · simp [behavioral, updatedFallback, hi]
  rw [hprofile] at hback
  have hround := M.kuhn_behavioral_roundTrip_updateWithinWith_apply_of_queriedInfos
    hrecall sites horizon target hqueried behavioral fallback who replacement
      replacementFallback
  exact hround.symm.trans hback.symm

/-- Replacing one player's mixed policy by an arbitrary behavioral policy
commutes with a fixed-fallback behavioral reading of every nondeviator. -/
theorem kuhn_mixed_update_toBehavioralWithinWith
    (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i))
    (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon)
    (mixed : Profile M.strategicSignature.mixed)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.BehavioralPolicy who)
    (replacementFallback : M.Policy who) :
    M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          (fun i => InformationModel.MixedPolicy.toBehavioralWith
            (M := M) (mixed i) (fallback i))
          who replacement) horizon =
      M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed)
          mixed who (replacement.toMixedWithin M (sites who) replacementFallback)) horizon := by
  let behavioral : Profile M.behavioralSignature :=
    fun i => InformationModel.MixedPolicy.toBehavioralWith
      (M := M) (mixed i) (fallback i)
  let replacementMixed : M.MixedPolicy who :=
    replacement.toMixedWithin M (sites who) replacementFallback
  let updatedFallback : Profile M.strategicSignature :=
    Profile.update fallback who replacementFallback
  have hback := M.runMixed_toBehavioralWith
    (InformationModel.constrainsAlike_of_perfectRecall hrecall)
    updatedFallback horizon
    (Profile.update (sig := M.strategicSignature.mixed)
      mixed who replacementMixed)
  have hprofile :
      (fun i => InformationModel.MixedPolicy.toBehavioralWith (M := M)
        ((Profile.update
          (sig := M.strategicSignature.mixed) mixed who replacementMixed) i)
        (updatedFallback i)) =
        Profile.update (sig := M.behavioralSignature) behavioral who
          (InformationModel.MixedPolicy.toBehavioralWith (M := M)
            replacementMixed replacementFallback) := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [updatedFallback]
    · simp [behavioral, updatedFallback, hi]
  rw [hprofile] at hback
  have hround := M.kuhn_behavioral_roundTrip_updateWithinWith
    hrecall sites horizon hcover behavioral fallback who replacement
      replacementFallback
  exact hround.symm.trans hback.symm

/-- Starting from a behavioral profile, an arbitrary mixed deviation is read
with a caller-supplied zero-mass fallback while every nondeviator keeps its
original behavioral policy. -/
theorem kuhn_behavioral_update_toMixedWithinWith
    (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i))
    (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.MixedPolicy who)
    (replacementFallback : M.Policy who) :
    M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed)
          (fun i => (behavioral i).toMixedWithin M (sites i) (fallback i)) who
          replacement) horizon =
      M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          behavioral who
            (InformationModel.MixedPolicy.toBehavioralWith
              (M := M) replacement replacementFallback)) horizon := by
  let deviation : M.BehavioralPolicy who :=
    InformationModel.MixedPolicy.toBehavioralWith
      (M := M) replacement replacementFallback
  let baselineMixed : Profile M.strategicSignature.mixed :=
    fun i => (behavioral i).toMixedWithin M (sites i) (fallback i)
  let roundBehavioral : Profile M.behavioralSignature :=
    fun i => InformationModel.MixedPolicy.toBehavioralWith
      (M := M) (baselineMixed i) (fallback i)
  let deviationMixed : M.MixedPolicy who :=
    deviation.toMixedWithin M (sites who) replacementFallback
  let updatedFallback : Profile M.strategicSignature :=
    Profile.update fallback who replacementFallback
  have hforward := M.runMixed_toMixedWithin (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    sites (Profile.update behavioral who deviation) updatedFallback
      horizon hcover
  rw [toMixedWithin_update (M := M) sites behavioral fallback who
      deviation replacementFallback] at hforward
  have hbackBase := M.runMixed_toBehavioralWith
    (InformationModel.constrainsAlike_of_perfectRecall hrecall)
    updatedFallback horizon
    (Profile.update (sig := M.strategicSignature.mixed)
      baselineMixed who deviationMixed)
  have hbackBaseProfile :
      (fun i => InformationModel.MixedPolicy.toBehavioralWith (M := M)
        ((Profile.update (sig := M.strategicSignature.mixed)
          baselineMixed who deviationMixed) i) (updatedFallback i)) =
        Profile.update (sig := M.behavioralSignature) roundBehavioral who
          (InformationModel.MixedPolicy.toBehavioralWith
            (M := M) deviationMixed replacementFallback) := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [updatedFallback]
    · simp [roundBehavioral, updatedFallback, hi]
  rw [hbackBaseProfile] at hbackBase
  have hbaseToRound :
      M.runBehavioral (Profile.update behavioral who deviation) horizon =
        M.runBehavioral
          (Profile.update roundBehavioral who
            (InformationModel.MixedPolicy.toBehavioralWith
              (M := M) deviationMixed replacementFallback)) horizon :=
    hforward.symm.trans hbackBase
  have hplayer := M.kuhn_behavioral_roundTrip_updateWithinWith
    hrecall sites horizon hcover roundBehavioral fallback who deviation
      replacementFallback
  have hbaseToDeviation := hbaseToRound.trans hplayer
  have hbackDeviation := M.runMixed_toBehavioralWith
    (InformationModel.constrainsAlike_of_perfectRecall hrecall)
    updatedFallback horizon
    (Profile.update (sig := M.strategicSignature.mixed)
      baselineMixed who replacement)
  have hbackDeviationProfile :
      (fun i => InformationModel.MixedPolicy.toBehavioralWith (M := M)
        ((Profile.update (sig := M.strategicSignature.mixed)
          baselineMixed who replacement) i) (updatedFallback i)) =
        Profile.update (sig := M.behavioralSignature) roundBehavioral who
          deviation := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [deviation, updatedFallback]
    · simp [roundBehavioral, updatedFallback, hi]
  rw [hbackDeviationProfile] at hbackDeviation
  have hresult := hbackDeviation.trans hbaseToDeviation.symm
  simpa [deviation, baselineMixed, roundBehavioral, deviationMixed] using
    hresult

/-- A mixed deviation against behavioral opponents needs only the target's
queried sites in the opponents' finite predraw. -/
theorem kuhn_behavioral_update_toMixedWithinWith_apply_of_queriedInfos
    (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i)) (horizon : ℕ)
    (target : E.History)
    (hqueried : ∀ i info, info ∈ M.queriedInfos i target.trace → info ∈ sites i)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.MixedPolicy who)
    (replacementFallback : M.Policy who) :
    M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed)
          (fun i => (behavioral i).toMixedWithin M (sites i) (fallback i)) who
          replacement) horizon target =
      M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          behavioral who
            (InformationModel.MixedPolicy.toBehavioralWith
              (M := M) replacement replacementFallback)) horizon target := by
  let deviation : M.BehavioralPolicy who :=
    InformationModel.MixedPolicy.toBehavioralWith
      (M := M) replacement replacementFallback
  let baselineMixed : Profile M.strategicSignature.mixed :=
    fun i => (behavioral i).toMixedWithin M (sites i) (fallback i)
  let roundBehavioral : Profile M.behavioralSignature :=
    fun i => InformationModel.MixedPolicy.toBehavioralWith
      (M := M) (baselineMixed i) (fallback i)
  let deviationMixed : M.MixedPolicy who :=
    deviation.toMixedWithin M (sites who) replacementFallback
  let updatedFallback : Profile M.strategicSignature :=
    Profile.update fallback who replacementFallback
  have hforward := M.runMixed_toMixedWithin_apply_of_queriedInfos
    (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    sites (Profile.update behavioral who deviation) updatedFallback
      horizon target hqueried
  rw [toMixedWithin_update (M := M) sites behavioral fallback who
      deviation replacementFallback] at hforward
  have hbackBase := congrArg (fun law : PMF E.History => law target)
    (M.runMixed_toBehavioralWith
      (InformationModel.constrainsAlike_of_perfectRecall hrecall)
      updatedFallback horizon
      (Profile.update (sig := M.strategicSignature.mixed)
        baselineMixed who deviationMixed))
  have hbackBaseProfile :
      (fun i => InformationModel.MixedPolicy.toBehavioralWith (M := M)
        ((Profile.update (sig := M.strategicSignature.mixed)
          baselineMixed who deviationMixed) i) (updatedFallback i)) =
        Profile.update (sig := M.behavioralSignature) roundBehavioral who
          (InformationModel.MixedPolicy.toBehavioralWith
            (M := M) deviationMixed replacementFallback) := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [updatedFallback]
    · simp [roundBehavioral, updatedFallback, hi]
  rw [hbackBaseProfile] at hbackBase
  have hbaseToRound :
      M.runBehavioral (Profile.update behavioral who deviation)
          horizon target =
        M.runBehavioral
          (Profile.update roundBehavioral who
            (InformationModel.MixedPolicy.toBehavioralWith
              (M := M) deviationMixed replacementFallback))
          horizon target := hforward.symm.trans hbackBase
  have hplayer := M.kuhn_behavioral_roundTrip_updateWithinWith_apply_of_queriedInfos
    hrecall sites horizon target hqueried roundBehavioral fallback who
      deviation replacementFallback
  have hbaseToDeviation := hbaseToRound.trans hplayer
  have hbackDeviation := congrArg (fun law : PMF E.History => law target)
    (M.runMixed_toBehavioralWith
      (InformationModel.constrainsAlike_of_perfectRecall hrecall)
      updatedFallback horizon
      (Profile.update (sig := M.strategicSignature.mixed)
        baselineMixed who replacement))
  have hbackDeviationProfile :
      (fun i => InformationModel.MixedPolicy.toBehavioralWith (M := M)
        ((Profile.update (sig := M.strategicSignature.mixed)
          baselineMixed who replacement) i) (updatedFallback i)) =
        Profile.update (sig := M.behavioralSignature) roundBehavioral who
          deviation := by
    funext i
    by_cases hi : i = who
    · subst i
      simp [deviation, updatedFallback]
    · simp [roundBehavioral, updatedFallback, hi]
  rw [hbackDeviationProfile] at hbackDeviation
  have hresult := hbackDeviation.trans hbaseToDeviation.symm
  simpa [deviation, baselineMixed, roundBehavioral, deviationMixed] using
    hresult

/-- Replacing one player's mixed policy by an arbitrary behavioral policy
commutes with conditional behavioral reading when the finite sites cover every
counterfactual history through the horizon. -/
theorem kuhn_mixed_update_toBehavioralWithin
    (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i))
    (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon)
    (mixed : Profile M.strategicSignature.mixed) (who : ι)
    (replacement : M.BehavioralPolicy who)
    (replacementFallback : M.Policy who) :
    M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          (fun i => InformationModel.MixedPolicy.toBehavioral
            (M := M) (mixed i)) who replacement) horizon =
      M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed)
          mixed who (replacement.toMixedWithin M (sites who) replacementFallback)) horizon := by
  let behavioral : Profile M.behavioralSignature :=
    fun i => InformationModel.MixedPolicy.toBehavioral
      (M := M) (mixed i)
  let fallback : Profile M.strategicSignature :=
    fun i => (behavioral i).supportFallback
  have hback := M.runMixed_toBehavioral
    (InformationModel.constrainsAlike_of_perfectRecall hrecall) horizon
    (Profile.update mixed who
      (replacement.toMixedWithin M (sites who) replacementFallback))
  rw [toBehavioral_update (M := M) mixed who
    (replacement.toMixedWithin M (sites who) replacementFallback)] at hback
  have hround := M.kuhn_behavioral_roundTrip_updateWithin
    hrecall sites horizon hcover behavioral fallback who replacement
      replacementFallback
  exact hround.symm.trans hback.symm

/-- Starting from a behavioral profile, an arbitrary mixed deviation is
realized by its behavioral reading while every nondeviator keeps the bounded
finite-site mixed policy selected for the baseline profile. -/
theorem kuhn_behavioral_update_toMixedWithin (hrecall : M.PerfectRecall)
    (sites : (i : ι) → Finset (M.InfoState i))
    (horizon : ℕ)
    (hcover : M.CoversInformationSites sites horizon)
    (behavioral : Profile M.behavioralSignature)
    (fallback : Profile M.strategicSignature) (who : ι)
    (replacement : M.MixedPolicy who) :
    M.runMixed
        (Profile.update (sig := M.strategicSignature.mixed)
          (fun i => (behavioral i).toMixedWithin M (sites i) (fallback i)) who
          replacement) horizon =
      M.runBehavioral
        (Profile.update (sig := M.behavioralSignature)
          behavioral who
            (InformationModel.MixedPolicy.toBehavioral
              (M := M) replacement)) horizon := by
  let deviation : M.BehavioralPolicy who :=
    InformationModel.MixedPolicy.toBehavioral (M := M) replacement
  let deviationFallback : M.Policy who := deviation.supportFallback
  let baselineMixed : Profile M.strategicSignature.mixed :=
    fun i => (behavioral i).toMixedWithin M (sites i) (fallback i)
  let roundBehavioral : Profile M.behavioralSignature :=
    fun i => InformationModel.MixedPolicy.toBehavioral
      (M := M) (baselineMixed i)
  let updatedFallback : Profile M.strategicSignature :=
    Profile.update fallback who deviationFallback
  have hforward := M.runMixed_toMixedWithin (M.actsOnceWhereItMatters_of_perfectRecall hrecall)
    sites (Profile.update behavioral who deviation) updatedFallback
      horizon hcover
  rw [toMixedWithin_update (M := M) sites behavioral fallback who
      deviation deviationFallback] at hforward
  have hbackBase := M.runMixed_toBehavioral
    (InformationModel.constrainsAlike_of_perfectRecall hrecall) horizon
    (Profile.update (sig := M.strategicSignature.mixed)
      baselineMixed who
        (deviation.toMixedWithin M (sites who) deviationFallback))
  rw [toBehavioral_update (M := M) baselineMixed who
    (deviation.toMixedWithin M (sites who) deviationFallback)] at hbackBase
  have hbaseToRound :
      M.runBehavioral (Profile.update behavioral who deviation) horizon =
        M.runBehavioral
          (Profile.update roundBehavioral who
            (InformationModel.MixedPolicy.toBehavioral
              (M := M) (deviation.toMixedWithin M (sites who) deviationFallback))) horizon :=
    hforward.symm.trans hbackBase
  have hplayer := M.kuhn_behavioral_roundTrip_updateWithin
    hrecall sites horizon hcover roundBehavioral fallback who deviation
      deviationFallback
  have hbaseToDeviation := hbaseToRound.trans hplayer
  have hbackDeviation := M.runMixed_toBehavioral
    (InformationModel.constrainsAlike_of_perfectRecall hrecall) horizon
    (Profile.update (sig := M.strategicSignature.mixed)
      baselineMixed who replacement)
  rw [toBehavioral_update (M := M) baselineMixed who replacement]
    at hbackDeviation
  have hresult := hbackDeviation.trans hbaseToDeviation.symm
  simpa [deviation, baselineMixed, roundBehavioral] using hresult

end BoundedUnilateralRealization

end InformationModel

end GameTheory.Protocol
