/-
# Coalitions and strong pseudo-Nash

A strong pseudo-Nash equilibrium is one that no coalition can deviate from so
that every member's utility ensemble computationally mean-dominates its own.
Transferring it from an ideal game to a real one needs a simulation of joint
deviations: a `CoalitionSecureImplementation` covers each joint deviation of a
coalition by one ideal joint deviation that serves every member at once, which
is security against jointly corrupted parties. It restricts to a
`SecureImplementation` on one-member coalitions.

The converse fails: security against single parties, even perfect, does not
carry strong pseudo-Nash, since a channel that only a coalition can exploit
changes no unilateral utility law.
-/
import GameTheory.Core.PseudoNash

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι} [DecidableEq ι]

/-- No coalition can deviate so that every member's utility ensemble
computationally mean-dominates its own. -/
abbrev ParameterizedGame.IsStrongPseudoNash (G : ParameterizedGame.{uι, us, uo} ι)
    (profile : Profile G.sig) : Prop :=
  IsStrongNash G.ensembleForm (meanDominancePreference G.utility) profile

/-- A compilation whose joint deviations of every coalition are simulated,
member by member, by one ideal joint deviation. -/
structure CoalitionSecureImplementation (tests : Set (SampleTest ℝ))
    (ideal real : ParameterizedGame.{uι, us, uo} ι) where
  /-- The real strategy running each ideal strategy on the implementation. -/
  compile : ∀ who, ideal.sig.Strategy who → real.sig.Strategy who
  honest : ∀ (profile : Profile ideal.sig) who,
    IndistinguishableBy tests (real.utilityLaw who (Profile.map compile profile))
      (ideal.utilityLaw who profile)
  simulate : ∀ (profile : Profile ideal.sig) (coalition : Finset ι)
      (replacement : Subprofile real.sig coalition),
    ∃ simulated : Subprofile ideal.sig coalition, ∀ member ∈ coalition,
      IndistinguishableBy tests
        (real.utilityLaw member
          (Profile.override coalition replacement (Profile.map compile profile)))
        (ideal.utilityLaw member (Profile.override coalition simulated profile))

/-- A coalition-secure implementation is secure against single parties: each
unilateral deviation is the deviation of a one-member coalition. -/
def CoalitionSecureImplementation.toSecureImplementation {tests : Set (SampleTest ℝ)}
    {ideal real : ParameterizedGame.{uι, us, uo} ι}
    (impl : CoalitionSecureImplementation tests ideal real) :
    SecureImplementation tests ideal real where
  compile := impl.compile
  honest := impl.honest
  simulate profile who deviation := by
    obtain ⟨simulated, hsimulated⟩ :=
      impl.simulate profile {who} (Subprofile.single who deviation)
    refine ⟨simulated ⟨who, Finset.mem_singleton_self who⟩, ?_⟩
    have := hsimulated who (Finset.mem_singleton_self who)
    rwa [Profile.override_single, Profile.override_singleton] at this

/-- **Coalition security carries strong pseudo-Nash.** -/
theorem CoalitionSecureImplementation.isStrongPseudoNash {tests : Set (SampleTest ℝ)}
    {ideal real : ParameterizedGame.{uι, us, uo} ι}
    (impl : CoalitionSecureImplementation tests ideal real)
    (hreal : ∀ who profile, ContainsMeanTests tests (real.utilityLaw who profile))
    (hideal : ∀ who profile, ContainsMeanTests tests (ideal.utilityLaw who profile))
    {profile : Profile ideal.sig} (h : ideal.IsStrongPseudoNash profile) :
    real.IsStrongPseudoNash (Profile.map impl.compile profile) := by
  refine IsStrongNash.of_coverage (fun coalition _ replacement => ?_) h
  obtain ⟨simulated, hsimulated⟩ := impl.simulate profile coalition replacement
  refine ⟨simulated, fun member hmember hsource => ?_⟩
  have hdominates : ComputationallyMeanDominates (ideal.utilityLaw member profile)
      (ideal.utilityLaw member (Profile.override coalition simulated profile)) :=
    (meanDominancePreference_pure _ _ _ _).mp hsource
  have hhonest := (impl.honest profile member).meanTestIndistinguishable
    (hideal member (Profile.override coalition simulated profile))
  have hdeviation := (hsimulated member hmember).meanTestIndistinguishable
    (hreal member (Profile.map impl.compile profile))
  exact (meanDominancePreference_pure _ _ _ _).mpr
    ((ComputationallyMeanDominates.congr_right hdeviation).mpr
      ((ComputationallyMeanDominates.congr_left hhonest).mpr hdominates))

/-- In a fixed game, strong pseudo-Nash is strong Nash for the empirical-mean
preference. -/
theorem ParameterizedGame.isStrongPseudoNash_constant_iff (F : GameForm.{uι, us, uo} ι)
    (utility : F.sig.Outcome → ι → ℝ) (profile : Profile F.sig) :
    (ParameterizedGame.constant F utility).IsStrongPseudoNash profile ↔
      IsStrongNash F (empiricalMeanPreference utility) profile := by
  rw [ParameterizedGame.IsStrongPseudoNash, isStrongNash_iff, isStrongNash_iff]
  exact forall_congr' fun coalition => forall_congr' fun _ => forall_congr' fun replacement =>
    exists_congr fun member => and_congr_right fun _ =>
      (meanDominancePreference_pure _ _ _ _).trans (empiricalMeanPreference_apply _ _ _ _).symm

end GameTheory
