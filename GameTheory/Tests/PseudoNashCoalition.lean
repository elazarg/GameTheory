/-
# Single-party security does not carry strong pseudo-Nash

Adding a message channel from one player to the other to a coin-guessing game
changes no unilateral utility law, so compiling each guess into a constant
function is an exact `SecureImplementation`, for every class of tests. Yet the
coalition that sends the coin through the channel breaks every strong pseudo-Nash
equilibrium of the compiled game. Hence no class of tests comparing empirical
means admits a `CoalitionSecureImplementation` of the base game by the channel
game, whatever the compilation.
-/
import GameTheory.Analysis.PseudoNash
import GameTheory.Tests.CoalitionSimulation

noncomputable section

namespace GameTheory.Tests.PseudoNashCoalition

open Filter GameTheory GameTheory.Math GameTheory.Math.Probability
open GameTheory.GameForm.CoalitionWitness

open GameTheory.GameForm.CoalitionWitness

/-- The coin-guessing game, constant in the size. -/
abbrev baseFamily : ParameterizedGame (Fin 2) :=
  ParameterizedGame.constant baseGame matchUtility

/-- The same game with a message channel from player zero to player one. -/
abbrev channelFamily : ParameterizedGame (Fin 2) :=
  ParameterizedGame.constant channelGame matchUtility

private theorem channel_honest_play (profile : Profile baseGame.sig) :
    channelGame.play (Profile.map compileConstant profile) = baseGame.play profile := rfl

private theorem channel_update_play (profile : Profile baseGame.sig) (who : Fin 2)
    (replacement : channelGame.sig.Strategy who) :
    ∃ simulated : baseGame.sig.Strategy who,
      channelGame.play (Profile.update (Profile.map compileConstant profile) who replacement) =
        baseGame.play (Profile.update profile who simulated) := by
  fin_cases who
  · refine ⟨profile 0, ?_⟩
    simp [compileConstant, Profile.update_of_ne]
  · refine ⟨replacement (profile 0), ?_⟩
    simp [compileConstant, Profile.update_of_ne]

/-- Compiling a guess into a constant function is an exact single-party
simulation, for every class of tests. -/
def channelSimulation (tests : Set (SampleTest ℝ)) :
    SecureImplementation tests baseFamily channelFamily where
  compile := compileConstant
  honest profile who := by
    have : channelFamily.utilityLaw who (Profile.map compileConstant profile) =
        baseFamily.utilityLaw who profile := by
      funext κ
      exact congrArg (PMF.map _) (channel_honest_play profile)
    rw [this]
    exact IndistinguishableBy.refl _ _
  simulate profile who replacement := by
    obtain ⟨simulated, hplay⟩ := channel_update_play profile who replacement
    refine ⟨simulated, ?_⟩
    have : channelFamily.utilityLaw who
        (Profile.update (Profile.map compileConstant profile) who replacement) =
          baseFamily.utilityLaw who (Profile.update profile who simulated) := by
      funext κ
      exact congrArg (PMF.map _) hplay
    rw [this]
    exact IndistinguishableBy.refl _ _

private theorem matchUtility_bounded : ∀ who, ∃ C, ∀ outcome, |matchUtility outcome who| ≤ C :=
  fun _ => ⟨1, fun outcome => by simp [matchUtility]; split_ifs <;> norm_num⟩

/-- **Perfect single-party security does not carry strong pseudo-Nash.** Every
base profile is strong pseudo-Nash; its exact single-party compilation into the
channel game is not. -/
theorem channel_breaks_strongPseudoNash (tests : Set (SampleTest ℝ))
    (profile : Profile baseGame.sig) :
    baseFamily.IsStrongPseudoNash profile ∧
      ¬ channelFamily.IsStrongPseudoNash
        (Profile.map (channelSimulation tests).compile profile) := by
  have hpref := empiricalMeanPreference_eq_euPreference matchUtility matchUtility_bounded
  constructor
  · rw [ParameterizedGame.isStrongPseudoNash_constant_iff, hpref]
    exact base_isStrongNash profile
  · rw [ParameterizedGame.isStrongPseudoNash_constant_iff, hpref]
    exact compiled_not_isStrongNash profile

private theorem abs_le_one_of_mem_support_match {law : PMF (Bool × Bool)} (who : Fin 2) :
    ∀ x ∈ (law.map fun outcome => matchUtility outcome who).support, |x| ≤ 1 := by
  intro x hx
  rw [PMF.mem_support_map_iff] at hx
  obtain ⟨outcome, _, rfl⟩ := hx
  simp only [matchUtility]
  split_ifs <;> norm_num

private theorem lawMean_match (law : PMF (Bool × Bool)) (who : Fin 2) :
    lawMean (law.map fun outcome => matchUtility outcome who) =
      expectedUtility matchUtility who law := by
  rw [lawMean, expect_map]
  rfl

/-- Hence no class of tests that compares empirical means with utility
ensembles admits a coalition-secure implementation of the base game by the
channel game, whatever the compilation. -/
theorem isEmpty_coalitionSecureImplementation (tests : Set (SampleTest ℝ))
    (hreal : ∀ who profile, ContainsMeanTests tests (channelFamily.utilityLaw who profile))
    (hideal : ∀ who profile, ContainsMeanTests tests (baseFamily.utilityLaw who profile)) :
    IsEmpty (CoalitionSecureImplementation tests baseFamily channelFamily) := by
  refine ⟨fun impl => ?_⟩
  let profile : Profile baseGame.sig := fun _ => false
  let compiled := Profile.map impl.compile profile
  let copying := Profile.override Finset.univ (fun i => copyProfile i.1) compiled
  have htransfer := impl.isStrongPseudoNash hreal hideal
    (channel_breaks_strongPseudoNash tests profile).1
  rw [ParameterizedGame.IsStrongPseudoNash, isStrongNash_iff] at htransfer
  obtain ⟨member, _, hprefer⟩ :=
    htransfer Finset.univ Finset.univ_nonempty (fun i => copyProfile i.1)
  -- the grand coalition's deviation against the compiled profile
  have hdominates : ComputationallyMeanDominates (channelFamily.utilityLaw member compiled)
      (channelFamily.utilityLaw member copying) :=
    (meanDominancePreference_pure _ _ _ _).mp hprefer
  -- honest simulation replaces the compiled utility by the base utility
  have hhonest := (impl.honest profile member).meanTestIndistinguishable
    (hreal member copying)
  have hbase : ComputationallyMeanDominates (baseFamily.utilityLaw member profile)
      (channelFamily.utilityLaw member copying) :=
    (ComputationallyMeanDominates.congr_left hhonest).mp hdominates
  have hconst := (computationallyMeanDominates_const_iff (R := 1)
    (X := (baseGame.play profile).map fun outcome => matchUtility outcome member)
    (Y := (channelGame.play copying).map fun outcome => matchUtility outcome member)
    (abs_le_one_of_mem_support_match member) (abs_le_one_of_mem_support_match member)).mp hbase
  rw [lawMean_match, lawMean_match, base_expect profile member] at hconst
  have hcopy : expectedUtility matchUtility member (channelGame.play copying) = 1 := by
    have hlaw : channelGame.play copying = channelGame.play copyProfile := by
      simp only [copying, override_copyProfile]
    rw [expectedUtility_congr_law matchUtility member hlaw, copyProfile_expect member]
  rw [hcopy] at hconst
  norm_num at hconst

end GameTheory.Tests.PseudoNashCoalition
