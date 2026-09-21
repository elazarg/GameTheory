import GameTheory.Tests.UtilitySimulation

/-! # Direct and bundled utility-bound composition

The two candidates use identical source, middle and target games and the same
already proved per-layer utility bounds. Their only difference is whether the
composed bound is retained as reusable data or assembled at the transfer call.
Both prove the same coalition-equilibrium equivalence at every compiled source
profile, with the same arbitrary additive error.
-/

noncomputable section

namespace GameTheory.GameForm.MixtureSimulationOn.Tests.UtilityTransferComparison

def compileLayered (who : Unit) (strategy : source.sig.Strategy who) :
    target.sig.Strategy who :=
  secondUtility.compileStrategy who (firstUtility.compileStrategy who strategy)

-- Bundled candidate: a reusable composed certificate and its transfer consumer.
def bundled : UtilitySimulation source target
    (fun outcome player => booleanUtility (sourceObserve outcome) player)
    (fun outcome player => booleanUtility (targetObserve outcome) player)
    (singletonGroups Unit) :=
  firstUtility.trans secondUtility

theorem bundled_transfer (ε : ℝ) (profile : Profile source.sig) :
    IsεGroupNash target (fun outcome player => booleanUtility (targetObserve outcome) player)
        (singletonGroups Unit) ε (fun who => compileLayered who (profile who)) ↔
      IsεGroupNash source (fun outcome player => booleanUtility (sourceObserve outcome) player)
        (singletonGroups Unit) ε profile :=
  bundled.isεGroupNash_compileProfile_iff ε profile

theorem bundled_bound (profile : Profile source.sig) (replacement : target.sig.Strategy ()) :
    ∃ alternative : source.sig.Strategy (),
      expectedUtility (fun outcome player => booleanUtility (targetObserve outcome) player) ()
          (target.play (Profile.update (fun who => compileLayered who (profile who)) ()
            replacement)) ≤
        expectedUtility (fun outcome player => booleanUtility (sourceObserve outcome) player) ()
          (source.play (Profile.update profile () alternative)) :=
  bundled.unilateral_bound subset_rfl profile () replacement

-- Direct candidate: compose the same bounds at the theorem call.
theorem direct_transfer (ε : ℝ) (profile : Profile source.sig) :
    IsεGroupNash target (fun outcome player => booleanUtility (targetObserve outcome) player)
        (singletonGroups Unit) ε (fun who => compileLayered who (profile who)) ↔
      IsεGroupNash source (fun outcome player => booleanUtility (sourceObserve outcome) player)
        (singletonGroups Unit) ε profile := by
  apply isεGroupNash_compileProfile_iff_of_utility_bounds compileLayered ?_
    (singletonGroups Unit) profile ?_ ε
  · intro sourceProfile who
    exact (secondUtility.honest_utility (firstUtility.compileProfile sourceProfile) who).trans
      (firstUtility.honest_utility sourceProfile who)
  · intro members hmembers replacement
    obtain ⟨middleAlternative, hright⟩ :=
      secondUtility.deviation_bound members hmembers (firstUtility.compileProfile profile)
        replacement
    obtain ⟨sourceAlternative, hleft⟩ :=
      firstUtility.deviation_bound members hmembers profile middleAlternative
    exact ⟨sourceAlternative, fun member hmember =>
      (hright member hmember).trans (hleft member hmember)⟩

theorem direct_bound (profile : Profile source.sig) (replacement : target.sig.Strategy ()) :
    ∃ alternative : source.sig.Strategy (),
      expectedUtility (fun outcome player => booleanUtility (targetObserve outcome) player) ()
          (target.play (Profile.update (fun who => compileLayered who (profile who)) ()
            replacement)) ≤
        expectedUtility (fun outcome player => booleanUtility (sourceObserve outcome) player) ()
          (source.play (Profile.update profile () alternative)) := by
  obtain ⟨middleAlternative, hright⟩ :=
    secondUtility.unilateral_bound subset_rfl (firstUtility.compileProfile profile) () replacement
  obtain ⟨sourceAlternative, hleft⟩ :=
    firstUtility.unilateral_bound subset_rfl profile () middleAlternative
  exact ⟨sourceAlternative, hright.trans hleft⟩

end GameTheory.GameForm.MixtureSimulationOn.Tests.UtilityTransferComparison
