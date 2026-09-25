import GameTheory.Tests.UtilitySimulation

/-! # Direct and bundled utility-bound composition -/

noncomputable section

namespace GameTheory.GameForm.MixtureSimulationOn.Tests.UtilityTransferComparison

open GameTheory.Math.Probability

def compileLayered (who : Unit) (strategy : source.sig.Strategy who) :
    target.sig.Strategy who :=
  secondUtility.compileStrategy who (firstUtility.compileStrategy who strategy)

/-- Bundled candidate: reusable composition and its transfer consumer. -/
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
      ∀ hsource : UtilityIntegrable
          (fun outcome player => booleanUtility (sourceObserve outcome) player) ()
          (source.play (Profile.update profile () alternative)),
        ∃ htarget : UtilityIntegrable
            (fun outcome player => booleanUtility (targetObserve outcome) player) ()
            (target.play (Profile.update
              (bundled.compileProfile profile) () replacement)),
          expectedUtility
              (fun outcome player => booleanUtility (targetObserve outcome) player) ()
              (target.play (Profile.update
                (bundled.compileProfile profile) () replacement)) htarget ≤
            expectedUtility
              (fun outcome player => booleanUtility (sourceObserve outcome) player) ()
              (source.play (Profile.update profile () alternative)) hsource :=
  bundled.unilateral_bound subset_rfl profile () replacement

/-- Direct candidate: compose the same guarded bounds at the theorem call. -/
theorem direct_transfer (ε : ℝ) (profile : Profile source.sig) :
    IsεGroupNash target (fun outcome player => booleanUtility (targetObserve outcome) player)
        (singletonGroups Unit) ε (fun who => compileLayered who (profile who)) ↔
      IsεGroupNash source (fun outcome player => booleanUtility (sourceObserve outcome) player)
        (singletonGroups Unit) ε profile := by
  apply isεGroupNash_compileProfile_iff_of_utility_bounds compileLayered ?_ ?_
    (singletonGroups Unit) profile ?_ ε
  · intro sourceProfile who
    exact (secondUtility.honest_integrable (firstUtility.compileProfile sourceProfile) who).trans
      (firstUtility.honest_integrable sourceProfile who)
  · intro sourceProfile who htarget hsource
    have hmiddle := (firstUtility.honest_integrable sourceProfile who).mpr hsource
    exact (secondUtility.honest_utility
      (firstUtility.compileProfile sourceProfile) who htarget hmiddle).trans
      (firstUtility.honest_utility sourceProfile who hmiddle hsource)
  · intro members hmembers replacement
    obtain ⟨middleAlternative, hright⟩ :=
      secondUtility.deviation_bound members hmembers (firstUtility.compileProfile profile)
        replacement
    obtain ⟨sourceAlternative, hleft⟩ :=
      firstUtility.deviation_bound members hmembers profile middleAlternative
    refine ⟨sourceAlternative, ?_⟩
    intro member hmember hsource
    obtain ⟨hmiddle, hleLeft⟩ := hleft member hmember hsource
    obtain ⟨htarget, hleRight⟩ := hright member hmember hmiddle
    exact ⟨htarget, hleRight.trans hleLeft⟩

theorem direct_bound (profile : Profile source.sig) (replacement : target.sig.Strategy ()) :
    ∃ alternative : source.sig.Strategy (),
      ∀ hsource : UtilityIntegrable
          (fun outcome player => booleanUtility (sourceObserve outcome) player) ()
          (source.play (Profile.update profile () alternative)),
        ∃ htarget : UtilityIntegrable
            (fun outcome player => booleanUtility (targetObserve outcome) player) ()
            (target.play (Profile.update
              (fun who => compileLayered who (profile who)) () replacement)),
          expectedUtility
              (fun outcome player => booleanUtility (targetObserve outcome) player) ()
              (target.play (Profile.update
                (fun who => compileLayered who (profile who)) () replacement)) htarget ≤
            expectedUtility
              (fun outcome player => booleanUtility (sourceObserve outcome) player) ()
              (source.play (Profile.update profile () alternative)) hsource := by
  obtain ⟨middleAlternative, hright⟩ :=
    secondUtility.unilateral_bound subset_rfl
      (firstUtility.compileProfile profile) () replacement
  obtain ⟨sourceAlternative, hleft⟩ :=
    firstUtility.unilateral_bound subset_rfl profile () middleAlternative
  refine ⟨sourceAlternative, ?_⟩
  intro hsource
  obtain ⟨hmiddle, hleLeft⟩ := hleft hsource
  obtain ⟨htarget, hleRight⟩ := hright hmiddle
  exact ⟨htarget, hleRight.trans hleLeft⟩

end GameTheory.GameForm.MixtureSimulationOn.Tests.UtilityTransferComparison
