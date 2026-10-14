module

/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

public import GameTheory.Analysis.Protocol.BeliefTransport
public import GameTheory.Math.Probability.ConditionalObservation

@[expose] public section

/-! # Bayes beliefs from actual passage through an information site

A terminal history retains the unique ancestor at an information antichain.
Conditioning that actual ancestor law on passage gives the standard Bayes
belief, even when the site's histories occur at different depths.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type*} {E : ExecutionProtocol Player} (M : InformationModel E)

open Classical in
/-- The information history encountered by a complete continuation, when one
exists. Antichain uniqueness makes the choice irrelevant in the passage laws. -/
def InformationSite.ancestor? {who : Player} (site : M.InformationSite who)
    (final : E.History) : Option (M.InformationHistory who site.1) :=
  if encountered : ∃ prior : M.InformationHistory who site.1,
      E.HistoryReaches prior.1 final then some encountered.choose else none

theorem InformationSite.ancestor?_eq_some_iff {who : Player}
    (site : M.InformationSite who) (antichain : site.IsHistoryAntichain)
    (final : E.History) (prior : M.InformationHistory who site.1) :
    site.ancestor? M final = some prior ↔ E.HistoryReaches prior.1 final := by
  classical
  unfold InformationSite.ancestor?
  split
  · rename_i encountered
    constructor
    · intro equal
      have reached := encountered.choose_spec
      rw [Option.some.inj equal] at reached
      exact reached
    · intro reached
      obtain ⟨firstFuel, first⟩ := encountered.choose_spec
      obtain ⟨secondFuel, second⟩ := reached
      exact congrArg some (site.eq_of_common_descendant M antichain
        encountered.choose prior final first second)
  · rename_i absent
    constructor
    · intro equal
      cases equal
    · intro reached
      exact False.elim (absent ⟨prior, reached⟩)

variable [E.FiniteMovers]

/-- Actual terminal passage assigns each encountered information history its
true reach weight. No common depth or supplied stopping law is required. -/
theorem InformationSite.terminal_ancestor_apply {who : Player}
    (site : M.InformationSite who) (antichain : site.IsHistoryAntichain)
    (certificate : E.WellFoundedHistories)
    (strategy : ∀ player, M.BehavioralPolicy player)
    (prior : M.InformationHistory who site.1) :
    ((M.runBehavioralTerminalFrom certificate strategy E.initHistory).map
      (site.ancestor? M)) (some prior) = M.historyReachWeight strategy prior.1 := by
  classical
  let terminal := M.runBehavioralTerminalFrom certificate strategy E.initHistory
  have same : {final : E.History | site.ancestor? M final = some prior} =
      {final | E.HistoryReaches prior.1 final} := by
    ext final
    exact site.ancestor?_eq_some_iff M antichain final prior
  calc
    (terminal.map (site.ancestor? M)) (some prior) =
        terminal.toOuterMeasure {final | site.ancestor? M final = some prior} := by
      rw [PMF.map_apply, PMF.toOuterMeasure_apply]
      apply tsum_congr
      intro final
      by_cases selected : site.ancestor? M final = some prior <;>
        simp [Set.indicator, eq_comm, selected]
    _ = terminal.toOuterMeasure {final | E.HistoryReaches prior.1 final} := by rw [same]
    _ = _ := M.coneMass_eq_historyReachWeight certificate strategy prior.1

/-- The actual ancestor law's passage probability is the full information
mass, with every variable-depth information history counted exactly once. -/
theorem InformationSite.terminal_ancestor_passage {who : Player}
    (site : M.InformationSite who) (antichain : site.IsHistoryAntichain)
    (certificate : E.WellFoundedHistories)
    (strategy : ∀ player, M.BehavioralPolicy player) :
    (((M.runBehavioralTerminalFrom certificate strategy E.initHistory).map
      (site.ancestor? M)).map Option.isSome) true =
        M.informationMass strategy who site := by
  classical
  rw [PMF.map_apply, ← (Equiv.optionEquivSumPUnit.{0} _).symm.tsum_eq,
    Summable.tsum_sum ENNReal.summable ENNReal.summable]
  simp only [Equiv.optionEquivSumPUnit_symm_inl, Equiv.optionEquivSumPUnit_symm_inr]
  simp only [Option.isSome_none, Bool.true_eq_false, ↓reduceIte,
    Option.isSome_some, tsum_zero, add_zero]
  unfold informationMass
  exact tsum_congr fun prior => site.terminal_ancestor_apply M antichain certificate strategy prior

/-- Standard Bayes beliefs are the actual encountered-ancestor law conditioned
on passage. The information site's histories may occur at different depths. -/
theorem InformationSite.bayesBelief_eq_conditional_ancestor {who : Player}
    (site : M.InformationSite who) (antichain : site.IsHistoryAntichain)
    (certificate : E.WellFoundedHistories)
    (strategy : ∀ player, M.BehavioralPolicy player)
    (positive : 0 < M.informationMass strategy who site) :
    (M.bayesBelief strategy who site antichain positive).map some =
      fiberPosterior ((M.runBehavioralTerminalFrom certificate strategy E.initHistory).map
        (site.ancestor? M)) Option.isSome true := by
  classical
  let encountered := (M.runBehavioralTerminalFrom certificate strategy E.initHistory).map
    (site.ancestor? M)
  have mass : (encountered.map Option.isSome) true =
      M.informationMass strategy who site :=
    site.terminal_ancestor_passage M antichain certificate strategy
  have present : true ∈ (encountered.map Option.isSome).support := by
    rw [PMF.mem_support_iff, mass]
    exact positive.ne'
  ext selected
  rw [fiberPosterior_apply encountered Option.isSome true present, mass]
  cases selected with
  | none =>
      simp only [Set.indicator, Set.mem_ofPred_eq, Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte, zero_mul]
      apply (PMF.apply_eq_zero_iff _ _).mpr
      rw [PMF.support_map]
      rintro ⟨prior, _supported, impossible⟩
      cases impossible
  | some prior =>
      rw [pmf_map_apply_of_injective _ (Option.some_injective _) prior,
        M.bayesBelief_apply strategy who site antichain positive prior]
      simp only [Set.indicator, Set.mem_ofPred_eq, Option.isSome_some, ↓reduceIte]
      rw [site.terminal_ancestor_apply M antichain certificate strategy prior,
        div_eq_mul_inv]

/-- Applying the same stochastic readout to an encountered information history
commutes with conditioning on genuine passage. In particular, an auxiliary
memory lottery is sampled from the actual earlier history, not the final state. -/
theorem InformationSite.bayesBelief_bind_eq_conditional_passage {Result : Type*}
    {who : Player} (site : M.InformationSite who)
    (antichain : site.IsHistoryAntichain) (certificate : E.WellFoundedHistories)
    (strategy : ∀ player, M.BehavioralPolicy player)
    (positive : 0 < M.informationMass strategy who site)
    (readout : M.InformationHistory who site.1 → PMF Result) :
    ((M.bayesBelief strategy who site antichain positive).bind readout).map some =
      fiberPosterior
        ((M.runBehavioralTerminalFrom certificate strategy E.initHistory).bind fun final =>
          match site.ancestor? M final with
          | none => PMF.pure none
          | some prior => (readout prior).map some) Option.isSome true := by
  classical
  let terminal := M.runBehavioralTerminalFrom certificate strategy E.initHistory
  let encountered := terminal.map (site.ancestor? M)
  let lifted : Option (M.InformationHistory who site.1) → PMF (Option Result)
    | none => PMF.pure none
    | some prior => (readout prior).map some
  have present : true ∈ (encountered.map Option.isSome).support := by
    rw [PMF.mem_support_iff,
      site.terminal_ancestor_passage M antichain certificate strategy]
    exact positive.ne'
  have retained : ∀ prior ∈ encountered.support,
      ∀ result ∈ (lifted prior).support, result.isSome = prior.isSome := by
    intro prior _supported result possible
    cases prior with
    | none =>
        cases (PMF.mem_support_pure_iff _ _).mp possible
        rfl
    | some prior =>
        obtain ⟨value, _chosen, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp possible
        rfl
  have conditioned := fiberPosterior_bind_of_observation encountered lifted
    Option.isSome Option.isSome retained true present
  calc
    _ = ((M.bayesBelief strategy who site antichain positive).map some).bind lifted := by
      simp only [PMF.map_bind, PMF.bind_map, Function.comp_def, lifted]
    _ = (fiberPosterior encountered Option.isSome true).bind lifted := by
      rw [site.bayesBelief_eq_conditional_ancestor M antichain certificate strategy positive]
    _ = fiberPosterior (encountered.bind lifted) Option.isSome true := conditioned.symm
    _ = _ := by
      simp only [encountered, PMF.bind_map, Function.comp_def, lifted, terminal]
      rfl

end GameTheory.Protocol.InformationModel
