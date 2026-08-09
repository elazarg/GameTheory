/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Fixed-target terminal semantics for finite quitting games

This file gives the game-generic semantic specification of accepting or
rejecting one fixed payoff target.  It belongs to the terminal target-selection
layer: none of its definitions depends on projective packets, charts, or
Farkas data.

A target is accepted when, at every positive accuracy, one literal terminal
approximate-Nash profile also delivers terminal payoff close to that same
target.  This is equivalent to the target itself being a uniform-equilibrium
payoff.  Negating the quantified terminal statement yields a positive scale at
which every terminal approximate equilibrium is separated from the target in
some coordinate.

The target-free existence equivalence in `TerminalUniformPayoffSelection`
asserts only that terminal approximate equilibria at every accuracy select
some uniform payoff, possibly after compact subsequence extraction.  The extra
payoff-delivery clause here identifies one prescribed target and therefore
supports rejection of a proposed target without denying equilibrium elsewhere.

The resulting acceptance-or-rejection theorem is a classical semantic
alternative, not a computable decision procedure and not a producer from more
primitive game data.  The optional retargeting adapter below assumes
target-free uniform-payoff existence explicitly; it does not establish that
existence or construct a retarget from a rejection witness.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A fixed-target terminal acceptance certificate.  At every positive
accuracy it supplies one repository-native terminal approximate-Nash profile
whose literal terminal payoff is close to the same declared target. -/
structure QuittingTerminalTargetAcceptanceCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) where
  terminalProfile : ∀ ε : ℝ, 0 < ε →
    ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) ε profile ∧
      ∀ who,
        |quittingTerminalPayoff reward profile who - target who| < ε

/-- A fixed-target terminal acceptance certificate compiles to the exact
declared uniform-equilibrium payoff. -/
theorem QuittingTerminalTargetAcceptanceCertificate.isUniformEquilibriumPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : Payoff ι}
    (certificate : QuittingTerminalTargetAcceptanceCertificate reward target) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by
    linarith
  obtain ⟨profile, hterminalNash, htarget⟩ :=
    certificate.terminalProfile (ε / 2) hhalf
  have huniform : (quittingGame reward).IsUniformεEquilibrium
      none ε profile :=
    quittingGame_isUniformεEquilibrium_of_terminalNash_finite
      reward profile (by linarith) hterminalNash
  obtain ⟨nashThreshold, hnashThreshold⟩ := huniform
  have heventuallyDelivery : ∀ᶠ horizon : ℕ in atTop, ∀ who,
      |(quittingGame reward).finiteAveragePayoff none horizon profile who -
        quittingTerminalPayoff reward profile who| < ε / 2 := by
    apply Filter.eventually_all.mpr
    intro who
    have hball :=
      (tendsto_finiteAveragePayoff_quittingGame reward profile who).eventually
        (Metric.ball_mem_nhds
          (quittingTerminalPayoff reward profile who) hhalf)
    filter_upwards [hball] with horizon hhorizon
    simpa only [Metric.mem_ball, Real.dist_eq] using hhorizon
  obtain ⟨deliveryThreshold, hdeliveryThreshold⟩ :=
    Filter.eventually_atTop.1 heventuallyDelivery
  refine ⟨profile, max nashThreshold deliveryThreshold,
    fun horizon hhorizon => ?_⟩
  constructor
  · exact hnashThreshold horizon
      (le_trans (Nat.le_max_left _ _) hhorizon)
  · intro who
    have hdelivery := hdeliveryThreshold horizon
      (le_trans (Nat.le_max_right _ _) hhorizon) who
    calc
      |(quittingGame reward).finiteAveragePayoff none horizon profile who -
          target who| =
        |((quittingGame reward).finiteAveragePayoff none horizon profile who -
            quittingTerminalPayoff reward profile who) +
          (quittingTerminalPayoff reward profile who - target who)| := by
            ring_nf
      _ ≤ |(quittingGame reward).finiteAveragePayoff none horizon profile who -
            quittingTerminalPayoff reward profile who| +
          |quittingTerminalPayoff reward profile who - target who| :=
        abs_add_le _ _
      _ ≤ ε := by
        linarith [htarget who]

/-- Terminal approximate equilibria whose terminal payoffs converge uniformly
to one prescribed target make that target a uniform-equilibrium payoff.  This
is the direct fixed-target form of terminal-to-uniform selection. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (target : Payoff ι)
    (hterminal : ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile ∧
        ∀ who, |quittingTerminalPayoff reward profile who - target who| ≤ ε) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  apply QuittingTerminalTargetAcceptanceCertificate.isUniformEquilibriumPayoff
  refine { terminalProfile := ?_ }
  intro ε hε
  obtain ⟨profile, hnash, hclose⟩ := hterminal (ε / 2) (by linarith)
  exact ⟨profile, hnash.mono (by linarith), fun who => by
    have := hclose who
    linarith⟩

/-- Terminal approximate equilibria which deliver one exact terminal target at
every error make that target a uniform-equilibrium payoff. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_fixedTarget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (target : Payoff ι)
    (hterminal : ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile ∧
        quittingTerminalPayoff reward profile = target) :
    (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_approxTarget
  intro ε hε
  obtain ⟨profile, hnash, htarget⟩ := hterminal ε hε
  refine ⟨profile, hnash, fun who => ?_⟩
  rw [congrFun htarget who, sub_self, abs_zero]
  exact hε.le

/-- Every exact uniform-equilibrium target supplies a fixed-target terminal
acceptance certificate. -/
theorem exists_quittingTerminalTargetAcceptanceCertificate_of_isUniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι)
    (huniform : (quittingGame reward).IsUniformEquilibriumPayoff none target) :
    Nonempty (QuittingTerminalTargetAcceptanceCertificate reward target) := by
  classical
  refine ⟨{ terminalProfile := ?_ }⟩
  intro ε hε
  have hhalf : 0 < ε / 2 := by
    linarith
  obtain ⟨profile, threshold, hprofile⟩ := huniform (ε / 2) hhalf
  have huniformProfile : (quittingGame reward).IsUniformεEquilibrium
      none (ε / 2) profile :=
    ⟨threshold, fun horizon hhorizon => (hprofile horizon hhorizon).1⟩
  have hterminalNashHalf : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (ε / 2) profile :=
    (quittingGame reward).isεAsymptoticNash_of_isUniformεEquilibrium
      none (quittingTerminalPayoff reward) huniformProfile
      (fun selectedProfile who =>
        tendsto_finiteAveragePayoff_quittingGame
          reward selectedProfile who)
  have hterminalNash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile :=
    hterminalNashHalf.mono (by linarith)
  have hclose : ∀ who,
      |quittingTerminalPayoff reward profile who - target who| < ε := by
    intro who
    have hlimit := tendsto_finiteAveragePayoff_quittingGame
      reward profile who
    have hupperLimit : Tendsto
        (fun horizon =>
          (quittingGame reward).finiteAveragePayoff none horizon profile who -
            target who)
        atTop
        (nhds (quittingTerminalPayoff reward profile who - target who)) :=
      hlimit.sub tendsto_const_nhds
    have hlowerLimit : Tendsto
        (fun horizon =>
          target who -
            (quittingGame reward).finiteAveragePayoff none horizon profile who)
        atTop
        (nhds (target who - quittingTerminalPayoff reward profile who)) :=
      tendsto_const_nhds.sub hlimit
    have hupper :
        quittingTerminalPayoff reward profile who - target who ≤ ε / 2 := by
      apply le_of_tendsto hupperLimit
      filter_upwards [eventually_ge_atTop threshold] with horizon hhorizon
      exact (abs_le.mp ((hprofile horizon hhorizon).2 who)).2
    have hlower :
        target who - quittingTerminalPayoff reward profile who ≤ ε / 2 := by
      apply le_of_tendsto hlowerLimit
      filter_upwards [eventually_ge_atTop threshold] with horizon hhorizon
      have hbound := (abs_le.mp ((hprofile horizon hhorizon).2 who)).1
      linarith
    exact abs_lt.2 ⟨by linarith, by linarith⟩
  exact ⟨profile, hterminalNash, hclose⟩

/-- Exact fixed-target terminal semantics: a target has an acceptance
certificate exactly when that same target is a uniform-equilibrium payoff. -/
theorem nonempty_quittingTerminalTargetAcceptanceCertificate_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    Nonempty (QuittingTerminalTargetAcceptanceCertificate reward target) ↔
      (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  constructor
  · rintro ⟨certificate⟩
    exact certificate.isUniformEquilibriumPayoff
  · exact
      exists_quittingTerminalTargetAcceptanceCertificate_of_isUniformEquilibriumPayoff
        reward target

/-- A quantitative terminal obstruction to one declared target.  At the
positive error `error`, every literal terminal approximate-Nash profile misses
the target by at least `error` in some coordinate. -/
structure QuittingTerminalTargetRejectionWitness
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) where
  error : ℝ
  error_pos : 0 < error
  separates : ∀ profile : (quittingGame reward).BehaviorProfile,
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) error profile →
    ∃ who,
      error ≤ |quittingTerminalPayoff reward profile who - target who|

/-- **Classical fixed-target semantic alternative.**  Every target either has
a terminal acceptance certificate or a quantitative terminal rejection
witness.  This theorem is excluded middle on the semantic specification; it is
not an effective decision procedure and consumes no projective data. -/
theorem quittingTerminalTarget_semanticAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    Nonempty (QuittingTerminalTargetAcceptanceCertificate reward target) ∨
      Nonempty (QuittingTerminalTargetRejectionWitness reward target) := by
  classical
  by_cases hcertificate : ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile ∧
        ∀ who,
          |quittingTerminalPayoff reward profile who - target who| < ε
  · exact Or.inl ⟨⟨hcertificate⟩⟩
  · push Not at hcertificate
    obtain ⟨error, herror, hseparates⟩ := hcertificate
    exact Or.inr ⟨{
      error := error
      error_pos := herror
      separates := hseparates
    }⟩

/-- A quantitative rejection witness is incompatible with every acceptance
certificate for the same target. -/
theorem QuittingTerminalTargetRejectionWitness.not_acceptance
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : Payoff ι}
    (witness : QuittingTerminalTargetRejectionWitness reward target) :
    ¬ Nonempty (QuittingTerminalTargetAcceptanceCertificate reward target) := by
  rintro ⟨certificate⟩
  obtain ⟨profile, hnash, hclose⟩ :=
    certificate.terminalProfile witness.error witness.error_pos
  obtain ⟨who, hseparated⟩ := witness.separates profile hnash
  exact (not_lt_of_ge hseparated) (hclose who)

/-- A quantitative terminal rejection witness rules out the declared target
as a uniform-equilibrium payoff. -/
theorem QuittingTerminalTargetRejectionWitness.not_isUniformEquilibriumPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : Payoff ι}
    (witness : QuittingTerminalTargetRejectionWitness reward target) :
    ¬ (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  intro huniform
  exact witness.not_acceptance
    (exists_quittingTerminalTargetAcceptanceCertificate_of_isUniformEquilibriumPayoff
      reward target huniform)

/-- Quantitative terminal rejection is equivalent to failure of the exact
fixed target at the uniform-payoff waist. -/
theorem nonempty_quittingTerminalTargetRejectionWitness_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : Payoff ι) :
    Nonempty (QuittingTerminalTargetRejectionWitness reward target) ↔
      ¬ (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  constructor
  · rintro ⟨witness⟩
    exact witness.not_isUniformEquilibriumPayoff
  · intro hnotUniform
    rcases quittingTerminalTarget_semanticAlternative reward target with
      haccept | hrejection
    · exact (hnotUniform
        ((nonempty_quittingTerminalTargetAcceptanceCertificate_iff
          reward target).1 haccept)).elim
    · exact hrejection

/-- A conditional retargeting package retains an accepted replacement target
and a quantitative rejection witness for the original target.  Its construction
below assumes target-free uniform-payoff existence; this structure does not
encode a projective pivot, rank decrease, or retarget-production algorithm. -/
structure QuittingTerminalTargetRetargetingWitness
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (rejectedTarget : Payoff ι) where
  target : Payoff ι
  target_ne : target ≠ rejectedTarget
  acceptance : QuittingTerminalTargetAcceptanceCertificate reward target
  rejection : QuittingTerminalTargetRejectionWitness reward rejectedTarget

/-- Conditional semantic retarget adapter.  The hypothesis is target-free
uniform-payoff existence itself; hence this theorem is not a producer for the
arbitrary quitting-game existence problem. -/
theorem quittingTerminalTarget_acceptance_or_retarget_of_exists_uniformPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (rejectedTarget : Payoff ι)
    (hexists : ∃ target : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none target) :
    Nonempty
        (QuittingTerminalTargetAcceptanceCertificate reward rejectedTarget) ∨
      Nonempty
        (QuittingTerminalTargetRetargetingWitness reward rejectedTarget) := by
  rcases quittingTerminalTarget_semanticAlternative
      reward rejectedTarget with haccept | hrejection
  · exact Or.inl haccept
  · obtain ⟨rejection⟩ := hrejection
    obtain ⟨target, htarget⟩ := hexists
    obtain ⟨acceptance⟩ :=
      exists_quittingTerminalTargetAcceptanceCertificate_of_isUniformEquilibriumPayoff
        reward target htarget
    have hne : target ≠ rejectedTarget := by
      intro heq
      subst target
      exact rejection.not_isUniformEquilibriumPayoff htarget
    exact Or.inr ⟨{
      target := target
      target_ne := hne
      acceptance := acceptance
      rejection := rejection
    }⟩

/-- Terminal approximate-Nash existence at every accuracy supplies the
explicit target-free existence premise through the existing selection theorem,
then applies the conditional semantic retarget adapter.  It does not construct
a replacement from the rejection witness. -/
theorem quittingTerminalTarget_acceptance_or_retarget_of_terminalNash_all_errors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (rejectedTarget : Payoff ι)
    (hterminal : ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile) :
    Nonempty
        (QuittingTerminalTargetAcceptanceCertificate reward rejectedTarget) ∨
      Nonempty
        (QuittingTerminalTargetRetargetingWitness reward rejectedTarget) := by
  apply quittingTerminalTarget_acceptance_or_retarget_of_exists_uniformPayoff
    reward rejectedTarget
  exact quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
    reward hterminal

end GameTheory
