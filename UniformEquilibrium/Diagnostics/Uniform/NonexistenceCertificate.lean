/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Models.Quitting.Asymptotic
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-!
# Quantitative certificates for failure of uniform-equilibrium existence

This module records the proof-facing refutation interfaces used by searches
for finite stochastic games without a uniform-equilibrium payoff.

The direct certificate asks for one positive exploitability gap at arbitrarily
late horizons, uniformly over the proposed behavior profile.  The player and
the unilateral deviation may depend on both the profile and the horizon.  This
is enough because a uniform approximate equilibrium must control every
deviation at every horizon beyond one common threshold.

For quitting games, it is enough instead to prove a positive exploitability
gap for expected terminal reward.  `QuittingAsymptotic` already proves that
finite-average payoffs converge pointwise to this terminal functional; the
second theorem packages the resulting contradiction with the exact half-gap
needed to turn a weak lower bound into a strict Nash violation.  The final
theorem proves that, after existentially choosing the gap, this terminal
certificate is also necessary for nonexistence.
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every behavior profile is exploitable by at least `gap` at arbitrarily
late finite horizons.  The witness player and deviation may depend on the
horizon. -/
def HasArbitrarilyLateExploitabilityGap
    (G : StochasticGame ι) (s₀ : G.State) (gap : ℝ) : Prop :=
  ∀ σ : G.BehaviorProfile, ∀ threshold : ℕ,
    ∃ (horizon : ℕ) (who : ι) (dev : G.BehaviorStrategy who),
      threshold ≤ horizon ∧
        G.finiteAveragePayoff s₀ horizon σ who + gap ≤
          G.finiteAveragePayoff s₀ horizon
            (Function.update σ who dev) who

/-- A uniform positive late-horizon exploitability gap rules out every
uniform-equilibrium payoff.  Applying the purported uniform payoff at
accuracy `gap / 2` makes the weak gain bound strictly incompatible with its
Nash inequality. -/
theorem not_exists_uniformEquilibriumPayoff_of_arbitrarilyLateExploitabilityGap
    (G : StochasticGame ι) (s₀ : G.State) {gap : ℝ}
    (hgap : 0 < gap)
    (hexploit : G.HasArbitrarilyLateExploitabilityGap s₀ gap) :
    ¬ ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  rintro ⟨v, hv⟩
  have hhalf : 0 < gap / 2 := by linarith
  obtain ⟨σ, threshold, huniform⟩ := hv (gap / 2) hhalf
  obtain ⟨horizon, who, dev, hhorizon, hexploit'⟩ :=
    hexploit σ threshold
  have hnash := (huniform horizon hhorizon).1 who dev
  linarith

end StochasticGame

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- Every behavior profile in a quitting game has a unilateral deviation
whose expected terminal reward improves by at least `gap`. -/
def HasTerminalExploitabilityGap
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (gap : ℝ) : Prop :=
  ∀ σ : (quittingGame reward).BehaviorProfile,
    ∃ (who : iota) (dev : (quittingGame reward).BehaviorStrategy who),
      quittingTerminalPayoff reward σ who + gap ≤
        quittingTerminalPayoff reward (Function.update σ who dev) who

/-- Quantifier-normalized quitting-game refutation theorem.  A uniform
positive terminal exploitability gap rules out a uniform-equilibrium payoff
from the active state. -/
theorem quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    {gap : ℝ} (hgap : 0 < gap)
    (hexploit : HasTerminalExploitabilityGap reward gap) :
    ¬ ∃ v : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none v := by
  apply quittingGame_not_exists_uniformEquilibriumPayoff_of_no_terminalNash
    reward (show 0 < gap / 2 by linarith)
  rintro ⟨σ, hnash⟩
  obtain ⟨who, dev, hexploit'⟩ := hexploit σ
  have hdev := hnash who dev
  linarith

/-- For finite quitting games, nonexistence of a uniform-equilibrium payoff is
exactly the existence of one fixed positive terminal exploitability gap against
every behavioral profile.

The forward implication negates terminal approximate existence at every
positive accuracy.  It produces one positive error at which every profile has
a strict profitable deviation; weakening the strict inequality gives the
fixed weak gap consumed by the reverse implication. -/
theorem not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota) :
    (¬ ∃ payoff : Payoff iota,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ↔
      ∃ gap : ℝ, 0 < gap ∧ HasTerminalExploitabilityGap reward gap := by
  classical
  constructor
  · intro hno
    have hnotFamily : ¬ ∀ ε : ℝ, 0 < ε →
        ∃ profile : (quittingGame reward).BehaviorProfile,
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) ε profile := by
      intro hfamily
      exact hno
        ((quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors
          reward).mpr hfamily)
    push Not at hnotFamily
    obtain ⟨gap, gap_pos, hnoNash⟩ := hnotFamily
    refine ⟨gap, gap_pos, ?_⟩
    intro profile
    have hprofile := hnoNash profile
    unfold StochasticGame.IsεAsymptoticNash at hprofile
    push Not at hprofile
    obtain ⟨who, deviation, hgain⟩ := hprofile
    exact ⟨who, deviation, hgain.le⟩
  · rintro ⟨gap, gap_pos, exploit⟩
    exact
      quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
        reward gap_pos exploit

end GameTheory
