/-
Hostile feasible-posterior regression.

Full revelation of a fair Boolean state supports two distinct posterior
beliefs.  The canonical coupling puts probability `1/2` on each matching
state/point-mass-belief pair and has the required state and belief marginals.
-/

import GameTheory.Mechanism.PosteriorSignals
import GameTheory.Math.Probability.ExpectationMixture

noncomputable section

namespace GameTheory.Tests.FeasiblePosteriors

open GameTheory.Math.Probability

def prior : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure false) (PMF.pure true)

def law : PosteriorLaw Bool :=
  PosteriorLaw.fullRevelation prior

theorem pure_injective : Function.Injective (@PMF.pure Bool) := by
  intro first second heq
  by_contra hne
  have hprob := congrArg (fun belief : PMF Bool => belief first) heq
  simp [PMF.pure_apply, hne] at hprob

theorem law_isBayesPlausible : law.IsBayesPlausible prior :=
  PosteriorLaw.isBayesPlausible_fullRevelation prior

theorem law_supports_distinct_beliefs :
    PMF.pure false ∈ law.support ∧
      PMF.pure true ∈ law.support ∧
      PMF.pure false ≠ PMF.pure true := by
  constructor
  · rw [law, PosteriorLaw.fullRevelation, PMF.support_map]
    refine ⟨false, ?_, rfl⟩
    show prior false ≠ 0
    norm_num [prior, mix_apply, PMF.pure_apply]
  · constructor
    · rw [law, PosteriorLaw.fullRevelation, PMF.support_map]
      refine ⟨true, ?_, rfl⟩
      show prior true ≠ 0
      norm_num [prior, mix_apply, PMF.pure_apply]
    · exact fun heq => Bool.false_ne_true
        (pure_injective heq)

theorem coupling_diagonal_probabilities :
    law.coupling (false, PMF.pure false) = 1 / 2 ∧
      law.coupling (true, PMF.pure true) = 1 / 2 := by
  classical
  constructor <;>
    rw [law, PosteriorLaw.coupling_fullRevelation, PMF.map_apply] <;>
    norm_num [prior, mix_apply, PMF.pure_apply,
      ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num)]

theorem coupling_has_prior_state_marginal :
    law.coupling.map Prod.fst = prior :=
  law.isBayesPlausible_iff_map_fst_coupling prior |>.mp
    law_isBayesPlausible

theorem coupling_has_law_belief_marginal :
    law.coupling.map Prod.snd = law :=
  law.map_snd_coupling

/-- The substantive splitting direction constructs a signal experiment for the
nondegenerate two-posterior law, not merely its canonical coupling. -/
theorem law_has_signalImplementation :
    ∃ (signal : SignalStructure Bool (PMF Bool))
      (posterior : PMF Bool → PMF Bool),
      signal.IsPosteriorAssignment prior posterior ∧
        signal.inducedPosteriorLaw prior posterior = law :=
  SignalStructure.exists_signalStructure_of_isBayesPlausible
    prior law law_isBayesPlausible

theorem constructedSignal_induces_law :
    (SignalStructure.fromPosteriorLaw law).inducedPosteriorLaw prior id = law :=
  SignalStructure.inducedPosteriorLaw_fromPosteriorLaw
    prior law law_isBayesPlausible

/-- Concentrating on the false point mass has the wrong mean for the fair
prior, so Bayes plausibility is a substantive restriction. -/
def biasedLaw : PosteriorLaw Bool :=
  PMF.pure (PMF.pure false)

theorem biasedLaw_not_isBayesPlausible :
    ¬ biasedLaw.IsBayesPlausible prior := by
  intro hplausible
  have hprob := congrArg (fun belief : PMF Bool => belief true) hplausible
  norm_num [PosteriorLaw.IsBayesPlausible, PosteriorLaw.mean, biasedLaw,
    prior, mix_apply, PMF.pure_apply] at hprob

end GameTheory.Tests.FeasiblePosteriors
