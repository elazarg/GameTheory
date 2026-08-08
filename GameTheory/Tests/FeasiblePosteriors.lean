/-
Hostile feasible-posterior regression.

Full revelation of a fair Boolean state supports two distinct posterior
beliefs.  The canonical coupling puts probability `1/2` on each matching
state/point-mass-belief pair and has the required state and belief marginals.
-/

import GameTheory.Mechanism.FeasiblePosteriors

noncomputable section

namespace GameTheory.Tests.FeasiblePosteriors

open Probability

def prior : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

def law : PosteriorLaw Bool :=
  PosteriorLaw.fullRevelation prior

theorem pure_injective : Function.Injective (@FinDist.pure Bool) := by
  intro first second heq
  by_contra hne
  have hprob := congrArg (fun belief : FinDist Bool => belief.prob first) heq
  rw [FinDist.prob_pure_self,
    FinDist.prob_pure_of_ne hne] at hprob
  norm_num at hprob

theorem law_isBayesPlausible : law.IsBayesPlausible prior :=
  PosteriorLaw.isBayesPlausible_fullRevelation prior

theorem law_supports_distinct_beliefs :
    FinDist.pure false ∈ law.support ∧
      FinDist.pure true ∈ law.support ∧
      FinDist.pure false ≠ FinDist.pure true := by
  constructor
  · rw [law, PosteriorLaw.fullRevelation, FinDist.support_map]
    refine ⟨false, ?_, rfl⟩
    rw [← FinDist.prob_pos_iff]
    norm_num [prior, FinDist.prob_mix, FinDist.prob_pure_eq_ite]
  · constructor
    · rw [law, PosteriorLaw.fullRevelation, FinDist.support_map]
      refine ⟨true, ?_, rfl⟩
      rw [← FinDist.prob_pos_iff]
      norm_num [prior, FinDist.prob_mix, FinDist.prob_pure_eq_ite]
    · exact fun heq => Bool.false_ne_true
        (pure_injective heq)

theorem coupling_diagonal_probabilities :
    law.coupling.prob (false, FinDist.pure false) = 1 / 2 ∧
      law.coupling.prob (true, FinDist.pure true) = 1 / 2 := by
  classical
  constructor <;>
    rw [PosteriorLaw.prob_coupling, law,
      PosteriorLaw.fullRevelation,
      FinDist.prob_map_of_injective FinDist.pure pure_injective] <;>
    norm_num [prior, FinDist.prob_mix, FinDist.prob_pure_eq_ite]

theorem coupling_has_prior_state_marginal :
    law.coupling.map Prod.fst = prior :=
  law.isBayesPlausible_iff_map_fst_coupling prior |>.mp
    law_isBayesPlausible

theorem coupling_has_law_belief_marginal :
    law.coupling.map Prod.snd = law :=
  law.map_snd_coupling

end GameTheory.Tests.FeasiblePosteriors
