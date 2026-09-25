/-
# EXP-008: canonical Bayesian interim-deviation probe

The finite fixture consumes the canonical Bayesian game and its guarded
ex-ante/interim characterization. It introduces no parallel game record.
-/

import GameTheory.Core.BayesianEquilibrium

noncomputable section

namespace GameTheory.Experimental.Phase2

open GameTheory GameTheory.Math.Probability

def binaryProbeCoin : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure false) (PMF.pure true)

/-- Two privately informed players face a finite binary common prior and
bounded matching payoffs. -/
def binaryProbeGame : BayesianGame Bool where
  Ty _ := Bool
  Act _ := Bool
  prior := independentProduct fun _ => binaryProbeCoin
  payoff types actions who := if actions who = types who then 1 else 0
local instance (who : Bool) : Fintype (binaryProbeGame.Ty who) := by
  exact (inferInstance : Fintype Bool)

local instance (who : Bool) : DecidableEq (binaryProbeGame.Ty who) := by
  exact (inferInstance : DecidableEq Bool)

/-- The canonical finite own-type partition applies to an arbitrary guarded
observable on the probe's common prior. -/
example (who : Bool) (f : (∀ i, binaryProbeGame.Ty i) → ℝ)
    (hf : PayoffIntegrable binaryProbeGame.prior f) :
    expect binaryProbeGame.prior f hf =
      ∑ ownType : binaryProbeGame.Ty who,
        expect binaryProbeGame.prior
          (((fun types => types who) ⁻¹' {ownType}).indicator f)
          (payoffIntegrable_indicator _ hf) :=
  binaryProbeGame.prior_expect_eq_sum who f hf

/-- The canonical updated-plan decomposition has a local guard for the actual
deviation law. -/
example (plan : Profile binaryProbeGame.signature) (who : Bool)
    (deviation : binaryProbeGame.Ty who → binaryProbeGame.Act who)
    (hdeviation : UtilityIntegrable binaryProbeGame.utility who
      (binaryProbeGame.toForm.play (Profile.update plan who deviation))) :
    expectedUtility binaryProbeGame.utility who
        (binaryProbeGame.toForm.play (Profile.update plan who deviation)) hdeviation =
      ∑ ownType : binaryProbeGame.Ty who,
        binaryProbeGame.interimValueOfDeviation who ownType plan (deviation ownType)
          deviation rfl hdeviation :=
  binaryProbeGame.expectedUtility_update plan who deviation hdeviation

/-- The canonical theorem applies to arbitrary contingent plans in the hostile
finite fixture; its whole-deviation payoff guards are established locally. -/
theorem binaryProbe_interim_characterization
    (plan : Profile binaryProbeGame.signature) :
    IsNash binaryProbeGame.toForm (euPreference binaryProbeGame.utility) plan ↔
      ∀ (who : Bool) (ownType : binaryProbeGame.Ty who)
        (respond : binaryProbeGame.Act who),
        binaryProbeGame.interimValueOfDeviation who ownType plan respond
          (binaryProbeGame.singleTypeDeviation plan who ownType respond) (by
            simp [BayesianGame.singleTypeDeviation])
          (by
            apply payoffIntegrable_of_bounded _ _ (C := 1)
            intro outcome
            rcases outcome with ⟨types, actions⟩
            simp [binaryProbeGame, BayesianGame.utility]
            split_ifs <;> norm_num) ≤
        binaryProbeGame.interimValueOfDeviation who ownType plan
          (plan who ownType) (fun t => plan who t) rfl (by
            simpa only [Profile.update_eq_self] using
              (by
                apply payoffIntegrable_of_bounded _ _ (C := 1)
                intro outcome
                rcases outcome with ⟨types, actions⟩
                simp [binaryProbeGame, BayesianGame.utility]
                split_ifs <;> norm_num)) := by
  apply binaryProbeGame.isNash_iff_interim plan
  intro who deviation
  apply payoffIntegrable_of_bounded _ _ (C := 1)
  intro outcome
  rcases outcome with ⟨types, actions⟩
  simp [binaryProbeGame, BayesianGame.utility]
  split_ifs <;> norm_num

end GameTheory.Experimental.Phase2
