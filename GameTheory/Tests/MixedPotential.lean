/-
Hostile finite consumer for the mixed extension of an exact potential.

A fair randomization by one player moves the coordination potential from one
to one half.  The same nonzero change is then checked through the generic
randomized expected-utility/potential identity.
-/

import GameTheory.Core.MixedPotential
import Mathlib.Probability.Distributions.Uniform

noncomputable section

namespace GameTheory.Tests.MixedPotential

open GameTheory.Math.Probability

@[reducible]
def signature : GameSignature (Fin 2) where
  Strategy _ := Bool
  Outcome := Bool × Bool

@[reducible]
def form : GameForm (Fin 2) :=
  GameForm.deterministic signature fun profile => (profile 0, profile 1)

def common (outcome : Bool × Bool) : ℝ :=
  if outcome.1 = outcome.2 then 1 else 0

@[reducible]
def game : UtilityGame (Fin 2) where
  form := form
  utility := fun outcome _ => common outcome

def potential (profile : Profile signature) : ℝ :=
  common (profile 0, profile 1)

def allFalse : Profile signature := fun _ => false

def fairCoin : PMF Bool := PMF.uniformOfFintype Bool

def halfMixed : Profile signature.mixed :=
  Profile.update (game.form.purify allFalse) 0 fairCoin

/-- The coordination payoff is an exact potential by identical interests. -/
theorem exactPotential : IsExactPotential game.form game.utility potential := by
  have hi : ∀ profile : Profile signature,
      PayoffIntegrable (form.play profile) common := by
    intro profile
    exact payoffIntegrable_pure _ _
  have h := isExactPotential_of_identicalInterests (F := form) common hi
  show IsExactPotential form (fun outcome _ => common outcome)
    (fun profile => common (profile 0, profile 1))
  simpa [form, expect_pure] using h

/-- The fixture's mixed utility law is integrable from its finite pure outcomes. -/
theorem actualIntegrable (profile : Profile signature.mixed)
    (who : Fin 2) :
    UtilityIntegrable game.utility who (game.form.mixed.play profile) := by
  simpa only [GameForm.mixed_play] using
    (payoffIntegrable_bind_of_finite
      (independentProduct profile) game.form.play
      (fun outcome => game.utility outcome who)
      (fun pureProfile => exactPotential.integrable pureProfile who))

/-- The mixed profile law integrates the fixture's bounded potential. -/
theorem potentialIntegrable (profile : Profile signature.mixed) :
    PayoffIntegrable (independentProduct profile) potential :=
  UtilityGame.IsExactPotential.mixedPotentialIntegrable exactPotential
    actualIntegrable profile

/-- The expected coordination potential is genuinely nonconstant under mixed
play: randomizing one coordinate against `false` gives one half. -/
theorem mixedPotential_half :
    game.form.mixedPotential potential halfMixed
      (potentialIntegrable halfMixed) = 1 / 2 := by
  let q := fun action : Bool => PMF.pure (Profile.update allFalse 0 action)
  have hlaw : independentProduct halfMixed = fairCoin.bind q := by
    rw [halfMixed, GameForm.pi_update_mixed]
    congr 1
    funext action
    rw [purify_update form allFalse 0 action]
    exact independentProduct_pure (Profile.update allFalse 0 action)
  have hbind : PayoffIntegrable (fairCoin.bind q) potential :=
    payoffIntegrable_congr_law hlaw (potentialIntegrable halfMixed)
  have hcond : ∀ action, PayoffIntegrable (q action) potential := by
    intro action
    exact payoffIntegrable_pure _ _
  have hpoint (action : Bool) :
      expect (q action) potential (hcond action) =
        potential (Profile.update allFalse 0 action) :=
    expect_pure _ _ _
  have houter := payoffIntegrable_bind_conditionalExpectation fairCoin q
    potential hbind hcond
  have houter' : PayoffIntegrable fairCoin
      (fun action => potential (Profile.update allFalse 0 action)) :=
    payoffIntegrable_congr_on_support
      (fun action _ => hpoint action) houter
  calc
    _ = expect (fairCoin.bind q) potential hbind :=
      expect_congr_law hlaw potential _ _
    _ = expect fairCoin (fun action => expect (q action) potential (hcond action))
        houter := expect_bind_tower fairCoin q potential hbind hcond
    _ = expect fairCoin
        (fun action => potential (Profile.update allFalse 0 action)) houter' :=
      expect_congr_on_support (fun action _ => hpoint action) _ _
    _ = 1 / 2 := by
      rw [expect_eq_sum]
      norm_num [Fintype.sum_bool, fairCoin, PMF.uniformOfFintype_apply,
        potential, common, allFalse, Profile.update_same,
        Profile.update_of_ne]

/-- The generic mixed exact-potential theorem specializes to the nonconstant
coordination fixture. -/
theorem mixedExactPotential :
    IsExactPotential game.form.mixed game.utility
      (fun profile => game.form.mixedPotential potential profile
        (potentialIntegrable profile)) := by
  simpa only using UtilityGame.IsExactPotential.mixed_of_finite exactPotential

/-- Replacing the fair coin by the pure coordinated action raises both
expected utility and mixed potential by the same nonzero amount. -/
theorem fair_to_coordinated_diff :
    expectedUtility game.utility 0
        (game.form.mixed.play
          (Profile.update halfMixed 0 (PMF.pure false)))
        (actualIntegrable (Profile.update halfMixed 0 (PMF.pure false)) 0) -
      expectedUtility game.utility 0 (game.form.mixed.play halfMixed)
        (actualIntegrable halfMixed 0) =
    game.form.mixedPotential potential
        (Profile.update halfMixed 0 (PMF.pure false))
        (potentialIntegrable (Profile.update halfMixed 0 (PMF.pure false))) -
      game.form.mixedPotential potential halfMixed
        (potentialIntegrable halfMixed) :=
  UtilityGame.IsExactPotential.mixed_pure_diff exactPotential halfMixed 0 false
    (actualIntegrable halfMixed 0)
    (actualIntegrable (Profile.update halfMixed 0 (PMF.pure false)) 0)
    (potentialIntegrable halfMixed)
    (potentialIntegrable (Profile.update halfMixed 0 (PMF.pure false)))

end GameTheory.Tests.MixedPotential
