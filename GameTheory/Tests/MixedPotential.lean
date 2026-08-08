/-
Hostile finite consumer for the mixed extension of an exact potential.

A fair randomization by one player moves the coordination potential from one
to one half.  The same nonzero change is then checked through the generic
randomized expected-utility/potential identity.
-/

import GameTheory.Core.MixedPotential

noncomputable section

namespace GameTheory.Tests.MixedPotential

open Probability

@[reducible]
def signature : GameSignature (Fin 2) where
  Strategy _ := Bool
  Outcome := Bool × Bool

@[reducible]
def form : GameForm (Fin 2) where
  sig := signature
  play profile := FinDist.pure (profile 0, profile 1)

def common (outcome : Bool × Bool) : ℝ :=
  if outcome.1 = outcome.2 then 1 else 0

@[reducible]
def game : UtilityGame (Fin 2) where
  form := form
  utility := fun outcome _ => common outcome

def potential (profile : Profile signature) : ℝ :=
  common (profile 0, profile 1)

def allFalse : Profile signature := fun _ => false

def fairCoin : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

def halfMixed : Profile signature.mixed :=
  Profile.update (game.form.purify allFalse) 0 fairCoin

/-- The coordination payoff is an exact potential by identical interests. -/
theorem exactPotential : IsExactPotential game.form game.utility potential := by
  show IsExactPotential game.form game.utility
    (fun profile => common (profile 0, profile 1))
  simpa [game, form, common] using
    (isExactPotential_of_identicalInterests (F := form) common)

/-- The expected coordination potential is genuinely nonconstant under mixed
play: randomizing one coordinate against `false` gives one half. -/
theorem mixedPotential_half : game.mixedPotential potential halfMixed = 1 / 2 := by
  rw [halfMixed, game.mixedPotential_update, fairCoin, FinDist.expect_mix,
    FinDist.expect_pure, FinDist.expect_pure, purify_update, purify_update,
    game.mixedPotential_purify, game.mixedPotential_purify]
  norm_num [potential, common, allFalse, Profile.update_same, Profile.update_of_ne]

/-- The generic mixed exact-potential theorem specializes to the nonconstant
coordination fixture. -/
theorem mixedExactPotential :
    IsExactPotential game.form.mixed game.utility (game.mixedPotential potential) :=
  UtilityGame.IsExactPotential.mixed exactPotential

/-- Replacing the fair coin by the pure coordinated action raises both
expected utility and mixed potential by the same nonzero amount. -/
theorem fair_to_coordinated_diff :
    expectedUtility game.utility 0
        (game.form.mixed.play
          (Profile.update halfMixed 0 (FinDist.pure false))) -
      expectedUtility game.utility 0 (game.form.mixed.play halfMixed) =
    game.mixedPotential potential
        (Profile.update halfMixed 0 (FinDist.pure false)) -
      game.mixedPotential potential halfMixed :=
  UtilityGame.IsExactPotential.mixed_pure_diff exactPotential halfMixed 0 false

end GameTheory.Tests.MixedPotential
