/-
# Zero-sum games and saddle points

When the players' payoffs sum to zero at every outcome there is only one number
to track, and an equilibrium becomes a *saddle point*: the first player cannot
push it up alone and the second cannot push it down alone.

Nothing here needs a fixed point. The definitions are static, the equilibrium
correspondence is arithmetic, and the fact that all saddle points of a game are
worth the same is a two-line argument from the definition. Only the assertion
that one exists needs analysis, and it lives above this module rather than in
it.

The two-player restriction is real and is in the type: the saddle inequalities
name a player who moves up and a player who moves down, and with three players
there is no such pair.
-/

import GameTheory.Core.Utility

noncomputable section

namespace GameTheory

open Probability

universe uι us uo

section ZeroSum

variable {ι : Type uι} [Fintype ι] {Outcome : Type uo}

/-- Every outcome distributes a total of zero: one player's gain is another's
loss. -/
def IsZeroSum (utility : Outcome → ι → ℝ) : Prop := ∀ outcome, ∑ i, utility outcome i = 0

/-- With two players the condition says exactly that the payoffs are negatives.
-/
theorem IsZeroSum.eq_neg {utility : Outcome → Fin 2 → ℝ} (hzero : IsZeroSum utility)
    (outcome : Outcome) : utility outcome 1 = -utility outcome 0 := by
  have := hzero outcome
  rw [Fin.sum_univ_two] at this
  linarith

/-- Hence the second player's expected utility is the first player's negated. -/
theorem IsZeroSum.expectedUtility_one {utility : Outcome → Fin 2 → ℝ}
    (hzero : IsZeroSum utility) (law : FinDist Outcome) :
    expectedUtility utility 1 law = -expectedUtility utility 0 law := by
  unfold expectedUtility
  rw [show (fun outcome => utility outcome 1) = fun outcome => (-1 : ℝ) * utility outcome 0 from
    funext fun outcome => by rw [neg_one_mul, hzero.eq_neg]]
  rw [FinDist.expect_smul]
  ring

/-- A zero-sum team game has zero utility at every outcome. -/
theorem IsZeroSum.teamGame_utility_zero [Nonempty ι] {utility : Outcome → ι → ℝ}
    (hzero : IsZeroSum utility) (hteam : IsTeamGame utility)
    (outcome : Outcome) (who : ι) : utility outcome who = 0 := by
  have hsum : (∑ player, utility outcome player) = 0 := hzero outcome
  have hconstant : ∀ player, utility outcome player = utility outcome who :=
    fun player => hteam outcome player who
  simp_rw [hconstant] at hsum
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  exact (mul_eq_zero.mp hsum).resolve_left hcard_ne

end ZeroSum

section Saddle

variable {F : GameForm (Fin 2)} {utility : F.sig.Outcome → Fin 2 → ℝ}
variable {σ τ : Profile F.sig.mixed}

variable (utility) in
/-- The first player cannot raise the shared number alone and the second cannot
lower it alone. Only the first player's payoff appears, because in a zero-sum
game the second player's is its negation. -/
def IsSaddlePoint (σ : Profile F.sig.mixed) : Prop :=
  (∀ μ : FinDist (F.sig.Strategy 0),
      expectedUtility utility 0 (F.mixed.play (Profile.update σ 0 μ)) ≤
        expectedUtility utility 0 (F.mixed.play σ)) ∧
    ∀ ν : FinDist (F.sig.Strategy 1),
      expectedUtility utility 0 (F.mixed.play σ) ≤
        expectedUtility utility 0 (F.mixed.play (Profile.update σ 1 ν))

/-- Replacing the second player's law by another profile's is the same as
replacing that profile's first player by this one's — with two players there is
nothing else to disagree about. -/
theorem update_one_eq_update_zero (σ τ : Profile F.sig.mixed) :
    Profile.update σ 1 (τ 1) = Profile.update τ 0 (σ 0) := by
  funext i
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
  · rw [Profile.update_of_ne _ _ (by decide), Profile.update_same]
  · rw [Profile.update_same, Profile.update_of_ne _ _ (by decide)]

/-- **A zero-sum equilibrium is a saddle point.** The first player's inequality
is the equilibrium condition; the second player's is the same condition read
through the negation. -/
theorem IsNash.isSaddlePoint (hzero : IsZeroSum utility)
    (hnash : IsNash F.mixed (euPreference utility) σ) : IsSaddlePoint utility σ := by
  rw [isNash_iff] at hnash
  refine ⟨fun μ => hnash 0 μ, fun ν => ?_⟩
  have hone := hnash 1 ν
  rw [euPreference_apply, hzero.expectedUtility_one, hzero.expectedUtility_one] at hone
  linarith

/-- **A saddle point of a zero-sum game is a mixed Nash equilibrium.**  The
row inequality is player zero's Nash condition; negating the column inequality
gives player one's condition. -/
theorem IsSaddlePoint.isNash (hσ : IsSaddlePoint utility σ)
    (hzero : IsZeroSum utility) :
    IsNash F.mixed (euPreference utility) σ := by
  rw [isNash_iff]
  intro who deviation
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) who with rfl | rfl
  · exact hσ.1 deviation
  · rw [euPreference_apply, hzero.expectedUtility_one,
      hzero.expectedUtility_one]
    exact neg_le_neg (hσ.2 deviation)

/-- In a two-player zero-sum game, mixed Nash and saddle points are exactly
the same canonical predicate. -/
theorem isNash_iff_isSaddlePoint (hzero : IsZeroSum utility) :
    IsNash F.mixed (euPreference utility) σ ↔ IsSaddlePoint utility σ :=
  ⟨fun hnash => hnash.isSaddlePoint hzero,
    fun hsaddle => hsaddle.isNash hzero⟩

/-- **Every saddle point of a game is worth the same.** Play one player's half
of one against the other player's half of the other and the two values are
squeezed together. -/
theorem IsSaddlePoint.value_eq (hσ : IsSaddlePoint utility σ) (hτ : IsSaddlePoint utility τ) :
    expectedUtility utility 0 (F.mixed.play σ) = expectedUtility utility 0 (F.mixed.play τ) := by
  refine le_antisymm ?_ ?_
  · exact (hσ.2 (τ 1)).trans (by rw [update_one_eq_update_zero]; exact hτ.1 (σ 0))
  · exact (hτ.2 (σ 1)).trans (by rw [update_one_eq_update_zero]; exact hσ.1 (τ 0))

end Saddle

end GameTheory
