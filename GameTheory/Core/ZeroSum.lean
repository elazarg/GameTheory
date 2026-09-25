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

open GameTheory.Math.Probability

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
theorem IsZeroSum.utilityIntegrable_one_of_zero
    {utility : Outcome → Fin 2 → ℝ} (hzero : IsZeroSum utility)
    (law : PMF Outcome)
    (hzeroIntegrable : UtilityIntegrable utility 0 law) :
    UtilityIntegrable utility 1 law := by
  apply payoffIntegrable_congr_on_support
    (fun outcome _ => (hzero.eq_neg outcome).symm)
  exact payoffIntegrable_neg hzeroIntegrable

theorem IsZeroSum.utilityIntegrable_zero_of_one
    {utility : Outcome → Fin 2 → ℝ} (hzero : IsZeroSum utility)
    (law : PMF Outcome)
    (honeIntegrable : UtilityIntegrable utility 1 law) :
    UtilityIntegrable utility 0 law := by
  apply payoffIntegrable_congr_on_support
    (fun outcome _ => by
      have heq := hzero.eq_neg outcome
      calc
        -utility outcome 1 = -(-utility outcome 0) := by rw [heq]
        _ = utility outcome 0 := by ring)
  exact payoffIntegrable_neg honeIntegrable

/-- The opposite player's integrability certificate follows from a zero-sum
identity under the same law. -/
theorem IsZeroSum.expectedUtility_one
    {utility : Outcome → Fin 2 → ℝ} (hzero : IsZeroSum utility)
    (law : PMF Outcome)
    (hzeroIntegrable : UtilityIntegrable utility 0 law)
    (honeIntegrable : UtilityIntegrable utility 1 law) :
    expectedUtility utility 1 law honeIntegrable =
      -expectedUtility utility 0 law hzeroIntegrable := by
  unfold expectedUtility
  calc
    expect law (fun outcome => utility outcome 1) honeIntegrable =
        expect law (fun outcome => -utility outcome 0)
          (payoffIntegrable_neg hzeroIntegrable) :=
      expect_congr_on_support
        (fun outcome _ => hzero.eq_neg outcome) honeIntegrable
        (payoffIntegrable_neg hzeroIntegrable)
    _ = -expect law (fun outcome => utility outcome 0) hzeroIntegrable :=
      expect_neg hzeroIntegrable

theorem IsZeroSum.expectedUtility_zero
    {utility : Outcome → Fin 2 → ℝ} (hzero : IsZeroSum utility)
    (law : PMF Outcome)
    (hzeroIntegrable : UtilityIntegrable utility 0 law)
    (honeIntegrable : UtilityIntegrable utility 1 law) :
    expectedUtility utility 0 law hzeroIntegrable =
      -expectedUtility utility 1 law honeIntegrable := by
  rw [hzero.expectedUtility_one law hzeroIntegrable honeIntegrable]
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
  ∃ hbase : UtilityIntegrable utility 0 (F.mixed.play σ),
    (∀ μ : PMF (F.sig.Strategy 0),
      ∃ hdev : UtilityIntegrable utility 0
          (F.mixed.play (Profile.update σ 0 μ)),
        expectedUtility utility 0 (F.mixed.play (Profile.update σ 0 μ)) hdev ≤
          expectedUtility utility 0 (F.mixed.play σ) hbase) ∧
    (∀ ν : PMF (F.sig.Strategy 1),
      ∃ hdev : UtilityIntegrable utility 0
          (F.mixed.play (Profile.update σ 1 ν)),
        expectedUtility utility 0 (F.mixed.play σ) hbase ≤
          expectedUtility utility 0 (F.mixed.play (Profile.update σ 1 ν)) hdev)

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
  have hbase := hnash.utilityIntegrable 0
  refine ⟨hbase, ?_, ?_⟩
  · intro μ
    obtain ⟨_, hdev, hle⟩ :=
      (isNash_iff (F := F.mixed) σ).1 hnash 0 μ
    refine ⟨hdev, ?_⟩
    exact hle.trans_eq (expectedUtility_congr_law utility 0 rfl _ hbase)
  · intro ν
    obtain ⟨honeBase, honeDev, hle⟩ :=
      (isNash_iff (F := F.mixed) σ).1 hnash 1 ν
    let devLaw := F.mixed.play (Profile.update σ 1 ν)
    have hzeroDev := hzero.utilityIntegrable_zero_of_one devLaw honeDev
    have hbaseEq := hzero.expectedUtility_one
      (F.mixed.play σ) hbase honeBase
    have hdevEq := hzero.expectedUtility_one devLaw hzeroDev honeDev
    refine ⟨hzeroDev, ?_⟩
    have hle' := hle
    rw [hdevEq, hbaseEq] at hle'
    linarith

/-- **A saddle point of a zero-sum game is a mixed Nash equilibrium.**  The
row inequality is player zero's Nash condition; negating the column inequality
gives player one's condition. -/
theorem IsSaddlePoint.isNash (hσ : IsSaddlePoint utility σ)
    (hzero : IsZeroSum utility) :
    IsNash F.mixed (euPreference utility) σ := by
  rcases hσ with ⟨hbase, hrow, hcolumn⟩
  rw [isNash_iff]
  intro who deviation
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) who with rfl | rfl
  · obtain ⟨hdev, hle⟩ := hrow deviation
    exact ⟨hbase, hdev, hle⟩
  · obtain ⟨hzeroDev, hle⟩ := hcolumn deviation
    let baseLaw := F.mixed.play σ
    let devLaw := F.mixed.play (Profile.update σ 1 deviation)
    have honeBase := hzero.utilityIntegrable_one_of_zero baseLaw hbase
    have honeDev := hzero.utilityIntegrable_one_of_zero devLaw hzeroDev
    have hbaseEq := hzero.expectedUtility_one baseLaw hbase honeBase
    have hdevEq := hzero.expectedUtility_one devLaw hzeroDev honeDev
    refine ⟨honeBase, honeDev, ?_⟩
    rw [hbaseEq, hdevEq]
    exact neg_le_neg hle

/-- In a two-player zero-sum game, mixed Nash and saddle points are exactly
the same canonical predicate. -/
theorem isNash_iff_isSaddlePoint (hzero : IsZeroSum utility) :
    IsNash F.mixed (euPreference utility) σ ↔ IsSaddlePoint utility σ :=
  ⟨fun hnash => hnash.isSaddlePoint hzero,
    fun hsaddle => hsaddle.isNash hzero⟩

/-- **Every saddle point of a game is worth the same.** Play one player's half
of one against the other player's half of the other and the two values are
squeezed together. -/
theorem IsSaddlePoint.value_eq (hσ : IsSaddlePoint utility σ)
    (hτ : IsSaddlePoint utility τ) :
    ∃ hσbase : UtilityIntegrable utility 0 (F.mixed.play σ),
      ∃ hτbase : UtilityIntegrable utility 0 (F.mixed.play τ),
        expectedUtility utility 0 (F.mixed.play σ) hσbase =
          expectedUtility utility 0 (F.mixed.play τ) hτbase := by
  rcases hσ with ⟨hσbase, hσrow, hσcolumn⟩
  rcases hτ with ⟨hτbase, hτrow, hτcolumn⟩
  refine ⟨hσbase, hτbase, ?_⟩
  refine le_antisymm ?_ ?_
  · obtain ⟨hσCross, hσle⟩ := hσcolumn (τ 1)
    obtain ⟨hτCross, hτle⟩ := hτrow (σ 0)
    have hlaw : F.mixed.play (Profile.update σ 1 (τ 1)) =
        F.mixed.play (Profile.update τ 0 (σ 0)) := by
      rw [update_one_eq_update_zero]
    calc
      expectedUtility utility 0 (F.mixed.play σ) hσbase ≤
          expectedUtility utility 0
            (F.mixed.play (Profile.update σ 1 (τ 1))) hσCross := hσle
      _ = expectedUtility utility 0
            (F.mixed.play (Profile.update τ 0 (σ 0))) hτCross :=
          expectedUtility_congr_law utility 0 hlaw hσCross hτCross
      _ ≤ expectedUtility utility 0 (F.mixed.play τ) hτbase := hτle
  · obtain ⟨hτCross, hτle⟩ := hτcolumn (σ 1)
    obtain ⟨hσCross, hσle⟩ := hσrow (τ 0)
    have hlaw : F.mixed.play (Profile.update τ 1 (σ 1)) =
        F.mixed.play (Profile.update σ 0 (τ 0)) := by
      rw [update_one_eq_update_zero]
    calc
      expectedUtility utility 0 (F.mixed.play τ) hτbase ≤
          expectedUtility utility 0
            (F.mixed.play (Profile.update τ 1 (σ 1))) hτCross := hτle
      _ = expectedUtility utility 0
            (F.mixed.play (Profile.update σ 0 (τ 0))) hσCross :=
          expectedUtility_congr_law utility 0 hlaw hτCross hσCross
      _ ≤ expectedUtility utility 0 (F.mixed.play σ) hσbase := hσle

end Saddle

end GameTheory
