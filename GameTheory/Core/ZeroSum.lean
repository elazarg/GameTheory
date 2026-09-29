/-
# Zero-sum games and saddle points

When the players' payoffs sum to zero at every outcome there is only one number
to track, and an equilibrium becomes a *saddle point*: the first player cannot
push it up alone and the second cannot push it down alone.

Nothing here needs a fixed point. The definitions are static, the equilibrium
correspondence is arithmetic, and the fact that all saddle points of a game are
worth the same is a two-line argument from the definition. The same squeeze
shows that an equilibrium strategy is secure against every opponent strategy,
so every coarse correlated equilibrium, however correlated, is worth the
equilibrium value. Only the assertion that an equilibrium exists needs
analysis, and it lives above this module rather than in it.

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
    (law : PMF Outcome) :
    expectedUtility utility 1 law =
      -expectedUtility utility 0 law := by
  unfold expectedUtility
  calc
    expect law (fun outcome => utility outcome 1) =
        expect law (fun outcome => -utility outcome 0) :=
      expect_congr_on_support
        (fun outcome _ => hzero.eq_neg outcome)
    _ = -expect law (fun outcome => utility outcome 0) :=
      expect_neg

theorem IsZeroSum.expectedUtility_zero
    {utility : Outcome → Fin 2 → ℝ} (hzero : IsZeroSum utility)
    (law : PMF Outcome) :
    expectedUtility utility 0 law =
      -expectedUtility utility 1 law := by
  rw [hzero.expectedUtility_one law]
  ring

/-- The second player's payoff has an expectation exactly when the first's
does. -/
theorem IsZeroSum.utilityHasExpectation_one_iff
    {utility : Outcome → Fin 2 → ℝ} (hzero : IsZeroSum utility) (law : PMF Outcome) :
    UtilityHasExpectation utility 1 law ↔ UtilityHasExpectation utility 0 law := by
  rw [UtilityHasExpectation, hasExpectation_congr_on_support
    (fun outcome _ => hzero.eq_neg outcome), hasExpectation_neg_iff]

/-- The second player's extended expected utility is the first player's
negated, whenever it exists. -/
theorem IsZeroSum.extendedExpectedUtility_one
    {utility : Outcome → Fin 2 → ℝ} (hzero : IsZeroSum utility) {law : PMF Outcome}
    (h : UtilityHasExpectation utility 0 law) :
    extendedExpectedUtility utility 1 law = -extendedExpectedUtility utility 0 law := by
  unfold extendedExpectedUtility
  rw [extendedExpect_congr_on_support (fun outcome _ => hzero.eq_neg outcome),
    extendedExpect_neg h]

/-- The second player weakly prefers one law to another exactly when the first
player weakly prefers the other. -/
theorem IsZeroSum.euPreference_one_iff
    {utility : Outcome → Fin 2 → ℝ} (hzero : IsZeroSum utility)
    (preferred alternative : PMF Outcome) :
    euPreference utility 1 preferred alternative ↔
      euPreference utility 0 alternative preferred := by
  unfold euPreference
  rw [hzero.utilityHasExpectation_one_iff, hzero.utilityHasExpectation_one_iff]
  constructor
  · rintro ⟨hpreferred, halternative, hle⟩
    rw [hzero.extendedExpectedUtility_one hpreferred,
      hzero.extendedExpectedUtility_one halternative, EReal.neg_le_neg_iff] at hle
    exact ⟨halternative, hpreferred, hle⟩
  · rintro ⟨halternative, hpreferred, hle⟩
    refine ⟨hpreferred, halternative, ?_⟩
    rw [hzero.extendedExpectedUtility_one hpreferred,
      hzero.extendedExpectedUtility_one halternative, EReal.neg_le_neg_iff]
    exact hle

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

/-- Replacing the second player's strategy by another profile's is the same as
replacing that profile's first player by this one's — with two players there is
nothing else to disagree about. -/
theorem update_one_eq_update_zero {sig : GameSignature (Fin 2)} (σ τ : Profile sig) :
    Profile.update σ 1 (τ 1) = Profile.update τ 0 (σ 0) := by
  funext i
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
  · rw [Profile.update_of_ne _ _ (by decide), Profile.update_same]
  · rw [Profile.update_same, Profile.update_of_ne _ _ (by decide)]

section Security

/-! ## Security and the value of coarse correlation

The strategy carrier is arbitrary: strategies may already be mixed or
behavioral, so these statements need no second layer of randomization. Only
expected utilities are fixed; outcome laws and sequential incentives are not. -/

variable {F : GameForm (Fin 2)} {utility : F.sig.Outcome → Fin 2 → ℝ}
  {profile : Profile F.sig}

/-- **Nash strategies are secure in zero-sum games.** Each player's equilibrium
strategy guarantees the equilibrium value against every opponent strategy. -/
theorem IsNash.zeroSum_security (hzero : IsZeroSum utility)
    (hnash : IsNash F (euPreference utility) profile) (other : Profile F.sig) :
    euPreference utility 0 (F.play (Profile.update other 0 (profile 0))) (F.play profile) ∧
      euPreference utility 0 (F.play profile)
        (F.play (Profile.update other 1 (profile 1))) := by
  constructor
  · have hle := (isNash_iff profile).1 hnash 1 (other 1)
    rwa [hzero.euPreference_one_iff, update_one_eq_update_zero profile other] at hle
  · have hle := (isNash_iff profile).1 hnash 0 (other 0)
    rwa [← update_one_eq_update_zero other profile] at hle

/-- **Coarse correlation cannot change a zero-sum value.** If a two-player
zero-sum game has a Nash equilibrium in its strategy carrier, every coarse
correlated equilibrium gives each player exactly the equilibrium payoff, even
when it recommends profiles far from that equilibrium. The payoffs need not be
integrable: an infinite equilibrium value is shared in the same way. -/
theorem IsCoarseCorrelatedEq.extendedExpectedUtility_eq_of_zeroSum
    (hzero : IsZeroSum utility) {law : PMF (Profile F.sig)}
    (hcce : IsCoarseCorrelatedEq F (euPreference utility) law)
    (hnash : IsNash F (euPreference utility) profile) (who : Fin 2) :
    extendedExpectedUtility utility who (F.outcomeLaw law) =
      extendedExpectedUtility utility who (F.play profile) := by
  have lower : euPreference utility 0 (F.outcomeLaw law) (F.play profile) := by
    have hdev := (isCoarseCorrelatedEq_iff law).1 hcce 0 (profile 0)
    exact euPreference_transitive utility 0 _ _ _
      hdev (euPreference_bind_left law _
        (fun other _ => (hnash.zeroSum_security hzero other).1) hdev.2.1)
  have upper : euPreference utility 0 (F.play profile) (F.outcomeLaw law) := by
    have hdev := (isCoarseCorrelatedEq_iff law).1 hcce 1 (profile 1)
    rw [hzero.euPreference_one_iff] at hdev
    exact euPreference_transitive utility 0 _ _ _
      (euPreference_bind law _ (fun other _ => (hnash.zeroSum_security hzero other).2)
        hdev.1) hdev
  have hsame := le_antisymm upper.2.2 lower.2.2
  rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) who with rfl | rfl
  · exact hsame
  · rw [hzero.extendedExpectedUtility_one lower.1,
      hzero.extendedExpectedUtility_one upper.1, hsame]

/-- **All zero-sum Nash equilibria are worth the same**, in any strategy
carrier. For mixed extensions this is also `IsSaddlePoint.value_eq`, which needs
no zero-sum premise because a saddle point is stated in one payoff. -/
theorem IsNash.extendedExpectedUtility_eq_of_zeroSum (hzero : IsZeroSum utility)
    {other : Profile F.sig}
    (hnash : IsNash F (euPreference utility) profile)
    (hother : IsNash F (euPreference utility) other) (who : Fin 2) :
    extendedExpectedUtility utility who (F.play profile) =
      extendedExpectedUtility utility who (F.play other) := by
  have hcce : IsCoarseCorrelatedEq F (euPreference utility) (PMF.pure profile) :=
    (isNash_iff_isCoarseCorrelatedEq_pure profile).1 hnash
  have hequal := hcce.extendedExpectedUtility_eq_of_zeroSum hzero hother who
  rwa [extendedExpectedUtility_congr_law utility who (F.outcomeLaw_pure profile)] at hequal

end Security

section Saddle

variable {F : GameForm (Fin 2)} {utility : F.sig.Outcome → Fin 2 → ℝ}
variable {σ τ : Profile F.sig.mixed}

variable (utility) in
/-- The first player cannot raise the shared number alone and the second cannot
lower it alone. Only the first player's payoff appears, because in a zero-sum
game the second player's is its negation. -/
def IsSaddlePoint (σ : Profile F.sig.mixed) : Prop :=
  (∀ μ : PMF (F.sig.Strategy 0),
      euPreference utility 0 (F.mixed.play σ) (F.mixed.play (Profile.update σ 0 μ))) ∧
    ∀ ν : PMF (F.sig.Strategy 1),
      euPreference utility 0 (F.mixed.play (Profile.update σ 1 ν)) (F.mixed.play σ)

/-- **A zero-sum equilibrium is a saddle point.** The first player's inequality
is the equilibrium condition; the second player's is the same condition read
through the negation. -/
theorem IsNash.isSaddlePoint (hzero : IsZeroSum utility)
    (hnash : IsNash F.mixed (euPreference utility) σ) : IsSaddlePoint utility σ := by
  refine ⟨fun μ => (isNash_iff (F := F.mixed) σ).1 hnash 0 μ, fun ν => ?_⟩
  exact (hzero.euPreference_one_iff _ _).1 ((isNash_iff (F := F.mixed) σ).1 hnash 1 ν)

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
  · exact (hzero.euPreference_one_iff _ _).2 (hσ.2 deviation)

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
    UtilityHasExpectation utility 0 (F.mixed.play σ) ∧
      UtilityHasExpectation utility 0 (F.mixed.play τ) ∧
        extendedExpectedUtility utility 0 (F.mixed.play σ) =
          extendedExpectedUtility utility 0 (F.mixed.play τ) := by
  have hστ : F.mixed.play (Profile.update σ 1 (τ 1)) =
      F.mixed.play (Profile.update τ 0 (σ 0)) := by
    rw [update_one_eq_update_zero]
  have hτσ : F.mixed.play (Profile.update τ 1 (σ 1)) =
      F.mixed.play (Profile.update σ 0 (τ 0)) := by
    rw [update_one_eq_update_zero]
  have hσcolumn := hσ.2 (τ 1)
  have hτrow := hτ.1 (σ 0)
  have hτcolumn := hτ.2 (σ 1)
  have hσrow := hσ.1 (τ 0)
  rw [hστ] at hσcolumn
  rw [hτσ] at hτcolumn
  exact ⟨hσrow.1, hτrow.1, le_antisymm (hσcolumn.2.2.trans hτrow.2.2)
    (hτcolumn.2.2.trans hσrow.2.2)⟩

end Saddle

end GameTheory
