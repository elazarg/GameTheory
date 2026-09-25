/-
# The minimax theorem

A two-player zero-sum finite game has a value: a number the first player can
guarantee and the second can hold them to. This is von Neumann's theorem, and
here it is a corollary rather than a separate argument — equilibria exist, a
zero-sum equilibrium is a saddle point, and a saddle point *is* a pair of
guarantees meeting at one number.

Everything except existence lives below the analytic boundary, including the
fact that all saddle points are worth the same. Only the assertion that one
exists needs a fixed point, and that is the single line this module contributes.
-/

import GameTheory.Analysis.Nash
import GameTheory.Core.ZeroSum

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe us uo

variable {F : GameForm (Fin 2)} [∀ i, Fintype (F.sig.Strategy i)]
variable [∀ i, Nonempty (F.sig.Strategy i)] (utility : F.sig.Outcome → Fin 2 → ℝ)

/-- **A zero-sum finite game has a saddle point.** -/
theorem exists_isSaddlePoint (hzero : IsZeroSum utility)
    (hintegrable : F.HasIntegrableUtility utility) :
    ∃ σ : Profile F.sig.mixed, IsSaddlePoint utility σ :=
  let ⟨σ, hnash⟩ := exists_isNash_mixed utility hintegrable
  ⟨σ, hnash.isSaddlePoint hzero⟩

/-- **The minimax theorem.** There is a number and a profile realizing it from
both sides: the first player cannot do better than the number against the second
player's half, and the second cannot hold the first below it. Any other saddle
point gives the same number, which is why it deserves the name *value*. -/
theorem exists_value (hzero : IsZeroSum utility)
    (hintegrable : F.HasIntegrableUtility utility) :
    ∃ (value : ℝ) (σ : Profile F.sig.mixed)
      (hbase : UtilityIntegrable utility 0 (F.mixed.play σ)),
      expectedUtility utility 0 (F.mixed.play σ) hbase = value ∧
      (∀ μ : PMF (F.sig.Strategy 0),
        ∃ hdev : UtilityIntegrable utility 0
          (F.mixed.play (Profile.update σ 0 μ)),
          expectedUtility utility 0
            (F.mixed.play (Profile.update σ 0 μ)) hdev ≤ value) ∧
      (∀ ν : PMF (F.sig.Strategy 1),
        ∃ hdev : UtilityIntegrable utility 0
          (F.mixed.play (Profile.update σ 1 ν)),
          value ≤ expectedUtility utility 0
            (F.mixed.play (Profile.update σ 1 ν)) hdev) ∧
      (∀ other : Profile F.sig.mixed, IsSaddlePoint utility other →
        ∃ hother : UtilityIntegrable utility 0 (F.mixed.play other),
          expectedUtility utility 0 (F.mixed.play other) hother = value) := by
  obtain ⟨σ, hsaddle⟩ := exists_isSaddlePoint utility hzero hintegrable
  rcases hsaddle with ⟨hbase, hrowSaddle, hcolumnSaddle⟩
  let value := expectedUtility utility 0 (F.mixed.play σ) hbase
  refine ⟨value, σ, hbase, rfl, ?_, ?_, ?_⟩
  · intro μ
    obtain ⟨hdev, hle⟩ := hrowSaddle μ
    exact ⟨hdev, by simpa only [value] using hle⟩
  · intro ν
    obtain ⟨hdev, hle⟩ := hcolumnSaddle ν
    exact ⟨hdev, by simpa only [value] using hle⟩
  · intro other hother
    obtain ⟨hotherBase, _, heq⟩ :=
      hother.value_eq ⟨hbase, hrowSaddle, hcolumnSaddle⟩
    exact ⟨hotherBase, by simpa only [value] using heq⟩

/-- Payoffs that some mixed row can guarantee against every mixed column.
The base profile is overwritten at both coordinates; it only packages the
dependent two-player strategy family without casts. -/
def lowerSecurityPayoffs (base : Profile F.sig.mixed) : Set ℝ :=
  {value | ∃ row : PMF (F.sig.Strategy 0),
    ∀ column : PMF (F.sig.Strategy 1),
      ∃ h : UtilityIntegrable utility 0
        (F.mixed.play
          (Profile.update (Profile.update base 0 row) 1 column)),
        value ≤ expectedUtility utility 0
          (F.mixed.play
            (Profile.update (Profile.update base 0 row) 1 column)) h}

/-- Payoff caps that some mixed column can impose against every mixed row. -/
def upperSecurityPayoffs (base : Profile F.sig.mixed) : Set ℝ :=
  {value | ∃ column : PMF (F.sig.Strategy 1),
    ∀ row : PMF (F.sig.Strategy 0),
      ∃ h : UtilityIntegrable utility 0
        (F.mixed.play
          (Profile.update (Profile.update base 0 row) 1 column)),
        expectedUtility utility 0
            (F.mixed.play
              (Profile.update (Profile.update base 0 row) 1 column)) h ≤
          value}

/-- **The textbook maximin--minimax equality.** The supremum of the payoffs
the row player can guarantee equals the infimum of the caps the column player
can impose.  A saddle profile attains both bounds. -/
theorem sup_lowerSecurityPayoffs_eq_inf_upperSecurityPayoffs
    (hzero : IsZeroSum utility)
    (hintegrable : F.HasIntegrableUtility utility) :
    ∃ base : Profile F.sig.mixed,
      sSup (lowerSecurityPayoffs utility base) =
        sInf (upperSecurityPayoffs utility base) := by
  obtain ⟨base, hsaddle⟩ := exists_isSaddlePoint utility hzero hintegrable
  rcases hsaddle with ⟨hbase, hrowSaddle, hcolumnSaddle⟩
  let value := expectedUtility utility 0 (F.mixed.play base) hbase
  have hreplaceColumn (row : PMF (F.sig.Strategy 0)) :
      Profile.update (Profile.update base 0 row) 1 (base 1) =
        Profile.update base 0 row := by
    apply Profile.update_eq_self
  have hreplaceRow (column : PMF (F.sig.Strategy 1)) :
      Profile.update (Profile.update base 0 (base 0)) 1 column =
        Profile.update base 1 column := by
    rw [Profile.update_eq_self]
  have hlowerGreatest : IsGreatest (lowerSecurityPayoffs utility base) value := by
    constructor
    · refine ⟨base 0, fun column => ?_⟩
      have hlaw : F.mixed.play
          (Profile.update (Profile.update base 0 (base 0)) 1 column) =
          F.mixed.play (Profile.update base 1 column) := by
        rw [hreplaceRow]
      obtain ⟨hdev, hle⟩ := hcolumnSaddle column
      have hcandidate := payoffIntegrable_congr_law hlaw.symm hdev
      refine ⟨hcandidate, ?_⟩
      dsimp [value]
      exact hle.trans_eq
        (expectedUtility_congr_law utility 0 hlaw hcandidate hdev).symm
    · rintro candidate ⟨row, hrow⟩
      obtain ⟨hsource, hguarantee⟩ := hrow (base 1)
      have hlaw : F.mixed.play
          (Profile.update (Profile.update base 0 row) 1 (base 1)) =
          F.mixed.play (Profile.update base 0 row) :=
        congrArg F.mixed.play (hreplaceColumn row)
      have hrowGuard := payoffIntegrable_congr_law hlaw hsource
      have hrowValue :=
        expectedUtility_congr_law utility 0 hlaw hsource hrowGuard
      obtain ⟨hdev, hle⟩ := hrowSaddle row
      calc
        candidate ≤ expectedUtility utility 0
            (F.mixed.play (Profile.update base 0 row)) hrowGuard := by
          exact hguarantee.trans_eq hrowValue.symm
        _ ≤ value := by simpa [value] using hle
  have hupperLeast : IsLeast (upperSecurityPayoffs utility base) value := by
    constructor
    · refine ⟨base 1, fun row => ?_⟩
      have hlaw : F.mixed.play
          (Profile.update (Profile.update base 0 row) 1 (base 1)) =
          F.mixed.play (Profile.update base 0 row) :=
        congrArg F.mixed.play (hreplaceColumn row)
      obtain ⟨hdev, hle⟩ := hrowSaddle row
      have hcandidate := payoffIntegrable_congr_law hlaw.symm hdev
      refine ⟨hcandidate, ?_⟩
      have hvalue := expectedUtility_congr_law utility 0 hlaw hcandidate hdev
      calc
        expectedUtility utility 0
            (F.mixed.play (Profile.update (Profile.update base 0 row) 1 (base 1)))
            hcandidate =
          expectedUtility utility 0 (F.mixed.play (Profile.update base 0 row)) hdev :=
            hvalue
        _ ≤ value := by simpa [value] using hle
    · rintro candidate ⟨column, hcolumn⟩
      obtain ⟨hsource, hcap⟩ := hcolumn (base 0)
      have hlaw : F.mixed.play
          (Profile.update (Profile.update base 0 (base 0)) 1 column) =
          F.mixed.play (Profile.update base 1 column) := by
        rw [hreplaceRow]
      have hdevGuard := payoffIntegrable_congr_law hlaw hsource
      have hdevValue := expectedUtility_congr_law utility 0 hlaw hsource hdevGuard
      obtain ⟨hdev, hle⟩ := hcolumnSaddle column
      calc
        value ≤ expectedUtility utility 0
            (F.mixed.play (Profile.update base 1 column)) hdevGuard := by
          simpa [value] using hle
        _ = expectedUtility utility 0
            (F.mixed.play
              (Profile.update (Profile.update base 0 (base 0)) 1 column)) hsource :=
          hdevValue.symm
        _ ≤ candidate := hcap
  exact ⟨base, hlowerGreatest.csSup_eq.trans hupperLeast.csInf_eq.symm⟩

end GameTheory
