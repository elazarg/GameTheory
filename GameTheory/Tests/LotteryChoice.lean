module

/-
# Observed lottery choice beyond expected utility

A possibility ranking induces consistent finite-menu choices among a sure
failure, a sure success, and a fair lottery. These observations have a complete
preorder representation but no expected-utility representation over outcomes.
-/

public import GameTheory.Tests.Potential
public import GameTheory.Math.FiniteChoice

@[expose] public section

noncomputable section

namespace GameTheory.Tests.LotteryChoice

open GameTheory.Math GameTheory.Math.Probability

/-- Three genuinely different lotteries, including the fair mixture. -/
def law (action : Fin 3) : PMF Bool :=
  if action = 0 then PMF.pure false else
    if action = 1 then PMF.pure true else Potential.supportFairLaw

def rank (chosen alternative : Fin 3) : Prop :=
  Potential.supportPreference () (law chosen) (law alternative)

theorem rank_reflexive (action : Fin 3) : rank action action := by
  classical
  exact (em (true ∈ (law action).support)).elim Or.inl Or.inr

theorem rank_total (chosen alternative : Fin 3) :
    rank chosen alternative ∨ rank alternative chosen := by
  classical
  by_cases supported : true ∈ (law chosen).support
  · exact Or.inl (Or.inl supported)
  · exact Or.inr (Or.inr supported)

theorem rank_transitive (a b c : Fin 3) (hab : rank a b) (hbc : rank b c) : rank a c := by
  rcases hab with ha | hb
  · exact Or.inl ha
  · rcases hbc with hb' | hc
    · exact (hb hb').elim
    · exact Or.inr hc

def choices : Finset (Fin 3) → Set (Fin 3) := FiniteChoice.best rank

theorem choices_consistent :
    FiniteChoice.Feasible choices ∧ FiniteChoice.Nonempty choices ∧
      FiniteChoice.WeakAxiom choices :=
  (FiniteChoice.rationalizable_iff choices).1
    ⟨rank, rank_total, rank_transitive, fun _ => rfl⟩

@[reducible]
def signature : GameSignature Unit where
  Strategy _ := Fin 3
  Outcome := Bool

@[reducible]
def form : GameForm Unit where
  sig := signature
  play profile := law (profile ())

def profile : Profile signature := fun _ => 0

/-- The observed menu includes a lottery response, not just point masses on
which the possibility preference happens to agree with a binary utility. -/
theorem selected_iff_bestResponse (candidate : Fin 3) :
    candidate ∈ choices Finset.univ ↔
      IsBestResponse form Potential.supportPreference () profile candidate :=
  (isBestResponse_iff_mem_best form Potential.supportPreference () profile candidate).symm

/-- No real expected utility even reproduces the comparisons among these
three observed action laws. -/
theorem comparisons_not_expectedUtility :
    ¬ ∃ candidate : Bool → Unit → ℝ,
      ∀ a b, rank a b ↔ euPreference candidate () (law a) (law b) := by
  rintro ⟨candidate, represents⟩
  have hnot : ¬ euPreference candidate () (PMF.pure false) (PMF.pure true) := by
    intro hcomparison
    have hbad := (represents 0 1).mpr (by simpa [law] using hcomparison)
    simp [rank, law, Potential.supportPreference] at hbad
  have hnotBound := (euPreference_iff candidate () (PMF.pure false) (PMF.pure true)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)).not.mp hnot
  have hpossibility : rank 2 1 := by
    simpa [rank, law] using
      (show Potential.supportPreference () Potential.supportFairLaw (PMF.pure true) from
        Or.inl Potential.true_mem_supportFairLaw)
  have hfair : euPreference candidate () Potential.supportFairLaw (PMF.pure true) := by
    simpa [law] using (represents 2 1).mp hpossibility
  have hfairBound :=
    (euPreference_iff candidate () Potential.supportFairLaw (PMF.pure true)
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)).mp hfair
  have hmix := expectedUtility_mix candidate () (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure true) (PMF.pure false)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  dsimp only [Potential.supportFairLaw] at hfairBound
  rw [hmix] at hfairBound
  simp only [expectedUtility_pure] at hnotBound hfairBound
  linarith

/-- Binary menus reveal enough of the observed choice correspondence to
exclude every real expected-utility representation of that correspondence. -/
theorem choices_not_expectedUtility :
    ¬ ∃ candidate : Bool → Unit → ℝ,
      ∀ menu, choices menu =
        FiniteChoice.best (fun a b => euPreference candidate () (law a) (law b)) menu := by
  rintro ⟨candidate, represents⟩
  apply comparisons_not_expectedUtility
  refine ⟨candidate, fun a b => ?_⟩
  have equal : choices =
      FiniteChoice.best (fun a b => euPreference candidate () (law a) (law b)) :=
    funext represents
  have revealed_equal : FiniteChoice.revealed choices a b ↔
      FiniteChoice.revealed
        (FiniteChoice.best (fun a b => euPreference candidate () (law a) (law b))) a b := by
    rw [equal]
  have numerical_reflexive (a : Fin 3) : euPreference candidate () (law a) (law a) :=
    euPreference_reflexive candidate
      (fun _ _ => hasExpectation_of_payoffIntegrable
        (payoffIntegrable_of_finite _ _)) () (law a)
  exact (FiniteChoice.revealed_best rank_reflexive a b).symm.trans
    (revealed_equal.trans (FiniteChoice.revealed_best numerical_reflexive a b))

end GameTheory.Tests.LotteryChoice
