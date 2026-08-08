/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.SourceInterfaces

/-!
# Faithful Q/non-Q LCP classification gate

The gate is ordered by strategic strength and by the exact source scopes:

1. the proved Never branch;
2. an ordinary sure-first-stage branch;
3. the simple stationary source branches (all players abnormal, or a
   homogeneous normalized LCP solution);
4. the ordinary standard-non-Q branch on the recursively normal matrix;
5. the continuous-path branch, using projective Q-bar on the full normalized
   matrix; and
6. the residual hard class.

The residual is not abbreviated as "Q but not Q-bar" without qualification.
It records that the *normal-player matrix* is standard Q, while the *full
matrix* fails AGKRS's weaker projective Q-bar condition, after all preceding
simple cases have been excluded.

A second theorem maps the algebraic gate through audited source interfaces.
Its ordinary and continuous conclusions remain different disjuncts.  The
standard-Q sunspot conclusion is exported only by separate theorems and is
never retyped as an ordinary equilibrium.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The already proved all-continue/Never case. -/
def NeverBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  IsQuittingZeroSolo reward

/-- An ordinary approximate-equilibrium family terminating surely at the first
stage through at least one player. -/
def InstantBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  HasOrdinaryInstantApproximateEquilibria reward

/-- The two simple stationary reasons preceding Theorem 2.11's matrix split. -/
def SimpleStationaryBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  AllPlayersAbnormal (normalizedSoloMatrix reward) ∨
    (HasNormalPlayers (normalizedSoloMatrix reward) ∧
      HasHomogeneousSimplexSolution
        (normalizedNormalPlayerMatrix reward))

/-- The ordinary Solan--Solan branch: standard non-Q on the recursively normal
matrix, under the literal Theorem 2.11 side conditions. -/
def OrdinaryNonQBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  HasNormalPlayers (normalizedSoloMatrix reward) ∧
    ¬HasHomogeneousSimplexSolution
      (normalizedNormalPlayerMatrix reward) ∧
    ¬IsStandardQMatrix (normalizedNormalPlayerMatrix reward)

/-- The continuous-path branch: after the ordinary standard-Q split, the full
normalized matrix satisfies AGKRS's projective Q-bar condition. -/
def ContinuousPathBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  HasNormalPlayers (normalizedSoloMatrix reward) ∧
    ¬HasHomogeneousSimplexSolution
      (normalizedNormalPlayerMatrix reward) ∧
    IsStandardQMatrix (normalizedNormalPlayerMatrix reward) ∧
    IsProjectiveQBarMatrix (normalizedSoloMatrix reward)

/-- **Precise residual hard class.**  The simple ordinary cases are absent,
the recursively normal matrix is standard Q, and the full normalized matrix
is not projective Q-bar. -/
structure ResidualHardClass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop where
  not_never : ¬NeverBranch reward
  not_instant : ¬InstantBranch reward
  normal_nonempty : HasNormalPlayers (normalizedSoloMatrix reward)
  no_homogeneous : ¬HasHomogeneousSimplexSolution
    (normalizedNormalPlayerMatrix reward)
  normal_standardQ : IsStandardQMatrix
    (normalizedNormalPlayerMatrix reward)
  not_full_projectiveQBar : ¬IsProjectiveQBarMatrix
    (normalizedSoloMatrix reward)

/-- The standard-Q side after all simple stationary source branches have been
removed. -/
def StandardQSide
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  HasNormalPlayers (normalizedSoloMatrix reward) ∧
    ¬HasHomogeneousSimplexSolution
      (normalizedNormalPlayerMatrix reward) ∧
    IsStandardQMatrix (normalizedNormalPlayerMatrix reward)

/-- **Faithful algebraic gate.**  Every finite quitting reward table lies in
one explicitly scoped branch.  This theorem is pure classification: it does
not import either external strategic theorem. -/
theorem faithful_q_nonQ_lcp_gate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    NeverBranch reward ∨
      InstantBranch reward ∨
      SimpleStationaryBranch reward ∨
      OrdinaryNonQBranch reward ∨
      ContinuousPathBranch reward ∨
      ResidualHardClass reward := by
  classical
  by_cases hnever : NeverBranch reward
  · exact Or.inl hnever
  · right
    by_cases hinstant : InstantBranch reward
    · exact Or.inl hinstant
    · right
      by_cases hnormal : HasNormalPlayers (normalizedSoloMatrix reward)
      · by_cases hhomogeneous : HasHomogeneousSimplexSolution
          (normalizedNormalPlayerMatrix reward)
        · exact Or.inl (Or.inr ⟨hnormal, hhomogeneous⟩)
        · right
          by_cases hstandard : IsStandardQMatrix
              (normalizedNormalPlayerMatrix reward)
          · right
            by_cases hqbar : IsProjectiveQBarMatrix
                (normalizedSoloMatrix reward)
            · exact Or.inl ⟨hnormal, hhomogeneous, hstandard, hqbar⟩
            · exact Or.inr
                { not_never := hnever
                  not_instant := hinstant
                  normal_nonempty := hnormal
                  no_homogeneous := hhomogeneous
                  normal_standardQ := hstandard
                  not_full_projectiveQBar := hqbar }
          · exact Or.inl ⟨hnormal, hhomogeneous, hstandard⟩
      · have habnormal :
          AllPlayersAbnormal (normalizedSoloMatrix reward) :=
          (allPlayersAbnormal_iff_not_hasNormalPlayers
            (normalizedSoloMatrix reward)).2 hnormal
        exact Or.inl (Or.inl habnormal)

/-- Strategic version of the gate after supplying the two audited source
interfaces.  Ordinary profiles and continuous paths remain separate. -/
theorem faithful_q_nonQ_lcp_gate_with_source_conclusions
    (SunspotApproximateEquilibria :
      ({S : Finset ι // S.Nonempty} → Payoff ι) → Prop)
    (ContinuousEquilibrium :
      ({S : Finset ι // S.Nonempty} → Payoff ι) → Prop)
    (solanSolan : SolanSolanSourceInterface SunspotApproximateEquilibria)
    (agkrs : AGKRSContinuousSourceInterface ContinuousEquilibrium)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (NeverBranch reward ∧ HasOrdinaryApproximateEquilibria reward) ∨
      (InstantBranch reward ∧ HasOrdinaryApproximateEquilibria reward) ∨
      (SimpleStationaryBranch reward ∧
        HasOrdinaryStationaryApproximateEquilibria reward) ∨
      (OrdinaryNonQBranch reward ∧
        HasOrdinaryStationaryApproximateEquilibria reward) ∨
      (ContinuousPathBranch reward ∧ ContinuousEquilibrium reward) ∨
      ResidualHardClass reward := by
  rcases faithful_q_nonQ_lcp_gate reward with
      hnever | hinstant | hsimple | hnonQ | hcontinuous | hresidual
  · exact Or.inl ⟨hnever,
      hasOrdinaryApproximateEquilibria_of_zeroSolo hnever⟩
  · exact Or.inr (Or.inl ⟨hinstant,
      hasOrdinaryApproximateEquilibria_of_instant hinstant⟩)
  · right; right; left
    refine ⟨hsimple, ?_⟩
    rcases hsimple with habnormal | ⟨hnormal, hhomogeneous⟩
    · exact solanSolan.allAbnormal_stationary reward habnormal
    · exact solanSolan.homogeneous_stationary reward hnormal hhomogeneous
  · right; right; right; left
    exact ⟨hnonQ,
      solanSolan.nonQ_stationary reward hnonQ.1 hnonQ.2.1 hnonQ.2.2⟩
  · right; right; right; right; left
    exact ⟨hcontinuous,
      agkrs.continuous_of_projectiveQBar reward hcontinuous.2.2.2⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hresidual))))

/-- The standard-Q side has the source's **sunspot/public-correlation**
conclusion.  It is intentionally separate from
`faithful_q_nonQ_lcp_gate_with_source_conclusions`. -/
theorem sunspot_of_standardQSide
    (SunspotApproximateEquilibria :
      ({S : Finset ι // S.Nonempty} → Payoff ι) → Prop)
    (solanSolan : SolanSolanSourceInterface SunspotApproximateEquilibria)
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hQ : StandardQSide reward) :
    SunspotApproximateEquilibria reward :=
  solanSolan.q_sunspot reward hQ.1 hQ.2.1 hQ.2.2

/-- In particular, the continuous-path branch also lies on the standard-Q
sunspot side, but the two conclusions are not identified. -/
theorem sunspot_of_continuousPathBranch
    (SunspotApproximateEquilibria :
      ({S : Finset ι // S.Nonempty} → Payoff ι) → Prop)
    (solanSolan : SolanSolanSourceInterface SunspotApproximateEquilibria)
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hcontinuous : ContinuousPathBranch reward) :
    SunspotApproximateEquilibria reward :=
  sunspot_of_standardQSide SunspotApproximateEquilibria solanSolan
    ⟨hcontinuous.1, hcontinuous.2.1, hcontinuous.2.2.1⟩

/-- The residual hard class likewise has only the separately typed source
sunspot conclusion; this does not solve it in ordinary strategies. -/
theorem sunspot_of_residualHardClass
    (SunspotApproximateEquilibria :
      ({S : Finset ι // S.Nonempty} → Payoff ι) → Prop)
    (solanSolan : SolanSolanSourceInterface SunspotApproximateEquilibria)
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hresidual : ResidualHardClass reward) :
    SunspotApproximateEquilibria reward :=
  sunspot_of_standardQSide SunspotApproximateEquilibria solanSolan
    ⟨hresidual.normal_nonempty, hresidual.no_homogeneous,
      hresidual.normal_standardQ⟩

end QuittingLCPClassification
end GameTheory
