/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.SourceInterfaces

/-!
# Faithful Q/non-Q LCP classification gate

The gate is ordered by strategic strength and by the audited source scopes:

1. the proved Never branch;
2. an ordinary branch terminating almost surely in the first stage;
3. the simple stationary source branches (all corrected-normal players
   deleted, or a homogeneous normalized LCP solution);
4. the ordinary standard-non-Q branch on the corrected normal-player matrix;
5. the continuous-path branch, using projective Q-bar on the full normalized
   matrix; and
6. the residual hard class.

Every branch after the first explicitly records failure of the preceding
simple cases.  The residual is not abbreviated as "Q but not Q-bar" without
qualification: its normal-player matrix is standard Q, its full normalized
matrix is not projective Q-bar, and the Never, instant, all-abnormal, and
homogeneous cases have all been removed.

The corrected normal-player recursion is not silently attributed to the
printed Solan--Solan statement.  Strategic conclusions using it require the
explicit `SolanSolanDistinctWitnessRepairInterface`.

Ordinary behavior profiles, continuous absorption paths, and
sunspot/public-correlation equilibria remain different conclusion types.
Ordinary normalization transport is proved concretely; transport of abstract
continuous and sunspot predicates requires an explicit translation-invariance
hypothesis.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The already proved all-Continue/Never case. -/
def NeverBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  IsQuittingZeroSolo reward

/-- The ordered instant branch: Never has failed, and ordinary approximate
equilibria terminate almost surely in the first stage. -/
structure InstantBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop where
  not_never : ¬NeverBranch reward
  instant : HasOrdinaryInstantApproximateEquilibria reward

/-- The ordered simple stationary branch.  It records failure of Never and of
the instant branch before exposing the corrected all-abnormal or homogeneous
LCP reason. -/
structure SimpleStationaryBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop where
  not_never : ¬NeverBranch reward
  no_instant : ¬HasOrdinaryInstantApproximateEquilibria reward
  reason :
    AllPlayersAbnormal (normalizedSoloMatrix reward) ∨
      (HasNormalPlayers (normalizedSoloMatrix reward) ∧
        HasHomogeneousSimplexSolution
          (normalizedNormalPlayerMatrix reward))

/-- The ordered ordinary branch: after all simple cases fail, the corrected
normal-player matrix is not standard Q.  Under absence of the homogeneous
branch this is equivalent to failure of the source's projective Q convention. -/
structure OrdinaryNonQBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop where
  not_never : ¬NeverBranch reward
  no_instant : ¬HasOrdinaryInstantApproximateEquilibria reward
  normal_nonempty : HasNormalPlayers (normalizedSoloMatrix reward)
  no_homogeneous : ¬HasHomogeneousSimplexSolution
    (normalizedNormalPlayerMatrix reward)
  normal_not_standardQ : ¬IsStandardQMatrix
    (normalizedNormalPlayerMatrix reward)

/-- The ordered continuous-path branch: the corrected normal-player matrix is
on its standard-Q side and the full normalized matrix satisfies AGKRS's
projective Q-bar condition. -/
structure ContinuousPathBranch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop where
  not_never : ¬NeverBranch reward
  no_instant : ¬HasOrdinaryInstantApproximateEquilibria reward
  normal_nonempty : HasNormalPlayers (normalizedSoloMatrix reward)
  no_homogeneous : ¬HasHomogeneousSimplexSolution
    (normalizedNormalPlayerMatrix reward)
  normal_standardQ : IsStandardQMatrix
    (normalizedNormalPlayerMatrix reward)
  full_projectiveQBar : IsProjectiveQBarMatrix
    (normalizedSoloMatrix reward)

/-- **Precise residual hard class.**  Every preceding simple or ordinary
branch has failed, the corrected normal-player matrix is standard Q, and the
full normalized matrix is not projective Q-bar. -/
structure ResidualHardClass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop where
  not_never : ¬NeverBranch reward
  no_instant : ¬HasOrdinaryInstantApproximateEquilibria reward
  normal_nonempty : HasNormalPlayers (normalizedSoloMatrix reward)
  no_homogeneous : ¬HasHomogeneousSimplexSolution
    (normalizedNormalPlayerMatrix reward)
  normal_standardQ : IsStandardQMatrix
    (normalizedNormalPlayerMatrix reward)
  not_full_projectiveQBar : ¬IsProjectiveQBarMatrix
    (normalizedSoloMatrix reward)

/-- The standard-Q side of the corrected normal-player split, without a claim
about ordinary, continuous, or sunspot strategies. -/
structure StandardQSide
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop where
  normal_nonempty : HasNormalPlayers (normalizedSoloMatrix reward)
  no_homogeneous : ¬HasHomogeneousSimplexSolution
    (normalizedNormalPlayerMatrix reward)
  normal_standardQ : IsStandardQMatrix
    (normalizedNormalPlayerMatrix reward)

/-- Forget the full-matrix Q-bar fact and retain the normal-core Q side. -/
def ContinuousPathBranch.toStandardQSide
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (h : ContinuousPathBranch reward) : StandardQSide reward where
  normal_nonempty := h.normal_nonempty
  no_homogeneous := h.no_homogeneous
  normal_standardQ := h.normal_standardQ

/-- Forget the full-matrix Q-bar failure and retain the normal-core Q side. -/
def ResidualHardClass.toStandardQSide
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (h : ResidualHardClass reward) : StandardQSide reward where
  normal_nonempty := h.normal_nonempty
  no_homogeneous := h.no_homogeneous
  normal_standardQ := h.normal_standardQ

/-- **Faithful ordered algebraic gate.**  Every finite quitting reward table
lies in one explicitly scoped branch.  This theorem is pure classification:
it does not instantiate either external strategic source interface. -/
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
    by_cases hinstant : HasOrdinaryInstantApproximateEquilibria reward
    · exact Or.inl
        { not_never := hnever
          instant := hinstant }
    · right
      by_cases hnormal : HasNormalPlayers (normalizedSoloMatrix reward)
      · by_cases hhomogeneous : HasHomogeneousSimplexSolution
          (normalizedNormalPlayerMatrix reward)
        · exact Or.inl
            { not_never := hnever
              no_instant := hinstant
              reason := Or.inr ⟨hnormal, hhomogeneous⟩ }
        · right
          by_cases hstandard : IsStandardQMatrix
              (normalizedNormalPlayerMatrix reward)
          · right
            by_cases hqbar : IsProjectiveQBarMatrix
                (normalizedSoloMatrix reward)
            · exact Or.inl
                { not_never := hnever
                  no_instant := hinstant
                  normal_nonempty := hnormal
                  no_homogeneous := hhomogeneous
                  normal_standardQ := hstandard
                  full_projectiveQBar := hqbar }
            · exact Or.inr
                { not_never := hnever
                  no_instant := hinstant
                  normal_nonempty := hnormal
                  no_homogeneous := hhomogeneous
                  normal_standardQ := hstandard
                  not_full_projectiveQBar := hqbar }
          · exact Or.inl
              { not_never := hnever
                no_instant := hinstant
                normal_nonempty := hnormal
                no_homogeneous := hhomogeneous
                normal_not_standardQ := hstandard }
      · have habnormal :
          AllPlayersAbnormal (normalizedSoloMatrix reward) :=
          (allPlayersAbnormal_iff_not_hasNormalPlayers
            (normalizedSoloMatrix reward)).2 hnormal
        exact Or.inl
          { not_never := hnever
            no_instant := hinstant
            reason := Or.inl habnormal }

/-- AGKRS's normalized-table conclusion for the continuous branch. -/
theorem normalizedContinuous_of_continuousPathBranch
    (ContinuousEquilibrium : QuittingPayoffTable ι → Prop)
    (agkrs : AGKRSContinuousSourceInterface ContinuousEquilibrium)
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hcontinuous : ContinuousPathBranch reward) :
    ContinuousEquilibrium (normalizedQuittingPayoffTable reward) :=
  agkrs.continuous_of_projectiveQBar reward
    hcontinuous.full_projectiveQBar

/-- Transport AGKRS's normalized continuous conclusion back to the repository
payoff table, under a separately supplied semantic translation theorem. -/
theorem continuous_of_continuousPathBranch
    (ContinuousEquilibrium : QuittingPayoffTable ι → Prop)
    (continuousTranslation :
      IsQuittingPayoffTranslationInvariant ContinuousEquilibrium)
    (agkrs : AGKRSContinuousSourceInterface ContinuousEquilibrium)
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hcontinuous : ContinuousPathBranch reward) :
    ContinuousEquilibrium (repositoryQuittingPayoffTable reward) :=
  (translationInvariant_normalized_iff_repository
    ContinuousEquilibrium continuousTranslation reward).mp
      (normalizedContinuous_of_continuousPathBranch
        ContinuousEquilibrium agkrs hcontinuous)

/-- Strategic version of the ordered gate after supplying the two narrowly
scoped source interfaces and the continuous predicate's translation theorem.
Ordinary profiles and continuous paths remain separate conclusions. -/
theorem faithful_q_nonQ_lcp_gate_with_source_conclusions
    (SunspotApproximateEquilibria : QuittingPayoffTable ι → Prop)
    (ContinuousEquilibrium : QuittingPayoffTable ι → Prop)
    (continuousTranslation :
      IsQuittingPayoffTranslationInvariant ContinuousEquilibrium)
    (solanSolan :
      SolanSolanDistinctWitnessRepairInterface
        SunspotApproximateEquilibria)
    (agkrs : AGKRSContinuousSourceInterface ContinuousEquilibrium)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (NeverBranch reward ∧ HasOrdinaryApproximateEquilibria reward) ∨
      (InstantBranch reward ∧ HasOrdinaryApproximateEquilibria reward) ∨
      (SimpleStationaryBranch reward ∧
        HasOrdinaryStationaryApproximateEquilibria reward) ∨
      (OrdinaryNonQBranch reward ∧
        HasOrdinaryStationaryApproximateEquilibria reward) ∨
      (ContinuousPathBranch reward ∧
        ContinuousEquilibrium (repositoryQuittingPayoffTable reward)) ∨
      ResidualHardClass reward := by
  rcases faithful_q_nonQ_lcp_gate reward with
      hnever | hinstant | hsimple | hnonQ | hcontinuous | hresidual
  · exact Or.inl ⟨hnever,
      hasOrdinaryApproximateEquilibria_of_zeroSolo hnever⟩
  · exact Or.inr (Or.inl ⟨hinstant,
      hasOrdinaryApproximateEquilibria_of_instant hinstant.instant⟩)
  · right; right; left
    refine ⟨hsimple, ?_⟩
    rcases hsimple.reason with habnormal | ⟨hnormal, hhomogeneous⟩
    · exact
        (hasNormalizedOrdinaryStationaryApproximateEquilibria_iff_original
          reward).mp
            (solanSolan.allAbnormal_stationary reward habnormal)
    · exact
        (hasNormalizedOrdinaryStationaryApproximateEquilibria_iff_original
          reward).mp
            (solanSolan.homogeneous_stationary reward hnormal hhomogeneous)
  · right; right; right; left
    refine ⟨hnonQ, ?_⟩
    exact
      (hasNormalizedOrdinaryStationaryApproximateEquilibria_iff_original
        reward).mp
          (solanSolan.nonQ_stationary reward hnonQ.normal_nonempty
            hnonQ.no_homogeneous hnonQ.normal_not_standardQ)
  · right; right; right; right; left
    exact ⟨hcontinuous,
      continuous_of_continuousPathBranch ContinuousEquilibrium
        continuousTranslation agkrs hcontinuous⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hresidual))))

/-- The source's normalized-table sunspot conclusion on the corrected
standard-Q side. -/
theorem normalizedSunspot_of_standardQSide
    (SunspotApproximateEquilibria : QuittingPayoffTable ι → Prop)
    (solanSolan :
      SolanSolanDistinctWitnessRepairInterface
        SunspotApproximateEquilibria)
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hQ : StandardQSide reward) :
    SunspotApproximateEquilibria (normalizedQuittingPayoffTable reward) :=
  solanSolan.q_sunspot reward hQ.normal_nonempty hQ.no_homogeneous
    hQ.normal_standardQ

/-- Transport the source's sunspot/public-correlation conclusion back to the
repository payoff table.  This remains separate from every ordinary strategy
conclusion. -/
theorem sunspot_of_standardQSide
    (SunspotApproximateEquilibria : QuittingPayoffTable ι → Prop)
    (sunspotTranslation :
      IsQuittingPayoffTranslationInvariant SunspotApproximateEquilibria)
    (solanSolan :
      SolanSolanDistinctWitnessRepairInterface
        SunspotApproximateEquilibria)
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hQ : StandardQSide reward) :
    SunspotApproximateEquilibria (repositoryQuittingPayoffTable reward) :=
  (translationInvariant_normalized_iff_repository
    SunspotApproximateEquilibria sunspotTranslation reward).mp
      (normalizedSunspot_of_standardQSide
        SunspotApproximateEquilibria solanSolan hQ)

/-- The continuous-path branch also lies on the corrected standard-Q sunspot
side, but the two conclusions are not identified. -/
theorem sunspot_of_continuousPathBranch
    (SunspotApproximateEquilibria : QuittingPayoffTable ι → Prop)
    (sunspotTranslation :
      IsQuittingPayoffTranslationInvariant SunspotApproximateEquilibria)
    (solanSolan :
      SolanSolanDistinctWitnessRepairInterface
        SunspotApproximateEquilibria)
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hcontinuous : ContinuousPathBranch reward) :
    SunspotApproximateEquilibria (repositoryQuittingPayoffTable reward) :=
  sunspot_of_standardQSide SunspotApproximateEquilibria sunspotTranslation
    solanSolan hcontinuous.toStandardQSide

/-- The residual hard class likewise has only the separately typed source
sunspot conclusion; this does not solve it in ordinary strategies. -/
theorem sunspot_of_residualHardClass
    (SunspotApproximateEquilibria : QuittingPayoffTable ι → Prop)
    (sunspotTranslation :
      IsQuittingPayoffTranslationInvariant SunspotApproximateEquilibria)
    (solanSolan :
      SolanSolanDistinctWitnessRepairInterface
        SunspotApproximateEquilibria)
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hresidual : ResidualHardClass reward) :
    SunspotApproximateEquilibria (repositoryQuittingPayoffTable reward) :=
  sunspot_of_standardQSide SunspotApproximateEquilibria sunspotTranslation
    solanSolan hresidual.toStandardQSide

end QuittingLCPClassification
end GameTheory
