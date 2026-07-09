/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Implementation

/-!
# k-implementation compilation tests

This module keeps the implementation examples and counterexamples wired into the
test aggregate.
-/

namespace GameTheory

namespace KernelGame

namespace RegularAPITests

variable {ι : Type} [DecidableEq ι] [Fintype ι] [Nonempty ι]
variable {G : KernelGame ι}
variable [G.HasAdditiveSubsidyEU]
variable [∀ i, TopologicalSpace (G.Strategy i)]
variable [∀ i, CompactSpace (G.Strategy i)]
variable [∀ i, T1Space (G.Strategy i)]

example (husc : G.RegularOwnUpperSemicontinuous) (z : Profile G) :
    G.regularAnalyticImplPrice z = ∑ i, G.regularImplementationGap z i :=
  G.regularAnalyticImplPrice_singleton husc z

example [∀ i, Nonempty (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous) :
    G.undominatedProfiles.Nonempty :=
  husc.undominatedProfiles_nonempty

example (husc : G.RegularOwnUpperSemicontinuous)
    (i : ι) (s : G.Strategy i) :
    ∃ t : G.Strategy i, G.WeaklyDominates i t s ∧ G.IsUndominated i t :=
  husc.exists_undominated_dominator i s

example (husc : G.RegularOwnUpperSemicontinuous) (z : Profile G) :
    G.regularAnalyticImplPrice z = 0 ↔ G.IsNash z :=
  G.regularAnalyticImplPrice_singleton_eq_zero_iff_isNash husc z

example [∀ i, MetricSpace (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    G.regularAnalyticImplPrice z ∈ G.regularAnalyticImplementationCosts z :=
  G.regularAnalyticImplPrice_mem_analyticImplementationCosts_of_nondegenerate husc z hnd

example [∀ i, MetricSpace (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    {z : Profile G} (hnd : G.SingletonNondegenerate z) :
    (∃ V : Profile G → Payoff ι,
      G.RegularSelectionAdmissibleAt V z ∧
        G.IsKImplementation V ({z} : Set (Profile G)) 0) ↔
      G.IsNash z :=
  G.exists_zero_regularAdmissibleKImplementation_iff_isNash husc hnd

example [∀ i, MetricSpace (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    {z : Profile G} (hnd : G.SingletonNondegenerate z) :
    (∃ V : Profile G → Payoff ι,
      G.RegularAnalyticAdmissible V ∧
        G.IsKImplementation V ({z} : Set (Profile G)) 0) ↔
      G.IsNash z :=
  G.exists_zero_regularAnalyticKImplementation_iff_isNash husc hnd

end RegularAPITests

namespace SetPriceAPITests

variable {ι : Type} [DecidableEq ι] [Fintype ι]
variable {G : KernelGame ι}

example {O : Set (Profile G)} (hmem : G.implPrice O ∈ G.implementationCosts O) :
    G.implementationCosts O = Set.Ici (G.implPrice O) :=
  G.implementationCosts_eq_Ici_implPrice_of_mem hmem

example {O : Set (Profile G)} (hne : (G.implementationCosts O).Nonempty)
    {k : ℝ} (hk : G.implPrice O < k) :
    k ∈ G.implementationCosts O :=
  G.implementationCosts_mem_of_implPrice_lt hne hk

example {O : Set (Profile G)} (hO : O.Nonempty)
    (hmem : G.exactImplPrice O ∈ G.exactImplementationCosts O) :
    G.exactImplementationCosts O = Set.Ici (G.exactImplPrice O) :=
  G.exactImplementationCosts_eq_Ici_exactImplPrice_of_mem hO hmem

example {O : Set (Profile G)} (hne : (G.exactImplementationCosts O).Nonempty)
    {k : ℝ} (hk : G.exactImplPrice O < k) :
    k ∈ G.exactImplementationCosts O :=
  G.exactImplementationCosts_mem_of_exactImplPrice_lt hne hk

example {V : Profile G → Payoff ι} {O : Set (Profile G)}
    (h : G.IsExactImplementation V O) :
    G.IsRectangular O :=
  h.target_rectangular

example {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    {V : Profile G → Payoff ι} (h : sk.RealizedBy V) :
    G.IsExactImplementation V (G.rect S) :=
  h.isExactImplementation_rect

example {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    {br : sk.BranchCertificate} {V : Profile G → Payoff ι} (h : br.RealizedBy V) :
    sk.RealizedBy V :=
  h.to_realizedBy

example {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    {V : Profile G → Payoff ι} (h : sk.RealizedBy V) :
    ∃ br : sk.BranchCertificate, br.RealizedBy V :=
  h.exists_branchCertificate

example [Fintype (Profile G)] [Finite G.Outcome]
    {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    (br : sk.BranchCertificate)
    [Fintype (ExactDominanceSkeleton.BranchCertificate.WeakRow br)]
    [Fintype (ExactDominanceSkeleton.BranchCertificate.StrictRow br)]
    {k : ℝ} {x : G.PaymentVar → ℝ} :
    ExactDominanceSkeleton.BranchCertificate.Matrix.Feasible br k x ↔
      br.RealizedBy (G.vectorTransfer x) ∧
        ∀ σ : Profile G, σ ∈ G.rect S →
          (∑ i, G.vectorTransfer x σ i) ≤ k :=
  ExactDominanceSkeleton.BranchCertificate.Matrix.feasible_iff_realizedBy_vectorTransfer_and_cost br

example [Fintype (Profile G)] {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} {br : sk.BranchCertificate}
    [Fintype (ExactDominanceSkeleton.BranchCertificate.WeakRow br)]
    [Fintype (ExactDominanceSkeleton.BranchCertificate.StrictRow br)]
    {k l : ℝ} {x : G.PaymentVar → ℝ}
    (h : ExactDominanceSkeleton.BranchCertificate.Matrix.Feasible br k x) (hkl : k ≤ l) :
    ExactDominanceSkeleton.BranchCertificate.Matrix.Feasible br l x :=
  h.mono_budget hkl

example [Fintype (Profile G)] {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} {br : sk.BranchCertificate}
    [Fintype (ExactDominanceSkeleton.BranchCertificate.WeakRow br)]
    [Fintype (ExactDominanceSkeleton.BranchCertificate.StrictRow br)]
    {x : G.BudgetPaymentVar → ℝ}
    (h : ExactDominanceSkeleton.BranchCertificate.Matrix.BudgetFeasible br x) :
    ExactDominanceSkeleton.BranchCertificate.Matrix.Feasible br (G.budgetOfVector x)
      (G.paymentOfBudgetVector x) :=
  h.to_feasible

example [Fintype (Profile G)] {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} {br : sk.BranchCertificate}
    [Fintype (ExactDominanceSkeleton.BranchCertificate.WeakRow br)]
    [Fintype (ExactDominanceSkeleton.BranchCertificate.StrictRow br)]
    {k : ℝ} {x : G.PaymentVar → ℝ} (hS : (G.rect S).Nonempty)
    (h : ExactDominanceSkeleton.BranchCertificate.Matrix.Feasible br k x) :
    ∃ z : G.BudgetPaymentVar → ℝ,
      ExactDominanceSkeleton.BranchCertificate.Matrix.BudgetFeasible br z ∧
        G.budgetOfVector z = k ∧ G.paymentOfBudgetVector z = x :=
  h.exists_budgetFeasible hS

example [Fintype (Profile G)] {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} {br : sk.BranchCertificate}
    [Fintype (ExactDominanceSkeleton.BranchCertificate.WeakRow br)]
    [Fintype (ExactDominanceSkeleton.BranchCertificate.StrictRow br)]
    {k : ℝ} {x : G.PaymentVar → ℝ}
    (h : ExactDominanceSkeleton.BranchCertificate.Matrix.Feasible br k x) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ row : ExactDominanceSkeleton.BranchCertificate.StrictRow br,
        ε ≤ ExactDominanceSkeleton.BranchCertificate.Matrix.strictSlack br x row :=
  h.exists_pos_le_strictSlack

example [Fintype (Profile G)] {S : ∀ i, Set (G.Strategy i)}
    {sk : G.ExactDominanceSkeleton S} (br : sk.BranchCertificate)
    [Fintype (ExactDominanceSkeleton.BranchCertificate.WeakRow br)] {k : ℝ} :
    (¬ ∃ x : G.PaymentVar → ℝ,
      Math.LinearProgramming.MinPrimalFeasible
        (ExactDominanceSkeleton.BranchCertificate.Matrix.weakA br)
        (ExactDominanceSkeleton.BranchCertificate.Matrix.weakB br k) x) ↔
      ∃ y : ExactDominanceSkeleton.BranchCertificate.WeakRow br → ℝ,
        Math.LinearProgramming.Nonnegative y ∧
          (∀ q : G.PaymentVar,
            Math.LinearProgramming.colEval
              (ExactDominanceSkeleton.BranchCertificate.Matrix.weakA br) y q ≤ 0) ∧
            0 < Math.LinearProgramming.dot
              (ExactDominanceSkeleton.BranchCertificate.Matrix.weakB br k) y :=
  open ExactDominanceSkeleton.BranchCertificate.Matrix in
    not_exists_weakFeasible_iff_exists_dual_certificate br

example {S : ∀ i, Set (G.Strategy i)} {sk : G.ExactDominanceSkeleton S}
    {V : Profile G → Payoff ι} {k : ℝ}
    (h : sk.RealizedBy V)
    (hcost : ∀ σ : Profile G, σ ∈ G.rect S → (∑ i, V σ i) ≤ k) :
    G.IsExactKImplementation V (G.rect S) k :=
  h.isExactKImplementation_rect hcost

example {S : ∀ i, Set (G.Strategy i)} (hS : (G.rect S).Nonempty) :
    G.skeletonExactImplementationCosts S =
      G.exactImplementationCosts (G.rect S) :=
  G.skeletonExactImplementationCosts_eq_exactImplementationCosts_rect hS

example {S : ∀ i, Set (G.Strategy i)} :
    G.branchSkeletonExactImplementationCosts S =
      G.skeletonExactImplementationCosts S :=
  G.branchSkeletonExactImplementationCosts_eq_skeletonExactImplementationCosts S

example {S : ∀ i, Set (G.Strategy i)} (hS : (G.rect S).Nonempty) :
    G.branchSkeletonExactImplementationCosts S =
      G.exactImplementationCosts (G.rect S) :=
  G.branchSkeletonExactImplementationCosts_eq_exactImplementationCosts_rect hS

example {S : ∀ i, Set (G.Strategy i)} (hS : (G.rect S).Nonempty) :
    G.skeletonExactImplPrice S = G.exactImplPrice (G.rect S) :=
  G.skeletonExactImplPrice_eq_exactImplPrice_rect hS

example {S : ∀ i, Set (G.Strategy i)} :
    G.branchSkeletonExactImplPrice S = G.skeletonExactImplPrice S :=
  G.branchSkeletonExactImplPrice_eq_skeletonExactImplPrice S

example [∀ i, Fintype (G.Strategy i)] [Fintype (Profile G)] [Finite G.Outcome]
    {S : ∀ i, Set (G.Strategy i)} :
    G.branchMatrixExactImplementationCosts S =
      G.branchSkeletonExactImplementationCosts S :=
  G.branchMatrixExactImplementationCosts_eq_branchSkeletonExactImplementationCosts S

example [∀ i, Fintype (G.Strategy i)] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)} (hS : (G.rect S).Nonempty) :
    G.branchBudgetLPExactImplementationCosts S =
      G.branchMatrixExactImplementationCosts S :=
  G.branchBudgetLPExactImplementationCosts_eq_branchMatrixExactImplementationCosts hS

example [∀ i, Fintype (G.Strategy i)] [Fintype (Profile G)] [Finite G.Outcome]
    {S : ∀ i, Set (G.Strategy i)} (hS : (G.rect S).Nonempty) :
    G.branchBudgetLPExactImplementationCosts S =
      G.exactImplementationCosts (G.rect S) :=
  G.branchBudgetLPExactImplementationCosts_eq_exactImplementationCosts_rect hS

example [∀ i, Fintype (G.Strategy i)] [Fintype (Profile G)] [Finite G.Outcome]
    {S : ∀ i, Set (G.Strategy i)} :
    G.branchMatrixExactImplPrice S = G.branchSkeletonExactImplPrice S :=
  G.branchMatrixExactImplPrice_eq_branchSkeletonExactImplPrice S

example [∀ i, Fintype (G.Strategy i)] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)} (hS : (G.rect S).Nonempty) :
    G.branchBudgetLPExactImplPrice S = G.branchMatrixExactImplPrice S :=
  G.branchBudgetLPExactImplPrice_eq_branchMatrixExactImplPrice hS

example {S : ∀ i, Set (G.Strategy i)} (hS : (G.rect S).Nonempty) :
    G.branchSkeletonExactImplPrice S = G.exactImplPrice (G.rect S) :=
  G.branchSkeletonExactImplPrice_eq_exactImplPrice_rect hS

example [∀ i, Fintype (G.Strategy i)] [Fintype (Profile G)] [Finite G.Outcome]
    {S : ∀ i, Set (G.Strategy i)} (hS : (G.rect S).Nonempty) :
    G.branchMatrixExactImplPrice S = G.exactImplPrice (G.rect S) :=
  G.branchMatrixExactImplPrice_eq_exactImplPrice_rect hS

example [∀ i, Fintype (G.Strategy i)] [Fintype (Profile G)] [Finite G.Outcome]
    {S : ∀ i, Set (G.Strategy i)} (hS : (G.rect S).Nonempty) :
    G.branchBudgetLPExactImplPrice S = G.exactImplPrice (G.rect S) :=
  G.branchBudgetLPExactImplPrice_eq_exactImplPrice_rect hS

example [∀ i, Fintype (G.Strategy i)] [Fintype (Profile G)] [Finite G.Outcome]
    {S : ∀ i, Set (G.Strategy i)} (hS : (G.rect S).Nonempty)
    (hmem : G.branchMatrixExactImplPrice S ∈ G.branchMatrixExactImplementationCosts S) :
    G.branchMatrixExactImplementationCosts S = Set.Ici (G.branchMatrixExactImplPrice S) :=
  G.branchMatrixExactImplementationCosts_eq_Ici_branchMatrixExactImplPrice_of_mem hS hmem

example [∀ i, Fintype (G.Strategy i)] [Fintype (Profile G)] [Finite G.Outcome]
    {S : ∀ i, Set (G.Strategy i)} (hS : (G.rect S).Nonempty)
    (hmem :
      G.branchBudgetLPExactImplPrice S ∈ G.branchBudgetLPExactImplementationCosts S) :
    G.branchBudgetLPExactImplementationCosts S = Set.Ici (G.branchBudgetLPExactImplPrice S) :=
  G.branchBudgetLPExactImplementationCosts_eq_Ici_branchBudgetLPExactImplPrice_of_mem
    hS hmem

example [∀ i, Fintype (G.Strategy i)] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)} {k l : ℝ}
    (hk : k ∈ G.branchMatrixExactImplementationCosts S) (hkl : k ≤ l) :
    l ∈ G.branchMatrixExactImplementationCosts S :=
  G.branchMatrixExactImplementationCosts_upward_closed hk hkl

example [∀ i, Fintype (G.Strategy i)] [Fintype (Profile G)]
    {S : ∀ i, Set (G.Strategy i)} {k l : ℝ}
    (hk : k ∈ G.branchBudgetLPExactImplementationCosts S) (hkl : k ≤ l) :
    l ∈ G.branchBudgetLPExactImplementationCosts S :=
  G.branchBudgetLPExactImplementationCosts_upward_closed hk hkl

end SetPriceAPITests

namespace ImplementationExamples

example :
    congestionGame.IsKImplementation congestionPromise
      ({congestionTarget} : Set (Profile congestionGame)) 0 :=
  congestionPromise_isZeroKImplementation

example :
    congestionGame.implPrice
      ({congestionTarget} : Set (Profile congestionGame)) = 0 :=
  congestionTarget_implPrice_eq_zero

example :
    congestionGame.IsNash congestionOtherNash ∧
      congestionOtherNash ≠ congestionTarget ∧
        congestionOtherNash ∉
          (congestionGame.subsidize congestionPromise).undominatedProfiles :=
  ⟨congestionOtherNash_isNash, congestionOtherNash_ne_target,
    congestionPromise_otherNash_not_undominated⟩

example :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      KernelGame.IsExactKImplementation
        (deviceTieGame.recommendationDevice deviceTieUniformLaw B hB).deviceGame
        (fun _ _ => 0)
        ({deviceTieGame.obedientDeviceStrategy} :
          Set (Profile
            (deviceTieGame.recommendationDevice deviceTieUniformLaw B hB).deviceGame)) 0 :=
  deviceTie_exists_strictRecommendationDevice_exactKImplementation

example :
    ¬ ∀ i (si : deviceTieGame.Strategy i),
      Math.ProbabilityMassFunction.pmfMass (μ := deviceTieDegenerateLaw)
        (fun θ : Profile deviceTieGame => θ i = si) ≠ 0 :=
  deviceTieDegenerateLaw_not_fullSupport

example (B : ℝ) (hB : 0 ≤ B) :
    ¬ ImplementationDevice.InterimWeaklyStrictlyDominantProfile
        (deviceTieGame.recommendationDevice deviceTieDegenerateLaw B hB)
        deviceTieGame.obedientDeviceStrategy :=
  deviceTieDegenerate_obedient_not_strictInterimDominantProfile B hB

example (B : ℝ) (hB : 0 ≤ B) :
    deviceTieDegenerateNullRuleProfile B hB ≠ deviceTieGame.obedientDeviceStrategy :=
  deviceTieDegenerateNullRuleProfile_ne_obedient B hB

example (B : ℝ) (hB : 0 ≤ B) :
    KernelGame.TransferClassProfileEquivalent
      (deviceTieGame.recommendationDevice deviceTieDegenerateLaw B hB).deviceGame
        ({fun _ _ => 0} :
          Set (Profile
            (deviceTieGame.recommendationDevice deviceTieDegenerateLaw B hB).deviceGame →
              Payoff (Fin 2)))
        (deviceTieDegenerateNullRuleProfile B hB)
        deviceTieGame.obedientDeviceStrategy :=
  deviceTieDegenerateNullRule_transferClassEquivalent_obedient B hB

example (B : ℝ) (hB : 0 ≤ B) :
    ¬ KernelGame.IsExactImplementation
        (deviceTieGame.recommendationDevice deviceTieDegenerateLaw B hB).deviceGame
        (fun _ _ => 0)
        ({deviceTieGame.obedientDeviceStrategy} :
          Set (Profile
            (deviceTieGame.recommendationDevice deviceTieDegenerateLaw B hB).deviceGame)) :=
  deviceTieDegenerate_zeroTransfer_not_exactSingletonImplementation B hB

namespace OverlappingRegretPaymentExample

example :
    game.recommendationPaymentImplPrice law = (4 / 3 : ℝ) :=
  recommendationPaymentImplPrice_eq_four_thirds

example :
    (4 / 3 : ℝ) ≤ game.recommendationPaymentImplPrice law :=
  four_thirds_le_recommendationPaymentImplPrice_by_weighted_certificate

example :
    Math.LinearProgramming.DualFeasible
      (game.recommendationPaymentLPA law)
      (fun _ : game.RecommendationPaymentLPCol => 0)
      lowerBoundRawDual :=
  lowerBoundRawDual_dualFeasible

example (k : ℝ) :
    Math.LinearProgramming.dualValue (game.recommendationPaymentLPb law k)
        lowerBoundRawDual =
      k - (4 / 3 : ℝ) :=
  lowerBoundRawDual_dualValue k

example :
    (4 / 3 : ℝ) ≤ game.recommendationPaymentImplPrice law :=
  four_thirds_le_recommendationPaymentImplPrice_by_raw_lp_certificate

example :
    game.maxConditionalSwapRegret law < game.recommendationPaymentImplPrice law ∧
      game.recommendationPaymentImplPrice law <
        game.maxSupportedPointwiseConditionalSwapRegret law :=
  recommendationPaymentImplPrice_strict_between_sandwich

end OverlappingRegretPaymentExample

namespace ExpectedDeviceEpsilonCounterexample

example :
    game.finiteExpectedDeviceImplPrice law ≤ (Fintype.card (Fin 2) : ℝ) * 1 ∧
      ¬ game.IsεCorrelatedEq 1 law :=
  finiteExpectedDeviceImplPrice_le_card_mul_one_and_not_isOneCorrelatedEq

end ExpectedDeviceEpsilonCounterexample

example :
    (0 : ℝ) ∉ onePlayerTieGame.implementationCosts
      ({onePlayerProfile false} : Set (Profile onePlayerTieGame)) :=
  onePlayerTie_zero_not_mem_implementationCosts

example :
    ¬ revealingZeroUtilityGame.IsEpsilonDifferentiallyPrivate 0 :=
  revealingZeroUtilityGame_not_zeroDifferentiallyPrivate

example (z : Profile revealingZeroUtilityGame) :
    revealingZeroUtilityGame.implPrice
      ({z} : Set (Profile revealingZeroUtilityGame)) = 0 :=
  revealingZeroUtilityGame_implPrice_singleton_eq_zero z

example :
    constantPrivateGame.IsEpsilonDifferentiallyPrivate 1 :=
  constantPrivateGame_oneDifferentiallyPrivate

example (z : Profile constantPrivateGame) :
    constantPrivateGame.implPrice ({z} : Set (Profile constantPrivateGame)) ≤
      (Fintype.card (Fin 1) : ℝ) * ((Real.exp 1 - 1) * 1) :=
  constantPrivateGame_implPrice_singleton_dp_bound z

example :
    mixedConverseGame.mixedExtension.IsKImplementation mixedConverseTransfer
      ({mixedConverseMixedTarget} : Set (Profile mixedConverseGame.mixedExtension)) 0 :=
  mixedConverseTransfer_isZeroKImplementation

example :
    ¬ mixedConverseGame.mixedExtension.IsNash mixedConverseMixedTarget :=
  mixedConverseMixedTarget_not_nash

example :
    mixedConverseGame.mixedExtension.implPrice
      ({mixedConverseMixedTarget} : Set (Profile mixedConverseGame.mixedExtension)) = 0 :=
  mixedConverse_implPrice_singleton_eq_zero

example :
    ¬ mixedConverseGame.MixedSelectionAdmissibleAt
      mixedConverseTransfer mixedConverseMixedTarget :=
  mixedConverseTransfer_not_selectionAdmissible

example :
    SelectionAdmissibleNotAnalyticExample.game.RegularSelectionAdmissibleAt
      SelectionAdmissibleNotAnalyticExample.spikeTransfer
      SelectionAdmissibleNotAnalyticExample.target :=
  SelectionAdmissibleNotAnalyticExample.spikeTransfer_selectionAdmissible

example :
    ¬ SelectionAdmissibleNotAnalyticExample.game.RegularAnalyticAdmissible
      SelectionAdmissibleNotAnalyticExample.spikeTransfer :=
  SelectionAdmissibleNotAnalyticExample.spikeTransfer_not_analyticAdmissible

example :
    (∀ σ i, 0 ≤ SelectionAdmissibleNotAnalyticExample.spikeTransfer σ i) ∧
      SelectionAdmissibleNotAnalyticExample.game.RegularSelectionAdmissibleAt
        SelectionAdmissibleNotAnalyticExample.spikeTransfer
        SelectionAdmissibleNotAnalyticExample.target ∧
        ¬ SelectionAdmissibleNotAnalyticExample.game.RegularAnalyticAdmissible
          SelectionAdmissibleNotAnalyticExample.spikeTransfer :=
  SelectionAdmissibleNotAnalyticExample.selectionAdmissible_and_not_analyticAdmissible

example :
    (∀ σ i, 0 ≤ MetricSelectionAdmissibleNotAnalyticExample.spikeTransfer σ i) ∧
      MetricSelectionAdmissibleNotAnalyticExample.game.RegularSelectionAdmissibleAt
        MetricSelectionAdmissibleNotAnalyticExample.spikeTransfer
        MetricSelectionAdmissibleNotAnalyticExample.target ∧
        ¬ MetricSelectionAdmissibleNotAnalyticExample.game.RegularAnalyticAdmissible
          MetricSelectionAdmissibleNotAnalyticExample.spikeTransfer :=
  MetricSelectionAdmissibleNotAnalyticExample.selectionAdmissible_and_not_analyticAdmissible

end ImplementationExamples

namespace OptimalPerturbationCounterexample

example :
    game.exactImplementationCosts target = Set.Ici (3 : ℝ) :=
  exactImplementationCosts_eq_Ici_three

example :
    game.exactImplPrice target = 3 :=
  exactImplPrice_eq_three

example :
    (∃ M e₀ e₁ : ℝ,
      game.IsExactKImplementation
        (game.optimalPerturbationTransfer rowTarget colTarget M e₀ e₁)
        target (e₀ + e₁) ∧ e₀ + e₁ = 5) ∧
      ∀ M e₀ e₁ : ℝ,
        game.IsExactImplementation
          (game.optimalPerturbationTransfer rowTarget colTarget M e₀ e₁) target →
          5 ≤ e₀ + e₁ :=
  optimalPerturbationFamily_minimum_cost_eq_five

example :
    game.exactImplPrice target = 3 ∧
      (∃ σ : Profile game,
        σ ∈ target ∧
          (∑ i : Fin 2, opTransfer σ i) = 5 ∧
            game.exactImplPrice target < (∑ i : Fin 2, opTransfer σ i)) :=
  op_algorithm_output_not_optimal_certificate

end OptimalPerturbationCounterexample

variable {ι : Type} {G : KernelGame ι}

example [DecidableEq ι] {b : Profile G}
    (hdom : ∀ i (c : G.Strategy i), G.WeaklyDominates i (b i) c) :
    G.undominatedProfiles =
      {σ : Profile G | ∀ i, G.UtilityEquivalent i (σ i) (b i)} :=
  G.undominatedProfiles_eq_utilityEquivalentClass_of_forall_weaklyDominates hdom

example [DecidableEq ι] {σ τ : Profile G}
    (h : ∀ i, G.UtilityEquivalent i (σ i) (τ i)) :
    σ ∈ G.undominatedProfiles ↔ τ ∈ G.undominatedProfiles :=
  G.undominatedProfiles_utilityEquivalent_iff h

example [DecidableEq ι] {C : Set (Profile G → Payoff ι)}
    {V : Profile G → Payoff ι} {O : Set (Profile G)}
    (h : G.IsImplementation V O) (hV : V ∈ C) :
    ∃ S : Set (Profile G), S.Nonempty ∧ S ⊆ O ∧
      ∀ σ ∈ S, ∀ τ : Profile G,
        G.TransferClassProfileEquivalent C σ τ → τ ∈ S :=
  h.exists_transferClassSaturated_subset hV

example [DecidableEq ι] {C : Set (Profile G → Payoff ι)}
    {V : Profile G → Payoff ι} {z τ : Profile G}
    (h : G.IsImplementation V ({z} : Set (Profile G))) (hV : V ∈ C)
    (hτz : G.TransferClassProfileEquivalent C τ z) :
    τ = z :=
  h.eq_of_transferClassProfileEquivalent_singleton hV hτz

example [DecidableEq ι] [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ) (z : Profile G) :
    G.implPrice ({z} : Set (Profile G)) =
      ∑ i, Finset.univ.sup' (Finset.univ_nonempty (α := G.Strategy i))
        (fun s : G.Strategy i => Φ (Function.update z i s) - Φ z) :=
  G.implPrice_singleton_eq_sum_potentialGaps hΦ z

example [DecidableEq ι] [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ) (z : Profile G) :
    G.implPrice ({z} : Set (Profile G)) ≤
      (Fintype.card ι : ℝ) *
        (Finset.univ.sup' (Finset.univ_nonempty (α := Profile G)) Φ - Φ z) :=
  G.implPrice_singleton_le_card_mul_potentialGap hΦ z

example [DecidableEq ι] [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ) (z : Profile G) :
    G.implPrice ({z} : Set (Profile G)) = 0 ↔
      ∀ i (s : G.Strategy i), Φ (Function.update z i s) ≤ Φ z :=
  G.implPrice_singleton_eq_zero_iff_potential_localMax hΦ z

example [DecidableEq ι] [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (p : Profile G.mixedExtension) :
    G.mixedAdmissibleImplPrice p =
      ∑ i, G.mixedImplementationGapAt p i p :=
  G.mixedAdmissibleImplPrice_singleton p

example [DecidableEq ι] [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (p : Profile G.mixedExtension) :
    G.mixedAdmissibleImplPrice p = 0 ↔ G.mixedExtension.IsNash p :=
  G.mixedAdmissibleImplPrice_singleton_eq_zero_iff_isNash p

example [DecidableEq ι] [Fintype ι] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {p : Profile G.mixedExtension} (hnd : G.MixedSingletonNondegenerate p) :
    (∃ V : Profile G.mixedExtension → Payoff ι,
      G.MixedSelectionAdmissibleAt V p ∧
        G.mixedExtension.IsKImplementation V ({p} : Set (Profile G.mixedExtension)) 0) ↔
      G.mixedExtension.IsNash p :=
  G.exists_zero_mixedAdmissibleKImplementation_iff_isNash hnd

example [DecidableEq ι] [Fintype ι] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {V : Profile G.mixedExtension → Payoff ι} {p : Profile G.mixedExtension}
    (h : G.MixedAnalyticAdmissible V) :
    G.MixedSelectionAdmissibleAt V p :=
  h.selectionAdmissible

example [DecidableEq ι] [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (p : Profile G.mixedExtension) :
    G.mixedAnalyticImplPrice p =
      ∑ i, G.mixedImplementationGapAt p i p :=
  G.mixedAnalyticImplPrice_singleton p

example [DecidableEq ι] [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (p : Profile G.mixedExtension) :
    G.mixedAnalyticImplPrice p = 0 ↔ G.mixedExtension.IsNash p :=
  G.mixedAnalyticImplPrice_singleton_eq_zero_iff_isNash p

example [DecidableEq ι] [Fintype ι] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    [∀ i, Finite (G.Strategy i)]
    {p : Profile G.mixedExtension} :
    (∃ V : Profile G.mixedExtension → Payoff ι,
      G.MixedAnalyticAdmissible V ∧
        G.mixedExtension.IsKImplementation V ({p} : Set (Profile G.mixedExtension)) 0) →
      G.mixedExtension.IsNash p :=
  G.isNash_of_exists_zero_mixedAnalyticKImplementation

example [DecidableEq ι] [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {ε U : ℝ} (hDP : G.IsEpsilonDifferentiallyPrivate ε) (hε : 0 ≤ ε)
    (hutil_nonneg : ∀ ω : G.Outcome, ∀ i : ι, 0 ≤ G.utility ω i)
    (hutil_le : ∀ ω : G.Outcome, ∀ i : ι, G.utility ω i ≤ U)
    (z : Profile G) :
    G.implPrice ({z} : Set (Profile G)) ≤
      (Fintype.card ι : ℝ) * ((Real.exp ε - 1) * U) :=
  G.implPrice_singleton_le_card_mul_dp_bound hDP hε hutil_nonneg hutil_le z

example [DecidableEq ι] [Fintype ι] [Nonempty ι] [Fintype G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {U : ℝ} (hU : 0 ≤ U)
    (hutil_nonneg : ∀ ω : G.Outcome, ∀ i : ι, 0 ≤ G.utility ω i)
    (hutil_le : ∀ ω : G.Outcome, ∀ i : ι, G.utility ω i ≤ U)
    (z : Profile G) :
    G.implPrice ({z} : Set (Profile G)) ≤
      U * G.singletonOutcomeVariationPrice z :=
  G.implPrice_singleton_le_mul_singletonOutcomeVariationPrice
    hU hutil_nonneg hutil_le z

example [DecidableEq ι] [Fintype ι] [Nonempty ι] [Fintype G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {U : ℝ} (hU : 0 ≤ U) (z : Profile G) :
    (G.outcomeVariationWitnessGame z U).implPrice
        ({(z : Profile (G.outcomeVariationWitnessGame z U))} :
          Set (Profile (G.outcomeVariationWitnessGame z U))) =
      U * G.singletonOutcomeVariationPrice z :=
  G.implPrice_singleton_outcomeVariationWitnessUtility hU z

example [DecidableEq ι] [Finite G.Outcome] {ε : ℝ} :
    G.IsEpsilonDifferentiallyPrivate ε ↔
      ∀ (i : ι) (σ : Profile G) (s : G.Strategy i) (u : G.Outcome → ℝ),
        (∀ ω, 0 ≤ u ω) →
          Math.Probability.expect (G.outcomeKernel (Function.update σ i s)) u -
              Math.Probability.expect (G.outcomeKernel σ) u ≤
            (Real.exp ε - 1) *
              Math.Probability.expect (G.outcomeKernel σ) u :=
  G.isEpsilonDifferentiallyPrivate_iff_expect_gain_le_exp_sub_one_mul_expect

example [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : M < B)
    (hfull : ∀ i (si : G.Strategy i),
      (G.recommendationDevice μ B hB).PositiveSignal i si)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    (G.recommendationDevice μ B hB).deviceGame.IsExactKImplementation
      (fun _ _ => 0)
      ({G.obedientDeviceStrategy} :
        Set (Profile (G.recommendationDevice μ B hB).deviceGame)) 0 :=
  G.recommendationDevice_obedient_zeroTransfer_exactKImplementation_of_eu_diameter_bound
    hce hB hdiam hbonus_weak hbonus_strict hfull hopponent

example [DecidableEq ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : M < B)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    (G.recommendationDevice μ B hB).deviceGame.undominatedProfiles =
      {b : Profile (G.recommendationDevice μ B hB).deviceGame |
        ∀ i (si : G.Strategy i),
          (G.recommendationDevice μ B hB).PositiveSignal i si → b i si = si} :=
  G.recommendationDevice_undominatedProfiles_eq_supported_obedient_class
    hce hB hdiam hbonus_weak hbonus_strict hopponent

example [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : M < B)
    (hfull : ∀ i (si : G.Strategy i),
      (G.recommendationDevice μ B hB).PositiveSignal i si)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    ∀ i (τ : PMF ((G.recommendationDevice μ B hB).deviceGame.Strategy i)),
      τ ≠ PMF.pure (G.obedientDeviceStrategy i) →
        KernelGame.WeaklyStrictlyDominates
          ((G.recommendationDevice μ B hB).deviceGame.mixedExtension)
          i (PMF.pure (G.obedientDeviceStrategy i)) τ :=
  G.recommendationDevice_obedient_mixedWeaklyStrictlyDominantProfile_of_eu_diameter_bound
    hce hB hdiam hbonus_weak hbonus_strict hfull hopponent

example [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ) :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.recommendationDevice μ B hB).InterimDominantExpectedKImplementsDistribution
        (G.obedientDeviceStrategy) μ 0 :=
  G.exists_recommendationDevice_interimDominantExpectedKImplementsDistribution hce

example [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, DecidableEq (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.regretRecommendationDevice μ B hB).InterimDominantExpectedKImplementsDistribution
        (G.obedientDeviceStrategy) μ
        (∑ i, G.maxSwapRegret μ i) :=
  G.exists_regretRecommendationDevice_interimDominantExpectedKImplDist μ

example [DecidableEq ι] [Fintype ι] {I : G.ImplementationDevice}
    [Finite (∀ i, I.Signal i)] [∀ i, Finite (I.Signal i)]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, DecidableEq (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    {b : ∀ i, I.Signal i → G.Strategy i} {μ : PMF (Profile G)} {k : ℝ}
    (h : I.InterimDominantExpectedKImplementsDistribution b μ k) :
    ∑ i, G.maxSwapRegret μ i ≤ k :=
  I.sum_maxSwapRegret_le_of_expectedKImplementation h

example [DecidableEq ι] [Fintype ι] {I : G.ImplementationDevice}
    [Finite (∀ i, I.Signal i)] [∀ i, Finite (I.Signal i)]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {b : ∀ i, I.Signal i → G.Strategy i} {μ : PMF (Profile G)} {k : ℝ}
    (h : I.InterimDominantExpectedKImplementsDistribution b μ k) :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.regretRecommendationDevice μ B hB).InterimDominantExpectedKImplementsDistribution
        (G.obedientDeviceStrategy) μ k :=
  G.exists_regretRecommendationDevice_expectedKImplDist_of_finiteDevice h

example [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.regretRecommendationDevice μ B hB).InterimDominantKImplementsDistribution
        (G.obedientDeviceStrategy) μ
        (G.maxSupportedPointwiseConditionalSwapRegret μ) :=
  G.exists_regretRecommendationDevice_interimDominantKImplDist μ

example [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.maxConditionalSwapRegret μ ≤
        G.recommendationDevicePointwiseImplPrice μ ∧
      G.recommendationDevicePointwiseImplPrice μ ≤
        G.maxSupportedPointwiseConditionalSwapRegret μ :=
  G.recommendationDevicePointwiseImplPrice_sandwich μ

example [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.maxConditionalSwapRegret μ ≤ G.finitePointwiseDeviceImplPrice μ ∧
      G.finitePointwiseDeviceImplPrice μ ≤
        G.recommendationDevicePointwiseImplPrice μ :=
  G.finitePointwiseDeviceImplPrice_sandwich μ

example [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {μ : PMF (Profile G)} {k : ℝ}
    (hk : k ∈ G.finitePointwiseDeviceImplementationCosts μ) :
    G.maxConditionalSwapRegret μ ≤ k :=
  G.maxConditionalSwapRegret_le_of_finitePointwiseDeviceCost hk

example [DecidableEq ι] [Fintype ι]
    [Finite (Profile G)] [Finite G.Outcome]
    {μ : PMF (Profile G)} {k : ℝ}
    (hk : k ∈ G.finitePointwiseDeviceImplementationCosts μ) :
    k ∈ G.recommendationPaymentImplementationCosts μ :=
  G.finitePointwiseDeviceCost_subset_recommendationPaymentCost hk

example [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G))
    (h :
      ∀ θ : Profile G, μ θ ≠ 0 →
        (∑ i, G.conditionalSwapRegret μ i (θ i)) ≤
          G.maxConditionalSwapRegret μ) :
    G.recommendationDevicePointwiseImplPrice μ =
      G.maxConditionalSwapRegret μ :=
  G.recommendationDevicePointwiseImplPrice_eq_maxConditionalSwapRegret_of_supported_sum_le
    μ h

example [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    (μ : PMF (Profile G)) :
    G.recommendationDevicePointwiseImplPrice μ =
      G.recommendationPaymentImplPrice μ :=
  G.recommendationDevicePointwiseImplPrice_eq_recommendationPaymentImplPrice μ

example [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.finitePointwiseDeviceImplPrice μ =
      G.recommendationPaymentImplPrice μ :=
  G.finitePointwiseDeviceImplPrice_eq_recommendationPaymentImplPrice μ

example [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.finitePointwiseDeviceImplPrice μ =
      G.recommendationDevicePointwiseImplPrice μ :=
  G.finitePointwiseDeviceImplPrice_eq_recommendationDevicePointwiseImplPrice μ

example [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, DecidableEq (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.finiteExpectedDeviceImplPrice μ = ∑ i, G.maxSwapRegret μ i :=
  G.finiteExpectedDeviceImplPrice_eq_sum_maxSwapRegret μ

example [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {μ : PMF (Profile G)} {ε : ℝ} (hε : G.IsεCorrelatedEq ε μ) :
    G.finiteExpectedDeviceImplPrice μ ≤ (Fintype.card ι : ℝ) * ε :=
  G.finiteExpectedDeviceImplPrice_le_card_mul_of_isεCorrelatedEq hε

example [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {μ : PMF (Profile G)} {ε : ℝ}
    (hprice : G.finiteExpectedDeviceImplPrice μ ≤ ε) :
    G.IsεCorrelatedEq ε μ :=
  G.isεCorrelatedEq_of_finiteExpectedDeviceImplPrice_le hprice

example [DecidableEq ι] [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (z : Profile G) :
    G.maxImplementationGap z ≤ G.implPrice ({z} : Set (Profile G)) ∧
      G.implPrice ({z} : Set (Profile G)) ≤
        (Fintype.card ι : ℝ) * G.maxImplementationGap z :=
  G.implPrice_singleton_linf_lone_sandwich z

example [DecidableEq ι] [Fintype ι]
    {μ : PMF (Profile G)} {k : ℝ}
    (hk : k ∈ G.recommendationPaymentImplementationCosts μ) :
    G.recommendationPaymentImplPrice μ ≤ k :=
  G.recommendationPaymentImplPrice_le_of_mem hk

example [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.maxConditionalSwapRegret μ ≤
        G.recommendationPaymentImplPrice μ ∧
      G.recommendationPaymentImplPrice μ ≤
        G.maxSupportedPointwiseConditionalSwapRegret μ :=
  G.recommendationPaymentImplPrice_sandwich μ

example [DecidableEq ι] [Fintype ι] [Fintype (Profile G)]
    {μ : PMF (Profile G)} {p : Profile G → Payoff ι} {k : ℝ} :
    Math.LinearProgramming.PrimalFeasible
        (G.recommendationPaymentLPA μ) (G.recommendationPaymentLPb μ k)
        (G.recommendationPaymentLPVector p) ↔
      G.RecommendationPaymentFeasible μ p k :=
  G.recommendationPaymentLPFeasible_iff

example [DecidableEq ι] [Fintype ι] [Fintype (Profile G)]
    [∀ i, Fintype (G.Strategy i)]
    {μ : PMF (Profile G)} {k : ℝ} {y : G.RecommendationPaymentLPRow → ℝ}
    (hy : Math.LinearProgramming.DualFeasible
      (G.recommendationPaymentLPA μ) (fun _ : G.RecommendationPaymentLPCol => 0) y)
    (hneg : Math.LinearProgramming.dualValue (G.recommendationPaymentLPb μ k) y < 0) :
    k ∉ G.recommendationPaymentImplementationCosts μ :=
  G.not_mem_recommendationPaymentImplementationCosts_of_dualValue_neg hy hneg

example [DecidableEq ι] [Fintype ι] [Fintype (Profile G)]
    [∀ i, Fintype (G.Strategy i)]
    {μ : PMF (Profile G)} {k : ℝ}
    (hk : k ∉ G.recommendationPaymentImplementationCosts μ) :
    ∃ y : G.RecommendationPaymentLPRow → ℝ,
      Math.LinearProgramming.DualFeasible
        (G.recommendationPaymentLPA μ) (fun _ : G.RecommendationPaymentLPCol => 0) y ∧
      Math.LinearProgramming.dualValue (G.recommendationPaymentLPb μ k) y < 0 :=
  G.exists_dualValue_neg_of_not_mem_recommendationPaymentImplementationCosts hk

example [DecidableEq ι] [Fintype ι] [Fintype (Profile G)]
    [∀ i, Fintype (G.Strategy i)]
    {μ : PMF (Profile G)} {k : ℝ} :
    k ∉ G.recommendationPaymentImplementationCosts μ ↔
      ∃ y : G.RecommendationPaymentLPRow → ℝ,
        Math.LinearProgramming.DualFeasible
          (G.recommendationPaymentLPA μ) (fun _ : G.RecommendationPaymentLPCol => 0) y ∧
        Math.LinearProgramming.dualValue (G.recommendationPaymentLPb μ k) y < 0 :=
  G.not_mem_recommendationPaymentImplementationCosts_iff_exists_dualValue_neg

example [DecidableEq ι] [Fintype ι] [Fintype (Profile G)]
    [∀ i, Fintype (G.Strategy i)]
    {μ : PMF (Profile G)} {L : ℝ}
    (hne : (G.recommendationPaymentImplementationCosts μ).Nonempty)
    (hcert : ∀ k, k < L →
      ∃ y : G.RecommendationPaymentLPRow → ℝ,
        Math.LinearProgramming.DualFeasible
          (G.recommendationPaymentLPA μ) (fun _ : G.RecommendationPaymentLPCol => 0) y ∧
        Math.LinearProgramming.dualValue (G.recommendationPaymentLPb μ k) y < 0) :
    L ≤ G.recommendationPaymentImplPrice μ :=
  G.le_recommendationPaymentImplPrice_of_dual_certificates hne hcert

example [DecidableEq ι] [Fintype ι] [Fintype (Profile G)]
    [∀ i, Fintype (G.Strategy i)]
    {μ : PMF (Profile G)} {L : ℝ}
    (hne : (G.recommendationPaymentImplementationCosts μ).Nonempty)
    (lam : (i : ι) → G.Strategy i → G.Strategy i → ℝ)
    (γ : Profile G → ℝ)
    (hlam_nonneg : ∀ i si a, 0 ≤ lam i si a)
    (hγ_nonneg : ∀ θ, 0 ≤ γ θ)
    (hγ_zero : ∀ θ, μ θ = 0 → γ θ = 0)
    (hγ_sum : (∑ θ : Profile G, γ θ) = 1)
    (hcoeff : ∀ θ i,
      (∑ si : G.Strategy i, ∑ a : G.Strategy i,
        lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) ≤ γ θ)
    (hvalue : L ≤
      ∑ i, ∑ si : G.Strategy i, ∑ a : G.Strategy i,
        lam i si a * G.recommendationPaymentIncentiveGain μ i si a) :
    L ≤ G.recommendationPaymentImplPrice μ :=
  G.le_recommendationPaymentImplPrice_of_weighted_lp_certificate hne
    lam γ hlam_nonneg hγ_nonneg hγ_zero hγ_sum hcoeff hvalue

example [DecidableEq ι] [Fintype ι] {I : G.ImplementationDevice}
    [Finite (∀ i, I.Signal i)] [∀ i, Finite (I.Signal i)]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {b : ∀ i, I.Signal i → G.Strategy i} {μ : PMF (Profile G)}
    (h : I.InterimDominantExpectedKImplementsDistribution b μ 0) :
    G.IsCorrelatedEq μ :=
  I.isCorrelatedEq_of_interimDominantExpectedKImplDist_zero h

example [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    (hfull : ∀ i (si : G.Strategy i),
      Math.ProbabilityMassFunction.pmfMass (μ := μ)
        (fun θ : Profile G => θ i = si) ≠ 0)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.recommendationDevice μ B hB).InterimWeaklyStrictlyDominantKImplementsDistribution
        (G.obedientDeviceStrategy) μ 0 :=
  G.exists_recommendationDevice_strictInterimDominantKImplementsDistribution
    hce hfull hopponent

example [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    (hfull : ∀ i (si : G.Strategy i),
      Math.ProbabilityMassFunction.pmfMass (μ := μ)
        (fun θ : Profile G => θ i = si) ≠ 0)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.recommendationDevice μ B hB).deviceGame.IsExactKImplementation
        (fun _ _ => 0)
        ({G.obedientDeviceStrategy} :
          Set (Profile (G.recommendationDevice μ B hB).deviceGame)) 0 :=
  G.exists_recommendationDevice_obedient_zeroTransfer_exactKImplementation
    hce hfull hopponent

end KernelGame

namespace InformationalImplementationExamples

open Math.LinearProgramming

example (c : figure3Game.Strategy 0) (hc : c ≠ figure3DominatingP1Strategy) :
    figure3Game.WeaklyStrictlyDominatesWithTransfer (fun _ _ => 0)
      0 figure3DominatingP1Strategy c :=
  figure3DominatingP1Strategy_weaklyStrictlyDominates_ne c hc

example {ι : Type} [DecidableEq ι] {G : InformationalGame ι}
    {V : G.ActionTransfer} {σ : G.StrategyProfile}
    (h : G.IsExPostDominantProfileWithTransfer V σ) :
    G.undominatedStrategyProfilesWithTransfer V =
      {τ : G.StrategyProfile |
        ∀ i, G.StrategyEquivalentWithTransfer V i (τ i) (σ i)} :=
  h.undominatedStrategyProfiles_eq

example {ι : Type} [DecidableEq ι] [Fintype ι] {G : InformationalGame ι}
    [Fintype G.ActionProfile] {σ : G.StrategyProfile}
    {x : G.SignalBlindPaymentVar → ℝ} :
    MinPrimalFeasible
      (InformationalGame.SignalBlindDominanceMatrix.A G σ)
      (InformationalGame.SignalBlindDominanceMatrix.b G σ) x ↔
      (∀ a i, 0 ≤ G.vectorActionTransfer x a i) ∧
        G.IsExPostDominantProfileWithTransfer (G.vectorActionTransfer x) σ :=
  open InformationalGame.SignalBlindDominanceMatrix in
    minPrimalFeasible_iff_nonnegative_exPostDominant

example {ι : Type} [DecidableEq ι] [Fintype ι] {G : InformationalGame ι}
    [Fintype G.ActionProfile] {σ : G.StrategyProfile}
    (row : G.SignalBlindDominanceRow) :
    (∑ q : G.SignalBlindPaymentVar,
      InformationalGame.SignalBlindDominanceMatrix.A G σ row q) = 0 :=
  open InformationalGame.SignalBlindDominanceMatrix in
    sum_A_row row

example {ι : Type} [DecidableEq ι] [Fintype ι] {G : InformationalGame ι}
    [Fintype G.ActionProfile] [Fintype G.SignalProfile]
    [∀ i, Fintype (G.Act i)] {σ : G.StrategyProfile}
    (y : G.SignalBlindDominanceRow → ℝ) :
    (∑ q : G.SignalBlindPaymentVar,
      colEval (InformationalGame.SignalBlindDominanceMatrix.A G σ) y q) = 0 :=
  open InformationalGame.SignalBlindDominanceMatrix in
    sum_colEval_A y

example {ι : Type} [DecidableEq ι] [Fintype ι] {G : InformationalGame ι}
    [Fintype G.ActionProfile] [Fintype G.SignalProfile]
    [∀ i, Fintype (G.Act i)] {σ : G.StrategyProfile}
    {y : G.SignalBlindDominanceRow → ℝ}
    (hy_col : ∀ q : G.SignalBlindPaymentVar,
      colEval (InformationalGame.SignalBlindDominanceMatrix.A G σ) y q ≤ 0)
    (q : G.SignalBlindPaymentVar) :
    colEval (InformationalGame.SignalBlindDominanceMatrix.A G σ) y q = 0 :=
  open InformationalGame.SignalBlindDominanceMatrix in
    colEval_eq_zero_of_forall_colEval_nonpos hy_col q

example {ι : Type} [DecidableEq ι] [Fintype ι] {G : InformationalGame ι}
    [Fintype G.ActionProfile] [Fintype G.SignalProfile]
    [∀ i, Fintype (G.Act i)] {σ : G.StrategyProfile} :
    (¬ ∃ V : G.ActionTransfer,
      (∀ a i, 0 ≤ V a i) ∧ G.IsExPostDominantProfileWithTransfer V σ) ↔
      ∃ y : G.SignalBlindDominanceRow → ℝ,
        Nonnegative y ∧
          (∀ q : G.SignalBlindPaymentVar,
            colEval (InformationalGame.SignalBlindDominanceMatrix.A G σ) y q ≤ 0) ∧
            0 < dot (InformationalGame.SignalBlindDominanceMatrix.b G σ) y :=
  open InformationalGame.SignalBlindDominanceMatrix in
    not_exists_nonnegative_exPostDominant_iff_exists_dual_certificate

example {ι : Type} [DecidableEq ι] [Fintype ι] {G : InformationalGame ι}
    [Fintype G.ActionProfile] [Fintype G.SignalProfile]
    [∀ i, Fintype (G.Act i)] {σ : G.StrategyProfile} :
    (∃ V : G.ActionTransfer,
      (∀ a i, 0 ≤ V a i) ∧ G.IsExPostDominantProfileWithTransfer V σ) ↔
      ¬ ∃ y : G.SignalBlindDominanceRow → ℝ,
        Nonnegative y ∧
          (∀ q : G.SignalBlindPaymentVar,
            colEval (InformationalGame.SignalBlindDominanceMatrix.A G σ) y q ≤ 0) ∧
            0 < dot (InformationalGame.SignalBlindDominanceMatrix.b G σ) y :=
  open InformationalGame.SignalBlindDominanceMatrix in
    exists_nonnegative_exPostDominant_iff_not_exists_dual_certificate

example {ι : Type} [DecidableEq ι] {G : InformationalGame ι}
    {κ : Type} [Fintype κ] {i : ι} {σ : G.StrategyProfile}
    (next : Equiv.Perm κ)
    (θ : κ → G.SignalProfile) (a : κ → G.ActionProfile) (dev : κ → G.Act i)
    (hlink : ∀ k,
      Function.update (a k) i (dev k) =
        Function.update (a (next k)) i (σ i (θ (next k) i)))
    (hcycle : 0 < ∑ k,
      (G.utility (θ k) (Function.update (a k) i (dev k)) i -
        G.utility (θ k) (Function.update (a k) i (σ i (θ k i))) i)) :
    ¬ ∃ V : G.ActionTransfer,
      G.IsExPostDominantProfileWithTransfer V σ :=
  InformationalGame.not_exists_signalBlind_exPostDominant_of_positive_cycle
    next θ a dev hlink hcycle

example {ι : Type} [DecidableEq ι] [Fintype ι] {G : InformationalGame ι}
    [Fintype G.ActionProfile] [Fintype G.SignalProfile]
    [∀ i, Fintype (G.Act i)]
    {κ : Type} [Fintype κ] {i : ι} {σ : G.StrategyProfile}
    (next : Equiv.Perm κ)
    (θ : κ → G.SignalProfile) (a : κ → G.ActionProfile) (dev : κ → G.Act i)
    (hlink : ∀ k,
      Function.update (a k) i (dev k) =
        Function.update (a (next k)) i (σ i (θ (next k) i)))
    (hcycle : 0 < ∑ k,
      (G.utility (θ k) (Function.update (a k) i (dev k)) i -
        G.utility (θ k) (Function.update (a k) i (σ i (θ k i))) i)) :
    ∃ y : G.SignalBlindDominanceRow → ℝ,
      Nonnegative y ∧
        (∀ q : G.SignalBlindPaymentVar,
          colEval (InformationalGame.SignalBlindDominanceMatrix.A G σ) y q ≤ 0) ∧
          0 < dot (InformationalGame.SignalBlindDominanceMatrix.b G σ) y :=
  InformationalGame.exists_signalBlindDominance_dual_certificate_of_positive_cycle
    next θ a dev hlink hcycle

example {ι : Type} [DecidableEq ι] {G : InformationalGame ι}
    {i : ι} {σ : G.StrategyProfile}
    (θ η : G.SignalProfile) (a : G.ActionProfile)
    (hcycle : 0 <
      (G.utility θ (Function.update a i (σ i (η i))) i -
        G.utility θ (Function.update a i (σ i (θ i))) i) +
      (G.utility η (Function.update a i (σ i (θ i))) i -
        G.utility η (Function.update a i (σ i (η i))) i)) :
    ¬ ∃ V : G.ActionTransfer,
      G.IsExPostDominantProfileWithTransfer V σ :=
  InformationalGame.not_exists_signalBlind_exPostDominant_of_positive_two_cycle
    θ η a hcycle

example :
    figure4Game.IsExPostEq figure4Target :=
  figure4Target_isExPostEq

example (k : ℝ) :
    ¬ ∃ V : figure4Game.ActionTransfer,
      figure4Game.IsSignalBlindKImplementation V
        ({figure4Target} : Set figure4Game.StrategyProfile) k :=
  figure4_no_signalBlind_kImplementation k

example :
    ∃ y : figure4Game.SignalBlindDominanceRow → ℝ,
      Nonnegative y ∧
        (∀ q : figure4Game.SignalBlindPaymentVar,
          colEval
            (InformationalGame.SignalBlindDominanceMatrix.A figure4Game figure4Target)
              y q ≤ 0) ∧
          0 < dot
            (InformationalGame.SignalBlindDominanceMatrix.b figure4Game figure4Target) y :=
  figure4_signalBlindDominance_dual_certificate

end InformationalImplementationExamples

namespace CombinatorialAuction

namespace BoundedOneGoodExample

example :
    setup.toInformationalGame.IsSignalBlindExPostDominantKImplementation
      (setup.toInformationalGame.conformanceBonusTransfer allReportsConform 2)
      setup.truthfulStrategy 0 :=
  truthful_zero_conformanceBonus_implementation

end BoundedOneGoodExample

namespace StrictConformanceExample

example :
    setup.toInformationalGame.IsSignalBlindKImplementation
      (setup.toInformationalGame.conformanceBonusTransfer conformingReport 3)
      ({targetStrategy} : Set setup.toInformationalGame.StrategyProfile) 0 :=
  target_strict_conformanceBonus_implementation

example (i : Buyer) :
    setup.toInformationalGame.conformanceBonusTransfer conformingReport 3
      (offPathAction i) i = 3 :=
  conformanceBonus_fires i

end StrictConformanceExample

namespace StrictFrugalVCGExample

example :
    game.IsSignalBlindKImplementation
      (game.conformanceBonusTransfer
        (boundedQBasedReport (ι := Buyer) trivialQ trivialQ_empty) 5)
      ({targetStrategy} : Set game.StrategyProfile) 0 :=
  strict_frugal_vcg_implementation

example :
    IsBoundedSurplusMaximizer allocation ∧ IsBoundedFrugal allocation :=
  ⟨allocation_isSurplusMaximizer, allocation_isFrugal⟩

example :
    IsQuasiField (A := Good) trivialQ :=
  trivialQ_isQuasiField

end StrictFrugalVCGExample

namespace FrugalityNecessityExample

example :
    Valuation.IsBasedOn sigma sigma_empty w1 ∧
      surplus truthfulReport truthfulAllocation ≥ surplus truthfulReport γ ∧
      surplus cheatingReport cheatingAllocation ≥ surplus cheatingReport δ ∧
      ab ⊂ cheatingAllocation.bundle 0 ∧
      w1 ab = w1 (cheatingAllocation.bundle 0) ∧
      v1 (truthfulAllocation.bundle 0) <
        v1 (cheatingAllocation.bundle 0) :=
  lemma1_fails_without_frugality

example :
    IsSurplusMaximizer nonfrugalAllocationRule ∧
      ¬ IsFrugal nonfrugalAllocationRule ∧
        Valuation.IsBasedOn sigma sigma_empty w1 ∧
          nonfrugalVCGSetup.trueUtility 0 v1 truthfulReport <
            nonfrugalVCGSetup.trueUtility 0 v1 cheatingReport :=
  lemma1_fails_without_frugality_trueUtility

end FrugalityNecessityExample
end CombinatorialAuction

namespace RedundantReportVCGExample

example (B : ℝ) :
    setup.toInformationalGame.undominatedStrategyProfilesWithTransfer
        (setup.toInformationalGame.conformanceBonusTransfer allReportsConform B) ≠
      ({setup.truthfulStrategy} : Set setup.toInformationalGame.StrategyProfile) :=
  undominatedStrategyProfiles_ne_singleton_truthful B

example (B : ℝ) (i : Player) :
    setup.toInformationalGame.StrategyEquivalentWithTransfer
      (setup.toInformationalGame.conformanceBonusTransfer allReportsConform B)
      i (flipSecondStrategy i) (setup.truthfulStrategy i) :=
  flipSecond_equivalent_truthful B i

example :
    setup.toInformationalGame.TransferClassStrategyProfileEquivalent
      conformanceBonusTransferClass flipSecondStrategy setup.truthfulStrategy :=
  flipSecond_transferClassEquivalent_truthful

example {V : setup.toInformationalGame.ActionTransfer}
    (hV : V ∈ conformanceBonusTransferClass) :
    ¬ setup.toInformationalGame.IsSignalBlindImplementation V
      ({setup.truthfulStrategy} : Set setup.toInformationalGame.StrategyProfile) :=
  not_signalBlindImplementation_singleton_truthful_of_conformanceBonusClass hV

end RedundantReportVCGExample

end GameTheory
