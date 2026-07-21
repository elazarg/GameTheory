/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Transport.SolutionConcepts

/-!
# GameTheory.Concepts.Transport.Tests

Compilation checks for solution-concept transport APIs.
-/

namespace GameTheory.KernelGame.EUGameIsomorphism.Tests

noncomputable section

variable {ι : Type} [DecidableEq ι]
variable {G H : KernelGame ι}

example (e : EUGameIsomorphism G H) (ε : ℝ) (σ : Profile G) :
    G.IsεNash ε σ ↔ H.IsεNash ε (e.profileEquiv σ) :=
  e.isεNash_iff ε σ

example (e : EUGameIsomorphism G H) :
    G.IsDominantStrategySolvable ↔ H.IsDominantStrategySolvable :=
  e.isDominantStrategySolvable_iff

example (e : EUGameIsomorphism G H) (n : ℕ) (who : ι)
    (s : G.Strategy who) :
    G.SurvivesStrictDominance n who s ↔
      H.SurvivesStrictDominance n who (e.stratEquiv who s) :=
  e.survivesStrictDominance_iff n who s

example (e : EUGameIsomorphism G H) (σ : Profile G) :
    G.IsIESDSSolvable σ ↔ H.IsIESDSSolvable (e.profileEquiv σ) :=
  e.isIESDSSolvable_iff σ

example (e : EUGameIsomorphism G H) (who : ι) (s : G.Strategy who) :
    G.IsPureRationalizable who s ↔
      H.IsPureRationalizable who (e.stratEquiv who s) :=
  e.isPureRationalizable_iff who s

example (e : EUGameIsomorphism G H) (n : ℕ) (who : ι)
    (s : G.Strategy who) :
    G.Survives n who s ↔ H.Survives n who (e.stratEquiv who s) :=
  e.survives_iff n who s

example (e : EUGameIsomorphism G H) (who : ι) (s : G.Strategy who) :
    G.IsRationalizable who s ↔
      H.IsRationalizable who (e.stratEquiv who s) :=
  e.isRationalizable_iff who s

example (e : EUGameIsomorphism G H) (who : ι) (s : G.Strategy who) (v : ℝ) :
    G.Guarantees who s v ↔ H.Guarantees who (e.stratEquiv who s) v :=
  e.guarantees_iff who s v

example (e : EUGameIsomorphism G H) (σ τ : Profile G) :
    G.ParetoDominates σ τ ↔
      H.ParetoDominates (e.profileEquiv σ) (e.profileEquiv τ) :=
  e.paretoDominates_iff σ τ

example (e : EUGameIsomorphism G H) (Φ : Profile G → ℝ) :
    G.IsExactPotential Φ ↔ H.IsExactPotential (e.profileFunctionEquiv Φ) :=
  e.isExactPotential_iff Φ

example [Fintype ι] (e : EUGameIsomorphism G H) (σ : Profile G) :
    G.socialWelfare σ = H.socialWelfare (e.profileEquiv σ) :=
  e.socialWelfare_eq σ

example [Fintype ι] (e : EUGameIsomorphism G H) :
    G.optimalWelfare = H.optimalWelfare :=
  e.optimalWelfare_eq

example [Fintype ι] [Finite (Profile G)] [Finite (Profile H)]
    (e : EUGameIsomorphism G H) (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.bestNashWelfare hN =
      H.bestNashWelfare ((e.exists_isNash_iff).mp hN) := by
  simpa using e.bestNashWelfare_eq hN

example [Fintype ι] [Finite (Profile G)] [Finite (Profile H)]
    (e : EUGameIsomorphism G H) (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.worstNashWelfare hN =
      H.worstNashWelfare ((e.exists_isNash_iff).mp hN) := by
  simpa using e.worstNashWelfare_eq hN

example [Fintype ι] [Finite (Profile G)] [Finite (Profile H)]
    (e : EUGameIsomorphism G H) (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.priceOfAnarchy hN =
      H.priceOfAnarchy ((e.exists_isNash_iff).mp hN) := by
  simpa using e.priceOfAnarchy_eq hN

example [Fintype ι] [Finite (Profile G)] [Finite (Profile H)]
    (e : EUGameIsomorphism G H) (hN : ∃ σ : Profile G, G.IsNash σ) :
    G.priceOfStability hN =
      H.priceOfStability ((e.exists_isNash_iff).mp hN) := by
  simpa using e.priceOfStability_eq hN

example {G H : KernelGame (Fin 2)} (e : EUGameIsomorphism G H) (σ : Profile G) :
    G.IsSaddlePoint σ ↔ H.IsSaddlePoint (e.profileEquiv σ) :=
  e.isSaddlePoint_iff σ

-- These order-theoretic transports deliberately require no decidable
-- equality, finiteness, boundedness, or attainment assumptions.
variable {κ : Type} {A B : KernelGame κ}

example (e : EUGameIsomorphism A B) (who : κ) (s : A.Strategy who) :
    A.worstCaseEUInf who s = B.worstCaseEUInf who (e.stratEquiv who s) :=
  e.worstCaseEUInf_eq who s

example (e : EUGameIsomorphism A B) (who : κ) :
    A.securityLevelSup who = B.securityLevelSup who :=
  e.securityLevelSup_eq who

example (e : EUGameIsomorphism A B) (who : κ) (p : PMF (A.Strategy who)) :
    A.mixedWorstCaseEUInf who p =
      B.mixedWorstCaseEUInf who (e.strategyPMFEquiv who p) :=
  e.mixedWorstCaseEUInf_eq who p

example (e : EUGameIsomorphism A B) (who : κ) :
    A.mixedSecurityLevel who = B.mixedSecurityLevel who :=
  e.mixedSecurityLevel_eq who

example [Finite (Profile A)] [Nonempty (Profile A)]
    [∀ i, Finite (A.Strategy i)] [∀ i, Nonempty (A.Strategy i)]
    [Finite (Profile B)] [Nonempty (Profile B)]
    [∀ i, Finite (B.Strategy i)] [∀ i, Nonempty (B.Strategy i)]
    (e : EUGameIsomorphism A B) (who : κ) :
    A.securityLevel who = B.securityLevel who := by
  simpa using e.securityLevel_eq who

example [Finite (Profile A)] [Nonempty (Profile A)]
    [∀ i, Finite (A.Strategy i)] [∀ i, Nonempty (A.Strategy i)]
    [Finite (Profile B)] [Nonempty (Profile B)]
    [∀ i, Finite (B.Strategy i)] [∀ i, Nonempty (B.Strategy i)]
    (e : EUGameIsomorphism A B) (σ : Profile A) :
    A.IsSecurityProfile σ ↔ B.IsSecurityProfile (e.profileEquiv σ) := by
  simpa using e.isSecurityProfile_iff σ

end

end GameTheory.KernelGame.EUGameIsomorphism.Tests
