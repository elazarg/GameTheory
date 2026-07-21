/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Foundations.GameMorphism
import GameTheory.Concepts.ZeroSum.Minimax
import GameTheory.Concepts.ZeroSum.SecurityStrategy
import Math.Reindex

/-!
# Security and Minimax Concepts under Game Isomorphism

Expected-utility game isomorphisms preserve guarantees, pure and mixed
order-theoretic security values, attained security predicates, and saddle
points. The value equalities use equivalences to reindex raw indexed
infima/suprema, so they require no finiteness or attainment assumptions.
-/

namespace GameTheory
namespace KernelGame
namespace EUGameIsomorphism

open Math.Probability

variable {ι : Type} {G H : KernelGame ι}

/-- A strategy guarantees the same payoff thresholds after relabeling. -/
theorem guarantees_iff [DecidableEq ι] (e : EUGameIsomorphism G H)
    (who : ι) (s : G.Strategy who) (v : ℝ) :
    G.Guarantees who s v ↔ H.Guarantees who (e.stratEquiv who s) v := by
  unfold KernelGame.Guarantees
  constructor
  · intro h τ
    calc
      H.eu (Function.update τ who (e.stratEquiv who s)) who =
          G.eu (Function.update (e.profileEquiv.symm τ) who s) who := by
        simpa using e.eu_update_preserved (e.profileEquiv.symm τ) who s
      _ ≥ v := h _
  · intro h σ
    calc
      G.eu (Function.update σ who s) who =
          H.eu (Function.update (e.profileEquiv σ) who (e.stratEquiv who s)) who :=
        (e.eu_update_preserved σ who s).symm
      _ ≥ v := h _

/-- Pure worst-case expected utility is invariant under strategy and profile
relabeling. -/
theorem worstCaseEUInf_eq (e : EUGameIsomorphism G H)
    (who : ι) (s : G.Strategy who) :
    G.worstCaseEUInf who s = H.worstCaseEUInf who (e.stratEquiv who s) := by
  classical
  unfold KernelGame.worstCaseEUInf
  calc
    (⨅ σ : Profile G, G.eu (Function.update σ who s) who) =
        ⨅ σ : Profile G,
          H.eu (Function.update (e.profileEquiv σ) who (e.stratEquiv who s)) who := by
      apply iInf_congr
      intro σ
      exact (e.eu_update_preserved σ who s).symm
    _ = ⨅ τ : Profile H,
          H.eu (Function.update τ who (e.stratEquiv who s)) who :=
      Math.Reindex.iInf_comp_equiv e.profileEquiv (fun τ : Profile H =>
        H.eu (Function.update τ who (e.stratEquiv who s)) who)

/-- The pure order-theoretic security level is invariant under game
isomorphism. -/
theorem securityLevelSup_eq (e : EUGameIsomorphism G H)
    (who : ι) :
    G.securityLevelSup who = H.securityLevelSup who := by
  classical
  unfold KernelGame.securityLevelSup
  calc
    (⨆ s : G.Strategy who, G.worstCaseEUInf who s) =
        ⨆ s : G.Strategy who,
          H.worstCaseEUInf who (e.stratEquiv who s) := by
      apply iSup_congr
      intro s
      exact e.worstCaseEUInf_eq who s
    _ = ⨆ t : H.Strategy who, H.worstCaseEUInf who t :=
      Math.Reindex.iSup_comp_equiv (e.stratEquiv who) _

/-- Attainment of the pure order-theoretic security level is invariant under
game isomorphism. -/
theorem isSecurityStrategySup_iff
    (e : EUGameIsomorphism G H) (who : ι) (s : G.Strategy who) :
    G.IsSecurityStrategySup who s ↔
      H.IsSecurityStrategySup who (e.stratEquiv who s) := by
  classical
  unfold KernelGame.IsSecurityStrategySup
  rw [e.worstCaseEUInf_eq, e.securityLevelSup_eq]

/-- A profile consists of order-theoretic security strategies exactly when
its relabeling does. -/
theorem isSecurityProfileSup_iff
    (e : EUGameIsomorphism G H) (σ : Profile G) :
    G.IsSecurityProfileSup σ ↔ H.IsSecurityProfileSup (e.profileEquiv σ) := by
  classical
  unfold KernelGame.IsSecurityProfileSup
  exact forall_congr' fun i => e.isSecurityStrategySup_iff i (σ i)

/-- Mixed-own-strategy worst-case expected utility is invariant when the PMF
is pushed through the player's strategy equivalence. -/
theorem mixedWorstCaseEUInf_eq
    (e : EUGameIsomorphism G H) (who : ι) (p : PMF (G.Strategy who)) :
    G.mixedWorstCaseEUInf who p =
      H.mixedWorstCaseEUInf who (e.strategyPMFEquiv who p) := by
  classical
  unfold KernelGame.mixedWorstCaseEUInf
  calc
    (⨅ σ : Profile G,
        expect p (fun a => G.eu (Function.update σ who a) who)) =
      ⨅ σ : Profile G,
        expect (e.strategyPMFEquiv who p) (fun b =>
          H.eu (Function.update (e.profileEquiv σ) who b) who) := by
      apply iInf_congr
      intro σ
      rw [strategyPMFEquiv_apply, expect_map]
      apply congrArg (expect p)
      funext a
      exact (e.eu_update_preserved σ who a).symm
    _ = ⨅ τ : Profile H,
        expect (e.strategyPMFEquiv who p) (fun b =>
          H.eu (Function.update τ who b) who) :=
      Math.Reindex.iInf_comp_equiv e.profileEquiv (fun τ : Profile H =>
        expect (e.strategyPMFEquiv who p) (fun b =>
          H.eu (Function.update τ who b) who))

/-- The mixed maximin value is invariant under expected-utility game
isomorphism. -/
theorem mixedSecurityLevel_eq
    (e : EUGameIsomorphism G H) (who : ι) :
    G.mixedSecurityLevel who = H.mixedSecurityLevel who := by
  classical
  unfold KernelGame.mixedSecurityLevel
  calc
    (⨆ p : PMF (G.Strategy who), G.mixedWorstCaseEUInf who p) =
        ⨆ p : PMF (G.Strategy who),
          H.mixedWorstCaseEUInf who (e.strategyPMFEquiv who p) := by
      apply iSup_congr
      intro p
      exact e.mixedWorstCaseEUInf_eq who p
    _ = ⨆ q : PMF (H.Strategy who), H.mixedWorstCaseEUInf who q :=
      Math.Reindex.iSup_comp_equiv (e.strategyPMFEquiv who) _

variable {G H : KernelGame (Fin 2)}

/-- Saddle points are invariant under expected-utility game isomorphism. -/
theorem isSaddlePoint_iff (e : EUGameIsomorphism G H) (σ : Profile G) :
    G.IsSaddlePoint σ ↔ H.IsSaddlePoint (e.profileEquiv σ) :=
  (isSaddlePoint_iff_isNash G σ).trans <|
    (e.nash_iff σ).trans (isSaddlePoint_iff_isNash H _).symm

end EUGameIsomorphism
end KernelGame
end GameTheory
