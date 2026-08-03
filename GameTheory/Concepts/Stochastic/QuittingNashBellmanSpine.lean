/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Existence.NashExistenceMixed
import GameTheory.Concepts.Stochastic.CompactSerialRelation
import GameTheory.Concepts.Stochastic.QuittingRootSuccessorCertificate
import GameTheory.Concepts.Stochastic.QuittingTerminalUniformization
import Math.ProbabilityMassFunction.Simplex

/-!
# Exact Nash--Bellman spines for finite quitting games

For every bounded finite quitting payoff table, one-stage mixed Nash
existence defines a predecessor-serial Bellman correspondence on a compact
payoff cube.  The compact serial-relation inverse limit then produces a
bounded infinite sequence of continuation values and mixed roots satisfying
the exact Bellman equation and exact root Nash inequalities at every time.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Product of Boolean mixed-action simplices used as a topological model of
quitting roots. -/
abbrev QuittingRootSimplex (ι : Type) [Fintype ι] :=
  ∀ _ : ι, stdSimplex ℝ Bool

/-- Convert simplex coordinates to the corresponding profile of finite
probability mass functions. -/
def quittingRootOfSimplex (root : QuittingRootSimplex ι) :
    ι → PMF Bool :=
  fun who => (stdSimplexEquiv (α := Bool)).symm (root who)

omit [DecidableEq ι] in
@[simp] theorem quittingRootOfSimplex_apply_toReal
    (root : QuittingRootSimplex ι) (who : ι) (action : Bool) :
    ((quittingRootOfSimplex root who) action).toReal = root who action := by
  simp [quittingRootOfSimplex, stdSimplexEquiv_symm_apply]

/-- The expected quitting payoff in simplex coordinates is a finite
multilinear sum. -/
theorem quittingRootExpectedPayoff_simplex_eq_sum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : QuittingRootSimplex ι) (who : ι) :
    quittingRootExpectedPayoff reward continuation
        (quittingRootOfSimplex root) who =
      ∑ action : ι → Bool,
        (∏ player, root player (action player)) *
          quittingRootPayoff reward continuation action who := by
  unfold quittingRootExpectedPayoff
  rw [expect_eq_sum]
  apply Finset.sum_congr rfl
  intro action _
  congr 1
  simp [pmfPi_apply, quittingRootOfSimplex]

omit [DecidableEq ι] in
/- Joint continuity in the continuation vector and all simplex root
coordinates. -/
theorem continuous_quittingRootExpectedPayoff_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootExpectedPayoff reward point.1
        (quittingRootOfSimplex point.2) who) := by
  classical
  rw [show (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootExpectedPayoff reward point.1
        (quittingRootOfSimplex point.2) who) =
      (fun point =>
        ∑ action : ι → Bool,
          (∏ player, point.2 player (action player)) *
            quittingRootPayoff reward point.1 action who) by
    funext point
    exact quittingRootExpectedPayoff_simplex_eq_sum
      reward point.1 point.2 who]
  refine continuous_finsetSum
    (s := (Finset.univ : Finset (ι → Bool))) ?_
  intro action _
  refine (continuous_finsetProd
    (s := (Finset.univ : Finset ι)) ?_).mul ?_
  · intro player _
    exact (continuous_apply (action player)).comp
      (continuous_subtype_val.comp
        ((continuous_apply player).comp continuous_snd))
  · by_cases hquit : (quittingQuitters action).Nonempty
    · simpa [quittingRootPayoff, hquit] using
        (continuous_const : Continuous
          (fun _ : Payoff ι × QuittingRootSimplex ι =>
            reward ⟨quittingQuitters action, hquit⟩ who))
    · simp only [quittingRootPayoff, dif_neg hquit]
      exact (continuous_apply who).comp continuous_fst

/-- Replace one simplex marginal by a pure Boolean action. -/
def quittingRootSimplexUpdate
    (root : QuittingRootSimplex ι) (who : ι) (action : Bool) :
    QuittingRootSimplex ι :=
  Function.update root who (stdSimplexEquiv (PMF.pure action))

/-- Simplex update agrees with PMF-profile update. -/
theorem quittingRootOfSimplex_update
    (root : QuittingRootSimplex ι) (who : ι) (action : Bool) :
    quittingRootOfSimplex (quittingRootSimplexUpdate root who action) =
      Function.update (quittingRootOfSimplex root) who (PMF.pure action) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [quittingRootSimplexUpdate, quittingRootOfSimplex]
  · simp [quittingRootSimplexUpdate, quittingRootOfSimplex,
      Function.update_of_ne hplayer]

/-- Replacing one simplex coordinate by a fixed pure action is continuous. -/
theorem continuous_quittingRootSimplexUpdate (who : ι) (action : Bool) :
    Continuous (fun root : QuittingRootSimplex ι =>
      quittingRootSimplexUpdate root who action) := by
  apply continuous_pi
  intro player
  by_cases hplayer : player = who
  · subst player
    simpa [quittingRootSimplexUpdate] using
      (continuous_const : Continuous (fun _ : QuittingRootSimplex ι =>
        stdSimplexEquiv (PMF.pure action)))
  · simpa [quittingRootSimplexUpdate, Function.update_of_ne hplayer] using
      (continuous_apply player : Continuous
        (fun root : QuittingRootSimplex ι => root player))

/-- Pure-Quit payoff is jointly continuous in the continuation and simplex
root. -/
theorem continuous_quittingRootQuitPayoff_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootQuitPayoff reward point.1
        (quittingRootOfSimplex point.2) who) := by
  have hmap : Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      (point.1, quittingRootSimplexUpdate point.2 who true)) :=
    continuous_fst.prodMk
      ((continuous_quittingRootSimplexUpdate who true).comp continuous_snd)
  have hcontinuous :=
    (continuous_quittingRootExpectedPayoff_simplex reward who).comp hmap
  rw [show (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootQuitPayoff reward point.1
        (quittingRootOfSimplex point.2) who) =
      ((fun point : Payoff ι × QuittingRootSimplex ι =>
          quittingRootExpectedPayoff reward point.1
            (quittingRootOfSimplex point.2) who) ∘
        fun point =>
          (point.1, quittingRootSimplexUpdate point.2 who true)) by
    funext point
    simp only [Function.comp_apply, quittingRootQuitPayoff]
    rw [quittingRootOfSimplex_update]]
  exact hcontinuous

/-- Pure-Continue payoff is jointly continuous in the continuation and
simplex root. -/
theorem continuous_quittingRootContinuePayoff_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootContinuePayoff reward point.1
        (quittingRootOfSimplex point.2) who) := by
  have hmap : Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      (point.1, quittingRootSimplexUpdate point.2 who false)) :=
    continuous_fst.prodMk
      ((continuous_quittingRootSimplexUpdate who false).comp continuous_snd)
  have hcontinuous :=
    (continuous_quittingRootExpectedPayoff_simplex reward who).comp hmap
  rw [show (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootContinuePayoff reward point.1
        (quittingRootOfSimplex point.2) who) =
      ((fun point : Payoff ι × QuittingRootSimplex ι =>
          quittingRootExpectedPayoff reward point.1
            (quittingRootOfSimplex point.2) who) ∘
        fun point =>
          (point.1, quittingRootSimplexUpdate point.2 who false)) by
    funext point
    simp only [Function.comp_apply, quittingRootContinuePayoff]
    rw [quittingRootOfSimplex_update]]
  exact hcontinuous

/-- The pure Quit-minus-Continue difference is jointly continuous. -/
theorem continuous_quittingRootEndpointDifference_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootEndpointDifference reward point.1
        (quittingRootOfSimplex point.2) who) := by
  exact (continuous_quittingRootQuitPayoff_simplex reward who).sub
    (continuous_quittingRootContinuePayoff_simplex reward who)

/-- Exact endpoint-Nash constraints form a closed subset of continuation
vectors and simplex roots. -/
theorem isClosed_isZeroQuittingRootEndpointNash_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsClosed {point : Payoff ι × QuittingRootSimplex ι |
      IsεQuittingRootEndpointNash reward point.1 0
        (quittingRootOfSimplex point.2)} := by
  have hcoordinate : ∀ who : ι,
      Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
        point.2 who false) ∧
      Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
        point.2 who true) := by
    intro who
    constructor
    · exact (continuous_apply false).comp
        (continuous_subtype_val.comp
          ((continuous_apply who).comp continuous_snd))
    · exact (continuous_apply true).comp
        (continuous_subtype_val.comp
          ((continuous_apply who).comp continuous_snd))
  have hclosed : ∀ who : ι, IsClosed
      {point : Payoff ι × QuittingRootSimplex ι |
        point.2 who false *
            quittingRootEndpointDifference reward point.1
              (quittingRootOfSimplex point.2) who ≤ 0 ∧
          0 ≤ point.2 who true *
            quittingRootEndpointDifference reward point.1
              (quittingRootOfSimplex point.2) who} := by
    intro who
    exact (isClosed_le
      ((hcoordinate who).1.mul
        (continuous_quittingRootEndpointDifference_simplex reward who))
      continuous_const).inter
      (isClosed_le continuous_const
        ((hcoordinate who).2.mul
          (continuous_quittingRootEndpointDifference_simplex reward who)))
  have hinter : IsClosed (⋂ who : ι,
      {point : Payoff ι × QuittingRootSimplex ι |
        point.2 who false *
            quittingRootEndpointDifference reward point.1
              (quittingRootOfSimplex point.2) who ≤ 0 ∧
          0 ≤ point.2 who true *
            quittingRootEndpointDifference reward point.1
              (quittingRootOfSimplex point.2) who}) :=
    isClosed_iInter hclosed
  have heq : {point : Payoff ι × QuittingRootSimplex ι |
      IsεQuittingRootEndpointNash reward point.1 0
        (quittingRootOfSimplex point.2)} =
      ⋂ who : ι,
        {point : Payoff ι × QuittingRootSimplex ι |
          point.2 who false *
              quittingRootEndpointDifference reward point.1
                (quittingRootOfSimplex point.2) who ≤ 0 ∧
            0 ≤ point.2 who true *
              quittingRootEndpointDifference reward point.1
                (quittingRootOfSimplex point.2) who} := by
    ext point
    simp only [IsεQuittingRootEndpointNash,
      quittingRootOfSimplex_apply_toReal, neg_zero, Set.mem_setOf_eq,
      Set.mem_iInter]
  rw [heq]
  exact hinter

/-- The one-stage normal-form game obtained from a continuation payoff
vector. -/
abbrev quittingContinuationGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) : KernelGame ι :=
  KernelGame.ofPureEU (fun _ => Bool)
    (fun action who => quittingRootPayoff reward continuation action who)

omit [DecidableEq ι] in
/- Mixed expected utility in the one-stage normal form is exactly the
quitting root expected payoff. -/
theorem quittingContinuationGame_mixedExtension_eu
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    (quittingContinuationGame reward continuation).mixedExtension.eu
        root who =
      quittingRootExpectedPayoff reward continuation root who := by
  letI : Finite (quittingContinuationGame reward continuation).Outcome := by
    change Finite (ι → Bool)
    infer_instance
  change (KernelGame.ofPureEU (fun _ : ι => Bool)
      (fun action who =>
        quittingRootPayoff reward continuation action who)).mixedExtension.eu
      root who = _
  rw [KernelGame.mixedExtension_eu]
  simp only [KernelGame.eu_ofPureEU]
  rfl

/-- Nash equilibrium in the one-stage normal form is exact quitting-root
Nash. -/
theorem quittingContinuationGame_isNash_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool) :
    (quittingContinuationGame reward continuation).mixedExtension.IsNash root ↔
      IsεQuittingRootNash reward continuation 0 root := by
  change (KernelGame.ofPureEU (fun _ : ι => Bool)
      (fun action who =>
        quittingRootPayoff reward continuation action who)).mixedExtension.IsNash
      root ↔ _
  simp only [KernelGame.IsNash, KernelGame.mixedExtension_Strategy,
    KernelGame.ofPureEU_Strategy, IsεQuittingRootNash, add_zero, ge_iff_le,
    quittingContinuationGame_mixedExtension_eu]

end GameTheory
