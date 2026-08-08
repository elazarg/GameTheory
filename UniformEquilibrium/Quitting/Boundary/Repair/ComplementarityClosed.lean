/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanSpine

/-!
# Closedness of endpoint complementarity

`IsεQuittingRootEndpointNash reward tail ε root` is a finite conjunction of
non-strict polynomial inequalities in the tolerance `ε`, the tail payoff and
the root marginals: for each player, `continueProbability * difference ≤ ε`
and `-ε ≤ quitProbability * difference`.  Nothing here is strict, so the
constraint set is closed.

`isClosed_isZeroQuittingRootEndpointNash_simplex` in
`QuittingNashBellmanSpine` already records the `ε = 0` case jointly in the
tail and the root.  This file records the two facts that limit arguments
actually consume and that are not available there.

* Closedness is joint in `ε` as well, so an exact equilibrium survives a
  limit in which the tolerance vanishes, not only a limit at fixed `ε = 0`.
* The two `ε = 0` slices — fixed tail with varying root, and fixed root with
  varying tail — are closed, and the root slice is a nonempty compact set of
  simplex roots.

Roots are carried in the simplex coordinates `QuittingRootSimplex ι` used
everywhere else in the development; `ι → PMF Bool` has no topology here, and
`quittingRootOfSimplex` is the bridge.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction Math.Topology
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Joint closedness in tolerance, tail and root -/

/-- The endpoint complementarity constraints are closed jointly in the
tolerance, the tail payoff and the simplex root.  Every clause is a
non-strict inequality between continuous functions. -/
theorem isClosed_isεQuittingRootEndpointNash_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsClosed {point : ℝ × Payoff ι × QuittingRootSimplex ι |
      IsεQuittingRootEndpointNash reward point.2.1 point.1
        (quittingRootOfSimplex point.2.2)} := by
  have hdifference : ∀ who : ι,
      Continuous (fun point : ℝ × Payoff ι × QuittingRootSimplex ι =>
        quittingRootEndpointDifference reward point.2.1
          (quittingRootOfSimplex point.2.2) who) := fun who =>
    (continuous_quittingRootEndpointDifference_simplex reward who).comp
      continuous_snd
  have hcoordinate : ∀ (who : ι) (action : Bool),
      Continuous (fun point : ℝ × Payoff ι × QuittingRootSimplex ι =>
        point.2.2 who action) := fun who action =>
    (continuous_apply action).comp
      (continuous_subtype_val.comp
        ((continuous_apply who).comp (continuous_snd.comp continuous_snd)))
  have hclosed : ∀ who : ι, IsClosed
      {point : ℝ × Payoff ι × QuittingRootSimplex ι |
        point.2.2 who false *
            quittingRootEndpointDifference reward point.2.1
              (quittingRootOfSimplex point.2.2) who ≤ point.1 ∧
          -point.1 ≤ point.2.2 who true *
            quittingRootEndpointDifference reward point.2.1
              (quittingRootOfSimplex point.2.2) who} := by
    intro who
    exact (isClosed_le ((hcoordinate who false).mul (hdifference who))
        continuous_fst).inter
      (isClosed_le continuous_fst.neg
        ((hcoordinate who true).mul (hdifference who)))
  have heq : {point : ℝ × Payoff ι × QuittingRootSimplex ι |
      IsεQuittingRootEndpointNash reward point.2.1 point.1
        (quittingRootOfSimplex point.2.2)} =
      ⋂ who : ι,
        {point : ℝ × Payoff ι × QuittingRootSimplex ι |
          point.2.2 who false *
              quittingRootEndpointDifference reward point.2.1
                (quittingRootOfSimplex point.2.2) who ≤ point.1 ∧
            -point.1 ≤ point.2.2 who true *
              quittingRootEndpointDifference reward point.2.1
                (quittingRootOfSimplex point.2.2) who} := by
    ext point
    simp only [IsεQuittingRootEndpointNash,
      quittingRootOfSimplex_apply_toReal, Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  exact isClosed_iInter hclosed

/-- **Vanishing tolerance passes to the limit.**  A convergent family of
approximate endpoint equilibria whose tolerances converge has an endpoint
equilibrium at the limiting tolerance; taking `ε = 0` turns approximate
complementarity into exact complementarity. -/
theorem isεQuittingRootEndpointNash_of_tendsto
    {α : Type*} {l : Filter α} [l.NeBot]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tolerance : α → ℝ) (tails : α → Payoff ι)
    (roots : α → QuittingRootSimplex ι)
    {ε : ℝ} {tail : Payoff ι} {root : QuittingRootSimplex ι}
    (htolerance : Tendsto tolerance l (𝓝 ε))
    (htails : Tendsto tails l (𝓝 tail))
    (hroots : Tendsto roots l (𝓝 root))
    (hmem : ∀ᶠ a in l, IsεQuittingRootEndpointNash reward (tails a)
      (tolerance a) (quittingRootOfSimplex (roots a))) :
    IsεQuittingRootEndpointNash reward tail ε
      (quittingRootOfSimplex root) :=
  (isClosed_isεQuittingRootEndpointNash_simplex reward).mem_of_tendsto
    (htolerance.prodMk_nhds (htails.prodMk_nhds hroots)) hmem

/-! ## The two exact slices -/

/-- Fixed tail: the exact endpoint-Nash roots are a closed set of simplex
roots. -/
theorem isClosed_setOf_isZeroQuittingRootEndpointNash_root
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι) :
    IsClosed {root : QuittingRootSimplex ι |
      IsεQuittingRootEndpointNash reward tail 0
        (quittingRootOfSimplex root)} :=
  (isClosed_isεQuittingRootEndpointNash_simplex reward).preimage
    (by fun_prop :
      Continuous fun root : QuittingRootSimplex ι => ((0 : ℝ), tail, root))

/-- Fixed root: the tail payoffs against which the root is exactly endpoint
Nash are a closed set. -/
theorem isClosed_setOf_isZeroQuittingRootEndpointNash_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : QuittingRootSimplex ι) :
    IsClosed {tail : Payoff ι |
      IsεQuittingRootEndpointNash reward tail 0
        (quittingRootOfSimplex root)} :=
  (isClosed_isεQuittingRootEndpointNash_simplex reward).preimage
    (by fun_prop :
      Continuous fun tail : Payoff ι => ((0 : ℝ), tail, root))

/-- Fixed tail: the exact endpoint-Nash roots are compact.  The ambient
product of Boolean simplices is compact, so the closed slice is. -/
theorem isCompact_setOf_isZeroQuittingRootEndpointNash_root
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι) :
    IsCompact {root : QuittingRootSimplex ι |
      IsεQuittingRootEndpointNash reward tail 0
        (quittingRootOfSimplex root)} :=
  (isClosed_setOf_isZeroQuittingRootEndpointNash_root reward tail).isCompact

/-- Fixed tail: an exact endpoint-Nash root exists, so the compact slice is
not vacuous.  This is one-stage mixed Nash existence read through the
endpoint reformulation. -/
theorem exists_isZeroQuittingRootEndpointNash_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι) :
    ∃ root : QuittingRootSimplex ι,
      IsεQuittingRootEndpointNash reward tail 0
        (quittingRootOfSimplex root) := by
  let stageGame : KernelGame ι := quittingContinuationGame reward tail
  haveI : ∀ who, Finite (stageGame.Strategy who) :=
    fun _ => inferInstanceAs (Finite Bool)
  haveI : ∀ who, Nonempty (stageGame.Strategy who) :=
    fun _ => inferInstanceAs (Nonempty Bool)
  haveI : Finite stageGame.Outcome :=
    inferInstanceAs (Finite (ι → Bool))
  obtain ⟨root, hroot⟩ := stageGame.mixed_nash_exists
  refine ⟨fun who => stdSimplexEquiv (root who), ?_⟩
  have hcoordinates :
      quittingRootOfSimplex (fun who => stdSimplexEquiv (root who)) = root := by
    funext who
    exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root who)
  rw [hcoordinates]
  exact (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward tail 0 root).2
    ((quittingContinuationGame_isNash_iff reward tail root).1 hroot)

/-- Fixed tail: the exact endpoint-Nash root slice is a nonempty compact
set. -/
theorem isCompact_and_nonempty_setOf_isZeroQuittingRootEndpointNash_root
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι) :
    IsCompact {root : QuittingRootSimplex ι |
        IsεQuittingRootEndpointNash reward tail 0
          (quittingRootOfSimplex root)} ∧
      {root : QuittingRootSimplex ι |
        IsεQuittingRootEndpointNash reward tail 0
          (quittingRootOfSimplex root)}.Nonempty :=
  ⟨isCompact_setOf_isZeroQuittingRootEndpointNash_root reward tail,
    exists_isZeroQuittingRootEndpointNash_simplex reward tail⟩

end GameTheory
