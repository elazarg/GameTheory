/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticBellmanHierarchy
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-!
# Endpoint-harmonic triviality

The endpoint harmonic submodule of an analytic Bellman germ is the kernel of
the endpoint continuation residual.  Adding the identity to that residual
turns it into the endpoint transition operator `T`, which acts on payoff
vectors through the state coordinate only.  Harmonicity is then exactly the
statement that a payoff vector is fixed by `T`.

Consequently the transition algebra acts on the harmonic submodule through
the trivial character: for every polynomial `p` one has `p(T) W = p(1) • W`.
Three corollaries close the module-filtration question.

* Every subspace of the harmonic submodule is invariant under `T` and under
  the whole algebra it generates, so being a submodule is vacuous for the
  processed harmonic-jet spans.
* The invariant subspaces of a harmonic subspace `V` are *all* subspaces of
  `V`, as a set equality.
* The longest chain of invariant subspaces of `V` has length exactly
  `Module.finrank ℝ V`, which is the rank already used by the recursion.

No associated-graded refinement of the harmonic-jet filtration can therefore
carry information beyond `Module.finrank`.

## Main results

* `mem_endpointHarmonicSubmodule_iff_transitionEnd` identifies harmonic vectors
  with the fixed space of the endpoint transition.
* `aeval_endpointTransitionEnd_apply_of_mem` proves the trivial-character
  formula for every polynomial in that transition.
* `setOf_algebraInvariant_le_eq_setOf_le` identifies algebra-invariant
  subspaces with all subspaces inside a harmonic space.
* `isGreatest_invtSubmodule_chain_length` and
  `isGreatest_algebraInvariant_chain_length` prove that the maximal strict
  chain length is exactly the ordinary finrank.

The module is standalone, contains no formal admissions, and need not be imported by the umbrella
to serve as a checked negative result about the proposed refinement.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.PMFProduct

namespace AnalyticBellmanGerm

/-! ### A general finite-dimensional chain bound

This lemma is linear algebra, independent of stochastic games.  Stating it at
that level avoids carrying game-specific finiteness instances through its
interface. -/

/-- Any strictly increasing chain of subspaces of a finite-dimensional real
vector space is at most as long as the dimension of the ambient subspace. -/
theorem strictSubmoduleChain_length_le_finrank
    {E : Type} [AddCommGroup E] [Module ℝ E] [Module.Finite ℝ E]
    {V : Submodule ℝ E} {n : ℕ}
    (c : Fin (n + 1) → Submodule ℝ E)
    (hc : StrictMono c) (hcV : ∀ i, c i ≤ V) :
    n ≤ Module.finrank ℝ V := by
  have hmono : StrictMono fun i => Module.finrank ℝ (c i) := by
    intro i j hij
    exact Submodule.finrank_lt_finrank_of_lt (hc hij)
  have hlt : ∀ i, Module.finrank ℝ (c i) < Module.finrank ℝ V + 1 :=
    fun i => Nat.lt_succ_of_le (Submodule.finrank_mono (hcV i))
  have hcard :=
    Fintype.card_le_of_injective
      (fun i : Fin (n + 1) =>
        (⟨Module.finrank ℝ (c i), hlt i⟩ :
          Fin (Module.finrank ℝ V + 1)))
      (by
        intro i j hij
        exact hmono.injective (by simpa using hij))
  simp only [Fintype.card_fin] at hcard
  omega

end AnalyticBellmanGerm

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

/-! ### The endpoint transition operator -/

/-- The endpoint transition operator of an analytic Bellman germ: the
endpoint continuation-value map, viewed as a linear endomorphism of the
state-payoff space.  It is the endpoint continuation residual shifted by the
identity, and it acts through the state coordinate alone. -/
def endpointTransitionEnd (germ : G.AnalyticBellmanGerm) :
    Module.End ℝ (G.State → Payoff ι) :=
  germ.endpointContinuationResidualLinearMap + LinearMap.id

theorem endpointContinuationResidualLinearMap_apply
    (germ : G.AnalyticBellmanGerm) (W : G.State → Payoff ι) :
    germ.endpointContinuationResidualLinearMap W =
      G.finkContinuationResidualVector W germ.endpointFinkPoint :=
  rfl

/-- The endpoint transition operator is the continuation residual plus the
argument. -/
theorem endpointTransitionEnd_apply
    (germ : G.AnalyticBellmanGerm) (W : G.State → Payoff ι) :
    germ.endpointTransitionEnd W =
      G.finkContinuationResidualVector W germ.endpointFinkPoint + W :=
  rfl

/-- Coordinatewise, the endpoint transition operator is the endpoint
continuation value. -/
theorem endpointTransitionEnd_apply_coord
    (germ : G.AnalyticBellmanGerm) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) :
    germ.endpointTransitionEnd W s who =
      G.finkContinuationEU W germ.endpointFinkPoint s who := by
  rw [endpointTransitionEnd_apply]
  simp [finkContinuationResidualVector, finkContinuationResidual]

/-- The endpoint transition operator is the endpoint state kernel acting on
the state coordinate, uniformly in the payoff coordinate.  This is the
tensor factorisation `K_end ⊗ id`. -/
theorem endpointTransitionEnd_apply_eq_expect
    (germ : G.AnalyticBellmanGerm) (W : G.State → Payoff ι)
    (s : G.State) (who : ι) :
    germ.endpointTransitionEnd W s who =
      expect (G.finkStateKernel germ.endpointFinkPoint s)
        (fun t => W t who) := by
  rw [endpointTransitionEnd_apply_coord, G.expect_finkStateKernel_eq]
  rfl

/-! ### Deliverable 1: the fixed-space characterisation -/

/-- A payoff vector is endpoint harmonic exactly when it is fixed by the
endpoint transition operator. -/
theorem mem_endpointHarmonicSubmodule_iff_transitionEnd
    (germ : G.AnalyticBellmanGerm) (W : G.State → Payoff ι) :
    W ∈ germ.endpointHarmonicSubmodule ↔
      germ.endpointTransitionEnd W = W := by
  rw [mem_endpointHarmonicSubmodule_iff]
  constructor
  · intro h
    rw [endpointTransitionEnd_apply, h, zero_add]
  · intro h
    rw [endpointTransitionEnd_apply] at h
    have hshift :
        G.finkContinuationResidualVector W germ.endpointFinkPoint + W =
          0 + W := by
      rw [h, zero_add]
    exact add_right_cancel hshift

/-- Endpoint harmonicity is the per-coordinate fixed-point equation for the
endpoint state kernel. -/
theorem mem_endpointHarmonicSubmodule_iff_forall_expect
    (germ : G.AnalyticBellmanGerm) (W : G.State → Payoff ι) :
    W ∈ germ.endpointHarmonicSubmodule ↔
      ∀ s who,
        expect (G.finkStateKernel germ.endpointFinkPoint s)
          (fun t => W t who) = W s who := by
  rw [mem_endpointHarmonicSubmodule_iff_transitionEnd]
  constructor
  · intro h s who
    rw [← endpointTransitionEnd_apply_eq_expect, h]
  · intro h
    funext s who
    rw [endpointTransitionEnd_apply_eq_expect, h]

/-- The endpoint harmonic submodule is the fixed space of the endpoint
transition operator. -/
theorem endpointHarmonicSubmodule_eq_ker_sub_id
    (germ : G.AnalyticBellmanGerm) :
    germ.endpointHarmonicSubmodule =
      LinearMap.ker (germ.endpointTransitionEnd - LinearMap.id) := by
  ext W
  rw [mem_endpointHarmonicSubmodule_iff_transitionEnd, LinearMap.mem_ker]
  constructor
  · intro h
    have : germ.endpointTransitionEnd W - W = 0 := by rw [h, sub_self]
    exact this
  · intro h
    have hzero : germ.endpointTransitionEnd W - W = 0 := h
    exact sub_eq_zero.mp hzero

/-! ### Deliverable 2: the trivial character -/

/-- Every endpoint-harmonic payoff vector is fixed by the endpoint
transition operator. -/
theorem endpointTransitionEnd_apply_of_mem
    (germ : G.AnalyticBellmanGerm) {W : G.State → Payoff ι}
    (hW : W ∈ germ.endpointHarmonicSubmodule) :
    germ.endpointTransitionEnd W = W :=
  (germ.mem_endpointHarmonicSubmodule_iff_transitionEnd W).mp hW

/-- Every power of the endpoint transition operator fixes every
endpoint-harmonic payoff vector. -/
theorem endpointTransitionEnd_pow_apply_of_mem
    (germ : G.AnalyticBellmanGerm) (n : ℕ) {W : G.State → Payoff ι}
    (hW : W ∈ germ.endpointHarmonicSubmodule) :
    (germ.endpointTransitionEnd ^ n) W = W := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply,
      germ.endpointTransitionEnd_apply_of_mem hW, ih]

/-- **Trivial character.**  On the endpoint harmonic submodule the
transition algebra acts through evaluation at `1`: for every real
polynomial `p`, the operator `p(T)` is multiplication by `p 1`. -/
theorem aeval_endpointTransitionEnd_apply_of_mem
    (germ : G.AnalyticBellmanGerm) (p : Polynomial ℝ)
    {W : G.State → Payoff ι}
    (hW : W ∈ germ.endpointHarmonicSubmodule) :
    (Polynomial.aeval germ.endpointTransitionEnd) p W = p.eval 1 • W := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, hp, hq, Polynomial.eval_add, add_smul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply,
      germ.endpointTransitionEnd_pow_apply_of_mem n hW,
      Module.algebraMap_end_apply, Polynomial.eval_monomial, one_pow,
      mul_one]

/-- Every element of the algebra generated by the endpoint transition
operator acts on the endpoint harmonic submodule as a scalar. -/
theorem exists_smul_eq_of_mem_adjoin
    (germ : G.AnalyticBellmanGerm)
    {f : Module.End ℝ (G.State → Payoff ι)}
    (hf : f ∈ Algebra.adjoin ℝ
      ({germ.endpointTransitionEnd} :
        Set (Module.End ℝ (G.State → Payoff ι))))
    {W : G.State → Payoff ι}
    (hW : W ∈ germ.endpointHarmonicSubmodule) :
    ∃ c : ℝ, f W = c • W := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hf
  obtain ⟨p, rfl⟩ := hf
  exact ⟨p.eval 1, germ.aeval_endpointTransitionEnd_apply_of_mem p hW⟩

/-! ### Deliverable 3: vacuous invariance -/

/-- Every subspace of the endpoint harmonic submodule is invariant under the
endpoint transition operator. -/
theorem mem_invtSubmodule_endpointTransitionEnd
    (germ : G.AnalyticBellmanGerm)
    {V : Submodule ℝ (G.State → Payoff ι)}
    (hV : V ≤ germ.endpointHarmonicSubmodule) :
    V ∈ Module.End.invtSubmodule germ.endpointTransitionEnd := by
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  intro W hW
  rw [germ.endpointTransitionEnd_apply_of_mem (hV hW)]
  exact hW

/-- Every subspace of the endpoint harmonic submodule is invariant under the
whole algebra generated by the endpoint transition operator. -/
theorem mapsTo_of_mem_adjoin_endpointTransitionEnd
    (germ : G.AnalyticBellmanGerm)
    {V : Submodule ℝ (G.State → Payoff ι)}
    (hV : V ≤ germ.endpointHarmonicSubmodule)
    {f : Module.End ℝ (G.State → Payoff ι)}
    (hf : f ∈ Algebra.adjoin ℝ
      ({germ.endpointTransitionEnd} :
        Set (Module.End ℝ (G.State → Payoff ι))))
    {W : G.State → Payoff ι} (hW : W ∈ V) :
    f W ∈ V := by
  obtain ⟨c, hc⟩ := germ.exists_smul_eq_of_mem_adjoin hf (hV hW)
  rw [hc]
  exact V.smul_mem c hW

namespace EndpointHarmonicJetSpan

/-- A processed endpoint-harmonic jet span is automatically invariant under
the endpoint transition operator, so the submodule condition asked of it
carries no information. -/
theorem carrier_mem_invtSubmodule {germ : G.AnalyticBellmanGerm}
    (jets : germ.EndpointHarmonicJetSpan) :
    jets.carrier ∈ Module.End.invtSubmodule germ.endpointTransitionEnd :=
  germ.mem_invtSubmodule_endpointTransitionEnd jets.carrier_le

/-- A processed endpoint-harmonic jet span is automatically invariant under
the whole endpoint transition algebra. -/
theorem carrier_mapsTo_of_mem_adjoin {germ : G.AnalyticBellmanGerm}
    (jets : germ.EndpointHarmonicJetSpan)
    {f : Module.End ℝ (G.State → Payoff ι)}
    (hf : f ∈ Algebra.adjoin ℝ
      ({germ.endpointTransitionEnd} :
        Set (Module.End ℝ (G.State → Payoff ι))))
    {W : G.State → Payoff ι} (hW : W ∈ jets.carrier) :
    f W ∈ jets.carrier :=
  germ.mapsTo_of_mem_adjoin_endpointTransitionEnd jets.carrier_le hf hW

end EndpointHarmonicJetSpan

/-! ### Deliverable 4: the filtration carries only the rank -/

/-- **Vacuous submodule condition.**  Inside a harmonic subspace `V`, the
invariant subspaces are exactly all the subspaces. -/
theorem setOf_invtSubmodule_le_eq_setOf_le
    (germ : G.AnalyticBellmanGerm)
    {V : Submodule ℝ (G.State → Payoff ι)}
    (hV : V ≤ germ.endpointHarmonicSubmodule) :
    {N : Submodule ℝ (G.State → Payoff ι) |
        N ≤ V ∧ N ∈ Module.End.invtSubmodule germ.endpointTransitionEnd} =
      {N : Submodule ℝ (G.State → Payoff ι) | N ≤ V} := by
  ext N
  simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
  intro hN
  exact germ.mem_invtSubmodule_endpointTransitionEnd (hN.trans hV)

/-- The algebra-invariant subspaces of a harmonic subspace `V` are exactly
all the subspaces of `V`. -/
theorem setOf_algebraInvariant_le_eq_setOf_le
    (germ : G.AnalyticBellmanGerm)
    {V : Submodule ℝ (G.State → Payoff ι)}
    (hV : V ≤ germ.endpointHarmonicSubmodule) :
    {N : Submodule ℝ (G.State → Payoff ι) |
        N ≤ V ∧ ∀ f ∈ Algebra.adjoin ℝ
          ({germ.endpointTransitionEnd} :
            Set (Module.End ℝ (G.State → Payoff ι))),
          ∀ W ∈ N, f W ∈ N} =
      {N : Submodule ℝ (G.State → Payoff ι) | N ≤ V} := by
  ext N
  simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
  intro hN f hf W hW
  exact germ.mapsTo_of_mem_adjoin_endpointTransitionEnd (hN.trans hV) hf hW

/-- Every dimension below `Module.finrank ℝ V` is realised by an invariant
subspace of a harmonic subspace `V`. -/
theorem exists_invtSubmodule_finrank_eq
    (germ : G.AnalyticBellmanGerm)
    {V : Submodule ℝ (G.State → Payoff ι)}
    (hV : V ≤ germ.endpointHarmonicSubmodule)
    {k : ℕ} (hk : k ≤ Module.finrank ℝ V) :
    ∃ N : Submodule ℝ (G.State → Payoff ι),
      N ≤ V ∧ N ∈ Module.End.invtSubmodule germ.endpointTransitionEnd ∧
        Module.finrank ℝ N = k := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V :=
    Module.finBasis ℝ V
  have hli : LinearIndependent ℝ fun i : Fin k => b (Fin.castLE hk i) :=
    b.linearIndependent.comp _ (Fin.castLE_injective hk)
  refine ⟨(Submodule.span ℝ
      (Set.range fun i : Fin k => b (Fin.castLE hk i))).map V.subtype,
    Submodule.map_subtype_le V _, ?_, ?_⟩
  · exact germ.mem_invtSubmodule_endpointTransitionEnd
      ((Submodule.map_subtype_le V _).trans hV)
  · rw [Submodule.finrank_map_subtype_eq, finrank_span_eq_card hli,
      Fintype.card_fin]

/-- A harmonic subspace `V` carries a full flag of invariant subspaces. -/
theorem exists_invtSubmodule_flag
    (germ : G.AnalyticBellmanGerm)
    {V : Submodule ℝ (G.State → Payoff ι)}
    (hV : V ≤ germ.endpointHarmonicSubmodule) :
    ∃ c : Fin (Module.finrank ℝ V + 1) →
        Submodule ℝ (G.State → Payoff ι),
      StrictMono c ∧ c 0 = ⊥ ∧ c (Fin.last _) = V ∧
        ∀ i, c i ≤ V ∧
          c i ∈ Module.End.invtSubmodule germ.endpointTransitionEnd := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V :=
    Module.finBasis ℝ V
  let c : Fin (Module.finrank ℝ V + 1) →
      Submodule ℝ (G.State → Payoff ι) := fun k =>
    (Submodule.span ℝ (Set.range fun i : Fin (k : ℕ) =>
      b (Fin.castLE (Nat.lt_succ_iff.mp k.isLt) i))).map V.subtype
  have hle : ∀ k, c k ≤ V := fun k => Submodule.map_subtype_le V _
  have hrank : ∀ k, Module.finrank ℝ (c k) = (k : ℕ) := by
    intro k
    have hli : LinearIndependent ℝ fun i : Fin (k : ℕ) =>
        b (Fin.castLE (Nat.lt_succ_iff.mp k.isLt) i) :=
      b.linearIndependent.comp _ (Fin.castLE_injective _)
    change Module.finrank ℝ ((Submodule.span ℝ _).map V.subtype) = (k : ℕ)
    rw [Submodule.finrank_map_subtype_eq, finrank_span_eq_card hli,
      Fintype.card_fin]
  have hmono : Monotone c := by
    intro k l hkl
    refine Submodule.map_mono (Submodule.span_mono ?_)
    rintro x ⟨i, rfl⟩
    exact ⟨⟨(i : ℕ), lt_of_lt_of_le i.isLt (Fin.le_def.mp hkl)⟩, rfl⟩
  have hinj : Function.Injective c := by
    intro k l hkl
    have hval : (k : ℕ) = (l : ℕ) := by
      rw [← hrank k, ← hrank l, hkl]
    exact Fin.ext hval
  refine ⟨c, hmono.strictMono_of_injective hinj, ?_, ?_,
    fun k => ⟨hle k, ?_⟩⟩
  · refine Submodule.finrank_eq_zero.mp ?_
    simpa using hrank 0
  · refine Submodule.eq_of_le_of_finrank_eq (hle _) ?_
    rw [hrank, Fin.val_last]
  · exact germ.mem_invtSubmodule_endpointTransitionEnd ((hle k).trans hV)

/-- **The filtration carries only the rank.**  The longest chain of
invariant subspaces of a harmonic subspace `V` has length exactly
`Module.finrank ℝ V`, so no invariant filtration of `V` refines the plain
linear dimension already used as the harmonic-jet rank. -/
theorem isGreatest_invtSubmodule_chain_length
    (germ : G.AnalyticBellmanGerm)
    {V : Submodule ℝ (G.State → Payoff ι)}
    (hV : V ≤ germ.endpointHarmonicSubmodule) :
    IsGreatest
      {n : ℕ | ∃ c : Fin (n + 1) → Submodule ℝ (G.State → Payoff ι),
        StrictMono c ∧ ∀ i, c i ≤ V ∧
          c i ∈ Module.End.invtSubmodule germ.endpointTransitionEnd}
      (Module.finrank ℝ V) := by
  constructor
  · obtain ⟨c, hc, _, _, hall⟩ := germ.exists_invtSubmodule_flag hV
    exact ⟨c, hc, hall⟩
  · rintro n ⟨c, hc, hall⟩
    exact strictSubmoduleChain_length_le_finrank c hc fun i => (hall i).1

/-- The same exact chain-length result for invariance under every element of
the algebra generated by the endpoint transition operator.  This is the
algebra-level form of the statement that the associated module filtration is
no finer than ordinary linear dimension. -/
theorem isGreatest_algebraInvariant_chain_length
    (germ : G.AnalyticBellmanGerm)
    {V : Submodule ℝ (G.State → Payoff ι)}
    (hV : V ≤ germ.endpointHarmonicSubmodule) :
    IsGreatest
      {n : ℕ | ∃ c : Fin (n + 1) → Submodule ℝ (G.State → Payoff ι),
        StrictMono c ∧ ∀ i, c i ≤ V ∧
          ∀ f ∈ Algebra.adjoin ℝ
            ({germ.endpointTransitionEnd} :
              Set (Module.End ℝ (G.State → Payoff ι))),
            ∀ W ∈ c i, f W ∈ c i}
      (Module.finrank ℝ V) := by
  constructor
  · obtain ⟨c, hc, _, _, hall⟩ := germ.exists_invtSubmodule_flag hV
    refine ⟨c, hc, fun i => ⟨(hall i).1, ?_⟩⟩
    intro f hf W hW
    exact germ.mapsTo_of_mem_adjoin_endpointTransitionEnd
      ((hall i).1.trans hV) hf hW
  · rintro n ⟨c, hc, hall⟩
    exact strictSubmoduleChain_length_le_finrank c hc fun i => (hall i).1

end AnalyticBellmanGerm

end StochasticGame
end GameTheory

end
