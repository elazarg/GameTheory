import GameTheory.Model.Lemmas.Profiles
import GameTheory.Model.Lemmas.Coordinates
import Math.PMFProduct
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace GameTheory
namespace InfoModel

open scoped BigOperators
open Execution
open Math.PMFProduct

variable {ι : Type}
variable {M : LSM ι} (I : InfoModel M)

/-- Atomic coordinate factorization over `CoordIdx`. -/
def AtomicCoordinateFactorization
    [Fintype ι]
    [Fintype M.Label]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : MixedProfile (I := I)) : Prop := by
  classical
  exact
    ∃ τ : ∀ k : I.CoordIdx, PMF (Option (M.Act k.1)),
      mixedJoint (I := I) μ = PMF.map (I.reassemblePolicy) (pmfPi τ)

/-- Each player's behavioral-to-mixed PMF decomposes as a product over coordinates. -/
theorem behavioralToMixed_apply_prod
    [Fintype M.Label] [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) (i : ι)
    (fi : M.Label → I.LocalTrace i → Option (M.Act i)) :
    (behavioralToMixed I σ i) fi =
      ∏ p : M.Label × I.LocalTrace i, (σ i p.1 p.2) (fi p.1 p.2) := by
  classical
  simp only [behavioralToMixed, PMF.map_apply, pmfPi_apply]
  rw [tsum_eq_single (Function.uncurry fi)]
  · simp [Equiv.curry, Function.uncurry]
  · intro g hg
    simp only [Equiv.curry, Equiv.coe_fn_mk]
    rw [if_neg]
    intro heq
    exact hg (funext fun ⟨a, b⟩ => (congrFun (congrFun heq a) b).symm)

/-- The joint measure `mixedJoint (behavioralToMixed σ)` decomposes as a double
product over controllers and coordinates. -/
theorem mixedJoint_behavioralToMixed_apply_prod
    [Fintype ι]
    [Fintype M.Label] [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    (σ : BehavioralProfile I) (π : PureProfile I) :
    (mixedJoint (I := I) (behavioralToMixed I σ)) π =
      ∏ i, ∏ p : M.Label × I.LocalTrace i, (σ i p.1 p.2) (π i p.1 p.2) := by
  simp only [mixedJoint, pmfPi_apply]
  congr 1
  funext i
  exact behavioralToMixed_apply_prod I σ i (π i)

/-- Explicit flattening formula for the joint law of `behavioralToMixed κ`. -/
theorem mixedJoint_behavioralToMixed_eq_map_reassemble
    [Fintype ι]
    [Fintype M.Label]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [DecidableEq I.CoordIdx]
    (κ : ∀ i, M.Label → I.LocalTrace i → PMF (Option (M.Act i))) :
    mixedJoint (I := I) (behavioralToMixed (I := I) κ) =
      PMF.map (I.reassemblePolicy) (pmfPi (fun k : I.CoordIdx => κ k.1 k.2.1 k.2.2)) := by
  classical
  let τ : ∀ k : I.CoordIdx, PMF (Option (M.Act k.1)) := fun k => κ k.1 k.2.1 k.2.2
  let e : I.FlatPolicy ≃ PureProfile I :=
    { toFun := I.reassemblePolicy
      invFun := fun π k => π k.1 k.2.1 k.2.2
      left_inv := by intro ω; funext k; rfl
      right_inv := by intro π; funext i ℓ v; rfl }
  ext π
  calc
    (mixedJoint (I := I) (behavioralToMixed (I := I) κ)) π
        = ∏ i, ∏ p : M.Label × I.LocalTrace i, (κ i p.1 p.2) (π i p.1 p.2) := by
            exact mixedJoint_behavioralToMixed_apply_prod (I := I) κ π
    _ = ∏ k : I.CoordIdx, (κ k.1 k.2.1 k.2.2) (π k.1 k.2.1 k.2.2) := by
            change
              (∏ i, ∏ p : M.Label × I.LocalTrace i, (κ i p.1 p.2) (π i p.1 p.2)) =
              ∏ k : Sigma (fun i => M.Label × I.LocalTrace i),
                (κ k.1 k.2.1 k.2.2) (π k.1 k.2.1 k.2.2)
            simpa [Finset.univ_sigma_univ (κ := fun i => M.Label × I.LocalTrace i)] using
              (Finset.prod_sigma' (s := (Finset.univ : Finset ι))
                (t := fun i => (Finset.univ : Finset (M.Label × I.LocalTrace i)))
                (f := fun i p => (κ i p.1 p.2) (π i p.1 p.2)))
    _ = (pmfPi τ) (e.symm π) := by
            simp [τ, e, pmfPi_apply]
    _ = (PMF.map e (pmfPi τ)) π := by
            rw [PMF.map_apply, tsum_eq_single (e.symm π)]
            · simp
            · intro a ha
              by_cases h : π = e a
              · exfalso
                exact ha (by simpa using (congrArg e.symm h).symm)
              · simp [h]
    _ = (PMF.map (I.reassemblePolicy) (pmfPi τ)) π := by
            rfl

/-- Canonical mixed profile induced by local kernels is coordinate-factorized. -/
theorem atomicFactorization_of_localKernels
    [Fintype ι]
    [Fintype M.Label]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [DecidableEq I.CoordIdx]
    (κ : ∀ i, M.Label → I.LocalTrace i → PMF (Option (M.Act i))) :
    ∃ τ : ∀ k : I.CoordIdx, PMF (Option (M.Act k.1)),
      mixedJoint (I := I) (behavioralToMixed (I := I) κ) =
      PMF.map (I.reassemblePolicy) (pmfPi τ) := by
  refine ⟨(fun k : I.CoordIdx => κ k.1 k.2.1 k.2.2), ?_⟩
  simpa using mixedJoint_behavioralToMixed_eq_map_reassemble (I := I) κ

end InfoModel
end GameTheory
