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
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) (i : ι)
    (fi : I.LocalTrace i → Option (M.Act i)) :
    (behavioralToMixed I σ i) fi =
      ∏ p : I.LocalTrace i, (σ i p) (fi p) := by
  simp [behavioralToMixed, pmfPi_apply]

/-- The joint measure `mixedJoint (behavioralToMixed σ)` decomposes as a double
product over controllers and coordinates. -/
theorem mixedJoint_behavioralToMixed_apply_prod
    [Fintype ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    (σ : BehavioralProfile I) (π : PureProfile I) :
    (mixedJoint (I := I) (behavioralToMixed I σ)) π =
      ∏ i, ∏ p : I.LocalTrace i, (σ i p) (π i p) := by
  simp [mixedJoint, behavioralToMixed_apply_prod]

/-- Explicit flattening formula for the joint law of `behavioralToMixed κ`. -/
theorem mixedJoint_behavioralToMixed_eq_map_reassemble
    [Fintype ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [DecidableEq I.CoordIdx]
    (κ : ∀ i, I.LocalTrace i → PMF (Option (M.Act i))) :
    mixedJoint (I := I) (behavioralToMixed (I := I) κ) =
      PMF.map (I.reassemblePolicy) (pmfPi (fun k : I.CoordIdx => κ k.1 k.2)) := by
  classical
  let τ : ∀ k : I.CoordIdx, PMF (Option (M.Act k.1)) := fun k => κ k.1 k.2
  let e : I.FlatPolicy ≃ PureProfile I :=
    { toFun := I.reassemblePolicy
      invFun := fun π k => π k.1 k.2
      left_inv := by intro ω; funext k; rfl
      right_inv := by intro π; funext i v; rfl }
  ext π
  calc
    (mixedJoint (I := I) (behavioralToMixed (I := I) κ)) π
        = ∏ i, ∏ p : I.LocalTrace i, (κ i p) (π i p) := by
            exact mixedJoint_behavioralToMixed_apply_prod (I := I) κ π
    _ = ∏ k : I.CoordIdx, (κ k.1 k.2) (π k.1 k.2) := by
            change
              (∏ i, ∏ p : I.LocalTrace i, (κ i p) (π i p)) =
              ∏ k : Sigma (fun i => I.LocalTrace i), (κ k.1 k.2) (π k.1 k.2)
            simpa [Finset.univ_sigma_univ (κ := fun i => I.LocalTrace i)] using
              (Finset.prod_sigma' (s := (Finset.univ : Finset ι))
                (t := fun i => (Finset.univ : Finset (I.LocalTrace i)))
                (f := fun i p => (κ i p) (π i p)))
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
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [DecidableEq I.CoordIdx]
    (κ : ∀ i, I.LocalTrace i → PMF (Option (M.Act i))) :
    ∃ τ : ∀ k : I.CoordIdx, PMF (Option (M.Act k.1)),
      mixedJoint (I := I) (behavioralToMixed (I := I) κ) =
      PMF.map (I.reassemblePolicy) (pmfPi τ) := by
  refine ⟨(fun k : I.CoordIdx => κ k.1 k.2), ?_⟩
  simpa using mixedJoint_behavioralToMixed_eq_map_reassemble (I := I) κ

end InfoModel
end GameTheory
