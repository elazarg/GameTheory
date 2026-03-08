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
variable {σ : Type} {Act : ι → Type} (I : InfoModel ι σ Act)

/-- Atomic coordinate factorization over `CoordIdx`. -/
def AtomicCoordinateFactorization
    [Fintype ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (Act i))]
    (μ : MixedProfile (I := I)) : Prop := by
  classical
  exact
    ∃ τ : ∀ k : I.CoordIdx, PMF (Option (Act k.1)),
      mixedJoint (I := I) μ = PMF.map (I.reassemblePolicy) (pmfPi τ)

/-- Each player's behavioral-to-mixed PMF decomposes as a product over coordinates. -/
theorem behavioralToMixed_apply_prod
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (Act i))]
    (b : BehavioralProfile I) (i : ι)
    (fi : I.LocalTrace i → Option (Act i)) :
    (behavioralToMixed I b i) fi =
      ∏ p : I.LocalTrace i, (b i p) (fi p) := by
  simp [behavioralToMixed, pmfPi_apply]

/-- The joint measure `mixedJoint (behavioralToMixed σ)` decomposes as a double
product over controllers and coordinates. -/
theorem mixedJoint_behavioralToMixed_apply_prod
    [Fintype ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    (b : BehavioralProfile I) (π : PureProfile I) :
    (mixedJoint (I := I) (behavioralToMixed I b)) π =
      ∏ i, ∏ p : I.LocalTrace i, (b i p) (π i p) := by
  simp [mixedJoint, behavioralToMixed_apply_prod]

/-- Explicit flattening formula for the joint law of `behavioralToMixed κ`. -/
theorem mixedJoint_behavioralToMixed_eq_map_reassemble
    [Fintype ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [DecidableEq I.CoordIdx]
    (κ : ∀ i, I.LocalTrace i → PMF (Option (Act i))) :
    mixedJoint (I := I) (behavioralToMixed (I := I) κ) =
      PMF.map (I.reassemblePolicy) (pmfPi (fun k : I.CoordIdx => κ k.1 k.2)) := by
  classical
  let τ : ∀ k : I.CoordIdx, PMF (Option (Act k.1)) := fun k => κ k.1 k.2
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
    [∀ i, Fintype (Option (Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [DecidableEq I.CoordIdx]
    (κ : ∀ i, I.LocalTrace i → PMF (Option (Act i))) :
    ∃ τ : ∀ k : I.CoordIdx, PMF (Option (Act k.1)),
      mixedJoint (I := I) (behavioralToMixed (I := I) κ) =
      PMF.map (I.reassemblePolicy) (pmfPi τ) := by
  refine ⟨(fun k : I.CoordIdx => κ k.1 k.2), ?_⟩
  simpa using mixedJoint_behavioralToMixed_eq_map_reassemble (I := I) κ

section Restricted

variable [∀ i, DecidableEq (I.LocalTrace i)]

/-- Each player's restricted behavioral-to-mixed PMF decomposes as a product
over the covered coordinates. -/
theorem restrictedBehavioralToMixed_apply_prod
    (H : ∀ i, Finset (I.LocalTrace i))
    [∀ i, Fintype (I.RestrictedLocalCoord H i)]
    [∀ i, Fintype (Option (Act i))]
    (b : RestrictedBehavioralProfile (I := I) H) (i : ι)
    (fi : RestrictedLocalCoord (I := I) H i → Option (Act i)) :
    (restrictedBehavioralToMixed (I := I) H b i) fi =
      ∏ p : RestrictedLocalCoord (I := I) H i, (b i p) (fi p) := by
  simp [restrictedBehavioralToMixed, pmfPi_apply]

/-- The raw restricted joint measure decomposes as a double product over
controllers and covered coordinates. -/
theorem restrictedMixedJointRaw_behavioralToMixed_apply_prod
    (H : ∀ i, Finset (I.LocalTrace i))
    [Fintype ι]
    [∀ i, Fintype (I.RestrictedLocalCoord H i)]
    [∀ i, Fintype (Option (Act i))]
    [∀ i, Fintype (RestrictedLocalPure (I := I) H i)]
    (b : RestrictedBehavioralProfile (I := I) H)
    (π : RestrictedPureProfile (I := I) H) :
    (restrictedMixedJointRaw (I := I) H
      (restrictedBehavioralToMixed (I := I) H b)) π =
      ∏ i, ∏ p : RestrictedLocalCoord (I := I) H i, (b i p) (π i p) := by
  simp [restrictedMixedJointRaw, restrictedBehavioralToMixed_apply_prod]

/-- Explicit flattening formula for the raw joint law of `restrictedBehavioralToMixed κ`. -/
theorem restrictedMixedJointRaw_behavioralToMixed_eq_map_reassemble
    (H : ∀ i, Finset (I.LocalTrace i))
    [Fintype ι]
    [∀ i, Fintype (I.RestrictedLocalCoord H i)]
    [∀ i, Fintype (Option (Act i))]
    [∀ i, Fintype (RestrictedLocalPure (I := I) H i)]
    [DecidableEq (Σ i, I.RestrictedLocalCoord H i)]
    (κ : ∀ i, RestrictedLocalCoord (I := I) H i → PMF (Option (Act i))) :
    restrictedMixedJointRaw (I := I) H
      (restrictedBehavioralToMixed (I := I) H κ) =
      PMF.map
        (fun ω : (∀ k : Σ i, I.RestrictedLocalCoord H i, Option (Act k.1)) =>
          fun i v => ω ⟨i, v⟩)
        (pmfPi (fun k : Σ i, I.RestrictedLocalCoord H i => κ k.1 k.2)) := by
  classical
  let τ : ∀ k : Σ i, I.RestrictedLocalCoord H i, PMF (Option (Act k.1)) :=
    fun k => κ k.1 k.2
  let e :
      (∀ k : Σ i, I.RestrictedLocalCoord H i, Option (Act k.1)) ≃
        RestrictedPureProfile (I := I) H :=
    { toFun := fun ω i v => ω ⟨i, v⟩
      invFun := fun π k => π k.1 k.2
      left_inv := by intro ω; funext k; rfl
      right_inv := by intro π; funext i v; rfl }
  ext π
  calc
    (restrictedMixedJointRaw (I := I) H
      (restrictedBehavioralToMixed (I := I) H κ)) π
        = ∏ i, ∏ p : RestrictedLocalCoord (I := I) H i, (κ i p) (π i p) := by
            exact restrictedMixedJointRaw_behavioralToMixed_apply_prod (I := I) H κ π
    _ = ∏ k : Sigma (fun i => I.RestrictedLocalCoord H i), (κ k.1 k.2) (π k.1 k.2) := by
          simpa [Finset.univ_sigma_univ (κ := fun i => I.RestrictedLocalCoord H i)] using
            (Finset.prod_sigma' (s := (Finset.univ : Finset ι))
              (t := fun i => (Finset.univ : Finset (I.RestrictedLocalCoord H i)))
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
    _ =
      (PMF.map
        (fun ω : (∀ k : Σ i, I.RestrictedLocalCoord H i, Option (Act k.1)) =>
          fun i v => ω ⟨i, v⟩)
        (pmfPi τ)) π := by
          rfl

end Restricted

end InfoModel
end GameTheory
