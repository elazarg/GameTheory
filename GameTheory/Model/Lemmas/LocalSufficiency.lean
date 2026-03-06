import GameTheory.Model.Lemmas.Profiles

namespace GameTheory
namespace InfoModel

open Execution

variable {ι : Type} [Fintype ι]
variable {M : LSM ι} (I : InfoModel M)
variable (D : Execution.Dynamics I)

/-- Local-history sufficiency for one-step law (distribution form).

At depth `n`, if two prefixes induce identical local observation traces for all
controllers, then the mixed-averaged one-step pure continuation kernels agree. -/
theorem oneStep_law_depends_only_on_localTraces
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : InfoModel.MixedProfile (I := I))
    (n : Nat)
    {hs₁ hs₂ : List M.Label × List M.State}
    (hlen₁ : hs₁.2.length = n + 1)
    (hlen₂ : hs₂.2.length = n + 1)
    (hloc : ∀ i, I.projectStates i hs₁.2 = I.projectStates i hs₂.2) :
    (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
      Math.ProbabilityMassFunction.pushforward
        (D.stepDist (pureToBehavioral I π) hs₁.2)
        (fun ls => (hs₁.1 ++ [ls.1], hs₁.2 ++ [ls.2])))
    =
    (InfoModel.mixedJoint (I := I) μ).bind (fun π =>
      Math.ProbabilityMassFunction.pushforward
        (D.stepDist (pureToBehavioral I π) hs₂.2)
        (fun ls => (hs₂.1 ++ [ls.1], hs₂.2 ++ [ls.2]))) := by
  sorry

/-- Local-history sufficiency for one-step law (scalar/pointwise form).

Pointwise version at a queried outcome `y`, matching tsum-based proof steps. -/
theorem oneStep_scalar_depends_only_on_localTraces
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : InfoModel.MixedProfile (I := I))
    (n : Nat)
    (y : List M.Label × List M.State)
    {hs₁ hs₂ : List M.Label × List M.State}
    (hlen₁ : hs₁.2.length = n + 1)
    (hlen₂ : hs₂.2.length = n + 1)
    (hloc : ∀ i, I.projectStates i hs₁.2 = I.projectStates i hs₂.2) :
    (∑' π, (InfoModel.mixedJoint (I := I) μ) π *
      ((D.runDistPure n π) hs₁ *
        (Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) hs₁.2)
          (fun ls => (hs₁.1 ++ [ls.1], hs₁.2 ++ [ls.2]))) y))
    =
    (∑' π, (InfoModel.mixedJoint (I := I) μ) π *
      ((D.runDistPure n π) hs₂ *
        (Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) hs₂.2)
          (fun ls => (hs₂.1 ++ [ls.1], hs₂.2 ++ [ls.2]))) y)) := by
  sorry

end InfoModel
end GameTheory

