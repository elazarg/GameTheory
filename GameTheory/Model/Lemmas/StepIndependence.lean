import GameTheory.Model.Lemmas.Profiles
import GameTheory.Model.Lemmas.AtomicFactorization
import GameTheory.Model.Lemmas.ExecutionLocality

namespace GameTheory
namespace InfoModel

open Execution
open Math.PMFProduct

variable {ι : Type} [Fintype ι]
variable {σ : Type} {Act : ι → Type} (I : InfoModel ι σ Act)

/-- **Scalar independence under the behavioral product measure.**
`E[f·g] = E[f]·E[g]` when `f` depends only on coordinates with private-history
length `≤ n` and `g` depends only on coordinates with private-history length
`> n`. -/
theorem behavioralToMixed_scalar_indep
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    (b : BehavioralProfile I) (n : Nat)
    (f g : PureProfile I → ENNReal)
    (hf : ∀ π π' : PureProfile I,
      (∀ i (v : I.LocalTrace i), v.2.length ≤ n → π i v = π' i v) → f π = f π')
    (hg : ∀ π π' : PureProfile I,
      (∀ i (v : I.LocalTrace i), v.2.length > n → π i v = π' i v) → g π = g π') :
    ∑ π, (mixedJoint I (behavioralToMixed I b)) π * (f π * g π) =
    (∑ π, (mixedJoint I (behavioralToMixed I b)) π * f π) *
    (∑ π, (mixedJoint I (behavioralToMixed I b)) π * g π) := by
  classical
  set μ := mixedJoint I (behavioralToMixed I b)
  let swap : PureProfile I → PureProfile I → PureProfile I :=
    fun π₁ π₂ i v => if v.2.length ≤ n then π₁ i v else π₂ i v
  have hweight_i : ∀ (π₁ π₂ : PureProfile I) (i : ι),
      (behavioralToMixed I b i) (swap π₁ π₂ i) *
      (behavioralToMixed I b i) (swap π₂ π₁ i) =
      (behavioralToMixed I b i) (π₁ i) *
      (behavioralToMixed I b i) (π₂ i) := by
    intro π₁ π₂ i
    simp only [behavioralToMixed_apply_prod, swap]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    funext v
    by_cases hv : v.2.length ≤ n <;> simp [hv, mul_comm]
  have hweight : ∀ (π₁ π₂ : PureProfile I),
      μ (swap π₁ π₂) * μ (swap π₂ π₁) = μ π₁ * μ π₂ := by
    intro π₁ π₂
    simp only [μ, mixedJoint, pmfPi_apply]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    funext i
    exact hweight_i π₁ π₂ i
  have hf_swap : ∀ π₁ π₂, f (swap π₁ π₂) = f π₁ := by
    intro π₁ π₂
    apply hf
    intro i v hv
    simp [swap, hv]
  have hg_swap : ∀ π₁ π₂, g (swap π₁ π₂) = g π₂ := by
    intro π₁ π₂
    apply hg
    intro i v hv
    simp only [swap]
    rw [if_neg (Nat.not_le.mpr hv)]
  let P := fun π => μ π
  let Fsame : PureProfile I × PureProfile I → ENNReal :=
    fun p => P p.1 * P p.2 * (f p.1 * g p.1)
  let Fcross : PureProfile I × PureProfile I → ENNReal :=
    fun p => P p.1 * P p.2 * (f p.1 * g p.2)
  let e : PureProfile I × PureProfile I → PureProfile I × PureProfile I :=
    fun p => (swap p.1 p.2, swap p.2 p.1)
  have he : Function.Involutive e := by
    intro ⟨π₁, π₂⟩
    apply Prod.ext <;> (funext i v; simp only [e, swap]; split <;> rfl)
  have hpoint : ∀ p, Fcross p = Fsame (e p) := by
    intro ⟨π₁, π₂⟩
    simp only [Fcross, Fsame, e, P]
    rw [hweight π₁ π₂, hf_swap, hg_swap]
  have hpair : (∑ p, Fcross p) = ∑ p, Fsame p := by
    calc (∑ p, Fcross p) = ∑ p, Fsame (e p) :=
            Finset.sum_congr rfl (fun p _ => hpoint p)
      _ = ∑ p, Fsame p := sum_univ_eq_sum_univ_of_involutive e he Fsame
  have hsumP : (∑ π, P π) = 1 := by
    simp only [P]
    exact (tsum_fintype (fun π => μ π)).symm.trans μ.tsum_coe
  calc ∑ π, μ π * (f π * g π)
      = (∑ π, μ π * (f π * g π)) * 1 := (mul_one _).symm
    _ = (∑ π, μ π * (f π * g π)) * ∑ π₂, P π₂ := by rw [hsumP]
    _ = ∑ π₁, ∑ π₂, μ π₁ * (f π₁ * g π₁) * P π₂ := Finset.sum_mul_sum ..
    _ = ∑ p : _ × _, Fsame p := by
        rw [← Fintype.sum_prod_type']
        congr 1
        ext ⟨π₁, π₂⟩
        simp only [Fsame, P]
        ring
    _ = ∑ p : _ × _, Fcross p := hpair.symm
    _ = ∑ π₁, ∑ π₂, μ π₁ * f π₁ * (μ π₂ * g π₂) := by
        rw [← Fintype.sum_prod_type']
        congr 1
        ext ⟨π₁, π₂⟩
        simp only [Fcross, P]
        ring
    _ = (∑ π, μ π * f π) * ∑ π, μ π * g π := (Finset.sum_mul_sum ..).symm

section Restricted

variable [∀ i, DecidableEq (I.LocalTrace i)]

/-- Scalar independence under the restricted behavioral product measure. The
proof is the same as the full-coordinate version, but only the coordinates in
the finite cover `H` are present. -/
theorem restrictedBehavioralToMixed_scalar_indep
    (H : ∀ i, Finset (I.LocalTrace i))
    [DecidableEq ι]
    [∀ i, Fintype (I.RestrictedLocalCoord H i)]
    [∀ i, Fintype (Option (Act i))]
    [∀ i, Fintype (RestrictedLocalPure (I := I) H i)]
    (b : RestrictedBehavioralProfile (I := I) H) (n : Nat)
    (f g : RestrictedPureProfile (I := I) H → ENNReal)
    (hf : ∀ π π' : RestrictedPureProfile (I := I) H,
      (∀ i (v : RestrictedLocalCoord (I := I) H i), v.1.2.length ≤ n → π i v = π' i v) →
        f π = f π')
    (hg : ∀ π π' : RestrictedPureProfile (I := I) H,
      (∀ i (v : RestrictedLocalCoord (I := I) H i), v.1.2.length > n → π i v = π' i v) →
        g π = g π') :
    ∑ π, (restrictedMixedJointRaw (I := I) H
      (restrictedBehavioralToMixed (I := I) H b)) π * (f π * g π) =
    (∑ π, (restrictedMixedJointRaw (I := I) H
      (restrictedBehavioralToMixed (I := I) H b)) π * f π) *
    (∑ π, (restrictedMixedJointRaw (I := I) H
      (restrictedBehavioralToMixed (I := I) H b)) π * g π) := by
  classical
  set μ :=
    restrictedMixedJointRaw (I := I) H (restrictedBehavioralToMixed (I := I) H b)
  let swap :
      RestrictedPureProfile (I := I) H →
      RestrictedPureProfile (I := I) H →
      RestrictedPureProfile (I := I) H :=
    fun π₁ π₂ i v => if v.1.2.length ≤ n then π₁ i v else π₂ i v
  have hweight_i :
      ∀ (π₁ π₂ : RestrictedPureProfile (I := I) H) (i : ι),
        (restrictedBehavioralToMixed (I := I) H b i) (swap π₁ π₂ i) *
        (restrictedBehavioralToMixed (I := I) H b i) (swap π₂ π₁ i) =
        (restrictedBehavioralToMixed (I := I) H b i) (π₁ i) *
        (restrictedBehavioralToMixed (I := I) H b i) (π₂ i) := by
    intro π₁ π₂ i
    simp only [restrictedBehavioralToMixed_apply_prod, swap]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    funext v
    by_cases hv : v.1.2.length ≤ n <;> simp [hv, mul_comm]
  have hweight :
      ∀ (π₁ π₂ : RestrictedPureProfile (I := I) H),
        μ (swap π₁ π₂) * μ (swap π₂ π₁) = μ π₁ * μ π₂ := by
    intro π₁ π₂
    simp only [μ, restrictedMixedJointRaw, pmfPi_apply]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    funext i
    exact hweight_i π₁ π₂ i
  have hf_swap : ∀ π₁ π₂, f (swap π₁ π₂) = f π₁ := by
    intro π₁ π₂
    apply hf
    intro i v hv
    simp [swap, hv]
  have hg_swap : ∀ π₁ π₂, g (swap π₁ π₂) = g π₂ := by
    intro π₁ π₂
    apply hg
    intro i v hv
    simp only [swap]
    rw [if_neg (Nat.not_le.mpr hv)]
  let P := fun π => μ π
  let Fsame : RestrictedPureProfile (I := I) H × RestrictedPureProfile (I := I) H → ENNReal :=
    fun p => P p.1 * P p.2 * (f p.1 * g p.1)
  let Fcross : RestrictedPureProfile (I := I) H × RestrictedPureProfile (I := I) H → ENNReal :=
    fun p => P p.1 * P p.2 * (f p.1 * g p.2)
  let e :
      RestrictedPureProfile (I := I) H × RestrictedPureProfile (I := I) H →
      RestrictedPureProfile (I := I) H × RestrictedPureProfile (I := I) H :=
    fun p => (swap p.1 p.2, swap p.2 p.1)
  have he : Function.Involutive e := by
    intro ⟨π₁, π₂⟩
    apply Prod.ext <;> (funext i v; simp only [e, swap]; split <;> rfl)
  have hpoint : ∀ p, Fcross p = Fsame (e p) := by
    intro ⟨π₁, π₂⟩
    simp only [Fcross, Fsame, e, P]
    rw [hweight π₁ π₂, hf_swap, hg_swap]
  have hpair : (∑ p, Fcross p) = ∑ p, Fsame p := by
    calc (∑ p, Fcross p) = ∑ p, Fsame (e p) :=
            Finset.sum_congr rfl (fun p _ => hpoint p)
      _ = ∑ p, Fsame p := sum_univ_eq_sum_univ_of_involutive e he Fsame
  have hsumP : (∑ π, P π) = 1 := by
    simp only [P]
    exact (tsum_fintype (fun π => μ π)).symm.trans μ.tsum_coe
  calc
    ∑ π, μ π * (f π * g π)
        = (∑ π, μ π * (f π * g π)) * 1 := (mul_one _).symm
    _ = (∑ π, μ π * (f π * g π)) * ∑ π₂, P π₂ := by rw [hsumP]
    _ = ∑ π₁, ∑ π₂, μ π₁ * (f π₁ * g π₁) * P π₂ := Finset.sum_mul_sum ..
    _ = ∑ p : _ × _, Fsame p := by
        rw [← Fintype.sum_prod_type']
        congr 1
        ext ⟨π₁, π₂⟩
        simp only [Fsame, P]
        ring
    _ = ∑ p : _ × _, Fcross p := hpair.symm
    _ = ∑ π₁, ∑ π₂, μ π₁ * f π₁ * (μ π₂ * g π₂) := by
        rw [← Fintype.sum_prod_type']
        congr 1
        ext ⟨π₁, π₂⟩
        simp only [Fcross, P]
        ring
    _ = (∑ π, μ π * f π) * ∑ π, μ π * g π := (Finset.sum_mul_sum ..).symm

/-- Restricted step-independence equality used in the bounded finite-cover Kuhn
run induction. Execution still happens on the full machine semantics; the pure
and behavioral profiles are obtained by extending restricted profiles outside
the cover with the deterministic action `none`. -/
def RestrictedStepIndependence
    (D : Execution.Dynamics I)
    (H : ∀ i, Finset (I.LocalTrace i))
    [DecidableEq ι]
    [∀ i, Fintype (RestrictedLocalCoord (I := I) H i)]
    [∀ i, Fintype (RestrictedLocalPure (I := I) H i)]
    [∀ i, Fintype (Option (Act i))]
    (μ : RestrictedMixedProfile (I := I) H) (n : Nat) : Prop :=
    (restrictedMixedJointRaw (I := I) H μ).bind (fun π =>
      (D.runDistPure n (extendRestrictedPureProfile (I := I) H π)).bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (restrictedRealizeBehavioralCanonical (I := I) H μ) ss)
          (fun t => ss ++ [t]))) =
    (restrictedMixedJointRaw (I := I) H μ).bind (fun π =>
      (D.runDistPure n (extendRestrictedPureProfile (I := I) H π)).bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I
            (extendRestrictedPureProfile (I := I) H π)) ss)
          (fun t => ss ++ [t])))

/-- Restricted bridge reduction: if a restricted mixed profile satisfies
step-independence at every depth, then run distributions factor through
sampling a restricted pure profile and executing its full extension. -/
theorem restricted_run_factorization
    (D : Execution.Dynamics I)
    (H : ∀ i, Finset (I.LocalTrace i))
    [DecidableEq ι]
    [∀ i, Fintype (RestrictedLocalCoord (I := I) H i)]
    [∀ i, Fintype (RestrictedLocalPure (I := I) H i)]
    [∀ i, Fintype (Option (Act i))]
    (hStepIndep : ∀ μ n, RestrictedStepIndependence (I := I) D H μ n)
    (μ : RestrictedMixedProfile (I := I) H) :
    ∀ n,
      D.runDist n (restrictedRealizeBehavioralCanonical (I := I) H μ) =
        (restrictedMixedJointRaw (I := I) H μ).bind
          (fun π => D.runDistPure n (extendRestrictedPureProfile (I := I) H π)) := by
  intro n
  induction n with
  | zero =>
      simp [Execution.Dynamics.runDist, Execution.Dynamics.runDistPure]
  | succ n ih =>
      calc
        D.runDist (n + 1) (restrictedRealizeBehavioralCanonical (I := I) H μ)
            = (D.runDist n (restrictedRealizeBehavioralCanonical (I := I) H μ)).bind
                (fun ss =>
                  Math.ProbabilityMassFunction.pushforward
                    (D.stepDist (restrictedRealizeBehavioralCanonical (I := I) H μ) ss)
                    (fun t => ss ++ [t])) := by
              simp [Execution.Dynamics.runDist]
        _ = ((restrictedMixedJointRaw (I := I) H μ).bind
              (fun π => D.runDistPure n (extendRestrictedPureProfile (I := I) H π))).bind
                (fun ss =>
                  Math.ProbabilityMassFunction.pushforward
                    (D.stepDist (restrictedRealizeBehavioralCanonical (I := I) H μ) ss)
                    (fun t => ss ++ [t])) := by
              rw [ih]
        _ = (restrictedMixedJointRaw (I := I) H μ).bind (fun π =>
              (D.runDistPure n (extendRestrictedPureProfile (I := I) H π)).bind (fun ss =>
                Math.ProbabilityMassFunction.pushforward
                  (D.stepDist (restrictedRealizeBehavioralCanonical (I := I) H μ) ss)
                  (fun t => ss ++ [t]))) := by
              rw [PMF.bind_bind]
        _ = (restrictedMixedJointRaw (I := I) H μ).bind (fun π =>
              (D.runDistPure n (extendRestrictedPureProfile (I := I) H π)).bind (fun ss =>
                Math.ProbabilityMassFunction.pushforward
                  (D.stepDist (pureToBehavioral I
                    (extendRestrictedPureProfile (I := I) H π)) ss)
                  (fun t => ss ++ [t]))) := by
              simpa using hStepIndep μ n
        _ = (restrictedMixedJointRaw (I := I) H μ).bind
              (fun π => D.runDistPure (n + 1) (extendRestrictedPureProfile (I := I) H π)) := by
              simp [Execution.Dynamics.runDist, Execution.Dynamics.runDistPure]

end Restricted

/-- Step-independence equality used in the Kuhn run induction. -/
def StepIndependence
    (D : Execution.Dynamics I)
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (Act i))]
    (μ : MixedProfile (I := I)) (n : Nat) : Prop :=
    (mixedJoint (I := I) μ).bind (fun π =>
      (D.runDistPure n π).bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (realizeBehavioralCanonical (I := I) μ) ss)
          (fun t => ss ++ [t]))) =
    (mixedJoint (I := I) μ).bind (fun π =>
      (D.runDistPure n π).bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) ss)
          (fun t => ss ++ [t])))

/-- Transport helper: if a mixed profile is definitionally equal to a
behavioral-induced mixed profile, step-independence transports across the equality. -/
theorem stepIndependence_of_eq_behavioralMixed
    (D : Execution.Dynamics I)
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (Act i))]
    (μ : MixedProfile (I := I))
    (b : BehavioralProfile I)
    (hμ : μ = behavioralToMixed (I := I) b)
    (n : Nat)
    (hStep : StepIndependence (I := I) D (behavioralToMixed (I := I) b) n) :
    StepIndependence (I := I) D μ n := by
  simpa [hμ] using hStep

/-- Remaining probabilistic bridge for behavioral-induced mixed profiles:
factor one-step extension through state-trace prefix sampling. -/
theorem behavioralToMixed_stepIndependence_bridge
    (D : Execution.Dynamics I)
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (Act i))]
    (b : BehavioralProfile I) (n : Nat) :
    (mixedJoint (I := I) (behavioralToMixed (I := I) b)).bind (fun π =>
      (D.runDistPure n π).bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist b ss)
          (fun t => ss ++ [t]))) =
    (mixedJoint (I := I) (behavioralToMixed (I := I) b)).bind (fun π =>
      (D.runDistPure n π).bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) ss)
          (fun t => ss ++ [t]))) := by
  classical
  set μ : PMF (PureProfile I) := mixedJoint (I := I) (behavioralToMixed (I := I) b)
  have hstepMarg :
      ∀ ss : List σ,
        μ.bind (fun π => D.stepDist (pureToBehavioral I π) ss) = D.stepDist b ss := by
    intro ss
    simpa [μ] using (marginal_stepDist (I := I) (D := D) b ss)
  have hRunCongr :
      ∀ ss : List σ, ∀ π π' : PureProfile I,
        (∀ i (v : I.LocalTrace i), v.2.length ≤ n → π i v = π' i v) →
        (D.runDistPure n π) ss = (D.runDistPure n π') ss := by
    intro ss π π' hag
    let ω₁ : I.FlatPolicy := fun k => π k.1 k.2
    let ω₂ : I.FlatPolicy := fun k => π' k.1 k.2
    have hagFlat :
        ∀ i v, v.2.length ≤ n → ω₁ ⟨i, v⟩ = ω₂ ⟨i, v⟩ := by
      intro i v hv
      simpa [ω₁, ω₂] using hag i v hv
    have hEq :
        D.runDistPure n (I.reassemblePolicy ω₁) =
          D.runDistPure n (I.reassemblePolicy ω₂) :=
      runDistPure_depends_on_len_le (I := I) (D := D) n ω₁ ω₂ hagFlat
    simpa [ω₁, ω₂] using congrArg (fun ν => ν ss) hEq
  ext y
  let Lfun : List σ → ENNReal :=
    fun ss =>
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist b ss)
        (fun t => ss ++ [t])) y
  let Gfun : List σ → PureProfile I → ENNReal :=
    fun ss π =>
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (pureToBehavioral I π) ss)
        (fun t => ss ++ [t])) y
  let FL : PureProfile I → List σ → ENNReal :=
    fun π ss => μ π * ((D.runDistPure n π) ss * Lfun ss)
  let FR : PureProfile I → List σ → ENNReal :=
    fun π ss => μ π * ((D.runDistPure n π) ss * Gfun ss π)
  have hswapL :
      (∑' π, μ π * ∑' ss, (D.runDistPure n π) ss * Lfun ss) =
        ∑' ss, ∑' π, FL π ss := by
    calc
      (∑' π, μ π * ∑' ss, (D.runDistPure n π) ss * Lfun ss)
          = ∑' π, ∑' ss, μ π * ((D.runDistPure n π) ss * Lfun ss) := by
              refine tsum_congr ?_
              intro π
              rw [ENNReal.tsum_mul_left]
      _ = ∑' ss, ∑' π, μ π * ((D.runDistPure n π) ss * Lfun ss) := by
            simpa using
              (ENNReal.tsum_comm (f := fun π ss => μ π * ((D.runDistPure n π) ss * Lfun ss)))
      _ = ∑' ss, ∑' π, FL π ss := by simp [FL]
  have hswapR :
      (∑' π, μ π * ∑' ss, (D.runDistPure n π) ss * Gfun ss π) =
        ∑' ss, ∑' π, FR π ss := by
    calc
      (∑' π, μ π * ∑' ss, (D.runDistPure n π) ss * Gfun ss π)
          = ∑' π, ∑' ss, μ π * ((D.runDistPure n π) ss * Gfun ss π) := by
              refine tsum_congr ?_
              intro π
              rw [ENNReal.tsum_mul_left]
      _ = ∑' ss, ∑' π, μ π * ((D.runDistPure n π) ss * Gfun ss π) := by
            simpa using
              (ENNReal.tsum_comm (f := fun π ss => μ π * ((D.runDistPure n π) ss * Gfun ss π)))
      _ = ∑' ss, ∑' π, FR π ss := by simp [FR]
  have hPerSs :
      ∀ ss : List σ, (∑' π, FL π ss) = ∑' π, FR π ss := by
    intro ss
    by_cases hlen : ss.length = n + 1
    · let f : PureProfile I → ENNReal := fun π => (D.runDistPure n π) ss
      let g : PureProfile I → ENNReal := fun π => Gfun ss π
      have hf :
          ∀ π π' : PureProfile I,
            (∀ i (v : I.LocalTrace i), v.2.length ≤ n → π i v = π' i v) →
            f π = f π' := by
        intro π π' hag
        exact hRunCongr ss π π' hag
      have hg :
          ∀ π π' : PureProfile I,
            (∀ i (v : I.LocalTrace i), v.2.length > n → π i v = π' i v) →
            g π = g π' := by
        intro π π' hag
        let ω₁ : I.FlatPolicy := fun k => π k.1 k.2
        let ω₂ : I.FlatPolicy := fun k => π' k.1 k.2
        have hagNow :
            ∀ i,
              ω₁ ⟨i, I.projectStates i ss⟩ =
                ω₂ ⟨i, I.projectStates i ss⟩ := by
          intro i
          have hprojLen : (I.projectStates i ss).2.length = n + 1 := by
            exact (I.projectStates_lengths i ss).2.trans hlen
          have hvlen : (I.projectStates i ss).2.length > n := by
            rw [hprojLen]
            omega
          simpa [ω₁, ω₂] using hag i (I.projectStates i ss) hvlen
        have hstepEq :
            D.stepDist (pureToBehavioral I (I.reassemblePolicy ω₁)) ss =
              D.stepDist (pureToBehavioral I (I.reassemblePolicy ω₂)) ss :=
          stepDist_depends_on_current_context (I := I) (D := D) ω₁ ω₂ ss hagNow
        have hpushEq := congrArg
          (fun ν =>
            (Math.ProbabilityMassFunction.pushforward ν
              (fun t => ss ++ [t])) y)
          hstepEq
        simpa [g, Gfun, ω₁, ω₂] using hpushEq
      have hind :
          ∑ π, μ π * (f π * g π) =
            (∑ π, μ π * f π) * (∑ π, μ π * g π) := by
        simpa [μ] using behavioralToMixed_scalar_indep (I := I) b n f g hf hg
      have hEg :
          (∑ π, μ π * g π) = Lfun ss := by
        have hbindPush :
            (μ.bind (fun π =>
              Math.ProbabilityMassFunction.pushforward
                (D.stepDist (pureToBehavioral I π) ss)
                (fun t => ss ++ [t]))) y = Lfun ss := by
          calc
            (μ.bind (fun π =>
              Math.ProbabilityMassFunction.pushforward
                (D.stepDist (pureToBehavioral I π) ss)
                (fun t => ss ++ [t]))) y
                =
              (Math.ProbabilityMassFunction.pushforward
                (μ.bind (fun π => D.stepDist (pureToBehavioral I π) ss))
                (fun t => ss ++ [t])) y := by
                  simpa using congrArg (fun ν => ν y) (
                    (Math.ProbabilityMassFunction.pushforward_bind
                      (μ := μ)
                      (k := fun π => D.stepDist (pureToBehavioral I π) ss)
                      (f := fun t => ss ++ [t])).symm)
            _ =
              (Math.ProbabilityMassFunction.pushforward
                (D.stepDist b ss)
                (fun t => ss ++ [t])) y := by
                  simp [hstepMarg ss]
            _ = Lfun ss := rfl
        simpa [g, Gfun, PMF.bind_apply] using hbindPush
      calc
        (∑' π, FL π ss) = ∑ π, μ π * (f π * Lfun ss) := by
            simp [FL, f, tsum_fintype, mul_assoc, mul_comm]
        _ = (∑ π, μ π * f π) * Lfun ss := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (Finset.sum_mul (s := Finset.univ) (f := fun π => μ π * f π) (a := Lfun ss)).symm
        _ = (∑ π, μ π * f π) * (∑ π, μ π * g π) := by rw [hEg]
        _ = ∑ π, μ π * (f π * g π) := hind.symm
        _ = (∑' π, FR π ss) := by
            simp [FR, f, g, Gfun, tsum_fintype, mul_assoc, mul_comm]
    · have hfzero : ∀ π : PureProfile I, (D.runDistPure n π) ss = 0 := by
        intro π
        by_contra hne
        have hlen' : ss.length = n + 1 := by
          have hrun : (D.runDist n (pureToBehavioral I π)) ss ≠ 0 := by
            simpa [Execution.Dynamics.runDistPure] using hne
          exact runDist_support_stateLength (I := I) (D := D) n (pureToBehavioral I π) ss hrun
        exact hlen hlen'
      have hFL0 : (∑' π, FL π ss) = 0 := by
        exact (ENNReal.tsum_eq_zero).2 (by intro π; simp [FL, hfzero π])
      have hFR0 : (∑' π, FR π ss) = 0 := by
        exact (ENNReal.tsum_eq_zero).2 (by intro π; simp [FR, hfzero π])
      rw [hFL0, hFR0]
  calc
    ((mixedJoint (I := I) (behavioralToMixed (I := I) b)).bind (fun π =>
      (D.runDistPure n π).bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist b ss)
          (fun t => ss ++ [t])))) y
        = (∑' π, μ π * ∑' ss, (D.runDistPure n π) ss * Lfun ss) := by
            simp [μ, Lfun, PMF.bind_apply]
    _ = ∑' ss, ∑' π, FL π ss := hswapL
    _ = ∑' ss, ∑' π, FR π ss := by
          apply tsum_congr
          intro ss
          exact hPerSs ss
    _ = (∑' π, μ π * ∑' ss, (D.runDistPure n π) ss * Gfun ss π) := hswapR.symm
    _ = ((mixedJoint (I := I) (behavioralToMixed (I := I) b)).bind (fun π =>
      (D.runDistPure n π).bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) ss)
          (fun t => ss ++ [t])))) y := by
            simp [μ, Gfun, PMF.bind_apply]

/-- Bridge reduction: if every mixed profile satisfies step-independence, then
run distributions factor through sampling a pure profile and executing it. -/
theorem run_factorization
    (D : Execution.Dynamics I)
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (Act i))]
    (hStepIndep : ∀ μ n, StepIndependence (I := I) D μ n)
    (μ : MixedProfile (I := I)) :
    ∀ n, D.runDist n (realizeBehavioralCanonical (I := I) μ) =
      (mixedJoint (I := I) μ).bind (fun π => D.runDistPure n π) := by
  intro n
  induction n with
  | zero =>
      simp [Execution.Dynamics.runDist, Execution.Dynamics.runDistPure]
  | succ n ih =>
      calc
        D.runDist (n + 1) (realizeBehavioralCanonical (I := I) μ)
            = (D.runDist n (realizeBehavioralCanonical (I := I) μ)).bind
                (fun ss =>
                  Math.ProbabilityMassFunction.pushforward
                    (D.stepDist (realizeBehavioralCanonical (I := I) μ) ss)
                    (fun t => ss ++ [t])) := by
              simp [Execution.Dynamics.runDist]
        _ = ((mixedJoint (I := I) μ).bind (fun π => D.runDistPure n π)).bind
              (fun ss =>
                Math.ProbabilityMassFunction.pushforward
                  (D.stepDist (realizeBehavioralCanonical (I := I) μ) ss)
                  (fun t => ss ++ [t])) := by
              rw [ih]
        _ = (mixedJoint (I := I) μ).bind (fun π =>
              (D.runDistPure n π).bind (fun ss =>
                Math.ProbabilityMassFunction.pushforward
                  (D.stepDist (realizeBehavioralCanonical (I := I) μ) ss)
                  (fun t => ss ++ [t]))) := by
              rw [PMF.bind_bind]
        _ = (mixedJoint (I := I) μ).bind (fun π =>
              (D.runDistPure n π).bind (fun ss =>
                Math.ProbabilityMassFunction.pushforward
                  (D.stepDist (pureToBehavioral I π) ss)
                  (fun t => ss ++ [t]))) := by
              simpa using hStepIndep μ n
        _ = (mixedJoint (I := I) μ).bind (fun π => D.runDistPure (n + 1) π) := by
              simp [Execution.Dynamics.runDist, Execution.Dynamics.runDistPure]

theorem reduce_atomicFactorization_bridge
    (D : Execution.Dynamics I)
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (Act i))]
    (hrepr :
      ∀ μ : MixedProfile (I := I),
        AtomicCoordinateFactorization (I := I) μ →
        ∃ b : BehavioralProfile I, μ = behavioralToMixed (I := I) b)
    (hstepBehavioral :
      ∀ (b : BehavioralProfile I) (n : Nat),
        StepIndependence (I := I) D (behavioralToMixed (I := I) b) n) :
    ∀ (μ : MixedProfile (I := I)) (n : Nat),
      AtomicCoordinateFactorization (I := I) μ →
      StepIndependence (I := I) D μ n := by
  intro μ n hAtomic
  rcases hrepr μ hAtomic with ⟨b, hμ⟩
  exact stepIndependence_of_eq_behavioralMixed (I := I) (D := D) μ b hμ n (hstepBehavioral b n)

/-- Standalone bridge statement: atomic coordinate factorization implies one-step
independence. -/
theorem atomicFactorization_implies_stepIndependence
    (D : Execution.Dynamics I)
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (Act i))]
    (μ : MixedProfile (I := I)) (n : Nat) :
    AtomicCoordinateFactorization (I := I) μ →
    StepIndependence (I := I) D μ n := by
  intro hAtomic
  refine
    (reduce_atomicFactorization_bridge (I := I) (D := D)
      (hrepr := ?_)
      (hstepBehavioral := ?_)
      μ n hAtomic)
  · intro μ' hAtomic'
    classical
    rcases hAtomic' with ⟨τ, hτ⟩
    let b : BehavioralProfile I := fun i v => τ ⟨i, v⟩
    have hb :
        mixedJoint (I := I) (behavioralToMixed (I := I) b) =
          PMF.map (I.reassemblePolicy) (pmfPi τ) := by
      simpa [b] using
        (mixedJoint_behavioralToMixed_eq_map_reassemble (I := I) b)
    have hJoint :
        mixedJoint (I := I) μ' =
          mixedJoint (I := I) (behavioralToMixed (I := I) b) := by
      calc
        mixedJoint (I := I) μ' = PMF.map (I.reassemblePolicy) (pmfPi τ) := hτ
        _ = mixedJoint (I := I) (behavioralToMixed (I := I) b) := hb.symm
    refine ⟨b, ?_⟩
    exact mixedJoint_injective (I := I) hJoint
  · intro b n'
    classical
    simpa [StepIndependence, realize_behavioralToMixed (I := I) b] using
      (behavioralToMixed_stepIndependence_bridge (I := I) (D := D) b n')

end InfoModel
end GameTheory
