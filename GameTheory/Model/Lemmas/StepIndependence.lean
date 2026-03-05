import GameTheory.Model.Lemmas.Profiles
import GameTheory.Model.Lemmas.AtomicFactorization
import GameTheory.Model.Lemmas.ExecutionLocality

namespace GameTheory
namespace InfoModel

open Execution
open Math.PMFProduct

variable {ι : Type} [Fintype ι]
variable {M : LSM ι} (I : InfoModel M)

/-- **Scalar independence under the behavioral product measure.**
    `E[f·g] = E[f]·E[g]` when `f` depends only on coordinates with local-trace
    length `≤ n` and `g` depends only on coordinates with length `> n`.
    Proved via involution/swap argument. -/
theorem behavioralToMixed_scalar_indep
    [DecidableEq ι]
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)]
    (σ : BehavioralProfile I) (n : Nat)
    (f g : PureProfile I → ENNReal)
    (hf : ∀ π π' : PureProfile I,
      (∀ i (v : I.LocalTrace i), v.length ≤ n → π i v = π' i v) → f π = f π')
    (hg : ∀ π π' : PureProfile I,
      (∀ i (v : I.LocalTrace i), v.length > n → π i v = π' i v) → g π = g π') :
    ∑ π, (mixedJoint I (behavioralToMixed I σ)) π * (f π * g π) =
    (∑ π, (mixedJoint I (behavioralToMixed I σ)) π * f π) *
    (∑ π, (mixedJoint I (behavioralToMixed I σ)) π * g π) := by
  classical
  set μ := mixedJoint I (behavioralToMixed I σ)
  have hμ_prod : ∀ π, μ π = ∏ i, ∏ p : I.LocalTrace i, (σ i p) (π i p) := by
    intro π
    simpa [μ, mixedJoint, behavioralToMixed_apply_prod]
  let swap : PureProfile I → PureProfile I → PureProfile I :=
    fun π₁ π₂ i v => if v.length ≤ n then π₁ i v else π₂ i v
  have hweight_i : ∀ (π₁ π₂ : PureProfile I) (i : ι),
      (behavioralToMixed I σ i) (swap π₁ π₂ i) *
      (behavioralToMixed I σ i) (swap π₂ π₁ i) =
      (behavioralToMixed I σ i) (π₁ i) *
      (behavioralToMixed I σ i) (π₂ i) := by
    intro π₁ π₂ i
    simp only [behavioralToMixed_apply_prod, swap]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1; funext v
    by_cases hv : v.length ≤ n <;> simp [hv, mul_comm]
  have hweight : ∀ (π₁ π₂ : PureProfile I),
      μ (swap π₁ π₂) * μ (swap π₂ π₁) = μ π₁ * μ π₂ := by
    intro π₁ π₂
    simp only [μ, mixedJoint, pmfPi_apply]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1; funext i; exact hweight_i π₁ π₂ i
  have hf_swap : ∀ π₁ π₂, f (swap π₁ π₂) = f π₁ := by
    intro π₁ π₂; apply hf; intro i v hv; simp [swap, hv]
  have hg_swap : ∀ π₁ π₂, g (swap π₁ π₂) = g π₂ := by
    intro π₁ π₂; apply hg; intro i v hv
    simp only [swap]; rw [if_neg (Nat.not_le.mpr hv)]
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
    simp only [P]; exact (tsum_fintype (fun π => μ π)).symm.trans μ.tsum_coe
  calc ∑ π, μ π * (f π * g π)
      = (∑ π, μ π * (f π * g π)) * 1 := (mul_one _).symm
    _ = (∑ π, μ π * (f π * g π)) * ∑ π₂, P π₂ := by rw [hsumP]
    _ = ∑ π₁, ∑ π₂, μ π₁ * (f π₁ * g π₁) * P π₂ := Finset.sum_mul_sum ..
    _ = ∑ p : _ × _, Fsame p := by
        rw [← Fintype.sum_prod_type']
        congr 1; ext ⟨π₁, π₂⟩; simp only [Fsame, P]; ring
    _ = ∑ p : _ × _, Fcross p := hpair.symm
    _ = ∑ π₁, ∑ π₂, μ π₁ * f π₁ * (μ π₂ * g π₂) := by
        rw [← Fintype.sum_prod_type']
        congr 1; ext ⟨π₁, π₂⟩; simp only [Fcross, P]; ring
    _ = (∑ π, μ π * f π) * ∑ π, μ π * g π := (Finset.sum_mul_sum ..).symm

/-- Step-independence equality used in the Kuhn run induction. -/
def StepIndependence
    (D : Execution.Dynamics I)
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : MixedProfile (I := I)) (n : Nat) : Prop :=
    (mixedJoint (I := I) μ).bind (fun π =>
      (D.runDistPure n π).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (realizeBehavioralCanonical (I := I) μ) hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) =
    (mixedJoint (I := I) μ).bind (fun π =>
      (D.runDistPure n π).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))))

/-- Transport helper: if a mixed profile is definitionally equal to a
behavioral-induced mixed profile, step-independence transports across the equality. -/
theorem stepIndependence_of_eq_behavioralMixed
    (D : Execution.Dynamics I)
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : MixedProfile (I := I))
    (σ : BehavioralProfile I)
    (hμ : μ = behavioralToMixed (I := I) σ)
    (n : Nat)
    (hStep : StepIndependence (I := I) D (behavioralToMixed (I := I) σ) n) :
    StepIndependence (I := I) D μ n := by
  simpa [hμ] using hStep

/-- Step 4 core proposition: scalar independence under the behavioral product law. -/
def step4_scalarIndependenceCore : Prop :=
  ∀ [DecidableEq ι] [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (Option (M.Act i))]
    [∀ i, Fintype (LocalPure (I := I) i)],
    ∀ (σ : BehavioralProfile I) (n : Nat)
      (f g : PureProfile I → ENNReal),
      (∀ π π' : PureProfile I,
        (∀ i (v : I.LocalTrace i), v.length ≤ n → π i v = π' i v) → f π = f π') →
      (∀ π π' : PureProfile I,
        (∀ i (v : I.LocalTrace i), v.length > n → π i v = π' i v) → g π = g π') →
      ∑ π, (mixedJoint I (behavioralToMixed I σ)) π * (f π * g π) =
      (∑ π, (mixedJoint I (behavioralToMixed I σ)) π * f π) *
      (∑ π, (mixedJoint I (behavioralToMixed I σ)) π * g π)

/-- Step 4 is proved: this is exactly `behavioralToMixed_scalar_indep`. -/
theorem step4_scalarIndependenceCore_proved : step4_scalarIndependenceCore (I := I) := by
  intro _ _ _ _ σ n f g hf hg
  exact behavioralToMixed_scalar_indep (I := I) σ n f g hf hg

/-- Remaining probabilistic bridge for behavioral-induced mixed profiles:
factor one-step extension through run-prefix sampling. -/
theorem behavioralToMixed_stepIndependence_bridge
    (D : Execution.Dynamics I)
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) (n : Nat) :
    (mixedJoint (I := I) (behavioralToMixed (I := I) σ)).bind (fun π =>
      (D.runDistPure n π).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist σ hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) =
    (mixedJoint (I := I) (behavioralToMixed (I := I) σ)).bind (fun π =>
      (D.runDistPure n π).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) := by
  classical
  set μ : PMF (PureProfile I) := mixedJoint (I := I) (behavioralToMixed (I := I) σ)
  have hstepMarg :
      ∀ ss : List M.State,
        μ.bind (fun π => D.stepDist (pureToBehavioral I π) ss) = D.stepDist σ ss := by
    intro ss
    simpa [μ] using (marginal_stepDist (I := I) (D := D) σ ss)
  have hRunCongr :
      ∀ hs : List M.Label × List M.State, ∀ π π' : PureProfile I,
        (∀ i (v : I.LocalTrace i), v.length ≤ n → π i v = π' i v) →
        (D.runDistPure n π) hs = (D.runDistPure n π') hs := by
    intro hs π π' hag
    let ω₁ : I.FlatPolicy := fun k => π k.1 k.2
    let ω₂ : I.FlatPolicy := fun k => π' k.1 k.2
    have hagFlat :
        ∀ i v, v.length ≤ n → ω₁ ⟨i, v⟩ = ω₂ ⟨i, v⟩ := by
      intro i v hv
      simpa [ω₁, ω₂] using hag i v hv
    have hEq :
        D.runDistPure n (I.reassemblePolicy ω₁) =
          D.runDistPure n (I.reassemblePolicy ω₂) :=
      runDistPure_depends_on_len_le (I := I) (D := D) n ω₁ ω₂ hagFlat
    simpa [ω₁, ω₂] using congrArg (fun ν => ν hs) hEq
  ext y
  let Lfun : (List M.Label × List M.State) → ENNReal :=
    fun hs =>
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist σ hs.2)
        (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y
  let Gfun : (List M.Label × List M.State) → PureProfile I → ENNReal :=
    fun hs π =>
      (Math.ProbabilityMassFunction.pushforward
        (D.stepDist (pureToBehavioral I π) hs.2)
        (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y
  let FL : PureProfile I → (List M.Label × List M.State) → ENNReal :=
    fun π hs => μ π * ((D.runDistPure n π) hs * Lfun hs)
  let FR : PureProfile I → (List M.Label × List M.State) → ENNReal :=
    fun π hs => μ π * ((D.runDistPure n π) hs * Gfun hs π)
  have hswapL :
      (∑' π, μ π * ∑' hs, (D.runDistPure n π) hs * Lfun hs)
        = ∑' hs, ∑' π, FL π hs := by
    calc
      (∑' π, μ π * ∑' hs, (D.runDistPure n π) hs * Lfun hs)
          = ∑' π, ∑' hs, μ π * ((D.runDistPure n π) hs * Lfun hs) := by
              refine tsum_congr ?_
              intro π
              rw [ENNReal.tsum_mul_left]
      _ = ∑' hs, ∑' π, μ π * ((D.runDistPure n π) hs * Lfun hs) := by
            simpa using
              (ENNReal.tsum_comm
                (f := fun π hs => μ π * ((D.runDistPure n π) hs * Lfun hs)))
      _ = ∑' hs, ∑' π, FL π hs := by simp [FL]
  have hswapR :
      (∑' π, μ π * ∑' hs, (D.runDistPure n π) hs * Gfun hs π)
        = ∑' hs, ∑' π, FR π hs := by
    calc
      (∑' π, μ π * ∑' hs, (D.runDistPure n π) hs * Gfun hs π)
          = ∑' π, ∑' hs, μ π * ((D.runDistPure n π) hs * Gfun hs π) := by
              refine tsum_congr ?_
              intro π
              rw [ENNReal.tsum_mul_left]
      _ = ∑' hs, ∑' π, μ π * ((D.runDistPure n π) hs * Gfun hs π) := by
            simpa using
              (ENNReal.tsum_comm
                (f := fun π hs => μ π * ((D.runDistPure n π) hs * Gfun hs π)))
      _ = ∑' hs, ∑' π, FR π hs := by simp [FR]
  have hPerHs :
      ∀ hs : List M.Label × List M.State, (∑' π, FL π hs) = ∑' π, FR π hs := by
    intro hs
    by_cases hlen : hs.2.length = n + 1
    · let f : PureProfile I → ENNReal := fun π => (D.runDistPure n π) hs
      let g : PureProfile I → ENNReal := fun π => Gfun hs π
      have hf :
          ∀ π π' : PureProfile I,
            (∀ i (v : I.LocalTrace i), v.length ≤ n → π i v = π' i v) →
            f π = f π' := by
        intro π π' hag
        exact hRunCongr hs π π' hag
      have hg :
          ∀ π π' : PureProfile I,
            (∀ i (v : I.LocalTrace i), v.length > n → π i v = π' i v) →
            g π = g π' := by
        intro π π' hag
        let ω₁ : I.FlatPolicy := fun k => π k.1 k.2
        let ω₂ : I.FlatPolicy := fun k => π' k.1 k.2
        have hagNow :
            ∀ i,
              ω₁ ⟨i, I.projectStates i hs.2⟩ =
                ω₂ ⟨i, I.projectStates i hs.2⟩ := by
          intro i
          have hvlen : (I.projectStates i hs.2).length > n := by
            simp [I.projectStates_length i hs.2, hlen]
          simpa [ω₁, ω₂] using hag i (I.projectStates i hs.2) hvlen
        have hstepEq :
            D.stepDist (pureToBehavioral I (I.reassemblePolicy ω₁)) hs.2 =
              D.stepDist (pureToBehavioral I (I.reassemblePolicy ω₂)) hs.2 :=
          stepDist_depends_on_current_context (I := I) (D := D) ω₁ ω₂ hs.2 hagNow
        have hpushEq := congrArg
          (fun ν =>
            (Math.ProbabilityMassFunction.pushforward ν
              (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y)
          hstepEq
        simpa [g, Gfun, ω₁, ω₂] using hpushEq
      have hind :
          ∑ π, μ π * (f π * g π) =
            (∑ π, μ π * f π) * (∑ π, μ π * g π) := by
        simpa [μ] using behavioralToMixed_scalar_indep (I := I) σ n f g hf hg
      have hEg :
          (∑ π, μ π * g π) = Lfun hs := by
        have hbindPush :
            (μ.bind (fun π =>
              Math.ProbabilityMassFunction.pushforward
                (D.stepDist (pureToBehavioral I π) hs.2)
                (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) y = Lfun hs := by
          calc
            (μ.bind (fun π =>
              Math.ProbabilityMassFunction.pushforward
                (D.stepDist (pureToBehavioral I π) hs.2)
                (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) y
                =
              (Math.ProbabilityMassFunction.pushforward
                (μ.bind (fun π => D.stepDist (pureToBehavioral I π) hs.2))
                (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y := by
                  simpa using congrArg (fun ν => ν y) (
                    (Math.ProbabilityMassFunction.pushforward_bind
                      (μ := μ)
                      (k := fun π => D.stepDist (pureToBehavioral I π) hs.2)
                      (f := fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))).symm
            _ = (Math.ProbabilityMassFunction.pushforward
                  (D.stepDist σ hs.2)
                  (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) y := by
                    simp [hstepMarg hs.2]
            _ = Lfun hs := rfl
        simpa [g, Gfun, PMF.bind_apply] using hbindPush
      calc
        (∑' π, FL π hs) = ∑ π, μ π * (f π * Lfun hs) := by
            simp [FL, f, tsum_fintype, mul_assoc, mul_comm]
        _ = (∑ π, μ π * f π) * Lfun hs := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (Finset.sum_mul (s := Finset.univ) (f := fun π => μ π * f π) (a := Lfun hs)).symm
        _ = (∑ π, μ π * f π) * (∑ π, μ π * g π) := by rw [hEg]
        _ = ∑ π, μ π * (f π * g π) := hind.symm
        _ = (∑' π, FR π hs) := by
            simp [FR, f, g, Gfun, tsum_fintype, mul_assoc, mul_comm]
    · have hfzero : ∀ π : PureProfile I, (D.runDistPure n π) hs = 0 := by
        intro π
        by_contra hne
        have hlen' :
            hs.2.length = n + 1 := by
          have hrun : (D.runDist n (pureToBehavioral I π)) hs ≠ 0 := by
            simpa [Execution.Dynamics.runDistPure] using hne
          exact runDist_support_stateLength (I := I) (D := D) n (pureToBehavioral I π) hs hrun
        exact hlen hlen'
      have hFL0 : (∑' π, FL π hs) = 0 := by
        exact (ENNReal.tsum_eq_zero).2 (by intro π; simp [FL, hfzero π])
      have hFR0 : (∑' π, FR π hs) = 0 := by
        exact (ENNReal.tsum_eq_zero).2 (by intro π; simp [FR, hfzero π])
      rw [hFL0, hFR0]
  calc
    ((mixedJoint (I := I) (behavioralToMixed (I := I) σ)).bind (fun π =>
      (D.runDistPure n π).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist σ hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))))) y
        = (∑' π, μ π * ∑' hs, (D.runDistPure n π) hs * Lfun hs) := by
            simp [μ, Lfun, PMF.bind_apply]
    _ = ∑' hs, ∑' π, FL π hs := hswapL
    _ = ∑' hs, ∑' π, FR π hs := by
          apply tsum_congr
          intro hs
          exact hPerHs hs
    _ = (∑' π, μ π * ∑' hs, (D.runDistPure n π) hs * Gfun hs π) := hswapR.symm
    _ = ((mixedJoint (I := I) (behavioralToMixed (I := I) σ)).bind (fun π =>
      (D.runDistPure n π).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward
          (D.stepDist (pureToBehavioral I π) hs.2)
          (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))))) y := by
            simp [μ, Gfun, PMF.bind_apply]

/-- Bridge reduction: to prove atomic-factorization implies step-independence,
it is enough to provide (1) behavioral representation from factorization and
(2) step-independence on behavioral-induced mixed profiles. -/
theorem run_factorization
    (D : Execution.Dynamics I)
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
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
                (fun hs =>
                  Math.ProbabilityMassFunction.pushforward
                    (D.stepDist (realizeBehavioralCanonical (I := I) μ) hs.2)
                    (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) := by
              simp [Execution.Dynamics.runDist]
        _ = ((mixedJoint (I := I) μ).bind (fun π => D.runDistPure n π)).bind
              (fun hs =>
                Math.ProbabilityMassFunction.pushforward
                  (D.stepDist (realizeBehavioralCanonical (I := I) μ) hs.2)
                  (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2]))) := by
              rw [ih]
        _ = (mixedJoint (I := I) μ).bind (fun π =>
              (D.runDistPure n π).bind (fun hs =>
                Math.ProbabilityMassFunction.pushforward
                  (D.stepDist (realizeBehavioralCanonical (I := I) μ) hs.2)
                  (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) := by
              rw [PMF.bind_bind]
        _ = (mixedJoint (I := I) μ).bind (fun π =>
              (D.runDistPure n π).bind (fun hs =>
                Math.ProbabilityMassFunction.pushforward
                  (D.stepDist (pureToBehavioral I π) hs.2)
                  (fun ls => (hs.1 ++ [ls.1], hs.2 ++ [ls.2])))) := by
              simpa using hStepIndep μ n
        _ = (mixedJoint (I := I) μ).bind (fun π => D.runDistPure (n + 1) π) := by
              simp [Execution.Dynamics.runDist, Execution.Dynamics.runDistPure]

theorem reduce_atomicFactorization_bridge
    (D : Execution.Dynamics I)
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (hrepr :
      ∀ μ : MixedProfile (I := I),
        AtomicCoordinateFactorization (I := I) μ →
        ∃ σ : BehavioralProfile I, μ = behavioralToMixed (I := I) σ)
    (hstepBehavioral :
      ∀ (σ : BehavioralProfile I) (n : Nat),
        StepIndependence (I := I) D (behavioralToMixed (I := I) σ) n) :
    ∀ (μ : MixedProfile (I := I)) (n : Nat),
      AtomicCoordinateFactorization (I := I) μ →
      StepIndependence (I := I) D μ n := by
  intro μ n hAtomic
  rcases hrepr μ hAtomic with ⟨σ, hμ⟩
  exact stepIndependence_of_eq_behavioralMixed (I := I) (D := D) μ σ hμ n (hstepBehavioral σ n)

/-- Standalone hard bridge statement:
atomic coordinate factorization should imply one-step independence. -/
theorem atomicFactorization_implies_stepIndependence
    (D : Execution.Dynamics I)
    [∀ i, Fintype (I.LocalTrace i)]
    [∀ i, Fintype (LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : MixedProfile (I := I)) (n : Nat) :
    AtomicCoordinateFactorization (I := I) μ →
    StepIndependence (I := I) D μ n := by
  intro hAtomic
  -- Reduce to two explicit bridge obligations:
  -- 1) representation of an atomic-factorized mixed profile by a behavioral profile
  -- 2) step-independence for behavioral-induced mixed profiles.
  refine
    (reduce_atomicFactorization_bridge (I := I) (D := D)
      (hrepr := ?_)
      (hstepBehavioral := ?_)
      μ n hAtomic)
  · intro μ' hAtomic'
    classical
    rcases hAtomic' with ⟨τ, hτ⟩
    let σ : BehavioralProfile I := fun i v => τ ⟨i, v⟩
    have hσ :
        mixedJoint (I := I) (behavioralToMixed (I := I) σ) =
          PMF.map (I.reassemblePolicy) (pmfPi τ) := by
      simpa [σ] using
        (mixedJoint_behavioralToMixed_eq_map_reassemble (I := I) σ)
    have hJoint :
        mixedJoint (I := I) μ' =
          mixedJoint (I := I) (behavioralToMixed (I := I) σ) := by
      calc
        mixedJoint (I := I) μ' = PMF.map (I.reassemblePolicy) (pmfPi τ) := hτ
        _ = mixedJoint (I := I) (behavioralToMixed (I := I) σ) := hσ.symm
    refine ⟨σ, ?_⟩
    exact mixedJoint_injective (I := I) hJoint
  · intro σ n'
    classical
    -- Normalize the left branch by eliminating canonical realization.
    -- Remaining gap is the probabilistic bridge between
    -- prefix-sampled pure execution and direct behavioral one-step extension.
    simpa [StepIndependence, realize_behavioralToMixed (I := I) σ] using
      (behavioralToMixed_stepIndependence_bridge (I := I) (D := D) σ n')

end InfoModel
end GameTheory
