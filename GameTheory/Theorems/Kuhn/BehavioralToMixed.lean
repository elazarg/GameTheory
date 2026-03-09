import GameTheory.Theorems.Kuhn.CorrelatedRealization
import Math.PMFProduct

/-! # Behavioral → Mixed direction of Kuhn's theorem for ObsModel

Every behavioral profile `β` has the same bounded trace distribution as the
product mixed strategy `ν = pmfPi (fun i => pmfPi (β i))`. No recall conditions
are needed for this direction.

## Main result

`kuhn_behavioral_to_mixed`: for all `β` and `k`,
  `O.runDist k β = ν.bind (fun π => O.runDistPure k π)`

## Assumptions

The theorem assumes `Fintype (O.LocalTrace i)` for each player `i`. Since
`O.LocalTrace i = List (Obs i)`, this is satisfiable only for bounded-horizon
games or restricted trace types. This is the same finiteness assumption used
in the InfoModel B→M proof.
-/

set_option autoImplicit false

namespace ObsModel

open Math.ProbabilityMassFunction Math.ParameterizedChain

variable {ι σ : Type} {Obs : ι → Type} {Act : (i : ι) → Obs i → Type}
variable {O : ObsModel ι σ Obs Act}

/-! ### Definitions -/

section Definitions

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.LocalTrace i)]

open Classical in
/-- Convert a behavioral profile to per-player mixed strategies by taking
the independent product over local traces for each player. -/
noncomputable def behavioralToMixed
    (β : BehavioralProfile O) : ∀ i, PMF (O.LocalStrategy i) :=
  fun i => Math.PMFProduct.pmfPi (β i)

open Classical in
/-- The full product mixed strategy: first product over traces per player,
then product over players. -/
noncomputable def behavioralToMixedJoint
    [∀ i, Fintype (O.LocalStrategy i)]
    (β : BehavioralProfile O) : PMF (PureProfile O) :=
  Math.PMFProduct.pmfPi (O.behavioralToMixed β)

end Definitions

/-! ### Step decomposition for pure profiles -/

section StepLemmas

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

open Classical in
/-- Under a pure behavioral profile, `jointActionDist` is a point mass. -/
theorem jointActionDist_pureToBehavioral (O : ObsModel ι σ Obs Act)
    (π : PureProfile O) (ss : List σ) :
    O.jointActionDist (O.pureToBehavioral π) ss =
      PMF.pure (fun i => π i (O.projectStates i ss)) := by
  unfold jointActionDist pureToBehavioral
  exact Math.PMFProduct.pmfPi_pure (fun i => π i (O.projectStates i ss))

/-- Under a pure behavioral profile, `stepDist` is a deterministic step. -/
theorem stepDist_pureToBehavioral (O : ObsModel ι σ Obs Act)
    (π : PureProfile O) (ss : List σ) :
    O.stepDist (O.pureToBehavioral π) ss =
      O.step (O.lastState ss)
        (O.castJointAction ss (fun i => π i (O.projectStates i ss))) := by
  unfold stepDist
  rw [jointActionDist_pureToBehavioral, PMF.pure_bind]

/-- The step distribution depends only on the profile's values at
the current observation trace. -/
theorem stepDist_pureToBehavioral_congr (O : ObsModel ι σ Obs Act)
    {π₁ π₂ : PureProfile O} (ss : List σ)
    (h : ∀ i, π₁ i (O.projectStates i ss) = π₂ i (O.projectStates i ss)) :
    O.stepDist (O.pureToBehavioral π₁) ss =
      O.stepDist (O.pureToBehavioral π₂) ss := by
  simp only [stepDist_pureToBehavioral]
  congr 1
  funext i
  simp only [castJointAction, h i]

end StepLemmas

/-! ### Run distribution depends only on short traces -/

section RunLemmas

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] in
/-- `projectStates i ss` has the same length as `ss`. -/
theorem projectStates_length (O : ObsModel ι σ Obs Act) (i : ι) (ss : List σ) :
    (O.projectStates i ss).length = ss.length := by
  simp [projectStates]

/-- Traces in the support of `runDistPure n` have length `n + 1`. -/
theorem runDistPure_support_length (O : ObsModel ι σ Obs Act)
    (n : Nat) (π : PureProfile O) (ss : List σ)
    (h : O.runDistPure n π ss ≠ 0) : ss.length = n + 1 := by
  rw [runDistPure_eq_pureRun] at h
  exact pureRun_length O.pureStep O.init n π ss h

/-- The bounded run distribution `runDistPure n π` depends only on
the values of `π` at observation traces of length `≤ n`. -/
theorem runDistPure_congr_of_agree_le (O : ObsModel ι σ Obs Act)
    {π₁ π₂ : PureProfile O} (n : Nat)
    (h : ∀ i (v : O.LocalTrace i), v.length ≤ n → π₁ i v = π₂ i v) :
    O.runDistPure n π₁ = O.runDistPure n π₂ := by
  induction n with
  | zero => simp [runDistPure, runDist]
  | succ n ih =>
    have hle : ∀ i (v : O.LocalTrace i), v.length ≤ n → π₁ i v = π₂ i v :=
      fun i v hv => h i v (Nat.le_succ_of_le hv)
    have hIH := ih hle
    ext ss
    simp only [runDistPure, runDist]
    -- Both sides: (runDist n ...).bind (fun ss' => pushforward (stepDist ... ss') (...))
    -- Use IH for the prefix run, and h for the step
    change (O.runDist n (O.pureToBehavioral π₁)).bind _ ss =
      (O.runDist n (O.pureToBehavioral π₂)).bind _ ss
    rw [show O.runDist n (O.pureToBehavioral π₁) = O.runDist n (O.pureToBehavioral π₂) from hIH]
    -- Both sides share the same prefix run; show step distributions agree on support
    simp only [PMF.bind_apply]
    congr 1; funext ss'
    by_cases hne : (O.runDist n (O.pureToBehavioral π₂)) ss' = 0
    · simp [hne]
    · have hlen : ss'.length = n + 1 := by
        apply runDistPure_support_length O n π₂
        simp only [runDistPure, runDist] at hne ⊢; exact hne
      have hstep : O.stepDist (O.pureToBehavioral π₁) ss' =
          O.stepDist (O.pureToBehavioral π₂) ss' :=
        stepDist_pureToBehavioral_congr O ss' (fun i => h i _ (by
          rw [projectStates_length]; omega))
      rw [hstep]

end RunLemmas

/-! ### Marginal step equality -/

section MarginalStep

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.LocalTrace i)]

open Classical in
/-- The marginal of the pure step over the product measure equals the
behavioral step: sampling `π ~ ν` and stepping with `pureToBehavioral π`
is the same as stepping with `β` directly. -/
theorem marginal_stepDist
    [∀ i, Fintype (O.LocalStrategy i)]
    (β : BehavioralProfile O) (ss : List σ) :
    (O.behavioralToMixedJoint β).bind
      (fun π => O.stepDist (O.pureToBehavioral π) ss) =
      O.stepDist β ss := by
  -- Unfold stepDist to (jointActionDist ...).bind (step ...) on both sides
  simp only [stepDist]
  -- Simplify LHS inner jointActionDist using pure profile structure
  simp only [jointActionDist_pureToBehavioral, PMF.pure_bind]
  -- Goal: ν.bind (fun π => step s (cast ss (fun i => π i (proj i ss)))) =
  --       (jointActionDist β ss).bind (fun a => step s (cast ss a))
  -- Key: pushforward of ν along eval = jointActionDist β ss
  -- Use sufficiency: if the pushforward matches, the composed binds match
  suffices hpush : (O.behavioralToMixedJoint β).bind
      (fun π => PMF.pure (fun i => π i (O.projectStates i ss))) =
      O.jointActionDist β ss by
    -- RHS = (ν.bind (pure ∘ eval)).bind g, by hpush
    rw [← hpush, PMF.bind_bind]
    -- Now: ν.bind (fun π => (pure (eval π)).bind g) = ν.bind (fun π => g (eval π))
    simp only [PMF.pure_bind]
  -- Prove the pushforward equality: ν.bind (pure ∘ eval) = jointActionDist β ss
  unfold behavioralToMixedJoint behavioralToMixed jointActionDist
  -- Goal: (pmfPi (fun i => pmfPi (β i))).bind (fun π => pure (fun i => π i (proj i ss)))
  --     = pmfPi (fun i => β i (proj i ss))
  -- This is: pushforward (pmfPi μ) eval = pmfPi (fun i => pushforward (μ i) (eval_i))
  -- Prove via ext at the tsum level
  ext a
  simp only [PMF.bind_apply, PMF.pure_apply]
  -- Don't unfold pmfPi — keep it abstract for the fiber argument
  rw [tsum_fintype]
  -- LHS: ∑ π, pmfPi (fun i => pmfPi (β i)) π * if a = eval π then 1 else 0
  -- Factor the product indicator
  simp_rw [mul_ite, mul_one, mul_zero, @eq_comm _ a]
  -- LHS: ∑ x, if eval x = a then pmfPi(fun i => pmfPi (β i)) x else 0
  -- RHS: pmfPi(fun i => β i (proj i ss)) a
  -- Factor: pmfPi = ∏, indicator = ∏, combine and use prod_sum
  -- Use Finset.sum_congr to unfold the outer pmfPi and factor indicators
  have hfactor : ∀ π : PureProfile O,
      (if (fun i => π i (O.projectStates i ss)) = a
        then (Math.PMFProduct.pmfPi (fun i => Math.PMFProduct.pmfPi (β i))) π else 0) =
      ∏ i, (if π i (O.projectStates i ss) = a i
        then (Math.PMFProduct.pmfPi (β i)) (π i) else 0) := by
    intro π
    by_cases h : (fun i => π i (O.projectStates i ss)) = a
    · rw [if_pos h, Math.PMFProduct.pmfPi_apply]
      apply Finset.prod_congr rfl; intro i _
      rw [if_pos (congr_fun h i)]
    · rw [if_neg h]
      have ⟨i, hi⟩ : ∃ i, π i (O.projectStates i ss) ≠ a i := by
        by_contra hall; push_neg at hall; exact h (funext hall)
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])).symm
  simp_rw [hfactor]
  -- ∑ x, ∏ i, f i (x i) = ∏ i, ∑ πi, f i πi
  rw [show (∑ x : PureProfile O, ∏ i, if x i (O.projectStates i ss) = a i
        then (Math.PMFProduct.pmfPi (β i)) (x i) else 0) =
      (∏ i, ∑ πi : O.LocalStrategy i, if πi (O.projectStates i ss) = a i
        then (Math.PMFProduct.pmfPi (β i)) πi else 0) from
    (@Fintype.prod_sum ι ENNReal _ _ _ (fun i => O.LocalStrategy i) _
      (fun i πi => if πi (O.projectStates i ss) = a i
        then (Math.PMFProduct.pmfPi (β i)) πi else 0)).symm]
  rw [Math.PMFProduct.pmfPi_apply]
  congr 1; funext i
  convert Math.PMFProduct.pmfPi_coord_mass (β i) (O.projectStates i ss) (a i)

end MarginalStep

/-! ### Scalar independence via swap involution -/

section ScalarIndependence

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.LocalTrace i)]

open Classical in
/-- Swap operation: for `v.length ≤ n` take from `π₁`, otherwise from `π₂`. -/
noncomputable def swapProfile
    (n : Nat) (π₁ π₂ : PureProfile O) : PureProfile O :=
  fun i v => if v.length ≤ n then π₁ i v else π₂ i v

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
  [∀ i, Fintype (O.LocalTrace i)] in
open Classical in
/-- The swap is an involution when paired with its reverse. -/
theorem swapProfile_involutive (n : Nat) :
    Function.Involutive (fun (p : PureProfile O × PureProfile O) =>
      (swapProfile n p.1 p.2, swapProfile n p.2 p.1)) := by
  intro ⟨π₁, π₂⟩
  apply Prod.ext <;> (funext i v; simp [swapProfile]; split <;> rfl)

set_option linter.unusedFintypeInType false in
open Classical in
/-- The product measure weight is preserved under the swap. -/
theorem swap_weight_eq
    [∀ i, Fintype (O.LocalStrategy i)]
    [Fintype (PureProfile O)]
    (β : BehavioralProfile O) (n : Nat) (π₁ π₂ : PureProfile O) :
    (O.behavioralToMixedJoint β) (swapProfile n π₁ π₂) *
    (O.behavioralToMixedJoint β) (swapProfile n π₂ π₁) =
    (O.behavioralToMixedJoint β) π₁ *
    (O.behavioralToMixedJoint β) π₂ := by
  simp only [behavioralToMixedJoint, behavioralToMixed,
    Math.PMFProduct.pmfPi_apply]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1; funext i
  simp only [swapProfile]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1; funext v
  by_cases hv : v.length ≤ n <;> simp [hv, mul_comm]

open Classical in
/-- **Scalar independence under the product measure.**
If `f` depends only on coordinates with trace length `≤ n` and `g` depends
only on coordinates with trace length `> n`, then `E[f·g] = E[f]·E[g]`. -/
theorem scalar_indep
    [∀ i, Fintype (O.LocalStrategy i)]
    [Fintype (PureProfile O)]
    (β : BehavioralProfile O) (n : Nat)
    (f g : PureProfile O → ENNReal)
    (hf : ∀ π₁ π₂ : PureProfile O,
      (∀ i (v : O.LocalTrace i), v.length ≤ n → π₁ i v = π₂ i v) → f π₁ = f π₂)
    (hg : ∀ π₁ π₂ : PureProfile O,
      (∀ i (v : O.LocalTrace i), v.length > n → π₁ i v = π₂ i v) → g π₁ = g π₂) :
    ∑ π, (O.behavioralToMixedJoint β) π * (f π * g π) =
    (∑ π, (O.behavioralToMixedJoint β) π * f π) *
    (∑ π, (O.behavioralToMixedJoint β) π * g π) := by
  set ν := O.behavioralToMixedJoint β
  have hf_swap : ∀ π₁ π₂, f (swapProfile n π₁ π₂) = f π₁ := by
    intro π₁ π₂; apply hf; intro i v hv; simp [swapProfile, hv]
  have hg_swap : ∀ π₁ π₂, g (swapProfile n π₁ π₂) = g π₂ := by
    intro π₁ π₂; apply hg; intro i v hv
    simp only [swapProfile, show ¬(v.length ≤ n) from Nat.not_le.mpr hv, ite_false]
  let P := fun π => ν π
  let Fsame : PureProfile O × PureProfile O → ENNReal :=
    fun p => P p.1 * P p.2 * (f p.1 * g p.1)
  let Fcross : PureProfile O × PureProfile O → ENNReal :=
    fun p => P p.1 * P p.2 * (f p.1 * g p.2)
  let e : PureProfile O × PureProfile O → PureProfile O × PureProfile O :=
    fun p => (swapProfile n p.1 p.2, swapProfile n p.2 p.1)
  have he : Function.Involutive e := swapProfile_involutive n
  have hpoint : ∀ p, Fcross p = Fsame (e p) := by
    intro ⟨π₁, π₂⟩
    simp only [Fcross, Fsame, e, P]
    rw [swap_weight_eq β n π₁ π₂, hf_swap π₁ π₂, hg_swap π₁ π₂]
  -- ∑ π, ν π * (f π * g π) = ∑ π₁ π₂, ν π₁ * ν π₂ * (f π₁ * g π₁) / (∑ π₂, ν π₂)
  -- Swap involution: ∑ (π₁,π₂) Fsame = ∑ (π₁,π₂) Fcross
  -- Fcross factors: (∑ π₁, ν π₁ * f π₁) * (∑ π₂, ν π₂ * g π₂)
  have hFsame_eq_Fcross : ∑ p : PureProfile O × PureProfile O, Fsame p =
      ∑ p : PureProfile O × PureProfile O, Fcross p := by
    calc ∑ p, Fsame p
        = ∑ p, Fsame (e p) :=
          (Math.PMFProduct.sum_univ_eq_sum_univ_of_involutive e he Fsame).symm
      _ = ∑ p, Fcross p := by
          congr 1; funext p; exact (hpoint p).symm
  have hFsame_expand : ∑ p : PureProfile O × PureProfile O, Fsame p =
      (∑ π, ν π * (f π * g π)) * (∑ π₂, ν π₂) := by
    have h1 : ∀ (a b : PureProfile O),
        Fsame (a, b) = (ν a * (f a * g a)) * ν b := fun a b => by
      simp [Fsame, P]; ring
    simp_rw [Fintype.sum_prod_type, h1, ← Finset.mul_sum, ← Finset.sum_mul]
  have hFcross_expand : ∑ p : PureProfile O × PureProfile O, Fcross p =
      (∑ π, ν π * f π) * (∑ π, ν π * g π) := by
    have h1 : ∀ (a b : PureProfile O),
        Fcross (a, b) = (ν a * f a) * (ν b * g b) := fun a b => by
      simp [Fcross, P]; ring
    simp_rw [Fintype.sum_prod_type, h1, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
  have hsum_one : (∑ π : PureProfile O, ν π) = 1 := by
    have := PMF.tsum_coe ν
    rwa [tsum_fintype] at this
  calc ∑ π, ν π * (f π * g π)
      = (∑ π, ν π * (f π * g π)) * 1 := by ring
    _ = (∑ π, ν π * (f π * g π)) * (∑ π₂, ν π₂) := by rw [hsum_one]
    _ = ∑ p : PureProfile O × PureProfile O, Fsame p := hFsame_expand.symm
    _ = ∑ p : PureProfile O × PureProfile O, Fcross p := hFsame_eq_Fcross
    _ = (∑ π, ν π * f π) * (∑ π, ν π * g π) := hFcross_expand

end ScalarIndependence

/-! ### Step independence bridge -/

section StepIndependenceBridge

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.LocalTrace i)]

open Classical in
set_option linter.unusedFintypeInType false in
/-- The step independence condition holds for the product measure
`ν = behavioralToMixedJoint β`. -/
theorem stepIndependence_bridge
    [∀ i, Fintype (O.LocalStrategy i)]
    [Fintype (PureProfile O)]
    (β : BehavioralProfile O) (n : Nat) :
    (O.behavioralToMixedJoint β).bind (fun π =>
      (O.runDistPure n π).bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward (O.stepDist β ss)
          (fun t => ss ++ [t]))) =
    (O.behavioralToMixedJoint β).bind (fun π =>
      (O.runDistPure n π).bind (fun ss =>
        Math.ProbabilityMassFunction.pushforward
          (O.stepDist (O.pureToBehavioral π) ss)
          (fun t => ss ++ [t]))) := by
  set ν := O.behavioralToMixedJoint β
  have hstepMarg : ∀ ss : List σ,
      ν.bind (fun π => O.stepDist (O.pureToBehavioral π) ss) = O.stepDist β ss :=
    marginal_stepDist β
  ext y
  let Lfun : List σ → ENNReal :=
    fun ss => (Math.ProbabilityMassFunction.pushforward
      (O.stepDist β ss) (fun t => ss ++ [t])) y
  let Gfun : List σ → PureProfile O → ENNReal :=
    fun ss π => (Math.ProbabilityMassFunction.pushforward
      (O.stepDist (O.pureToBehavioral π) ss) (fun t => ss ++ [t])) y
  -- Both sides expand as tsum over π, ss
  simp only [PMF.bind_apply]
  -- Swap tsum order
  have hswapL :
      (∑' π, ν π * ∑' ss, (O.runDistPure n π) ss * Lfun ss) =
        ∑' ss, ∑' π, ν π * ((O.runDistPure n π) ss * Lfun ss) := by
    simp_rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_comm (f := fun π ss => ν π * ((O.runDistPure n π) ss * Lfun ss))
  have hswapR :
      (∑' π, ν π * ∑' ss, (O.runDistPure n π) ss * Gfun ss π) =
        ∑' ss, ∑' π, ν π * ((O.runDistPure n π) ss * Gfun ss π) := by
    simp_rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_comm (f := fun π ss => ν π * ((O.runDistPure n π) ss * Gfun ss π))
  rw [hswapL, hswapR]
  -- Per-ss: use scalar independence when ss.length = n+1, else both are 0
  congr 1; funext ss
  by_cases hlen : ss.length = n + 1
  · -- The interesting case: scalar independence
    let f : PureProfile O → ENNReal := fun π => (O.runDistPure n π) ss
    let g : PureProfile O → ENNReal := fun π => Gfun ss π
    -- f depends on traces of length ≤ n
    have hf : ∀ π₁ π₂ : PureProfile O,
        (∀ i (v : O.LocalTrace i), v.length ≤ n → π₁ i v = π₂ i v) → f π₁ = f π₂ := by
      intro π₁ π₂ hag
      exact congrArg (· ss) (runDistPure_congr_of_agree_le O n hag)
    -- g depends on traces of length = ss.length = n+1 > n
    have hg : ∀ π₁ π₂ : PureProfile O,
        (∀ i (v : O.LocalTrace i), v.length > n → π₁ i v = π₂ i v) → g π₁ = g π₂ := by
      intro π₁ π₂ hag
      change Gfun ss π₁ = Gfun ss π₂
      simp only [Gfun]
      rw [stepDist_pureToBehavioral_congr O ss (fun i => hag i _ (by
        rw [projectStates_length]; omega))]
    have hind :
        ∑ π, ν π * (f π * g π) =
          (∑ π, ν π * f π) * (∑ π, ν π * g π) :=
      scalar_indep β n f g hf hg
    -- E[g] = Lfun ss (marginal step equality)
    have hEg : (∑ π, ν π * g π) = Lfun ss := by
      have : ν.bind (fun π => O.stepDist (O.pureToBehavioral π) ss) = O.stepDist β ss :=
        hstepMarg ss
      have hbindPush :
          (ν.bind (fun π =>
            Math.ProbabilityMassFunction.pushforward
              (O.stepDist (O.pureToBehavioral π) ss)
              (fun t => ss ++ [t]))) y = Lfun ss := by
        simp only [Lfun]
        congr 1
        rw [show ν.bind (fun π =>
            Math.ProbabilityMassFunction.pushforward
              (O.stepDist (O.pureToBehavioral π) ss) (fun t => ss ++ [t]))
          = Math.ProbabilityMassFunction.pushforward
            (ν.bind (fun π => O.stepDist (O.pureToBehavioral π) ss))
            (fun t => ss ++ [t]) from by
              simp [Math.ProbabilityMassFunction.pushforward, PMF.bind_bind]]
        rw [hstepMarg ss]
      simp only [PMF.bind_apply] at hbindPush
      simp only [g, Gfun]
      convert hbindPush using 1
      simp_rw [tsum_fintype]
    -- LHS: ∑ π, ν π * (f π * Lfun ss) = (∑ π, ν π * f π) * Lfun ss
    -- RHS: ∑ π, ν π * (f π * g π)
    calc (∑' π, ν π * ((O.runDistPure n π) ss * Lfun ss))
        = ∑ π, ν π * (f π * Lfun ss) := by simp [f, tsum_fintype]
      _ = (∑ π, ν π * f π) * Lfun ss := by
          simp_rw [← mul_assoc]
          exact (Finset.sum_mul ..).symm
      _ = (∑ π, ν π * f π) * (∑ π, ν π * g π) := by rw [hEg]
      _ = ∑ π, ν π * (f π * g π) := hind.symm
      _ = ∑' π, ν π * ((O.runDistPure n π) ss * Gfun ss π) := by
          simp [f, g, tsum_fintype]
  · -- Traces with wrong length get 0 from runDistPure
    have hzero : ∀ π : PureProfile O, (O.runDistPure n π) ss = 0 := by
      intro π
      by_contra hne
      exact hlen (runDistPure_support_length O n π ss hne)
    simp [hzero]

end StepIndependenceBridge

/-! ### Main theorem -/

section MainTheorem

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.LocalTrace i)]

set_option linter.unusedFintypeInType false in
open Classical in
/-- **Kuhn's theorem, B→M direction for ObsModel.**
Every behavioral profile has the same bounded trace distribution as the
product mixed strategy. No recall conditions are needed. -/
theorem kuhn_behavioral_to_mixed
    [∀ i, Fintype (O.LocalStrategy i)]
    [Fintype (PureProfile O)]
    (β : BehavioralProfile O) (k : Nat) :
    O.runDist k β =
      (O.behavioralToMixedJoint β).bind (fun π => O.runDistPure k π) :=
  runDist_eq_of_stepIndependence
    (O.behavioralToMixedJoint β) β
    (fun n => stepIndependence_bridge β n) k

end MainTheorem

end ObsModel
