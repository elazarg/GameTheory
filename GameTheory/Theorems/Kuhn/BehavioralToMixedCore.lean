import GameTheory.Theorems.Kuhn.KuhnModel
import Math.PMFProduct

/-! # Behavioral -> Mixed direction of Kuhn's theorem for `KuhnModel`

This is the semantic-core version of Kuhn's B->M direction, proved on
`KuhnModel` (currently named `ObsModelCore` in the code). Unlike the older
snapshot-refined `ObsModel` proof, it does not assume a faithful observation
history. The only additional hypothesis beyond finite information states is
`HorizonSeparation`: if the same information state occurs at two different
horizons, then its action space is trivial. This is exactly what is needed to
justify sampling all nontrivial contingent choices ex ante.
-/

set_option autoImplicit false

namespace ObsModelCore

open Math.ProbabilityMassFunction Math.ParameterizedChain Math.PMFProduct

variable {ι σ : Type} {Obs : ι → Type} {Act : (i : ι) → Obs i → Type}
variable {O : ObsModelCore ι σ Obs Act}

section Definitions

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.InfoState i)]

open Classical in
/-- Convert a behavioral profile to per-player mixed strategies by taking the
independent product over information states for each player. -/
noncomputable def behavioralToMixed
    (β : BehavioralProfile O) : ∀ i, PMF (O.LocalStrategy i) :=
  fun i => Math.PMFProduct.pmfPi (β i)

open Classical in
/-- The full product mixed strategy: first over information states per player,
then over players. -/
noncomputable def behavioralToMixedJoint
    [∀ i, Fintype (O.LocalStrategy i)]
    (β : BehavioralProfile O) : PMF (PureProfile O) :=
  Math.PMFProduct.pmfPi (O.behavioralToMixed β)

/-- Information state `v` is strategically relevant by horizon `n` if it occurs
as `projectStates i ss` for some trace of length at most `n`.  `runDistPure n`
can only depend on such states. -/
def ReachableInfoStateWithin (O : ObsModelCore ι σ Obs Act)
    (i : ι) (n : Nat) (v : O.InfoState i) : Prop :=
  ∃ ss : List σ, ss.length ≤ n ∧ O.projectStates i ss = v

/-- If the same information state is seen at two different horizons, then its
action space must be trivial.  This is the minimal extra condition needed for
the B->M proof on `ObsModelCore`. -/
def HorizonSeparation (O : ObsModelCore ι σ Obs Act) : Prop :=
  ∀ (i : ι) {ss ss' : List σ},
    O.projectStates i ss = O.projectStates i ss' →
    ss.length < ss'.length →
    Subsingleton (Act i (O.currentObs i (O.projectStates i ss')))

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] [∀ i, Fintype (O.InfoState i)] in
theorem reachableInfoStateWithin_mono
    (i : ι) {n m : Nat} {v : O.InfoState i}
    (h : O.ReachableInfoStateWithin i n v) (hnm : n ≤ m) :
    O.ReachableInfoStateWithin i m v := by
  rcases h with ⟨ss, hss, rfl⟩
  exact ⟨ss, le_trans hss hnm, rfl⟩

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] [∀ i, Fintype (O.InfoState i)] in
theorem reachableInfoStateWithin_projectStates
    (i : ι) {ss : List σ} {n : Nat} (hss : ss.length ≤ n) :
    O.ReachableInfoStateWithin i n (O.projectStates i ss) :=
  ⟨ss, hss, rfl⟩

end Definitions

section StepLemmas

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

open Classical in
/-- Under a pure behavioral profile, `jointActionDist` is a point mass. -/
theorem jointActionDist_pureToBehavioral
    (π : PureProfile O) (ss : List σ) :
    O.jointActionDist (O.pureToBehavioral π) ss =
      PMF.pure (fun i => π i (O.projectStates i ss)) := by
  ext a
  by_cases h : a = fun i => π i (O.projectStates i ss)
  · subst h
    simp [ObsModelCore.jointActionDist, ObsModelCore.pureToBehavioral, Math.PMFProduct.pmfPi_apply]
  · have ⟨i, hi⟩ : ∃ i, a i ≠ π i (O.projectStates i ss) := by
      by_contra hall
      push_neg at hall
      exact h (funext hall)
    have hprod :
        (∏ x, if a x = π x (O.projectStates x ss) then (1 : ENNReal) else 0) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    simpa only [ObsModelCore.jointActionDist, ObsModelCore.pureToBehavioral,
      Math.PMFProduct.pmfPi_apply, PMF.pure_apply, h] using hprod

/-- Under a pure behavioral profile, `stepDist` is a deterministic step. -/
theorem stepDist_pureToBehavioral
    (π : PureProfile O) (ss : List σ) :
    O.stepDist (O.pureToBehavioral π) ss =
      O.step (O.lastState ss)
        (O.castJointAction ss (fun i => π i (O.projectStates i ss))) := by
  simp [ObsModelCore.stepDist, jointActionDist_pureToBehavioral]

/-- The step distribution depends only on the profile's values at the current
information state. -/
theorem stepDist_pureToBehavioral_congr
    {π₁ π₂ : PureProfile O} (ss : List σ)
    (h : ∀ i, π₁ i (O.projectStates i ss) = π₂ i (O.projectStates i ss)) :
    O.stepDist (O.pureToBehavioral π₁) ss =
      O.stepDist (O.pureToBehavioral π₂) ss := by
  simp only [stepDist_pureToBehavioral]
  congr 1
  funext i
  exact congrArg (O.currentObs_projectStates i ss ▸ ·) (h i)

end StepLemmas

section RunLemmas

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

/-- Traces in the support of `runDistPure n` have length `n + 1`. -/
theorem runDistPure_support_length
    (n : Nat) (π : PureProfile O) (ss : List σ)
    (h : O.runDistPure n π ss ≠ 0) : ss.length = n + 1 := by
  rw [runDistPure_eq_pureRun] at h
  exact pureRun_length O.pureStep O.init n π ss h

/-- `runDistPure n` depends only on information states reachable within horizon
`n`. -/
theorem runDistPure_congr_of_agree_within
    {π₁ π₂ : PureProfile O} (n : Nat)
    (h : ∀ i (v : O.InfoState i), O.ReachableInfoStateWithin i n v → π₁ i v = π₂ i v) :
    O.runDistPure n π₁ = O.runDistPure n π₂ := by
  induction n with
  | zero =>
      simp [ObsModelCore.runDistPure, ObsModelCore.runDist]
  | succ n ih =>
      have hle : ∀ i (v : O.InfoState i), O.ReachableInfoStateWithin i n v → π₁ i v = π₂ i v :=
        fun i v hv => h i v (O.reachableInfoStateWithin_mono i hv (Nat.le_succ _))
      have hIH := ih hle
      ext ss
      simp only [runDistPure]
      change (O.runDist n (O.pureToBehavioral π₁)).bind _ ss =
        (O.runDist n (O.pureToBehavioral π₂)).bind _ ss
      rw [show O.runDist n (O.pureToBehavioral π₁) = O.runDist n (O.pureToBehavioral π₂) from hIH]
      simp only [PMF.bind_apply]
      congr 1
      funext ss'
      by_cases hne : (O.runDist n (O.pureToBehavioral π₂)) ss' = 0
      · simp [hne]
      · have hlen : ss'.length = n + 1 := by
          apply runDistPure_support_length (O := O) n π₂
          simpa [runDistPure] using hne
        have hstep : O.stepDist (O.pureToBehavioral π₁) ss' =
            O.stepDist (O.pureToBehavioral π₂) ss' :=
          stepDist_pureToBehavioral_congr (O := O) ss' (fun i =>
            h i _ (O.reachableInfoStateWithin_projectStates i (by omega)))
        have hpush := congrArg
          (fun d => Math.ProbabilityMassFunction.pushforward d (fun t => ss' ++ [t])) hstep
        exact congrArg
          (fun x => (O.runDist n (O.pureToBehavioral π₂)) ss' * x)
          (congrArg (· ss) hpush)

end RunLemmas

section MarginalStep

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.InfoState i)]

open Classical in
/-- The marginal of the pure step over the product measure equals the behavioral
step. -/
theorem marginal_stepDist
    [∀ i, Fintype (O.LocalStrategy i)]
    (β : BehavioralProfile O) (ss : List σ) :
    (O.behavioralToMixedJoint β).bind
      (fun π => O.stepDist (O.pureToBehavioral π) ss) =
      O.stepDist β ss := by
  rw [show (fun π => O.stepDist (O.pureToBehavioral π) ss) =
      (fun π => O.step (O.lastState ss)
        (O.castJointAction ss (fun i => π i (O.projectStates i ss)))) from by
        funext π
        exact stepDist_pureToBehavioral (O := O) π ss]
  simp only [ObsModelCore.stepDist]
  suffices hpush : (O.behavioralToMixedJoint β).bind
      (fun π => PMF.pure (fun i => π i (O.projectStates i ss))) =
      O.jointActionDist β ss by
    calc
      (O.behavioralToMixedJoint β).bind
          (fun π => O.step (O.lastState ss)
            (O.castJointAction ss (fun i => π i (O.projectStates i ss)))) =
        ((O.behavioralToMixedJoint β).bind
          (fun π => PMF.pure (fun i => π i (O.projectStates i ss)))).bind
            (fun a => O.step (O.lastState ss) (O.castJointAction ss a)) := by
              rw [PMF.bind_bind]
              simp
      _ = O.stepDist β ss := by
          rw [hpush]
          rfl
  unfold behavioralToMixedJoint behavioralToMixed jointActionDist
  ext a
  simp only [PMF.bind_apply, PMF.pure_apply]
  rw [tsum_fintype]
  simp_rw [mul_ite, mul_one, mul_zero, @eq_comm _ a]
  have hfactor : ∀ π : PureProfile O,
      (if (fun i => π i (O.projectStates i ss)) = a
        then (Math.PMFProduct.pmfPi (fun i => Math.PMFProduct.pmfPi (β i))) π else 0) =
      ∏ i, (if π i (O.projectStates i ss) = a i
        then (Math.PMFProduct.pmfPi (β i)) (π i) else 0) := by
    intro π
    by_cases h : (fun i => π i (O.projectStates i ss)) = a
    · rw [if_pos h, Math.PMFProduct.pmfPi_apply]
      apply Finset.prod_congr rfl
      intro i _
      rw [if_pos (congr_fun h i)]
    · rw [if_neg h]
      have ⟨i, hi⟩ : ∃ i, π i (O.projectStates i ss) ≠ a i := by
        by_contra hall
        push_neg at hall
        exact h (funext hall)
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])).symm
  simp_rw [hfactor]
  rw [show (∑ x : PureProfile O, ∏ i, if x i (O.projectStates i ss) = a i
        then (Math.PMFProduct.pmfPi (β i)) (x i) else 0) =
      (∏ i, ∑ πi : O.LocalStrategy i, if πi (O.projectStates i ss) = a i
        then (Math.PMFProduct.pmfPi (β i)) πi else 0) from
    (@Fintype.prod_sum ι ENNReal _ _ _ (fun i => O.LocalStrategy i) _
      (fun i πi => if πi (O.projectStates i ss) = a i
        then (Math.PMFProduct.pmfPi (β i)) πi else 0)).symm]
  change (∏ i, ∑ πi : O.LocalStrategy i, if πi (O.projectStates i ss) = a i
      then (Math.PMFProduct.pmfPi (β i)) πi else 0) =
    ∏ i, β i (O.projectStates i ss) (a i)
  congr 1
  funext i
  convert Math.PMFProduct.pmfPi_coord_mass (β i) (O.projectStates i ss) (a i)

end MarginalStep

section ScalarIndependence

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.InfoState i)]

open Classical in
/-- Swap: use `π₁` on states reachable within horizon `n`, and `π₂` otherwise. -/
noncomputable def swapProfile
    (n : Nat) (π₁ π₂ : PureProfile O) : PureProfile O :=
  fun i v => if O.ReachableInfoStateWithin i n v then π₁ i v else π₂ i v

omit [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)] [∀ i, Fintype (O.InfoState i)] in
theorem swapProfile_involutive (n : Nat) :
    Function.Involutive (fun (p : PureProfile O × PureProfile O) =>
      (swapProfile (O := O) n p.1 p.2, swapProfile (O := O) n p.2 p.1)) := by
  intro ⟨π₁, π₂⟩
  apply Prod.ext
  · funext i v
    by_cases hv : O.ReachableInfoStateWithin i n v <;> simp [swapProfile, hv]
  · funext i v
    by_cases hv : O.ReachableInfoStateWithin i n v <;> simp [swapProfile, hv]

set_option linter.unusedFintypeInType false in
open Classical in
theorem swap_weight_eq
    [∀ i, Fintype (O.LocalStrategy i)]
    [Fintype (PureProfile O)]
    (β : BehavioralProfile O) (n : Nat) (π₁ π₂ : PureProfile O) :
    (O.behavioralToMixedJoint β) (swapProfile (O := O) n π₁ π₂) *
    (O.behavioralToMixedJoint β) (swapProfile (O := O) n π₂ π₁) =
    (O.behavioralToMixedJoint β) π₁ *
    (O.behavioralToMixedJoint β) π₂ := by
  simp only [behavioralToMixedJoint, behavioralToMixed, Math.PMFProduct.pmfPi_apply]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  funext i
  simp only [swapProfile]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  funext v
  by_cases hv : O.ReachableInfoStateWithin i n v <;> simp [hv, mul_comm]

open Classical in
theorem scalar_indep
    [∀ i, Fintype (O.LocalStrategy i)]
    [Fintype (PureProfile O)]
    (β : BehavioralProfile O) (n : Nat)
    (f g : PureProfile O → ENNReal)
    (hf : ∀ π₁ π₂ : PureProfile O,
      (∀ i (v : O.InfoState i), O.ReachableInfoStateWithin i n v → π₁ i v = π₂ i v) →
        f π₁ = f π₂)
    (hg : ∀ π₁ π₂ : PureProfile O,
      (∀ i (v : O.InfoState i), ¬ O.ReachableInfoStateWithin i n v → π₁ i v = π₂ i v) →
        g π₁ = g π₂) :
    ∑ π, (O.behavioralToMixedJoint β) π * (f π * g π) =
      (∑ π, (O.behavioralToMixedJoint β) π * f π) *
      (∑ π, (O.behavioralToMixedJoint β) π * g π) := by
  set ν := O.behavioralToMixedJoint β
  have hf_swap : ∀ π₁ π₂, f (swapProfile (O := O) n π₁ π₂) = f π₁ := by
    intro π₁ π₂
    apply hf
    intro i v hv
    simp [swapProfile, hv]
  have hg_swap : ∀ π₁ π₂, g (swapProfile (O := O) n π₁ π₂) = g π₂ := by
    intro π₁ π₂
    apply hg
    intro i v hv
    simp [swapProfile, hv]
  let P := fun π => ν π
  let Fsame : PureProfile O × PureProfile O → ENNReal :=
    fun p => P p.1 * P p.2 * (f p.1 * g p.1)
  let Fcross : PureProfile O × PureProfile O → ENNReal :=
    fun p => P p.1 * P p.2 * (f p.1 * g p.2)
  let e : PureProfile O × PureProfile O → PureProfile O × PureProfile O :=
    fun p => (swapProfile (O := O) n p.1 p.2, swapProfile (O := O) n p.2 p.1)
  have he : Function.Involutive e := swapProfile_involutive (O := O) n
  have hpoint : ∀ p, Fcross p = Fsame (e p) := by
    intro ⟨π₁, π₂⟩
    simp only [Fcross, Fsame, e, P]
    rw [swap_weight_eq (O := O) β n π₁ π₂, hf_swap π₁ π₂, hg_swap π₁ π₂]
  have hFsame_eq_Fcross : ∑ p : PureProfile O × PureProfile O, Fsame p =
      ∑ p : PureProfile O × PureProfile O, Fcross p := by
    calc
      ∑ p, Fsame p = ∑ p, Fsame (e p) :=
        (Math.PMFProduct.sum_univ_eq_sum_univ_of_involutive e he Fsame).symm
      _ = ∑ p, Fcross p := by
        congr 1
        funext p
        exact (hpoint p).symm
  have hFsame_expand : ∑ p : PureProfile O × PureProfile O, Fsame p =
      (∑ π, ν π * (f π * g π)) * (∑ π₂, ν π₂) := by
    have h1 : ∀ (a b : PureProfile O),
        Fsame (a, b) = (ν a * (f a * g a)) * ν b := fun a b => by
      simp [Fsame, P]
      ring
    simp_rw [Fintype.sum_prod_type, h1, ← Finset.mul_sum, ← Finset.sum_mul]
  have hFcross_expand : ∑ p : PureProfile O × PureProfile O, Fcross p =
      (∑ π, ν π * f π) * (∑ π, ν π * g π) := by
    have h1 : ∀ (a b : PureProfile O),
        Fcross (a, b) = (ν a * f a) * (ν b * g b) := fun a b => by
      simp [Fcross, P]
      ring
    simp_rw [Fintype.sum_prod_type, h1, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
  have hsum_one : (∑ π : PureProfile O, ν π) = 1 := by
    have := PMF.tsum_coe ν
    rwa [tsum_fintype] at this
  calc
    ∑ π, ν π * (f π * g π) = (∑ π, ν π * (f π * g π)) * 1 := by ring
    _ = (∑ π, ν π * (f π * g π)) * (∑ π₂, ν π₂) := by rw [hsum_one]
    _ = ∑ p : PureProfile O × PureProfile O, Fsame p := hFsame_expand.symm
    _ = ∑ p : PureProfile O × PureProfile O, Fcross p := hFsame_eq_Fcross
    _ = (∑ π, ν π * f π) * (∑ π, ν π * g π) := hFcross_expand

end ScalarIndependence

section StepIndependenceBridge

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]
variable [∀ i, Fintype (O.InfoState i)]

open Classical in
set_option linter.unusedFintypeInType false in
theorem stepIndependence_bridge
    [∀ i, Fintype (O.LocalStrategy i)]
    [Fintype (PureProfile O)]
    (hSep : O.HorizonSeparation)
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
    marginal_stepDist (O := O) β
  ext y
  let Lfun : List σ → ENNReal := fun ss =>
    (Math.ProbabilityMassFunction.pushforward (O.stepDist β ss) (fun t => ss ++ [t])) y
  let Gfun : List σ → PureProfile O → ENNReal := fun ss π =>
    (Math.ProbabilityMassFunction.pushforward
      (O.stepDist (O.pureToBehavioral π) ss) (fun t => ss ++ [t])) y
  simp only [PMF.bind_apply]
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
  congr 1
  funext ss
  by_cases hlen : ss.length = n + 1
  · let f : PureProfile O → ENNReal := fun π => (O.runDistPure n π) ss
    let g : PureProfile O → ENNReal := fun π => Gfun ss π
    have hf : ∀ π₁ π₂ : PureProfile O,
        (∀ i (v : O.InfoState i), O.ReachableInfoStateWithin i n v → π₁ i v = π₂ i v) →
          f π₁ = f π₂ := by
      intro π₁ π₂ hag
      exact congrArg (· ss) (runDistPure_congr_of_agree_within (O := O) n hag)
    have hg : ∀ π₁ π₂ : PureProfile O,
        (∀ i (v : O.InfoState i), ¬ O.ReachableInfoStateWithin i n v → π₁ i v = π₂ i v) →
          g π₁ = g π₂ := by
      intro π₁ π₂ hag
      change Gfun ss π₁ = Gfun ss π₂
      simp only [Gfun]
      rw [stepDist_pureToBehavioral_congr (O := O) ss (fun i =>
        by
          by_cases hreach : O.ReachableInfoStateWithin i n (O.projectStates i ss)
          · rcases hreach with ⟨ss', hss', hproj⟩
            have hsub : Subsingleton (Act i (O.currentObs i (O.projectStates i ss))) := by
              apply hSep i hproj
              omega
            exact Subsingleton.elim _ _
          · exact hag i _ hreach)]
    have hind :
        ∑ π, ν π * (f π * g π) =
          (∑ π, ν π * f π) * (∑ π, ν π * g π) :=
      scalar_indep (O := O) β n f g hf hg
    have hEg : (∑ π, ν π * g π) = Lfun ss := by
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
    calc
      (∑' π, ν π * ((O.runDistPure n π) ss * Lfun ss)) =
        ∑ π, ν π * (f π * Lfun ss) := by simp [f, tsum_fintype]
      _ = (∑ π, ν π * f π) * Lfun ss := by
          simp_rw [← mul_assoc]
          exact (Finset.sum_mul ..).symm
      _ = (∑ π, ν π * f π) * (∑ π, ν π * g π) := by rw [hEg]
      _ = ∑ π, ν π * (f π * g π) := hind.symm
      _ = ∑' π, ν π * ((O.runDistPure n π) ss * Gfun ss π) := by
          simp [f, g, tsum_fintype]
  · have hzero : ∀ π : PureProfile O, (O.runDistPure n π) ss = 0 := by
      intro π
      by_contra hne
      exact hlen (runDistPure_support_length (O := O) n π ss hne)
    simp [hzero]

end StepIndependenceBridge

section MainTheorem

variable [DecidableEq ι] [Fintype ι] [∀ i o, Fintype (Act i o)]

set_option linter.unusedFintypeInType false in
open Classical in
/-- Generic step-independence implies trace-distribution equality on the core
model.  This local copy keeps the core B->M development self-contained. -/
theorem runDist_eq_of_stepIndependence
    (ν : PMF (PureProfile O))
    (b : BehavioralProfile O)
    (hStep : ∀ n,
      ν.bind (fun π =>
        (O.runDistPure n π).bind (fun ss =>
          pushforward (O.stepDist b ss) (fun t => ss ++ [t]))) =
      ν.bind (fun π =>
        (O.runDistPure n π).bind (fun ss =>
          pushforward (O.stepDist (O.pureToBehavioral π) ss)
            (fun t => ss ++ [t])))) (k : Nat) :
    O.runDist k b = ν.bind (fun π => O.runDistPure k π) := by
  induction k with
  | zero =>
      simp [ObsModelCore.runDist, ObsModelCore.runDistPure]
  | succ n ih =>
      calc
        O.runDist (n + 1) b
          = (O.runDist n b).bind (fun ss =>
              pushforward (O.stepDist b ss) (fun t => ss ++ [t])) := by
                simp [ObsModelCore.runDist]
        _ = (ν.bind (fun π => O.runDistPure n π)).bind (fun ss =>
              pushforward (O.stepDist b ss) (fun t => ss ++ [t])) := by
                rw [ih]
        _ = ν.bind (fun π =>
              (O.runDistPure n π).bind (fun ss =>
                pushforward (O.stepDist b ss) (fun t => ss ++ [t]))) := by
                rw [PMF.bind_bind]
        _ = ν.bind (fun π =>
              (O.runDistPure n π).bind (fun ss =>
                pushforward (O.stepDist (O.pureToBehavioral π) ss)
                  (fun t => ss ++ [t]))) := by
                simpa using hStep n
        _ = ν.bind (fun π => O.runDistPure (n + 1) π) := by
                simp [ObsModelCore.runDist, ObsModelCore.runDistPure]

/-- **Kuhn's theorem, B->M direction for `ObsModelCore`.**
Every behavioral profile has the same bounded trace distribution as the
corresponding ex-ante product mixed strategy, provided nontrivial information
states do not recur at different horizons. -/
theorem kuhn_behavioral_to_mixed
    [∀ i, Fintype (O.InfoState i)]
    [∀ i, Fintype (O.LocalStrategy i)]
    (hSep : O.HorizonSeparation)
    (β : BehavioralProfile O) (k : Nat) :
    O.runDist k β =
      (O.behavioralToMixedJoint β).bind (fun π => O.runDistPure k π) := by
  exact runDist_eq_of_stepIndependence (O := O)
    (O.behavioralToMixedJoint β) β
    (fun n => stepIndependence_bridge (O := O) hSep β n) k

end MainTheorem

end ObsModelCore
