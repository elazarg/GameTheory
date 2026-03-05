import GameTheory.Model.Lemmas.Profiles

namespace GameTheory
namespace InfoModel

open Execution
open Math.PMFProduct

variable {ι : Type} [Fintype ι]
variable {M : LSM ι} (I : InfoModel M)

/-- Condition a player-local mixed strategy on taking action `a` at local
observation trace `v`. Falls back to `μ` on zero-mass events. -/
noncomputable def condMixedLocal
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i))
    (v : I.LocalTrace i)
    (a : Option (M.Act i)) :
    PMF (InfoModel.LocalPure (I := I) i) :=
  if _ : Math.ProbabilityMassFunction.pushforward μi (fun f => f v) a ≠ 0 then
    Math.ProbabilityMassFunction.condOn μi (fun f => f v) a
  else
    μi

/-- Iterated local conditioning. -/
noncomputable def iterCondMixedLocal
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i)) :
    List (InfoModel.LocalHistTok (I := I) i) → PMF (InfoModel.LocalPure (I := I) i)
  | [] => μi
  | (v, a) :: rest =>
      iterCondMixedLocal i (condMixedLocal (I := I) i μi v a) rest

omit [Fintype ι] in
@[simp] theorem iterCondMixedLocal_nil
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i)) :
    iterCondMixedLocal (I := I) i μi [] = μi := rfl

omit [Fintype ι] in
/-- Repeated local conditioning composes by list append: conditioning on
`hist₁ ++ hist₂` is the same as first conditioning on `hist₁` and then on
`hist₂`. -/
theorem iterCondMixedLocal_append
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i))
    (hist₁ hist₂ : List (InfoModel.LocalHistTok (I := I) i)) :
    iterCondMixedLocal (I := I) i μi (hist₁ ++ hist₂) =
      iterCondMixedLocal (I := I) i
        (iterCondMixedLocal (I := I) i μi hist₁) hist₂ := by
  induction hist₁ generalizing μi with
  | nil =>
      simp [iterCondMixedLocal]
  | cons tok rest ih =>
      rcases tok with ⟨v, a⟩
      simp [iterCondMixedLocal, ih]

omit [Fintype ι] in
theorem pushforward_bind_condMixedLocal
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i))
    (v : I.LocalTrace i) :
    (Math.ProbabilityMassFunction.pushforward μi (fun f => f v)).bind
      (condMixedLocal (I := I) i μi v) = μi := by
  classical
  have hcond :
      ∀ a, (Math.ProbabilityMassFunction.pushforward μi (fun f => f v)) a ≠ 0 →
        condMixedLocal (I := I) i μi v a =
          Math.ProbabilityMassFunction.condOn μi (fun f => f v) a := by
    intro a ha
    simp [condMixedLocal, ha]
  calc
    (Math.ProbabilityMassFunction.pushforward μi (fun f => f v)).bind
        (condMixedLocal (I := I) i μi v)
        =
      (Math.ProbabilityMassFunction.pushforward μi (fun f => f v)).bind
        (fun a =>
          Math.ProbabilityMassFunction.condOn μi (fun f => f v) a) := by
            exact Math.ProbabilityMassFunction.bind_congr_of_ne_zero
              (μ := Math.ProbabilityMassFunction.pushforward μi (fun f => f v))
              (f := condMixedLocal (I := I) i μi v)
              (g := fun a => Math.ProbabilityMassFunction.condOn μi (fun f => f v) a)
              hcond
    _ = μi := by
          simpa using
            (Math.ProbabilityMassFunction.bind_pushforward_condOn
              (μ := μi) (proj := fun f => f v) (g := fun f => PMF.pure f)).symm

set_option linter.unusedFintypeInType false in
open Classical in
/-- Decompose a product-measure bind by sampling queried actions first,
then resampling local pure policies from per-player conditionals. -/
theorem mixedJoint_bind_decompose_query
    (μ : InfoModel.MixedProfile (I := I))
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (v : ∀ i, I.LocalTrace i)
    {β : Type}
    (g : PureProfile I → PMF β) :
    (InfoModel.mixedJoint (I := I) μ).bind g =
      (pmfPi (fun i => Math.ProbabilityMassFunction.pushforward (μ i) (fun f => f (v i)))).bind
        (fun acts =>
          (InfoModel.mixedJoint (I := I)
            (fun i => condMixedLocal (I := I) i (μ i) (v i) (acts i))).bind g) := by
  have hplayer :
      ∀ i fi,
        ∑ a : Option (M.Act i),
          (Math.ProbabilityMassFunction.pushforward (μ i) (fun f => f (v i))) a *
            (condMixedLocal (I := I) i (μ i) (v i) a) fi
          = (μ i) fi := by
    intro i fi
    have h := pushforward_bind_condMixedLocal (I := I) i (μ i) (v i)
    have hfi := PMF.ext_iff.mp h fi
    simpa only [PMF.bind_apply, tsum_fintype] using hfi
  apply PMF.ext
  intro y
  simp only [PMF.bind_apply, tsum_fintype, InfoModel.mixedJoint, pmfPi_apply]
  symm
  simp_rw [Finset.mul_sum, ← mul_assoc, ← Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  congr 1
  funext f
  congr 1
  rw [(Fintype.prod_sum
    (fun i a =>
      (Math.ProbabilityMassFunction.pushforward (μ i) (fun f => f (v i))) a *
        (condMixedLocal (I := I) i (μ i) (v i) a) (f i))).symm]
  congr 1
  funext i
  exact hplayer i (f i)

/-- Compatibility of a local pure policy with a realized local history. -/
def LocalHistCompatible
    (i : ι)
    (f : InfoModel.LocalPure (I := I) i)
    (hist : List (InfoModel.LocalHistTok (I := I) i)) : Prop :=
  ∀ tok ∈ hist, f tok.1 = tok.2

/-- Indicator that a local pure policy matches the realized local history. -/
noncomputable def localHistIndicator
    (i : ι)
    (f : InfoModel.LocalPure (I := I) i)
    (hist : List (InfoModel.LocalHistTok (I := I) i)) : ENNReal := by
  classical
  exact if LocalHistCompatible (I := I) i f hist then 1 else 0

/-- Normalizing mass accumulated by iterated local conditioning. -/
noncomputable def localHistMass
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i)) :
    List (InfoModel.LocalHistTok (I := I) i) → ENNReal
  | [] => 1
  | (v, a) :: rest =>
      (Math.ProbabilityMassFunction.pushforward μi (fun f => f v)) a *
        localHistMass i (condMixedLocal (I := I) i μi v a) rest

omit [Fintype ι] in
theorem localHistMass_mul_iterCondMixedLocal_apply
    (i : ι)
    [Fintype (InfoModel.LocalPure (I := I) i)]
    [Fintype (Option (M.Act i))]
    (μi : PMF (InfoModel.LocalPure (I := I) i)) :
    ∀ (hist : List (InfoModel.LocalHistTok (I := I) i)) (f : InfoModel.LocalPure (I := I) i),
      localHistMass (I := I) i μi hist *
          iterCondMixedLocal (I := I) i μi hist f =
        μi f * localHistIndicator (I := I) i f hist
  | [], f => by
      classical
      simp [localHistMass, localHistIndicator, LocalHistCompatible]
  | (v, a) :: rest, f => by
      classical
      have ih :=
        localHistMass_mul_iterCondMixedLocal_apply
          (i := i) (μi := condMixedLocal (I := I) i μi v a) rest f
      set p : ENNReal :=
        (Math.ProbabilityMassFunction.pushforward μi (fun g => g v)) a
      have hhead :
          p * condMixedLocal (I := I) i μi v a f =
            μi f * if f v = a then 1 else 0 := by
        by_cases hp : p = 0
        · by_cases hfa : f v = a
          · have hf0 : μi f = 0 := by
              apply Math.ProbabilityMassFunction.eq_zero_of_pushforward_eq_zero
                (μ := μi) (proj := fun g => g v) (b := a) hp
              simpa using hfa
            simp [p, hp, condMixedLocal, hfa, hf0]
          · simp [p, hp, condMixedLocal, hfa]
        · have hp' : p ≠ 0 := hp
          have hcond :
              condMixedLocal (I := I) i μi v a =
                Math.ProbabilityMassFunction.condOn μi (fun g => g v) a := by
            simp [condMixedLocal, p, hp']
          rw [hcond]
          rw [Math.ProbabilityMassFunction.condOn_apply
            (μ := μi) (proj := fun g => g v) (b := a) (a := f) hp']
          by_cases hfa : f v = a
          · simp [p, hfa, div_eq_mul_inv, mul_left_comm, mul_comm,
              ENNReal.mul_inv_cancel hp' (PMF.apply_ne_top _ _)]
          · simp [p, hfa]
      calc
        localHistMass (I := I) i μi ((v, a) :: rest) *
            iterCondMixedLocal (I := I) i μi ((v, a) :: rest) f
            =
          p * (localHistMass (I := I) i
            (condMixedLocal (I := I) i μi v a) rest *
              iterCondMixedLocal (I := I) i
                (condMixedLocal (I := I) i μi v a) rest f) := by
                simp [localHistMass, iterCondMixedLocal, p, mul_assoc]
        _ =
          p * ((condMixedLocal (I := I) i μi v a) f *
            localHistIndicator (I := I) i f rest) := by
              rw [ih]
        _ =
          (p * condMixedLocal (I := I) i μi v a f) *
            localHistIndicator (I := I) i f rest := by
              ac_rfl
        _ =
          (μi f * if f v = a then 1 else 0) *
            localHistIndicator (I := I) i f rest := by
              rw [hhead]
        _ =
          μi f * ((if f v = a then 1 else 0) *
            localHistIndicator (I := I) i f rest) := by
              ac_rfl
        _ =
          μi f * localHistIndicator (I := I) i f ((v, a) :: rest) := by
              by_cases hfa : f v = a <;>
                by_cases hrest : LocalHistCompatible (I := I) i f rest <;>
                simp [localHistIndicator, LocalHistCompatible, hfa]

omit [Fintype ι] in
theorem localHistCompatible_append_singleton_iff
    (i : ι)
    (f : InfoModel.LocalPure (I := I) i)
    (hist : List (InfoModel.LocalHistTok (I := I) i))
    (v : I.LocalTrace i)
    (a : Option (M.Act i)) :
    LocalHistCompatible (I := I) i f (hist ++ [(v, a)]) ↔
      LocalHistCompatible (I := I) i f hist ∧ f v = a := by
  constructor
  · intro h
    constructor
    · intro tok htok
      exact h tok (by simp [htok])
    · exact h (v, a) (by simp)
  · rintro ⟨hhist, hv⟩ tok htok
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at htok
    rcases htok with htok | htok
    · exact hhist tok htok
    · rcases htok with rfl
      exact hv

/-- Product-measure identity after conditioning each player's marginal on its
realized local history. -/
theorem localHistMass_mul_mixedJoint_iterCond_apply
    [∀ i, Fintype (InfoModel.LocalPure (I := I) i)]
    [∀ i, Fintype (Option (M.Act i))]
    (μ : InfoModel.MixedProfile (I := I))
    (hist : ∀ i, List (InfoModel.LocalHistTok (I := I) i))
    (π : PureProfile I) :
    (∏ i, localHistMass (I := I) i (μ i) (hist i)) *
      (InfoModel.mixedJoint (I := I)
        (fun i => iterCondMixedLocal (I := I) i (μ i) (hist i))) π
      =
    (InfoModel.mixedJoint (I := I) μ) π *
      ∏ i, localHistIndicator (I := I) i (π i) (hist i) := by
  simp only [InfoModel.mixedJoint, pmfPi_apply]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  funext i
  exact localHistMass_mul_iterCondMixedLocal_apply
    (I := I) i (μi := μ i) (hist i) (π i)

end InfoModel
end GameTheory
