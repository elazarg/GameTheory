/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Real.Basic

/-!
# Cyclic Schur elimination for block-pair predecessor charts

A locally selected predecessor chart has an invertible active-hazard block.
Solving that block produces its value derivative.  For a finite temporal word,
this file proves that the kernel of the full cyclic Jacobian is linearly
equivalent to the kernel of `I` minus the ordered return derivative.

The endpoint-indexed formulation makes composition orientation explicit: for
two temporal phases, the return derivative is `T₀.comp T₁`.
-/

noncomputable section

namespace Math.LinearAlgebra.CyclicSchur

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

abbrev CyclicVariables {K : ℕ} (H : Fin K → Type*) (E : Type*) :=
  (∀ k, H k) × (Fin (K + 1) → E)

/-- The four blocks of one locally linearized predecessor equation.  The
active-hazard block is supplied as an equivalence because this is exactly the
local nondegeneracy used by Schur elimination. -/
structure LocalLinearization (K : ℕ) (H : Fin K → Type*) (E : Type*)
    [∀ k, AddCommGroup (H k)] [∀ k, Module ℝ (H k)]
    [AddCommGroup E] [Module ℝ E] where
  activeBlock : ∀ k : Fin K, H k ≃ₗ[ℝ] H k
  continuationBlock : ∀ k : Fin K, E →ₗ[ℝ] H k
  hazardValueBlock : ∀ k : Fin K, H k →ₗ[ℝ] E
  directValueBlock : ∀ _ : Fin K, E →ₗ[ℝ] E

variable {K : ℕ} {H : Fin K → Type*}
variable [∀ k, AddCommGroup (H k)] [∀ k, Module ℝ (H k)]

/-- The derivative of the selected one-phase predecessor chart after solving
the active equations for the hazard perturbation. -/
def chartDerivative (data : LocalLinearization K H E) (k : Fin K) :
    E →ₗ[ℝ] E :=
  (data.hazardValueBlock k).comp
      ((data.activeBlock k).symm.toLinearMap.comp
        (data.continuationBlock k)) +
    data.directValueBlock k

/-- Maps a terminal perturbation backwards to every cut of a temporal word. -/
def backwardMaps : (K : ℕ) → (Fin K → E →ₗ[ℝ] E) →
    Fin (K + 1) → E →ₗ[ℝ] E
  | 0, _ => fun _ => LinearMap.id
  | K + 1, chart =>
      let tail := backwardMaps K (fun k => chart k.succ)
      Fin.cases ((chart 0).comp (tail 0)) tail

/-- The first chart is outermost, so the last temporal phase acts first. -/
def orderedReturn {K : ℕ} (chart : Fin K → E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  backwardMaps K chart 0

@[simp] theorem backwardMaps_castSucc {K : ℕ}
    (chart : Fin K → E →ₗ[ℝ] E) (k : Fin K) :
    backwardMaps K chart k.castSucc =
      (chart k).comp (backwardMaps K chart k.succ) := by
  induction K with
  | zero => exact Fin.elim0 k
  | succ K ih =>
      refine Fin.cases ?_ (fun j => ?_) k
      · rfl
      · change
          backwardMaps K (fun i => chart i.succ) j.castSucc =
            (chart j.succ).comp
              (backwardMaps K (fun i => chart i.succ) j.succ)
        exact ih (fun i => chart i.succ) j

@[simp] theorem backwardMaps_last {K : ℕ}
    (chart : Fin K → E →ₗ[ℝ] E) :
    backwardMaps K chart (Fin.last K) = LinearMap.id := by
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [← Fin.succ_last]
      exact ih (fun i => chart i.succ)

/-- Every path satisfying the local linearized predecessor recurrences is
the backwards propagation of its terminal value. -/
theorem path_eq_backwardMaps {K : ℕ}
    (chart : Fin K → E →ₗ[ℝ] E)
    (value : Fin (K + 1) → E)
    (hstep : ∀ k : Fin K,
      value k.castSucc = chart k (value k.succ)) :
    ∀ j, value j =
      backwardMaps K chart j (value (Fin.last K)) := by
  induction K with
  | zero =>
      intro j
      fin_cases j
      rfl
  | succ K ih =>
      let tailChart : Fin K → E →ₗ[ℝ] E := fun k => chart k.succ
      let tailValue : Fin (K + 1) → E := fun j => value j.succ
      have htailStep : ∀ k : Fin K,
          tailValue k.castSucc = tailChart k (tailValue k.succ) := by
        intro k
        simpa [tailChart, tailValue] using hstep k.succ
      have htail := ih tailChart tailValue htailStep
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · have hzero : value 0 = chart 0 (value (Fin.succ 0)) := by
          simpa using hstep (0 : Fin (K + 1))
        rw [hzero]
        simpa [backwardMaps, tailChart, tailValue, ← Fin.succ_last] using
          congrArg (chart 0) (htail 0)
      · simpa [backwardMaps, tailChart, tailValue, ← Fin.succ_last] using
          htail k

/-- The full cyclic Jacobian.  Its first component consists of the active
equations.  The zeroth value component is the endpoint-closing equation, and
component `k.succ` is the value equation for phase `k`. -/
def fullJacobian (data : LocalLinearization K H E) :
    CyclicVariables H E →ₗ[ℝ] CyclicVariables H E where
  toFun z :=
    (fun k => data.activeBlock k (z.1 k) -
        data.continuationBlock k (z.2 k.succ),
      fun j => Fin.cases
        (z.2 0 - z.2 (Fin.last K))
        (fun k => z.2 k.castSucc - data.hazardValueBlock k (z.1 k) -
          data.directValueBlock k (z.2 k.succ)) j)
  map_add' x y := by
    ext k
    · simp
      abel
    · refine Fin.cases ?_ (fun j => ?_) k <;> simp <;> abel
  map_smul' c x := by
    ext k
    · simp [smul_sub]
    · refine Fin.cases ?_ (fun j => ?_) k <;> simp [smul_sub]

/-- The cyclic closing defect after all active variables have been
eliminated. -/
def returnDefect (data : LocalLinearization K H E) : E →ₗ[ℝ] E :=
  LinearMap.id - orderedReturn (chartDerivative data)

/-- Backwards propagation of values from a terminal perturbation. -/
def valueLift (data : LocalLinearization K H E) :
    E →ₗ[ℝ] (Fin (K + 1) → E) :=
  LinearMap.pi (backwardMaps K (chartDerivative data))

/-- The active-hazard perturbations recovered from backwards-propagated
values. -/
def hazardLift (data : LocalLinearization K H E) :
    E →ₗ[ℝ] (∀ k, H k) :=
  LinearMap.pi fun k =>
    (data.activeBlock k).symm.toLinearMap.comp
      ((data.continuationBlock k).comp
        (backwardMaps K (chartDerivative data) k.succ))

/-- The full perturbation reconstructed from its terminal value. -/
def fullLift (data : LocalLinearization K H E) :
    E →ₗ[ℝ] CyclicVariables H E :=
  (hazardLift data).prod (valueLift data)

/-- Forget all variables except the value perturbation after the last phase. -/
def terminalProjection : CyclicVariables H E →ₗ[ℝ] E where
  toFun z := z.2 (Fin.last K)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem terminalProjection_apply (z : CyclicVariables H E) :
    terminalProjection z = z.2 (Fin.last K) := rfl

theorem active_eq_of_fullJacobian_eq_zero
    (data : LocalLinearization K H E) {z : CyclicVariables H E}
    (hz : fullJacobian data z = 0) (k : Fin K) :
    z.1 k = (data.activeBlock k).symm
      (data.continuationBlock k (z.2 k.succ)) := by
  have hcomponent := congrFun (congrArg Prod.fst hz) k
  change data.activeBlock k (z.1 k) -
    data.continuationBlock k (z.2 k.succ) = 0 at hcomponent
  apply (data.activeBlock k).injective
  simpa using sub_eq_zero.mp hcomponent

theorem value_step_of_fullJacobian_eq_zero
    (data : LocalLinearization K H E) {z : CyclicVariables H E}
    (hz : fullJacobian data z = 0) (k : Fin K) :
    z.2 k.castSucc = chartDerivative data k (z.2 k.succ) := by
  have hcomponent := congrFun (congrArg Prod.snd hz) k.succ
  change z.2 k.castSucc - data.hazardValueBlock k (z.1 k) -
    data.directValueBlock k (z.2 k.succ) = 0 at hcomponent
  have hvalue : z.2 k.castSucc =
      data.hazardValueBlock k (z.1 k) +
        data.directValueBlock k (z.2 k.succ) := by
    apply sub_eq_zero.mp
    simpa [sub_sub] using hcomponent
  rw [hvalue, active_eq_of_fullJacobian_eq_zero data hz k]
  simp [chartDerivative]

theorem value_close_of_fullJacobian_eq_zero
    (data : LocalLinearization K H E) {z : CyclicVariables H E}
    (hz : fullJacobian data z = 0) :
    z.2 0 = z.2 (Fin.last K) := by
  have hcomponent := congrFun (congrArg Prod.snd hz) 0
  change z.2 0 - z.2 (Fin.last K) = 0 at hcomponent
  exact sub_eq_zero.mp hcomponent

theorem returnDefect_terminalProjection_eq_zero
    (data : LocalLinearization K H E) {z : CyclicVariables H E}
    (hz : fullJacobian data z = 0) :
    returnDefect data (terminalProjection z) = 0 := by
  have hpath := path_eq_backwardMaps (chartDerivative data) z.2
    (value_step_of_fullJacobian_eq_zero data hz)
  have hreturn : orderedReturn (chartDerivative data)
      (z.2 (Fin.last K)) = z.2 (Fin.last K) := by
    calc
      orderedReturn (chartDerivative data) (z.2 (Fin.last K)) = z.2 0 := by
        simpa [orderedReturn] using (hpath 0).symm
      _ = z.2 (Fin.last K) := value_close_of_fullJacobian_eq_zero data hz
  simp [returnDefect, hreturn]

@[simp] theorem terminalProjection_fullLift
    (data : LocalLinearization K H E) (terminal : E) :
    terminalProjection (fullLift data terminal) = terminal := by
  simp [terminalProjection, fullLift, valueLift]

theorem fullLift_terminalProjection_eq_self
    (data : LocalLinearization K H E) {z : CyclicVariables H E}
    (hz : fullJacobian data z = 0) :
    fullLift data (terminalProjection z) = z := by
  have hpath := path_eq_backwardMaps (chartDerivative data) z.2
    (value_step_of_fullJacobian_eq_zero data hz)
  ext j
  · simp only [fullLift, hazardLift, terminalProjection, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.prod_apply, Function.prod_apply,
      LinearMap.pi_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply]
    rw [← hpath j.succ]
    exact (active_eq_of_fullJacobian_eq_zero data hz j).symm
  · simp only [fullLift, valueLift, terminalProjection, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.prod_apply, Function.prod_apply,
      LinearMap.pi_apply]
    exact (hpath j).symm

theorem fullJacobian_fullLift_eq_zero
    (data : LocalLinearization K H E) {terminal : E}
    (hterminal : returnDefect data terminal = 0) :
    fullJacobian data (fullLift data terminal) = 0 := by
  have hclose : orderedReturn (chartDerivative data) terminal = terminal := by
    have hsub : terminal - orderedReturn (chartDerivative data) terminal = 0 := by
      simpa [returnDefect] using hterminal
    exact (sub_eq_zero.mp hsub).symm
  ext j
  · simp [fullJacobian, fullLift, hazardLift, valueLift]
  · refine Fin.cases ?_ (fun k => ?_) j
    · simp only [fullJacobian, fullLift, valueLift, LinearMap.prod_apply,
        Function.prod_apply, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.pi_apply, backwardMaps_last, LinearMap.id_coe, id_eq,
        backwardMaps_castSucc, LinearMap.coe_comp, Function.comp_apply,
        Fin.cases_zero, Prod.snd_zero, Pi.zero_apply]
      exact sub_eq_zero.mpr hclose
    · simp [fullJacobian, fullLift, hazardLift, valueLift,
        chartDerivative]

/-- Terminal projection sends a full cyclic kernel vector to the reduced
return-defect kernel. -/
def fullKernelToReturnKernel (data : LocalLinearization K H E) :
    (fullJacobian data).ker →ₗ[ℝ] (returnDefect data).ker where
  toFun z := ⟨terminalProjection z,
    returnDefect_terminalProjection_eq_zero data (by
      simpa only [LinearMap.mem_ker] using z.property)⟩
  map_add' _ _ := by
    apply Subtype.ext
    simp
  map_smul' _ _ := by
    apply Subtype.ext
    simp

/-- Schur reconstruction sends a reduced kernel vector back to a full cyclic
kernel vector. -/
def returnKernelToFullKernel (data : LocalLinearization K H E) :
    (returnDefect data).ker →ₗ[ℝ] (fullJacobian data).ker where
  toFun terminal := ⟨fullLift data terminal,
    fullJacobian_fullLift_eq_zero data terminal.property⟩
  map_add' _ _ := by
    apply Subtype.ext
    simp
  map_smul' _ _ := by
    apply Subtype.ext
    simp

/-- Schur elimination identifies the kernel of the full cyclic Jacobian with
the kernel of `I` minus the ordered return derivative. -/
def fullJacobianKernelEquiv (data : LocalLinearization K H E) :
    (fullJacobian data).ker ≃ₗ[ℝ] (returnDefect data).ker :=
  LinearEquiv.ofLinear
    (fullKernelToReturnKernel data) (returnKernelToFullKernel data)
    (by
      apply LinearMap.ext
      intro terminal
      apply Subtype.ext
      change terminalProjection (fullLift data (terminal : E)) = terminal
      exact terminalProjection_fullLift data terminal)
    (by
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      change fullLift data (terminalProjection (z : CyclicVariables H E)) = z
      exact fullLift_terminalProjection_eq_self data (by
        simpa only [LinearMap.mem_ker] using z.property))

theorem fullJacobian_ker_eq_bot_iff (data : LocalLinearization K H E) :
    (fullJacobian data).ker = ⊥ ↔ (returnDefect data).ker = ⊥ := by
  let kernelEquiv := fullJacobianKernelEquiv data
  constructor
  · intro hfull
    refine (Submodule.eq_bot_iff _).mpr ?_
    intro terminal hterminal
    let terminalKernel : (returnDefect data).ker := ⟨terminal, hterminal⟩
    let fullKernel := kernelEquiv.symm terminalKernel
    have hfullZero : (fullKernel : CyclicVariables H E) = 0 := by
      exact (Submodule.eq_bot_iff _).mp hfull fullKernel fullKernel.property
    have hfullSubtypeZero : fullKernel = 0 := Subtype.ext hfullZero
    have hterminalSubtypeZero : terminalKernel = 0 := by
      calc
        terminalKernel = kernelEquiv fullKernel :=
          (kernelEquiv.apply_symm_apply terminalKernel).symm
        _ = kernelEquiv 0 := congrArg (fun x => kernelEquiv x) hfullSubtypeZero
        _ = 0 := map_zero kernelEquiv
    exact congrArg Subtype.val hterminalSubtypeZero
  · intro hreturn
    refine (Submodule.eq_bot_iff _).mpr ?_
    intro z hz
    let fullKernel : (fullJacobian data).ker := ⟨z, hz⟩
    let terminalKernel := kernelEquiv fullKernel
    have hterminalZero : (terminalKernel : E) = 0 := by
      exact (Submodule.eq_bot_iff _).mp hreturn terminalKernel
        terminalKernel.property
    have hterminalSubtypeZero : terminalKernel = 0 :=
      Subtype.ext hterminalZero
    have hfullSubtypeZero : fullKernel = 0 := by
      calc
        fullKernel = kernelEquiv.symm terminalKernel :=
          (kernelEquiv.symm_apply_apply fullKernel).symm
        _ = kernelEquiv.symm 0 :=
          congrArg (fun x => kernelEquiv.symm x) hterminalSubtypeZero
        _ = 0 := map_zero kernelEquiv.symm
    exact congrArg Subtype.val hfullSubtypeZero

theorem fullJacobian_injective_iff (data : LocalLinearization K H E) :
    Function.Injective (fullJacobian data) ↔
      Function.Injective (returnDefect data) := by
  rw [← LinearMap.ker_eq_bot, ← LinearMap.ker_eq_bot]
  exact fullJacobian_ker_eq_bot_iff data

/-- In finite dimensions, the full cyclic Jacobian is invertible exactly when
`I` minus the ordered return derivative is invertible. -/
theorem fullJacobian_isUnit_iff (data : LocalLinearization K H E)
    [FiniteDimensional ℝ E]
    [∀ k, FiniteDimensional ℝ (H k)] :
    IsUnit (fullJacobian data) ↔ IsUnit (returnDefect data) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.isUnit_iff_ker_eq_bot]
  exact fullJacobian_ker_eq_bot_iff data

@[simp] theorem orderedReturn_zero (chart : Fin 0 → E →ₗ[ℝ] E) :
    orderedReturn chart = LinearMap.id := rfl

@[simp] theorem orderedReturn_one (T₀ : E →ₗ[ℝ] E) :
    orderedReturn ![T₀] = T₀ := by
  ext x
  rfl

@[simp] theorem orderedReturn_two (T₀ T₁ : E →ₗ[ℝ] E) :
    orderedReturn ![T₀, T₁] = T₀.comp T₁ := by
  ext x
  rfl

end Math.LinearAlgebra.CyclicSchur
