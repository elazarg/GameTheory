/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.Real.Basic

/-!
# Compatibility of a finite family of linear equations

For finitely many vectors `delta a` and prescribed levels `level a`, either
one vector pairs with every `delta a` at the prescribed level, or a signed
linear dependence among the `delta a` fails for the corresponding levels.
This is the exact finite-dimensional compatibility alternative.
-/

namespace Math

open scoped BigOperators

variable {State Action : Type*}

/-- The linear map which records all pairings with a finite family of
vectors. -/
def finitePairingMap [Fintype State] [Fintype Action]
    (delta : Action → State → ℝ) :
    (State → ℝ) →ₗ[ℝ] (Action → ℝ) where
  toFun potential action := dotProduct (delta action) potential
  map_add' potential₁ potential₂ := by
    funext action
    simp [dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' scalar potential := by
    funext action
    simp [dotProduct, mul_left_comm, Finset.mul_sum]

theorem finitePairingMap_apply [Fintype State] [Fintype Action]
    (delta : Action → State → ℝ) (potential : State → ℝ)
    (action : Action) :
    finitePairingMap delta potential action =
      dotProduct (delta action) potential :=
  rfl

/-- **Finite linear compatibility alternative.** Exactly one of the
following kinds of certificate exists:

* a potential whose pairing with every `delta a` is `level a`;
* signed coefficients balancing the `delta a` but not the `level a`.

The theorem states existence as a disjunction. The two branches are
automatically exclusive by taking the pairing of the balance with a
compatible potential. -/
theorem exists_potential_or_signed_incompatibility
    [Fintype State] [Fintype Action]
    (delta : Action → State → ℝ) (level : Action → ℝ) :
    (∃ potential : State → ℝ,
      ∀ action, dotProduct (delta action) potential = level action) ∨
    (∃ coefficient : Action → ℝ,
      (∀ state, ∑ action, coefficient action * delta action state = 0) ∧
      ∑ action, coefficient action * level action ≠ 0) := by
  classical
  let pairing := finitePairingMap delta
  by_cases hcompatible : level ∈ LinearMap.range pairing
  · left
    obtain ⟨potential, hpotential⟩ := hcompatible
    refine ⟨potential, fun action => ?_⟩
    exact congrFun hpotential action
  · right
    obtain ⟨functional, hlevel, hvanish⟩ :=
      (LinearMap.range pairing).exists_dual_map_eq_bot_of_notMem
        hcompatible inferInstance
    let coefficient : Action → ℝ := fun action =>
      functional fun other => if action = other then 1 else 0
    have functional_eq_sum (x : Action → ℝ) :
        functional x = ∑ action, coefficient action * x action := by
      rw [LinearMap.pi_apply_eq_sum_univ]
      simp only [coefficient, smul_eq_mul]
      exact Finset.sum_congr rfl fun action _ => by ring
    have functional_pairing_zero (potential : State → ℝ) :
        functional (pairing potential) = 0 := by
      have hmem :
          functional (pairing potential) ∈
            (LinearMap.range pairing).map functional :=
        ⟨pairing potential, LinearMap.mem_range_self _ potential, rfl⟩
      rw [hvanish] at hmem
      simpa using hmem
    refine ⟨coefficient, ?_, ?_⟩
    · intro state
      let basisPotential : State → ℝ := fun other =>
        if state = other then 1 else 0
      have hzero := functional_pairing_zero basisPotential
      rw [functional_eq_sum] at hzero
      have hpairing (action : Action) :
          pairing basisPotential action = delta action state := by
        simp [pairing, finitePairingMap, basisPotential, dotProduct]
      simpa only [hpairing] using hzero
    · rw [← functional_eq_sum]
      exact hlevel

/-- A compatible potential and a signed incompatibility witness cannot
coexist. -/
theorem not_signed_incompatibility_of_potential
    [Fintype State] [Fintype Action]
    {delta : Action → State → ℝ} {level : Action → ℝ}
    {potential : State → ℝ}
    (hpotential :
      ∀ action, dotProduct (delta action) potential = level action)
    {coefficient : Action → ℝ}
    (hbalance :
      ∀ state, ∑ action, coefficient action * delta action state = 0) :
    ∑ action, coefficient action * level action = 0 := by
  classical
  calc
    ∑ action, coefficient action * level action =
        ∑ action, coefficient action *
          dotProduct (delta action) potential := by
            apply Finset.sum_congr rfl
            intro action _
            rw [hpotential action]
    _ = ∑ action, ∑ state,
        coefficient action *
          (delta action state * potential state) := by
            apply Finset.sum_congr rfl
            intro action _
            simp only [dotProduct, Finset.mul_sum]
    _ = ∑ state, ∑ action,
        coefficient action *
          (delta action state * potential state) :=
            Finset.sum_comm
    _ = ∑ state,
        (∑ action, coefficient action * delta action state) *
          potential state := by
            apply Finset.sum_congr rfl
            intro state _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro action _
            ring
    _ = 0 := by simp [hbalance]

/-- Compatibility is equivalent to the absence of a signed dependence whose
prescribed levels fail to balance. -/
theorem exists_potential_iff_no_signed_incompatibility
    [Fintype State] [Fintype Action]
    (delta : Action → State → ℝ) (level : Action → ℝ) :
    (∃ potential : State → ℝ,
      ∀ action, dotProduct (delta action) potential = level action) ↔
    ¬∃ coefficient : Action → ℝ,
      (∀ state, ∑ action, coefficient action * delta action state = 0) ∧
      ∑ action, coefficient action * level action ≠ 0 := by
  constructor
  · rintro ⟨potential, hpotential⟩
    rintro ⟨coefficient, hbalance, hlevel⟩
    exact hlevel
      (not_signed_incompatibility_of_potential hpotential hbalance)
  · intro hnoWitness
    rcases exists_potential_or_signed_incompatibility delta level with
      hpotential | hwitness
    · exact hpotential
    · exact False.elim (hnoWitness hwitness)

/-- The smallest compatibility failure: on one state, the zero drift cannot
attain a nonzero prescribed level. The coefficient `1` is already a signed
incompatibility witness. -/
theorem singleton_zeroDrift_oneLevel_incompatible :
    (¬∃ potential : Unit → ℝ,
      dotProduct (fun _ : Unit => (0 : ℝ)) potential = 1) ∧
    (∃ coefficient : Unit → ℝ,
      (∀ _state : Unit,
        ∑ action, coefficient action *
          (fun _ : Unit => (0 : ℝ)) action = 0) ∧
      ∑ action, coefficient action * (1 : ℝ) ≠ 0) := by
  constructor
  · rintro ⟨potential, hpotential⟩
    simp at hpotential
  · refine ⟨fun _ => 1, ?_, ?_⟩
    · intro _state
      simp
    · simp

end Math
