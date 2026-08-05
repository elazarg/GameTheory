/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Real.Sqrt

/-!
# Square-root rates for accuracy-indexed periodic meshes

This file isolates the scalar optimization used after a periodic quitting-game
mesh has been compiled.  If terminal exploitability costs `A / m` and the
finite-horizon boundary costs `B * m / N`, then any mesh scale between
`sqrt N` and `2 * sqrt N` has error at most `(A + 2 * B) / sqrt N`.

The statement deliberately receives the mesh scale as data.  Choosing a new
scale for each horizon gives an anytime family; it is not the assertion that
one fixed profile works at every horizon.
-/

namespace Math

/-- The scalar square-root optimization behind accuracy-indexed periodic
meshes.  The hypotheses on `m` are satisfied by `ceil (sqrt N)` when
`1 ≤ N`. -/
theorem inv_add_linear_le_sqrt_rate
    {A B N m : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 1 ≤ N)
    (hm_lower : Real.sqrt N ≤ m)
    (hm_upper : m ≤ 2 * Real.sqrt N) :
    A / m + B * m / N ≤ (A + 2 * B) / Real.sqrt N := by
  have hN_pos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hN_nonneg : 0 ≤ N := hN_pos.le
  have hsqrt_pos : 0 < Real.sqrt N := Real.sqrt_pos.2 hN_pos
  have hsqrt_nonneg : 0 ≤ Real.sqrt N := hsqrt_pos.le
  have hm_pos : 0 < m := lt_of_lt_of_le hsqrt_pos hm_lower
  have h_inv : A / m ≤ A / Real.sqrt N := by
    rw [div_le_div_iff₀ hm_pos hsqrt_pos]
    exact mul_le_mul_of_nonneg_left hm_lower hA
  have h_scale : m / N ≤ 2 / Real.sqrt N := by
    rw [div_le_div_iff₀ hN_pos hsqrt_pos]
    have hmul := mul_le_mul_of_nonneg_right hm_upper hsqrt_nonneg
    nlinarith [Real.sq_sqrt hN_nonneg]
  have h_linear : B * m / N ≤ 2 * B / Real.sqrt N := by
    have hmul := mul_le_mul_of_nonneg_left h_scale hB
    calc
      B * m / N = B * (m / N) := by ring
      _ ≤ B * (2 / Real.sqrt N) := hmul
      _ = 2 * B / Real.sqrt N := by ring
  calc
    A / m + B * m / N
        ≤ A / Real.sqrt N + 2 * B / Real.sqrt N :=
          add_le_add h_inv h_linear
    _ = (A + 2 * B) / Real.sqrt N := by ring

/-- Consumer form: separate terminal and boundary estimates may be added
before applying the square-root optimization. -/
theorem periodicMeshGap_le_sqrt_rate
    {terminalError boundaryError A B N m : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 1 ≤ N)
    (hm_lower : Real.sqrt N ≤ m)
    (hm_upper : m ≤ 2 * Real.sqrt N)
    (hterminal : terminalError ≤ A / m)
    (hboundary : boundaryError ≤ B * m / N) :
    terminalError + boundaryError ≤ (A + 2 * B) / Real.sqrt N := by
  calc
    terminalError + boundaryError ≤ A / m + B * m / N :=
      add_le_add hterminal hboundary
    _ ≤ (A + 2 * B) / Real.sqrt N :=
      inv_add_linear_le_sqrt_rate hA hB hN hm_lower hm_upper

end Math
