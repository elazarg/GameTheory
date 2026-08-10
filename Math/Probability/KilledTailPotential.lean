/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.SurvivalProduct

/-!
# Scalar potentials for killed time-inhomogeneous tails

This file isolates the finite algebra behind a scalar potential transported
through a time-inhomogeneous survival process.  If

```
potential t = source t + seam t + survival t * potential (t + 1),
```

then every finite fold has three terms:

* the killed sum of `source`;
* the killed sum of `seam`;
* the surviving terminal boundary value.

The boundary term is retained explicitly.  In particular, finite seam
summability does not by itself remove a positive harmonic or "phantom"
boundary at infinity.

For an excessive potential, the canonical seam is its one-step
`killedDissipation`.  The final results state the additional boundary
hypothesis needed to force that seam to vanish: the surviving boundary must
already exhaust the part of the initial potential not used by the source.
Equivalently, against an exact reference account with the same source and
initial value, the excessive account's boundary must dominate the reference
boundary.  Without such a boundary comparison, strict dissipation is fully
compatible with finite killed-source accounting.

All statements are deterministic real algebra.  They do not construct a
stochastic process, identify a game-theoretic packet with an occupation law,
or justify a boundary comparison between two independently constructed
accounts.
-/

namespace Math
namespace Probability

/-! ## Survival weights, killed sources, and boundary remainders -/

/-- Survival from `start` through the first `offset` stages. -/
def killedPrefixWeight
    (survival : ℕ → ℝ) (start offset : ℕ) : ℝ :=
  survivalProduct survival start offset

@[simp] theorem killedPrefixWeight_zero
    (survival : ℕ → ℝ) (start : ℕ) :
    killedPrefixWeight survival start 0 = 1 := by
  simp [killedPrefixWeight]

theorem killedPrefixWeight_succ
    (survival : ℕ → ℝ) (start offset : ℕ) :
    killedPrefixWeight survival start (offset + 1) =
      killedPrefixWeight survival start offset *
        survival (start + offset) := by
  exact survivalProduct_succ survival start offset

theorem killedPrefixWeight_nonneg
    (survival : ℕ → ℝ) (hsurvival : ∀ time, 0 ≤ survival time)
    (start offset : ℕ) :
    0 ≤ killedPrefixWeight survival start offset := by
  exact survivalProduct_nonneg survival hsurvival start offset

/-- Source accumulated before killing over the half-open window
`[start, start + fuel)`. -/
def killedSourceSum
    (survival source : ℕ → ℝ) (start fuel : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range fuel,
    killedPrefixWeight survival start offset * source (start + offset)

@[simp] theorem killedSourceSum_zero
    (survival source : ℕ → ℝ) (start : ℕ) :
    killedSourceSum survival source start 0 = 0 := by
  simp [killedSourceSum]

theorem killedSourceSum_succ
    (survival source : ℕ → ℝ) (start fuel : ℕ) :
    killedSourceSum survival source start (fuel + 1) =
      killedSourceSum survival source start fuel +
        killedPrefixWeight survival start fuel * source (start + fuel) := by
  rw [killedSourceSum, Finset.sum_range_succ]
  rfl

theorem killedSourceSum_add
    (survival source seam : ℕ → ℝ) (start fuel : ℕ) :
    killedSourceSum survival (fun time ↦ source time + seam time)
        start fuel =
      killedSourceSum survival source start fuel +
        killedSourceSum survival seam start fuel := by
  simp only [killedSourceSum, mul_add, Finset.sum_add_distrib]

theorem killedSourceSum_nonneg
    (survival source : ℕ → ℝ)
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hsource : ∀ time, 0 ≤ source time)
    (start fuel : ℕ) :
    0 ≤ killedSourceSum survival source start fuel := by
  unfold killedSourceSum
  exact Finset.sum_nonneg fun offset _ ↦
    mul_nonneg
      (killedPrefixWeight_nonneg survival hsurvival start offset)
      (hsource (start + offset))

/-- The terminal potential that survives a finite killed window.  Keeping
this term visible is essential when the infinite survival product may be
positive. -/
def killedBoundaryRemainder
    (survival potential : ℕ → ℝ) (start fuel : ℕ) : ℝ :=
  killedPrefixWeight survival start fuel * potential (start + fuel)

@[simp] theorem killedBoundaryRemainder_zero
    (survival potential : ℕ → ℝ) (start : ℕ) :
    killedBoundaryRemainder survival potential start 0 = potential start := by
  simp [killedBoundaryRemainder]

theorem killedBoundaryRemainder_succ
    (survival potential : ℕ → ℝ) (start fuel : ℕ) :
    killedBoundaryRemainder survival potential start (fuel + 1) =
      killedPrefixWeight survival start fuel *
        survival (start + fuel) * potential (start + fuel + 1) := by
  simp [killedBoundaryRemainder, killedPrefixWeight_succ, Nat.add_assoc]

theorem killedBoundaryRemainder_nonneg
    (survival potential : ℕ → ℝ)
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hpotential : ∀ time, 0 ≤ potential time)
    (start fuel : ℕ) :
    0 ≤ killedBoundaryRemainder survival potential start fuel :=
  mul_nonneg
    (killedPrefixWeight_nonneg survival hsurvival start fuel)
    (hpotential (start + fuel))

/-- Source utilization plus the surviving boundary value. -/
def killedTailAccount
    (survival source potential : ℕ → ℝ)
    (start fuel : ℕ) : ℝ :=
  killedSourceSum survival source start fuel +
    killedBoundaryRemainder survival potential start fuel

/-! ## Finite folding -/

/-- Exact finite folding of a killed scalar recursion. -/
theorem potential_eq_killedTailAccount
    (survival source potential : ℕ → ℝ)
    (hstep : ∀ time,
      potential time =
        source time + survival time * potential (time + 1))
    (start fuel : ℕ) :
    potential start =
      killedTailAccount survival source potential start fuel := by
  induction fuel with
  | zero => simp [killedTailAccount]
  | succ fuel ih =>
      calc
        potential start =
            killedTailAccount survival source potential start fuel := ih
        _ = killedSourceSum survival source start fuel +
            killedPrefixWeight survival start fuel *
              potential (start + fuel) := rfl
        _ = killedSourceSum survival source start fuel +
            killedPrefixWeight survival start fuel *
              (source (start + fuel) +
                survival (start + fuel) *
                  potential (start + fuel + 1)) := by
              rw [hstep (start + fuel)]
        _ = killedSourceSum survival source start (fuel + 1) +
            killedBoundaryRemainder survival potential start (fuel + 1) := by
              rw [killedSourceSum_succ, killedBoundaryRemainder_succ]
              ring
        _ = killedTailAccount survival source potential
            start (fuel + 1) := rfl

/-- Exact source/seam/boundary decomposition.  Both source and seam are raw
killed charges; neither is normalized by the absorption clock. -/
theorem potential_eq_killedSource_add_seam_add_boundary
    (survival source seam potential : ℕ → ℝ)
    (hstep : ∀ time,
      potential time = source time + seam time +
        survival time * potential (time + 1))
    (start fuel : ℕ) :
    potential start =
      killedSourceSum survival source start fuel +
        killedSourceSum survival seam start fuel +
          killedBoundaryRemainder survival potential start fuel := by
  have hfold := potential_eq_killedTailAccount
    survival (fun time ↦ source time + seam time) potential
    (fun time ↦ by
      rw [hstep time])
    start fuel
  rw [killedTailAccount, killedSourceSum_add] at hfold
  linarith

/-! ## Excessive potentials and their canonical seam -/

/-- A potential is excessive for a killed source when it dominates one
source payment followed by its surviving continuation value. -/
def IsKilledExcessive
    (survival source potential : ℕ → ℝ) : Prop :=
  ∀ time,
    source time + survival time * potential (time + 1) ≤ potential time

/-- The canonical nonnegative seam of an excessive potential. -/
def killedDissipation
    (survival source potential : ℕ → ℝ) (time : ℕ) : ℝ :=
  potential time - source time -
    survival time * potential (time + 1)

theorem isKilledExcessive_iff_dissipation_nonneg
    (survival source potential : ℕ → ℝ) :
    IsKilledExcessive survival source potential ↔
      ∀ time, 0 ≤ killedDissipation survival source potential time := by
  constructor
  · intro hexcessive time
    unfold killedDissipation
    linarith [hexcessive time]
  · intro hdissipation time
    unfold killedDissipation at hdissipation
    linarith [hdissipation time]

/-- Every potential has an exact recursion after its one-step slack is named
as `killedDissipation`. -/
theorem potential_eq_source_add_dissipation_add_survival
    (survival source potential : ℕ → ℝ) (time : ℕ) :
    potential time =
      source time + killedDissipation survival source potential time +
        survival time * potential (time + 1) := by
  unfold killedDissipation
  ring

/-- Exact accounting of an excessive potential's source, dissipation seam,
and terminal boundary.  Excessivity is not needed for the equality; it only
supplies the seam's sign. -/
theorem potential_eq_source_add_dissipationSum_add_boundary
    (survival source potential : ℕ → ℝ)
    (start fuel : ℕ) :
    potential start =
      killedSourceSum survival source start fuel +
        killedSourceSum survival
          (killedDissipation survival source potential) start fuel +
          killedBoundaryRemainder survival potential start fuel := by
  exact potential_eq_killedSource_add_seam_add_boundary
    survival source (killedDissipation survival source potential) potential
    (potential_eq_source_add_dissipation_add_survival
      survival source potential)
    start fuel

/-- Finite excessive-potential inequality.  The boundary remainder cannot be
dropped without an independent hypothesis controlling it. -/
theorem killedTailAccount_le_of_excessive
    (survival source potential : ℕ → ℝ)
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hexcessive : IsKilledExcessive survival source potential)
    (start fuel : ℕ) :
    killedTailAccount survival source potential start fuel ≤
      potential start := by
  have hdissipation : ∀ time,
      0 ≤ killedDissipation survival source potential time :=
    (isKilledExcessive_iff_dissipation_nonneg
      survival source potential).mp hexcessive
  have hsum : 0 ≤
      killedSourceSum survival
        (killedDissipation survival source potential) start fuel :=
    killedSourceSum_nonneg survival
      (killedDissipation survival source potential)
      hsurvival hdissipation start fuel
  have haccount :=
    potential_eq_source_add_dissipationSum_add_boundary
      survival source potential start fuel
  unfold killedTailAccount
  linarith

/-- The utilization shortfall of the source-only account is exactly the
killed dissipation seam. -/
theorem killedDissipationSum_eq_initial_sub_source_sub_boundary
    (survival source potential : ℕ → ℝ)
    (start fuel : ℕ) :
    killedSourceSum survival
        (killedDissipation survival source potential) start fuel =
      potential start - killedSourceSum survival source start fuel -
        killedBoundaryRemainder survival potential start fuel := by
  have haccount :=
    potential_eq_source_add_dissipationSum_add_boundary
      survival source potential start fuel
  linarith

/-! ## The missing boundary hypothesis -/

/-- The surviving boundary already exhausts every unit of initial potential
not used by the named source.  For an excessive account, the reverse
inequality follows from finite folding, so this premise is exactly what rules
out a positive dissipation seam over the selected window. -/
def BoundaryExhaustsSourceResidual
    (survival source potential : ℕ → ℝ)
    (start fuel : ℕ) : Prop :=
  potential start - killedSourceSum survival source start fuel ≤
    killedBoundaryRemainder survival potential start fuel

/-- Boundary exhaustion forces the total killed dissipation to vanish. -/
theorem killedDissipationSum_eq_zero_of_boundaryExhausts
    (survival source potential : ℕ → ℝ)
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hexcessive : IsKilledExcessive survival source potential)
    (start fuel : ℕ)
    (hboundary : BoundaryExhaustsSourceResidual
      survival source potential start fuel) :
    killedSourceSum survival
        (killedDissipation survival source potential) start fuel = 0 := by
  have hdissipation : ∀ time,
      0 ≤ killedDissipation survival source potential time :=
    (isKilledExcessive_iff_dissipation_nonneg
      survival source potential).mp hexcessive
  have hnonneg : 0 ≤
      killedSourceSum survival
        (killedDissipation survival source potential) start fuel :=
    killedSourceSum_nonneg survival
      (killedDissipation survival source potential)
      hsurvival hdissipation start fuel
  have hidentity :=
    killedDissipationSum_eq_initial_sub_source_sub_boundary
      survival source potential start fuel
  unfold BoundaryExhaustsSourceResidual at hboundary
  apply le_antisymm
  · linarith
  · exact hnonneg

/-- On a positively surviving stage, boundary exhaustion forces the local
excessive inequality to be an equality. -/
theorem killedDissipation_eq_zero_of_boundaryExhausts
    (survival source potential : ℕ → ℝ)
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hexcessive : IsKilledExcessive survival source potential)
    (start fuel offset : ℕ)
    (hoffset : offset ∈ Finset.range fuel)
    (hweight : 0 < killedPrefixWeight survival start offset)
    (hboundary : BoundaryExhaustsSourceResidual
      survival source potential start fuel) :
    killedDissipation survival source potential (start + offset) = 0 := by
  have hdissipation : ∀ time,
      0 ≤ killedDissipation survival source potential time :=
    (isKilledExcessive_iff_dissipation_nonneg
      survival source potential).mp hexcessive
  have hsum := killedDissipationSum_eq_zero_of_boundaryExhausts
    survival source potential hsurvival hexcessive start fuel hboundary
  have hterm :
      killedPrefixWeight survival start offset *
          killedDissipation survival source potential (start + offset) = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (fun other _ ↦
        mul_nonneg
          (killedPrefixWeight_nonneg
            survival hsurvival start other)
          (hdissipation (start + other)))).mp
        (by simpa [killedSourceSum] using hsum)
    exact hoffset
  exact (mul_eq_zero.mp hterm).resolve_left hweight.ne'

/-- A strict local dissipation at positive prefix weight forces a strict
boundary shortfall.  This is the finite obstruction to identifying an
excessive packet ledger with a source-only debt ledger. -/
theorem boundary_lt_sourceResidual_of_strictDissipation
    (survival source potential : ℕ → ℝ)
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hexcessive : IsKilledExcessive survival source potential)
    (start fuel offset : ℕ)
    (hoffset : offset ∈ Finset.range fuel)
    (hweight : 0 < killedPrefixWeight survival start offset)
    (hstrict :
      source (start + offset) +
          survival (start + offset) * potential (start + offset + 1) <
        potential (start + offset)) :
    killedBoundaryRemainder survival potential start fuel <
      potential start - killedSourceSum survival source start fuel := by
  have hdissipation : ∀ time,
      0 ≤ killedDissipation survival source potential time :=
    (isKilledExcessive_iff_dissipation_nonneg
      survival source potential).mp hexcessive
  have hlocal : 0 <
      killedDissipation survival source potential (start + offset) := by
    unfold killedDissipation
    linarith
  have hsumpos : 0 <
      killedSourceSum survival
        (killedDissipation survival source potential) start fuel := by
    unfold killedSourceSum
    apply Finset.sum_pos'
    · intro other _
      exact mul_nonneg
        (killedPrefixWeight_nonneg survival hsurvival start other)
        (hdissipation (start + other))
    · exact ⟨offset, hoffset, mul_pos hweight hlocal⟩
  have hidentity :=
    killedDissipationSum_eq_initial_sub_source_sub_boundary
      survival source potential start fuel
  linarith

/-- Consequently, boundary exhaustion and strict positive-weight
dissipation are incompatible.  The contradiction requires the displayed
boundary premise; excessive folding alone does not provide it. -/
theorem not_strictDissipation_of_boundaryExhausts
    (survival source potential : ℕ → ℝ)
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hexcessive : IsKilledExcessive survival source potential)
    (start fuel offset : ℕ)
    (hoffset : offset ∈ Finset.range fuel)
    (hweight : 0 < killedPrefixWeight survival start offset)
    (hboundary : BoundaryExhaustsSourceResidual
      survival source potential start fuel) :
    ¬ (source (start + offset) +
          survival (start + offset) * potential (start + offset + 1) <
        potential (start + offset)) := by
  intro hstrict
  have hshortfall := boundary_lt_sourceResidual_of_strictDissipation
    survival source potential hsurvival hexcessive start fuel offset
    hoffset hweight hstrict
  exact (not_lt_of_ge hboundary) hshortfall

/-! ## Comparison with an exact reference account -/

/-- A useful sufficient form of boundary exhaustion.  If an exact reference
account has the same source and initial value, and the excessive account's
surviving boundary dominates the reference boundary, then the excessive
account has no killed dissipation over that window.

The boundary dominance premise is deliberately explicit: proving it is the
model-specific seam-utilization obligation, not a consequence of scalar
killed-potential algebra. -/
theorem killedDissipationSum_eq_zero_of_referenceBoundary_le
    (survival source potential reference : ℕ → ℝ)
    (hsurvival : ∀ time, 0 ≤ survival time)
    (hexcessive : IsKilledExcessive survival source potential)
    (href : ∀ time,
      reference time =
        source time + survival time * reference (time + 1))
    (start fuel : ℕ)
    (hinitial : potential start = reference start)
    (hboundary :
      killedBoundaryRemainder survival reference start fuel ≤
        killedBoundaryRemainder survival potential start fuel) :
    killedSourceSum survival
        (killedDissipation survival source potential) start fuel = 0 := by
  apply killedDissipationSum_eq_zero_of_boundaryExhausts
    survival source potential hsurvival hexcessive start fuel
  unfold BoundaryExhaustsSourceResidual
  have hrefFold :=
    potential_eq_killedTailAccount
      survival source reference href start fuel
  unfold killedTailAccount at hrefFold
  linarith

end Probability
end Math
