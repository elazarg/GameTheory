/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.SingletonFaceCirculationOrbit

/-!
# The repaired four-player family's circulation certificate at its stress point

This followup repairs the four-player
cyclic weight `F(x, ε)` to `F'(x, λ)` by moving the second solo coordinate from
`0` to `x` (`solo r({i})`: `i ↦ 1, i+1 ↦ 3, i+2 ↦ x, i+3 ↦ 0`).  The followup's
answer ("## Answer to followup") produces a singleton-face circulation
certificate for every `x > 0, λ ≥ 0` (§4) and names
`(x, λ) = (2, 1)` as "the hardest stress test for the remaining exact-cycle
classification" (§7): it lies off every bounded-period exact branch the answer
proves (`x > 1` rules out the opposite-player branch, `λ ≤ 2` rules out the
symmetric branch, `x ≠ 1` and `λ > 0` rule out the singleton lock).

This file machine-checks the answer's §4 certificate data at exactly that
point, and instantiates the singleton-orbit theorem of
`SingletonFaceCirculationOrbit.lean` on it.

## The transcribed data

At `x = 2`, `λ = 1`:

* `a = a(2) = 1/2`, from the followup's `a(x) = (1 - x + √((x-1)² + 8)) / 4`
  (equation (1)); the answer records this value directly in §7.
* the payoff `v(2) = (1, 2, 2, 1)` (§7), which is `V^0` of §4's equation (39)
  `V^0 = (1, 3 - 2a, 1/a, 1)` at `a = 1/2`.
* the four singleton payoff rows `R^k`, the rotations of `R^0 = (1, 3, 2, 0)`
  under `ρ(v₀, v₁, v₂, v₃) = (v₃, v₀, v₁, v₂)` (§4): `R^0 = (1,3,2,0)`,
  `R^1 = (0,1,3,2)`, `R^2 = (2,0,1,3)`, `R^3 = (3,2,0,1)`.
* the four cycle vertices `V^k = ρ^k V^0`: `V^0 = (1,2,2,1)`, `V^1 = (1,1,2,2)`,
  `V^2 = (2,1,1,2)`, `V^3 = (2,2,1,1)`, satisfying the answer's boxed identity
  (equation (40)) `V^k = (1 - a) R^k + a V^{k+1}` -- checked below by
  `norm_num` at every `k`, with the exact rationals of §4.1, not a numeric
  approximation.

`FaceCirculationCertificate.step` is stated *forward*
(`vertex (l+1) = ratio l * vertex l + (1 - ratio l) * mixTarget ...`), while
the answer's equation (40) is stated *backward* in its own cyclic index `k`
(matching the "backward orbit convention" the orbit file's docstring already
flags).  The certificate below reads the answer's cycle in reverse,
`vertex l := V^{-l}`, with phase `l`'s owner set to coordinate `V^{-l-1}`'s
label; §4.1's identity `V^k_k = V^{k+1}_k = 1` (equation (43)) is exactly what
makes the owner pinning below hold on the nose.

## The floor

The answer's floor is `max{d_i, χ_i}`, `d_i` the solo diagonal and `χ_i` the
true min-max (`Scope` note of `SingletonFaceCirculation.lean`).  Here
`d_i = stressWeight {i} i = 1` for every `i` (read off the table, no
computation needed), and §2.3/§2.4 compute the exact min-max at the branch
`x ≥ x₊(λ)` (equation (14)): at `(2, 1)`,
`x₊(1) = 1 - 1/((1+1)²(2+1)) = 11/12 ≤ 2`, so `χ(2,1) = q_1 = (1+1)/(2+1) =
2/3` (the boxed equation (14)'s upper branch).  That min-max computation --
the supersolution algebra of §2.2/§2.3 -- is **quoted, not formalized here**,
exactly as `cyclicCirculationFloor`'s docstring already quotes the
three-coordinate min-max for its own calibration instance.  The floor used
below is the constant `1`, which is `d_i` exactly and dominates the quoted
`χ(2,1) = 2/3` with room to spare; `solo_le_floor` is proved unconditionally
from the table, so the only unformalized input is the strict inequality
`χ(2,1) < 1`, needed only for the informal reading "the floor is
`max{d, χ}`" and not for any field of the certificate itself.

## Contents

* `stressWeight`: the repaired family's weight at `(x, λ) = (2, 1)`, all
  sixteen rows.
* `stressFloor`, `stressVertex`, `stressOwner`: the floor and the reversed
  cycle of §4.1.
* `stressCirculation`: the `FaceCirculationCertificate`, with every step
  identity, floor bound, and pinning clause checked by `norm_num`.
* `stressCirculationSupport`: its point-mass presentation.
* `exists_stressCirculation_orbit`: the instantiated singleton-orbit theorem
  -- for every `ε > 0` and target quit mass `Q`, a rational discretization
  whose states obey the one-stage recursion, stay support-perfect at
  tolerance `ε`, stay above the floor forever, and whose quit mass exceeds
  `Q` on a finite prefix.

## What this does and does not give

What is machine-checked: the four singleton payoff rows and the four cycle
vertices exist as stated with exact rational coordinates; the closing
identities `V^k = (1-a) R^k + a V^{k+1}` hold on the nose at `a = 1/2`; the
floor `1` dominates every solo value and every vertex sits above it; the
phase owners are pinned on both the ideal vertex and the phase target; and,
from all of that through `SingletonFaceCirculationOrbit.lean`'s general
machinery, orbits of arbitrarily large prefix quit mass exist at this weight,
support-perfect at any prescribed tolerance, above the floor forever.  All of
this is at the level of `L` (the game's live-state Bellman recursion,
`oneStageNext`), not at the level of a stochastic-game equilibrium payoff.

What is *not* checked here: that `χ(2,1) = 2/3` (quoted above, from §2.3's
supersolution algebra); that the displayed floor is in fact a *rationality*
floor for any strategic notion (that reading is supplied by
`SingletonFaceCirculationOrbit.lean`'s own scope note, inherited unchanged);
and the compiler step from a family of support-perfect orbits at every
tolerance to a genuine uniform equilibrium payoff of the stochastic quitting
game -- that compilation is the standing program's in-flight chain, not
something this file or its imports discharge.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace RepairedFourPlayerStress

open Finset Math.PMFProduct

/-- The four cyclic players. -/
abbrev Player := Fin 4

/-- **The repaired family's weight at the stress point `(x, λ) = (2, 1)`**,
from the followup's repaired family: solo `r({i})` pays
`i ↦ 1, i+1 ↦ 3, i+2 ↦ x, i+3 ↦ 0`; adjacent pairs `r({i,i+1})` pay
`i ↦ 1+λ, i+1 ↦ 0`, both outsiders `↦ 1`; distance-two pairs pay both
outsiders `↦ 1`, both members `↦ 0`; triples pay the outsider `↦ 1`, all
three members `↦ 0`; the full set is the zero vector.  Specialized to
`x = 2`, `λ = 1`. -/
def stressWeight (S : Finset Player) : Player → ℝ :=
  match decide (0 ∈ S), decide (1 ∈ S), decide (2 ∈ S), decide (3 ∈ S) with
  | false, false, false, false => ![0, 0, 0, 0]
  | true, false, false, false => ![1, 3, 2, 0]
  | false, true, false, false => ![0, 1, 3, 2]
  | false, false, true, false => ![2, 0, 1, 3]
  | false, false, false, true => ![3, 2, 0, 1]
  | true, true, false, false => ![2, 0, 1, 1]
  | true, false, true, false => ![0, 1, 0, 1]
  | true, false, false, true => ![0, 1, 1, 2]
  | false, true, true, false => ![1, 2, 0, 1]
  | false, true, false, true => ![1, 0, 1, 0]
  | false, false, true, true => ![1, 1, 2, 0]
  | true, true, true, false => ![0, 0, 0, 1]
  | true, true, false, true => ![0, 0, 1, 0]
  | true, false, true, true => ![0, 1, 0, 0]
  | false, true, true, true => ![1, 0, 0, 0]
  | true, true, true, true => ![0, 0, 0, 0]

/-! ## The four singleton rows -/

theorem stressWeight_zero : stressWeight {0} = ![1, 3, 2, 0] := by
  funext i; fin_cases i <;> simp +decide [stressWeight]

theorem stressWeight_one : stressWeight {1} = ![0, 1, 3, 2] := by
  funext i; fin_cases i <;> simp +decide [stressWeight]

theorem stressWeight_two : stressWeight {2} = ![2, 0, 1, 3] := by
  funext i; fin_cases i <;> simp +decide [stressWeight]

theorem stressWeight_three : stressWeight {3} = ![3, 2, 0, 1] := by
  funext i; fin_cases i <;> simp +decide [stressWeight]

/-- The solo diagonal `d_i` is `1` at every coordinate: read off directly
from the table, not from any min-max computation. -/
theorem stressWeight_diagonal (i : Player) : stressWeight {i} i = 1 := by
  fin_cases i <;>
    simp [stressWeight_zero, stressWeight_one, stressWeight_two, stressWeight_three]

/-- Every entry of the table has absolute value at most `3`. -/
theorem abs_stressWeight_le_three (S : Finset Player) (j : Player) :
    |stressWeight S j| ≤ 3 := by
  by_cases h0 : (0 : Player) ∈ S <;> by_cases h1 : (1 : Player) ∈ S <;>
    by_cases h2 : (2 : Player) ∈ S <;> by_cases h3 : (3 : Player) ∈ S <;>
    fin_cases j <;> simp [stressWeight, h0, h1, h2, h3] <;> norm_num

/-! ## The floor -/

/-- The rationality floor at the stress point: the constant `1`.  It equals
the solo diagonal `d_i` exactly (`stressWeight_diagonal`) and dominates the
quoted min-max `χ(2,1) = 2/3` of §2.3/§2.4 -- see the module docstring for
why that min-max value is quoted rather than reproved here. -/
def stressFloor : Player → ℝ := fun _ => 1

theorem stressWeight_solo_le_floor (j : Player) : stressWeight {j} j ≤ stressFloor j := by
  rw [stressWeight_diagonal, stressFloor]

/-! ## The reversed cycle of §4.1 -/

/-- The four phases of `ZMod 4`. -/
theorem zmod_four_cases (t : ZMod 4) : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by
  revert t; decide

/-- The owner of phase `l`, reading the answer's cycle backwards: phase `l`
is owned by coordinate `3 - l`. -/
def stressOwner (l : ZMod 4) : Player :=
  if l = 0 then 3 else if l = 1 then 2 else if l = 2 then 1 else 0

/-- The ideal cycle of §4, equation (39), at `a = 1/2`: `V^0 = (1,2,2,1)`,
`V^1 = (1,1,2,2)`, `V^2 = (2,1,1,2)`, `V^3 = (2,2,1,1)`, indexed so that
`stressVertex l = V^{-l}` -- the order the certificate's forward step needs,
matching the orbit file's "backward orbit convention" remark. -/
def stressVertex (l : ZMod 4) : Player → ℝ :=
  if l = 0 then ![1, 2, 2, 1]
  else if l = 1 then ![2, 2, 1, 1]
  else if l = 2 then ![2, 1, 1, 2]
  else ![1, 1, 2, 2]

/-- **The four step identities of equation (40)**, `V^k = (1-a) R^k +
a V^{k+1}` at `a = 1/2`, read through the reversed indexing: exact rational
arithmetic, `norm_num` throughout. -/
theorem stressVertex_step (l : ZMod 4) (j : Player) :
    stressVertex (l + 1) j =
      (1 / 2 : ℝ) * stressVertex l j + (1 - 1 / 2) * stressWeight {stressOwner l} j := by
  rcases zmod_four_cases l with rfl | rfl | rfl | rfl <;> fin_cases j <;>
    simp +decide [stressVertex, stressOwner, stressWeight_zero, stressWeight_one,
      stressWeight_two, stressWeight_three] <;> norm_num

/-- **The floor bound of equation (42)**: every vertex of the cycle lies at
or above `1` at every coordinate. -/
theorem stressVertex_ge_floor (l : ZMod 4) (j : Player) :
    stressFloor j ≤ stressVertex l j := by
  rcases zmod_four_cases l with rfl | rfl | rfl | rfl <;> fin_cases j <;>
    simp +decide [stressVertex, stressFloor]

/-- **The owner pinning of equation (43)**, `V^k_k = V^{k+1}_k = 1`: each
phase's owner sits at its own solo value on the ideal vertex. -/
theorem stressVertex_owner_pinned (l : ZMod 4) :
    stressVertex l (stressOwner l) = stressWeight {stressOwner l} (stressOwner l) := by
  rw [stressWeight_diagonal]
  rcases zmod_four_cases l with rfl | rfl | rfl | rfl <;>
    simp +decide [stressVertex, stressOwner]

/-! ## The certificate -/

/-- **The stress-point circulation certificate**: the answer's §4 cycle
`V^0 → V^3 → V^2 → V^1 → V^0`, with point-mass phase distributions, owners
`3, 2, 1, 0`, and every contraction ratio `a = 1/2`. -/
def stressCirculation :
    FaceCirculationCertificate stressWeight stressFloor 4 where
  vertex := stressVertex
  mixWeight := fun l k => if k = stressOwner l then 1 else 0
  ratio := fun _ => 1 / 2
  mixWeight_nonneg := by
    intro l j
    split <;> norm_num
  mixWeight_sum := by
    intro l
    simp
  ratio_pos := by intro l; norm_num
  ratio_lt_one := by intro l; norm_num
  step := by
    intro l j
    simp only [mixTarget_single]
    exact stressVertex_step l j
  vertex_ge_floor := stressVertex_ge_floor
  vertex_pinned := by
    intro l j hj
    have hjl : j = stressOwner l := by by_contra hcon; simp [hcon] at hj
    subst hjl
    exact stressVertex_owner_pinned l
  target_pinned := by
    intro l j hj
    have hjl : j = stressOwner l := by by_contra hcon; simp [hcon] at hj
    subst hjl
    rw [mixTarget_single]
  solo_le_floor := stressWeight_solo_le_floor

/-- The stress-point certificate, presented with its point-mass supports. -/
def stressCirculationSupport : SingletonSupport stressCirculation where
  owner := stressOwner
  mixWeight_eq := fun _ => rfl

/-! ## The instantiated orbit theorem -/

/-- **Orbits of arbitrarily large quit mass at the stress point `(2, 1)`.**
For every tolerance `ε > 0` and every target quit mass `Q` there is a
discretisation of the stress-point certificate whose every microstep row is
support-perfect at tolerance `ε` against its own state, whose every state
stays at or above the floor `1`, whose states obey the one-stage Bellman
recursion `oneStageNext`, and a finite prefix of which has quit mass at least
`Q`.  See the module docstring for exactly what this does and does not give:
this is a machine-checked orbit of the live-state recursion `L`, not (yet) a
uniform equilibrium payoff of the stochastic quitting game. -/
theorem exists_stressCirculation_orbit (ε : ℝ) (hε : 0 < ε) (Q : ℝ) :
    ∃ (N : ℕ) (β : ZMod 4 → ℝ), 0 < N ∧
      (∀ n j, circulationState stressCirculationSupport β N (n + 1) j =
        oneStageNext stressWeight (circulationRow stressCirculationSupport β N n)
          (circulationState stressCirculationSupport β N n) j) ∧
      (∀ n, IsSupportPerfectRow stressWeight
        (circulationRow stressCirculationSupport β N n)
        (circulationState stressCirculationSupport β N n) ε) ∧
      (∀ n j, stressFloor j ≤
        circulationState stressCirculationSupport β N n j) ∧
      ∃ T : ℕ, Q ≤ ∑ n ∈ Finset.range T,
        (1 - continueMass (circulationRow stressCirculationSupport β N n)) := by
  obtain ⟨N, b, hN, hb0, hb1, hbN, hbH⟩ :=
    exists_pow_eq_and_one_sub_le (1 / 2) (by norm_num) (by norm_num) (ε / 6) (by linarith)
  have hratio : ∀ l : ZMod 4, (fun _ : ZMod 4 => b) l ^ N = stressCirculation.ratio l :=
    fun _ => hbN
  have hb1' : ∀ l : ZMod 4, (fun _ : ZMod 4 => b) l ≤ 1 := fun _ => hb1.le
  have hb0' : ∀ l : ZMod 4, 0 ≤ (fun _ : ZMod 4 => b) l := fun _ => hb0
  refine ⟨N, fun _ => b, hN, ?_, ?_, ?_, ?_⟩
  · exact fun n j => circulationState_succ stressCirculationSupport _ N hN hratio n j
  · exact fun n => isSupportPerfectRow_circulation stressCirculationSupport _ N hN hb0' hb1'
      hratio 3 (by norm_num) abs_stressWeight_le_three ε (fun _ => by linarith) n
  · exact fun n j => circulationState_ge_floor stressCirculationSupport _ N hN hb0' hb1'
      hratio n j
  · exact exists_prefix_quitMass_ge stressCirculationSupport _ N b (fun _ => le_rfl) hb1 Q

end RepairedFourPlayerStress
end GameTheory
