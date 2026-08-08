/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Circulation.TwoCoordinateBoundary
import UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationOrbit

/-!
# The circulation boundary re-measured at a `χ` floor with collision deterrence

`QuittingCirculationTwoCoordinateBoundary.lean` measured the `L = 1`
face-circulation class at `ι = Bool` and found all four branches of the
two-player capstone (`QuittingTwoPlayerExistence.lean`) outside it.  That
measurement was taken at the certificate's own floor, `max{d, χ}`, whose
achievable range bottoms out at the solo value `d`; the class collapsed to
`v1 true ≤ v0 true ∨ v0 false ≤ v1 false`.  This file re-runs the boundary
after replacing the floor-at-solo by the bare min-max level `χ` — which may
sit strictly *below* `d` — and paying for the difference with an explicit
deterrence clause.

## What "multi-owner" does and does not buy

`MultiOwnerFaceCirculationOrbit.lean` lets a phase mixture `λ^ℓ` have
arbitrary support and realises it by a balanced owner word.  It does **not**
make two players active at the same microstep: `multiRow` is
`singletonRow (1 - β_ℓ) (word ℓ t)`, so exactly one coordinate carries quit
probability at every stage of the chain.  The only collision a deviating
coordinate `k` ever faces is the *active owner's own hazard* `h`, through the
`h * (r{k,i}_k - r{i}_k)` summand of `gainValue_singletonRow_of_ne`.
Multi-owner support therefore contributes no collision mass beyond what a
singleton phase already has; what does contribute is a hazard `h` that is
**not driven to zero**.

`subSolo_forces_hazard` makes this exact: if the state sits `δ` below solo at
some inactive coordinate and the microstep row is support-perfect at
tolerance `ε`, then `δ ≤ ε + h (δ + 2M)`.  Contrapositively
(`subSolo_gap_le_of_hazard_le`), a hazard budget `h ≤ H` caps the sub-solo
gap by `(1 - H) δ ≤ ε + 2 M H`.  The inherited orbit theorem
`exists_multiCirculation_orbit` chooses `H = ε / D` and lets `ε → 0`, so
inside that theorem's interface the floor is *forced* back to solo.  That
settles the floor-interface question: the orbit theorem's `solo_le_floor`
clause cannot be generalised while its hazard budget stands, so the variant's
orbit production is stated separately below
(`exists_exact_orbit_of_collisionFacedTwoFeasible`) — and it is *stronger*,
not weaker: it is exact (`ε = 0`), needs no reward bound `M`, and needs no
hazard budget at all.  The one-stage generalisation that makes this possible,
`isSupportPerfectRow_singletonRow_of_deterrence`, replaces
`isSupportPerfectRow_singletonRow`'s `∀ k, r{k}_k ≤ rest_k` by the deterrence
inequality, over an arbitrary finite index type.

## The variant class at two coordinates

`CollisionFacedTwoFeasible v0 v1 c χ` asks for a distribution `λ` on `Bool`,
a hazard `h ∈ (0,1]`, pinning of every support coordinate, `χ ≤ u` (not
`max{d,χ} ≤ u`), and, at every support owner `i` and every `k ≠ i`, the
deterrence inequality `(1-h)(d_k - u_k) + h(c_k - r{i}_k) ≤ 0`.
`collisionFacedTwoFeasible_iff` closes it, exactly as before the mixed
disjunct degenerates, into

  `(χ ≤ v0 ∧ ∃ h ∈ (0,1], (1-h) v1_true + h c_true ≤ v0_true) ∨ (mirror)`.

The second conjunct of the first disjunct is *verbatim* the `hrate`
hypothesis of `quittingGame_isUniformEquilibriumPayoff_soloRate`; the
original class's `v1 true ≤ v0 true` is its `h = 0` degeneration.  That one
change is what moves the boundary.

## The min-max parameter, and why it is not free

`χ` is a parameter, but not an unconstrained one: `IsStationaryPunishmentCap`
records that `χ_i` is below `i`'s optimal-stopping value against *every*
constant opponent quit rate `y`.  At `n = 2` that value is
`max{(1-y) d_i + y c_i, r{k}_i}` for `y > 0` and `max{d_i, 0}` for `y = 0`
(the `y = 0` clause is the `χ_i ≤ max 0 (d_i)` bound the previous file
quoted).  Since the min-max level is a minimum over opponent behaviour, it is
below the value against any fixed `y`, so the cap is sound in the direction
the certificate consumes; the min-max itself is still not formalized, exactly
as in `SingletonFaceCirculation.lean`'s scope note.  The cap is satisfiable
(`isStationaryPunishmentCap_min`), so no theorem below is vacuous, and it is
*not* trivially satisfied by the certificate's own needs: it is what forces
the covering witnesses' hazards to be the branch's own rates.

## The four per-branch verdicts

* **Solo-rate: covered** (`soloRate_collisionFacedTwoFeasible`).  Its `hrate`
  at rate `p` *is* the deterrence clause at hazard `p`; `0 ≤ d_owner` gives
  `χ_owner ≤ d_owner` from the `y = 0` cap, and `hrate` itself collapses the
  blocker's stationary punishment value at `y = p` to the blocker's cross
  payoff.
* **Pair repair: covered** (`pairRepair_collisionFacedTwoFeasible`).  The
  decisive branch.  Taking the *blocker* as the certificate's owner and
  hazard `h = 1`, the branch's `howner` (`c_owner ≤ r{blocker}_owner`) is the
  deterrence clause, and also collapses the owner's punishment value at
  `y = 1`; the blocker's floor clause follows from `hblocker`
  (`r{owner}_blocker ≤ d_blocker`) by letting the punishing rate tend to `0`.
  The weight the previous file exhibited outside the class,
  `pairRepairWitness`, is inside the variant for every capped `χ`
  (`pairRepairWitness_inside_chiFloor`), while still outside
  `CirculationTwoExists`.
* **Zero solo: persists outside** (`zeroSolo_persists_outside_chiFloor`).
* **Joint exit: persists outside** (`jointExit_persists_outside_chiFloor`).

Both changes carry weight, and neither alone suffices.  At each covered
witness the *best* floor-at-solo still fails (both crossing theorems also
conclude `¬ CirculationTwoExists`), so the floor had to drop below `d`; and
each covered witness needs a strictly positive hazard, so freeing `h` was
equally necessary.  The floor clause is likewise not decorative: the cap
bounds `χ` above but does not by itself imply `χ ≤ u`, and each covering proof
below has to earn that inequality from the branch's own hypotheses.

Both survivors fail the deterrence clause on both disjuncts *for every* `χ`
and every hazard, so no floor relaxation can reach them.  What their
equilibria use is visible in `zeroSoloPayoff_not_soloMixture` and
`jointExitPayoff_not_soloMixture`: their payoffs are not convex combinations
of the solo rows at all — the all-continue payoff `0` and the joint-exit row
`r{0,1}` both lie outside the segment `[r{0}, r{1}]` that
`mixTarget` can reach.  A circulation certificate's states are pinned convex
combinations of solo rows and its microsteps are singleton rows, so it can
neither name a simultaneous-quit payoff nor produce the zero-quit-mass
all-continue profile.

## The verdict

Half the previous boundary was an artifact of the floor.  The residual
habitat at `n = 2` is not "sub-solo compensation" — pair repair, the branch
that needs genuinely approximate equilibria, is now *inside* the class.  It
is the two mechanisms that leave the solo-row hull: zero quit mass
(all-continue) and simultaneous quitting (joint exit).  Relaxing the floor
cannot reach either, because neither failure is a floor failure; the
obstruction is `mixTarget`'s range together with the singleton shape of
`multiRow`.
-/

noncomputable section

namespace GameTheory

open QuittingTwoPlayerExistence QuittingTwoPlayerPairRepair
open QuittingCirculationTwoCoordinateBoundary Math.PMFProduct

namespace QuittingCirculationChiFloorBoundary

/-! ## The microstep floor interface -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Deterrence replaces the solo floor at a singleton microstep.**  If the
owner is pinned at its solo value and every other coordinate's stop-minus-
continue difference is nonpositive, the singleton row `h e_i` is support-
perfect at tolerance **zero**.

This is the exact generalisation of `isSupportPerfectRow_singletonRow`, whose
hypothesis `∀ k, r{k}_k ≤ rest_k` is the special case where the inactive
coordinate's own gap already does the work.  Here the gap may be positive —
`rest_k` may sit strictly below `r{k}_k` — provided the owner's hazard `h`
buys enough collision penalty `r{k,i}_k - r{i}_k` to cancel it.  No reward
bound `M` is used, and the tolerance is `0` rather than `2 M h`. -/
theorem isSupportPerfectRow_singletonRow_of_deterrence (r : Finset ι → ι → ℝ)
    (h : ℝ) (i : ι) (rest : ι → ℝ) (hpin : rest i = r {i} i)
    (hdet : ∀ k, k ≠ i →
      (1 - h) * (r {k} k - rest k) + h * (r {k, i} k - r {i} k) ≤ 0) :
    IsSupportPerfectRow r (singletonRow h i) rest 0 := by
  intro j
  by_cases hj : j = i
  · subst hj
    rw [gainValue_singletonRow_self, hpin]
    constructor <;> intro _ <;> simp
  · rw [gainValue_singletonRow_of_ne r h hj]
    refine ⟨fun hpos => absurd hpos ?_, fun _ => ?_⟩
    · rw [singletonRow_of_ne h hj]
      exact lt_irrefl 0
    · exact hdet j hj

/-- **A sub-solo state forces a hazard bounded below.**  If the state sits at
least `δ` below its solo value at some coordinate `k` inactive at the
microstep, and the microstep row is support-perfect at tolerance `ε`, then
`δ ≤ ε + h (δ + 2M)`.

The only deterrent available to an inactive coordinate is the owner-quits
event, of probability exactly `h`, on which it loses at most the one-stage
reward swing `2M`.  So a sub-solo gap of size `δ` cannot be sustained at a
hazard below roughly `(δ - ε) / (δ + 2M)`. -/
theorem subSolo_forces_hazard (r : Finset ι → ι → ℝ) (M : ℝ) (hM : ∀ S j, |r S j| ≤ M)
    (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (i k : ι) (hk : k ≠ i) (rest : ι → ℝ)
    (δ ε : ℝ) (hsub : rest k ≤ r {k} k - δ)
    (hrow : IsSupportPerfectRow r (singletonRow h i) rest ε) :
    δ ≤ ε + h * (δ + 2 * M) := by
  have hlt : singletonRow h i k < 1 := by
    rw [singletonRow_of_ne h hk]; linarith
  have hgain := (hrow k).2 hlt
  rw [gainValue_singletonRow_of_ne r h hk] at hgain
  have hswing : -(2 * M) ≤ r {k, i} k - r {i} k := by
    have h1 := abs_le.mp (hM {k, i} k)
    have h2 := abs_le.mp (hM {i} k)
    linarith
  have hA : (1 - h) * δ ≤ (1 - h) * (r {k} k - rest k) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hB : h * -(2 * M) ≤ h * (r {k, i} k - r {i} k) :=
    mul_le_mul_of_nonneg_left hswing hh0
  linarith

/-- **A hazard budget caps the sub-solo gap.**  Combining
`subSolo_forces_hazard` with `h ≤ H` gives `(1 - H) δ ≤ ε + 2 M H`.

`exists_multiCirculation_orbit` produces its orbit with hazard budget
`H = ε / (2M + 2M(s-1)(3-a)/(1-a) + 1)`, which tends to `0` with `ε`.  Inside
that interface, therefore, `δ → 0`: the certificate's floor is pinned back to
the solo value, and the `solo_le_floor` clause is not a removable convenience
but the exact content of the small-hazard regime.  The `χ`-floored variant
below consequently gets its own orbit theorem rather than a weakening of that
one. -/
theorem subSolo_gap_le_of_hazard_le (r : Finset ι → ι → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ S j, |r S j| ≤ M) (h H : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hhH : h ≤ H)
    (i k : ι) (hk : k ≠ i) (rest : ι → ℝ) (δ ε : ℝ) (hδ0 : 0 ≤ δ)
    (hsub : rest k ≤ r {k} k - δ)
    (hrow : IsSupportPerfectRow r (singletonRow h i) rest ε) :
    (1 - H) * δ ≤ ε + 2 * M * H := by
  have hmain := subSolo_forces_hazard r M hM h hh0 hh1 i k hk rest δ ε hsub hrow
  nlinarith [mul_le_mul_of_nonneg_right hhH hδ0,
    mul_le_mul_of_nonneg_left hhH (by linarith : (0 : ℝ) ≤ 2 * M)]

/-! ## The min-max parameter, as a stationary punishment cap -/

/-- **The stationary stopping value at two coordinates.**  Against an opponent
who quits at the constant rate `y ∈ (0,1]`, a player whose solo value is
`solo`, whose collision value is `coll` and whose cross payoff (the opponent's
solo row, read at the player's own coordinate) is `cross`, has optimal
stopping value `max ((1-y) solo + y coll) cross`: quit now for the first
argument, or wait for the opponent's exit, which arrives almost surely.  At
`y = 0` the value is `max solo 0` instead, since waiting forever pays `0`. -/
def stationaryPunishValue (solo coll cross y : ℝ) : ℝ :=
  max ((1 - y) * solo + y * coll) cross

/-- **The min-max parameter is capped by every stationary punishment.**  The
min-max level is a minimum over the opponent's behaviour, so it lies below the
value against each fixed constant rate `y`, and below the `y = 0` value
`max 0 d` — the bound the previous file quoted as `χ_i ≤ max 0 (d_i)`.  This
is the only thing the theorems below assume about `χ`; the min-max level
itself is not formalized. -/
def IsStationaryPunishmentCap (v0 v1 c chi : Bool → ℝ) : Prop :=
  chi false ≤ max 0 (v0 false) ∧ chi true ≤ max 0 (v1 true) ∧
    (∀ y : ℝ, 0 < y → y ≤ 1 →
      chi false ≤ stationaryPunishValue (v0 false) (c false) (v1 false) y) ∧
    (∀ y : ℝ, 0 < y → y ≤ 1 →
      chi true ≤ stationaryPunishValue (v1 true) (c true) (v0 true) y)

/-- **The cap is satisfiable at every weight**, so no theorem conditioned on
it is vacuous: the coordinatewise minimum of `0`, both solo rows and the
collision row is below every stationary punishment value, each of which is a
`max` of a convex combination of two of those numbers with a third. -/
theorem isStationaryPunishmentCap_min (v0 v1 c : Bool → ℝ) :
    IsStationaryPunishmentCap v0 v1 c
      (fun j => min (min 0 (min (v0 j) (v1 j))) (c j)) := by
  have hkey : ∀ (a b cc y : ℝ), 0 ≤ y → y ≤ 1 →
      min (min a b) cc ≤ (1 - y) * a + y * b := by
    intro a b cc y hy0 hy1
    have h1 : min (min a b) cc ≤ a := le_trans (min_le_left _ _) (min_le_left _ _)
    have h2 : min (min a b) cc ≤ b := le_trans (min_le_left _ _) (min_le_right _ _)
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_max_left _ _))
  · exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (le_max_left _ _))
  · intro y hy0 hy1
    refine le_trans ?_ (le_max_left ((1 - y) * v0 false + y * c false) (v1 false))
    refine le_trans ?_ (hkey (v0 false) (c false) 0 y hy0.le hy1)
    refine le_min (le_min ?_ ?_) ?_ <;>
      simp only [min_le_iff] <;>
      first
        | exact Or.inl (Or.inr (Or.inl le_rfl))
        | exact Or.inr le_rfl
        | exact Or.inl (Or.inl le_rfl)
  · intro y hy0 hy1
    refine le_trans ?_ (le_max_left ((1 - y) * v1 true + y * c true) (v0 true))
    refine le_trans ?_ (hkey (v1 true) (c true) 0 y hy0.le hy1)
    refine le_min (le_min ?_ ?_) ?_ <;>
      simp only [min_le_iff] <;>
      first
        | exact Or.inl (Or.inr (Or.inr le_rfl))
        | exact Or.inr le_rfl
        | exact Or.inl (Or.inl le_rfl)

/-! ## The `χ`-floored, collision-deterred certificate at two coordinates -/

/-- **The variant certificate at `ι = Bool`, `L = 1`.**  As in
`CirculationL1Feasible`, a distribution `λ` on the two players mixes the two
solo rows into `u`, and every coordinate `λ` charges is pinned at its own solo
value.  Two things change.

* The floor clause is `χ ≤ u`, with `χ` the bare min-max level, in place of
  `max{d, χ} ≤ u`.  A coordinate's assigned payoff may now sit strictly below
  its own solo value.
* Each support owner `i` carries a **hazard** `h ∈ (0,1]`, and every `k ≠ i`
  must be deterred at that hazard:
  `(1-h)(d_k - u_k) + h(c_k - r{i}_k) ≤ 0`.  This is exactly
  `gainValue_singletonRow_of_ne`'s value at the state `u`, i.e. the microstep
  row `h e_i` being support-perfect at `k` with tolerance `0`. -/
def CollisionFacedTwoFeasible (v0 v1 c chi : Bool → ℝ) : Prop :=
  ∃ (lam : Bool → ℝ) (h : ℝ), 0 ≤ lam false ∧ 0 ≤ lam true ∧ lam false + lam true = 1 ∧
    0 < h ∧ h ≤ 1 ∧
    (∀ j, chi j ≤ lam false * v0 j + lam true * v1 j) ∧
    (0 < lam false → lam false * v0 false + lam true * v1 false = v0 false) ∧
    (0 < lam true → lam false * v0 true + lam true * v1 true = v1 true) ∧
    (0 < lam false →
      (1 - h) * (v1 true - (lam false * v0 true + lam true * v1 true)) +
        h * (c true - v0 true) ≤ 0) ∧
    (0 < lam true →
      (1 - h) * (v0 false - (lam false * v0 false + lam true * v1 false)) +
        h * (c false - v1 false) ≤ 0)

/-- **The variant's closed form.**  As with `circulationL1Feasible_bool_iff`
the mixed disjunct is not genuine: two positive weights force `v0 = v1` by
pinning, and the mixed deterrence clause then collapses to the pure one.  What
survives is a two-way disjunction whose deterrence conjunct is *verbatim* the
`hrate` hypothesis of `quittingGame_isUniformEquilibriumPayoff_soloRate`.
Setting `h = 0` in that conjunct recovers `v1 true ≤ v0 true`, the first
disjunct of `circulationTwoExists_iff`: the old class is the hazard-free
degeneration of this one. -/
theorem collisionFacedTwoFeasible_iff (v0 v1 c chi : Bool → ℝ) :
    CollisionFacedTwoFeasible v0 v1 c chi ↔
      (chi false ≤ v0 false ∧ chi true ≤ v0 true ∧
        ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ (1 - h) * v1 true + h * c true ≤ v0 true) ∨
      (chi false ≤ v1 false ∧ chi true ≤ v1 true ∧
        ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ (1 - h) * v0 false + h * c false ≤ v1 false) := by
  constructor
  · rintro ⟨lam, h, hlam0, hlam1, hsum, hh0, hh1, hge, hpin0, hpin1, hdet0, hdet1⟩
    by_cases hq : lam true = 0
    · have hp1 : lam false = 1 := by linarith
      have hdet := hdet0 (by rw [hp1]; norm_num)
      rw [hp1, hq] at hdet hge
      refine Or.inl ⟨?_, ?_, h, hh0, hh1, by linarith⟩
      · have := hge false; linarith
      · have := hge true; linarith
    · have hqpos : 0 < lam true := lt_of_le_of_ne hlam1 (Ne.symm hq)
      by_cases hp : lam false = 0
      · have hq1 : lam true = 1 := by linarith
        have hdet := hdet1 (by rw [hq1]; norm_num)
        rw [hp, hq1] at hdet hge
        refine Or.inr ⟨?_, ?_, h, hh0, hh1, by linarith⟩
        · have := hge false; linarith
        · have := hge true; linarith
      · have hppos : 0 < lam false := lt_of_le_of_ne hlam0 (Ne.symm hp)
        have heq0 := hpin0 hppos
        have heq1 := hpin1 hqpos
        have hv10 : v1 false = v0 false := by
          have h1 : lam true * v1 false = lam true * v0 false := by
            linear_combination heq0 - v0 false * hsum
          exact mul_left_cancel₀ (ne_of_gt hqpos) h1
        have hv01 : v0 true = v1 true := by
          have h1 : lam false * v0 true = lam false * v1 true := by
            linear_combination heq1 - v1 true * hsum
          exact mul_left_cancel₀ (ne_of_gt hppos) h1
        have hufalse : lam false * v0 false + lam true * v1 false = v0 false := heq0
        have hutrue : lam false * v0 true + lam true * v1 true = v1 true := heq1
        have hdet := hdet0 hppos
        rw [hutrue] at hdet
        have hc : h * (c true - v0 true) ≤ 0 := by linarith
        have hct : c true ≤ v0 true := by
          by_contra hcon
          push Not at hcon
          nlinarith
        refine Or.inl ⟨?_, ?_, h, hh0, hh1, by nlinarith⟩
        · have := hge false; rw [hufalse] at this; exact this
        · have := hge true; rw [hutrue] at this; linarith
  · rintro (⟨hf, ht, h, hh0, hh1, hdet⟩ | ⟨hf, ht, h, hh0, hh1, hdet⟩)
    · refine ⟨fun j => if j then 0 else 1, h, by norm_num, by norm_num, by norm_num,
        hh0, hh1, fun j => by cases j <;> simpa using ‹_›, fun _ => by norm_num,
        fun hc => by norm_num at hc, fun _ => by norm_num; linarith,
        fun hc => by norm_num at hc⟩
    · refine ⟨fun j => if j then 1 else 0, h, by norm_num, by norm_num, by norm_num,
        hh0, hh1, fun j => by cases j <;> simpa using ‹_›,
        fun hc => by norm_num at hc, fun _ => by norm_num,
        fun hc => by norm_num at hc, fun _ => by norm_num; linarith⟩

/-! ## The variant's own orbit production -/

/-- The two-coordinate weight in row form: solo rows `v0, v1` and collision
row `c`.  Every coalition that is not a singleton reads `c`, which at
`ι = Bool` is exactly the joint coalition `{false, true}`. -/
def rowWeight (v0 v1 c : Bool → ℝ) : Finset Bool → Bool → ℝ :=
  fun S => if S = {false} then v0 else if S = {true} then v1 else c

@[simp] theorem rowWeight_false (v0 v1 c : Bool → ℝ) : rowWeight v0 v1 c {false} = v0 := by
  simp [rowWeight]

@[simp] theorem rowWeight_true (v0 v1 c : Bool → ℝ) : rowWeight v0 v1 c {true} = v1 := by
  have hne : ({true} : Finset Bool) ≠ {false} := by decide
  simp [rowWeight, hne]

theorem rowWeight_pair (v0 v1 c : Bool → ℝ) {k i : Bool} (hk : k ≠ i) :
    rowWeight v0 v1 c {k, i} = c := by
  have h1 : ({k, i} : Finset Bool) ≠ {false} := by revert hk; cases k <;> cases i <;> decide
  have h2 : ({k, i} : Finset Bool) ≠ {true} := by revert hk; cases k <;> cases i <;> decide
  simp [rowWeight, h1, h2]

/-- **The left disjunct is an exactly support-perfect microstep row.**  At the
solo row `v0` itself, the singleton row `h e_false` satisfies every one-stage
inequality with tolerance `0`: the owner is pinned, and the blocker is deterred
by the deterrence clause. -/
theorem isSupportPerfectRow_rowWeight_left (v0 v1 c : Bool → ℝ) (h : ℝ)
    (hdet : (1 - h) * v1 true + h * c true ≤ v0 true) :
    IsSupportPerfectRow (rowWeight v0 v1 c) (singletonRow h false) v0 0 := by
  refine isSupportPerfectRow_singletonRow_of_deterrence _ h false v0 (by simp) ?_
  intro k hk
  obtain rfl : k = true := by revert hk; cases k <;> simp
  rw [rowWeight_pair v0 v1 c hk]
  simp only [rowWeight_true, rowWeight_false]
  linarith

/-- **The right disjunct is an exactly support-perfect microstep row**, the
mirror of `isSupportPerfectRow_rowWeight_left`. -/
theorem isSupportPerfectRow_rowWeight_right (v0 v1 c : Bool → ℝ) (h : ℝ)
    (hdet : (1 - h) * v0 false + h * c false ≤ v1 false) :
    IsSupportPerfectRow (rowWeight v0 v1 c) (singletonRow h true) v1 0 := by
  refine isSupportPerfectRow_singletonRow_of_deterrence _ h true v1 (by simp) ?_
  intro k hk
  obtain rfl : k = false := by revert hk; cases k <;> simp
  rw [rowWeight_pair v0 v1 c hk]
  simp only [rowWeight_true, rowWeight_false]
  linarith

/-- **Unbounded quit mass from a constant singleton row.**  A hazard `h > 0`
repeated `T` times releases quit mass `T h`, so every target is met. -/
theorem exists_prefix_quitMass_singletonRow_ge (h : ℝ) (hh0 : 0 < h) (i : ι) (Q : ℝ) :
    ∃ T : ℕ, Q ≤ ∑ _n ∈ Finset.range T, (1 - continueMass (singletonRow h i)) := by
  obtain ⟨T, hT⟩ := exists_nat_ge (Q / h)
  refine ⟨T, ?_⟩
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, quitMass_singletonRow]
  rw [div_le_iff₀ hh0] at hT
  linarith

/-- **The variant certificate produces an exact orbit.**  Unlike
`exists_multiCirculation_orbit`, whose conclusions hold at a positive
tolerance `ε` bought with a vanishing hazard budget, the `χ`-floored
certificate yields a stationary chain whose microstep rows are support-perfect
at tolerance **zero**, whose state is above the `χ` floor exactly, and whose
prefix quit mass is unbounded — with no reward bound and no hazard budget.

This is the separate orbit theorem the floor-interface change requires:
`subSolo_gap_le_of_hazard_le` shows the inherited theorem's interface cannot
host a sub-solo floor, so nothing is silently weakened here. -/
theorem exists_exact_orbit_of_collisionFacedTwoFeasible (v0 v1 c chi : Bool → ℝ)
    (hcert : CollisionFacedTwoFeasible v0 v1 c chi) (Q : ℝ) :
    ∃ (h : ℝ) (i : Bool) (rest : Bool → ℝ), 0 < h ∧ h ≤ 1 ∧
      (∀ j, chi j ≤ rest j) ∧
      IsSupportPerfectRow (rowWeight v0 v1 c) (singletonRow h i) rest 0 ∧
      ∃ T : ℕ, Q ≤ ∑ _n ∈ Finset.range T, (1 - continueMass (singletonRow h i)) := by
  rcases (collisionFacedTwoFeasible_iff v0 v1 c chi).mp hcert with
    ⟨hf, ht, h, hh0, hh1, hdet⟩ | ⟨hf, ht, h, hh0, hh1, hdet⟩
  · exact ⟨h, false, v0, hh0, hh1, fun j => by cases j <;> assumption,
      isSupportPerfectRow_rowWeight_left v0 v1 c h hdet,
      exists_prefix_quitMass_singletonRow_ge h hh0 false Q⟩
  · exact ⟨h, true, v1, hh0, hh1, fun j => by cases j <;> assumption,
      isSupportPerfectRow_rowWeight_right v0 v1 c h hdet,
      exists_prefix_quitMass_singletonRow_ge h hh0 true Q⟩

/-! ## The two covered branches -/

/-- **The solo-quitter branch is covered.**  Its rate hypothesis `hrate` at
rate `p` is the deterrence clause at hazard `p`.  The owner's floor clause
comes from the `y = 0` cap, since `0 ≤ d_owner` makes `max 0 (d_owner)` equal
`d_owner`; the blocker's comes from the cap at the punishing rate `y = p`,
where `hrate` itself collapses `stationaryPunishValue` to the blocker's cross
payoff. -/
theorem soloRate_collisionFacedTwoFeasible (v0 v1 c chi : Bool → ℝ)
    (hcap : IsStationaryPunishmentCap v0 v1 c chi) (hsolo : 0 ≤ v0 false)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hrate : (1 - p) * v1 true + p * c true ≤ v0 true) :
    CollisionFacedTwoFeasible v0 v1 c chi := by
  obtain ⟨hcap0, _, _, hcapt⟩ := hcap
  rw [collisionFacedTwoFeasible_iff]
  refine Or.inl ⟨by rwa [max_eq_right hsolo] at hcap0, ?_, p, hp0, hp1, hrate⟩
  have hval := hcapt p hp0 hp1
  unfold stationaryPunishValue at hval
  rwa [max_eq_right hrate] at hval

/-- **The pair-repair branch is covered** — the decisive verdict.  The
certificate's owner is the *blocker*, at full hazard `h = 1`, so the deterred
coordinate is the branch's own owner and the deterrence clause is literally
`howner : r{owner,blocker}_owner ≤ r{blocker}_owner`.  That same inequality
collapses the owner's stationary punishment value at `y = 1`, giving the
owner's floor clause.  The blocker's floor clause needs the whole cap family:
`hblocker : r{owner}_blocker ≤ d_blocker` makes the punishment value at rate
`y` at most `d_blocker + y·max(0, c_blocker - d_blocker)`, and letting `y`
tend to `0` gives `χ_blocker ≤ d_blocker`.

The branch's weights are exactly the sub-solo-compensation cases the
floor-at-solo class excluded, and no hypothesis beyond the branch's own two
inequalities is used. -/
theorem pairRepair_collisionFacedTwoFeasible (v0 v1 c chi : Bool → ℝ)
    (hcap : IsStationaryPunishmentCap v0 v1 c chi)
    (howner : c false ≤ v1 false) (hblocker : v0 true ≤ v1 true) :
    CollisionFacedTwoFeasible v0 v1 c chi := by
  obtain ⟨_, _, hcapf, hcapt⟩ := hcap
  rw [collisionFacedTwoFeasible_iff]
  refine Or.inr ⟨?_, ?_, 1, one_pos, le_rfl, by linarith⟩
  · have hval := hcapf 1 one_pos le_rfl
    unfold stationaryPunishValue at hval
    rwa [max_eq_right (by linarith : (1 - (1 : ℝ)) * v0 false + 1 * c false ≤ v1 false)] at hval
  · refine le_of_forall_pos_le_add fun d hd => ?_
    set C : ℝ := max 0 (c true - v1 true) with hCdef
    have hC0 : 0 ≤ C := le_max_left _ _
    have hCle : c true - v1 true ≤ C := le_max_right _ _
    have hden : (0 : ℝ) < C + 1 := by linarith
    set y : ℝ := min 1 (d / (C + 1)) with hydef
    have hy0 : 0 < y := lt_min one_pos (div_pos hd hden)
    have hy1 : y ≤ 1 := min_le_left _ _
    have hyC : y * C ≤ d := by
      have h1 : y ≤ d / (C + 1) := min_le_right _ _
      have h2 : y * (C + 1) ≤ d / (C + 1) * (C + 1) :=
        mul_le_mul_of_nonneg_right h1 hden.le
      have h3 : d / (C + 1) * (C + 1) = d := by field_simp
      rw [h3] at h2
      nlinarith
    have hval := hcapt y hy0 hy1
    unfold stationaryPunishValue at hval
    have hbound : max ((1 - y) * v1 true + y * c true) (v0 true) ≤ v1 true + y * C := by
      refine max_le ?_ ?_
      · linarith [mul_le_mul_of_nonneg_left hCle hy0.le]
      · linarith [mul_nonneg hy0.le hC0]
    linarith

/-! ## The reward-level form of the two covered branches -/

/-- The joint-coalition row of a two-player weight, read at each coordinate:
`collisionRow reward j` is the payoff to `j` when both players quit. -/
def collisionRow (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) : Bool → ℝ :=
  fun j => quittingSingletonCollisionReward reward (!j) j

@[simp] theorem collisionRow_sampleReward (v0 v1 c : Bool → ℝ) :
    collisionRow (sampleReward v0 v1 c) = c := by
  funext j
  rw [collisionRow, quittingSingletonCollisionReward_sampleReward v0 v1 c (!j) j
    (by cases j <;> decide)]

/-- **The solo-quitter branch, at reward level.**  The hypotheses are verbatim
those of `quittingGame_isUniformEquilibriumPayoff_soloRate` at
`owner = false`. -/
theorem soloRate_reward_collisionFacedTwoFeasible
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) (chi : Bool → ℝ)
    (hcap : IsStationaryPunishmentCap (quittingSoloReward reward false)
      (quittingSoloReward reward true) (collisionRow reward) chi)
    (hsolo : 0 ≤ quittingSoloReward reward false false)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hrate : (1 - p) * quittingSoloReward reward true true +
        p * quittingSingletonCollisionReward reward false true ≤
      quittingSoloReward reward false true) :
    CollisionFacedTwoFeasible (quittingSoloReward reward false)
      (quittingSoloReward reward true) (collisionRow reward) chi :=
  soloRate_collisionFacedTwoFeasible _ _ _ _ hcap hsolo hp0 hp1 hrate

/-- **The pair-repair branch, at reward level.**  The hypotheses are verbatim
those of `exists_uniformEquilibriumPayoff_of_bool_pairRepair` at
`owner = false`, so every weight that branch handles admits the variant
certificate for every capped `χ`. -/
theorem pairRepair_reward_collisionFacedTwoFeasible
    (reward : {S : Finset Bool // S.Nonempty} → Payoff Bool) (chi : Bool → ℝ)
    (hcap : IsStationaryPunishmentCap (quittingSoloReward reward false)
      (quittingSoloReward reward true) (collisionRow reward) chi)
    (howner : quittingSingletonCollisionReward reward true false ≤
      quittingSoloReward reward true false)
    (hblocker : quittingSoloReward reward false true ≤ quittingSoloReward reward true true) :
    CollisionFacedTwoFeasible (quittingSoloReward reward false)
      (quittingSoloReward reward true) (collisionRow reward) chi :=
  pairRepair_collisionFacedTwoFeasible _ _ _ _ hcap howner hblocker

/-! ## The two witnesses the previous file left outside are now inside -/

/-- The previous file's pair-repair witness: owner's solo value `1`, blocker's
solo value `5`, cross payoffs both `0`, collision-at-owner `-1`. -/
def pairRepairWitness : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  sampleReward (fun j => if j then 0 else 1) (fun j => if j then 5 else 0)
    (fun j => if j then 0 else -1)

/-- **The pair-repair witness crosses the boundary.**  The very weight
`pairRepair_exists_outside_circulationTwoExists` exhibited outside the
floor-at-solo class is inside the `χ`-floored class, for *every* `χ` obeying
the stationary punishment cap — while remaining outside
`CirculationTwoExists`.  The boundary the previous file drew was therefore an
artifact of the floor, not of the certificate idea. -/
theorem pairRepairWitness_inside_chiFloor (chi : Bool → ℝ)
    (hcap : IsStationaryPunishmentCap (quittingSoloReward pairRepairWitness false)
      (quittingSoloReward pairRepairWitness true) (collisionRow pairRepairWitness) chi) :
    CollisionFacedTwoFeasible (quittingSoloReward pairRepairWitness false)
        (quittingSoloReward pairRepairWitness true) (collisionRow pairRepairWitness) chi ∧
      ¬ CirculationTwoExists (quittingSoloReward pairRepairWitness false)
        (quittingSoloReward pairRepairWitness true) := by
  have howner : quittingSingletonCollisionReward pairRepairWitness true false ≤
      quittingSoloReward pairRepairWitness true false := by
    unfold pairRepairWitness
    rw [quittingSingletonCollisionReward_sampleReward _ _ _ true false (by decide)]
    simp
  have hblocker : quittingSoloReward pairRepairWitness false true ≤
      quittingSoloReward pairRepairWitness true true := by
    simp [pairRepairWitness]
  refine ⟨pairRepair_reward_collisionFacedTwoFeasible _ chi hcap howner hblocker, ?_⟩
  simp only [pairRepairWitness, quittingSoloReward_sampleReward_false,
    quittingSoloReward_sampleReward_true]
  rw [circulationTwoExists_iff]
  norm_num

/-- The previous file's solo-quitter witness: owner's solo value `2`,
blocker's solo value `1`, cross payoffs `0`, collision-at-blocker `-10`. -/
def soloRateWitness : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  sampleReward (fun j => if j then 0 else 2) (fun j => if j then 1 else 0)
    (fun j => if j then -10 else 0)

/-- **The solo-quitter witness crosses the boundary too**, at hazard `p = 1`:
the blocker is held out by the collision value `-10`, not by any floor. -/
theorem soloRateWitness_inside_chiFloor (chi : Bool → ℝ)
    (hcap : IsStationaryPunishmentCap (quittingSoloReward soloRateWitness false)
      (quittingSoloReward soloRateWitness true) (collisionRow soloRateWitness) chi) :
    CollisionFacedTwoFeasible (quittingSoloReward soloRateWitness false)
        (quittingSoloReward soloRateWitness true) (collisionRow soloRateWitness) chi ∧
      ¬ CirculationTwoExists (quittingSoloReward soloRateWitness false)
        (quittingSoloReward soloRateWitness true) := by
  have hsolo : 0 ≤ quittingSoloReward soloRateWitness false false := by
    simp [soloRateWitness]
  have hrate : (1 - (1 : ℝ)) * quittingSoloReward soloRateWitness true true +
      1 * quittingSingletonCollisionReward soloRateWitness false true ≤
      quittingSoloReward soloRateWitness false true := by
    unfold soloRateWitness
    rw [quittingSingletonCollisionReward_sampleReward _ _ _ false true (by decide)]
    simp
  refine ⟨soloRate_reward_collisionFacedTwoFeasible _ chi hcap hsolo one_pos le_rfl hrate, ?_⟩
  simp only [soloRateWitness, quittingSoloReward_sampleReward_false,
    quittingSoloReward_sampleReward_true]
  rw [circulationTwoExists_iff]
  norm_num

/-- **Both changes are load-bearing at both covered branches.**  Composing
`isStationaryPunishmentCap_min` with the two crossing theorems exhibits a
concrete `χ` at which each witness is inside the variant class, so neither the
cap hypothesis nor the certificate is vacuous and the exact orbit of
`exists_exact_orbit_of_collisionFacedTwoFeasible` is realised at real
two-player weights.  Each witness also still fails `circulationTwoExists_iff`,
i.e. fails at the *best* floor-at-solo, so the sub-solo floor is necessary; and
each needs a strictly positive hazard (`pairRepairWitness` at `h = 1`,
`soloRateWitness` at any `h ≥ 1/11`), so the freed hazard is necessary too. -/
theorem chiFloor_nonvacuous :
    CollisionFacedTwoFeasible (quittingSoloReward pairRepairWitness false)
        (quittingSoloReward pairRepairWitness true) (collisionRow pairRepairWitness)
        (fun j => min (min 0 (min (quittingSoloReward pairRepairWitness false j)
          (quittingSoloReward pairRepairWitness true j))) (collisionRow pairRepairWitness j)) ∧
      CollisionFacedTwoFeasible (quittingSoloReward soloRateWitness false)
        (quittingSoloReward soloRateWitness true) (collisionRow soloRateWitness)
        (fun j => min (min 0 (min (quittingSoloReward soloRateWitness false j)
          (quittingSoloReward soloRateWitness true j))) (collisionRow soloRateWitness j)) :=
  ⟨(pairRepairWitness_inside_chiFloor _ (isStationaryPunishmentCap_min _ _ _)).1,
    (soloRateWitness_inside_chiFloor _ (isStationaryPunishmentCap_min _ _ _)).1⟩

/-! ## The two branches that persist outside -/

/-- The zero-solo weight: both solo values `0`, both cross payoffs `-5`,
collision `0`. -/
def zeroSoloWitness : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  sampleReward (fun j => if j then -5 else 0) (fun j => if j then 0 else -5) (fun _ => 0)

/-- **The zero-solo branch persists outside**, for every `χ` whatsoever.  Both
deterrence clauses read `0 ≤ -5` at every hazard, so the failure is not a
floor failure and no relaxation of the floor can repair it: the all-continue
equilibrium of a zero-solo weight releases *no* quit mass, which is the one
thing a circulation certificate is built to produce. -/
theorem zeroSolo_persists_outside_chiFloor :
    (∃ payoff : Payoff Bool,
      (quittingGame zeroSoloWitness).IsUniformEquilibriumPayoff none payoff) ∧
    ∀ chi : Bool → ℝ, ¬ CollisionFacedTwoFeasible (quittingSoloReward zeroSoloWitness false)
      (quittingSoloReward zeroSoloWitness true) (collisionRow zeroSoloWitness) chi := by
  have hzero : IsQuittingZeroSolo zeroSoloWitness := by
    intro who
    cases who <;> simp [zeroSoloWitness, quittingSingletonTerminal, sampleReward]
  refine ⟨exists_uniformEquilibriumPayoff_of_zeroSolo zeroSoloWitness hzero, fun chi => ?_⟩
  simp only [zeroSoloWitness, quittingSoloReward_sampleReward_false,
    quittingSoloReward_sampleReward_true, collisionRow_sampleReward]
  rw [collisionFacedTwoFeasible_iff]
  rintro (⟨_, _, h, hh0, hh1, hdet⟩ | ⟨_, _, h, hh0, hh1, hdet⟩) <;> norm_num at hdet

/-- The joint-exit weight: both solo values `1`, both cross payoffs `-5`,
collision `10` at both coordinates. -/
def jointExitWitness : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  sampleReward (fun j => if j then -5 else 1) (fun j => if j then 1 else -5)
    (fun _ => 10)

/-- The joint exit of `jointExitWitness` pays `10` to both players. -/
@[simp] theorem jointExitWitness_jointExitTerminal :
    jointExitWitness (jointExitTerminal false) = fun _ => (10 : ℝ) := by
  have h1 : ({false, true} : Finset Bool) ≠ {false} := by decide
  have h2 : ({false, true} : Finset Bool) ≠ {true} := by decide
  simp [jointExitWitness, jointExitTerminal, sampleReward, h1, h2]

/-- **The joint-exit branch persists outside**, for every `χ`.  Here the
deterrence clause fails in the opposite direction: the collision value `10`
dominates every cross payoff, so joining the other player's exit is strictly
attractive at every hazard, and both disjuncts read `1 + 9h ≤ -5`.  Again this
is not a floor failure — a certificate can never deter a coordinate that
*wants* the collision. -/
theorem jointExit_persists_outside_chiFloor :
    (∃ payoff : Payoff Bool,
      (quittingGame jointExitWitness).IsUniformEquilibriumPayoff none payoff) ∧
    ∀ chi : Bool → ℝ, ¬ CollisionFacedTwoFeasible (quittingSoloReward jointExitWitness false)
      (quittingSoloReward jointExitWitness true) (collisionRow jointExitWitness) chi := by
  have howner : quittingSoloReward jointExitWitness true false ≤
      quittingSingletonCollisionReward jointExitWitness true false := by
    unfold jointExitWitness
    rw [quittingSingletonCollisionReward_sampleReward _ _ _ true false (by decide)]
    norm_num
  have hblocker : quittingSoloReward jointExitWitness false true ≤
      quittingSingletonCollisionReward jointExitWitness false true := by
    unfold jointExitWitness
    rw [quittingSingletonCollisionReward_sampleReward _ _ _ false true (by decide)]
    norm_num
  refine ⟨⟨_, quittingGame_isUniformEquilibriumPayoff_jointExit jointExitWitness false
    howner hblocker⟩, fun chi => ?_⟩
  simp only [jointExitWitness, quittingSoloReward_sampleReward_false,
    quittingSoloReward_sampleReward_true, collisionRow_sampleReward]
  rw [collisionFacedTwoFeasible_iff]
  rintro (⟨_, _, h, hh0, hh1, hdet⟩ | ⟨_, _, h, hh0, hh1, hdet⟩) <;> norm_num at hdet <;>
    linarith

/-! ## What the survivors' equilibria use -/

/-- **The all-continue payoff is not a mixture of the solo rows.**  Both cross
payoffs of `zeroSoloWitness` are `-5`, so every convex combination of the two
solo rows has a coordinate at `-5`, while the branch's payoff is `0` at both.
A circulation certificate's states are pinned convex combinations of solo rows
(`mixTarget`), so this payoff is outside the certificate's reach for reasons
having nothing to do with the floor. -/
theorem zeroSoloPayoff_not_soloMixture :
    ¬ ∃ lam : Bool → ℝ, 0 ≤ lam false ∧ 0 ≤ lam true ∧ lam false + lam true = 1 ∧
      ∀ j, (0 : Payoff Bool) j =
        lam false * quittingSoloReward zeroSoloWitness false j +
          lam true * quittingSoloReward zeroSoloWitness true j := by
  rintro ⟨lam, hlam0, hlam1, hsum, hmix⟩
  have h0 := hmix false
  have h1 := hmix true
  simp only [zeroSoloWitness, quittingSoloReward_sampleReward_false,
    quittingSoloReward_sampleReward_true] at h0 h1
  norm_num at h0 h1
  linarith

/-- **The joint-exit payoff is not a mixture of the solo rows.**  The two solo
rows of `jointExitWitness` sum to `(-4, -4)` coordinatewise, so every convex
combination has coordinate sum `-4`, while the joint exit row `(10, 10)` sums
to `20`.  Simultaneous quitting is a payoff `mixTarget` cannot name, and
`multiRow` — a singleton row at every microstep, multi-owner phases
included — can never produce it. -/
theorem jointExitPayoff_not_soloMixture :
    ¬ ∃ lam : Bool → ℝ, 0 ≤ lam false ∧ 0 ≤ lam true ∧ lam false + lam true = 1 ∧
      ∀ j, jointExitWitness (jointExitTerminal false) j =
        lam false * quittingSoloReward jointExitWitness false j +
          lam true * quittingSoloReward jointExitWitness true j := by
  rintro ⟨lam, hlam0, hlam1, hsum, hmix⟩
  have h0 := hmix false
  have h1 := hmix true
  rw [jointExitWitness_jointExitTerminal] at h0 h1
  simp only [jointExitWitness, quittingSoloReward_sampleReward_false,
    quittingSoloReward_sampleReward_true] at h0 h1
  norm_num at h0 h1
  linarith

/-! ## The verdict -/

/-- **The re-run boundary, in one statement.**

Two branches fall to the `χ`-floored, collision-deterred variant and two do
not.

* Solo-rate and pair-repair are *covered in general*, not merely at a witness:
  their own defining inequalities are the variant's deterrence clause, at
  hazard `p` and at hazard `1` respectively, and their floor clauses come from
  the stationary punishment cap alone.
* Zero-solo and joint-exit have explicit weights outside the variant for
  *every* `χ`.

So the certificate class was mismeasured: `circulationTwoExists_iff`'s
floor-at-solo, not the certificate idea, is what excluded the
sub-solo-compensation weights, and the residual-habitat specification moves
accordingly — from "weights whose equilibrium pays a player less than its own
solo value" to "weights whose equilibrium payoff leaves the solo-row hull".
The two survivors are exactly the latter
(`zeroSoloPayoff_not_soloMixture`, `jointExitPayoff_not_soloMixture`), and
their obstruction is structural rather than numerical: `mixTarget`'s range is
the hull of the solo rows, and `multiRow` is a singleton row at every
microstep — even at a multi-owner phase — so neither a zero-quit-mass profile
nor a simultaneous-quit payoff is expressible, at any floor. -/
theorem chiFloor_fourBranch_verdict :
    (∀ v0 v1 c chi : Bool → ℝ, IsStationaryPunishmentCap v0 v1 c chi → 0 ≤ v0 false →
        ∀ p : ℝ, 0 < p → p ≤ 1 → (1 - p) * v1 true + p * c true ≤ v0 true →
          CollisionFacedTwoFeasible v0 v1 c chi) ∧
      (∀ v0 v1 c chi : Bool → ℝ, IsStationaryPunishmentCap v0 v1 c chi →
        c false ≤ v1 false → v0 true ≤ v1 true → CollisionFacedTwoFeasible v0 v1 c chi) ∧
      (∀ chi : Bool → ℝ, ¬ CollisionFacedTwoFeasible
        (quittingSoloReward zeroSoloWitness false) (quittingSoloReward zeroSoloWitness true)
        (collisionRow zeroSoloWitness) chi) ∧
      (∀ chi : Bool → ℝ, ¬ CollisionFacedTwoFeasible
        (quittingSoloReward jointExitWitness false) (quittingSoloReward jointExitWitness true)
        (collisionRow jointExitWitness) chi) :=
  ⟨fun v0 v1 c chi hcap hsolo _p hp0 hp1 hrate =>
      soloRate_collisionFacedTwoFeasible v0 v1 c chi hcap hsolo hp0 hp1 hrate,
    fun v0 v1 c chi hcap howner hblocker =>
      pairRepair_collisionFacedTwoFeasible v0 v1 c chi hcap howner hblocker,
    zeroSolo_persists_outside_chiFloor.2, jointExit_persists_outside_chiFloor.2⟩

end QuittingCirculationChiFloorBoundary

end GameTheory
