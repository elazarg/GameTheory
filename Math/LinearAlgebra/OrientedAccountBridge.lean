/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.LinearAlgebra.OwnerLabeledFlowHolonomy

/-!
# Oriented account bridges: the exact common-bridge core

**Provenance.**  This is the finite linear-algebra core of an owner-history
account-obstruction analysis, built on the holonomy substrate of
`Math.LinearAlgebra.OwnerLabeledFlowHolonomy`.  It formalizes three pieces of
that analysis:

* the drift operator `D` and the signed public cycle space of its "Common
  notation" — here `D` is the negated coboundary
  `H ↦ (r ↦ H (src r) - ∑ v, P r v * H v)` already available through
  `OwnerLabeledFlowHolonomy.sum_incidenceEntry_mul`, and the cycle space is
  the kernel of `incidence`;
* Part B (orientation completion): a charge may admit a ledger for one
  orientation and not the other, so "both orientations, one ledger each"
  (`HasBothOrientations`, carrying separate credit and debit potentials
  `K⁺` and `K⁻`) is a genuinely weaker datum than a single two-sided account;
* Part C (the common Bellman bridge and the exact cycle criterion):
  the scalar bridge `c = D B` is an *equality*, so its feasibility is
  governed by the cycle space with both signs, not by the one-sided cone.

**Scope, honestly.**  Only the orientation/bridge gates of the strategic
account-completeness invariant `SAC` are treated here.  The
other two clauses — *finite public observability* (Part A) and *shift
compactness or bounded restart* (Part D) — are **future work** and are not
formalized in this file, nor is any statement below strong enough to imply
them.

**This file is deliberately game-free**, exactly like its substrate: rows `R`
and vertices `V` are bare finite types and `P` is a bare row-stochastic
matrix.  The strategic reading belongs to the consumers.

## Main definitions

* `IsExactBridge src P c H`: the *equality* version of
  `OwnerLabeledFlowHolonomy.IsAccountPotential`, i.e. `c` is an exact
  coboundary, `c r = H (src r) - ∑ v, P r v * H v` for every row.
* `NeutralHolonomy src P c`: every circulation pairs to exactly `0` with `c`
  (the two-sided cycle criterion for the scalar bridge).
* `HasBothOrientations src P c`: Part B — one ledger per orientation, with
  the two potentials allowed to differ.
* `HasFullSupportCirculation src P`: the irreducibility-flavoured hypothesis
  that some circulation charges every row strictly positively.

## Main results

* `neutralHolonomy_iff_zeroHolonomy_pair`: the two-sided cycle criterion is
  exactly zero holonomy for `c` together with zero holonomy for `-c`.
* `hasBothOrientations_iff_zeroHolonomy_pair`: unconditionally, carrying one
  ledger per orientation is exactly the two-sided cycle criterion (two
  applications of the substrate's Farkas duality).
* `exists_isExactBridge_iff_zeroHolonomy_pair`: **under**
  `HasFullSupportCirculation`, an exact bridge exists iff the two-sided cycle
  criterion holds; equivalently (`exists_isExactBridge_iff_hasBothOrientations`)
  iff both orientations carry a ledger.  The forward direction is
  unconditional; the converse genuinely needs the hypothesis.
* `ParallelRows.not_exists_isExactBridge_charge`: the hypothesis is not
  decorative.  Two parallel rows leaving a source vertex that is never
  re-entered admit *no* nonzero circulation at all, so the cycle criterion is
  vacuously true and both orientations carry ledgers, yet no exact bridge
  exists.  So `HasBothOrientations` does **not** imply an exact bridge in
  general.
* `SelfLoop.not_hasBothOrientations` and
  `SelfLoop.not_exists_isExactBridge`: the
  *pure common-orientation obstruction*.  On the one-state self-loop with a
  strictly negative charge the credit ledger exists (`H = 0` works) while the
  debit ledger does not: the unique normalized circulation is the Farkas
  witness `φ(e) = 1`.  Here `HasFullSupportCirculation` *holds*, so
  the failure is one of orientation only.
-/

open Finset BigOperators
open Math.LinearAlgebra.OwnerLabeledFlowHolonomy

namespace Math
namespace LinearAlgebra
namespace OrientedAccountBridge

noncomputable section

section General

variable {R V : Type*} [Fintype R] [Fintype V] [DecidableEq V]

/-! ### The exact bridge -/

omit [Fintype R] [DecidableEq V] in
/-- An *exact account bridge*: the charge cochain is the exact drift of a
scalar potential, `c r = H (src r) - ∑ v, P r v * H v` for every row.  This is
the equality version of `OwnerLabeledFlowHolonomy.IsAccountPotential`, whose
sign convention it matches: `IsAccountPotential` asserts `c r ≤ H (src r) -
∑ v, P r v * H v`.  It is the scalar case `k = 1`, `α = 1` of the general
weighted exact-bridge equation. -/
def IsExactBridge (src : R → V) (P : R → V → ℝ) (c : R → ℝ) (H : V → ℝ) : Prop :=
  ∀ r, c r = H (src r) - ∑ v, P r v * H v

omit [Fintype R] [DecidableEq V] in
/-- An exact bridge is in particular a one-sided ledger for `c`. -/
theorem accountPotential_of_isExactBridge {src : R → V} {P : R → V → ℝ}
    {c : R → ℝ} {H : V → ℝ} (h : IsExactBridge src P c H) :
    IsAccountPotential src P c H := by
  intro r
  have hr := h r
  linarith

omit [Fintype R] [DecidableEq V] in
/-- An exact bridge for `c` yields, by negating the potential, a one-sided
ledger for the opposite orientation `-c`. -/
theorem neg_accountPotential_of_isExactBridge {src : R → V} {P : R → V → ℝ}
    {c : R → ℝ} {H : V → ℝ} (h : IsExactBridge src P c H) :
    IsAccountPotential src P (fun r => -(c r)) fun v => -(H v) := by
  intro r
  have hr := h r
  have hneg : (∑ v, P r v * -(H v)) = -∑ v, P r v * H v := by
    simp [mul_neg]
  simp only [hneg]
  linarith

omit [Fintype R] [DecidableEq V] in
/-- Vacuity probe: the zero charge is bridged by the zero potential. -/
theorem isExactBridge_zero (src : R → V) (P : R → V → ℝ) :
    IsExactBridge src P (0 : R → ℝ) (0 : V → ℝ) := by
  intro r
  simp

/-! ### The two-sided cycle criterion -/

omit [Fintype V] [DecidableEq V] in
/-- Holonomy is odd in the charge cochain. -/
theorem holonomy_neg (c : R → ℝ) (x : R → ℝ) :
    holonomy (fun r => -(c r)) x = -holonomy c x := by
  simp [holonomy, mul_neg]

/-- The scalar two-sided cycle criterion:
every circulation pairs to *exactly* zero with the charge cochain.  Contrast
`OwnerLabeledFlowHolonomy.ZeroHolonomy`, which only asks for `≤ 0`. -/
def NeutralHolonomy (src : R → V) (P : R → V → ℝ) (c : R → ℝ) : Prop :=
  ∀ x : R → ℝ, IsCirculation src P x → holonomy c x = 0

omit [Fintype V] in
/-- The two-sided criterion is exactly the conjunction of the two one-sided
gluing conditions, one per orientation. -/
theorem neutralHolonomy_iff_zeroHolonomy_pair (src : R → V) (P : R → V → ℝ)
    (c : R → ℝ) :
    NeutralHolonomy src P c
      ↔ ZeroHolonomy src P c ∧ ZeroHolonomy src P fun r => -(c r) := by
  constructor
  · intro h
    refine ⟨fun x hx => le_of_eq (h x hx), fun x hx => ?_⟩
    rw [holonomy_neg, h x hx, neg_zero]
  · rintro ⟨hcredit, hdebit⟩ x hx
    have h1 := hcredit x hx
    have h2 := hdebit x hx
    rw [holonomy_neg] at h2
    linarith

/-! ### One ledger per orientation (Part B) -/

/-- The separated (Part B) form: the charge is carried
by a credit ledger *and* its opposite by a debit ledger, the two potentials
being allowed to differ.  This is strictly weaker than one exact two-sided
account; see `ParallelRows.not_exists_isExactBridge_charge`. -/
def HasBothOrientations (src : R → V) (P : R → V → ℝ) (c : R → ℝ) : Prop :=
  (∃ H : V → ℝ, IsAccountPotential src P c H) ∧
    ∃ H : V → ℝ, IsAccountPotential src P (fun r => -(c r)) H

/-- Unconditionally, carrying one ledger per orientation is exactly the
two-sided cycle criterion: apply the substrate's Farkas duality
`zeroHolonomy_iff_exists_accountPotential` to `c` and to `-c`. -/
theorem hasBothOrientations_iff_zeroHolonomy_pair (src : R → V) (P : R → V → ℝ)
    (c : R → ℝ) :
    HasBothOrientations src P c
      ↔ ZeroHolonomy src P c ∧ ZeroHolonomy src P fun r => -(c r) := by
  rw [HasBothOrientations,
    ← zeroHolonomy_iff_exists_accountPotential src P c,
    ← zeroHolonomy_iff_exists_accountPotential src P (fun r => -(c r))]

/-- The same statement phrased through `NeutralHolonomy`. -/
theorem hasBothOrientations_iff_neutralHolonomy (src : R → V) (P : R → V → ℝ)
    (c : R → ℝ) :
    HasBothOrientations src P c ↔ NeutralHolonomy src P c := by
  rw [hasBothOrientations_iff_zeroHolonomy_pair,
    neutralHolonomy_iff_zeroHolonomy_pair]

omit [Fintype R] [DecidableEq V] in
/-- **Easy direction.**  An exact bridge carries both orientations. -/
theorem hasBothOrientations_of_isExactBridge {src : R → V} {P : R → V → ℝ}
    {c : R → ℝ} (h : ∃ H : V → ℝ, IsExactBridge src P c H) :
    HasBothOrientations src P c := by
  obtain ⟨H, hH⟩ := h
  exact ⟨⟨H, accountPotential_of_isExactBridge hH⟩,
    ⟨fun v => -(H v), neg_accountPotential_of_isExactBridge hH⟩⟩

/-- **Easy direction, cycle form.**  An exact bridge makes every circulation
pair to exactly zero. -/
theorem neutralHolonomy_of_exists_isExactBridge {src : R → V} {P : R → V → ℝ}
    {c : R → ℝ} (h : ∃ H : V → ℝ, IsExactBridge src P c H) :
    NeutralHolonomy src P c :=
  (hasBothOrientations_iff_neutralHolonomy src P c).mp
    (hasBothOrientations_of_isExactBridge h)

/-! ### From one-sided ledgers to an exact bridge -/

/-- Pairing the drift of any potential against a circulation gives zero: the
adjunction `⟨H, B x⟩ = ⟨x, D H⟩` together with the balance equations. -/
theorem sum_drift_eq_zero_of_circulation {src : R → V} {P : R → V → ℝ}
    {x : R → ℝ} (hx : IsCirculation src P x) (H : V → ℝ) :
    (∑ r, x r * (H (src r) - ∑ v, P r v * H v)) = 0 := by
  rw [← sum_mul_incidence]
  exact Finset.sum_eq_zero fun v _ => by rw [hx.balanced v, mul_zero]

/-- A circulation charging **every** row strictly positively.  This is the
finite-linear-algebra shadow of the reachability/recurrence side condition
that a nonnegative member of the cycle space is an occupation measure only
when its support is reachable and jointly realizable: it says the cone of
circulations spans the whole signed cycle space. -/
def HasFullSupportCirculation (src : R → V) (P : R → V → ℝ) : Prop :=
  ∃ z : R → ℝ, IsCirculation src P z ∧ ∀ r, 0 < z r

/-- **The tightening lemma.**  A one-sided ledger for `c` is automatically
*exact* as soon as some strictly positive circulation pairs to zero with `c`:
the rowwise slacks are nonnegative and their strictly positive weighted sum
vanishes, so every slack vanishes. -/
theorem isExactBridge_of_accountPotential_of_pos_circulation {src : R → V}
    {P : R → V → ℝ} {c : R → ℝ} {z : R → ℝ} (hz : IsCirculation src P z)
    (hzpos : ∀ r, 0 < z r) (hzero : holonomy c z = 0) {H : V → ℝ}
    (hH : IsAccountPotential src P c H) : IsExactBridge src P c H := by
  set slack : R → ℝ := fun r => (H (src r) - ∑ v, P r v * H v) - c r with hslack
  have hnonneg : ∀ r, 0 ≤ slack r := by
    intro r
    have hr := hH r
    rw [hslack]
    dsimp only
    linarith
  have hdrift := sum_drift_eq_zero_of_circulation hz H
  have hcharge : (∑ r, z r * c r) = 0 := hzero
  have hsum : (∑ r, z r * slack r) = 0 := by
    have hsplit : (∑ r, z r * slack r)
        = (∑ r, z r * (H (src r) - ∑ v, P r v * H v)) - ∑ r, z r * c r := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hslack]
      dsimp only
      ring
    rw [hsplit, hdrift, hcharge, sub_zero]
  have hterms : ∀ r ∈ (Finset.univ : Finset R), 0 ≤ z r * slack r := by
    intro r _
    exact mul_nonneg (le_of_lt (hzpos r)) (hnonneg r)
  have hzeroes := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsum
  intro r
  have hr := hzeroes r (Finset.mem_univ r)
  rcases mul_eq_zero.mp hr with hz0 | hs0
  · exact absurd hz0 (ne_of_gt (hzpos r))
  · rw [hslack] at hs0
    dsimp only at hs0
    linarith

/-- **Hard direction, under the full-support hypothesis.**  If every
circulation pairs to exactly zero with `c` and some circulation charges every
row, then `c` is an exact coboundary.  Part C: the cycle-quotient
criterion becomes sufficient once the nonnegative cycle cone spans the signed
cycle space. -/
theorem exists_isExactBridge_of_neutralHolonomy {src : R → V} {P : R → V → ℝ}
    {c : R → ℝ} (hfull : HasFullSupportCirculation src P)
    (h : NeutralHolonomy src P c) : ∃ H : V → ℝ, IsExactBridge src P c H := by
  obtain ⟨z, hz, hzpos⟩ := hfull
  obtain ⟨H, hH⟩ :=
    exists_accountPotential_of_zeroHolonomy
      ((neutralHolonomy_iff_zeroHolonomy_pair src P c).mp h).1
  exact ⟨H, isExactBridge_of_accountPotential_of_pos_circulation hz hzpos
    (h z hz) hH⟩

/-- **Main theorem (two-sided reduction).**  Under the full-support
circulation hypothesis, an exact account bridge exists exactly when the charge
cochain glues in *both* orientations.  The `→` direction is unconditional
(`neutralHolonomy_of_exists_isExactBridge`); the `←` direction needs the
hypothesis, and `ParallelRows.not_exists_isExactBridge_charge` shows it cannot
be dropped. -/
theorem exists_isExactBridge_iff_zeroHolonomy_pair {src : R → V}
    {P : R → V → ℝ} {c : R → ℝ} (hfull : HasFullSupportCirculation src P) :
    (∃ H : V → ℝ, IsExactBridge src P c H)
      ↔ ZeroHolonomy src P c ∧ ZeroHolonomy src P fun r => -(c r) := by
  rw [← neutralHolonomy_iff_zeroHolonomy_pair]
  exact ⟨neutralHolonomy_of_exists_isExactBridge,
    exists_isExactBridge_of_neutralHolonomy hfull⟩

/-- **Main theorem, ledger form.**  Under the full-support circulation
hypothesis the two notions coincide: one ledger per orientation
already forces a single two-sided account. -/
theorem exists_isExactBridge_iff_hasBothOrientations {src : R → V}
    {P : R → V → ℝ} {c : R → ℝ} (hfull : HasFullSupportCirculation src P) :
    (∃ H : V → ℝ, IsExactBridge src P c H) ↔ HasBothOrientations src P c := by
  rw [hasBothOrientations_iff_zeroHolonomy_pair]
  exact exists_isExactBridge_iff_zeroHolonomy_pair hfull

end General

/-! ### The parallel-rows separation

Two rows leaving the same source vertex `false` and both landing
deterministically on `true`.  Nothing ever returns, so the *only* circulation
is `0`: the cycle criterion is vacuously satisfied by every charge cochain and
every charge carries both orientations.  Yet an exact bridge would force the
two rows to carry the *same* charge, since both drifts equal
`H false - H true`.  This separates `HasBothOrientations` from
`IsExactBridge`, and shows the full-support hypothesis in
`exists_isExactBridge_iff_zeroHolonomy_pair` is necessary. -/

namespace ParallelRows

/-- Both rows are sourced at the vertex `false`. -/
def src : Bool → Bool := fun _ => false

/-- Both rows move deterministically to the vertex `true`. -/
def transition : Bool → Bool → ℝ := fun _ v => if v then 1 else 0

/-- Row `false` carries charge `1`, row `true` carries charge `0`. -/
def charge : Bool → ℝ := fun r => if r then 0 else 1

theorem isStochastic_transition : IsStochastic transition := by
  refine ⟨fun r v => ?_, fun r => ?_⟩
  · cases v <;> norm_num [transition]
  · norm_num [transition, Fintype.sum_bool]

/-- **(a)** The only circulation is the zero flow: the balance equation at the
source vertex reads `x false + x true = 0`. -/
theorem circulation_eq_zero {x : Bool → ℝ} (hx : IsCirculation src transition x) :
    x = 0 := by
  have hbal := hx.balanced false
  have h0 := hx.nonneg false
  have h1 := hx.nonneg true
  norm_num [incidence, src, transition, Fintype.sum_bool] at hbal
  funext r
  cases r with
  | false => simpa using by linarith
  | true => simpa using by linarith

/-- **(b)** Consequently *every* charge cochain satisfies the gluing
condition, in both orientations. -/
theorem zeroHolonomy_any (c : Bool → ℝ) : ZeroHolonomy src transition c := by
  intro x hx
  rw [circulation_eq_zero hx, holonomy]
  simp

/-- **(c)** Every charge carries one ledger per orientation. -/
theorem hasBothOrientations_any (c : Bool → ℝ) :
    HasBothOrientations src transition c :=
  (hasBothOrientations_iff_zeroHolonomy_pair src transition c).mpr
    ⟨zeroHolonomy_any c, zeroHolonomy_any _⟩

/-- **(d)** Yet no exact bridge exists for `charge`: both rows have the same
drift `H false - H true`, so an exact bridge would force `1 = 0`. -/
theorem not_exists_isExactBridge_charge :
    ¬ ∃ H : Bool → ℝ, IsExactBridge src transition charge H := by
  rintro ⟨H, hH⟩
  have h0 := hH false
  have h1 := hH true
  norm_num [charge, src, transition, Fintype.sum_bool] at h0 h1
  linarith

/-- **(e)** The full-support hypothesis genuinely fails here. -/
theorem not_hasFullSupportCirculation :
    ¬ HasFullSupportCirculation src transition := by
  rintro ⟨z, hz, hzpos⟩
  have hz0 := hzpos false
  rw [circulation_eq_zero hz] at hz0
  simp at hz0

end ParallelRows

/-! ### The one-state orientation falsifier

The *pure common-orientation obstruction*.
One public mode, one row, a self-loop, and a strictly negative charge `a`.

The unique normalized circulation is the constant `1`; it pairs to `a` with
the charge.  So the credit ledger exists — `H = 0` discharges `a ≤ 0` — while
the debit ledger for `-a > 0` cannot exist: the self-loop circulation is the
Farkas witness `φ(e) = 1`.  Here the *full-support* hypothesis
`hasFullSupportCirculation` **holds**, so this is not a connectivity failure:
it is a pure orientation failure that a full-support hypothesis alone cannot
rule out. -/

namespace SelfLoop

/-- The unique row is sourced at the unique public mode. -/
def src : Unit → Unit := fun _ => ()

/-- The unique row returns to the unique public mode: a self-loop. -/
def transition : Unit → Unit → ℝ := fun _ _ => 1

/-- The unique row carries the scalar charge `a`. -/
def charge (a : ℝ) : Unit → ℝ := fun _ => a

/-- The unit occupation, the unique normalized circulation. -/
def occupation : Unit → ℝ := fun _ => 1

theorem isStochastic_transition : IsStochastic transition := by
  refine ⟨fun r v => ?_, fun r => ?_⟩
  · norm_num [transition]
  · simp [transition]

/-- **(a)** The unit occupation is a normalized circulation. -/
theorem isNormalizedCirculation_occupation :
    IsNormalizedCirculation src transition occupation := by
  refine ⟨⟨fun r => ?_, fun v => ?_⟩, ?_⟩
  · norm_num [occupation]
  · simp [incidence, src, transition, occupation]
  · simp [occupation]

/-- **(b)** The full-support hypothesis holds: the self-loop is recurrent. -/
theorem hasFullSupportCirculation : HasFullSupportCirculation src transition :=
  ⟨occupation, isNormalizedCirculation_occupation.toIsCirculation, fun _ => by
    norm_num [occupation]⟩

/-- The holonomy of the unit occupation is the charge itself. -/
theorem holonomy_occupation (a : ℝ) :
    holonomy (charge a) occupation = a := by
  simp [holonomy, charge, occupation]

/-- **(c)** The credit ledger exists for a nonpositive charge: the zero
potential discharges it. -/
theorem accountPotential_zero {a : ℝ} (ha : a ≤ 0) :
    IsAccountPotential src transition (charge a) (0 : Unit → ℝ) := by
  intro r
  simpa [charge] using ha

/-- **(d)** For a strictly negative charge the *opposite* orientation fails
the gluing condition: the self-loop circulation has holonomy `-a > 0`. -/
theorem not_zeroHolonomy_neg {a : ℝ} (ha : a < 0) :
    ¬ ZeroHolonomy src transition fun r => -(charge a r) := by
  intro hzero
  have hle :=
    hzero occupation isNormalizedCirculation_occupation.toIsCirculation
  rw [holonomy_neg, holonomy_occupation] at hle
  linarith

/-- **(e)** Hence no debit ledger exists at all. -/
theorem not_exists_accountPotential_neg {a : ℝ} (ha : a < 0) :
    ¬ ∃ H : Unit → ℝ, IsAccountPotential src transition
      (fun r => -(charge a r)) H :=
  fun h => not_zeroHolonomy_neg ha (zeroHolonomy_of_exists_accountPotential h)

/-- **(f)** The pure orientation obstruction: one orientation is realizable,
the other is not, so the charge does not carry both orientations. -/
theorem not_hasBothOrientations {a : ℝ} (ha : a < 0) :
    ¬ HasBothOrientations src transition (charge a) :=
  fun h => not_exists_accountPotential_neg ha h.2

/-- **(g)** A fortiori there is no exact bridge, even though the one-sided
ledger of `accountPotential_zero` exists and the full-support hypothesis
holds. -/
theorem not_exists_isExactBridge {a : ℝ} (ha : a < 0) :
    ¬ ∃ H : Unit → ℝ, IsExactBridge src transition (charge a) H :=
  fun h => not_hasBothOrientations ha (hasBothOrientations_of_isExactBridge h)

/-- **(h)** The one-sided datum that survives: the credit ledger is really
there, so this is an orientation obstruction and not an outright
infeasibility. -/
theorem exists_accountPotential {a : ℝ} (ha : a < 0) :
    ∃ H : Unit → ℝ, IsAccountPotential src transition (charge a) H :=
  ⟨0, accountPotential_zero (le_of_lt ha)⟩

end SelfLoop

end

end OrientedAccountBridge
end LinearAlgebra
end Math
