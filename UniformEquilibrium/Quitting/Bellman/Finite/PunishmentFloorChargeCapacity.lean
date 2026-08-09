/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefix

/-!
# Canonical punishment-floor prefix-charge capacity

This module replaces an arbitrary real upper bound on exact punishment-floor
prefixes by the canonical extended-nonnegative capacity

`sup { charge(cert) | cert is an exact punishment-floor prefix }`.

The value `⊤` records genuine unboundedness.  When the capacity is finite, its
real value is the least nonnegative real upper bound on every exact prefix
charge.  No attainment of the supremum is asserted.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Extended-nonnegative supremum of all exact punishment-floor prefix
charges. -/
def quittingPunishmentFloorPrefixChargeCapacity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ENNReal :=
  ⨆ cert : QuittingPunishmentFloorFinitePrefix reward,
    ENNReal.ofReal cert.charge

/-- Real-valued canonical prefix-charge bound.  It has its intended
least-upper-bound meaning when the extended capacity is finite. -/
def quittingPunishmentFloorPrefixChargeBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  (quittingPunishmentFloorPrefixChargeCapacity reward).toReal

/-- The real canonical prefix-charge bound is nonnegative. -/
theorem quittingPunishmentFloorPrefixChargeBound_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    0 ≤ quittingPunishmentFloorPrefixChargeBound reward :=
  ENNReal.toReal_nonneg

/-- Every exact prefix charge lies below the canonical capacity. -/
theorem punishmentFloorPrefixCharge_le_capacity
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    ENNReal.ofReal cert.charge ≤
      quittingPunishmentFloorPrefixChargeCapacity reward :=
  le_iSup
    (fun prefixCert : QuittingPunishmentFloorFinitePrefix reward ↦
      ENNReal.ofReal prefixCert.charge) cert

/-- Least-upper-bound characterization against a nonnegative real
candidate. -/
theorem punishmentFloorPrefixChargeCapacity_le_ofReal_iff
    {bound : ℝ} (hbound : 0 ≤ bound) :
    quittingPunishmentFloorPrefixChargeCapacity reward ≤
        ENNReal.ofReal bound ↔
      ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
        cert.charge ≤ bound := by
  constructor
  · intro hcapacity cert
    apply (ENNReal.ofReal_le_ofReal_iff hbound).mp
    exact (punishmentFloorPrefixCharge_le_capacity cert).trans hcapacity
  · intro hall
    apply iSup_le
    intro cert
    exact ENNReal.ofReal_le_ofReal (hall cert)

/-- Finiteness of the extended capacity is equivalent to existence of a
finite nonnegative real bound on all exact prefix charges. -/
theorem punishmentFloorPrefixChargeCapacity_ne_top_iff :
    quittingPunishmentFloorPrefixChargeCapacity reward ≠ ⊤ ↔
      ∃ bound : ℝ, 0 ≤ bound ∧
        ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
          cert.charge ≤ bound := by
  constructor
  · intro hfinite
    refine ⟨(quittingPunishmentFloorPrefixChargeCapacity reward).toReal,
      ENNReal.toReal_nonneg, ?_⟩
    intro cert
    apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
    exact punishmentFloorPrefixCharge_le_capacity cert
  · rintro ⟨bound, hbound, hall⟩
    have hcapacity :
        quittingPunishmentFloorPrefixChargeCapacity reward ≤
          ENNReal.ofReal bound :=
      (punishmentFloorPrefixChargeCapacity_le_ofReal_iff hbound).2 hall
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcapacity

/-- The capacity is `⊤` exactly when every nonnegative real target is
strictly exceeded by some finite exact prefix. -/
theorem punishmentFloorPrefixChargeCapacity_eq_top_iff :
    quittingPunishmentFloorPrefixChargeCapacity reward = ⊤ ↔
      ∀ target : ℝ, 0 ≤ target →
        ∃ cert : QuittingPunishmentFloorFinitePrefix reward,
          target < cert.charge := by
  classical
  constructor
  · intro htop target htarget
    by_contra hno
    have hall : ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
        cert.charge ≤ target := by
      intro cert
      exact le_of_not_gt fun hgt ↦ hno ⟨cert, hgt⟩
    have hcapacity :
        quittingPunishmentFloorPrefixChargeCapacity reward ≤
          ENNReal.ofReal target :=
      (punishmentFloorPrefixChargeCapacity_le_ofReal_iff htarget).2 hall
    rw [htop] at hcapacity
    exact ENNReal.ofReal_ne_top (top_unique hcapacity)
  · intro hunbounded
    by_contra hfinite
    obtain ⟨bound, hbound, hall⟩ :=
      punishmentFloorPrefixChargeCapacity_ne_top_iff.mp hfinite
    obtain ⟨cert, hgt⟩ := hunbounded bound hbound
    exact (not_lt_of_ge (hall cert)) hgt

/-- When finite, the real capacity bounds every exact prefix charge. -/
theorem punishmentFloorPrefixCharge_le_capacity_toReal
    (hfinite : quittingPunishmentFloorPrefixChargeCapacity reward ≠ ⊤)
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    cert.charge ≤
      quittingPunishmentFloorPrefixChargeBound reward :=
  (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
    (punishmentFloorPrefixCharge_le_capacity cert)

/-- When finite, the real capacity is the least nonnegative real upper bound
on all exact prefix charges. -/
theorem punishmentFloorPrefixChargeCapacity_toReal_le_iff
    (hfinite : quittingPunishmentFloorPrefixChargeCapacity reward ≠ ⊤)
    {bound : ℝ} (hbound : 0 ≤ bound) :
    quittingPunishmentFloorPrefixChargeBound reward ≤ bound ↔
      ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
        cert.charge ≤ bound := by
  unfold quittingPunishmentFloorPrefixChargeBound
  rw [← ENNReal.le_ofReal_iff_toReal_le hfinite hbound]
  exact punishmentFloorPrefixChargeCapacity_le_ofReal_iff hbound

end GameTheory
