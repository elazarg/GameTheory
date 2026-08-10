/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Tactic

/-!
# Survival-weighted raw obstructions

This file provides a small generic algebra for nonnegative raw charges carried
by killed or absorbing blocks.

A raw charge is a nonnegative real vector.  A block pairs such a charge with a
survival factor in `[0,1]`.  Chronological concatenation is

```text
survival(x ++ y) = survival(x) * survival(y),
charge(x ++ y)   = charge(x) + survival(x) • charge(y).
```

Thus raw charges have survival grade one.  The construction is associative and
has the zero-charge, unit-survival block as an identity.

An annotated block additionally carries entry and exit values.  For compatible
blocks, endpoint displacement is an ordinary coboundary:

```text
displacement(x ++ y) = displacement(x) + displacement(y).
```

It therefore has grade zero, not grade one.  If
`A = 1 - survival` and `ξ = displacement / A`, then concatenation satisfies

```text
A(x ++ y) = A(x) + survival(x) * A(y),
A(x ++ y) * ξ(x ++ y) = A(x) * ξ(x) + A(y) * ξ(y).
```

The missing survival factor in the second occurrence of `A(y)` is deliberate:
the tangent numerator is a coboundary, whereas the absorption clock is a killed
charge.  This grading distinction is the durable content of the tangent
calculation.

The module is intentionally independent of games, probability distributions,
compactness, and strategic realizability.  Clients choose the charge-channel
type and supply any domain-specific adapters separately.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace SurvivalWeightedObstruction

/-! ## The nonnegative raw-charge cone -/

/-- A finite- or infinite-coordinate raw charge with pointwise nonnegative
real mass.  The coordinate type is deliberately unconstrained. -/
structure NonnegativeCharge (κ : Type*) where
  value : κ → ℝ
  nonneg : ∀ channel, 0 ≤ value channel

namespace NonnegativeCharge

variable {κ : Type*}

@[ext]
theorem ext {x y : NonnegativeCharge κ}
    (h : ∀ channel, x.value channel = y.value channel) : x = y := by
  cases x with
  | mk x hx =>
    cases y with
    | mk y hy =>
      have hxy : x = y := funext h
      subst y
      rfl

/-- The origin of the raw-charge cone. -/
def zero : NonnegativeCharge κ where
  value := 0
  nonneg := fun _ ↦ le_rfl

/-- Coordinatewise addition of raw charges. -/
def add (x y : NonnegativeCharge κ) : NonnegativeCharge κ where
  value := fun channel ↦ x.value channel + y.value channel
  nonneg := fun channel ↦ add_nonneg (x.nonneg channel) (y.nonneg channel)

/-- Nonnegative scalar multiplication in the raw-charge cone. -/
def scale (a : ℝ) (ha : 0 ≤ a)
    (x : NonnegativeCharge κ) : NonnegativeCharge κ where
  value := fun channel ↦ a * x.value channel
  nonneg := fun channel ↦ mul_nonneg ha (x.nonneg channel)

@[simp]
theorem zero_value (channel : κ) :
    (zero : NonnegativeCharge κ).value channel = 0 := rfl

@[simp]
theorem add_value (x y : NonnegativeCharge κ) (channel : κ) :
    (add x y).value channel = x.value channel + y.value channel := rfl

@[simp]
theorem scale_value (a : ℝ) (ha : 0 ≤ a)
    (x : NonnegativeCharge κ) (channel : κ) :
    (scale a ha x).value channel = a * x.value channel := rfl

@[simp]
theorem add_zero (x : NonnegativeCharge κ) : add x zero = x := by
  ext channel
  simp

@[simp]
theorem zero_add (x : NonnegativeCharge κ) : add zero x = x := by
  ext channel
  simp

theorem add_assoc (x y z : NonnegativeCharge κ) :
    add (add x y) z = add x (add y z) := by
  ext channel
  simp only [add_value]
  ring

theorem add_comm (x y : NonnegativeCharge κ) : add x y = add y x := by
  ext channel
  simp only [add_value]
  ring

@[simp]
theorem scale_zero (a : ℝ) (ha : 0 ≤ a) :
    scale a ha (zero : NonnegativeCharge κ) = zero := by
  ext channel
  simp

@[simp]
theorem zero_scale (x : NonnegativeCharge κ) :
    scale 0 le_rfl x = zero := by
  ext channel
  simp

@[simp]
theorem one_scale (x : NonnegativeCharge κ) :
    scale 1 zero_le_one x = x := by
  ext channel
  simp

theorem scale_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (x : NonnegativeCharge κ) :
    scale (a + b) (add_nonneg ha hb) x =
      add (scale a ha x) (scale b hb x) := by
  ext channel
  simp only [scale_value, add_value]
  ring

theorem scale_add_charge (a : ℝ) (ha : 0 ≤ a)
    (x y : NonnegativeCharge κ) :
    scale a ha (add x y) = add (scale a ha x) (scale a ha y) := by
  ext channel
  simp only [scale_value, add_value]
  ring

theorem scale_scale (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (x : NonnegativeCharge κ) :
    scale a ha (scale b hb x) =
      scale (a * b) (mul_nonneg ha hb) x := by
  ext channel
  simp only [scale_value]
  ring

end NonnegativeCharge

/-! ## Survival-weighted blocks -/

/-- A nonnegative raw charge equipped with a survival factor in `[0,1]`. -/
structure Block (κ : Type*) where
  survival : ℝ
  survival_nonneg : 0 ≤ survival
  survival_le_one : survival ≤ 1
  charge : NonnegativeCharge κ

namespace Block

variable {κ : Type*}

@[ext]
theorem ext {x y : Block κ}
    (hsurvival : x.survival = y.survival)
    (hcharge : x.charge = y.charge) : x = y := by
  cases x with
  | mk xs xs0 xs1 xc =>
    cases y with
    | mk ys ys0 ys1 yc =>
      simp only at hsurvival hcharge
      subst ys
      subst yc
      rfl

/-- The chronological identity: certain survival and no raw charge. -/
def identity : Block κ where
  survival := 1
  survival_nonneg := zero_le_one
  survival_le_one := le_rfl
  charge := NonnegativeCharge.zero

/-- Chronological concatenation.  The later charge is paid only on the mass
which survives the earlier block. -/
def concat (earlier later : Block κ) : Block κ where
  survival := earlier.survival * later.survival
  survival_nonneg :=
    mul_nonneg earlier.survival_nonneg later.survival_nonneg
  survival_le_one := by
    calc
      earlier.survival * later.survival ≤ 1 * later.survival :=
        mul_le_mul_of_nonneg_right earlier.survival_le_one
          later.survival_nonneg
      _ = later.survival := one_mul _
      _ ≤ 1 := later.survival_le_one
  charge := NonnegativeCharge.add earlier.charge
    (NonnegativeCharge.scale earlier.survival
      earlier.survival_nonneg later.charge)

@[simp]
theorem identity_survival : (identity : Block κ).survival = 1 := rfl

@[simp]
theorem identity_charge :
    (identity : Block κ).charge = NonnegativeCharge.zero := rfl

@[simp]
theorem concat_survival (earlier later : Block κ) :
    (concat earlier later).survival = earlier.survival * later.survival := rfl

@[simp]
theorem concat_charge_value (earlier later : Block κ) (channel : κ) :
    (concat earlier later).charge.value channel =
      earlier.charge.value channel +
        earlier.survival * later.charge.value channel := rfl

@[simp]
theorem identity_concat (block : Block κ) : concat identity block = block := by
  apply Block.ext
  · simp
  · ext channel
    simp

@[simp]
theorem concat_identity (block : Block κ) : concat block identity = block := by
  apply Block.ext
  · simp
  · ext channel
    simp

/-- Associativity of chronological concatenation. -/
theorem concat_assoc (first second third : Block κ) :
    concat (concat first second) third =
      concat first (concat second third) := by
  apply Block.ext
  · simp only [concat_survival]
    ring
  · ext channel
    simp only [concat_charge_value, concat_survival]
    ring

/-- The literal mass killed by the block. -/
def absorbedMass (block : Block κ) : ℝ := 1 - block.survival

theorem absorbedMass_nonneg (block : Block κ) : 0 ≤ block.absorbedMass :=
  sub_nonneg.mpr block.survival_le_one

theorem absorbedMass_le_one (block : Block κ) : block.absorbedMass ≤ 1 := by
  unfold absorbedMass
  linarith [block.survival_nonneg]

@[simp]
theorem absorbedMass_identity : (identity : Block κ).absorbedMass = 0 := by
  simp [absorbedMass]

/-- Absorption itself is a survival-grade-one charge. -/
theorem absorbedMass_concat (earlier later : Block κ) :
    (concat earlier later).absorbedMass =
      earlier.absorbedMass + earlier.survival * later.absorbedMass := by
  simp only [absorbedMass, concat_survival]
  ring

/-- Scale every raw charge channel without changing the block's survival
clock. -/
def scaleCharge (a : ℝ) (ha : 0 ≤ a) (block : Block κ) : Block κ where
  survival := block.survival
  survival_nonneg := block.survival_nonneg
  survival_le_one := block.survival_le_one
  charge := NonnegativeCharge.scale a ha block.charge

@[simp]
theorem scaleCharge_survival (a : ℝ) (ha : 0 ≤ a) (block : Block κ) :
    (scaleCharge a ha block).survival = block.survival := rfl

@[simp]
theorem one_scaleCharge (block : Block κ) :
    scaleCharge 1 zero_le_one block = block := by
  apply Block.ext
  · rfl
  · exact NonnegativeCharge.one_scale block.charge

theorem scaleCharge_scaleCharge (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (block : Block κ) :
    scaleCharge a ha (scaleCharge b hb block) =
      scaleCharge (a * b) (mul_nonneg ha hb) block := by
  apply Block.ext
  · rfl
  · exact NonnegativeCharge.scale_scale a b ha hb block.charge

/-- Scaling raw charges commutes with chronological concatenation. -/
theorem scaleCharge_concat (a : ℝ) (ha : 0 ≤ a)
    (earlier later : Block κ) :
    scaleCharge a ha (concat earlier later) =
      concat (scaleCharge a ha earlier) (scaleCharge a ha later) := by
  apply Block.ext
  · rfl
  · ext channel
    simp only [scaleCharge, concat_charge_value,
      NonnegativeCharge.scale_value]
    ring

end Block

/-! ## Annotated blocks and the grading-correct tangent -/

/-- A survival-weighted raw block with source and target value annotations. -/
structure AnnotatedBlock (κ ν : Type*) where
  block : Block κ
  entryValue : ν → ℝ
  exitValue : ν → ℝ

namespace AnnotatedBlock

variable {κ ν : Type*}

@[ext]
theorem ext {x y : AnnotatedBlock κ ν}
    (hblock : x.block = y.block)
    (hentry : x.entryValue = y.entryValue)
    (hexit : x.exitValue = y.exitValue) : x = y := by
  cases x
  cases y
  simp_all

/-- The identity block based at a specified value annotation. -/
def identityAt (value : ν → ℝ) : AnnotatedBlock κ ν where
  block := Block.identity
  entryValue := value
  exitValue := value

/-- The seam condition required for source-typed concatenation. -/
def Compatible (earlier later : AnnotatedBlock κ ν) : Prop :=
  earlier.exitValue = later.entryValue

/-- Concatenation retains the outer endpoints and concatenates the killed raw
blocks chronologically. -/
def concat (earlier later : AnnotatedBlock κ ν) : AnnotatedBlock κ ν where
  block := Block.concat earlier.block later.block
  entryValue := earlier.entryValue
  exitValue := later.exitValue

theorem compatible_identityAt_left (block : AnnotatedBlock κ ν) :
    Compatible (identityAt block.entryValue) block := rfl

theorem compatible_identityAt_right (block : AnnotatedBlock κ ν) :
    Compatible block (identityAt block.exitValue) := rfl

@[simp]
theorem identityAt_concat (block : AnnotatedBlock κ ν) :
    concat (identityAt block.entryValue) block = block := by
  apply AnnotatedBlock.ext
  · exact Block.identity_concat block.block
  · rfl
  · rfl

@[simp]
theorem concat_identityAt (block : AnnotatedBlock κ ν) :
    concat block (identityAt block.exitValue) = block := by
  apply AnnotatedBlock.ext
  · exact Block.concat_identity block.block
  · rfl
  · rfl

theorem concat_assoc (first second third : AnnotatedBlock κ ν) :
    concat (concat first second) third = concat first (concat second third) := by
  apply AnnotatedBlock.ext
  · exact Block.concat_assoc first.block second.block third.block
  · rfl
  · rfl

def endpointDisplacement (block : AnnotatedBlock κ ν) (coordinate : ν) : ℝ :=
  block.entryValue coordinate - block.exitValue coordinate

/-- Endpoint displacement is a grade-zero coboundary. -/
theorem endpointDisplacement_concat
    (earlier later : AnnotatedBlock κ ν)
    (hcompatible : earlier.Compatible later) (coordinate : ν) :
    (concat earlier later).endpointDisplacement coordinate =
      earlier.endpointDisplacement coordinate +
        later.endpointDisplacement coordinate := by
  rw [Compatible] at hcompatible
  have hcoordinate := congrFun hcompatible coordinate
  simp only [endpointDisplacement, concat]
  rw [hcoordinate]
  ring

/-- Absorption-clock tangent, totalized to zero at zero absorbed mass. -/
def tangent (block : AnnotatedBlock κ ν) (coordinate : ν) : ℝ :=
  block.endpointDisplacement coordinate / block.block.absorbedMass

/-- The exact finite-scale tangent identity. -/
theorem eq_tangent_iff
    (block : AnnotatedBlock κ ν) (coordinate : ν)
    (hmass : block.block.absorbedMass ≠ 0) (ξ : ℝ) :
    ξ = block.tangent coordinate ↔
      block.block.absorbedMass * ξ =
        block.endpointDisplacement coordinate := by
  rw [tangent, eq_div_iff hmass]
  ring_nf

/-- **Grading-correct tangent numerator.**  The absorption clock of the later
block is survival-weighted in `Block.absorbedMass_concat`, but its endpoint
coboundary enters this numerator without that survival factor. -/
theorem absorbedMass_mul_tangent_concat
    (earlier later : AnnotatedBlock κ ν)
    (hcompatible : earlier.Compatible later) (coordinate : ν)
    (htotal : (concat earlier later).block.absorbedMass ≠ 0)
    (hearlier : earlier.block.absorbedMass ≠ 0)
    (hlater : later.block.absorbedMass ≠ 0) :
    (concat earlier later).block.absorbedMass *
        (concat earlier later).tangent coordinate =
      earlier.block.absorbedMass * earlier.tangent coordinate +
        later.block.absorbedMass * later.tangent coordinate := by
  unfold tangent
  rw [mul_div_cancel₀ _ htotal,
    mul_div_cancel₀ _ hearlier,
    mul_div_cancel₀ _ hlater,
    endpointDisplacement_concat earlier later hcompatible]

/-- Quotient form of the grading-correct tangent concatenation law. -/
theorem tangent_concat
    (earlier later : AnnotatedBlock κ ν)
    (hcompatible : earlier.Compatible later) (coordinate : ν)
    (htotal : (concat earlier later).block.absorbedMass ≠ 0)
    (hearlier : earlier.block.absorbedMass ≠ 0)
    (hlater : later.block.absorbedMass ≠ 0) :
    (concat earlier later).tangent coordinate =
      (earlier.block.absorbedMass * earlier.tangent coordinate +
          later.block.absorbedMass * later.tangent coordinate) /
        (earlier.block.absorbedMass +
          earlier.block.survival * later.block.absorbedMass) := by
  have hdenominator :
      earlier.block.absorbedMass +
          earlier.block.survival * later.block.absorbedMass ≠ 0 := by
    rw [← Block.absorbedMass_concat]
    exact htotal
  apply (eq_div_iff hdenominator).2
  rw [← Block.absorbedMass_concat]
  rw [mul_comm]
  exact absorbedMass_mul_tangent_concat earlier later hcompatible coordinate
    htotal hearlier hlater

end AnnotatedBlock

end SurvivalWeightedObstruction
end Math
