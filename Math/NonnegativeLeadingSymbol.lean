/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Data.NNReal.Basic
import Mathlib.RingTheory.Congruence.Basic

/-!
# Leading symbols of nonnegative curves

For a filter `l`, two nonnegative real-valued curves have the same leading
symbol when their real coercions are asymptotically equivalent along `l`.
Nonnegativity is the load-bearing condition that makes addition compatible
with this equivalence.  Multiplication is compatible by the usual product
rule for asymptotic equivalence.

The resulting quotient is a commutative semiring.  Consequently every exact
finite identity made from sums and products descends to leading symbols.  The
last section records the product, simplex, successor-bundle, state-balance,
and cut shapes used by finite product flows.
-/

open Filter Finset BigOperators
open Asymptotics
open scoped NNReal

namespace Math

noncomputable section

universe uα uJ

variable {α : Type uα}

/-- View an `NNReal`-valued curve as a nonnegative real-valued curve. -/
def nnrealCurveToReal (curve : α → ℝ≥0) : α → ℝ :=
  fun index => curve index

@[simp] theorem nnrealCurveToReal_zero :
    nnrealCurveToReal (0 : α → ℝ≥0) = 0 :=
  rfl

@[simp] theorem nnrealCurveToReal_one :
    nnrealCurveToReal (1 : α → ℝ≥0) = 1 :=
  rfl

@[simp] theorem nnrealCurveToReal_add (first second : α → ℝ≥0) :
    nnrealCurveToReal (first + second) =
      nnrealCurveToReal first + nnrealCurveToReal second :=
  rfl

@[simp] theorem nnrealCurveToReal_mul (first second : α → ℝ≥0) :
    nnrealCurveToReal (first * second) =
      nnrealCurveToReal first * nnrealCurveToReal second :=
  rfl

/-- Asymptotic equivalence of nonnegative curves is compatible with both
addition and multiplication. -/
def nonnegativeLeadingCongruence (l : Filter α) : RingCon (α → ℝ≥0) where
  r first second :=
    nnrealCurveToReal first ~[l] nnrealCurveToReal second
  iseqv.refl curve := IsEquivalent.refl
  iseqv.symm h := h.symm
  iseqv.trans hfirst hsecond := hfirst.trans hsecond
  add' {first first' second second'} hfirst hsecond := by
    change (fun index => (first index : ℝ)) ~[l]
      (fun index => (first' index : ℝ)) at hfirst
    change (fun index => (second index : ℝ)) ~[l]
      (fun index => (second' index : ℝ)) at hsecond
    change (fun index => (first index : ℝ) + (second index : ℝ)) ~[l]
      (fun index => (first' index : ℝ) + (second' index : ℝ))
    exact IsEquivalent.add_add_of_nonneg
      (fun index => NNReal.coe_nonneg (first' index))
      (fun index => NNReal.coe_nonneg (second' index)) hfirst hsecond
  mul' {first first' second second'} hfirst hsecond := by
    change (fun index => (first index : ℝ)) ~[l]
      (fun index => (first' index : ℝ)) at hfirst
    change (fun index => (second index : ℝ)) ~[l]
      (fun index => (second' index : ℝ)) at hsecond
    change (fun index => (first index : ℝ) * (second index : ℝ)) ~[l]
      (fun index => (first' index : ℝ) * (second' index : ℝ))
    exact hfirst.mul hsecond

/-- Leading symbols of nonnegative curves along `l`. -/
abbrev NonnegativeLeadingSymbol (l : Filter α) :=
  (nonnegativeLeadingCongruence l).Quotient

/-- The quotient map from nonnegative curves to their leading symbols. -/
def leadingSymbolHom (l : Filter α) :
    (α → ℝ≥0) →+* NonnegativeLeadingSymbol l :=
  (nonnegativeLeadingCongruence l).mk'

/-- Two curves have equal leading symbols exactly when they are
asymptotically equivalent after coercion to real curves. -/
theorem leadingSymbolHom_eq_iff (l : Filter α) (first second : α → ℝ≥0) :
    leadingSymbolHom l first = leadingSymbolHom l second ↔
      nnrealCurveToReal first ~[l] nnrealCurveToReal second := by
  exact (nonnegativeLeadingCongruence l).eq

@[simp] theorem leadingSymbolHom_zero (l : Filter α) :
    leadingSymbolHom l 0 = 0 :=
  map_zero (leadingSymbolHom l)

@[simp] theorem leadingSymbolHom_one (l : Filter α) :
    leadingSymbolHom l 1 = 1 :=
  map_one (leadingSymbolHom l)

@[simp] theorem leadingSymbolHom_add (l : Filter α)
    (first second : α → ℝ≥0) :
    leadingSymbolHom l (first + second) =
      leadingSymbolHom l first + leadingSymbolHom l second :=
  map_add (leadingSymbolHom l) first second

@[simp] theorem leadingSymbolHom_mul (l : Filter α)
    (first second : α → ℝ≥0) :
    leadingSymbolHom l (first * second) =
      leadingSymbolHom l first * leadingSymbolHom l second :=
  map_mul (leadingSymbolHom l) first second

@[simp] theorem leadingSymbolHom_sum {J : Type uJ} [Fintype J]
    (l : Filter α) (curve : J → α → ℝ≥0) :
    leadingSymbolHom l (∑ index, curve index) =
      ∑ index, leadingSymbolHom l (curve index) :=
  map_sum (leadingSymbolHom l) curve Finset.univ

@[simp] theorem leadingSymbolHom_prod {J : Type uJ} [Fintype J]
    (l : Filter α) (curve : J → α → ℝ≥0) :
    leadingSymbolHom l (∏ index, curve index) =
      ∏ index, leadingSymbolHom l (curve index) :=
  map_prod (leadingSymbolHom l) curve Finset.univ

section ExactIdentities

variable {l : Filter α}
  {J : Type uJ} [Fintype J]

/-- Exact product identities descend to the leading-symbol semiring. -/
theorem leading_product_identity
    {mass stock : α → ℝ≥0} {factor : J → α → ℝ≥0}
    (hproduct : mass = stock * ∏ index, factor index) :
    leadingSymbolHom l mass =
      leadingSymbolHom l stock *
        ∏ index, leadingSymbolHom l (factor index) := by
  rw [hproduct, leadingSymbolHom_mul, leadingSymbolHom_prod]

/-- Exact finite simplex identities descend to leading symbols. -/
theorem leading_simplex_identity
    {weight : J → α → ℝ≥0}
    (hsimplex : (∑ index, weight index) = 1) :
    (∑ index, leadingSymbolHom l (weight index)) = 1 := by
  rw [← leadingSymbolHom_sum, hsimplex, leadingSymbolHom_one]

/-- Fixed-kernel successor proportionality descends to leading symbols.  The
kernel weights are represented by constant or otherwise prescribed
nonnegative curves. -/
theorem leading_successor_bundle_identity
    {kernelFirst kernelSecond fluxFirst fluxSecond : α → ℝ≥0}
    (hsuccessor : kernelFirst * fluxSecond = kernelSecond * fluxFirst) :
    leadingSymbolHom l kernelFirst * leadingSymbolHom l fluxSecond =
      leadingSymbolHom l kernelSecond * leadingSymbolHom l fluxFirst := by
  rw [← leadingSymbolHom_mul, hsuccessor, leadingSymbolHom_mul]

/-- Exact nonnegative state balance descends before any residual subtraction. -/
theorem leading_state_balance_identity
    {stock resetSource : α → ℝ≥0}
    {incoming : J → α → ℝ≥0}
    (hbalance : stock = resetSource + ∑ edge, incoming edge) :
    leadingSymbolHom l stock =
      leadingSymbolHom l resetSource +
        ∑ edge, leadingSymbolHom l (incoming edge) := by
  rw [hbalance, leadingSymbolHom_add, leadingSymbolHom_sum]

/-- Exact cut balance descends before any residual subtraction. -/
theorem leading_cut_balance_identity
    {resetStock outgoing resetInitial incoming : α → ℝ≥0}
    (hcut : resetStock + outgoing = resetInitial + incoming) :
    leadingSymbolHom l resetStock + leadingSymbolHom l outgoing =
      leadingSymbolHom l resetInitial + leadingSymbolHom l incoming := by
  rw [← leadingSymbolHom_add, hcut, leadingSymbolHom_add]

end ExactIdentities

end

end Math
