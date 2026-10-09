import GameTheory.Finite.BimatrixBooleanGate

/-! Both Boolean outputs occur in accepted certificates for a conjunction that
reads the same input twice. The gate theorem applies without distinct-input assumptions. -/
namespace GameTheory.Tests.BimatrixBooleanGate
open GameTheory.Finite GameTheory.Finite.BimatrixBooleanGate
open GameTheory.Finite.BimatrixGateProgram
open GameTheory.Finite.BimatrixAffineGate
open GameTheory.Finite.BimatrixBlockGame
open scoped BigOperators

def selfAnd : Fin 1 → Gate 1 := fun _ => andGate 0 0

def falseCertificate : BimatrixCertificate 2 2 where
  rowDenominator := 1
  colDenominator := 1
  rowWeights := ![1, 0]
  colWeights := ![0, 1]
  rowUtilityNumerator := 12
  colUtilityNumerator := -7

def trueCertificate : BimatrixCertificate 2 2 where
  rowDenominator := 1
  colDenominator := 1
  rowWeights := ![0, 1]
  colWeights := ![1, 0]
  rowUtilityNumerator := 12
  colUtilityNumerator := -7

theorem falseCertificate_valid :
    falseCertificate.Valid (rowPayoff 10 2) (columnPayoff 10 2 selfAnd) := by decide

theorem trueCertificate_valid :
    trueCertificate.Valid (rowPayoff 10 2) (columnPayoff 10 2 selfAnd) := by decide

theorem selfAnd_bound : ∀ i r, |(selfAnd i).coefficients r| ≤ 7 := by
  intro i r
  exact andGate_coefficients_bound 0 0 r

theorem selfAnd_false : value (k := 1) falseCertificate 0 = 0 := by
  have h := andGate_value 10 7 (by decide : 0 < 1) selfAnd falseCertificate
    falseCertificate_valid (by decide) selfAnd_bound (by decide) 0 0 0 rfl
    false false 0 (by norm_num [value, falseCertificate, finProdFinEquiv])
    (by norm_num [value, falseCertificate, finProdFinEquiv]) (by norm_num)
  exact h

theorem selfAnd_true : value (k := 1) trueCertificate 0 =
    blockMass (k := 1) trueCertificate.rowWeights trueCertificate.rowDenominator 0 := by
  have h := andGate_value 10 7 (by decide : 0 < 1) selfAnd trueCertificate
    trueCertificate_valid (by decide) selfAnd_bound (by decide) 0 0 0 rfl
    true true 0 (by norm_num [value, trueCertificate, finProdFinEquiv])
    (by norm_num [value, trueCertificate, finProdFinEquiv]) (by norm_num)
  exact h

end GameTheory.Tests.BimatrixBooleanGate
