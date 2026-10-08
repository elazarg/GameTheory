import GameTheory.Finite.BimatrixPivotSource
import GameTheory.Math.CanonicalDictionary
import GameTheory.Math.ComplementaryLabels
import Mathlib.Data.Prod.Lex

/-! Canonical feasible bases of the bimatrix complementarity system.
Basis variables form a finite set, so column permutations do not create new
nodes. Nonbasic variables carry the binding labels used by complementary paths.
-/
namespace GameTheory.Finite
open GameTheory.Math GameTheory.Math.CanonicalDictionary
variable {m n : ℕ}

/-- A slack or payoff variable, ordered by its label and then its kind. -/
abbrev BimatrixVariable (m n : ℕ) := Fin (m + n) ×ₗ Bool

/-- Columns of `w - M z = 1`, with false denoting slack variables. -/
def bimatrixBasisColumns (A B : Fin m → Fin n → ℤ) :
    Matrix (Fin (m + n)) (BimatrixVariable m n) ℚ := fun i v =>
  if (ofLex v).2 then bimatrixEnteringColumn A B (finSumFinEquiv.symm (ofLex v).1) i
  else (Pi.single (ofLex v).1 (1 : ℚ) : Fin (m + n) → ℚ) i

/-- An unordered basis certified invertible and strictly symbolically feasible. -/
structure BimatrixBasis (A B : Fin m → Fin n → ℤ) where
  /-- The unordered set of selected system columns. -/
  basic : Finset (BimatrixVariable m n)
  cardinality : basic.card = m + n
  feasible : IsFeasible (bimatrixBasisColumns A B) (fun _ => 1) basic cardinality

namespace BimatrixBasis
variable {A B : Fin m → Fin n → ℤ}

@[ext] theorem ext {basis other : BimatrixBasis A B} (h : basis.basic = other.basic) :
    basis = other := by
  cases basis
  cases other
  cases h
  rfl

/-- Nonbasic zero variables, with the ordering wrapper removed for label counting. -/
def nonbasic (basis : BimatrixBasis A B) : Finset (Fin (m + n) × Bool) :=
  (basis.basicᶜ).map ofLex.toEmbedding

@[simp] theorem mem_nonbasic (basis : BimatrixBasis A B) (v : Fin (m + n) × Bool) :
    v ∈ basis.nonbasic ↔ toLex v ∉ basis.basic := by
  simp [nonbasic]

theorem nonbasic_card (basis : BimatrixBasis A B) : basis.nonbasic.card = m + n := by
  simp only [nonbasic, Finset.card_map, Finset.card_compl, Fintype.card_lex,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, basis.cardinality]
  omega

/-- Nonbasic labels are complementary, or have one missing and one duplicated label. -/
theorem label_dichotomy (basis : BimatrixBasis A B) (d : Fin (m + n))
    (h : ComplementaryLabels.CoversExcept basis.nonbasic d) :
    ComplementaryLabels.IsComplementary basis.nonbasic ∨
      ((d, false) ∉ basis.nonbasic ∧ (d, true) ∉ basis.nonbasic) ∧
        ∃! i, (i, false) ∈ basis.nonbasic ∧ (i, true) ∈ basis.nonbasic :=
  ComplementaryLabels.complementary_or_unique_duplicate _ _
    (by simpa using basis.nonbasic_card) h

/-- Exchange a basic variable for a certified nonbasic entering variable. -/
def exchange (basis : BimatrixBasis A B) (l : Fin (m + n))
    (entering : BimatrixVariable m n) (he : entering ∉ basis.basic)
    (hl : IsLeavingRow (PerturbedDictionary.dictionaryCoefficients
      (basisMatrix (bimatrixBasisColumns A B) basis.basic basis.cardinality) (fun _ => 1))
      ((basisMatrix (bimatrixBasisColumns A B) basis.basic basis.cardinality)⁻¹.mulVec
        (fun i => bimatrixBasisColumns A B i entering)) l) : BimatrixBasis A B where
  basic := FiniteBasisExchange.exchange basis.basic
    (basis.basic.orderEmbOfFin basis.cardinality l) entering
  cardinality := (FiniteBasisExchange.card_exchange
    (Finset.orderEmbOfFin_mem basis.basic basis.cardinality l) he).trans basis.cardinality
  feasible := exchange_feasible _ _ _ _ basis.feasible l entering he hl

/-- Exchanging basis variables exchanges the zero-variable set in the reverse order. -/
theorem nonbasic_exchange (basis : BimatrixBasis A B) (l : Fin (m + n))
    (entering : BimatrixVariable m n) (he : entering ∉ basis.basic)
    (hl : IsLeavingRow (PerturbedDictionary.dictionaryCoefficients
      (basisMatrix (bimatrixBasisColumns A B) basis.basic basis.cardinality) (fun _ => 1))
      ((basisMatrix (bimatrixBasisColumns A B) basis.basic basis.cardinality)⁻¹.mulVec
        (fun i => bimatrixBasisColumns A B i entering)) l) :
    (basis.exchange l entering he hl).nonbasic = FiniteBasisExchange.exchange basis.nonbasic
      (ofLex entering) (ofLex (basis.basic.orderEmbOfFin basis.cardinality l)) := by
  unfold nonbasic exchange
  rw [FiniteBasisExchange.compl_exchange
    (Finset.orderEmbOfFin_mem basis.basic basis.cardinality l) he,
    FiniteBasisExchange.map_exchange]
  rfl


end BimatrixBasis

/-- The all-slack variable set defining the unique artificial source basis. -/
def bimatrixSlackVariables (m n : ℕ) : Finset (BimatrixVariable m n) :=
  Finset.univ.image (fun i : Fin (m + n) => toLex (i, false))

theorem bimatrixSlackVariables_card : (bimatrixSlackVariables m n).card = m + n := by
  rw [bimatrixSlackVariables, Finset.card_image_of_injective _]
  · exact Fintype.card_fin _
  · intro i j h
    exact congrArg (fun v => (ofLex v).1) h

theorem bimatrixSlack_basisMatrix (A B : Fin m → Fin n → ℤ) :
    basisMatrix (bimatrixBasisColumns A B) (bimatrixSlackVariables m n)
      bimatrixSlackVariables_card = 1 := by
  have he : (fun i : Fin (m + n) => toLex (i, false)) =
      (bimatrixSlackVariables m n).orderEmbOfFin bimatrixSlackVariables_card := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · intro i j hij
      exact Prod.Lex.left _ _ hij
  ext i j
  simp only [basisMatrix, ← he, bimatrixBasisColumns, ofLex_toLex, Bool.false_eq_true,
    ↓reduceIte, Matrix.one_apply, Pi.single_apply]

/-- The canonical all-slack source is feasible without a positivity premise on payoffs. -/
def bimatrixSourceBasis (A B : Fin m → Fin n → ℤ) : BimatrixBasis A B where
  basic := bimatrixSlackVariables m n
  cardinality := bimatrixSlackVariables_card
  feasible := by
    unfold IsFeasible
    rw [bimatrixSlack_basisMatrix]
    exact ⟨by simp, bimatrixSource_coefficients_positive⟩


/-- Almost complementary nodes enforce coverage of every label except the dropped one. -/
structure BimatrixPathNode (A B : Fin m → Fin n → ℤ) (d : Fin (m + n)) where
  /-- The invertible, strictly feasible canonical basis underlying the node. -/
  basis : BimatrixBasis A B
  coverage : ComplementaryLabels.CoversExcept basis.nonbasic d

namespace BimatrixPathNode
variable {A B : Fin m → Fin n → ℤ} {d : Fin (m + n)}

/-- A pivot stays almost complementary when it enters a dropped or duplicated zero label. -/
def exchange (node : BimatrixPathNode A B d) (l : Fin (m + n))
    (entering : BimatrixVariable m n) (he : entering ∉ node.basis.basic)
    (hl : IsLeavingRow (PerturbedDictionary.dictionaryCoefficients
      (basisMatrix (bimatrixBasisColumns A B) node.basis.basic node.basis.cardinality)
        (fun _ => 1))
      ((basisMatrix (bimatrixBasisColumns A B) node.basis.basic node.basis.cardinality)⁻¹.mulVec
        (fun i => bimatrixBasisColumns A B i entering)) l)
    (hlabel : (ofLex entering).1 = d ∨
      ((ofLex entering).1, false) ∈ node.basis.nonbasic ∧
        ((ofLex entering).1, true) ∈ node.basis.nonbasic) : BimatrixPathNode A B d where
  basis := node.basis.exchange l entering he hl
  coverage := by
    rw [BimatrixBasis.nonbasic_exchange]
    rcases hlabel with hd | hdup
    · have hv : ofLex entering = (d, (ofLex entering).2) := Prod.ext hd rfl
      rw [hv]
      exact node.coverage.exchange_dropped _ _
    · have h := node.coverage.exchange_duplicate hdup (ofLex entering).2
        (ofLex (node.basis.basic.orderEmbOfFin node.basis.cardinality l))
      exact h

end BimatrixPathNode

/-- The source's nonbasic variables are exactly the payoff variables. -/
theorem bimatrixSource_nonbasic_mem (A B : Fin m → Fin n → ℤ)
    (v : Fin (m + n) × Bool) :
    v ∈ (bimatrixSourceBasis A B).nonbasic ↔ v.2 = true := by
  rw [BimatrixBasis.mem_nonbasic]
  change toLex v ∉ bimatrixSlackVariables m n ↔ v.2 = true
  rcases v with ⟨i, b⟩
  cases b <;> simp [bimatrixSlackVariables]

/-- The canonical source is a node for every designated dropped label. -/
def bimatrixSourceNode (A B : Fin m → Fin n → ℤ) (d : Fin (m + n)) :
    BimatrixPathNode A B d where
  basis := bimatrixSourceBasis A B
  coverage := fun i _ => Or.inr ((bimatrixSource_nonbasic_mem A B (i, true)).mpr rfl)

/-- Equality of the source variables identifies a single source node. -/
theorem bimatrixSourceNode_unique (A B : Fin m → Fin n → ℤ) (d : Fin (m + n))
    (node : BimatrixPathNode A B d)
    (h : node.basis.basic = bimatrixSlackVariables m n) : node = bimatrixSourceNode A B d := by
  have hb : node.basis = bimatrixSourceBasis A B := BimatrixBasis.ext h
  cases node
  cases hb
  rfl

end GameTheory.Finite
