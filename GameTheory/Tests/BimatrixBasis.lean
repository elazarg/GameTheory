import GameTheory.Finite.BimatrixBasis

/-! Canonical source identity and a certified pivot in a degenerate rectangular game. -/
namespace GameTheory.Tests.BimatrixBasis
open GameTheory.Finite GameTheory.Math GameTheory.Math.CanonicalDictionary
private def allOnes : Fin 1 → Fin 2 → ℤ := fun _ _ => 1
private def dropped : Fin 3 := (finSumFinEquiv : (Fin 1 ⊕ Fin 2) ≃ Fin 3) (.inl 0)

-- Source nonbasic labels contain exactly the payoff variables.
example : ∀ i : Fin 3, (i, true) ∈ (bimatrixSourceBasis allOnes allOnes).nonbasic ∧
    (i, false) ∉ (bimatrixSourceBasis allOnes allOnes).nonbasic := by
  intro i
  constructor
  · exact (bimatrixSource_nonbasic_mem allOnes allOnes (i, true)).mpr rfl
  · intro h
    have hh := (bimatrixSource_nonbasic_mem allOnes allOnes (i, false)).mp h
    exact Bool.false_ne_true hh

-- A set of source variables determines one node, regardless of proof certificates.
example (node : BimatrixPathNode allOnes allOnes dropped)
    (h : node.basis.basic = bimatrixSlackVariables 1 2) :
    node = bimatrixSourceNode allOnes allOnes dropped :=
  bimatrixSourceNode_unique _ _ _ node h

-- The positive-payoff source theorem constructs an actual valid path-node successor.
example : ∃ node : BimatrixPathNode allOnes allOnes dropped,
    toLex (dropped, true) ∈ node.basis.basic ∧
      node.basis.basic ≠ (bimatrixSourceBasis allOnes allOnes).basic := by
  let source := bimatrixSourceNode allOnes allOnes dropped
  let entering : BimatrixVariable 1 2 := toLex (dropped, true)
  have he : entering ∉ source.basis.basic := by
    change toLex (dropped, true) ∉ bimatrixSlackVariables 1 2
    simp [bimatrixSlackVariables]
  obtain ⟨l, hl, _⟩ := exists_unique_bimatrixSource_leavingRow allOnes allOnes
    (by decide) (by decide) (by intro i j; exact Int.zero_lt_one)
    (by intro i j; exact Int.zero_lt_one) (.inl 0)
  have hleave : IsLeavingRow (PerturbedDictionary.dictionaryCoefficients
      (basisMatrix (bimatrixBasisColumns allOnes allOnes) source.basis.basic
        source.basis.cardinality) (fun _ => 1))
      ((basisMatrix (bimatrixBasisColumns allOnes allOnes) source.basis.basic
        source.basis.cardinality)⁻¹.mulVec
          (fun i => bimatrixBasisColumns allOnes allOnes i entering)) l := by
    simpa only [source, bimatrixSourceNode, bimatrixSourceBasis, bimatrixSlack_basisMatrix,
      inv_one, Matrix.one_mulVec, entering, dropped, bimatrixBasisColumns,
      ofLex_toLex, ↓reduceIte, Equiv.symm_apply_apply] using hl
  let next := source.exchange l entering he hleave (Or.inl rfl)
  have hn : entering ∈ next.basis.basic :=
    FiniteBasisExchange.entering_mem _ _ _
  refine ⟨next, hn, ?_⟩
  intro h
  apply he
  change entering ∈ (bimatrixSourceBasis allOnes allOnes).basic
  rw [← h]
  exact hn

-- Empty games still have a unique empty feasible basis; no dropped-label node is fabricated.
example : (bimatrixSourceBasis (fun _ : Fin 0 => fun _ : Fin 0 => (0 : ℤ))
    (fun _ : Fin 0 => fun _ : Fin 0 => (0 : ℤ))).basic = ∅ := by
  simp [bimatrixSourceBasis, bimatrixSlackVariables]

end GameTheory.Tests.BimatrixBasis
