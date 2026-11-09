module

public import GameTheoryComplexity.Backend.SATWords
public import Complexity.Logics.Propositional.CNF.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

@[expose] public section

/-! Native machine certificates for the public unary SAT byte serializer.
Variable indices are charged in unary before their raw unary bodies are emitted.
The clause and formula traversals compute all literal bytes and separators,
charging the framed intermediate lists and the complete concatenated output.
-/

namespace GameTheory.Complexity.Backend.SATWords

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Unary literal encoding computes the sign, every unary index bit and the delimiter. -/
@[fun_prop] theorem encodeLiteral_polyTime :
    ComputableInPolyTime encodeLiteral (encPair encUnary encBool) encBits := by
  have hbody : ComputableInPolyTime literalBody (encPair encUnary encBool) encBits :=
    .bitsCons (.snd encUnary encBool)
      ((ComputableInPolyTime.bitsReplicate true).comp (.fst encUnary encBool))
  have hbit : ComputableInPolyTime (fun bit : Bool => [bit, bit]) encBool encBits := .of_finite _
  have hdouble : ComputableInPolyTime
      (fun word : List Bool => word.flatMap fun bit => [bit, bit]) encBits encBits :=
    ComputableInPolyTime.flatMapToBitsWithInput (bits_encList_polyTime encBool).1
      (hbit.comp (.snd encBits encBool))
  exact (hdouble.comp hbody).bitsAppend (ComputableInPolyTime.const [false, true])

private theorem encodeClause_eq_flatMap (clause : Clause ℕ) :
    encodeClause clause = clause.flatMap encodeLiteral := by
  induction clause with
  | nil => rfl
  | cons literal clause ih => simp only [encodeClause_cons, List.flatMap_cons, ih]

/-- A full traversal emits every encoded literal in clause order. -/
@[fun_prop] theorem encodeClause_polyTime :
    ComputableInPolyTime encodeClause (encClause encUnary) encBits := by
  have hflat : ComputableInPolyTime
      (fun clause : Clause ℕ => clause.flatMap encodeLiteral) (encClause encUnary) encBits :=
    ComputableInPolyTime.flatMapToBitsWithInput
      (ComputableInPolyTime.id' (encIn := encClause encUnary))
      (encodeLiteral_polyTime.comp (.snd (encClause encUnary) (encPair encUnary encBool)))
  simpa only [← encodeClause_eq_flatMap] using hflat

private theorem encodeFormula_eq_flatMap (formula : CNF ℕ) :
    encodeFormula formula = formula.flatMap (fun clause => encodeClause clause ++ [true, false]) := by
  induction formula with
  | nil => rfl
  | cons clause formula ih => simp only [encodeFormula_cons, List.flatMap_cons, ih]

/-- A full traversal emits every clause and its separator, including empty clauses. -/
@[fun_prop] theorem encodeFormula_polyTime :
    ComputableInPolyTime encodeFormula (encCNFOver encUnary) encBits := by
  have hclause : ComputableInPolyTime
      (fun pair : CNF ℕ × Clause ℕ => encodeClause pair.2 ++ [true, false])
      (encPair (encCNFOver encUnary) (encClause encUnary)) encBits :=
    (encodeClause_polyTime.comp (.snd (encCNFOver encUnary) (encClause encUnary))).bitsAppend
      (ComputableInPolyTime.const [true, false])
  have hflat : ComputableInPolyTime
      (fun formula : CNF ℕ => formula.flatMap (fun clause => encodeClause clause ++ [true, false]))
      (encCNFOver encUnary) encBits :=
    ComputableInPolyTime.flatMapToBitsWithInput (ComputableInPolyTime.id') hclause
  simpa only [← encodeFormula_eq_flatMap] using hflat

end GameTheory.Complexity.Backend.SATWords
