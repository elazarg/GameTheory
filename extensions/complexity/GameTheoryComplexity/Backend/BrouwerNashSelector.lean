module

public import GameTheoryComplexity.Backend.BrouwerNashGlobalCorrectness
public import GameTheoryComplexity.Backend.BrouwerNashJitterQuery
public import GameTheoryComplexity.Backend.BrouwerNashExtractionQuery
public import GameTheoryComplexity.Backend.BrouwerNashIncrementQuery
public import GameTheoryComplexity.Backend.BrouwerNashInterpolationQuery
public import GameTheoryComplexity.Backend.BrouwerNashColorQuery
public import GameTheoryComplexity.Backend.BrouwerNashSelectorKind

@[expose] public section

/-! The disjoint coefficient regions compose in their canonical order. Source-dependent
color codes are charged as actual native word producers at the selector boundary. -/
namespace GameTheory.Complexity.Backend.BrouwerNashSelector
open Turing.MultiTapeTM

local notation "QueryContext" => ((List Bool × (List Bool × List Bool)) × (List Bool × List Bool))
local notation "queryEncoding" => encPair (encPair encBits (encPair encBits encBits)) (encPair encBits encBits)

private def queries : List (QueryContext → List Bool) := [
  (fun context => BrouwerNashGlobalQuery.coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
  (fun context => BrouwerNashJitterQuery.coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
  (fun context => BrouwerNashExtractionQuery.coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
  (fun context => BrouwerNashIncrementQuery.allCoefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
  (fun context => BrouwerNashInterpolationQuery.coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
  (fun context => BrouwerNashColorQuery.coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2)]

/-- Add the six canonical coefficient regions in their original right-fold order. -/
def coefficientWord (source code₀ code₁ out action : List Bool) : List Bool :=
  binarySignedQuerySum [
    (fun context : QueryContext => BrouwerNashGlobalQuery.coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
    (fun context => BrouwerNashJitterQuery.coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
    (fun context => BrouwerNashExtractionQuery.coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
    (fun context => BrouwerNashIncrementQuery.allCoefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
    (fun context => BrouwerNashInterpolationQuery.coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2),
    (fun context => BrouwerNashColorQuery.coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2)]
    ((source,(code₀,code₁)),(out,action))

private theorem coefficientWord_eq (context : QueryContext) :
    coefficientWord context.1.1 context.1.2.1 context.1.2.2 context.2.1 context.2.2 =
      binarySignedQuerySum queries context := rfl

@[fun_prop] theorem coefficientWord_polyTime {Input : Type} {input : Input ↪ List Bool}
    {source code₀ code₁ out action : Input → List Bool}
    (hs : ComputableInPolyTime source input encBits)
    (h₀ : ComputableInPolyTime code₀ input encBits)
    (h₁ : ComputableInPolyTime code₁ input encBits)
    (ho : ComputableInPolyTime out input encBits)
    (ha : ComputableInPolyTime action input encBits) :
    ComputableInPolyTime (fun a => coefficientWord (source a) (code₀ a) (code₁ a) (out a) (action a))
      input encBits := by
  have hc : ComputableInPolyTime (fun context : QueryContext => context) queryEncoding queryEncoding := .id'
  have hqueries : ∀ query ∈ queries, ComputableInPolyTime query queryEncoding encBits := by
    intro query hq
    simp only [queries, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact BrouwerNashGlobalQuery.coefficientWord_polyTime hc.fst'.fst' hc.fst'.snd'.fst'
        hc.fst'.snd'.snd' hc.snd'.fst' hc.snd'.snd'
    · exact BrouwerNashJitterQuery.coefficientWord_polyTime hc.fst'.fst' hc.fst'.snd'.fst'
        hc.fst'.snd'.snd' hc.snd'.fst' hc.snd'.snd'
    · exact BrouwerNashExtractionQuery.coefficientWord_polyTime hc.fst'.fst' hc.fst'.snd'.fst'
        hc.fst'.snd'.snd' hc.snd'.fst' hc.snd'.snd'
    · exact BrouwerNashIncrementQuery.allCoefficientWord_polyTime hc.fst'.fst' hc.fst'.snd'.fst'
        hc.fst'.snd'.snd' hc.snd'.fst' hc.snd'.snd'
    · exact BrouwerNashInterpolationQuery.coefficientWord_polyTime hc.fst'.fst' hc.fst'.snd'.fst'
        hc.fst'.snd'.snd' hc.snd'.fst' hc.snd'.snd'
    · exact BrouwerNashColorQuery.coefficientWord_polyTime hc.fst'.fst' hc.fst'.snd'.fst'
        hc.fst'.snd'.snd' hc.snd'.fst' hc.snd'.snd'
  exact (binarySignedQuerySum_polyTime queries hqueries
    ((hs.prod (h₀.prod h₁)).prod (ho.prod ha))).of_enc_eq (fun a =>
      congrArg encBits (coefficientWord_eq ((source a,(code₀ a,code₁ a)),(out a,action a))))

/-- All contributions add exactly, including reference aliases and signed constants. -/
theorem coefficientWord_expansion (source code₀ code₁ out action : List Bool) :
    binarySignedValue (coefficientWord source code₀ code₁ out action) =
      binarySignedValue (BrouwerNashGlobalQuery.coefficientWord source code₀ code₁ out action) +
        (binarySignedValue (BrouwerNashJitterQuery.coefficientWord source code₀ code₁ out action) +
          (binarySignedValue (BrouwerNashExtractionQuery.coefficientWord source code₀ code₁ out action) +
            (binarySignedValue (BrouwerNashIncrementQuery.allCoefficientWord source code₀ code₁ out action) +
              (binarySignedValue (BrouwerNashInterpolationQuery.coefficientWord source code₀ code₁ out action) +
                binarySignedValue (BrouwerNashColorQuery.coefficientWord source code₀ code₁ out action))))) := by
  simp only [coefficientWord, binarySignedQuerySum_value, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- Specialize both actual compiled color-code producers to the source word. -/
def coefficientQuery (codes : Fin 2 → List Bool → List Bool)
    (source out action : List Bool) : List Bool :=
  coefficientWord source (codes 0 source) (codes 1 source) out action

/-- The joint native query charges source, output, action and both compiled code words. -/
@[fun_prop] theorem coefficientQuery_polyTime (codes : Fin 2 → List Bool → List Bool)
    (hc : ∀ flag, ComputableInPolyTime (codes flag) encBits encBits) :
    ComputableInPolyTime (fun p : List Bool × (List Bool × List Bool) =>
      coefficientQuery codes p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits)) encBits := by
  have hs := ComputableInPolyTime.fst encBits (encPair encBits encBits)
  have hr := ComputableInPolyTime.snd encBits (encPair encBits encBits)
  have hcert := coefficientWord_polyTime hs ((hc 0).comp hs) ((hc 1).comp hs) hr.fst' hr.snd'
  simpa only [coefficientQuery, Function.comp_def] using hcert

/-- Specialize the complete comparator flag to the two compiled color codes. -/
def kindQuery (codes : Fin 2 → List Bool → List Bool) (source out : List Bool) : List Bool :=
  BrouwerNashSelectorKind.kindWord source (codes 0 source) (codes 1 source) out

/-- The kind query charges the source, output ruler and both compiled code words. -/
@[fun_prop] theorem kindQuery_polyTime (codes : Fin 2 → List Bool → List Bool)
    (hc : ∀ flag, ComputableInPolyTime (codes flag) encBits encBits) :
    ComputableInPolyTime (fun p : List Bool × List Bool => kindQuery codes p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hs := ComputableInPolyTime.fst encBits encBits
  have hcert := BrouwerNashSelectorKind.kindWord_polyTime hs ((hc 0).comp hs) ((hc 1).comp hs)
    (ComputableInPolyTime.snd encBits encBits)
  simpa only [kindQuery, Function.comp_def] using hcert

end GameTheory.Complexity.Backend.BrouwerNashSelector
