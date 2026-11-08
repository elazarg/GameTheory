module

public import GameTheoryComplexity.Backend.EndOfLineMachineOps
public import Complexity.Computability.Complexity.Classes.TFNP

@[expose] public section

/-! A native polynomial-time Boolean verifier for succinct End-of-Line. It
evaluates the source and the candidate's immediate neighbors, checks the exact
witness width, and accepts the empty fallback when the source promise fails. -/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM
open ComputableInPolyTime
open EndOfLineMachineOps

/-- Check the distinguished source and agreement across its first edge. -/
def endOfLineSourceFlag (input : List Bool) : Bool :=
  decide (endOfLinePredecessor input (endOfLineOrigin input) = endOfLineOrigin input) &&
    (!decide (endOfLineSuccessor input (endOfLineOrigin input) = endOfLineOrigin input) &&
      decide (endOfLinePredecessor input
        (endOfLineSuccessor input (endOfLineOrigin input)) = endOfLineOrigin input))

theorem endOfLineSourceFlag_accept (input : List Bool) :
    endOfLineSourceFlag input = true ↔ endOfLineSourceValid input := by
  simp [endOfLineSourceFlag, endOfLineSourceValid]

/-- Exactly one consistent incident edge makes a candidate an endpoint. -/
def endOfLineEndpointFlag (input vertex : List Bool) : Bool :=
  (successorFlag input vertex && !predecessorFlag input vertex) ||
    (predecessorFlag input vertex && !successorFlag input vertex)

theorem endOfLineEndpointFlag_accept (input vertex : List Bool) :
    endOfLineEndpointFlag input vertex = true ↔ GameTheory.Math.EndOfLine.IsEndpoint
      (endOfLinePredecessor input) (endOfLineSuccessor input) vertex := by
  simp only [endOfLineEndpointFlag, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq,
    successorFlag_accept, predecessorFlag_accept, GameTheory.Math.EndOfLine.IsEndpoint]

/-- Check an endpoint witness or the designated invalid-source fallback. -/
def endOfLineVerdict (input witness : List Bool) : Bool :=
  (endOfLineSourceFlag input &&
    (decide (witness.length = endOfLineWidth input) &&
      (!decide (witness = endOfLineOrigin input) && endOfLineEndpointFlag input witness))) ||
    (!endOfLineSourceFlag input && decide (witness = []))

theorem endOfLineVerdict_accept (input witness : List Bool) :
    endOfLineVerdict input witness = true ↔ endOfLineRelation input witness := by
  simp only [endOfLineVerdict, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq,
    decide_eq_true_eq, endOfLineSourceFlag_accept, endOfLineEndpointFlag_accept,
    endOfLineRelation]

@[fun_prop] theorem endOfLineSourceFlag_polyTime
    {α : Type} {encIn : α ↪ List Bool} {input : α → List Bool}
    (hi : ComputableInPolyTime input encIn encBits) :
    ComputableInPolyTime (fun a => endOfLineSourceFlag (input a)) encIn encBool := by
  have ho := origin_polyTime hi
  have hs := successor_polyTime hi ho
  exact bool_and' (decide_eq' (predecessor_polyTime hi ho) ho)
    (bool_and' (bool_not.comp (decide_eq' hs ho))
      (decide_eq' (predecessor_polyTime hi hs) ho))

@[fun_prop] theorem endOfLineEndpointFlag_polyTime
    {α : Type} {encIn : α ↪ List Bool} {input vertex : α → List Bool}
    (hi : ComputableInPolyTime input encIn encBits)
    (hv : ComputableInPolyTime vertex encIn encBits) :
    ComputableInPolyTime (fun a => endOfLineEndpointFlag (input a) (vertex a))
      encIn encBool := by
  have hs := successorFlag_polyTime hi hv
  have hp := predecessorFlag_polyTime hi hv
  exact bool_or.comp ((bool_and' hs (bool_not.comp hp)).prod
    (bool_and' hp (bool_not.comp hs)))

@[fun_prop] theorem endOfLineVerdict_polyTime
    {α : Type} {encIn : α ↪ List Bool} {input witness : α → List Bool}
    (hi : ComputableInPolyTime input encIn encBits)
    (hw : ComputableInPolyTime witness encIn encBits) :
    ComputableInPolyTime (fun a => endOfLineVerdict (input a) (witness a))
      encIn encBool := by
  have hsource := endOfLineSourceFlag_polyTime hi
  have ho := origin_polyTime hi
  have hwidth := decide_eq' (length_bits.comp hw) (width_polyTime hi)
  have hne := bool_not.comp (decide_eq' hw ho)
  have hendpoint := endOfLineEndpointFlag_polyTime hi hw
  exact bool_or.comp
    ((bool_and' hsource (bool_and' hwidth (bool_and' hne hendpoint))).prod
      (bool_and' (bool_not.comp hsource) (decide_eq' hw (const []))))

/-- Polynomial balance and the native Boolean verifier give FNP membership. -/
theorem endOfLineRelation_mem_FNP : endOfLineRelation ∈ Cslib.Complexity.FNP encBits := by
  refine ⟨endOfLineRelation_polyBalanced, ?_⟩
  exact ⟨(fun p : List Bool × List Bool => endOfLineVerdict p.1 p.2),
    endOfLineVerdict_polyTime (fst encBits encBits) (snd encBits encBits),
    fun input witness => (endOfLineVerdict_accept input witness).symm⟩

/-- Succinct End-of-Line is a total polynomially verified search problem. -/
theorem endOfLineRelation_mem_TFNP : endOfLineRelation ∈ Cslib.Complexity.TFNP encBits :=
  ⟨endOfLineRelation_mem_FNP, endOfLineRelation_total⟩

end GameTheory.Complexity.Backend
