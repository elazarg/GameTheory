module

public import GameTheoryComplexity.Backend.SATWords
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

@[expose] public section

/-! A finite-state machine certifies syntax validation of the public unary SAT
byte format. Five Boolean registers suffice on every input. The proof identifies
that actual bounded-state scan with successful canonical native CNF decoding;
no runtime bound is inferred from the size of a decoded formula.
-/

namespace GameTheory.Complexity.Backend

open Turing.MultiTapeTM

private abbrev SyntaxState := Bool × Bool × (Bool × Bool × Bool)

private abbrev syntaxEncoding : SyntaxState ↪ List Bool :=
  encPair encBool (encPair encBool (encPair encBool (encPair encBool encBool)))

private theorem finiteSyntaxFold_polyTime
    (step : SyntaxState → Bool → SyntaxState) (initial : SyntaxState) :
    ComputableInPolyTime (fun input : List Bool => input.foldl step initial)
      encBits syntaxEncoding := by
  have hstep : ComputableInPolyTime (fun pair : SyntaxState × Bool => step pair.1 pair.2)
      (encPair syntaxEncoding encBool) syntaxEncoding := .of_finite _
  have hfold := ComputableTidilyInPolyTime.foldl_of_bounded_growth
    (encA := encBool) (encL := encBits)
    (list := id) (init := fun _ : List Bool => initial) (step := step)
    (ComputableTidilyInPolyTime.id' (encIn := encBits))
    (ComputableTidilyInPolyTime.const initial) hstep.tidy
    (growth := 0) (fun _ _ => by simp [syntaxEncoding])
  simpa only [id_eq] using ComputableInPolyTime.of_tidy hfold

/-- The actual finite-state scan has one native polynomial-time machine certificate. -/
@[fun_prop] theorem satSyntaxValid_polyTime :
    ComputableInPolyTime SATWords.syntaxValid encBits encBool := by
  unfold SATWords.syntaxValid
  let finish (state : SyntaxState) : Bool :=
    !state.1 && (!state.2.2.1 && !state.2.2.2.1 && !state.2.2.2.2)
  have hfinish : ComputableInPolyTime finish syntaxEncoding encBool := .of_finite _
  exact hfinish.comp (finiteSyntaxFold_polyTime _ (false, false, false, false, false))

/-- One-bit characteristic word for successful native CNF decoding. -/
def satSyntaxWord (input : List Bool) : List Bool := [(SATWords.decodeFormula? input).isSome]

@[simp] theorem satSyntaxWord_eq (input : List Bool) :
    satSyntaxWord input = [(SATWords.decodeFormula? input).isSome] := rfl

/-- Syntax validation is certified by native finite-state execution, including
malformed and incomplete inputs, before being used by payoff serializers. -/
@[fun_prop] theorem satSyntaxWord_polyTime :
    ComputableInPolyTime satSyntaxWord encBits encBits := by
  change ComputableInPolyTime
    (fun input : List Bool => [(SATWords.decodeFormula? input).isSome]) encBits encBits
  simpa only [SATWords.syntaxValid_eq_decodeFormula] using
    ComputableInPolyTime.bitsCons satSyntaxValid_polyTime (ComputableInPolyTime.const [])

end GameTheory.Complexity.Backend
