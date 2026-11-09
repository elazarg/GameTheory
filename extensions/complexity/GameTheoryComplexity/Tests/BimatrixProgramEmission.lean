module

public import GameTheoryComplexity.Backend.BimatrixProgramEmission

@[expose] public section

/-! Packed signed fields preserve aliases, signs, suffix bits and empty dimensions. -/
namespace GameTheory.Complexity.Tests.BimatrixProgramEmission

open GameTheory.Complexity.Backend GameTheory.Complexity.Backend.BimatrixProgramEmission
open Turing.MultiTapeTM

example : coefficients (fun (_ : List Bool) _ _ => [true, true]) []
    [false, true] [true, true, true, true] =
      (List.replicate 8 [true, true, false, false]).flatten := by decide +kernel

example : coefficients (fun (_ : List Bool) _ _ => [true, false]) []
    [true] [false, false, false] =
      [true, false, false, true, false, false] := by decide +kernel

example : coefficients (fun (_ : List Bool) _ _ => [true, true]) [] [] [true] = [] := by decide +kernel

example : coefficients (fun (_ : List Bool) _ _ => [true, true]) [] [true, true] [] = [] := by decide +kernel

example (source dimension width : List Bool) :
    (coefficients (fun s output action => s ++ output ++ action) source dimension width).length =
      dimension.length * ((dimension.length * 2) * width.length) :=
  coefficients_length _ _ _ _

example : ComputableInPolyTime (fun p : List Bool × List Bool =>
      coefficients (fun s output action => s ++ output ++ action) p.1 p.2 [false, false, false])
    (encPair encBits encBits) encBits := by
  have hs := ComputableInPolyTime.fst encBits (encPair encBits encBits)
  have ho := (ComputableInPolyTime.fst encBits encBits).comp
    (ComputableInPolyTime.snd encBits (encPair encBits encBits))
  have ha := (ComputableInPolyTime.snd encBits encBits).comp
    (ComputableInPolyTime.snd encBits (encPair encBits encBits))
  exact coefficients_polyTime
    (ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsAppend hs ho) ha)
    (ComputableInPolyTime.fst encBits encBits) (ComputableInPolyTime.snd encBits encBits)
    (ComputableInPolyTime.const [false, false, false])

end GameTheory.Complexity.Tests.BimatrixProgramEmission
