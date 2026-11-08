module

public import GameTheoryComplexity.Backend.WordFold
public import GameTheoryComplexity.Backend.BinaryCertificateArithmetic
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! A suffix-dependent scan checks captured context, growing output and exact bytes. -/

namespace GameTheory.Complexity.Tests.WordFold

open Turing.MultiTapeTM Backend Backend.WordFold

/-- A concrete indexed sum: every term reads the actual suffix and a captured word. -/
def indexedSum (context word : List Bool) : List Bool :=
  suffixFold (fun context suffix accumulated _ =>
    binaryCertificateAdd ![accumulated, suffix ++ context]) context [] word

@[simp] theorem indexedSum_nil (context : List Bool) : indexedSum context [] = [] := rfl

@[simp] theorem indexedSum_cons (context : List Bool) (bit : Bool) (word : List Bool) :
    indexedSum context (bit :: word) = binaryCertificateAdd ![indexedSum context word, word ++ context] := by
  exact suffixFold_cons _ _ _ _ _

theorem indexedSum_length (context word : List Bool) :
    (indexedSum context word).length ≤ context.length + 2 * word.length := by
  induction word with
  | nil => simp
  | cons bit word ih =>
    rw [indexedSum_cons, binaryCertificateAdd_length, List.length_append, List.length_cons]
    omega

theorem indexedSum_polyTime :
    ComputableInPolyTime (fun p : List Bool × List Bool => indexedSum p.1 p.2)
      (encPair encBits encBits) encBits := by
  have hc := ComputableInPolyTime.fst encBits encBits
  have hw := ComputableInPolyTime.snd encBits encBits
  have hstep : ComputableInPolyTime
      (fun p : (List Bool × (List Bool × List Bool)) × Bool =>
        binaryCertificateAdd ![p.1.2.2, p.1.2.1 ++ p.1.1])
      (encPair (encPair encBits (encPair encBits encBits)) encBool) encBits := by
    have houter := ComputableInPolyTime.fst (encPair encBits (encPair encBits encBits)) encBool
    have hcontext := (ComputableInPolyTime.fst encBits (encPair encBits encBits)).comp houter
    have hstate := (ComputableInPolyTime.snd encBits (encPair encBits encBits)).comp houter
    have hsuffix := (ComputableInPolyTime.fst encBits encBits).comp hstate
    have haccumulated := (ComputableInPolyTime.snd encBits encBits).comp hstate
    have hterm := ComputableInPolyTime.bitsAppend hsuffix hcontext
    have htable : ComputableInPolyTime
        (fun p : (List Bool × (List Bool × List Bool)) × Bool =>
          ![p.1.2.2, p.1.2.1 ++ p.1.1])
        (encPair (encPair encBits (encPair encBits encBits)) encBool) (encPi encBits) := by
      apply ComputableInPolyTime.pi
      intro i
      fin_cases i
      · exact haccumulated
      · exact hterm
    exact binaryCertificateAdd_polyTime.comp htable
  have hcl := ComputableInPolyTime.length_bits_comp hc
  have hwl := ComputableInPolyTime.length_bits_comp hw
  exact suffixFold_polyTime hc hw (ComputableInPolyTime.const []) hstep
    (hcl.polyBounded.add ((PolyBounded.const 2).mul hwl.polyBounded))
    (fun p suffix hsuffix => by
      have hlen := indexedSum_length p.1 suffix
      have hle := hsuffix.length_le
      change (indexedSum p.1 suffix).length ≤ p.1.length + 2 * p.2.length
      omega)

-- A prefix scan, or one that discards the original suffix bits, gives a different answer.
example : indexedSum [true] [true, false] = [true, true, false] := by decide +kernel

end GameTheory.Complexity.Tests.WordFold
