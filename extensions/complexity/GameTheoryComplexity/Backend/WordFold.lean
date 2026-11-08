module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration

@[expose] public section

/-! A right-to-left word fold supplies the already processed suffix to each step.
The implementation stores that suffix beside the accumulated output word.
Its native machine certificate charges the captured context, the callback and
every intermediate output; a polynomial bound on suffix results suffices.
-/

namespace GameTheory.Complexity.Backend.WordFold

open Turing.MultiTapeTM

private abbrev advance {Context : Type}
    (step : Context → List Bool → List Bool → Bool → List Bool)
    (context : Context) (state : List Bool × List Bool) (bit : Bool) : List Bool × List Bool :=
  (bit :: state.1, step context state.1 state.2 bit)

/-- Process a word from its right end, passing the suffix, accumulated word and current bit. -/
def suffixFold {Context : Type}
    (step : Context → List Bool → List Bool → Bool → List Bool)
    (context : Context) (initial word : List Bool) : List Bool :=
  (word.reverse.foldl
    (fun state bit => (bit :: state.1, step context state.1 state.2 bit)) ([], initial)).2

private theorem suffixFold_state_fst {Context : Type}
    (step : Context → List Bool → List Bool → Bool → List Bool)
    (context : Context) (initial word : List Bool) :
    (word.reverse.foldl (advance step context) ([], initial)).1 = word := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    rw [List.reverse_cons, List.foldl_append]
    change bit :: (word.reverse.foldl (advance step context) ([], initial)).1 = bit :: word
    exact congrArg (List.cons bit) ih

@[simp] theorem suffixFold_nil {Context : Type}
    (step : Context → List Bool → List Bool → Bool → List Bool)
    (context : Context) (initial : List Bool) :
    suffixFold step context initial [] = initial := rfl

/-- The callback sees the actual tail, including its bits and padding. -/
@[simp] theorem suffixFold_cons {Context : Type}
    (step : Context → List Bool → List Bool → Bool → List Bool)
    (context : Context) (initial : List Bool) (bit : Bool) (word : List Bool) :
    suffixFold step context initial (bit :: word) =
      step context word (suffixFold step context initial word) bit := by
  simp only [suffixFold, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change step context (word.reverse.foldl (advance step context) ([], initial)).1
    (word.reverse.foldl (advance step context) ([], initial)).2 bit = _
  rw [suffixFold_state_fst]

/-- A uniformly certified callback and polynomially bounded suffix results give one
polynomial-time scan. The input word and initial output are computed from the original input;
the complete context and suffix are charged on every callback invocation. -/
theorem suffixFold_polyTime
    {Input Context : Type} {input : Input ↪ List Bool}
    {contextEncoding : Context ↪ List Bool}
    {context : Input → Context} {word initial : Input → List Bool}
    {step : Context → List Bool → List Bool → Bool → List Bool}
    (hcontext : ComputableInPolyTime context input contextEncoding)
    (hword : ComputableInPolyTime word input encBits)
    (hinitial : ComputableInPolyTime initial input encBits)
    (hstep : ComputableInPolyTime
      (fun p : (Context × (List Bool × List Bool)) × Bool =>
        step p.1.1 p.1.2.1 p.1.2.2 p.2)
      (encPair (encPair contextEncoding (encPair encBits encBits)) encBool) encBits)
    {bound : Input → ℕ}
    (hbound : PolyBounded (fun x => (input x).length) bound)
    (hstates : ∀ x suffix, suffix <:+ word x →
      (suffixFold step (context x) (initial x) suffix).length ≤ bound x) :
    ComputableInPolyTime
      (fun x => suffixFold step (context x) (initial x) (word x)) input encBits := by
  have hreverse : ComputableInPolyTime (fun x => (word x).reverse) input encBits :=
    ComputableInPolyTime.bitsReverse.comp hword
  have hstart : ComputableInPolyTime (fun x => (([] : List Bool), initial x)) input
      (encPair encBits encBits) :=
    (ComputableInPolyTime.const []).prod hinitial
  have hadvance : ComputableInPolyTime
      (fun p : (Context × (List Bool × List Bool)) × Bool => advance step p.1.1 p.1.2 p.2)
      (encPair (encPair contextEncoding (encPair encBits encBits)) encBool)
      (encPair encBits encBits) := by
    apply ComputableInPolyTime.pair (enc₁ := encBits) (enc₂ := encBits)
    · exact ComputableInPolyTime.bitsCons (by fun_prop) (by fun_prop)
    · exact hstep
  have hlength : PolyBounded (fun x => (input x).length) (fun x => (word x).length) :=
    hword.polyBounded_length
  have hsize : PolyBounded (fun x => (input x).length)
      (fun x => 2 * (word x).length + 1 + bound x) :=
    (((PolyBounded.const 2).mul hlength).add (.const 1)).add hbound
  let invariant (x : Input) (consumed : List Bool) (state : List Bool × List Bool) : Prop :=
    state.1 = consumed.reverse ∧
      state.2 = suffixFold step (context x) (initial x) consumed.reverse
  have hfold := ComputableInPolyTime.foldlWith_spec hcontext hreverse hstart hadvance
    invariant (fun _ => ⟨rfl, rfl⟩)
    (fun x consumed state bit _ hstate => by
      change bit :: state.1 = (consumed ++ [bit]).reverse ∧
        step (context x) state.1 state.2 bit =
          suffixFold step (context x) (initial x) (consumed ++ [bit]).reverse
      rw [List.reverse_append, List.reverse_singleton, List.singleton_append, suffixFold_cons]
      constructor
      · exact congrArg (List.cons bit) hstate.1
      · rw [hstate.1, hstate.2])
    hsize
    (fun x consumed state hprefix hstate => by
      have hsuffix : consumed.reverse <:+ word x := by simpa using hprefix.reverse
      have hlength' : consumed.length ≤ (word x).length := by
        simpa only [List.length_reverse] using hprefix.length_le
      have hvalue := hstates x consumed.reverse hsuffix
      rw [length_encPair]
      change 2 * state.1.length + 1 + state.2.length ≤ _
      rw [hstate.1, hstate.2, List.length_reverse]
      omega)
  simpa only [Function.comp_def, suffixFold, advance] using
    (ComputableInPolyTime.snd encBits encBits).comp hfold.1

end GameTheory.Complexity.Backend.WordFold
