module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

@[expose] public section

/-! Circuit-problem words use doubled payload bits and a two-bit separator.
The total decoder preserves the decoded first prefix on malformed input, while
the remainder is nonempty only after a valid separator. This public byte format
is independent of the native encodings used for machine arguments.
-/

namespace GameTheory.Complexity.Backend.CircuitWords

open Turing.MultiTapeTM

/-- Double every left bit, write the separator, and retain the right word verbatim. -/
def encodePair (left right : List Bool) : List Bool :=
  (left.flatMap fun bit => [bit, bit]) ++ [false, true] ++ right

/-- Decode the doubled prefix and, only after a valid separator, its remainder. -/
def splitPair : List Bool → List Bool × List Bool
  | false :: false :: tail =>
      let decoded := splitPair tail
      (false :: decoded.1, decoded.2)
  | true :: true :: tail =>
      let decoded := splitPair tail
      (true :: decoded.1, decoded.2)
  | false :: true :: tail => ([], tail)
  | _ => ([], [])

/-- Keep the prefix decoded before a separator, malformed pair or incomplete pair. -/
def first (word : List Bool) : List Bool := (splitPair word).1

/-- Return the suffix after a valid separator, or the empty word on malformed input. -/
def rest (word : List Bool) : List Bool := (splitPair word).2

@[simp] theorem encodePair_nil (right : List Bool) :
    encodePair [] right = false :: true :: right := rfl

@[simp] theorem encodePair_cons (bit : Bool) (left right : List Bool) :
    encodePair (bit :: left) right = bit :: bit :: encodePair left right := by
  simp [encodePair]

@[simp] theorem encodePair_length (left right : List Bool) :
    (encodePair left right).length = 2 * left.length + 2 + right.length := by
  induction left with
  | nil => simp; omega
  | cons bit left ih =>
    rw [encodePair_cons]
    simp only [List.length_cons, ih]
    omega

@[simp] theorem splitPair_encodePair (left right : List Bool) :
    splitPair (encodePair left right) = (left, right) := by
  induction left with
  | nil => rfl
  | cons bit left ih => cases bit <;> simp [splitPair, ih]

@[simp] theorem first_encodePair (left right : List Bool) :
    first (encodePair left right) = left := by simp [first]

@[simp] theorem rest_encodePair (left right : List Bool) :
    rest (encodePair left right) = right := by simp [rest]

theorem encodePair_injective {left left' right right' : List Bool}
    (equal : encodePair left right = encodePair left' right') :
    left = left' ∧ right = right' := by
  have decoded := congrArg splitPair equal
  simpa using decoded

private theorem splitPair_lengths :
    ∀ word : List Bool, (splitPair word).1.length ≤ word.length ∧
      (splitPair word).2.length ≤ word.length
  | [] => by simp [splitPair]
  | [bit] => by cases bit <;> simp [splitPair]
  | false :: false :: tail => by
      have bounds := splitPair_lengths tail
      simp only [splitPair, List.length_cons]
      omega
  | false :: true :: tail => by simp [splitPair]; omega
  | true :: false :: tail => by simp [splitPair]
  | true :: true :: tail => by
      have bounds := splitPair_lengths tail
      simp only [splitPair, List.length_cons]
      omega

theorem first_length_le (word : List Bool) : (first word).length ≤ word.length :=
  (splitPair_lengths word).1

theorem rest_length_le (word : List Bool) : (rest word).length ≤ word.length :=
  (splitPair_lengths word).2

private def duplicateStep (accumulator : List Bool) (bit : Bool) : List Bool :=
  accumulator ++ [bit, bit]

private theorem duplicateFold (word accumulator : List Bool) :
    word.foldl duplicateStep accumulator =
      accumulator ++ word.flatMap (fun bit => [bit, bit]) := by
  induction word generalizing accumulator with
  | nil => simp
  | cons bit tail ih =>
    simpa [duplicateStep, List.append_assoc] using ih (accumulator ++ [bit, bit])

/-- The circuit byte encoder has an actual native polynomial-time machine. -/
@[fun_prop] theorem encodePair_polyTime :
    ComputableInPolyTime (fun words : List Bool × List Bool => encodePair words.1 words.2)
      (encPair encBits encBits) encBits := by
  have hstep : ComputableInPolyTime
      (fun input : List Bool × Bool => duplicateStep input.1 input.2)
      (encPair encBits encBool) encBits :=
    (ComputableInPolyTime.fst encBits encBool).bitsAppend
      (.bitsCons (.snd encBits encBool)
        (.bitsCons (.snd encBits encBool) (.const [])))
  have hfold := ComputableTidilyInPolyTime.foldl_of_bounded_growth
    (encA := encBool) (encL := encBits)
    (list := id) (init := fun _ : List Bool => []) (step := duplicateStep)
    (ComputableTidilyInPolyTime.id' (encIn := encBits))
    (ComputableTidilyInPolyTime.const []) hstep.tidy
    (growth := 2) (fun _ _ => by simp [duplicateStep])
  have hdouble : ComputableInPolyTime
      (fun word : List Bool => word.flatMap (fun bit => [bit, bit])) encBits encBits := by
    simpa only [id_eq, duplicateFold, List.nil_append] using
      ComputableInPolyTime.of_tidy hfold
  simpa only [encodePair, Function.comp_def, List.append_assoc] using
    (hdouble.comp (.fst encBits encBits)).bitsAppend
      ((ComputableInPolyTime.const [false, true]).bitsAppend (.snd encBits encBits))

/-! A left-to-right transducer stores reversed output words. Its finite phase is
first-bit, second-bit, after-separator or invalid; the pending bit completes the
doubled pair. Each input bit adds at most two symbols to the encoded state. -/

private abbrev Phase := Bool × Bool
private abbrev Control := (Phase × Bool) × Bool
private abbrev ScanState := Phase × Bool × List Bool × List Bool

private abbrev phaseEncoding : Phase ↪ List Bool := encPair encBool encBool
private abbrev controlEncoding : Control ↪ List Bool :=
  encPair (encPair phaseEncoding encBool) encBool
private abbrev stateEncoding : ScanState ↪ List Bool :=
  encPair phaseEncoding (encPair encBool (encPair encBits encBits))

private def afterSeparator (phase : Phase) : Bool := phase.1 && !phase.2

private def advancePhase (control : Control) : Phase :=
  let phase := control.1.1
  if phase.1 then phase else
    if phase.2 then
      if control.1.2 == control.2 then (false, false) else (true, control.1.2)
    else (false, true)

private def writeLeft (control : Control) : Bool :=
  !control.1.1.1 && control.1.1.2 && (control.1.2 == control.2)

private def writeRight (control : Control) : Bool := afterSeparator control.1.1

private def scanStep (state : ScanState) (bit : Bool) : ScanState :=
  let control := ((state.1, state.2.1), bit)
  (advancePhase control, bit,
    (if writeLeft control then bit :: state.2.2.1 else state.2.2.1),
    (if writeRight control then bit :: state.2.2.2 else state.2.2.2))

private def initialState : ScanState := ((false, false), false, [], [])

private def finishState (state : ScanState) : List Bool × List Bool :=
  (state.2.2.1.reverse,
    if afterSeparator state.1 then state.2.2.2.reverse else [])

private theorem scan_invalid_correct :
    ∀ (word : List Bool) (pending : Bool) (left right : List Bool),
      finishState (word.foldl scanStep ((true, true), pending, left, right)) =
        (left.reverse, [])
  | [], _, _, _ => by simp [finishState, afterSeparator]
  | bit :: tail, _, left, right => by
      change finishState (tail.foldl scanStep ((true, true), bit, left, right)) = _
      exact scan_invalid_correct tail bit left right

private theorem scan_good_correct :
    ∀ (word : List Bool) (pending : Bool) (left right : List Bool),
      finishState (word.foldl scanStep ((true, false), pending, left, right)) =
        (left.reverse, right.reverse ++ word)
  | [], _, _, _ => by simp [finishState, afterSeparator]
  | bit :: tail, _, left, right => by
      change finishState (tail.foldl scanStep ((true, false), bit, left, bit :: right)) = _
      rw [scan_good_correct tail bit left (bit :: right)]
      simp [List.reverse_cons, List.append_assoc]

private theorem scan_first_correct :
    ∀ (word : List Bool) (pending : Bool) (left : List Bool),
      finishState (word.foldl scanStep ((false, false), pending, left, [])) =
        (left.reverse ++ (splitPair word).1, (splitPair word).2)
  | [], _, _ => by simp [finishState, afterSeparator, splitPair]
  | [bit], _, _ => by
      cases bit <;> simp [scanStep, advancePhase, writeLeft, writeRight,
        finishState, afterSeparator, splitPair]
  | false :: false :: tail, _, left => by
      change finishState (tail.foldl scanStep ((false, false), false, false :: left, [])) =
        (left.reverse ++ false :: (splitPair tail).1, (splitPair tail).2)
      rw [scan_first_correct tail false (false :: left)]
      simp [List.reverse_cons, List.append_assoc]
  | false :: true :: tail, _, left => by
      simp only [splitPair, List.append_nil]
      change finishState (tail.foldl scanStep ((true, false), true, left, [])) =
        (left.reverse, tail)
      simpa using scan_good_correct tail true left []
  | true :: false :: tail, _, left => by
      simp only [splitPair, List.append_nil]
      change finishState (tail.foldl scanStep ((true, true), false, left, [])) =
        (left.reverse, [])
      exact scan_invalid_correct tail false left []
  | true :: true :: tail, _, left => by
      change finishState (tail.foldl scanStep ((false, false), true, true :: left, [])) =
        (left.reverse ++ true :: (splitPair tail).1, (splitPair tail).2)
      rw [scan_first_correct tail true (true :: left)]
      simp [List.reverse_cons, List.append_assoc]

private theorem scan_correct (word : List Bool) :
    finishState (word.foldl scanStep initialState) = splitPair word := by
  simpa [initialState] using scan_first_correct word false []

private theorem stateEncoding_length (state : ScanState) :
    (stateEncoding state).length = 13 + 2 * state.2.2.1.length + state.2.2.2.length := by
  simp [stateEncoding, phaseEncoding]
  omega

private theorem scanStep_polyTime :
    ComputableInPolyTime (fun input : ScanState × Bool => scanStep input.1 input.2)
      (encPair stateEncoding encBool) stateEncoding := by
  have hstate := ComputableInPolyTime.fst stateEncoding encBool
  have hbit := ComputableInPolyTime.snd stateEncoding encBool
  have hphase := (ComputableInPolyTime.fst phaseEncoding
    (encPair encBool (encPair encBits encBits))).comp hstate
  have hrest := (ComputableInPolyTime.snd phaseEncoding
    (encPair encBool (encPair encBits encBits))).comp hstate
  have hpending := (ComputableInPolyTime.fst encBool (encPair encBits encBits)).comp hrest
  have hwords := (ComputableInPolyTime.snd encBool (encPair encBits encBits)).comp hrest
  have hleft := (ComputableInPolyTime.fst encBits encBits).comp hwords
  have hright := (ComputableInPolyTime.snd encBits encBits).comp hwords
  have hcontrol := (hphase.prod hpending).prod hbit
  have hphaseNext : ComputableInPolyTime advancePhase controlEncoding phaseEncoding :=
    .of_finite _
  have hwriteLeft : ComputableInPolyTime writeLeft controlEncoding encBool := .of_finite _
  have hwriteRight : ComputableInPolyTime writeRight controlEncoding encBool := .of_finite _
  exact (hphaseNext.comp hcontrol).prod (hbit.prod
    (((hwriteLeft.comp hcontrol).ite (.bitsCons hbit hleft) hleft).prod
      ((hwriteRight.comp hcontrol).ite (.bitsCons hbit hright) hright)))

private theorem scanStep_growth (state : ScanState) (bit : Bool) :
    (stateEncoding (scanStep state bit)).length ≤ (stateEncoding state).length + 2 := by
  rcases state with ⟨⟨closed, second⟩, pending, left, right⟩
  cases closed <;> cases second <;> cases pending <;> cases bit <;>
    simp [scanStep, advancePhase, writeLeft, writeRight, afterSeparator] <;>
    omega

private theorem finishState_polyTime :
    ComputableInPolyTime finishState stateEncoding (encPair encBits encBits) := by
  have hphase := ComputableInPolyTime.fst phaseEncoding
    (encPair encBool (encPair encBits encBits))
  have hrest := ComputableInPolyTime.snd phaseEncoding
    (encPair encBool (encPair encBits encBits))
  have hwords := (ComputableInPolyTime.snd encBool (encPair encBits encBits)).comp hrest
  have hleft := (ComputableInPolyTime.fst encBits encBits).comp hwords
  have hright := (ComputableInPolyTime.snd encBits encBits).comp hwords
  have hleftReverse := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.bitsReverse.comp hleft.tidy)
  have hrightReverse := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.bitsReverse.comp hright.tidy)
  have hgood : ComputableInPolyTime afterSeparator phaseEncoding encBool := .of_finite _
  exact hleftReverse.prod ((hgood.comp hphase).ite hrightReverse (.const []))

/-- The total circuit-byte parser is certified through a finite-state scan with
constant encoded growth on every input bit and every accumulator. -/
@[fun_prop] theorem splitPair_polyTime :
    ComputableInPolyTime splitPair encBits (encPair encBits encBits) := by
  have hscan := ComputableTidilyInPolyTime.foldl_of_bounded_growth
    (encA := encBool) (encL := encBits)
    (list := id) (init := fun _ : List Bool => initialState) (step := scanStep)
    (ComputableTidilyInPolyTime.id' (encIn := encBits))
    (ComputableTidilyInPolyTime.const initialState) scanStep_polyTime.tidy
    (growth := 2) scanStep_growth
  simpa only [id_eq, Function.comp_def, scan_correct] using
    finishState_polyTime.comp (ComputableInPolyTime.of_tidy hscan)

@[fun_prop] theorem first_polyTime : ComputableInPolyTime first encBits encBits :=
  (ComputableInPolyTime.fst encBits encBits).comp splitPair_polyTime

@[fun_prop] theorem rest_polyTime : ComputableInPolyTime rest encBits encBits :=
  (ComputableInPolyTime.snd encBits encBits).comp splitPair_polyTime

/-- An incomplete pair retains the already decoded payload. -/
example : splitPair [true, true, false] = ([true], []) := rfl

/-- An invalid off-diagonal pair rejects the remainder without discarding the prefix. -/
example : splitPair [false, false, true, false, true] = ([false], []) := rfl

/-- The separator ends the decoded prefix and leaves the following bytes unchanged. -/
example : splitPair [false, true, true, false] = ([], [true, false]) := rfl

end GameTheory.Complexity.Backend.CircuitWords
