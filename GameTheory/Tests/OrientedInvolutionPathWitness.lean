import GameTheory.Math.OrientedInvolutionPathWitness

/-! Raw witnesses exclude the calibrated source and recover alternating terminals. -/
namespace GameTheory.Tests.OrientedInvolutionPathWitness
open GameTheory.Math GameTheory.Math.OrientedInvolutionPath

-- The outgoing-inconsistency branch itself carries no origin exclusion.
example : ¬EndOfLine.RawWitness (predecessor Bool.not id id)
    (successor Bool.not id id) true true := by decide +kernel

example : EndOfLine.RawWitness (predecessor Bool.not id id)
    (successor Bool.not id id) true false := by decide +kernel

example (x : Bool) : EndOfLine.RawWitness (predecessor Bool.not id id)
    (successor Bool.not id id) true x ↔ id x = x ∧ x ≠ true := by
  apply OrientedInvolutionPath.rawWitness_iff Bool.not id id
  · exact Bool.not_not
  · intro b
    rfl
  · intro b
    cases b <;> decide
  · intro b
    rfl
  · intro b hb
    exact (hb rfl).elim
  · rfl
  · rfl

end GameTheory.Tests.OrientedInvolutionPathWitness
