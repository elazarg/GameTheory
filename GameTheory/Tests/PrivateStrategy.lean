/-
# Correlated private randomness survives behavioral realization

A private bit is reused across two responses. The environment echoes the first
output as the second input, and the response is that input xor the private
bit. The first output is uniform and the second is certainly false, so the two
outputs are correlated through memory the transcript never records; the
realized behavioral policy reproduces the joint law anyway.
-/

import GameTheory.Protocol.PrivateStrategy
import Mathlib.Probability.Distributions.Uniform

noncomputable section

namespace GameTheory.Tests.PrivateStrategy

open GameTheory.Protocol.PrivateStrategy GameTheory.Math.Probability

/-- Draw a private bit once and answer every input with its xor. -/
def strategy : Strategy Bool Bool Bool where
  initial := PMF.uniformOfFintype _
  respond memory input := PMF.pure (xor memory input, memory)

/-- The environment shows the most recent output. -/
def observe (past : List Bool) : Bool := past.headD false

/-- The environment records each output. -/
def advance (past : List Bool) (output : Bool) : PMF (List Bool) :=
  PMF.pure (output :: past)

theorem private_two (memory : Bool) : runPrivate strategy observe advance 2 [] [] memory =
    PMF.pure ([false, memory], [(memory, false), (false, memory)]) := by
  cases memory <;> simp [runPrivate, strategy, observe, advance]

theorem behavioral_two : runBehavioral (behavioral strategy) observe advance 2 [] [] =
    (PMF.uniformOfFintype Bool).map fun bit =>
      ([false, bit], [(bit, false), (false, bit)]) := by
  rw [← realize strategy observe advance 2 [] []]
  change (PMF.uniformOfFintype Bool).bind _ = _
  rw [← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro memory _
  exact private_two memory

end GameTheory.Tests.PrivateStrategy
