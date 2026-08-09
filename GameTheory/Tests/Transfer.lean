/-
# Reaching the static core from two languages

Two native shapes — an influence diagram and a two-round simultaneous game —
both arrive at a `GameForm`, and from there every static solution concept
applies to them unchanged.

What this file is measuring is the *cost* of that arrival. A design that wanted
named adequacy certificates between semantic levels would introduce a record per
level, a construction per language, and composition laws to chain them. The
alternative on show here is that compilation is an ordinary function into a
shared target, so a transfer is function composition and needs no record at all.

The measurement below is deliberately blunt: count what each language had to add
in order to be usable by the static concepts. The answer is nothing, twice.
-/

import GameTheory.Protocol.Strategic
import GameTheory.Core.Utility
import GameTheory.Core.Response
import GameTheory.Experimental.PostArchitecture.MAIDThreeNodeWitness
import GameTheory.Experimental.PostArchitecture.RoundsWitness

noncomputable section

namespace GameTheory.Tests

open GameTheory GameTheory.Protocol GameTheory.Probability GameTheory.Languages

/-! ## Arrival

Neither line below defines anything language-specific. Each is the language's
own protocol handed to the one generic compilation. -/

/-- The influence diagram as a static game form. -/
def picnicForm : GameForm MAID.Agent := (MAID.protocol MAID.picnic).toGameForm 3

/-- The two-round simultaneous game as a static game form. -/
def roundsForm : GameForm (Fin 2) := rounds.toGameForm 2

/-! ## The named evaluation fact is shared

Both languages get their outcome law from the *same* theorem. Nothing is
reproved per language, which is the property a certificate level would have to
beat. -/

theorem picnicForm_play (profile : Profile (MAID.protocol MAID.picnic).strategicSignature) :
    picnicForm.play profile =
      (MAID.protocol MAID.picnic).runFor
        ((MAID.protocol MAID.picnic).chooserOf profile) 3 (MAID.protocol MAID.picnic).init :=
  ExecutionProtocol.toGameForm_play ..

theorem roundsForm_play (profile : Profile rounds.strategicSignature) :
    roundsForm.play profile = rounds.runFor (rounds.chooserOf profile) 2 rounds.init :=
  ExecutionProtocol.toGameForm_play ..

/-! ## The static concepts apply

Nothing below mentions a protocol, a trace, a chooser, or a horizon. The static
layer cannot tell which language it is looking at, which is the point. -/

/-- Any real payoff on the diagram's stopping states makes it a utility game. -/
def picnicGame (payoff : (MAID.protocol MAID.picnic).State → MAID.Agent → ℝ) :
    UtilityGame MAID.Agent where
  form := picnicForm
  utility := payoff

/-- And the same for the round-based game, with no second construction. -/
def roundsGame (payoff : rounds.State → Fin 2 → ℝ) : UtilityGame (Fin 2) where
  form := roundsForm
  utility := payoff

/-- Equilibrium is stated once, generically, and applies to both. Neither
language contributed a definition or a lemma to make this typecheck. -/
example (payoff : (MAID.protocol MAID.picnic).State → MAID.Agent → ℝ)
    (profile : Profile picnicForm.sig) : Prop :=
  IsNash picnicForm (euPreference payoff) profile

example (payoff : rounds.State → Fin 2 → ℝ) (profile : Profile roundsForm.sig) : Prop :=
  IsNash roundsForm (euPreference payoff) profile

/-- Dominance too, from the same generic definition. -/
example (payoff : rounds.State → Fin 2 → ℝ) (who : Fin 2)
    (preferred alternative : roundsForm.sig.Strategy who) : Prop :=
  WeaklyDominates roundsForm (euPreference payoff) who preferred alternative

/-! ## What a certificate level would have to beat

Each language needed **zero** new declarations to reach the static core: the two
`def`s at the top of this file apply an existing function, and the two
evaluation theorems are the same existing generic theorem instantiated twice.

A named adequacy record between the protocol and static levels would add, per
level, a structure and its composition laws, and per language a construction
discharging its fields. It would enable no theorem that is not already available
above, because the transfer here is function composition and composition of
functions needs no witness.

The honest scope of that observation: it holds for languages that compile *into*
a shared target. It says nothing about a transfer between two languages that
must preserve something the shared target forgets — recall, or the identity of a
decision site — which is exactly where a certificate might still earn its place.
Nothing in this repository yet demands such a transfer. -/

end GameTheory.Tests
