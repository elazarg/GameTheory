/-
# External cumulative values for factored-observation stochastic games

The FOSG semantic object deliberately carries execution and information, not a
distinguished reward field.  Consumers supply the value of each realized
transition; the accumulation itself is the canonical Protocol trace fold.
-/

import GameTheory.Languages.FOSG

namespace GameTheory.Languages.FOSG

open GameTheory.Protocol

universe uι us ua up uq uk uv

namespace Game

variable {ι : Type uι} {α : Type uv} [Zero α] [Add α]

/-- Cumulative value for one player along a canonical FOSG history, under a
caller-supplied value for each realized transition. -/
def cumulativeValue (G : Game.{uι, us, ua, up, uq, uk} ι)
    (value : G.execution.StepEvent → ι → α) (h : G.History) (player : ι) : α :=
  h.valueSum fun event => value event player

@[simp]
theorem cumulativeValue_init (G : Game.{uι, us, ua, up, uq, uk} ι)
    (value : G.execution.StepEvent → ι → α) (player : ι) :
    G.cumulativeValue value G.execution.initHistory player = 0 := rfl

@[simp]
theorem cumulativeValue_extend (G : Game.{uι, us, ua, up, uq, uk} ι)
    (value : G.execution.StepEvent → ι → α) (h : G.History) (player : ι)
    {joint : ∀ i, Option (G.execution.Action i)}
    (isLegal : G.execution.Legal h.state joint) {target : G.execution.State}
    (realized : target ∈ (G.execution.step h.state ⟨joint, isLegal⟩).support) :
    G.cumulativeValue value (h.extend isLegal realized) player =
      G.cumulativeValue value h player +
        value ⟨h.state, joint, isLegal, target, realized⟩ player := rfl

end Game

end GameTheory.Languages.FOSG
