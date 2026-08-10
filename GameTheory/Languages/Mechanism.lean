/-
# Direct-revelation mechanism syntax

A mechanism records report types, an outcome type, and the rule mapping a
report profile to an outcome.  This language module contains no utility,
preference, or solution concept.  The deterministic compiler is structural;
strategyproofness and auction theorems live in `GameTheory.Mechanism`.
-/

import GameTheory.Core.Form

noncomputable section

namespace GameTheory.Languages

open GameTheory Probability

universe uι us

/-- Each agent reports something private; the mechanism maps the reports to an
outcome. -/
structure Mechanism (ι : Type uι) where
  /-- What agent `i` is asked to report. -/
  Report : ι → Type us
  /-- What the mechanism produces. -/
  Outcome : Type us
  /-- How the reports are resolved. -/
  choose : (∀ i, Report i) → Outcome

namespace Mechanism

variable {ι : Type uι} (M : Mechanism ι)

/-- Compile reports to strategies and retain the mechanism outcome. -/
@[reducible]
def toForm : GameForm ι where
  sig := { Strategy := M.Report, Outcome := M.Outcome }
  play reports := FinDist.pure (M.choose reports)

end Mechanism

end GameTheory.Languages
