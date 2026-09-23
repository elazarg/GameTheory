/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.FinDist

/-! # An interleaved restricted menu

After Bob's observed reply, Alice may select either of two outcomes or withhold.
The command selecting a given outcome depends on the reply. Opposite utilities
have no common optimal randomized continuation. The control isolates why
sampling a command before receipt cannot replace a policy that observes the
reply.
-/

noncomputable section

namespace GameTheory.Tests.InterleavedMenus

open GameTheory.Math.Probability

/-- The two reachable values are represented by bits; `none` is withholding.
The globally preferred value zero is absent from this restricted menu. -/
def payoff (prefer : Bool) : Option Bool → ℝ
  | none => 0
  | some value => if value = prefer then 2 else 1

/-- A matching command selects the first value, a mismatching command the second. -/
def resolve (reply : Bool) (command : Option Bool) : Option Bool :=
  command.map (fun bit => bit == reply)

def bestCommand (prefer reply : Bool) : Option Bool :=
  some (if prefer then reply else !reply)

theorem bestCommand_payoff (prefer reply : Bool) :
    payoff prefer (resolve reply (bestCommand prefer reply)) = 2 := by
  cases prefer <;> cases reply <;> norm_num [payoff, resolve, bestCommand]

/-- No fixed command can select the first value for both possible replies. -/
theorem fixed_command_loses_information (command : Option Bool) :
    ¬ (resolve false command = some true ∧ resolve true command = some true) := by
  cases command with
  | none => simp [resolve]
  | some bit => cases bit <;> simp [resolve]

theorem reply_payoff_sum (command : Option Bool) :
    payoff true (resolve false command) + payoff true (resolve true command) ≤ 3 := by
  cases command with
  | none => norm_num [payoff, resolve]
  | some bit => cases bit <;> norm_num [payoff, resolve]

/-- Sampling a command before receipt cannot replace responding to the reply.
This also rules out randomized batches that ignore the incoming information. -/
theorem no_randomized_fixed_response (law : FinDist (Option Bool)) :
    ¬ (2 ≤ law.expect (fun command => payoff true (resolve false command)) ∧
      2 ≤ law.expect (fun command => payoff true (resolve true command))) := by
  rintro ⟨first, second⟩
  have total : law.expect (fun command =>
      payoff true (resolve false command) + payoff true (resolve true command)) ≤ 3 :=
    FinDist.expect_le_of_forall _ _ _ (fun command _ => reply_payoff_sum command)
  rw [FinDist.expect_add] at total
  linarith

theorem payoff_sum (result : Option Bool) :
    payoff false result + payoff true result ≤ 3 := by
  cases result with
  | none => norm_num [payoff]
  | some bit => cases bit <;> norm_num [payoff]

/-- At either observed reply, no behavioral choice is optimal for both utilities.
Both bounds are required by SPE at a proper root with this final decision. -/
theorem no_common_randomized_completion (reply : Bool) (law : FinDist (Option Bool)) :
    ¬ (2 ≤ law.expect (fun command => payoff false (resolve reply command)) ∧
      2 ≤ law.expect (fun command => payoff true (resolve reply command))) := by
  rintro ⟨first, second⟩
  have total : law.expect (fun command =>
      payoff false (resolve reply command) + payoff true (resolve reply command)) ≤ 3 :=
    FinDist.expect_le_of_forall _ _ _ (fun command _ => payoff_sum (resolve reply command))
  rw [FinDist.expect_add] at total
  linarith

end GameTheory.Tests.InterleavedMenus
