/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.ExpectationAlgebra
import GameTheory.Math.Probability.Bounds

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

theorem payoffIntegrable_resolved (law : PMF (Option Bool))
    (prefer reply : Bool) :
    PayoffIntegrable law (fun command => payoff prefer (resolve reply command)) :=
  payoffIntegrable_of_bounded law _ (C := 2) (by
    intro command
    cases command with
    | none => simp [payoff, resolve]
    | some bit =>
      cases prefer <;> cases reply <;> cases bit <;>
        norm_num [payoff, resolve])

/-- Sampling a command before receipt cannot replace responding to the reply.
This also rules out randomized batches that ignore the incoming information. -/
theorem no_randomized_fixed_response (law : PMF (Option Bool)) :
    ¬ (2 ≤ expect law (fun command => payoff true (resolve false command))
          (payoffIntegrable_resolved law true false) ∧
      2 ≤ expect law (fun command => payoff true (resolve true command))
          (payoffIntegrable_resolved law true true)) := by
  rintro ⟨first, second⟩
  let hfirst := payoffIntegrable_resolved law true false
  let hsecond := payoffIntegrable_resolved law true true
  have hsum := expect_add hfirst hsecond
  have total : expect law (fun command =>
      payoff true (resolve false command) + payoff true (resolve true command))
        (payoffIntegrable_add hfirst hsecond) ≤
      expect law (fun _ => 3) (payoffIntegrable_constant law 3) :=
    expect_mono (fun command _ => reply_payoff_sum command)
      (payoffIntegrable_add hfirst hsecond) (payoffIntegrable_constant law 3)
  rw [hsum] at total
  rw [expect_constant law 3 (payoffIntegrable_constant law 3)] at total
  have hfirst' : 2 ≤ expect law
      (fun command => payoff true (resolve false command)) hfirst := by
    simpa [hfirst] using first
  have hsecond' : 2 ≤ expect law
      (fun command => payoff true (resolve true command)) hsecond := by
    simpa [hsecond] using second
  linarith

theorem payoff_sum (result : Option Bool) :
    payoff false result + payoff true result ≤ 3 := by
  cases result with
  | none => norm_num [payoff]
  | some bit => cases bit <;> norm_num [payoff]

/-- At either observed reply, no behavioral choice is optimal for both utilities.
Both bounds are required by SPE at a proper root with this final decision. -/
theorem no_common_randomized_completion (reply : Bool) (law : PMF (Option Bool)) :
    ¬ (2 ≤ expect law (fun command => payoff false (resolve reply command))
          (payoffIntegrable_resolved law false reply) ∧
      2 ≤ expect law (fun command => payoff true (resolve reply command))
          (payoffIntegrable_resolved law true reply)) := by
  rintro ⟨first, second⟩
  let hfirst := payoffIntegrable_resolved law false reply
  let hsecond := payoffIntegrable_resolved law true reply
  have hsum := expect_add hfirst hsecond
  have total : expect law (fun command =>
      payoff false (resolve reply command) + payoff true (resolve reply command))
        (payoffIntegrable_add hfirst hsecond) ≤
      expect law (fun _ => 3) (payoffIntegrable_constant law 3) :=
    expect_mono (fun command _ => payoff_sum (resolve reply command))
      (payoffIntegrable_add hfirst hsecond) (payoffIntegrable_constant law 3)
  rw [hsum] at total
  rw [expect_constant law 3 (payoffIntegrable_constant law 3)] at total
  have hfirst' : 2 ≤ expect law
      (fun command => payoff false (resolve reply command)) hfirst := by
    simpa [hfirst] using first
  have hsecond' : 2 ≤ expect law
      (fun command => payoff true (resolve reply command)) hsecond := by
    simpa [hsecond] using second
  linarith

end GameTheory.Tests.InterleavedMenus
