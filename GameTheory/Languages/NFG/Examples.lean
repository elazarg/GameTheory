import GameTheory.Languages.NFG.Compile
import Mathlib.Tactic.Linarith

/-!
# Normal-Form Game Examples

Prisoner's Dilemma, Matching Pennies, and Stag Hunt with Nash equilibrium
proofs.
-/

namespace NFG

/-! ## Prisoner's Dilemma -/

/-- Actions in the Prisoner's Dilemma. -/
inductive PDAction where
  | cooperate
  | defect
deriving DecidableEq, Repr

instance : Fintype PDAction where
  elems := {PDAction.cooperate, PDAction.defect}
  complete x := by cases x <;> simp

open PDAction in
/-- The Prisoner's Dilemma game.
  Payoff matrix:
  - (D,D) = (1,1), (C,D) = (0,3), (D,C) = (3,0), (C,C) = (2,2) -/
def prisonersDilemma : NFGGame Bool (fun _ => PDAction) where
  Outcome := ∀ _ : Bool, PDAction
  outcome := id
  utility s p :=
    match s true, s false, p with
    | defect,    defect,    true  => 1
    | cooperate, defect,    true  => 0
    | defect,    cooperate, true  => 3
    | cooperate, cooperate, true  => 2
    | defect,    defect,    false => 1
    | cooperate, defect,    false => 3
    | defect,    cooperate, false => 0
    | cooperate, cooperate, false => 2

/-- The profile where both players defect. -/
def pd_defect_defect : StrategyProfile (fun _ : Bool => PDAction) :=
  fun _ => PDAction.defect

/-- (Defect, Defect) is a Nash equilibrium of the Prisoner's Dilemma. -/
theorem pd_defect_is_nash : IsNashPure prisonersDilemma pd_defect_defect := by
  intro i a'
  cases i <;> cases a' <;>
    simp [prisonersDilemma, pd_defect_defect, deviate, Function.update]

/-- The profile where both players cooperate. -/
def pd_coop_coop : StrategyProfile (fun _ : Bool => PDAction) :=
  fun _ => PDAction.cooperate

/-- (Cooperate, Cooperate) is NOT a Nash equilibrium. -/
theorem pd_coop_not_nash : ¬ IsNashPure prisonersDilemma pd_coop_coop := by
  intro h
  have h1 := h true PDAction.defect
  unfold IsNashPure prisonersDilemma pd_coop_coop deviate at h1
  simp [Function.update] at h1
  linarith

/-! ## Matching Pennies -/

/-- Actions in Matching Pennies. -/
inductive MPAction where
  | heads
  | tails
deriving DecidableEq, Repr

instance : Fintype MPAction where
  elems := {MPAction.heads, MPAction.tails}
  complete x := by cases x <;> simp

open MPAction in
/-- Matching Pennies game.
  Payoff matrix:
  - (H,H) = (1,-1), (H,T) = (-1,1), (T,H) = (-1,1), (T,T) = (1,-1) -/
def matchingPennies : NFGGame Bool (fun _ => MPAction) where
  Outcome := ∀ _ : Bool, MPAction
  outcome := id
  utility s p :=
    match s true, s false, p with
    | heads, heads, true  =>  1
    | heads, tails, true  => -1
    | tails, heads, true  => -1
    | tails, tails, true  =>  1
    | heads, heads, false => -1
    | heads, tails, false =>  1
    | tails, heads, false =>  1
    | tails, tails, false => -1

/-- Matching Pennies has no pure Nash equilibrium. -/
theorem matchingPennies_no_pure_nash :
    ∀ s : StrategyProfile (fun _ : Bool => MPAction), ¬ IsNashPure matchingPennies s := by
  intro s h
  have e1 : s true = MPAction.heads ∨ s true = MPAction.tails := by cases s true <;> simp
  have e2 : s false = MPAction.heads ∨ s false = MPAction.tails := by cases s false <;> simp
  rcases e1 with hs1 | hs1 <;> rcases e2 with hs2 | hs2
  · have := h false MPAction.tails
    simp [matchingPennies, deviate, Function.update, hs1, hs2] at this
    linarith
  · have := h true MPAction.tails
    simp [matchingPennies, deviate, Function.update, hs1, hs2] at this
    linarith
  · have := h true MPAction.heads
    simp [matchingPennies, deviate, Function.update, hs1, hs2] at this
    linarith
  · have := h false MPAction.heads
    simp [matchingPennies, deviate, Function.update, hs1, hs2] at this
    linarith

/-! ## Stag Hunt

A 2×2 coordination game (Rousseau 1755 / Skyrms 2004). Two pure Nash
equilibria coexist: `(stag, stag)` is Pareto-dominant, while `(hare, hare)`
is risk-dominant (safer when partners are untrusted). The game illustrates
that Nash equilibrium does not single out a unique outcome in coordination
problems. -/

/-- Actions in the Stag Hunt. -/
inductive SHAction where
  | stag
  | hare
deriving DecidableEq, Repr

instance : Fintype SHAction where
  elems := {SHAction.stag, SHAction.hare}
  complete x := by cases x <;> simp

open SHAction in
/-- The Stag Hunt game.
  Payoff matrix:
  - (S,S) = (3,3) -- successful joint stag hunt
  - (S,H) = (0,1) -- stag hunter goes hungry; hare hunter eats
  - (H,S) = (1,0)
  - (H,H) = (1,1) -- both eat hare -/
def stagHunt : NFGGame Bool (fun _ => SHAction) where
  Outcome := ∀ _ : Bool, SHAction
  outcome := id
  utility s p :=
    match s true, s false, p with
    | stag, stag, _     => 3
    | stag, hare, true  => 0
    | stag, hare, false => 1
    | hare, stag, true  => 1
    | hare, stag, false => 0
    | hare, hare, _     => 1

/-- The profile where both players hunt stag. -/
def sh_stag_stag : StrategyProfile (fun _ : Bool => SHAction) :=
  fun _ => SHAction.stag

/-- The profile where both players hunt hare. -/
def sh_hare_hare : StrategyProfile (fun _ : Bool => SHAction) :=
  fun _ => SHAction.hare

/-- (Stag, Stag) is a Nash equilibrium (Pareto-dominant). -/
theorem sh_stag_is_nash : IsNashPure stagHunt sh_stag_stag := by
  intro i a'
  cases i <;> cases a' <;>
    simp [stagHunt, sh_stag_stag, deviate, Function.update]

/-- (Hare, Hare) is a Nash equilibrium (risk-dominant). -/
theorem sh_hare_is_nash : IsNashPure stagHunt sh_hare_hare := by
  intro i a'
  cases i <;> cases a' <;>
    simp [stagHunt, sh_hare_hare, deviate, Function.update]

/-- The mismatched profile `(Stag, Hare)` is **not** a Nash equilibrium: the
stag hunter prefers to switch to hare. -/
theorem sh_stag_hare_not_nash :
    ¬ IsNashPure stagHunt (fun b => if b then SHAction.stag else SHAction.hare) := by
  intro h
  have h1 := h true SHAction.hare
  simp [stagHunt, deviate, Function.update] at h1
  linarith

/-! ## Distributional API examples -/

open GameTheory

/-- The `udist` of (Defect, Defect) in PD is a point mass (deterministic pure game). -/
theorem pd_defect_udist :
    prisonersDilemma.toKernelGame.udist pd_defect_defect =
    PMF.pure (prisonersDilemma.utility (prisonersDilemma.outcome pd_defect_defect)) :=
  NFGGame.toKernelGame_udist prisonersDilemma pd_defect_defect

/-- (Defect, Defect) is Nash for the EU preference (via `IsNashFor`).
    This demonstrates that `IsNash` and `IsNashFor euPref` are interchangeable. -/
theorem pd_defect_isNashFor_eu :
    prisonersDilemma.toKernelGame.IsNashFor
      prisonersDilemma.toKernelGame.euPref pd_defect_defect :=
  (KernelGame.IsNash_iff_IsNashFor_eu _ _).mp
    ((IsNashPure_iff_kernelGame _ _).mp pd_defect_is_nash)

/-- Defect is dominant for the EU preference (via `IsDominantFor`). -/
theorem pd_defect_isDominantFor_eu (i : Bool) :
    prisonersDilemma.toKernelGame.IsDominantFor
      prisonersDilemma.toKernelGame.euPref
      i PDAction.defect :=
  (KernelGame.IsDominant_iff_IsDominantFor_eu _ _ _).mp
    ((IsDominant_iff_kernelGame _ _ _).mp (by
      intro s a'
      cases i <;> cases ha : a' <;> cases h1 : s true <;> cases h2 : s false <;>
        simp_all [prisonersDilemma, deviate, Function.update] <;> norm_num))

end NFG
