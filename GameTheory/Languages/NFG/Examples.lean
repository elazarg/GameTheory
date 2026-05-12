import GameTheory.Languages.NFG.Compile
import Mathlib.Tactic.Linarith

/-!
# Normal-Form Game Examples

Canonical 2×2 games with Nash equilibrium proofs:
- Prisoner's Dilemma (unique pure equilibrium, Pareto-dominated)
- Matching Pennies (no pure equilibrium)
- Stag Hunt (two coordination equilibria)
- Hawk–Dove / Chicken (two anti-coordination equilibria)
- Battle of the Sexes (two coordination equilibria with conflicting prefs)
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

/-! ## Hawk–Dove (Chicken)

An anti-coordination game (Maynard Smith & Price 1973, also called *Chicken*
in driving-style narrative). Aggressive `hawk` and accommodating `dove`.
When both escalate, both lose; if exactly one escalates, the hawk wins the
prize. Two asymmetric pure Nash equilibria. -/

/-- Actions in Hawk–Dove. -/
inductive HDAction where
  | hawk
  | dove
deriving DecidableEq, Repr

instance : Fintype HDAction where
  elems := {HDAction.hawk, HDAction.dove}
  complete x := by cases x <;> simp

open HDAction in
/-- Hawk–Dove game.
  Payoff matrix:
  - (H,H) = (-1,-1) -- mutual escalation, both injured
  - (H,D) = (3, 0)  -- hawk wins prize, dove backs off
  - (D,H) = (0, 3)
  - (D,D) = (1, 1)  -- peaceful split -/
def hawkDove : NFGGame Bool (fun _ => HDAction) where
  Outcome := ∀ _ : Bool, HDAction
  outcome := id
  utility s p :=
    match s true, s false, p with
    | hawk, hawk, _     => -1
    | hawk, dove, true  =>  3
    | hawk, dove, false =>  0
    | dove, hawk, true  =>  0
    | dove, hawk, false =>  3
    | dove, dove, _     =>  1

/-- The profile where P1 plays hawk, P2 plays dove. -/
def hd_hawk_dove : StrategyProfile (fun _ : Bool => HDAction) :=
  fun b => if b then HDAction.hawk else HDAction.dove

/-- The profile where P1 plays dove, P2 plays hawk. -/
def hd_dove_hawk : StrategyProfile (fun _ : Bool => HDAction) :=
  fun b => if b then HDAction.dove else HDAction.hawk

/-- (Hawk, Dove) is a Nash equilibrium. -/
theorem hd_hawk_dove_is_nash : IsNashPure hawkDove hd_hawk_dove := by
  intro i a'
  cases i <;> cases a' <;>
    simp [hawkDove, hd_hawk_dove, deviate, Function.update]

/-- (Dove, Hawk) is a Nash equilibrium. -/
theorem hd_dove_hawk_is_nash : IsNashPure hawkDove hd_dove_hawk := by
  intro i a'
  cases i <;> cases a' <;>
    simp [hawkDove, hd_dove_hawk, deviate, Function.update]

/-! ## Battle of the Sexes

A coordination game with conflict (Luce & Raiffa 1957). Both players want to
be together but disagree on the activity. Two pure Nash equilibria, each
favoring one player. -/

/-- Actions in Battle of the Sexes. -/
inductive BoSAction where
  | opera
  | football
deriving DecidableEq, Repr

instance : Fintype BoSAction where
  elems := {BoSAction.opera, BoSAction.football}
  complete x := by cases x <;> simp

open BoSAction in
/-- Battle of the Sexes game.
  Payoff matrix (P1 prefers opera, P2 prefers football):
  - (O,O) = (3, 1)
  - (O,F) = (0, 0) -- miscoordination
  - (F,O) = (0, 0)
  - (F,F) = (1, 3) -/
def battleOfTheSexes : NFGGame Bool (fun _ => BoSAction) where
  Outcome := ∀ _ : Bool, BoSAction
  outcome := id
  utility s p :=
    match s true, s false, p with
    | opera,    opera,    true  => 3
    | opera,    opera,    false => 1
    | football, football, true  => 1
    | football, football, false => 3
    | _,        _,        _     => 0

/-- The profile where both go to the opera. -/
def bos_opera_opera : StrategyProfile (fun _ : Bool => BoSAction) :=
  fun _ => BoSAction.opera

/-- The profile where both go to football. -/
def bos_football_football : StrategyProfile (fun _ : Bool => BoSAction) :=
  fun _ => BoSAction.football

/-- (Opera, Opera) is a Nash equilibrium. -/
theorem bos_opera_is_nash : IsNashPure battleOfTheSexes bos_opera_opera := by
  intro i a'
  cases i <;> cases a' <;>
    simp [battleOfTheSexes, bos_opera_opera, deviate, Function.update]

/-- (Football, Football) is a Nash equilibrium. -/
theorem bos_football_is_nash : IsNashPure battleOfTheSexes bos_football_football := by
  intro i a'
  cases i <;> cases a' <;>
    simp [battleOfTheSexes, bos_football_football, deviate, Function.update]

/-! ## Dictator Game

The dictator splits a fixed pie between themselves and a passive receiver
(Kahneman–Knetsch–Thaler 1986). The receiver has no strategic choice —
their action is irrelevant to the payoffs — so any profile in which the
dictator keeps the maximum share is a Nash equilibrium. -/

/-- Actions in the Dictator Game (only the proposer's action matters). -/
inductive DGAction where
  | keepAll
  | giveHalf
  | giveAll
deriving DecidableEq, Repr

instance : Fintype DGAction where
  elems := {DGAction.keepAll, DGAction.giveHalf, DGAction.giveAll}
  complete x := by cases x <;> simp

open DGAction in
/-- Dictator Game. Player `true` is the dictator and chooses one of three
splits of a pie of size 10. Player `false`'s action is ignored.
Payoffs: keepAll = (10, 0), giveHalf = (5, 5), giveAll = (0, 10). -/
def dictatorGame : NFGGame Bool (fun _ => DGAction) where
  Outcome := ∀ _ : Bool, DGAction
  outcome := id
  utility s p :=
    match s true, p with
    | keepAll,  true  => 10
    | keepAll,  false => 0
    | giveHalf, true  => 5
    | giveHalf, false => 5
    | giveAll,  true  => 0
    | giveAll,  false => 10

/-- The profile in which the dictator keeps all. -/
def dg_keep_all : StrategyProfile (fun _ : Bool => DGAction) :=
  fun b => if b then DGAction.keepAll else DGAction.keepAll

/-- The dictator keeping all is a Nash equilibrium. (The receiver's
strategy doesn't matter; the dictator strictly prefers `keepAll`.) -/
theorem dg_keep_is_nash : IsNashPure dictatorGame dg_keep_all := by
  intro i a'
  cases i <;> cases a' <;>
    (simp [dictatorGame, dg_keep_all, deviate, Function.update]; try linarith)

/-- The dictator giving all is NOT a Nash equilibrium (the dictator can
strictly improve by deviating to `keepAll`). -/
theorem dg_giveAll_not_nash :
    ¬ IsNashPure dictatorGame (fun _ : Bool => DGAction.giveAll) := by
  intro h
  have := h true DGAction.keepAll
  unfold IsNashPure dictatorGame deviate at this
  simp [Function.update] at this
  linarith

/-! ## Traveler's Dilemma (small version)

Basu (1994): two travelers claim a reimbursement value; the lower claim
is paid to both, with a small bonus/penalty for the lower/higher claimer.
The classical paradox arises with many actions and iterated weak
dominance; with only two actions the structure is already visible —
`claim2` weakly dominates `claim3`, and `(claim2, claim2)` is the
strict Nash equilibrium. -/

/-- Two-action Traveler's Dilemma claims. -/
inductive TDAction where
  | claim2
  | claim3
deriving DecidableEq, Repr

instance : Fintype TDAction where
  elems := {TDAction.claim2, TDAction.claim3}
  complete x := by cases x <;> simp

open TDAction in
/-- Two-action Traveler's Dilemma.
  Payoff: the lower claim is paid to both; the lower claimer gets +1, the
  higher claimer gets -1.
  - `(claim2, claim2)`: both get 2
  - `(claim2, claim3)`: P1 gets 3, P2 gets 1
  - `(claim3, claim2)`: P1 gets 1, P2 gets 3
  - `(claim3, claim3)`: both get 3 -/
def travelersDilemma : NFGGame Bool (fun _ => TDAction) where
  Outcome := ∀ _ : Bool, TDAction
  outcome := id
  utility s p :=
    match s true, s false, p with
    | claim2, claim2, _     => 2
    | claim2, claim3, true  => 3
    | claim2, claim3, false => 1
    | claim3, claim2, true  => 1
    | claim3, claim2, false => 3
    | claim3, claim3, _     => 3

/-- The profile where both claim 2. -/
def td_claim2_claim2 : StrategyProfile (fun _ : Bool => TDAction) :=
  fun _ => TDAction.claim2

/-- `(claim2, claim2)` is a strict Nash equilibrium of the Traveler's
Dilemma: any deviation strictly worsens the deviator's payoff. -/
theorem td_claim2_is_nash : IsNashPure travelersDilemma td_claim2_claim2 := by
  intro i a'
  cases i <;> cases a' <;>
    (simp [travelersDilemma, td_claim2_claim2, deviate, Function.update]; try linarith)

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
