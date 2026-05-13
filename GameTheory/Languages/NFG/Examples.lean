import GameTheory.Languages.NFG.Compile
import Mathlib.Tactic.DeriveFintype
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
deriving DecidableEq, Repr, Fintype

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
deriving DecidableEq, Repr, Fintype

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
deriving DecidableEq, Repr, Fintype

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
deriving DecidableEq, Repr, Fintype

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
deriving DecidableEq, Repr, Fintype

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
deriving DecidableEq, Repr, Fintype

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
deriving DecidableEq, Repr, Fintype

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

/-! ## Cournot Duopoly (3-action version)

Cournot (1838): two firms simultaneously choose production quantities;
market price is a decreasing function of total output and each firm's
profit is `quantity × price`. With quantities `{1, 2, 3}` and inverse
demand `price = max(5 - Q, 0)`, the unique pure Nash is `(2, 2)` with
profit `4` each — both firms over-produce relative to monopoly. -/

/-- Available quantities for the Cournot duopoly. -/
inductive CournotQty where
  | qty1
  | qty2
  | qty3
deriving DecidableEq, Repr, Fintype

open CournotQty in
/-- Cournot profit table for `(q_self, q_other) ∈ {1,2,3}²` with inverse
demand `price = max(5 - q_self - q_other, 0)`. Tabulated rather than
computed to keep equilibrium proofs simp-friendly. -/
def cournotProfit : CournotQty → CournotQty → ℝ
  | qty1, qty1 => 3   | qty1, qty2 => 2   | qty1, qty3 => 1
  | qty2, qty1 => 4   | qty2, qty2 => 2   | qty2, qty3 => 0
  | qty3, qty1 => 3   | qty3, qty2 => 0   | qty3, qty3 => 0

/-- The Cournot duopoly NFG. -/
def cournotDuopoly : NFGGame Bool (fun _ => CournotQty) where
  Outcome := ∀ _ : Bool, CournotQty
  outcome := id
  utility s p :=
    if p then cournotProfit (s true) (s false)
    else cournotProfit (s false) (s true)

/-- Both firms playing `qty2` (the unique pure Nash). -/
def cournot_q2_q2 : StrategyProfile (fun _ : Bool => CournotQty) :=
  fun _ => CournotQty.qty2

/-- `(qty2, qty2)` is a Nash equilibrium of the Cournot duopoly. -/
theorem cournot_q2_q2_is_nash : IsNashPure cournotDuopoly cournot_q2_q2 := by
  intro i a'
  cases i <;> cases a' <;>
    (simp [cournotDuopoly, cournot_q2_q2, cournotProfit, deviate, Function.update];
     try linarith)

/-! ## Braess's Paradox (toy 2x2 / 2x3 instance)

Braess (1968): adding an extra strategy to a strategic game can
*lower* the Nash-equilibrium welfare. Below is the smallest
self-contained 2-player instance illustrating the effect:

  Restricted game (2 actions, `BraessRestricted`):
                  A     B
            A   (3,3) (0,0)
            B   (0,0) (3,3)
  Two pure Nash equilibria, both with payoff `(3,3)`.

  Augmented game (3 actions, `BraessAugmented`) — adds a "shortcut"
  action `C` that strictly dominates both `A` and `B`:
                  A     B     C
            A   (3,3) (0,0) (1,5)
            B   (0,0) (3,3) (1,5)
            C   (5,1) (5,1) (2,2)
  `C` strictly dominates `A` and `B` for each player (5>3>1>0 against
  every opponent action), so the unique pure Nash is `(C,C)` with
  payoff `(2,2)` — strictly worse than the restricted-game Nash
  payoff `(3,3)`. Adding a dominant strategy made everyone worse off. -/

/-- Restricted-game actions. -/
inductive BraessRAction where | a | b
deriving DecidableEq, Repr, Fintype

/-- Augmented-game actions (with the Braess "shortcut" `c`). -/
inductive BraessAAction where | a | b | c
deriving DecidableEq, Repr, Fintype

open BraessRAction in
/-- The Braess restricted game. -/
def braessRestricted : NFGGame Bool (fun _ => BraessRAction) where
  Outcome := ∀ _ : Bool, BraessRAction
  outcome := id
  utility s _ :=
    match s true, s false with
    | a, a => 3
    | b, b => 3
    | _, _ => 0

open BraessAAction in
/-- The Braess augmented game. -/
def braessAugmented : NFGGame Bool (fun _ => BraessAAction) where
  Outcome := ∀ _ : Bool, BraessAAction
  outcome := id
  utility s p :=
    match s true, s false, p with
    | a, a, _     => 3
    | b, b, _     => 3
    | a, b, _     => 0
    | b, a, _     => 0
    | a, c, true  => 1
    | a, c, false => 5
    | b, c, true  => 1
    | b, c, false => 5
    | c, a, true  => 5
    | c, a, false => 1
    | c, b, true  => 5
    | c, b, false => 1
    | c, c, _     => 2

/-- `(a, a)` is a Nash equilibrium of the restricted game. -/
theorem braessRestricted_aa_is_nash :
    IsNashPure braessRestricted (fun _ : Bool => BraessRAction.a) := by
  intro i a'
  cases i <;> cases a' <;>
    simp [braessRestricted, deviate, Function.update]

/-- `(c, c)` is a Nash equilibrium of the augmented game (the
"Braess equilibrium"). -/
theorem braessAugmented_cc_is_nash :
    IsNashPure braessAugmented (fun _ : Bool => BraessAAction.c) := by
  intro i a'
  cases i <;> cases a' <;>
    (simp [braessAugmented, deviate, Function.update]; try linarith)

/-- `(a, a)` is NOT Nash in the augmented game: each player strictly
prefers `c` (payoff 5) to `a` (payoff 3). -/
theorem braessAugmented_aa_not_nash :
    ¬ IsNashPure braessAugmented (fun _ : Bool => BraessAAction.a) := by
  intro h
  have h1 := h true BraessAAction.c
  unfold IsNashPure braessAugmented deviate at h1
  simp [Function.update] at h1
  linarith

/-- **Braess's paradox on this instance**: the welfare-maximizing
Nash of the restricted game (`a, a`, total welfare 6) is strictly
better than the unique pure Nash of the augmented game (`c, c`,
total welfare 4). The "shortcut" action `c` strictly dominates
`a` and `b` for every player, but driving them all to it costs
everyone two units of payoff. -/
theorem braess_welfare_decreases :
    (braessRestricted.utility
        (fun _ : Bool => BraessRAction.a) true
      + braessRestricted.utility
        (fun _ : Bool => BraessRAction.a) false) >
    (braessAugmented.utility
        (fun _ : Bool => BraessAAction.c) true
      + braessAugmented.utility
        (fun _ : Bool => BraessAAction.c) false) := by
  simp [braessRestricted, braessAugmented]; norm_num

/-! ## Bertrand Competition (3-price version)

Bertrand (1883): two firms simultaneously set prices for a
homogeneous good; the lower-priced firm captures the entire market,
ties split it. With marginal cost `c = 1` and discrete price
choices `{1, 2, 3}`, the per-firm profit at `(p_i, p_j)` is

  - `p_i - 1` if `p_i < p_j` (undercut and capture all demand),
  - `(p_i - 1) / 2` if `p_i = p_j` (split the market),
  - `0` if `p_i > p_j` (priced out).

In the continuous-price version, the unique Nash drives both prices
to marginal cost. The discrete version is multi-equilibrium:
`(2, 2)` is a *strict* Nash (deviations strictly lose customer or
strictly forgo margin), while `(1, 1)` is *weak* — undercutting is
impossible at the price floor and overcutting is payoff-equivalent
(both yield 0). We prove both Nash facts. -/

/-- Bertrand price choices. -/
inductive BertrandPrice where
  | p1 | p2 | p3
deriving DecidableEq, Repr, Fintype

/-- Numeric value of a price. -/
def BertrandPrice.toReal : BertrandPrice → ℝ
  | p1 => 1 | p2 => 2 | p3 => 3

open BertrandPrice in
/-- Per-firm Bertrand profit table given marginal cost `c = 1`. -/
noncomputable def bertrandProfit : BertrandPrice → BertrandPrice → ℝ
  | p1, p1 => 0
  | p1, p2 => 0       -- price-floor undercut: revenue 0
  | p1, p3 => 0
  | p2, p1 => 0       -- priced out
  | p2, p2 => 1/2     -- shared monopoly profit at p=2
  | p2, p3 => 1       -- undercuts p3, captures market at p=2
  | p3, p1 => 0
  | p3, p2 => 0
  | p3, p3 => 1       -- shared at p=3

/-- The Bertrand duopoly NFG. -/
noncomputable def bertrandDuopoly : NFGGame Bool (fun _ => BertrandPrice) where
  Outcome := ∀ _ : Bool, BertrandPrice
  outcome := id
  utility s p :=
    if p then bertrandProfit (s true) (s false)
    else bertrandProfit (s false) (s true)

/-- Both firms playing `p2` (the strict undercut-resistant Nash). -/
def bertrand_p2_p2 : StrategyProfile (fun _ : Bool => BertrandPrice) :=
  fun _ => BertrandPrice.p2

/-- Both firms playing `p1` (the weak competitive-floor Nash). -/
def bertrand_p1_p1 : StrategyProfile (fun _ : Bool => BertrandPrice) :=
  fun _ => BertrandPrice.p1

/-- `(p2, p2)` is a Nash equilibrium of the Bertrand duopoly. -/
theorem bertrand_p2_is_nash : IsNashPure bertrandDuopoly bertrand_p2_p2 := by
  intro i a'
  cases i <;> cases a' <;>
    (simp [bertrandDuopoly, bertrand_p2_p2, bertrandProfit, deviate, Function.update];
     try linarith)

/-- `(p1, p1)` is a (weak) Nash equilibrium: at the price floor,
undercutting is impossible and overcutting yields zero (no profit). -/
theorem bertrand_p1_is_nash : IsNashPure bertrandDuopoly bertrand_p1_p1 := by
  intro i a'
  cases i <;> cases a' <;>
    simp [bertrandDuopoly, bertrand_p1_p1, bertrandProfit, deviate, Function.update]

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
