import GameTheory.EFG
import GameTheory.EFG_NFG
import Mathlib.Tactic.Linarith

/-!
# Concrete Sequential Refinements for Extensive-Form Games

Concrete definitions for subgame perfection and related refinements,
building on the schema-based definitions in `EFG.lean`.

## Main definitions

- `IsSubgame` — concrete subgame identification (informationally closed subtree)
- `IsSubgamePerfectEq` — subgame-perfect equilibrium using the concrete predicate
- `IsPerfectInfo` — perfect-information trees (each info-set appears at most once)

## Main theorems

- `isSubgame_root` — the root is always a subgame of itself
- `isSubgame_terminal` — terminal nodes are subgames (when reachable)
- `spe_implies_nash` — SPE implies Nash equilibrium in the strategic form
- `spe_implies_isNash` — SPE implies Nash (EU formulation)
- `perfectInfo_isSubgame_decision` — in perfect-info games, every decision node
  starts a subgame
- Entry deterrence game: SPE and non-SPE Nash verification
-/

namespace EFG

open GameTheory

-- ============================================================================
-- Helper lemmas
-- ============================================================================

theorem decisionNodeIn_reachBy {S : InfoStructure} {Outcome : Type}
    {p : S.Player} {I : S.Infoset p} {t : GameTree S Outcome}
    (h : DecisionNodeIn I t) :
    ∃ (hist : List (HistoryStep S)) (next : S.Act I → GameTree S Outcome),
      ReachBy hist t (.decision I next) := by
  induction h with
  | root next => exact ⟨[], next, .here _⟩
  | in_chance k μ hk next' b _hIn ih =>
    obtain ⟨hist, next, hReach⟩ := ih
    exact ⟨HistoryStep.chance k b :: hist, next, .chance b hReach⟩
  | in_decision I' next' a _hIn ih =>
    obtain ⟨hist, next, hReach⟩ := ih
    exact ⟨HistoryStep.action _ I' a :: hist, next, .action a hReach⟩

theorem reachBy_deterministic {S : InfoStructure} {Outcome : Type}
    {h : List (HistoryStep S)} {root t₁ t₂ : GameTree S Outcome}
    (hr₁ : ReachBy h root t₁) (hr₂ : ReachBy h root t₂) : t₁ = t₂ := by
  induction hr₁ with
  | here _ => cases hr₂; rfl
  | chance b _ ih => cases hr₂ with | chance _ hr₂' => exact ih hr₂'
  | action a _ ih => cases hr₂ with | action _ hr₂' => exact ih hr₂'

-- ============================================================================
-- Concrete subgame identification
-- ============================================================================

def IsSubgame {S : InfoStructure} {Outcome : Type}
    (root t : GameTree S Outcome) : Prop :=
  (∃ h, ReachBy h root t) ∧
  ∀ (p : S.Player) (I : S.Infoset p), DecisionNodeIn I t →
    ∀ (h : List (HistoryStep S)) (next : S.Act I → GameTree S Outcome),
      ReachBy h root (.decision I next) → ∃ h', ReachBy h' t (.decision I next)

theorem isSubgame_root {S : InfoStructure} {Outcome : Type}
    (root : GameTree S Outcome) : IsSubgame root root :=
  ⟨⟨[], .here root⟩, fun _ _ _ h next hR => ⟨h, hR⟩⟩

theorem isSubgame_terminal {S : InfoStructure} {Outcome : Type}
    {root : GameTree S Outcome} {z : Outcome} {h₀ : List (HistoryStep S)}
    (hreach : ReachBy h₀ root (.terminal z)) : IsSubgame root (.terminal z) :=
  ⟨⟨h₀, hreach⟩, fun _ _ hIn _ _ _ => absurd hIn (by intro h; cases h)⟩

-- ============================================================================
-- Concrete SPE and bridge theorems
-- ============================================================================

def EFGGame.IsSubgamePerfectEq (G : EFGGame) (σ : PureProfile G.inf) : Prop :=
  G.IsSubgamePerfect (IsSubgame G.tree) σ

theorem spe_implies_nash (G : EFGGame) (σ : PureProfile G.inf)
    (h : G.IsSubgamePerfectEq σ) :
    G.toStrategicKernelGame.IsNashFor
      (KernelGame.euPref G.toStrategicKernelGame) σ :=
  h G.tree (isSubgame_root G.tree)

theorem spe_implies_isNash (G : EFGGame) (σ : PureProfile G.inf)
    (h : G.IsSubgamePerfectEq σ) : G.toStrategicKernelGame.IsNash σ := by
  rw [KernelGame.IsNash_iff_IsNashFor_eu]; exact spe_implies_nash G σ h

-- ============================================================================
-- Terminal subgames are trivially Nash
-- ============================================================================

theorem terminal_isNashFor_euPref {G : EFGGame} (z : G.Outcome)
    (σ : PureProfile G.inf) :
    (G.withTree (.terminal z)).toStrategicKernelGame.IsNashFor
      (KernelGame.euPref G.toStrategicKernelGame) σ := by
  intro who _s'
  change expect (PMF.pure z) (fun ω => G.utility ω who) ≥
         expect (PMF.pure z) (fun ω => G.utility ω who)
  exact le_refl _

-- ============================================================================
-- Perfect information
-- ============================================================================

def IsPerfectInfo {S : InfoStructure} {Outcome : Type}
    (t : GameTree S Outcome) : Prop :=
  ∀ (h₁ h₂ : List (HistoryStep S)) (p : S.Player) (I : S.Infoset p)
    (next₁ next₂ : S.Act I → GameTree S Outcome),
    ReachBy h₁ t (.decision I next₁) → ReachBy h₂ t (.decision I next₂) →
    h₁ = h₂ ∧ HEq next₁ next₂

theorem perfectInfo_implies_perfectRecall {S : InfoStructure} {Outcome : Type}
    (t : GameTree S Outcome) (hpi : IsPerfectInfo t) : PerfectRecall t :=
  PerfectRecall_single_infoSet t hpi

theorem perfectInfo_isSubgame_decision {S : InfoStructure} {Outcome : Type}
    (root : GameTree S Outcome) (hpi : IsPerfectInfo root)
    {p : S.Player} (I : S.Infoset p) (next : S.Act I → GameTree S Outcome)
    {h₀ : List (HistoryStep S)} (hreach : ReachBy h₀ root (.decision I next)) :
    IsSubgame root (.decision I next) := by
  refine ⟨⟨h₀, hreach⟩, fun q J hInSub h' next' hReachRoot => ?_⟩
  obtain ⟨h_sub, nextJ, hReachSub⟩ := decisionNodeIn_reachBy hInSub
  obtain ⟨hEq, _⟩ := hpi (h₀ ++ h_sub) h' q J _ next'
    (ReachBy_append hreach hReachSub) hReachRoot
  rw [← hEq] at hReachRoot
  obtain ⟨mid, hMid1, hMid2⟩ := ReachBy_split h₀ h_sub hReachRoot
  have hmid := reachBy_deterministic hreach hMid1; subst hmid
  exact ⟨h_sub, hMid2⟩

-- ============================================================================
-- Entry Deterrence Game
-- ============================================================================

abbrev entryS : InfoStructure where
  n := 2; Infoset := fun _ => Unit; arity := fun _ _ => 2
  arity_pos := fun _ _ => by omega

noncomputable abbrev entryTree : GameTree entryS (Payoff entryS.Player) :=
  .decision (p := (0 : Fin 2)) () fun
    | 0 => .decision (p := (1 : Fin 2)) () fun
      | 0 => .terminal (fun i => if i == (0 : Fin 2) then 2 else 2)
      | 1 => .terminal (fun i => if i == (0 : Fin 2) then 0 else 0)
    | 1 => .terminal (fun i => if i == (0 : Fin 2) then 1 else 3)

noncomputable abbrev entryGame : EFGGame where
  inf := entryS; Outcome := Payoff entryS.Player; tree := entryTree; utility := id

def entrySPE : PureProfile entryS := fun _ _ => (0 : Fin 2)
def entryNash : PureProfile entryS := fun _ _ => (1 : Fin 2)

theorem entry_spe_eu_p0 :
    entryGame.toStrategicKernelGame.eu entrySPE (0 : Fin 2) = 2 := by
  simp [KernelGame.eu, EFGGame.toStrategicKernelGame,
        GameTree.evalDist, pureToBehavioral, entrySPE, expect_pure]

theorem entry_nash_eu_p0 :
    entryGame.toStrategicKernelGame.eu entryNash (0 : Fin 2) = 1 := by
  simp [KernelGame.eu, EFGGame.toStrategicKernelGame,
        GameTree.evalDist, pureToBehavioral, entryNash, expect_pure]

-- ============================================================================
-- Nash proof tactic: simp + omega to close all Fin 2 EFG cases
-- ============================================================================

-- The key insight: after simp with Function.update reduces the profile,
-- we need to also reduce `match`/`if` on Fin 2, `pureToBehavioral`, and
-- `evalDist` on the resulting subtree. Using `simp` with the full set
-- after the `rcases` on Fin 2 action value handles this.

private theorem entryS_act_eq (a : Fin 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp

-- ============================================================================
-- SPE proof
-- ============================================================================

open Classical in
theorem entrySPE_isSPE : entryGame.IsSubgamePerfectEq entrySPE := by
  intro t ⟨⟨h, hReach⟩, _⟩
  -- Exhaustively enumerate reachable subtrees via cases on ReachBy
  cases hReach with
  | here =>
    -- t = root (P0's decision)
    intro who s'
    fin_cases who <;> (
      simp only [KernelGame.euPref, EFGGame.toStrategicKernelGame, EFGGame.withTree,
        KernelGame.outcomeKernel, GameTree.evalDist, pureToBehavioral,
        evalDist_decision, PMF.pure_bind, evalDist_terminal, expect_pure, entrySPE]
      rcases entryS_act_eq (s' ()) with h | h <;>
        simp [Function.update, h, pureToBehavioral, GameTree.evalDist,
              evalDist_decision, PMF.pure_bind, evalDist_terminal, expect_pure, entrySPE])
  | action a hRest =>
    fin_cases a
    · -- a = 0 (Enter): subtree is P1's decision
      simp only [Fin.isValue] at hRest
      cases hRest with
      | here =>
        -- t = P1's decision subtree
        intro who s'
        fin_cases who <;> (
          simp only [KernelGame.euPref, EFGGame.toStrategicKernelGame, EFGGame.withTree,
            KernelGame.outcomeKernel, GameTree.evalDist, pureToBehavioral,
            evalDist_decision, PMF.pure_bind, evalDist_terminal, expect_pure, entrySPE]
          rcases entryS_act_eq (s' ()) with h | h <;>
            simp [Function.update, h, pureToBehavioral, GameTree.evalDist,
                  evalDist_decision, PMF.pure_bind, evalDist_terminal, expect_pure, entrySPE])
      | action b hRest' =>
        -- Terminal after P1's action
        fin_cases b <;> (cases hRest' with | here => exact terminal_isNashFor_euPref _ _)
    · -- a = 1 (Stay Out): terminal
      simp only [Fin.isValue] at hRest
      cases hRest with
      | here => exact terminal_isNashFor_euPref _ _

open Classical in
theorem entryNash_isNash : entryGame.toStrategicKernelGame.IsNash entryNash := by
  intro who s'
  fin_cases who <;> (
    simp only [KernelGame.eu, EFGGame.toStrategicKernelGame, KernelGame.outcomeKernel,
      GameTree.evalDist, pureToBehavioral, evalDist_decision, PMF.pure_bind,
      evalDist_terminal, expect_pure, entryNash]
    rcases entryS_act_eq (s' ()) with h | h <;>
      simp [Function.update, h, pureToBehavioral, GameTree.evalDist,
            evalDist_decision, PMF.pure_bind, evalDist_terminal, expect_pure, entryNash])

open Classical in
theorem entryNash_not_spe : ¬ entryGame.IsSubgamePerfectEq entryNash := by
  intro hSPE
  have hSub : IsSubgame entryTree
      (.decision (p := (1 : Fin 2)) () fun
        | 0 => .terminal (fun i => if i == (0 : Fin 2) then 2 else 2)
        | 1 => .terminal (fun i => if i == (0 : Fin 2) then 0 else 0)) := by
    constructor
    · exact ⟨_, .action (0 : Fin 2) (.here _)⟩
    · intro p I hIn hist next' hReach
      cases hIn with
      | root _ =>
        rcases ReachBy_decision_inv hReach with ⟨_, hp, _, _⟩ | ⟨a, rest, _, hRest⟩
        · exact absurd hp (by decide)
        · fin_cases a
          · simp only [Fin.isValue] at hRest
            rcases ReachBy_decision_inv hRest with ⟨rfl, _, hI, hN⟩ | ⟨b, _, _, hb⟩
            · -- next' and the P1 subtree children match via HEq
              have hN' := (eq_of_heq hN).symm; subst hN'
              exact ⟨[], .here _⟩
            · fin_cases b <;> nomatch hb
          · simp only [Fin.isValue] at hRest; nomatch hRest
      | in_decision _ _ a hDeeper =>
        fin_cases a <;> exact absurd hDeeper (by intro h; cases h)
  have hNash := hSPE _ hSub
  have h1 := hNash (1 : Fin 2) (fun _ => (0 : Fin 2))
  simp only [KernelGame.euPref, EFGGame.toStrategicKernelGame, EFGGame.withTree,
    KernelGame.outcomeKernel, GameTree.evalDist, pureToBehavioral,
    evalDist_decision, PMF.pure_bind, evalDist_terminal, expect_pure,
    entryNash] at h1
  simp [Function.update, pureToBehavioral, GameTree.evalDist,
        evalDist_decision, PMF.pure_bind, evalDist_terminal, expect_pure] at h1
  linarith

theorem entrySPE_isNash : entryGame.toStrategicKernelGame.IsNash entrySPE :=
  spe_implies_isNash entryGame entrySPE entrySPE_isSPE

-- ============================================================================
-- Perfect recall
-- ============================================================================

private theorem entry_playerHistory_nil :
    ∀ h {p : entryS.Player} (I : entryS.Infoset p)
    (next : entryS.Act I → GameTree entryS (Payoff entryS.Player)),
    ReachBy h entryTree (.decision I next) →
    playerHistory entryS p h = [] := by
  intro h p I next hr
  rcases ReachBy_decision_inv hr with ⟨rfl, _, _, _⟩ | ⟨a, rest, rfl, hr'⟩
  · rfl
  · fin_cases a
    · simp only [Fin.isValue] at hr'
      rcases ReachBy_decision_inv hr' with ⟨rfl, rfl, _, _⟩ | ⟨b, _, rfl, hr''⟩
      · simp [playerHistory]
      · fin_cases b <;> nomatch hr''
    · simp only [Fin.isValue] at hr'; nomatch hr'

theorem entry_perfectRecall : PerfectRecall entryTree := by
  intro h₁ h₂ p I next₁ next₂ hr₁ hr₂
  rw [entry_playerHistory_nil h₁ I next₁ hr₁, entry_playerHistory_nil h₂ I next₂ hr₂]

end EFG
