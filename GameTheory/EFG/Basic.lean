import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad

import GameTheory.Core.KernelGame
import GameTheory.Concepts.SolutionConcepts

/-!
# Extensive-Form Games (EFG)

Extensive-form game trees parameterized by an `InfoStructure` that maps
info-set IDs to player + action arity.

Design:
- `InfoStructure` maps info-set ids to player + arity (with `arity_pos`)
- `GameTree` decision nodes store only the info-set id `I`
- Strategy types are cleanly per-info-set with no `0 < n` guards
- Chance nodes use `Fin k` with a proof `0 < k`
- Distributional semantics only (`evalDist`); EU is external via `KernelGame`

-/

namespace EFG

open GameTheory

structure InfoStructure where
  n : Nat
  Infoset : Fin n → Type
  [fInfo : ∀ p, Fintype (Infoset p)]
  [dInfo : ∀ p, DecidableEq (Infoset p)]
  arity : (p : Fin n) → Infoset p → Nat
  arity_pos : ∀ p I, 0 < arity p I

abbrev InfoStructure.Player (S : InfoStructure) : Type :=
  Fin S.n

abbrev InfoStructure.Act (S : InfoStructure) {p : S.Player} (I : S.Infoset p) : Type :=
  Fin (S.arity p I)

attribute [instance] InfoStructure.fInfo InfoStructure.dInfo

inductive GameTree (S : InfoStructure) (Outcome : Type) where
  | terminal (z : Outcome)
  | chance (k : Nat) (μ : PMF (Fin k)) (hk : 0 < k)
      (next : Fin k → GameTree S Outcome)
  | decision {p: S.Player} (I : S.Infoset p) (next : S.Act I → GameTree S Outcome)

structure EFGGame where
  inf : InfoStructure
  Outcome : Type
  tree : GameTree inf Outcome
  utility : Outcome → Payoff inf.Player


-- ============================================================================
-- Strategy types
-- ============================================================================

def PureStrategy (S : InfoStructure) (p : S.Player) : Type :=
  (I : S.Infoset p) → S.Act I

instance {S : InfoStructure} {p : S.Player} : Fintype (PureStrategy S p) :=
  Pi.instFintype

abbrev MixedProfile (S : InfoStructure) : Type :=
  (p : S.Player) → PMF (PureStrategy S p)

def BehavioralStrategy (S : InfoStructure) (p : S.Player) :=
  (I : S.Infoset p) → PMF (S.Act I)

/-- A pure strategy profile: each player has their own pure strategy. -/
abbrev PureProfile (S : InfoStructure) :=
  (p : Fin S.n) → PureStrategy S p

/-- A behavioral strategy profile: each player has their own behavioral strategy. -/
abbrev BehavioralProfile (S : InfoStructure) :=
  (p : Fin S.n) → BehavioralStrategy S p


/-- Lift a pure strategy profile to a behavioral one (point mass at each info set). -/
noncomputable def pureToBehavioral {S : InfoStructure} (σ : PureProfile S) : BehavioralProfile S :=
  fun p I => PMF.pure (σ p I)

-- ============================================================================
-- Evaluation
-- ============================================================================

/-- Evaluate under a behavioral profile, returning a PMF over outcomes. -/
noncomputable def GameTree.evalDist {S : InfoStructure} {Outcome : Type}
    (σ : BehavioralProfile S) : GameTree S Outcome → PMF Outcome
  | .terminal z => PMF.pure z
  | .chance _k μ _hk next => μ.bind (fun b => (next b).evalDist σ)
  | .decision (p := p) I next => (σ p I).bind (fun a => (next a).evalDist σ)

-- ============================================================================
-- Simp lemmas
-- ============================================================================

@[simp] theorem evalDist_terminal {S : InfoStructure} {Outcome : Type}
    (σ : BehavioralProfile S) (z : Outcome) :
    (GameTree.terminal z : GameTree S Outcome).evalDist σ = PMF.pure z := rfl

@[simp] theorem evalDist_chance {S : InfoStructure} {Outcome : Type}
    (σ : BehavioralProfile S)
    (k : Nat) (μ : PMF (Fin k)) {hk : 0 < k} (next : Fin k → GameTree S Outcome) :
    (GameTree.chance k μ hk next).evalDist σ =
    μ.bind (fun b => (next b).evalDist σ) := rfl

@[simp] theorem evalDist_decision {S : InfoStructure} {Outcome : Type}
    (σ : BehavioralProfile S) {p : S.Player} (I : S.Infoset p)
    (next : S.Act I → GameTree S Outcome) :
    (GameTree.decision I next).evalDist σ =
    (σ p I).bind (fun a => (next a).evalDist σ) := rfl

-- ============================================================================
-- Deterministic trees
-- ============================================================================

/-- A game tree is deterministic if it has no chance nodes. -/
inductive IsDeterministic {S : InfoStructure} {Outcome : Type} :
    GameTree S Outcome → Prop where
  | terminal (z : Outcome) : IsDeterministic (.terminal z)
  | decision {p : S.Player} (I : S.Infoset p) (next : S.Act I → GameTree S Outcome) :
      (∀ a, IsDeterministic (next a)) → IsDeterministic (.decision I next)

/-- Deterministic evaluation of a game tree under a pure strategy profile.
    At chance nodes (which cannot appear in a deterministic tree),
    an arbitrary branch is taken as junk. -/
def GameTree.evalPure {S : InfoStructure} {Outcome : Type}
    (t : GameTree S Outcome) (σ : PureProfile S) : Outcome :=
  match t with
  | .terminal z => z
  | .chance _k _μ hk next => (next ⟨0, hk⟩).evalPure σ
  | .decision (p := p) I next => (next (σ p I)).evalPure σ

@[simp] theorem evalPure_terminal {S : InfoStructure} {Outcome : Type}
    (σ : PureProfile S) (z : Outcome) :
    (GameTree.terminal z : GameTree S Outcome).evalPure σ = z := rfl

@[simp] theorem evalPure_decision {S : InfoStructure} {Outcome : Type}
    (σ : PureProfile S) {p : S.Player} (I : S.Infoset p)
    (next : S.Act I → GameTree S Outcome) :
    (GameTree.decision I next).evalPure σ = (next (σ p I)).evalPure σ := rfl

/-- For a deterministic tree, `evalDist` under a pure behavioral profile equals
    `PMF.pure` of the deterministic evaluation. -/
theorem evalDist_pureToBehavioral_eq_pure {S : InfoStructure} {Outcome : Type}
    (t : GameTree S Outcome) (σ : PureProfile S) (hd : IsDeterministic t) :
    t.evalDist (pureToBehavioral σ) = PMF.pure (t.evalPure σ) := by
  induction hd with
  | terminal z => rfl
  | decision I next _hall ih =>
    simp only [evalDist_decision, pureToBehavioral, PMF.pure_bind, GameTree.evalPure]
    exact ih (σ _ I)

/-- EFG outcome kernel: behavioral profile → PMF over outcomes. -/
noncomputable def GameTree.toKernel {S : InfoStructure} {Outcome : Type}
    (t : GameTree S Outcome) :
    Math.Probability.Kernel (BehavioralProfile S) Outcome :=
  fun σ => t.evalDist σ

-- ============================================================================
-- DecisionNodeIn
-- ============================================================================

/-- A decision node with info set `I` (of player `p`) appears somewhere in a `GameTree`. -/
inductive DecisionNodeIn {S : InfoStructure} {Outcome : Type} {p : S.Player} (I : S.Infoset p) :
    GameTree S Outcome → Prop where
  | root (next : S.Act I → GameTree S Outcome) : DecisionNodeIn I (.decision I next)
  | in_chance (k μ hk next b) : DecisionNodeIn I (next b) →
      DecisionNodeIn I (.chance k μ hk next)
  | in_decision {q : S.Player} (I' : S.Infoset q) (next : S.Act I' → GameTree S Outcome) (a) :
      DecisionNodeIn I (next a) →
      DecisionNodeIn I (.decision I' next)

/-- No decision node can appear inside a terminal tree. -/
theorem DecisionNodeIn_terminal_false {S : InfoStructure} {Outcome : Type}
    {p : S.Player} {I : S.Infoset p} {z : Outcome}
    (h : DecisionNodeIn I (GameTree.terminal (S := S) z)) : False := by
  cases h

/-- Inversion for `DecisionNodeIn` on a chance node. -/
theorem DecisionNodeIn_chance_inv {S : InfoStructure} {Outcome : Type}
    {p : S.Player} {I : S.Infoset p} {k : Nat} {μ : PMF (Fin k)} {hk : 0 < k}
    {next : Fin k → GameTree S Outcome}
    (h : DecisionNodeIn I (.chance k μ hk next)) :
    ∃ b, DecisionNodeIn I (next b) := by
  cases h with
  | in_chance _ _ _ _ b hsub => exact ⟨b, hsub⟩

/-- Inversion for `DecisionNodeIn` on a decision node. -/
theorem DecisionNodeIn_decision_inv {S : InfoStructure} {Outcome : Type}
    {p q : S.Player} {I : S.Infoset p} {I' : S.Infoset q}
    {next : S.Act I' → GameTree S Outcome}
    (h : DecisionNodeIn I (.decision I' next)) :
    (p = q ∧ HEq I I') ∨ ∃ a, DecisionNodeIn I (next a) := by
  cases h with
  | root _ => exact Or.inl ⟨rfl, HEq.rfl⟩
  | in_decision _ _ a hsub => exact Or.inr ⟨a, hsub⟩

-- ============================================================================
-- Swap theorems
-- ============================================================================

/-- Swapping two independent decision nodes preserves the outcome distribution. -/
theorem swap_decisions {S : InfoStructure} {Outcome : Type}
    (σ : BehavioralProfile S) {p₁ p₂ : S.Player}
    (I₁ : S.Infoset p₁) (I₂ : S.Infoset p₂)
    (grid : S.Act I₁ → S.Act I₂ → GameTree S Outcome) :
    (GameTree.decision I₁ (fun i =>
      GameTree.decision I₂ (fun j => grid i j))).evalDist σ =
    (GameTree.decision I₂ (fun j =>
      GameTree.decision I₁ (fun i => grid i j))).evalDist σ := by
  simp only [evalDist_decision]
  exact PMF.bind_comm (σ p₁ I₁) (σ p₂ I₂) (fun i j => (grid i j).evalDist σ)

/-- Swapping a chance node and a decision node preserves the outcome distribution. -/
theorem swap_chance_decision {S : InfoStructure} {Outcome : Type}
    (σ : BehavioralProfile S) {p : S.Player} (I : S.Infoset p)
    (nc : Nat) (μ : PMF (Fin nc)) {hc : 0 < nc}
    (grid : Fin nc → S.Act I → GameTree S Outcome) :
    (GameTree.chance nc μ hc (fun c =>
      GameTree.decision I (fun d => grid c d))).evalDist σ =
    (GameTree.decision I (fun d =>
      GameTree.chance nc μ hc (fun c => grid c d))).evalDist σ := by
  simp only [evalDist_chance, evalDist_decision]
  exact PMF.bind_comm μ (σ p I) (fun c d => (grid c d).evalDist σ)

/-- Swapping two independent chance nodes preserves the outcome distribution. -/
theorem swap_chances {S : InfoStructure} {Outcome : Type}
    (σ : BehavioralProfile S)
    (k₁ k₂ : Nat) (μ₁ : PMF (Fin k₁)) (μ₂ : PMF (Fin k₂))
    {hk₁ : 0 < k₁} {hk₂ : 0 < k₂}
    (grid : Fin k₁ → Fin k₂ → GameTree S Outcome) :
    (GameTree.chance k₁ μ₁ hk₁ (fun c₁ =>
      GameTree.chance k₂ μ₂ hk₂ (fun c₂ => grid c₁ c₂))).evalDist σ =
    (GameTree.chance k₂ μ₂ hk₂ (fun c₂ =>
      GameTree.chance k₁ μ₁ hk₁ (fun c₁ => grid c₁ c₂))).evalDist σ := by
  simp only [evalDist_chance]
  exact PMF.bind_comm μ₁ μ₂ (fun c₁ c₂ => (grid c₁ c₂).evalDist σ)

-- ============================================================================
-- toKernelGame
-- ============================================================================

/-- Convert an EFG game to a kernel-based game. -/
noncomputable def EFGGame.toKernelGame (G : EFGGame) :
    KernelGame G.inf.Player where
  Strategy := BehavioralStrategy G.inf
  Outcome := G.Outcome
  utility := G.utility
  outcomeKernel := fun σ => G.tree.evalDist σ

/-- Strategic form of an EFG as a `KernelGame`, preserving outcome distributions.
    Strategies are pure contingent plans; the outcome kernel evaluates the game
    tree under the corresponding behavioral profile. -/
noncomputable def EFGGame.toStrategicKernelGame (G : EFGGame) :
    KernelGame G.inf.Player where
  Strategy := fun p => PureStrategy G.inf p
  Outcome := G.Outcome
  utility := G.utility
  outcomeKernel := fun σ => G.tree.evalDist (pureToBehavioral σ)

/-- The strategic kernel game has the same outcome semantics as the behavioral one
    under `pureToBehavioral`. -/
theorem toStrategicKernelGame_outcomeKernel (G : EFGGame) (σ : PureProfile G.inf) :
    G.toStrategicKernelGame.outcomeKernel σ =
    G.toKernelGame.outcomeKernel (pureToBehavioral σ) := by
  rfl

/-- Semantics equality alias for the strategic-form bridge. -/
theorem toStrategicKernelGame_semantics_eq (G : EFGGame) (σ : PureProfile G.inf) :
    G.toStrategicKernelGame.outcomeKernel σ =
    G.toKernelGame.outcomeKernel (pureToBehavioral σ) :=
  toStrategicKernelGame_outcomeKernel G σ

/-- The strategic kernel game has the same joint utility distribution as the
    behavioral EFG kernel game under `pureToBehavioral`. -/
theorem toStrategicKernelGame_udist (G : EFGGame) (σ : PureProfile G.inf) :
    G.toStrategicKernelGame.udist σ =
    G.toKernelGame.udist (pureToBehavioral σ) := rfl

/-- Updating a pure profile and then lifting to behavioral is the same as
    lifting first and then updating the behavioral profile. -/
theorem pureToBehavioral_update {S : InfoStructure}
    (σ : PureProfile S) (p : S.Player) (s' : PureStrategy S p) :
    pureToBehavioral (Function.update σ p s') =
    Function.update (pureToBehavioral σ) p (fun I => PMF.pure (s' I)) := by
  funext p' I
  by_cases h : p' = p
  · subst h; simp [pureToBehavioral]
  · simp [pureToBehavioral, h]

/-- Reinterpret an EFG game with the same meta-data and a different tree root. -/
def EFGGame.withTree (G : EFGGame) (t : GameTree G.inf G.Outcome) : EFGGame where
  inf := G.inf
  Outcome := G.Outcome
  tree := t
  utility := G.utility

/-- Subgame-perfect equilibrium w.r.t. a supplied subgame predicate and preference. -/
def EFGGame.IsSubgamePerfectFor (G : EFGGame)
    (isSubgame : GameTree G.inf G.Outcome → Prop)
    (pref : G.inf.Player → PMF G.Outcome → PMF G.Outcome → Prop)
    (σ : PureProfile G.inf) : Prop :=
  ∀ t : GameTree G.inf G.Outcome, isSubgame t →
    (G.withTree t).toStrategicKernelGame.IsNashFor pref σ

/-- EU-specialized subgame-perfect equilibrium. -/
def EFGGame.IsSubgamePerfect (G : EFGGame)
    (isSubgame : GameTree G.inf G.Outcome → Prop)
    (σ : PureProfile G.inf) : Prop :=
  G.IsSubgamePerfectFor isSubgame (KernelGame.euPref G.toStrategicKernelGame) σ

-- ============================================================================
-- Perfect recall
-- ============================================================================

/-- A single step in a play history.
    We store *typed* choices, so histories never mention out-of-range indices. -/
inductive HistoryStep (S : InfoStructure) where
  | chance (k : Nat) (b : Fin k)
  | action (p : S.Player) (I : S.Infoset p) (act : S.Act I)

/-- Strategy + belief pair for sequential-style refinements. -/
structure EFGGame.Assessment (G : EFGGame) where
  strategy : BehavioralProfile G.inf
  beliefs : ∀ {p : G.inf.Player}, G.inf.Infoset p → PMF (List (HistoryStep G.inf))

/-- Generic sequential-equilibrium schema from supplied rationality/consistency predicates. -/
def EFGGame.IsSequentialEqFor (G : EFGGame)
    (SequentiallyRational : G.Assessment → Prop)
    (BayesConsistent : G.Assessment → Prop)
    (A : G.Assessment) : Prop :=
  SequentiallyRational A ∧ BayesConsistent A

/-- Perfect Bayesian equilibrium schema (same shape, different intended predicates). -/
def EFGGame.IsPerfectBayesianEqFor (G : EFGGame)
    (SequentiallyRational : G.Assessment → Prop)
    (BayesConsistent : G.Assessment → Prop)
    (A : G.Assessment) : Prop :=
  G.IsSequentialEqFor SequentiallyRational BayesConsistent A

/-- Reachability: `ReachBy h root target` means following history `h` from
    `root` leads to `target`. History is earliest step first. -/
inductive ReachBy {S : InfoStructure} {Outcome : Type} :
    List (HistoryStep S) → GameTree S Outcome → GameTree S Outcome → Prop where
  | here (t) : ReachBy [] t t
  | chance {k μ hk next rest s} (b : Fin k) :
      ReachBy rest (next b) s →
      ReachBy (HistoryStep.chance k b :: rest) (.chance k μ hk next) s
  | action {p : S.Player} {I : S.Infoset p} {next rest s} (a : S.Act I) :
      ReachBy rest (next a) s →
      ReachBy (HistoryStep.action p I a :: rest) (.decision I next) s

/-- Extract the subsequence of actions by player `who` from a history,
    keeping the infoset and the *typed* action taken there. -/
def playerHistory (S : InfoStructure) (who : S.Player) :
    List (HistoryStep S) → List (Σ I : S.Infoset who, S.Act I)
  | [] => []
  | HistoryStep.action p I act :: rest =>
      if h : p = who then
        (by subst h; exact ⟨I, act⟩) :: playerHistory S who rest
      else
        playerHistory S who rest
  | HistoryStep.chance _k _b :: rest =>
      playerHistory S who rest

/-- Perfect recall: any two paths to nodes in the same info set `I`
    must have the same player-`I`-owner action history. -/
def PerfectRecall {S : InfoStructure} {Outcome : Type}
    (t : GameTree S Outcome) : Prop :=
  ∀ (h₁ h₂ : List (HistoryStep S)) {p : S.Player} (I : S.Infoset p)
    (next₁ next₂ : S.Act I → GameTree S Outcome),
    ReachBy h₁ t (.decision I next₁) →
    ReachBy h₂ t (.decision I next₂) →
    playerHistory S p h₁ = playerHistory S p h₂

-- ============================================================================
-- Structural lemmas
-- ============================================================================

/-- Terminal trees have perfect recall (vacuously). -/
theorem PerfectRecall_terminal {S : InfoStructure} {Outcome : Type}
    (z : Outcome) : PerfectRecall (GameTree.terminal (S := S) z) := by
  intro h₁ h₂ p I next₁ next₂ hr₁ _hr₂
  nomatch hr₁

/-- If each info set appears at most once in the tree, then perfect recall holds.
    (No repeated info sets ⇒ all paths to same info set are the same path.) -/
theorem PerfectRecall_single_infoSet {S : InfoStructure} {Outcome : Type}
    (t : GameTree S Outcome)
    (huniq : ∀ (h₁ h₂ : List (HistoryStep S)) {p : S.Player} (I : S.Infoset p)
      (next₁ next₂ : S.Act I → GameTree S Outcome),
      ReachBy h₁ t (.decision I next₁) →
      ReachBy h₂ t (.decision I next₂) →
      h₁ = h₂ ∧ HEq next₁ next₂) :
    PerfectRecall t := by
  intro h₁ h₂ p I next₁ next₂ hr₁ hr₂
  obtain ⟨rfl, _⟩ := huniq h₁ h₂ I next₁ next₂ hr₁ hr₂
  rfl

/-- No path from a terminal node can reach a decision node. -/
theorem ReachBy_terminal_absurd {S : InfoStructure} {Outcome : Type}
    {h : List (HistoryStep S)} {z : Outcome} {p : S.Player} {I : S.Infoset p}
    {next : S.Act I → GameTree S Outcome}
    (hr : ReachBy h (.terminal (S := S) z) (.decision I next)) : False := by
  nomatch hr

/-- Inversion for `ReachBy` from a decision node to a decision node. -/
theorem ReachBy_decision_inv {S : InfoStructure} {Outcome : Type}
    {h : List (HistoryStep S)} {p q : S.Player}
    {I₀ : S.Infoset p} {I : S.Infoset q}
    {f : S.Act I₀ → GameTree S Outcome}
    {next : S.Act I → GameTree S Outcome}
    (hr : ReachBy h (.decision I₀ f) (.decision I next)) :
    (h = [] ∧ p = q ∧ HEq I₀ I ∧ HEq f next) ∨
    (∃ (a : S.Act I₀) (rest : List (HistoryStep S)),
      h = HistoryStep.action p I₀ a :: rest ∧
      ReachBy rest (f a) (.decision I next)) := by
  cases hr with
  | here =>
      exact Or.inl ⟨rfl, rfl, HEq.rfl, HEq.rfl⟩
  | action a hr' =>
      exact Or.inr ⟨a, _, rfl, hr'⟩

/-- Inversion for `ReachBy` from a chance node to a decision node. -/
theorem ReachBy_chance_inv' {S : InfoStructure} {Outcome : Type}
    {h : List (HistoryStep S)} {k : Nat} {μ : PMF (Fin k)} {hk : 0 < k}
    {f : Fin k → GameTree S Outcome} {p : S.Player} {I : S.Infoset p}
    {next : S.Act I → GameTree S Outcome}
    (hr : ReachBy h (.chance k μ hk f) (.decision I next)) :
    ∃ (b : Fin k) (rest : List (HistoryStep S)),
      h = HistoryStep.chance k b :: rest ∧
      ReachBy rest (f b) (.decision I next) := by
  cases hr with
  | chance b hr' => exact ⟨b, _, rfl, hr'⟩

/-- Concatenation lemma: if `ReachBy h₁ root mid` and `ReachBy h₂ mid target`,
    then `ReachBy (h₁ ++ h₂) root target`. -/
theorem ReachBy_append {S : InfoStructure} {Outcome : Type}
    {h₁ h₂ : List (HistoryStep S)}
    {root mid target : GameTree S Outcome}
    (hr₁ : ReachBy h₁ root mid) (hr₂ : ReachBy h₂ mid target) :
    ReachBy (h₁ ++ h₂) root target := by
  induction hr₁ with
  | here _ => exact hr₂
  | chance b _ ih => exact .chance b (ih hr₂)
  | action a _ ih => exact .action a (ih hr₂)

/-- Splitting lemma: if `ReachBy (h₁ ++ h₂) root target`, then there exists
    a `mid` such that `ReachBy h₁ root mid` and `ReachBy h₂ mid target`. -/
theorem ReachBy_split {S : InfoStructure} {Outcome : Type}
    (h₁ h₂ : List (HistoryStep S))
    {root target : GameTree S Outcome}
    (hr : ReachBy (h₁ ++ h₂) root target) :
    ∃ mid, ReachBy h₁ root mid ∧ ReachBy h₂ mid target := by
  induction h₁ generalizing root with
  | nil => exact ⟨root, .here root, hr⟩
  | cons step rest ih =>
    match hr with
    | .chance b htail =>
      obtain ⟨mid, hmid₁, hmid₂⟩ := ih htail
      exact ⟨mid, .chance b hmid₁, hmid₂⟩
    | .action a htail =>
      obtain ⟨mid, hmid₁, hmid₂⟩ := ih htail
      exact ⟨mid, .action a hmid₁, hmid₂⟩

/-- `playerHistory` distributes over concatenation. -/
theorem playerHistory_append (S : InfoStructure) (who : S.Player)
    (h₁ h₂ : List (HistoryStep S)) :
    playerHistory S who (h₁ ++ h₂) =
    playerHistory S who h₁ ++ playerHistory S who h₂ := by
  induction h₁ with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | chance k b =>
      simp only [playerHistory, List.cons_append]
      exact ih
    | action p I act =>
      simp only [playerHistory, List.cons_append]
      split <;> simp_all

end EFG
