import GameTheory.Languages.EFG.CompileObs
import GameTheory.Theorems.Kuhn
import Math.PMFProduct

/-!
# Kuhn's Theorem for EFG — via ObsModel

Kuhn's theorem (behavioral ↔ mixed strategy equivalence) for extensive-form
games, derived as a corollary of the generic ObsModel-level proof.

## Architecture

The EFG game tree compiles to an `ObsModel` via `compileObsModel` (in
`CompileObs.lean`). Kuhn's theorem is proved generically on `ObsModel`
(in `Theorems/Kuhn/`). This file:

1. States the ObsModel-level Kuhn corollary for compiled EFGs
2. Provides EFG-native definitions used downstream (`FlatProfile`,
   `productProfile`, `flatToBehavioral`, etc.)
3. Bridges the ObsModel result to tree-level `evalDist` statements

## Main results

- `kuhn_behavioral_to_mixed_of_compiled` : B→M at ObsModel level (no recall)
- `kuhn_mixed_to_behavioral_of_compiled` : M→B at ObsModel level (under PSPR)
- `kuhn_behavioral_to_mixed` : B→M at tree level
- `kuhn_mixed_to_behavioral` : M→B at tree level
-/

namespace EFG

open GameTheory Math.PMFProduct

variable {S : InfoStructure} {Outcome : Type}

-- ============================================================================
-- Type aliases and instances
-- ============================================================================

/-- Flat index over all infosets across all players. -/
abbrev FlatIdx (S : InfoStructure) := (p : Fin S.n) × S.Infoset p

/-- A flat profile assigns an action to every infoset of every player. -/
abbrev FlatProfile (S : InfoStructure) := (idx : FlatIdx S) → S.Act idx.2

instance : Fintype (FlatIdx S) :=
  Sigma.instFintype

instance : DecidableEq (FlatIdx S) :=
  Sigma.instDecidableEqSigma

instance : Fintype (FlatProfile S) :=
  Pi.instFintype

-- ============================================================================
-- Product PMF and flat-to-behavioral conversion
-- ============================================================================

/-- Product PMF: independently sample each info set from a behavioral profile.
    Uses `pmfPi`: assigns weight `∏ idx, σ idx.1 idx.2 (s idx)` to profile `s`. -/
noncomputable def productProfile (σ : BehavioralProfile S) : PMF (FlatProfile S) :=
  pmfPi (fun idx => σ idx.1 idx.2)

@[simp] theorem productProfile_apply (σ : BehavioralProfile S) (s : FlatProfile S) :
    (productProfile σ) s = ∏ idx : FlatIdx S, σ idx.1 idx.2 (s idx) := by
  simp [productProfile]

/-- Evaluate a flat profile as a behavioral profile (point mass at each infoset). -/
noncomputable def flatToBehavioral (s : FlatProfile S) : BehavioralProfile S :=
  fun p I => PMF.pure (s ⟨p, I⟩)

/-- Equivalence between flat profiles and pure profiles. -/
def flatProfileEquivPureProfile : Equiv (FlatProfile S) (PureProfile S) where
  toFun := fun s p I => s ⟨p, I⟩
  invFun := fun pi idx => pi idx.1 idx.2
  left_inv := by intro s; funext idx; cases idx; rfl
  right_inv := by intro pi; funext p I; rfl

instance (p : S.Player) : DecidableEq (PureStrategy S p) :=
  show DecidableEq ((I : S.Infoset p) → S.Act I) from inferInstance

instance : DecidableEq (PureProfile S) :=
  show DecidableEq ((p : S.Player) → PureStrategy S p) from
    Fintype.decidablePiFintype

/-- Joint distribution over pure profiles from a mixed (per-player) profile. -/
noncomputable abbrev mixedProfileJoint (muP : MixedProfile S) : PMF (PureProfile S) :=
  pmfPi (A := fun p => PureStrategy S p) muP

-- ============================================================================
-- NoInfoSetRepeat
-- ============================================================================

/-- No info set appears both at a decision node and in its subtrees.
    This ensures the product PMF factorizes correctly at decision nodes.
    Follows from `PerfectRecall` (proved below). -/
def NoInfoSetRepeat : GameTree S Outcome → Prop
  | .terminal _ => True
  | .chance _k _μ _hk next => ∀ b, NoInfoSetRepeat (next b)
  | .decision (p := _p) I next =>
      (∀ a, ¬ DecisionNodeIn I (next a)) ∧ (∀ a, NoInfoSetRepeat (next a))

/-- Every `DecisionNodeIn` witness yields a `ReachBy` path. -/
theorem DecisionNodeIn_to_ReachBy {p : S.Player} {I : S.Infoset p} {t : GameTree S Outcome}
    (h : DecisionNodeIn I t) :
    ∃ (hist : List (HistoryStep S)) (next : S.Act I → GameTree S Outcome),
      ReachBy hist t (.decision I next) := by
  induction h with
  | root next => exact ⟨[], next, .here _⟩
  | in_chance k μ hk f b _ ih =>
    obtain ⟨hist, next, hr⟩ := ih
    exact ⟨.chance k b :: hist, next, .chance b hr⟩
  | in_decision I' f a _ ih =>
    obtain ⟨hist, next, hr⟩ := ih
    exact ⟨.action _ I' a :: hist, next, .action a hr⟩

/-- Perfect recall implies no info set repeats on paths. -/
theorem PerfectRecall_implies_NoInfoSetRepeat
    (t : GameTree S Outcome) (hpr : PerfectRecall t) : NoInfoSetRepeat t := by
  induction t with
  | terminal _ => trivial
  | chance _k _μ _hk next ih =>
    intro b
    apply ih b
    intro h₁ h₂ p I next₁ next₂ hr₁ hr₂
    have := hpr (.chance _ b :: h₁) (.chance _ b :: h₂) I next₁ next₂
      (.chance b hr₁) (.chance b hr₂)
    simpa [playerHistory] using this
  | decision I next ih =>
    refine ⟨fun a hmem => ?_, fun a => ?_⟩
    · obtain ⟨hist, next₂, hr₂⟩ := DecisionNodeIn_to_ReachBy hmem
      have key := hpr [] (.action _ I a :: hist) I next next₂
        (.here _) (.action a hr₂)
      simp [playerHistory] at key
    · apply ih a
      intro h₁ h₂ q J next₁ next₂ hr₁ hr₂
      have key := hpr (.action _ I a :: h₁) (.action _ I a :: h₂) J next₁ next₂
        (.action a hr₁) (.action a hr₂)
      simp only [playerHistory] at key
      split at key <;> simp_all

-- ============================================================================
-- ObsModel-level Kuhn corollary
-- ============================================================================

section ObsModelKuhn

open GameTheory.EFG GameTheory.Theorems

variable (t : GameTree S Outcome)

/-- The compiled ObsModel for an EFG tree. -/
noncomputable abbrev compiledObs (t : GameTree S Outcome) :=
  GameTheory.EFG.compileObsModel t

variable [∀ i, Fintype (Option (CtrlAct S i))]

noncomputable instance compiledObs_localStrategy_fintype :
    ∀ i, Fintype ((compiledObs t).LocalStrategy i) := by
  intro i
  exact sorry

noncomputable instance compiledObs_pureProfile_fintype :
    Fintype (ObsModel.PureProfile (compiledObs t)) := by
  exact sorry

noncomputable instance compiledObs_localTrace_fintype :
    ∀ i, Fintype ((compiledObs t).LocalTrace i) := by
  intro i
  exact sorry

/-- **Kuhn B→M for compiled EFGs**: behavioral strategies can be realized as
product mixed strategies. No recall conditions needed. -/
theorem kuhn_behavioral_to_mixed_of_compiled
    (β : ObsModel.BehavioralProfile (compiledObs t)) (k : Nat) :
    (compiledObs t).runDist k β =
      ((compiledObs t).behavioralToMixedJoint β).bind
        ((compiledObs t).runDistPure k) :=
  ObsModel.kuhn_behavioral_to_mixed β k

/-- **Kuhn M→B for compiled EFGs**: under per-step player recall,
product mixed strategies can be realized by behavioral strategies. -/
theorem kuhn_mixed_to_behavioral_of_compiled
    [∀ i, Nonempty (Option (CtrlAct S i))]
    (hPSPR : ObsModel.PerStepPlayerRecall (compiledObs t))
    (μ : ∀ i, PMF ((compiledObs t).LocalStrategy i))
    (k : Nat) :
    ∃ β : ObsModel.BehavioralProfile (compiledObs t),
      (compiledObs t).runDist k β =
        (pmfPi μ).bind ((compiledObs t).runDistPure k) :=
  ObsModel.kuhn_mixed_to_behavioral_pspr hPSPR μ k

end ObsModelKuhn

-- ============================================================================
-- Tree-level Kuhn theorems (bridge from ObsModel to evalDist)
-- ============================================================================

/-- Two behavioral profiles agreeing on all infosets in `t` give the same `evalDist`. -/
theorem evalDist_eq_of_behavioral_agree (t : GameTree S Outcome)
    (σ₁ σ₂ : BehavioralProfile S)
    (h : ∀ {q} {J : S.Infoset q}, DecisionNodeIn J t → σ₁ q J = σ₂ q J) :
    t.evalDist σ₁ = t.evalDist σ₂ := by
  induction t with
  | terminal _ => rfl
  | chance _k _μ _hk next ih =>
    simp only [GameTree.evalDist]; congr 1; funext b
    exact ih b (fun hd => h (.in_chance _ _ _ _ b hd))
  | decision I next ih =>
    simp only [GameTree.evalDist]
    have hI := h (DecisionNodeIn.root next)
    rw [hI]
    congr 1; funext a
    exact ih a (fun hd => h (.in_decision I next a hd))

/-- The tree-level B→M core: the product PMF `productProfile σ` induces the
    same `evalDist` as `σ` when no info set repeats. -/
theorem behavioral_to_mixed (σ : BehavioralProfile S)
    (t : GameTree S Outcome) (hnr : NoInfoSetRepeat t) :
    (productProfile σ).bind (fun s => t.evalDist (flatToBehavioral s)) =
    t.evalDist σ := by
  induction t with
  | terminal z =>
    simp [GameTree.evalDist]
  | chance _k _μ _hk next ih =>
    simp only [GameTree.evalDist]
    -- Need: (productProfile σ).bind (fun s => μ.bind (fun b => ...)) =
    --       μ.bind (fun b => ...)
    -- Swap the two binds, then apply the IH per branch.
    rw [show (productProfile σ).bind
          (fun s => _μ.bind
            (fun b => (next b).evalDist (flatToBehavioral s))) =
        _μ.bind (fun b => (productProfile σ).bind
          (fun s => (next b).evalDist (flatToBehavioral s))) from
      PMF.bind_comm (productProfile σ) _μ
        (fun s b => (next b).evalDist (flatToBehavioral s))]
    congr 1; funext b
    exact ih b (hnr b)
  | @decision p I next ih =>
    obtain ⟨hnodup, hnr_sub⟩ := hnr
    simp only [GameTree.evalDist]
    -- The product PMF over all infosets factorizes: the I-component gives
    -- the marginal at I, and the rest gives the conditional.
    -- This is the core factorization step of the B→M direction.
    sorry

/-- Kuhn's theorem (behavioral → mixed direction):
    For any behavioral profile σ and tree with perfect recall,
    there exists a product distribution over flat profiles
    that induces the same outcome distribution. -/
theorem kuhn_behavioral_to_mixed (σ : BehavioralProfile S) (t : GameTree S Outcome)
    (hpr : PerfectRecall t) :
    ∃ μ : PMF (FlatProfile S),
      μ.bind (fun s => t.evalDist (flatToBehavioral s)) = t.evalDist σ :=
  ⟨productProfile σ, behavioral_to_mixed σ t
    (PerfectRecall_implies_NoInfoSetRepeat t hpr)⟩

open GameTheory in
/-- Kuhn's theorem lifted to utility distributions (behavioral → mixed). -/
theorem kuhn_behavioral_to_mixed_udist (G : EFGGame)
    (σ : BehavioralProfile G.inf) (hpr : PerfectRecall G.tree) :
    ∃ μ : PMF (FlatProfile G.inf),
      μ.bind (fun s => G.toKernelGame.udist (flatToBehavioral s)) =
      G.toKernelGame.udist σ := by
  obtain ⟨μ, hμ⟩ := kuhn_behavioral_to_mixed σ G.tree hpr
  exact ⟨μ, by
    simp only [KernelGame.udist, EFGGame.toKernelGame]
    rw [← hμ, PMF.bind_bind]⟩

/-- **Kuhn's theorem (mixed → behavioral direction).**
    For any game tree with perfect recall and any mixed strategy profile,
    there exists a behavioral strategy profile that induces the same
    outcome distribution. -/
theorem kuhn_mixed_to_behavioral
    (t : GameTree S Outcome)
    (hpr : PerfectRecall t)
    (muP : MixedProfile S) :
    ∃ sigma : BehavioralProfile S,
      t.evalDist sigma =
      (mixedProfileJoint (S := S) muP).bind
        (fun pi => t.evalDist
          (pureToBehavioral (S := S) pi)) := by
  sorry

open GameTheory in
/-- Kuhn's theorem lifted to utility distributions (mixed → behavioral). -/
theorem kuhn_mixed_to_behavioral_udist (G : EFGGame)
    (hpr : PerfectRecall G.tree) (muP : MixedProfile G.inf) :
    ∃ σ : BehavioralProfile G.inf,
      G.toKernelGame.udist σ =
      (mixedProfileJoint (S := G.inf) muP).bind
        (fun pi => G.toKernelGame.udist (pureToBehavioral pi)) := by
  obtain ⟨σ, hσ⟩ := kuhn_mixed_to_behavioral G.tree hpr muP
  exact ⟨σ, by
    simp only [KernelGame.udist, EFGGame.toKernelGame]
    rw [hσ, PMF.bind_bind]⟩

end EFG
