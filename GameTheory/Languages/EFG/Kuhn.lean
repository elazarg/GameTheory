import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Constructions

import GameTheory.Languages.EFG.Syntax
import Math.PMFProduct
import Math.ProbabilityMassFunction

/-!
# Kuhn's Theorem — Behavioral ↔ Mixed Strategy Equivalence

Kuhn's theorem states that behavioral and mixed strategies are outcome-equivalent
in extensive-form games with perfect recall.

- **Behavioral→Mixed**: The product PMF over independently sampled actions
  induces the same outcome. Requires `NoInfoSetRepeat` (no info set appears
  both at a decision node and in its subtrees), which follows from perfect recall.
- **Mixed→Behavioral**: Requires perfect recall. The conditional behavioral
  strategy induces the same outcome.

## Key definitions

- `FlatIdx` — sigma type `(p : Fin S.n) × S.Infoset p` indexing all infosets
- `FlatProfile` — dependent function assigning an action to each infoset
- `productProfile` — product PMF from a behavioral profile
- `NoInfoSetRepeat` — no info set repeats on a root-to-leaf path
- `mixedToBehavioral` — conditional behavioral strategy from a mixed strategy
-/

namespace EFG

open scoped BigOperators
open Math.PMFProduct

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
-- Product PMF
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

/-- `evalDist` under a flat profile viewed as behavioral. -/
noncomputable def GameTree.evalFlat (t : GameTree S Outcome) (s : FlatProfile S) :
    PMF Outcome :=
  t.evalDist (flatToBehavioral s)

-- ============================================================================
-- NoInfoSetRepeat (typed version)
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

/-- Perfect recall implies no info set repeats on paths.
    Proof: if info set `I` appears at the root and in subtree `next a`, then
    the player history at the root is `[]` while at the inner occurrence it
    starts with `(I, a)` — contradicting perfect recall. -/
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
    · -- I appears in subtree next a — contradiction with perfect recall
      obtain ⟨hist, next₂, hr₂⟩ := DecisionNodeIn_to_ReachBy hmem
      have key := hpr [] (.action _ I a :: hist) I next next₂
        (.here _) (.action a hr₂)
      simp [playerHistory] at key
    · -- NoInfoSetRepeat propagates to subtrees
      apply ih a
      intro h₁ h₂ q J next₁ next₂ hr₁ hr₂
      have key := hpr (.action _ I a :: h₁) (.action _ I a :: h₂) J next₁ next₂
        (.action a hr₁) (.action a hr₂)
      simp only [playerHistory] at key
      split at key <;> simp_all

-- ============================================================================
-- Agreement lemma
-- ============================================================================

/-- Two behavioral profiles agreeing on all infosets in `t` give the same `evalDist`. -/
theorem evalDist_eq_of_behavioral_agree_core (t : GameTree S Outcome)
    (σ₁ σ₂ : BehavioralProfile S)
    (h : ∀ {q} {J : S.Infoset q}, DecisionNodeIn J t → σ₁ q J = σ₂ q J) :
    t.evalDist σ₁ = t.evalDist σ₂ := by
  induction t with
  | terminal _ => rfl
  | chance _k _μ _hk next ih =>
    simp only [GameTree.evalDist]; congr 1; funext b
    exact ih b (fun hdn => h (.in_chance _ _ _ _ b hdn))
  | decision I next ih =>
    simp only [GameTree.evalDist]
    rw [h (.root next)]
    congr 1; funext a
    exact ih a (fun hdn => h (.in_decision I next a hdn))

/-- Two flat profiles that agree on all infosets appearing in `t` produce
    the same evalDist when used as behavioral profiles. -/
theorem evalDist_pure_eq_of_agree (t : GameTree S Outcome)
    (s₁ s₂ : FlatProfile S)
    (h : ∀ {q} {J : S.Infoset q}, DecisionNodeIn J t → s₁ ⟨q, J⟩ = s₂ ⟨q, J⟩) :
    t.evalFlat s₁ = t.evalFlat s₂ := by
  simpa [GameTree.evalFlat, flatToBehavioral] using
    (evalDist_eq_of_behavioral_agree_core t (flatToBehavioral s₁) (flatToBehavioral s₂)
      (fun {q} {J} hdn => by
        simp [flatToBehavioral, h hdn]))

-- ============================================================================
-- Behavioral → Mixed
-- ============================================================================

/-- **Behavioral→Mixed**: the product PMF over all infosets, when composed with
    deterministic evaluation, equals behavioral evaluation.
    Requires `NoInfoSetRepeat` (implied by `PerfectRecall`). -/
theorem behavioral_to_mixed (σ : BehavioralProfile S) (t : GameTree S Outcome)
    (hnr : NoInfoSetRepeat t) :
    (productProfile σ).bind (fun s => t.evalDist (flatToBehavioral s)) =
    t.evalDist σ := by
  induction t with
  | terminal z =>
    simp only [GameTree.evalDist]
    exact (productProfile σ).bind_const (PMF.pure z)
  | chance _k μ _hk next ih =>
    simp only [evalDist_chance]
    rw [PMF.bind_comm (productProfile σ) μ]
    congr 1; funext b
    exact ih b (hnr b)
  | decision I next ih =>
    rename_i p
    -- Unfold evalDist on both sides
    simp only [evalDist_decision]
    -- Simplify PMF.pure_bind inside the LHS bind
    conv_lhs =>
      arg 2; ext s
      simp only [flatToBehavioral, PMF.pure_bind]
    -- Now LHS = (productProfile σ).bind (fun s => evalDist (flatToBehavioral s) (next (s ⟨p,I⟩)))
    -- This matches pmfPi_bind_factor with g a s = evalDist (flatToBehavioral s) (next a)
    -- Independence: g doesn't depend on the ⟨p,I⟩ coordinate of s
    have hindep : ∀ (a : S.Act I) (s₁ s₂ : FlatProfile S),
        (∀ idx : FlatIdx S, idx ≠ ⟨p, I⟩ → s₁ idx = s₂ idx) →
        (next a).evalDist (flatToBehavioral s₁) =
        (next a).evalDist (flatToBehavioral s₂) := by
      intro a s₁ s₂ hagree
      apply evalDist_pure_eq_of_agree
      intro q J hdn
      apply hagree
      intro heq
      have hp : q = p := congrArg Sigma.fst heq
      subst hp
      have hI : J = I := eq_of_heq (Sigma.mk.inj heq).2
      subst hI; exact hnr.1 a hdn
    -- Factor the product at coordinate ⟨p, I⟩
    change (pmfPi (fun (idx : FlatIdx S) => σ idx.1 idx.2)).bind
        (fun s => (fun (a : S.Act I) (s : FlatProfile S) =>
          (next a).evalDist (flatToBehavioral s)) (s ⟨p, I⟩) s) =
      (σ p I).bind (fun a => (next a).evalDist σ)
    rw [pmfPi_bind_factor (fun (idx : FlatIdx S) => σ idx.1 idx.2) ⟨p, I⟩
      (fun (a : S.Act I) (s : FlatProfile S) =>
        (next a).evalDist (flatToBehavioral s))
      (Ignores₂_of_pointwise (⟨p, I⟩ : FlatIdx S) _ hindep)]
    congr 1; funext a
    exact ih a (hnr.2 a)

-- ============================================================================
-- Reachability (for mixed → behavioral)
-- ============================================================================

/-- Whether a flat profile `s` reaches a decision node with info set `I`
    (of player `p`) in tree `t`. At decision nodes, the profile's action
    determines which subtree is followed. At chance nodes, reachable if
    any branch reaches it. -/
def reachesFlat {p : S.Player} (I : S.Infoset p)
    (s : FlatProfile S) : GameTree S Outcome → Prop
  | .terminal _ => False
  | .chance _k _μ _hk next => ∃ b, reachesFlat I s (next b)
  | .decision (p := q) I' next =>
      (∃ (heq : q = p), heq ▸ I' = I) ∨
      reachesFlat I s (next (s ⟨q, I'⟩))

open Classical in
/-- Probability that a distribution over flat profiles reaches info set `I`. -/
noncomputable def reachProbFlat {p : S.Player}
    (μ : PMF (FlatProfile S)) (t : GameTree S Outcome) (I : S.Infoset p) : ENNReal :=
  ∑ s : FlatProfile S,
    if reachesFlat I s t then μ s else 0

-- ============================================================================
-- Mixed → Behavioral (single-player)
-- ============================================================================

open Classical in
/-- Construct a behavioral strategy from a distribution over flat profiles
    by conditioning. At info set `I` of player `p`:
    σ(a) = Pr[s(p,I) = a ∧ reach(I)] / Pr[reach(I)].
    When reach probability is 0, default to the first action. -/
noncomputable def mixedToBehavioralFlat {p : S.Player}
    (μ : PMF (FlatProfile S)) (t : GameTree S Outcome) :
    BehavioralStrategy S p :=
  fun I =>
    let pReach := reachProbFlat μ t I
    if hpR : pReach = 0 then PMF.pure ⟨0, S.arity_pos p I⟩
    else
      PMF.ofFintype (fun a =>
        (∑ s : FlatProfile S,
          if reachesFlat I s t ∧ s ⟨p, I⟩ = a then μ s else 0) / pReach)
        (by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
          conv_lhs => arg 1; rw [Finset.sum_comm]
          have hcollapse : ∀ s : FlatProfile S,
              (∑ a : S.Act I,
                if reachesFlat I s t ∧ s ⟨p, I⟩ = a then (μ s : ENNReal) else 0) =
              if reachesFlat I s t then μ s else 0 := by
            intro s
            by_cases hr : reachesFlat I s t
            · simp only [hr, true_and, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
            · simp [hr]
          simp_rw [hcollapse]
          have hpReach_le : pReach ≤ 1 := by
            calc pReach
                = ∑ s, if reachesFlat I s t then (μ s : ENNReal) else 0 := rfl
              _ ≤ ∑ s, μ s := Finset.sum_le_sum fun s _ => by split_ifs <;> simp
              _ = 1 := by
                  simpa [tsum_fintype] using (PMF.tsum_coe μ)
          exact ENNReal.mul_inv_cancel hpR
            (ne_of_lt (lt_of_le_of_lt hpReach_le (by simp))))

-- ============================================================================
-- Helper lemmas for mixed → behavioral
-- ============================================================================

/-- `reachesFlat` implies `DecisionNodeIn`. -/
theorem DecisionNodeIn_of_reachesFlat {p : S.Player} {I : S.Infoset p}
    {s : FlatProfile S} {t : GameTree S Outcome}
    (h : reachesFlat I s t) : DecisionNodeIn I t := by
  induction t with
  | terminal _ => exact absurd h (by simp [reachesFlat])
  | chance _k _μ _hk next ih =>
    simp only [reachesFlat] at h
    obtain ⟨b, hb⟩ := h
    exact .in_chance _ _ _ _ b (ih b hb)
  | decision I' next ih =>
    simp only [reachesFlat] at h
    rcases h with ⟨heq, hI⟩ | hsub
    · subst heq; subst hI; exact .root next
    · exact .in_decision I' next _ (ih _ hsub)

/-- Under perfect recall, if info set `I` (of player `p`) appears in two subtrees
    `next a₁` and `next a₂` of a decision node `I'` (of same player), then `a₁ = a₂`. -/
theorem infoSet_unique_subtree_typed {p : S.Player} {I : S.Infoset p}
    {I' : S.Infoset p} {next : S.Act I' → GameTree S Outcome}
    (hpr : PerfectRecall (.decision I' next))
    {a₁ a₂ : S.Act I'} (h₁ : DecisionNodeIn I (next a₁))
    (h₂ : DecisionNodeIn I (next a₂)) : a₁ = a₂ := by
  obtain ⟨hist₁, next₁, hr₁⟩ := DecisionNodeIn_to_ReachBy h₁
  obtain ⟨hist₂, next₂, hr₂⟩ := DecisionNodeIn_to_ReachBy h₂
  have pr₁ := ReachBy.action a₁ hr₁
  have pr₂ := ReachBy.action a₂ hr₂
  have key := hpr _ _ I next₁ next₂ pr₁ pr₂
  simp only [playerHistory, dite_true, List.cons.injEq] at key
  exact eq_of_heq (Sigma.mk.inj key.1).2

/-- If `s` reaches info set `I` through `decision I' next` (with `I' ≠ I`),
    then `s ⟨p, I'⟩` is the unique action leading to the subtree containing `I`. -/
theorem reachesFlat_decision_forces_action {p : S.Player} {I : S.Infoset p}
    {I' : S.Infoset p} {next : S.Act I' → GameTree S Outcome}
    {s : FlatProfile S}
    (hpr : PerfectRecall (.decision I' next))
    (hII' : I' ≠ I)
    (hreach : reachesFlat I s (.decision I' next))
    : ∀ a, DecisionNodeIn I (next a) → s ⟨p, I'⟩ = a := by
  simp only [reachesFlat] at hreach
  rcases hreach with ⟨heq, hI⟩ | h
  · -- I' = I case — contradicts hII'
    exact absurd hI (by cases heq; exact hII')
  · -- s reaches I in next (s ⟨p, I'⟩)
    intro a ha
    exact infoSet_unique_subtree_typed hpr
      (DecisionNodeIn_of_reachesFlat h) ha

/-- Every flat profile reaches the root infoset. -/
theorem reachesFlat_root {p : S.Player} {I' : S.Infoset p}
    {next : S.Act I' → GameTree S Outcome} {s : FlatProfile S} :
    reachesFlat I' s (.decision I' next) :=
  Or.inl ⟨rfl, rfl⟩

open Classical in
/-- Reach probability at the root infoset is 1. -/
theorem reachProbFlat_root {p : S.Player} {I' : S.Infoset p}
    {next : S.Act I' → GameTree S Outcome} {μ : PMF (FlatProfile S)} :
    reachProbFlat μ (.decision I' next) I' = 1 := by
  simp only [reachProbFlat]
  have : ∀ s : FlatProfile S,
      (if reachesFlat I' s (GameTree.decision I' next) then (μ s : ENNReal) else 0) = μ s := by
    intro s; rw [if_pos reachesFlat_root]
  simp_rw [this]
  simpa [tsum_fintype] using (PMF.tsum_coe μ)

open Classical in
/-- At the root, the conditional numerator collapses. -/
theorem root_num_collapse {p : S.Player} {I' : S.Infoset p}
    {next : S.Act I' → GameTree S Outcome}
    (μ : PMF (FlatProfile S)) (a : S.Act I') :
    (∑ s : FlatProfile S,
      if reachesFlat I' s (.decision I' next) ∧ s ⟨p, I'⟩ = a
      then (μ s : ENNReal) else 0) =
    ∑ s : FlatProfile S, if s ⟨p, I'⟩ = a then μ s else 0 := by
  congr 1; funext s
  simp only [reachesFlat_root, true_and]

/-- The marginal/pushforward of μ along the root action. -/
noncomputable def μMarginal {p : S.Player} (I' : S.Infoset p)
    (μ : PMF (FlatProfile S)) : PMF (S.Act I') :=
  Math.ProbabilityMassFunction.pushforward μ (fun s => s ⟨p, I'⟩)

open Classical in
/-- The conditional distribution of flat profiles given that player `p`
    takes action `a` at infoset `I₀`. -/
noncomputable def μCond {p : S.Player} (I₀ : S.Infoset p) (a : S.Act I₀)
    (μ : PMF (FlatProfile S)) : PMF (FlatProfile S) :=
  let p_a := μMarginal I₀ μ a
  if hp : p_a = 0 then μ -- Fallback for 0-probability actions
  else
    PMF.ofFintype
      (fun s => if s ⟨p, I₀⟩ = a then μ s / p_a else 0)
      (by
        simp only []
        rw [show (∑ s, if s ⟨p, I₀⟩ = a then μ s / p_a else (0 : ENNReal)) =
            (∑ s, (if s ⟨p, I₀⟩ = a then (μ s : ENNReal) else 0) * p_a⁻¹) from
          Finset.sum_congr rfl (fun s _ => by split_ifs <;> simp [div_eq_mul_inv]),
          ← Finset.sum_mul]
        have h_sum : (∑ s : FlatProfile S,
            if s ⟨p, I₀⟩ = a then (μ s : ENNReal) else 0) = p_a := by
          -- Expose the underlying definition of p_a
          change _ = μMarginal I₀ μ a
          simp [μMarginal, Math.ProbabilityMassFunction.pushforward, tsum_fintype, eq_comm]
        rw [h_sum]
        exact ENNReal.mul_inv_cancel hp
          (PMF.apply_ne_top (μMarginal I₀ μ) a))

/-- Evaluating μCond at a specific profile gives μ s / p_a if the action matches, else 0. -/
theorem μCond_apply {p : S.Player} (I₀ : S.Infoset p) (a : S.Act I₀)
    (μ : PMF (FlatProfile S)) (s : FlatProfile S) (hp : μMarginal I₀ μ a ≠ 0) :
    μCond I₀ a μ s = if s ⟨p, I₀⟩ = a then μ s / μMarginal I₀ μ a else 0 := by
  simp only [μCond, dif_neg hp, PMF.ofFintype_apply]

/-- Law of total probability: binding a function over the full distribution is
    equivalent to binding over the marginal and then the conditional. -/
theorem bind_marginal_cond {p : S.Player} (I₀ : S.Infoset p)
    (μ : PMF (FlatProfile S)) (f : FlatProfile S → PMF Outcome) :
    μ.bind f = (μMarginal I₀ μ).bind (fun a => (μCond I₀ a μ).bind f) := by
  simpa [μMarginal, μCond, Math.ProbabilityMassFunction.pushforward,
      Math.ProbabilityMassFunction.condOn] using
    (Math.ProbabilityMassFunction.bind_pushforward_condOn
      (μ := μ) (proj := fun s : FlatProfile S => s ⟨p, I₀⟩) (g := f))

/-- Mass times conditional recovers original mass on the conditioned fiber. -/
theorem μMarginal_mul_μCond_apply {p : S.Player}
    (I₀ : S.Infoset p) (a : S.Act I₀)
    (μ : PMF (FlatProfile S))
    (hpa : μMarginal I₀ μ a ≠ 0)
    (s : FlatProfile S) :
    μMarginal I₀ μ a * μCond I₀ a μ s =
      if s ⟨p, I₀⟩ = a then μ s else 0 := by
  have hpa_top : μMarginal I₀ μ a ≠ ⊤ :=
    PMF.apply_ne_top (μMarginal I₀ μ) a
  rw [μCond_apply I₀ a μ s hpa]
  split_ifs with hs
  · rw [mul_comm, ENNReal.div_mul_cancel hpa hpa_top]
  · simp


/-- Under perfect recall, for infosets in `next a` (with `I₀ ≠ J`),
    `reachesFlat J s (decision I₀ next)` iff `s ⟨p, I₀⟩ = a ∧ reachesFlat J s (next a)`. -/
theorem reachesFlat_decision_iff {p : S.Player} {J I₀ : S.Infoset p}
    {s : FlatProfile S} {next : S.Act I₀ → GameTree S Outcome} {a : S.Act I₀}
    (hpr : PerfectRecall (.decision I₀ next))
    (hJ : DecisionNodeIn J (next a)) (hne : I₀ ≠ J) :
    reachesFlat J s (.decision (p := p) I₀ next) ↔
    s ⟨p, I₀⟩ = a ∧ reachesFlat J s (next a) := by
  constructor
  · intro h
    simp only [reachesFlat] at h
    rcases h with ⟨_, hIJ⟩ | hsub
    · exact absurd hIJ hne
    · have hsa := reachesFlat_decision_forces_action hpr hne
          (by simp only [reachesFlat]; exact Or.inr hsub) a hJ
      constructor
      · exact hsa
      · rw [← hsa]; exact hsub
  · intro ⟨hsa, hr⟩
    simp only [reachesFlat]
    right; rw [hsa]; exact hr

theorem evalDist_decision_cond_restrict {p : S.Player} {I₀ : S.Infoset p}
    {next : S.Act I₀ → GameTree S Outcome} {a : S.Act I₀}
    (μ : PMF (FlatProfile S)) (hp : μMarginal I₀ μ a ≠ 0) :
    (μCond I₀ a μ).bind (fun s => (GameTree.decision I₀ next).evalDist (flatToBehavioral s)) =
    (μCond I₀ a μ).bind (fun s => (next a).evalDist (flatToBehavioral s)) := by
  ext x
  simp only [PMF.bind_apply, tsum_fintype]
  congr 1; funext s
  by_cases hsa : s ⟨p, I₀⟩ = a
  · -- If the profile takes action `a`, the evaluations are definitionally equal
    have h_eval : (GameTree.decision I₀ next).evalDist (flatToBehavioral s) x =
        (next a).evalDist (flatToBehavioral s) x := by
      simp only [GameTree.evalDist, flatToBehavioral, PMF.pure_bind, hsa]
    rw [h_eval]
  · -- If the profile does not take action `a`, the conditional probability is 0
    rw [μCond_apply I₀ a μ s hp, if_neg hsa, zero_mul, zero_mul]

/-- Scaling lemma for the *reach probability* under a decision root:
    reachProb(parent) = p_a * reachProb(subtree under μCond). -/
lemma reachProbFlat_decision_scale {p}
    {I₀ : S.Infoset p} {next : S.Act I₀ → GameTree S Outcome} {a : S.Act I₀}
    (hpr : PerfectRecall (.decision I₀ next))
    (μ : PMF (FlatProfile S)) (hpa : μMarginal I₀ μ a ≠ 0)
    {J : S.Infoset p} (hJ : DecisionNodeIn J (next a)) :
    reachProbFlat μ (.decision (p := p) I₀ next) J
      = (μMarginal I₀ μ a) * reachProbFlat (μCond I₀ a μ) (next a) J := by
  classical
  -- First, show I₀ ≠ J (since J is in a subtree).
  have hne : I₀ ≠ J := by
    intro h; subst h
    exact (PerfectRecall_implies_NoInfoSetRepeat _ hpr).1 a hJ
  -- Use your reachesFlat_decision_iff
  have hiff : ∀ s : FlatProfile S,
      reachesFlat J s (.decision (p := p) I₀ next)
        ↔ (s ⟨p, I₀⟩ = a ∧ reachesFlat J s (next a)) :=
    fun s => reachesFlat_decision_iff hpr hJ hne
  -- Abbrev p_a and its non-top proof (standard for PMFs).
  let p_a : ENNReal := μMarginal I₀ μ a
  have hpa_top : p_a ≠ ⊤ := by
    -- PMF point masses are always finite.
    exact PMF.apply_ne_top (μMarginal I₀ μ) a
  -- Expand both reachProbFlat, rewrite indicators via hiff, and use μCond_apply.
  simp only [reachProbFlat]
  -- LHS: sum over s of (if s(I₀)=a ∧ reach_sub then μ s else 0)
  -- RHS: p_a * sum over s of (if reach_sub then μCond s else 0)
  -- but μCond s is μ s / p_a if s(I₀)=a else 0.
  -- so p_a * RHS collapses to the LHS.
  have : (∑ s : FlatProfile S,
      if reachesFlat J s (next a) then (μCond I₀ a μ) s else 0)
    =
    (∑ s : FlatProfile S,
      if s ⟨p, I₀⟩ = a ∧ reachesFlat J s (next a) then (μ s / p_a) else 0) := by
    apply Finset.sum_congr rfl
    intro s _
    by_cases hr : reachesFlat J s (next a)
    · simp [hr, μCond_apply (I₀ := I₀) (a := a) (μ := μ) (s := s) hpa]
      by_cases hsa : s ⟨p, I₀⟩ = a
      · subst hsa
        simp_all only [ne_eq, Finset.mem_univ, reduceIte, p_a]
      · simp [hsa]
    · simp [hr]
  have hterm :
      (p_a * (∑ s : FlatProfile S,
        if reachesFlat J s (next a) then (μCond I₀ a μ s : ENNReal) else 0))
        =
      (∑ s : FlatProfile S,
        if s ⟨p, I₀⟩ = a ∧ reachesFlat J s (next a) then (μ s : ENNReal) else 0) := by
    simp_rw [p_a]
    simp_rw [Finset.mul_sum, mul_ite, mul_zero,
      μMarginal_mul_μCond_apply (I₀ := I₀) (a := a) (μ := μ) hpa]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hr : reachesFlat J s (next a)
    · by_cases hs : s ⟨p, I₀⟩ = a
      · simp [hr, hs]
      · simp [hr, hs]
    · simp [hr]
  -- Finally, rewrite LHS using hiff, RHS using the μCond expansion, and use hterm.
  -- LHS:
  have hL :
      (∑ s : FlatProfile S,
        if reachesFlat J s (.decision (p := p) I₀ next) then (μ s : ENNReal) else 0)
      =
      (∑ s : FlatProfile S,
        if s ⟨p, I₀⟩ = a ∧ reachesFlat J s (next a) then (μ s : ENNReal) else 0) := by
    apply Finset.sum_congr rfl
    intro s _
    have := hiff s
    by_cases hreach : reachesFlat J s (.decision (p := p) I₀ next)
    · have : s ⟨p, I₀⟩ = a ∧ reachesFlat J s (next a) := (this.mp hreach)
      simp [hreach, this]
    · have : ¬ (s ⟨p, I₀⟩ = a ∧ reachesFlat J s (next a)) := by
        intro h; exact hreach ((this.mpr h))
      simp [hreach, this]
  -- we stitch:
  simpa [hL, p_a] using hterm.symm


open Classical in
-- Scaling lemma for each action-numerator.
lemma num_decision_scale
    {I₀ : S.Infoset p} {next : S.Act I₀ → GameTree S Outcome} {a : S.Act I₀}
    (hpr : PerfectRecall (.decision I₀ next))
    (μ : PMF (FlatProfile S)) (hpa : μMarginal I₀ μ a ≠ 0)
    {J : S.Infoset p} (hJ : DecisionNodeIn J (next a))
    (b : S.Act J) :
    (∑ s : FlatProfile S,
      if reachesFlat J s (GameTree.decision (p := p) I₀ next) ∧ s ⟨p, J⟩ = b
      then (μ s : ENNReal) else 0)
      =
    (μMarginal I₀ μ a) *
      (∑ s : FlatProfile S,
        if reachesFlat J s (next a) ∧ s ⟨p, J⟩ = b
        then (μCond I₀ a μ s : ENNReal) else 0) := by
  -- Same idea as reachProb scaling, but keep the s⟨p,J⟩=b conjunct.
  have hne : (I₀ ≠ J) := by
    intro h; subst h
    exact (PerfectRecall_implies_NoInfoSetRepeat _ hpr).1 a hJ
  have hiff : ∀ s : FlatProfile S,
      reachesFlat J s (.decision (p := p) I₀ next)
        ↔ (s ⟨p, I₀⟩ = a ∧ reachesFlat J s (next a)) :=
    fun s => reachesFlat_decision_iff hpr hJ hne
  let p_a : ENNReal := μMarginal I₀ μ a
  have hpa_top : p_a ≠ ⊤ := by
    exact PMF.apply_ne_top (μMarginal I₀ μ) a
  -- Expand RHS, rewrite μCond_apply, and cancel p_a as in reachProb lemma.
  -- Do it by termwise analysis with split_ifs.
  -- First rewrite the LHS indicator via hiff.
  have hL :
      (∑ s : FlatProfile S,
        if reachesFlat J s (.decision (p := p) I₀ next) ∧ s ⟨p, J⟩ = b
        then (μ s : ENNReal) else 0)
      =
      (∑ s : FlatProfile S,
        if (s ⟨p, I₀⟩ = a ∧ reachesFlat J s (next a)) ∧ s ⟨p, J⟩ = b
        then (μ s : ENNReal) else 0) := by
    apply Finset.sum_congr rfl
    intro s _
    have := hiff s
    by_cases hreach : reachesFlat J s (.decision (p := p) I₀ next)
    · have hsub : s ⟨p, I₀⟩ = a ∧ reachesFlat J s (next a) := this.mp hreach
      simp [hreach, hsub]
    · have hsub : ¬ (s ⟨p, I₀⟩ = a ∧ reachesFlat J s (next a)) := by
        intro h; exact hreach (this.mpr h)
      simp [hreach, hsub]
  -- Now show RHS equals that sum by expanding μCond and cancelling p_a.
  rw [hL]
  simp_rw [Finset.mul_sum, mul_ite, mul_zero,
    μMarginal_mul_μCond_apply (I₀ := I₀) (a := a) (μ := μ) hpa]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hr : reachesFlat J s (next a)
  · by_cases hsb : s ⟨p, J⟩ = b
    · by_cases hsa : s ⟨p, I₀⟩ = a
      · simp [hr, hsb, hsa]
      · simp [hr, hsb, hsa]
    · simp [hr, hsb]
  · simp [hr]

/-- Your desired lemma, assuming μMarginal(I₀)=a is nonzero. -/
theorem mixedToBehavioralFlat_decision_sub
    {I₀ : S.Infoset p} {next : S.Act I₀ → GameTree S Outcome} {a : S.Act I₀}
    (hpr : PerfectRecall (.decision I₀ next))
    (μ : PMF (FlatProfile S)) (hpa : μMarginal I₀ μ a ≠ 0)
    {J : S.Infoset p} (hJ : DecisionNodeIn J (next a)) :
    mixedToBehavioralFlat (p := p) μ (.decision I₀ next) J =
    mixedToBehavioralFlat (p := p) (μCond I₀ a μ) (next a) J := by
  classical
  let p_a : ENNReal := μMarginal I₀ μ a
  have hpa_top : p_a ≠ ⊤ := by
    exact PMF.apply_ne_top (μMarginal I₀ μ) a
  have hReach :
      reachProbFlat μ (.decision (p := p) I₀ next) J
        = p_a * reachProbFlat (μCond I₀ a μ) (next a) J := by
    simpa [p_a] using reachProbFlat_decision_scale (p := p) hpr μ hpa hJ
  simp only [mixedToBehavioralFlat]
  set rL : ENNReal := reachProbFlat μ (.decision (p := p) I₀ next) J
  set rR : ENNReal := reachProbFlat (μCond I₀ a μ) (next a) J
  have hrL : rL = p_a * rR := by simpa [rL, rR, p_a] using hReach
  by_cases hrL0 : rL = 0
  · have hrR0 : rR = 0 := by
      have : p_a * rR = 0 := by simpa [hrL] using hrL0
      have : p_a = 0 ∨ rR = 0 := by simpa using (mul_eq_zero.mp this)
      cases this with
      | inl hp => exact (False.elim (hpa (by simpa [p_a] using hp)))
      | inr hr => exact hr
    simp [rL, rR, hrL0, hrR0]
  · have hrR0 : rR ≠ 0 := by
      intro hr
      apply hrL0
      simp [hrL, hr, mul_zero]
    simp only [hrL0, ↓reduceDIte, hrR0, rL, rR]
    ext b
    have hNum :
        (∑ s : FlatProfile S,
          if reachesFlat J s (.decision (p := p) I₀ next) ∧ s ⟨p, J⟩ = b
          then (μ s : ENNReal) else 0)
        =
        p_a *
          (∑ s : FlatProfile S,
            if reachesFlat J s (next a) ∧ s ⟨p, J⟩ = b
            then (μCond I₀ a μ s : ENNReal) else 0) := by
      simpa [p_a] using num_decision_scale (p := p) hpr μ hpa hJ b
    simp only [hrL, mul_comm, div_eq_mul_inv, PMF.ofFintype_apply, hNum, mul_left_comm, rR, rL]
    rw [ENNReal.mul_inv]
    · rw [mul_comm (reachProbFlat (μCond I₀ a μ) (next a) J)⁻¹ p_a⁻¹]
      simp_rw [← mul_assoc]
      have hpa_nz : p_a ≠ 0 := hpa
      rw [ENNReal.mul_inv_cancel hpa_nz hpa_top]
      rw [one_mul]
    · simp_all only [ne_eq, mul_eq_zero, not_false_eq_true, or_self, p_a, rL, rR]
    · simp_all only [ne_eq, mul_eq_zero, false_or, not_false_eq_true, or_true, p_a, rL, rR]


open Classical in
/-- At the root, `mixedToBehavioralFlat` equals the marginal. -/
theorem mixedToBehavioralFlat_root_eq {p : S.Player} {I' : S.Infoset p}
    {next : S.Act I' → GameTree S Outcome} {μ : PMF (FlatProfile S)} :
    mixedToBehavioralFlat (p := p) μ (.decision I' next) I' = μMarginal I' μ := by
  simp only [mixedToBehavioralFlat, reachProbFlat_root]
  rw [dif_neg (by norm_num : (1 : ENNReal) ≠ 0)]
  ext a
  have hroot :
      (∑ s : FlatProfile S,
        if reachesFlat I' s (.decision I' next) ∧ a = s ⟨p, I'⟩
        then (μ s : ENNReal) else 0) =
      ∑ s : FlatProfile S, if a = s ⟨p, I'⟩ then μ s else 0 := by
    simpa [eq_comm] using
      (root_num_collapse (p := p) (I' := I') (next := next) (μ := μ) (a := a))
  simp [PMF.ofFintype_apply, div_one, hroot,
    μMarginal, Math.ProbabilityMassFunction.pushforward, tsum_fintype, eq_comm]

/-- PerfectRecall propagates to subtrees under a chance node. -/
theorem PerfectRecall_chance_sub {k : Nat} {μ : PMF (Fin k)} {hk : 0 < k}
    {next : Fin k → GameTree S Outcome}
    (hpr : PerfectRecall (.chance k μ hk next)) (b : Fin k) :
    PerfectRecall (next b) := by
  intro h₁ h₂ p I next₁ next₂ hr₁ hr₂
  have := hpr (.chance _ b :: h₁) (.chance _ b :: h₂) I next₁ next₂
    (.chance b hr₁) (.chance b hr₂)
  simpa [playerHistory] using this

/-- PerfectRecall propagates to subtrees under a decision node. -/
theorem PerfectRecall_decision_sub {p : S.Player} {I : S.Infoset p}
    {next : S.Act I → GameTree S Outcome}
    (hpr : PerfectRecall (.decision I next)) (a : S.Act I) :
    PerfectRecall (next a) := by
  intro h₁ h₂ q J next₁ next₂ hr₁ hr₂
  have key := hpr (.action _ I a :: h₁) (.action _ I a :: h₂) J next₁ next₂
    (.action a hr₁) (.action a hr₂)
  simp only [playerHistory] at key
  split at key <;> simp_all

/-- All decision nodes in a subtree of a chance node inherit the `hsp` property. -/
theorem hsp_chance_sub {k : Nat} {μ : PMF (Fin k)} {hk : 0 < k}
    {next : Fin k → GameTree S Outcome} {p : S.Player} (b : Fin k)
    (hsp : ∀ {q : S.Player} {J : S.Infoset q},
      DecisionNodeIn J (.chance k μ hk next) → q = p) :
    ∀ {q : S.Player} {J : S.Infoset q}, DecisionNodeIn J (next b) → q = p :=
  fun hdn => hsp (.in_chance _ _ _ _ b hdn)

/-- All decision nodes in a subtree of a decision node inherit the `hsp` property. -/
theorem hsp_decision_sub {q : S.Player} {I' : S.Infoset q}
    {next : S.Act I' → GameTree S Outcome} {p : S.Player} (a : S.Act I')
    (hsp : ∀ {r : S.Player} {J : S.Infoset r},
      DecisionNodeIn J (.decision I' next) → r = p) :
    ∀ {r : S.Player} {J : S.Infoset r}, DecisionNodeIn J (next a) → r = p :=
  fun hdn => hsp (.in_decision I' next a hdn)

/-- If a ReachBy path to J exists and s's actions match the player history,
    then `reachesFlat J s t` holds. Proved by induction on `t`. -/
theorem reachesFlat_of_ReachBy_matching {s : FlatProfile S}
    (p : S.Player) (J : S.Infoset p) :
    ∀ (t : GameTree S Outcome),
    (∀ {q : S.Player} {K : S.Infoset q}, DecisionNodeIn K t → q = p) →
    ∀ {hist : List (HistoryStep S)} {next_J : S.Act J → GameTree S Outcome},
    ReachBy hist t (.decision J next_J) →
    (∀ step ∈ playerHistory S p hist, s ⟨p, step.1⟩ = step.2) →
    reachesFlat J s t
  | .terminal _, _, _, _, hr, _ => False.elim (ReachBy_terminal_absurd hr)
  | .chance _k _μ _hk next, hsp, _, _, hr, hmatch => by
    obtain ⟨b, rest, rfl, hr'⟩ := ReachBy_chance_inv' hr
    exact ⟨b, reachesFlat_of_ReachBy_matching p J (next b)
      (hsp_chance_sub b hsp) hr' (by simpa [playerHistory] using hmatch)⟩
  | .decision (p := q) I₀ next, hsp, _, _, hr, hmatch => by
    have hqp : q = p := hsp (.root _); cases hqp
    rcases ReachBy_decision_inv hr with ⟨rfl, _, hI, _⟩ | ⟨a, rest, rfl, hr'⟩
    · exact Or.inl ⟨rfl, eq_of_heq hI⟩
    · simp only [reachesFlat]
      by_cases hIJ : I₀ = J
      · exact Or.inl ⟨trivial, hIJ⟩
      · right
        have hsa : s ⟨p, I₀⟩ = a := by
          have : ⟨I₀, a⟩ ∈ playerHistory S p (HistoryStep.action p I₀ a :: rest) := by
            simp [playerHistory]
          exact hmatch ⟨I₀, a⟩ this
        conv in s ⟨p, I₀⟩ => rw [hsa]
        exact reachesFlat_of_ReachBy_matching p J (next a)
          (hsp_decision_sub a hsp) hr' (fun step hmem => by
            apply hmatch; simp only [playerHistory, ↓reduceDIte, List.mem_cons]; exact Or.inr hmem)

/-- If `reachesFlat J s t`, there exists a ReachBy path with matching player history. -/
theorem reachesFlat_gives_matching_path
    (p : S.Player) (J : S.Infoset p) (s : FlatProfile S) :
    ∀ (t : GameTree S Outcome),
    (∀ {q : S.Player} {K : S.Infoset q}, DecisionNodeIn K t → q = p) →
    reachesFlat J s t →
    ∃ (hist : List (HistoryStep S)) (next_J : S.Act J → GameTree S Outcome),
      ReachBy hist t (.decision J next_J) ∧
      ∀ step ∈ playerHistory S p hist, s ⟨p, step.1⟩ = step.2
  | .terminal _, _, hreach => absurd hreach (by simp [reachesFlat])
  | .chance _k _μ _hk next, hsp, hreach => by
    obtain ⟨b, hb⟩ := hreach
    obtain ⟨hist, nJ, hr, hm⟩ := reachesFlat_gives_matching_path p J s
      (next b) (hsp_chance_sub b hsp) hb
    exact ⟨.chance _ b :: hist, nJ, .chance b hr, by simpa [playerHistory] using hm⟩
  | .decision (p := q) I₀ next, hsp, hreach => by
    have hqp : q = p := hsp (.root _)
    simp only [reachesFlat] at hreach
    rcases hreach with ⟨heq, hIJ⟩ | hsub
    · -- Root case: I₀ = J
      cases hqp; cases heq; cases hIJ
      exact ⟨[], next, .here _, by simp [playerHistory]⟩
    · -- Subtree case
      obtain ⟨hist, nJ, hr, hm⟩ := reachesFlat_gives_matching_path p J s
        (next (s ⟨q, I₀⟩)) (hsp_decision_sub _ hsp) hsub
      cases hqp
      exact ⟨.action p I₀ (s ⟨p, I₀⟩) :: hist, nJ, .action _ hr, by
        simp only [playerHistory, dite_true]
        intro step hmem
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · rfl
        · exact hm step hmem'⟩

/-- Under perfect recall, reachability is the same across chance branches. -/
theorem reachesFlat_chance_iff {p : S.Player} {J : S.Infoset p}
    {s : FlatProfile S} {k : Nat} {μ_c : PMF (Fin k)} {hk : 0 < k}
    {next : Fin k → GameTree S Outcome} {b : Fin k}
    (hpr : PerfectRecall (.chance k μ_c hk next))
    (hsp : ∀ {q : S.Player} {K : S.Infoset q},
      DecisionNodeIn K (.chance k μ_c hk next) → q = p)
    (hJ : DecisionNodeIn J (next b)) :
    reachesFlat J s (.chance k μ_c hk next) ↔ reachesFlat J s (next b) := by
  constructor
  · intro ⟨b', hb'⟩
    obtain ⟨h₂, nJ₂, hr₂, hm₂⟩ :=
      reachesFlat_gives_matching_path p J s (next b') (hsp_chance_sub b' hsp) hb'
    obtain ⟨h₁, nJ₁, hr₁⟩ := DecisionNodeIn_to_ReachBy hJ
    have hph := hpr (.chance _ b :: h₁) (.chance _ b' :: h₂)
      J nJ₁ nJ₂ (.chance b hr₁) (.chance b' hr₂)
    simp only [playerHistory] at hph
    exact reachesFlat_of_ReachBy_matching p J (next b)
      (hsp_chance_sub b hsp) hr₁ (fun step hmem => hm₂ step (hph ▸ hmem))
  · exact fun h => ⟨b, h⟩

open Classical in
/-- Under perfect recall, `mixedToBehavioralFlat` is the same whether conditioned
    on a chance tree or on a specific branch (for infosets in that branch). -/
theorem mixedToBehavioralFlat_chance_eq {p : S.Player}
    {μ : PMF (FlatProfile S)} {k : Nat} {μ_c : PMF (Fin k)} {hk : 0 < k}
    {next : Fin k → GameTree S Outcome} {b : Fin k}
    (hpr : PerfectRecall (.chance k μ_c hk next))
    (hsp : ∀ {q : S.Player} {K : S.Infoset q},
      DecisionNodeIn K (.chance k μ_c hk next) → q = p)
    {J : S.Infoset p} (hJ : DecisionNodeIn J (next b)) :
    mixedToBehavioralFlat (p := p) μ (.chance k μ_c hk next) J =
    mixedToBehavioralFlat (p := p) μ (next b) J := by
  -- The key: reachesFlat J s (chance ...) ↔ reachesFlat J s (next b) for all s
  have hiff : ∀ s, reachesFlat J s (.chance k μ_c hk next) ↔ reachesFlat J s (next b) :=
    fun s => reachesFlat_chance_iff hpr hsp hJ
  -- Propositional equality from iff
  have hreq : ∀ s, reachesFlat J s (.chance k μ_c hk next) = reachesFlat J s (next b) :=
    fun s => propext (hiff s)
  -- Therefore reachProbFlat and the numerator are the same
  have hreach_eq : reachProbFlat μ (.chance k μ_c hk next) J =
      reachProbFlat μ (next b) J := by
    simp only [reachProbFlat]; congr 1; funext s; rw [hreq]
  have hnum_eq : ∀ a,
      (∑ s, if reachesFlat J s (.chance k μ_c hk next) ∧ s ⟨p, J⟩ = a then μ s else 0) =
      (∑ s, if reachesFlat J s (next b) ∧ s ⟨p, J⟩ = a then μ s else 0) := by
    intro a; congr 1; funext s; rw [hreq]
  simp only [mixedToBehavioralFlat, hreach_eq]
  split
  · rfl
  · ext a; simp only [PMF.ofFintype_apply, hnum_eq]

/-- **Mixed→Behavioral** for single-player trees: under perfect recall,
    the conditional behavioral strategy induces the same outcome distribution
    as the mixed strategy. This is the harder direction of Kuhn's theorem. -/
theorem mixed_to_behavioral_flat (t : GameTree S Outcome) (hpr : PerfectRecall t)
    (p : S.Player) (μ : PMF (FlatProfile S))
    (hsp : ∀ {q : S.Player} {J : S.Infoset q}, DecisionNodeIn J t → q = p) :
    t.evalDist (fun q => if h : q = p then h ▸ mixedToBehavioralFlat μ t
                         else fun I => PMF.pure ⟨0, S.arity_pos q I⟩) =
    μ.bind (fun s => t.evalDist (flatToBehavioral s)) := by
  induction t generalizing μ with
  | terminal z =>
    simp only [GameTree.evalDist]
    exact (μ.bind_const (PMF.pure z)).symm
  | chance k μ_c hk next ih =>
    simp only [evalDist_chance]
    conv_rhs => rw [PMF.bind_comm μ μ_c]
    congr 1; funext b
    have h_agree := evalDist_eq_of_behavioral_agree_core (next b)
      (fun q => if h : q = p then h ▸ mixedToBehavioralFlat μ (.chance k μ_c hk next)
                else fun I => PMF.pure ⟨0, S.arity_pos q I⟩)
      (fun q => if h : q = p then h ▸ mixedToBehavioralFlat μ (next b)
                else fun I => PMF.pure ⟨0, S.arity_pos q I⟩)
      (fun {q} {J} hdn => by
        have : q = p := hsp (.in_chance _ _ _ _ b hdn)
        cases this; simp only
        exact mixedToBehavioralFlat_chance_eq hpr hsp hdn)
    rw [h_agree]
    -- Notice we pass `μ` explicitly to `ih` using named arguments
    exact ih b (μ := μ) (hpr := PerfectRecall_chance_sub hpr b) (hsp := hsp_chance_sub b hsp)
  | decision I₀ next ih =>
    -- 1. Unify the node owner with the global `p`
    have hp_eq : _ = p := hsp (.root next)
    cases hp_eq
    -- 2. Apply the law of total probability to the RHS
    have h_rhs : μ.bind (fun s => (GameTree.decision I₀ next).evalDist (flatToBehavioral s)) =
        (μMarginal I₀ μ).bind (fun a => (μCond I₀ a μ).bind (fun s =>
          (GameTree.decision I₀ next).evalDist (flatToBehavioral s))) :=
      bind_marginal_cond I₀ μ _
    rw [h_rhs]
    -- 3. Expose the LHS as a bind over the root marginal *before* ext x
    have h_lhs_root : (fun q =>
        if h : q = p then h ▸ mixedToBehavioralFlat μ (GameTree.decision I₀ next)
        else fun I => PMF.pure ⟨0, S.arity_pos q I⟩) p I₀ = μMarginal I₀ μ := by
      simp only
      exact mixedToBehavioralFlat_root_eq
    have h_lhs : (GameTree.decision I₀ next).evalDist (fun q =>
            if h : q = p then h ▸ mixedToBehavioralFlat μ (GameTree.decision I₀ next)
            else fun I => PMF.pure ⟨0, S.arity_pos q I⟩) =
        (μMarginal I₀ μ).bind (fun a => (next a).evalDist (fun q =>
            if h : q = p then h ▸ mixedToBehavioralFlat μ (GameTree.decision I₀ next)
            else fun I => PMF.pure ⟨0, S.arity_pos q I⟩)) := by
      have h_unfold : (GameTree.decision I₀ next).evalDist (fun q =>
            if h : q = p then h ▸ mixedToBehavioralFlat μ (GameTree.decision I₀ next)
            else fun I => PMF.pure ⟨0, S.arity_pos q I⟩) =
        ((fun q =>
          if h : q = p then h ▸ mixedToBehavioralFlat μ (GameTree.decision I₀ next)
          else fun I => PMF.pure ⟨0, S.arity_pos q I⟩) p I₀).bind (fun a =>
            (next a).evalDist (fun q =>
              if h : q = p then h ▸ mixedToBehavioralFlat μ (GameTree.decision I₀ next)
              else fun I => PMF.pure ⟨0, S.arity_pos q I⟩)) := rfl
      rw [h_unfold, h_lhs_root]
    rw [h_lhs]
    -- 4. Drop down to pointwise evaluation for PMF equality
    ext x
    simp only [PMF.bind_apply, tsum_fintype]
    -- 5. Match the sums point-by-point
    apply Finset.sum_congr rfl
    intro a _
    by_cases hp_marg : μMarginal I₀ μ a = 0
    · -- 0-probability actions vanish on both sides
      simp [hp_marg]
    · -- Non-zero probability actions
      congr 1
      have h_restrict := evalDist_decision_cond_restrict (next := next) (a := a) μ hp_marg
      have h_restrict_x : ((μCond I₀ a μ).bind (fun s =>
              (GameTree.decision I₀ next).evalDist (flatToBehavioral s))) x =
          ((μCond I₀ a μ).bind (fun s => (next a).evalDist (flatToBehavioral s))) x := by
        rw [h_restrict]
      simp only [PMF.bind_apply, tsum_fintype] at h_restrict_x
      rw [h_restrict_x]
      have h_ih := ih a (PerfectRecall_decision_sub hpr a) (μCond I₀ a μ) (hsp_decision_sub a hsp)
      have h_ih_x : (GameTree.evalDist (fun q =>
          if h : q = p then h ▸ mixedToBehavioralFlat (μCond I₀ a μ) (next a)
          else fun I => PMF.pure ⟨0, S.arity_pos q I⟩) (next a)) x
           =
          ((μCond I₀ a μ).bind (fun s => (next a).evalDist (flatToBehavioral s))) x := by
        rw [h_ih]
      simp only [PMF.bind_apply, tsum_fintype] at h_ih_x
      rw [← h_ih_x]
      congr 1
      apply evalDist_eq_of_behavioral_agree_core
      intro q J hdn
      have hqp : q = p := hsp_decision_sub a hsp hdn
      cases hqp
      simp only
      exact mixedToBehavioralFlat_decision_sub hpr μ hp_marg hdn

-- ============================================================================
-- Combined Kuhn's theorem
-- ============================================================================

/-- Kuhn's theorem (behavioral → mixed direction):
    For any behavioral profile σ and tree with perfect recall,
    there exists a product distribution over flat profiles
    that induces the same outcome distribution. -/
theorem kuhn_behavioral_to_mixed (σ : BehavioralProfile S) (t : GameTree S Outcome)
    (hpr : PerfectRecall t) :
    ∃ μ : PMF (FlatProfile S),
      μ.bind (fun s => t.evalDist (flatToBehavioral s)) = t.evalDist σ :=
  ⟨productProfile σ, behavioral_to_mixed σ t (PerfectRecall_implies_NoInfoSetRepeat t hpr)⟩

open GameTheory in
/-- Kuhn's theorem lifted to utility distributions (behavioral → mixed):
    For any EFG game with perfect recall, every behavioral profile has an
    equivalent mixed profile that induces the same joint utility distribution. -/
theorem kuhn_behavioral_to_mixed_udist (G : EFGGame)
    (σ : BehavioralProfile G.inf) (hpr : PerfectRecall G.tree) :
    ∃ μ : PMF (FlatProfile G.inf),
      μ.bind (fun s => G.toKernelGame.udist (flatToBehavioral s)) =
      G.toKernelGame.udist σ := by
  obtain ⟨μ, hμ⟩ := kuhn_behavioral_to_mixed σ G.tree hpr
  exact ⟨μ, by
    simp only [KernelGame.udist, EFGGame.toKernelGame]
    rw [← hμ, PMF.bind_bind]⟩

/-! Additional mixed-to-behavioral section (merged from former KuhnFull). -/


instance (p : S.Player) : DecidableEq (PureStrategy S p) :=
  show DecidableEq ((I : S.Infoset p) → S.Act I) from inferInstance
instance : DecidableEq (PureProfile S) :=
  show DecidableEq ((p : S.Player) → PureStrategy S p) from
    Fintype.decidablePiFintype

noncomputable abbrev mixedProfileJoint (muP : MixedProfile S) : PMF (PureProfile S) :=
  pmfPi (A := fun p => PureStrategy S p) muP

def flatProfileEquivPureProfile : Equiv (FlatProfile S) (PureProfile S) where
  toFun := fun s p I => s ⟨p, I⟩
  invFun := fun pi idx => pi idx.1 idx.2
  left_inv := by intro s; funext idx; cases idx; rfl
  right_inv := by intro pi; funext p I; rfl

noncomputable def pmfPureToFlat (mu : PMF (PureProfile S)) : PMF (FlatProfile S) :=
  mu.bind (fun pi => PMF.pure (flatProfileEquivPureProfile.symm pi))

noncomputable def muMarginal {p : S.Player} (I : S.Infoset p)
    (mu : PMF (FlatProfile S)) : PMF (S.Act I) :=
  mu.bind (fun s => PMF.pure (s ⟨p, I⟩))

noncomputable def muCond {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (mu : PMF (FlatProfile S)) (hpa : muMarginal (S := S) I mu a ≠ 0) : PMF (FlatProfile S) :=
  PMF.ofFintype
    (fun s => if s ⟨p, I⟩ = a then mu s / (muMarginal (S := S) I mu a) else 0)
    (by
      rw [show (∑ s, if s ⟨p, I⟩ = a then mu s / muMarginal (S := S) I mu a
            else (0 : ENNReal)) =
          (∑ s, (if s ⟨p, I⟩ = a
          then (mu s : ENNReal) else 0) * (muMarginal (S := S) I mu a)⁻¹) from
        Finset.sum_congr rfl (fun s _ => by split_ifs <;> simp [div_eq_mul_inv]),
        ← Finset.sum_mul]
      have hsum : (∑ s : FlatProfile S, if s ⟨p, I⟩ = a then (mu s : ENNReal) else 0)
          = muMarginal (S := S) I mu a := by
        change _ = (mu.bind (fun s => PMF.pure (s ⟨p, I⟩)) ) a
        simp_all [PMF.bind_apply, PMF.pure_apply, tsum_fintype, mul_ite, mul_one, mul_zero]
        grind
      rw [hsum]
      exact ENNReal.mul_inv_cancel hpa
        (PMF.apply_ne_top (muMarginal (S := S) I mu) a))

@[simp] theorem muCond_apply {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (mu : PMF (FlatProfile S)) (hpa : muMarginal (S := S) I mu a ≠ 0)
    (s : FlatProfile S) :
    muCond (S := S) I a mu hpa s =
      if s ⟨p, I⟩ = a then mu s / (muMarginal (S := S) I mu a) else 0 := by
  simp [muCond, PMF.ofFintype_apply]

/-- A flat PMF is **player-independent** if it arises as the pushforward of a product
of per-player mixed strategies. This is the key structural property preserved
through conditioning. -/
abbrev PlayerIndep (mu : PMF (FlatProfile S)) : Prop :=
  ∃ muP : MixedProfile S, mu = pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)

---
-- Product Conditioning Algebra
---

lemma pmfPureToFlat_apply (mu : PMF (PureProfile S)) (s : FlatProfile S) :
    pmfPureToFlat (S := S) mu s = ∑ pi : PureProfile S,
      mu pi * (if flatProfileEquivPureProfile.symm pi = s then 1 else 0) := by
  simp [pmfPureToFlat, PMF.bind_apply, PMF.pure_apply, tsum_fintype,
    mul_ite, mul_one, mul_zero, eq_comm]

/-- `pmfPureToFlat mu` at flat profile `s` equals `mu` at the corresponding pure profile. -/
lemma pmfPureToFlat_eq (mu : PMF (PureProfile S)) (s : FlatProfile S) :
    pmfPureToFlat (S := S) mu s =
    mu (flatProfileEquivPureProfile (S := S) s) := by
  rw [pmfPureToFlat_apply]
  have : ∀ pi : PureProfile S,
      mu pi * (if flatProfileEquivPureProfile.symm pi = s then 1 else 0) =
      if pi = flatProfileEquivPureProfile (S := S) s then mu pi else 0 := by
    intro pi
    simp only [Equiv.symm_apply_eq]
    split_ifs with h <;> simp [h]
  simp_rw [this]
  simp [Finset.sum_ite_eq']

/-- Predicate on player `p`’s pure strategy at infoset `I`. -/
def Ep {p : S.Player} (I : S.Infoset p) (a : S.Act I) : PureStrategy S p → Prop :=
  fun sp => sp I = a

instance {p : S.Player} {I : S.Infoset p} {a : S.Act I} :
    DecidablePred (Ep (S := S) I a) :=
  fun sp => show Decidable (sp I = a) from inferInstance

instance {p : S.Player} {I : S.Infoset p} {a : S.Act I} :
    DecidablePred (fun (π : PureProfile S) => Ep (S := S) I a (π p)) :=
  fun π => show Decidable (π p I = a) from inferInstance

/-- The flat marginal at infoset I equals the pure-side pushforward. -/
lemma muMarginal_pmfPureToFlat_eq (mu : PMF (PureProfile S))
    {p : S.Player} (I : S.Infoset p) (a : S.Act I) :
    muMarginal (S := S) I (pmfPureToFlat (S := S) mu) a =
    pmfMass (μ := mu) (fun π => Ep (S := S) I a (π p)) := by
  simp only [muMarginal, PMF.bind_apply, PMF.pure_apply, tsum_fintype,
    pmfPureToFlat_eq, mul_ite, mul_one, mul_zero]
  simp only [pmfMass, pmfMask, Ep]
  -- Reindex: FlatProfile → PureProfile via the equivalence
  exact Fintype.sum_equiv (flatProfileEquivPureProfile (S := S)) _ _
    (fun s => by simp [flatProfileEquivPureProfile, eq_comm])

/-- Condition the product PMF on the coordinate event `π p I = a`
 (depends only on coordinate `p`). -/
noncomputable def pureCond (muP : MixedProfile S) {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0) : PMF (PureProfile S) :=
  pmfCond (μ := mixedProfileJoint (S := S) muP)
    (fun π => Ep (S := S) I a (π p))
    (by
      classical
      have h : pmfMass (pmfPi muP) (fun s => Ep (S := S) I a (s p)) =
          pmfMass (muP p) (Ep (S := S) I a) := pmfMass_pmfPi_coord muP p (Ep I a)
      have h' : pmfMass (μ := mixedProfileJoint (S := S) muP) (fun π => Ep (S := S) I a (π p)) =
          pmfMass (μ := muP p) (Ep (S := S) I a) := by
        simpa [mixedProfileJoint] using h
      rw [h']; exact hE)

/-- The key bridge: flat-side conditioning (`muCond`) on a product measure equals the
pushforward of pure-side conditioning (`pureCond`). This reduces all flat conditioning
questions to the product PMF machinery in `PMFProduct`. -/
theorem muCond_eq_pmfPureToFlat_pureCond
    (muP : MixedProfile S)
    {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (hpa_flat :
      muMarginal (S := S) I
        (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) a ≠ 0)
    (hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0) :
    muCond (S := S) I a
      (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) hpa_flat
      =
    pmfPureToFlat (S := S) (pureCond (S := S) muP I a hE) := by
  let e := flatProfileEquivPureProfile (S := S)
  let mu := mixedProfileJoint (S := S) muP
  -- The two denominators are equal
  have hd_eq : muMarginal (S := S) I (pmfPureToFlat (S := S) mu) a =
      pmfMass (μ := mu) (fun π => Ep (S := S) I a (π p)) :=
    muMarginal_pmfPureToFlat_eq mu I a
  ext s
  -- Key facts
  have hep : Ep (S := S) I a ((e s) p) ↔ s ⟨p, I⟩ = a := by
    simp [Ep, e, flatProfileEquivPureProfile]
  -- Expand everything at once
  simp only [muCond_apply, pmfPureToFlat_eq, pureCond, pmfCond_apply, pmfMask]
  -- After simp: LHS has if s⟨p,I⟩=a then mu(es)/muMarginal else 0
  --             RHS has (if Ep .. then mu(es) else 0) / pmfMass
  -- Both conditionals equivalent, both denominators equal
  rw [hd_eq]
  by_cases hs : s ⟨p, I⟩ = a
  · rw [if_pos hs, if_pos (hep.mpr hs)]
  · rw [if_neg hs, if_neg (show ¬ Ep (S := S) I a ((e s) p)
      from (not_congr hep).mpr hs)]
    simp

/-- Conditioning preserves player-independence, and cross-player marginals
are invariant. These two facts are the engine of the entire proof. -/
theorem PlayerIndep_pmfPureToFlat (muP : MixedProfile S) :
    PlayerIndep (S := S) (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) := by
  exact ⟨muP, rfl⟩

theorem PlayerIndep_muCond
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu)
    {p : S.Player} {I : S.Infoset p} {a : S.Act I}
    (hpa : muMarginal (S := S) I mu a ≠ 0) :
    PlayerIndep (S := S) (muCond (S := S) I a mu hpa) := by
  classical
  rcases hind with ⟨muP, rfl⟩
  -- derive the pure-side nonzero mass (you can prove this from `hpa` if you want;
  -- for now, just define it using classical choice + the fact it must be nonzero
  -- because pushforward to flat has nonzero mass).
  have hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0 := by
    rw [← pmfMass_pmfPi_coord
      (σ := muP) (j := p) (E := Ep (S := S) I a),
      ← muMarginal_pmfPureToFlat_eq]
    exact hpa
  refine ⟨Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE), ?_⟩
  -- Use the bridge lemma + the PMFProduct “conditioning a product updates only that coordinate”
  -- on the pure side:
  have hpure :
      pureCond (S := S) muP I a hE
        =
      mixedProfileJoint (S := S)
        (Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE)) := by
    -- This is exactly `pmfPi_cond_coord` specialized to index = players, event on coordinate p.
    -- (your PMFProduct lemma)
    exact pmfPi_cond_coord
      (A := fun q => PureStrategy S q) muP p
      (Ep (S := S) I a) hE
  -- finish
  calc
    muCond (S := S) I a (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) hpa
        =
      pmfPureToFlat (S := S) (pureCond (S := S) muP I a hE) := by
          simpa using (muCond_eq_pmfPureToFlat_pureCond (S := S) muP I a hpa hE)
    _ = pmfPureToFlat (S := S)
          (mixedProfileJoint (S := S)
            (Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE))) := by
          simp [hpure]
    _ = pmfPureToFlat (S := S) (mixedProfileJoint (S := S)
            (Function.update muP p (pmfCond (μ := muP p) (Ep (S := S) I a) hE))) := rfl

theorem muMarginal_muCond_other
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu)
    {p q : S.Player}
    (hpq : q ≠ p)
    {I : S.Infoset p}
    {J : S.Infoset q}
    {a : S.Act I}
    (hpa : muMarginal (S := S) I mu a ≠ 0) :
    muMarginal (S := S) J (muCond (S := S) I a mu hpa) =
    muMarginal (S := S) J mu := by
  classical
  rcases hind with ⟨muP, rfl⟩
  -- same pure-side nonzero mass as above
  have hE : pmfMass (μ := muP p) (Ep (S := S) I a) ≠ 0 := by
    rw [← pmfMass_pmfPi_coord
      (σ := muP) (j := p) (E := Ep (S := S) I a),
      ← muMarginal_pmfPureToFlat_eq]
    exact hpa
  -- rewrite `muCond` as pushforward of pure-side conditioning
  have hrew :
      muCond (S := S) I a (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)) hpa
        =
      pmfPureToFlat (S := S) (pureCond (S := S) muP I a hE) := by
    simpa using (muCond_eq_pmfPureToFlat_pureCond (S := S) muP I a hpa hE)
  -- now apply the PMFProduct lemma: conditioning the product on coordinate p
  -- doesn’t change other coordinate marginals (q ≠ p), and pushforward commutes.
  --
  -- Concretely, marginal at infoset J of player q is pushforward along `π ↦ π q J`.
  -- On the pure side, that’s still coordinate q (as a PureStrategy) then apply at J.
  -- This is one more “pushforward-compose” lemma + `pmfPi_cond_coord_push_other`.
  -- Unfold muMarginal and rewrite muCond via hrew
  simp only [muMarginal, hrew]
  -- Goal: pmfPureToFlat(pureCond).bind(s↦pure(s⟨q,J⟩)) =
  --       pmfPureToFlat(joint).bind(s↦pure(s⟨q,J⟩))
  -- Unfold pmfPureToFlat and simplify to get pure-side binds
  simp only [pmfPureToFlat, PMF.bind_bind, PMF.pure_bind]
  -- Goal: (pureCond muP I a hE).bind (· q J |> PMF.pure) =
  --       (mixedProfileJoint muP).bind (· q J |> PMF.pure)
  -- Factor through pushforward at coordinate q
  calc (pureCond (S := S) muP I a hE).bind
        (fun pi => PMF.pure (pi q J))
      = ((pureCond (S := S) muP I a hE).bind
          (fun pi => PMF.pure (pi q))).bind
          (fun sq => PMF.pure (sq J)) := by
        simp only [PMF.bind_bind, PMF.pure_bind]
    _ = ((mixedProfileJoint (S := S) muP).bind
          (fun pi => PMF.pure (pi q))).bind
          (fun sq => PMF.pure (sq J)) := by
        congr 1
        exact (pmfPi_cond_coord_push_other
          (A := fun q => PureStrategy S q) muP hpq
          (Ep (S := S) I a) hE).trans
          (pmfPi_push_coord
            (A := fun q => PureStrategy S q) muP q).symm
    _ = (mixedProfileJoint (S := S) muP).bind
          (fun pi => PMF.pure (pi q J)) := by
        simp only [PMF.bind_bind, PMF.pure_bind]

theorem muCond_comm_of_PlayerIndep
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu)
    {p q : S.Player} (hpq : p ≠ q)
    {I : S.Infoset p} {a : S.Act I}
    {J : S.Infoset q} {b : S.Act J}
    (hpa : muMarginal (S := S) I mu a ≠ 0)
    (hpb : muMarginal (S := S) J mu b ≠ 0) :
    muCond (S := S) J b (muCond (S := S) I a mu hpa)
      (by
        have : muMarginal (S := S) J (muCond (S := S) I a mu hpa) b =
            muMarginal (S := S) J mu b :=
          congrArg (fun ν => ν b)
            (muMarginal_muCond_other (S := S) mu hind
              (Ne.symm hpq) hpa)
        simpa [this] using hpb)
      =
    muCond (S := S) I a (muCond (S := S) J b mu hpb)
      (by
        have : muMarginal (S := S) I (muCond (S := S) J b mu hpb) a =
            muMarginal (S := S) I mu a :=
          congrArg (fun ν => ν a)
            (muMarginal_muCond_other (S := S) mu hind hpq hpb)
        simpa [this] using hpa) := by
  ext s
  simp only [muCond_apply]
  have hJsame :
      muMarginal (S := S) J (muCond (S := S) I a mu hpa) b =
      muMarginal (S := S) J mu b :=
    congrArg (fun ν => ν b)
      (muMarginal_muCond_other (S := S) mu hind (Ne.symm hpq) hpa)
  have hIsame :
      muMarginal (S := S) I (muCond (S := S) J b mu hpb) a =
      muMarginal (S := S) I mu a :=
    congrArg (fun ν => ν a)
      (muMarginal_muCond_other (S := S) mu hind hpq hpb)
  by_cases hsi : s ⟨p, I⟩ = a
  · by_cases hsj : s ⟨q, J⟩ = b
    · simp only [hsj, ite_true, hsi]
      rw [hJsame, hIsame]
      exact mul_right_comm _ _ _
    · simp [hsi, hsj]
  · by_cases hsj : s ⟨q, J⟩ = b
    · simp [hsi, hsj]
    · simp [hsi, hsj]

---
-- Path Conditioning, Filtering, and Perfect Recall
--
-- A `DecPath` records the sequence of player decisions along a path from the root.
-- `GoodPath mu path` witnesses that each step has nonzero marginal mass,
-- allowing sequential conditioning. `FilterPlayer q path` extracts only player
-- `q`'s decisions. The main result of this section is
-- `muMarginal_condPath_invariant_filter`: the marginal at `q`'s infoset after
-- conditioning on the full path equals the marginal after conditioning on just
-- `q`'s filtered path. Combined with perfect recall (`FilterPlayer_path_eq_history`),
-- this means the behavioral strategy at each infoset depends only on the
-- canonical history, not on the particular path to the infoset.
---

structure DecConstraint (S : InfoStructure) where
  p : S.Player
  I : S.Infoset p
  a : S.Act I
deriving DecidableEq

abbrev DecPath (S : InfoStructure) := List (DecConstraint S)

def Satisfies (s : FlatProfile S) (c : DecConstraint S) : Prop :=
  s ⟨c.p, c.I⟩ = c.a

def SatisfiesPath (s : FlatProfile S) (path : DecPath S) : Prop :=
  ∀ c, c ∈ path -> Satisfies (S := S) s c

/-- Evidence that we can condition along `path` step-by-step (each step has nonzero mass). -/
def GoodPath {S} (mu : PMF (FlatProfile S)) : DecPath S → Type
  | [] => PUnit
  | c :: cs =>
      Σ' h : muMarginal (S := S) c.I mu c.a ≠ 0,
        GoodPath (S := S) (muCond (S := S) c.I c.a mu h) cs

noncomputable def muCondPath {S} :
    (mu : PMF (FlatProfile S)) → (path : DecPath S)
     → GoodPath (S := S) mu path → PMF (FlatProfile S)
  | mu, [], _ => mu
  | mu, c :: cs, ⟨h, hgood⟩ =>
      muCondPath (S := S) (mu := muCond (S := S) c.I c.a mu h) (path := cs) hgood

@[simp] lemma muCondPath_nil (mu : PMF (FlatProfile S)) (h : GoodPath (S := S) mu []) :
    muCondPath (S := S) (mu := mu) (path := []) h = mu := rfl

@[simp] lemma muCondPath_cons (mu : PMF (FlatProfile S)) (c : DecConstraint S) (cs : DecPath S)
    (h : GoodPath (S := S) mu (c :: cs)) :
    muCondPath (S := S) (mu := mu) (path := c :: cs) h =
      muCondPath (S := S)
        (mu := muCond (S := S) c.I c.a mu h.1)
        (path := cs) h.2 := rfl

/-- `muCond` doesn't depend on which proof of nonzero mass is used. -/
theorem muCond_irrel {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (mu : PMF (FlatProfile S))
    (h1 h2 : muMarginal (S := S) I mu a ≠ 0) :
    muCond (S := S) I a mu h1 = muCond (S := S) I a mu h2 := rfl

/-- `muCondPath` doesn't depend on which `GoodPath` witness is used. -/
theorem muCondPath_irrel (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hg₁ hg₂ : GoodPath (S := S) mu path) :
    muCondPath (S := S) mu path hg₁ = muCondPath (S := S) mu path hg₂ := by
  induction path generalizing mu with
  | nil => rfl
  | cons c cs ih => exact ih (muCond (S := S) c.I c.a mu hg₁.1) hg₁.2 hg₂.2

/-- `muCondPath` is invariant under equal distributions. -/
theorem muCondPath_eq_of_eq
    {mu1 mu2 : PMF (FlatProfile S)} (h : mu1 = mu2)
    {path : DecPath S}
    (hg1 : GoodPath (S := S) mu1 path)
    (hg2 : GoodPath (S := S) mu2 path) :
    muCondPath (S := S) mu1 path hg1 =
    muCondPath (S := S) mu2 path hg2 := by
  subst h; exact muCondPath_irrel (S := S) mu1 path hg1 hg2

def RelevantTo (p : S.Player) (c : DecConstraint S) : Prop := c.p = p

noncomputable def FilterPlayer (p : S.Player) (path : DecPath S) : DecPath S :=
  path.filter (fun c => decide (c.p = p))

lemma mem_FilterPlayer_iff (p : S.Player) (c : DecConstraint S) (path : DecPath S) :
    c ∈ FilterPlayer (S := S) p path ↔ c ∈ path ∧ c.p = p := by
  classical
  simp [FilterPlayer, List.mem_filter]

def decPathToHistory : DecPath S → List (HistoryStep S)
  | [] => []
  | c :: cs => HistoryStep.action c.p c.I c.a :: decPathToHistory cs

def playerViewOfConstraint (q : S.Player) (c : DecConstraint S) (h : c.p = q) :
    Σ I : S.Infoset q, S.Act I := by
  subst h
  exact ⟨c.I, c.a⟩

def viewToConstraint (q : S.Player) (v : Σ I : S.Infoset q, S.Act I) : DecConstraint S :=
  { p := q, I := v.1, a := v.2 }

lemma viewToConstraint_playerView
    (q : S.Player) (c : DecConstraint S) (h : c.p = q) :
    viewToConstraint (S := S) q (playerViewOfConstraint (S := S) q c h) = c := by
  cases c with
  | mk p I a =>
      dsimp [playerViewOfConstraint, viewToConstraint] at *
      cases h
      rfl

def decPathPlayerView (q : S.Player) : DecPath S → List (Σ I : S.Infoset q, S.Act I)
  | [] => []
  | c :: cs =>
      if h : c.p = q then
        playerViewOfConstraint (S := S) q c h :: decPathPlayerView q cs
      else
        decPathPlayerView q cs

lemma decPathPlayerView_eq_playerHistory (q : S.Player) (path : DecPath S) :
    decPathPlayerView (S := S) q path =
      playerHistory S q (decPathToHistory (S := S) path) := by
  induction path with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [decPathToHistory, decPathPlayerView, playerHistory, ih]
      by_cases h : c.p = q
      · simp [h, playerViewOfConstraint]
      · simp [h]

lemma map_viewToConstraint_decPathPlayerView
    (q : S.Player) (path : DecPath S) :
    List.map (viewToConstraint (S := S) q) (decPathPlayerView (S := S) q path)
      =
    FilterPlayer (S := S) q path := by
  induction path with
  | nil =>
      rfl
  | cons c cs ih =>
      by_cases h : c.p = q
      · simp [decPathPlayerView, FilterPlayer, h, ih]
        simp [viewToConstraint_playerView (S := S) q c h]
      · simp [decPathPlayerView, FilterPlayer, h, ih]

inductive SubtreeAt : GameTree S Outcome -> DecPath S -> GameTree S Outcome -> Prop where
  | refl (t : GameTree S Outcome) : SubtreeAt t [] t
  | chance {k : Nat} {muC : PMF (Fin k)} {hk : 0 < k} {next : Fin k -> GameTree S Outcome}
      {path : DecPath S} {u : GameTree S Outcome} {b : Fin k} :
      SubtreeAt (next b) path u -> SubtreeAt (.chance k muC hk next) path u
  | decision {pOwner : S.Player} {I0 : S.Infoset pOwner}
      {next : S.Act I0 -> GameTree S Outcome}
      {path : DecPath S} {u : GameTree S Outcome} {a : S.Act I0} :
      SubtreeAt (next a) path u ->
      SubtreeAt (.decision I0 next)
        ({ p := pOwner, I := I0, a := a } :: path) u

/-- Transitivity of SubtreeAt. -/
theorem SubtreeAt.trans {t₁ t₂ t₃ : GameTree S Outcome}
    {p₁ p₂ : DecPath S}
    (h₁ : SubtreeAt (S := S) (Outcome := Outcome) t₁ p₁ t₂)
    (h₂ : SubtreeAt (S := S) (Outcome := Outcome) t₂ p₂ t₃) :
    SubtreeAt (S := S) (Outcome := Outcome) t₁ (p₁ ++ p₂) t₃ := by
  induction h₁ with
  | refl => simpa
  | chance _ ih => exact .chance (ih h₂)
  | decision _ ih => exact .decision (ih h₂)

/-- Go from a decision node to one of its children via transitivity.
    The child's path extends the parent's by appending the decision. -/
theorem SubtreeAt.decision_child
    {t : GameTree S Outcome}
    {pi : DecPath S}
    {pOwner : S.Player} {I0 : S.Infoset pOwner}
    {next : S.Act I0 → GameTree S Outcome}
    (hsub : SubtreeAt (S := S) (Outcome := Outcome) t pi
      (.decision I0 next))
    (a : S.Act I0) :
    SubtreeAt (S := S) (Outcome := Outcome) t
      (pi ++ [{ p := pOwner, I := I0, a := a }]) (next a) :=
  hsub.trans (.decision (.refl _))

/-- Bridge from SubtreeAt to ReachBy, preserving player history. -/
theorem SubtreeAt_to_ReachBy_with_playerHistory
    {tRoot u : GameTree S Outcome} {pi : DecPath S}
    (hsub : SubtreeAt (S := S) (Outcome := Outcome) tRoot pi u) :
    ∃ h, ReachBy (S := S) (Outcome := Outcome) h tRoot u ∧
      ∀ q, playerHistory S q h = decPathPlayerView (S := S) q pi := by
  induction hsub with
  | refl t => exact ⟨[], ReachBy.here t, fun _ => rfl⟩
  | @chance k muC hk next path u b _ ih =>
    rcases ih with ⟨h, hreach, hview⟩
    exact ⟨HistoryStep.chance k b :: h, ReachBy.chance b hreach, fun q => by
      simp [playerHistory, hview q]⟩
  | @decision pOwner I0 next path u a _ ih =>
    rcases ih with ⟨h, hreach, hview⟩
    refine ⟨HistoryStep.action pOwner I0 a :: h, ReachBy.action a hreach, fun q => ?_⟩
    simp only [playerHistory, decPathPlayerView]
    by_cases hp : pOwner = q
    · subst hp
      simp [playerViewOfConstraint, hview _]
    · simp [hp, hview q]

def PathReachesInfoset
    (tRoot : GameTree S Outcome)
    (pi : DecPath S)
    {q : S.Player}
    (J : S.Infoset q) : Prop :=
  ∃ next, SubtreeAt (S := S) (Outcome := Outcome) tRoot pi (.decision J next)

open Classical in
noncomputable def qHistoryList (tRoot : GameTree S Outcome) (q : S.Player)
    (J : S.Infoset q) : DecPath S :=
  if h : ∃ pi, PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi J then
    FilterPlayer (S := S) q (Classical.choose h)
  else
    []

noncomputable def qHistory (tRoot : GameTree S Outcome) (q : S.Player)
    (J : S.Infoset q) : Finset (DecConstraint S) :=
  (qHistoryList (S := S) (Outcome := Outcome) tRoot q J).toFinset

/-- Extend a good path by one more constraint, using a nonzero-mass proof at the end. -/
noncomputable def GoodPath.snoc
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hpath : GoodPath (S := S) mu path)
    (c : DecConstraint S)
    (hc : muMarginal (S := S) c.I (muCondPath (S := S) (mu := mu) (path := path) hpath) c.a ≠ 0) :
    GoodPath (S := S) mu (path ++ [c]) := by
  induction path generalizing mu with
  | nil =>
      -- path = []
      exact ⟨hc, ⟨⟩⟩
  | cons c0 cs ih =>
      rcases hpath with ⟨h0, hcs⟩
      refine ⟨h0, ?_⟩
      -- now we are under the conditioned measure
      exact ih
        (mu := muCond (S := S) c0.I c0.a mu h0)
        (hpath := hcs)
        (hc := hc)

theorem muCondPath_step_eq_append
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hpath : GoodPath (S := S) mu path)
    (c : DecConstraint S)
    (hc : muMarginal (S := S) c.I (muCondPath (S := S) (mu := mu) (path := path) hpath) c.a ≠ 0) :
    muCond (S := S) c.I c.a (muCondPath (S := S) (mu := mu) (path := path) hpath) hc =
      muCondPath (S := S) (mu := mu) (path := path ++ [c])
        (GoodPath.snoc (S := S) mu path hpath c hc) := by
  -- unfold muCondPath on (path ++ [c]); it peels off the final `c` exactly once
  induction path generalizing mu with
  | nil =>
      -- path = []
      rfl
  | cons c0 cs ih =>
      -- reduce both sides under the first step `c0`
      rcases hpath with ⟨h0, hcs⟩
      -- both sides start with the same conditioning on c0, so recurse
      simp [muCondPath, GoodPath.snoc, List.cons_append, ih]

theorem PlayerIndep_muCondPath
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hind : PlayerIndep (S := S) mu)
    (hgood : GoodPath (S := S) mu path) :
    PlayerIndep (S := S) (muCondPath (S := S) mu path hgood) := by
  induction path generalizing mu with
  | nil => exact hind
  | cons c cs ih =>
    exact ih (muCond (S := S) c.I c.a mu hgood.1)
      (PlayerIndep_muCond (S := S) mu hind hgood.1)
      hgood.2

/-- Canonical witness that filtered constraints remain conditionable when we drop
    a non-q conditioning step. -/
noncomputable def goodPath_transport_other
    (mu : PMF (FlatProfile S))
    (c : DecConstraint S)
    (cs : DecPath S)
    (q : S.Player)
    (hc : muMarginal (S := S) c.I mu c.a ≠ 0)
    (hneq : c.p ≠ q)
    (hind : PlayerIndep (S := S) mu)
    (hcs :
      GoodPath (S := S)
        (muCond (S := S) c.I c.a mu hc)
        (FilterPlayer (S := S) q cs)) :
    GoodPath (S := S) mu (FilterPlayer (S := S) q cs) := by
  induction cs generalizing mu with
  | nil =>
      simpa [FilterPlayer] using (PUnit.unit : GoodPath (S := S) mu [])
  | cons d ds ih =>
      by_cases hdq : d.p = q
      · have hshape :
            GoodPath (S := S) (muCond (S := S) c.I c.a mu hc)
              (d :: FilterPlayer (S := S) q ds) := by
          simpa [FilterPlayer, hdq] using hcs
        rcases hshape with ⟨hd_cond, htail_cond⟩
        have hdp_ne_cp : d.p ≠ c.p := by
          intro hdc; exact hneq (hdc ▸ hdq)
        have hd_nonzero : muMarginal (S := S) d.I mu d.a ≠ 0 := by
          have hmarg :
              muMarginal (S := S) d.I (muCond (S := S) c.I c.a mu hc) d.a
                = muMarginal (S := S) d.I mu d.a :=
            congrArg (fun ν => ν d.a)
              (muMarginal_muCond_other (S := S) (mu := mu) hind
                hdp_ne_cp (I := c.I) (J := d.I) (a := c.a) hc)
          simpa [hmarg] using hd_cond
        have hc_after : muMarginal (S := S) c.I
            (muCond (S := S) d.I d.a mu hd_nonzero) c.a ≠ 0 := by
          have hmarg :
              muMarginal (S := S) c.I (muCond (S := S) d.I d.a mu hd_nonzero) c.a
                = muMarginal (S := S) c.I mu c.a :=
            congrArg (fun ν => ν c.a)
              (muMarginal_muCond_other (S := S) (mu := mu) hind
                (by simpa using hdp_ne_cp.symm)
                (I := d.I) (J := c.I) (a := d.a) hd_nonzero)
          simpa [hmarg] using hc
        have hind_d :
            PlayerIndep (S := S) (muCond (S := S) d.I d.a mu hd_nonzero) :=
          PlayerIndep_muCond (S := S) (mu := mu) hind hd_nonzero
        have hcomm :
            muCond (S := S) d.I d.a (muCond (S := S) c.I c.a mu hc) hd_cond
              =
            muCond (S := S) c.I c.a (muCond (S := S) d.I d.a mu hd_nonzero) hc_after := by
          simpa using
            muCond_comm_of_PlayerIndep (S := S) (mu := mu) hind
              (Ne.symm hdp_ne_cp) (I := c.I) (a := c.a)
              (J := d.I) (b := d.a) hc hd_nonzero
        have htail' :
            GoodPath (S := S)
              (muCond (S := S) c.I c.a (muCond (S := S) d.I d.a mu hd_nonzero) hc_after)
              (FilterPlayer (S := S) q ds) :=
          cast (by rw [hcomm]) htail_cond
        have htail :
            GoodPath (S := S) (muCond (S := S) d.I d.a mu hd_nonzero)
              (FilterPlayer (S := S) q ds) :=
          ih (mu := muCond (S := S) d.I d.a mu hd_nonzero)
            (hc := hc_after) (hind := hind_d) (hcs := htail')
        simpa [FilterPlayer, hdq] using (⟨hd_nonzero, htail⟩ :
          GoodPath (S := S) mu (d :: FilterPlayer (S := S) q ds))
      · have hshape :
            GoodPath (S := S) (muCond (S := S) c.I c.a mu hc)
              (FilterPlayer (S := S) q ds) := by
          simpa [FilterPlayer, hdq] using hcs
        have htail :
            GoodPath (S := S) mu (FilterPlayer (S := S) q ds) :=
          ih (mu := mu) (hc := hc) (hind := hind) (hcs := hshape)
        simpa [FilterPlayer, hdq] using htail

noncomputable def goodPathFilter
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hgood : GoodPath (S := S) mu path) (q : S.Player)
    (hind : PlayerIndep (S := S) mu) :
    GoodPath (S := S) mu (FilterPlayer (S := S) q path) := by
  induction path generalizing mu with
  | nil =>
      simpa [FilterPlayer] using (PUnit.unit : GoodPath (S := S) mu [])
  | cons c cs ih =>
      rcases hgood with ⟨hc, hcs⟩
      by_cases hq : c.p = q
      · simp only [FilterPlayer, hq, decide_true, List.filter_cons_of_pos]
        refine ⟨?_, ?_⟩
        · simpa [hq] using hc
        · exact ih (muCond (S := S) c.I c.a mu hc) hcs
            (PlayerIndep_muCond (S := S) mu hind hc)
      · simp only [FilterPlayer, hq, decide_false, Bool.false_eq_true, not_false_eq_true,
          List.filter_cons_of_neg]
        exact goodPath_transport_other (S := S) mu c cs q hc hq hind
          (ih (muCond (S := S) c.I c.a mu hc) hcs
            (PlayerIndep_muCond (S := S) mu hind hc))

/-- Conditioning on a constraint for a different player, then conditioning along a path,
    gives the same marginal at player q's infoset as just conditioning along the path.
    This follows from the product structure: non-q conditioning only modifies non-q coordinates. -/
theorem muMarginal_skip_nonq_cond
    (mu : PMF (FlatProfile S)) (hind : PlayerIndep (S := S) mu)
    (c : DecConstraint S) (q : S.Player) (hcq : c.p ≠ q)
    (J : S.Infoset q)
    (hc : muMarginal (S := S) c.I mu c.a ≠ 0)
    (path : DecPath S)
    (hall : ∀ d, d ∈ path → d.p = q)
    (hgood1 : GoodPath (S := S) (muCond (S := S) c.I c.a mu hc) path)
    (hgood2 : GoodPath (S := S) mu path) :
    muMarginal (S := S) J
      (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc) path hgood1) =
    muMarginal (S := S) J (muCondPath (S := S) mu path hgood2) := by
  induction path generalizing mu with
  | nil =>
      simp only [muCondPath]
      exact muMarginal_muCond_other (S := S) mu hind (Ne.symm hcq) hc
  | cons d ds ih =>
      have hdq : d.p = q := hall d (List.mem_cons.mpr (Or.inl rfl))
      have hdp_ne_cp : d.p ≠ c.p := by
        intro hdc; exact hcq (hdc ▸ hdq)
      rcases hgood1 with ⟨hd_cond, htail_cond⟩
      rcases hgood2 with ⟨hd_base, htail_base⟩
      have hc_after :
          muMarginal (S := S) c.I
            (muCond (S := S) d.I d.a mu hd_base) c.a ≠ 0 := by
        have hmarg :
            muMarginal (S := S) c.I (muCond (S := S) d.I d.a mu hd_base) c.a
              = muMarginal (S := S) c.I mu c.a :=
          congrArg (fun ν => ν c.a)
            (muMarginal_muCond_other (S := S) (mu := mu) hind
              (Ne.symm hdp_ne_cp) hd_base)
        simpa [hmarg] using hc
      have hcomm :
          muCond (S := S) d.I d.a (muCond (S := S) c.I c.a mu hc) hd_cond
            =
          muCond (S := S) c.I c.a
            (muCond (S := S) d.I d.a mu hd_base) hc_after := by
        simpa using
          muCond_comm_of_PlayerIndep (S := S) (mu := mu) hind
            (Ne.symm hdp_ne_cp) (I := c.I) (a := c.a)
            (J := d.I) (b := d.a) hc hd_base
      have htail_cond' :
          GoodPath (S := S)
            (muCond (S := S) c.I c.a
              (muCond (S := S) d.I d.a mu hd_base) hc_after)
            ds :=
        cast (by rw [hcomm]) htail_cond
      have hind_d :
          PlayerIndep (S := S) (muCond (S := S) d.I d.a mu hd_base) :=
        PlayerIndep_muCond (S := S) mu hind hd_base
      have hall_tail : ∀ d', d' ∈ ds → d'.p = q :=
        fun d' hd'mem => hall d' (List.mem_cons.mpr (Or.inr hd'mem))
      calc
        muMarginal (S := S) J
            (muCondPath (S := S) (muCond (S := S) c.I c.a mu hc)
              (d :: ds) ⟨hd_cond, htail_cond⟩)
          = muMarginal (S := S) J
            (muCondPath (S := S)
              (muCond (S := S) c.I c.a
                (muCond (S := S) d.I d.a mu hd_base) hc_after)
              ds htail_cond') := by
                simp only [muCondPath]
                congr 1
                exact muCondPath_eq_of_eq (S := S)
                  hcomm htail_cond htail_cond'
        _ = muMarginal (S := S) J
            (muCondPath (S := S) (muCond (S := S) d.I d.a mu hd_base) ds htail_base) :=
          ih (muCond (S := S) d.I d.a mu hd_base)
            hind_d hc_after hall_tail htail_cond' htail_base
        _ = muMarginal (S := S) J
            (muCondPath (S := S) mu (d :: ds) ⟨hd_base, htail_base⟩) := by
              simp [muCondPath]

theorem muMarginal_condPath_invariant_filter
    (mu : PMF (FlatProfile S)) (path : DecPath S)
    (hind : PlayerIndep (S := S) mu)
    (hgood : GoodPath (S := S) mu path)
    (q : S.Player) (J : S.Infoset q)
    (hgoodF : GoodPath (S := S) mu (FilterPlayer (S := S) q path)) :
    muMarginal (S := S) J (muCondPath (S := S) mu path hgood) =
    muMarginal (S := S) J
      (muCondPath (S := S) mu (FilterPlayer (S := S) q path) hgoodF) := by
  induction path generalizing mu with
  | nil => rfl
  | cons c cs ih =>
    -- muCondPath (c :: cs) = muCondPath cs ∘ muCond c
    -- FilterPlayer q (c :: cs) = if c.p = q then c :: FilterPlayer q cs
    --                                       else FilterPlayer q cs
    by_cases hcq : c.p = q
    · -- c.p = q: FilterPlayer keeps c, both sides peel off c
      subst hcq
      -- FilterPlayer c.p (c :: cs) = c :: FilterPlayer c.p cs propositionally
      have hfilt : FilterPlayer (S := S) c.p (c :: cs) =
          c :: FilterPlayer (S := S) c.p cs := by
        simp [FilterPlayer]
      -- Transport hgoodF to the simplified type
      revert hgoodF; rw [hfilt]; intro hgoodF
      -- Now hgoodF : GoodPath mu (c :: FilterPlayer c.p cs)
      exact ih (muCond (S := S) c.I c.a mu hgood.1)
        (PlayerIndep_muCond (S := S) mu hind hgood.1)
        hgood.2 hgoodF.2
    · -- c.p ≠ q: FilterPlayer drops c, so FilterPlayer q (c::cs) = FilterPlayer q cs
      have hfilt : FilterPlayer (S := S) q (c :: cs) =
          FilterPlayer (S := S) q cs := by
        simp [FilterPlayer, hcq]
      -- Transport hgoodF
      revert hgoodF; rw [hfilt]; intro hgoodF
      -- LHS: muMarginal J (muCondPath (muCond c mu) cs)
      -- By IH on cs with mu' = muCond c mu:
      --   = muMarginal J (muCondPath (muCond c mu) (FilterPlayer q cs))
      -- Then by skip lemma: = muMarginal J (muCondPath mu (FilterPlayer q cs))
      let mu' := muCond (S := S) c.I c.a mu hgood.1
      -- We need a GoodPath for FilterPlayer q cs under mu'
      have hind' := PlayerIndep_muCond (S := S) mu hind hgood.1
      -- Use muMarginal_condPath_invariant_filter (IH) to reduce to filtered path under mu'
      have hgoodF' : GoodPath (S := S) mu' (FilterPlayer (S := S) q cs) :=
        goodPathFilter (S := S) mu' cs hgood.2 q hind'
      have hallF : ∀ d, d ∈ FilterPlayer (S := S) q cs → d.p = q :=
        fun d hd => ((mem_FilterPlayer_iff (S := S) q d cs).mp hd).2
      calc muMarginal (S := S) J (muCondPath (S := S) mu (c :: cs) hgood)
          = muMarginal (S := S) J (muCondPath (S := S) mu' cs hgood.2) := rfl
        _ = muMarginal (S := S) J
              (muCondPath (S := S) mu' (FilterPlayer (S := S) q cs) hgoodF') :=
            ih mu' hind' hgood.2 hgoodF'
        _ = muMarginal (S := S) J
              (muCondPath (S := S) mu (FilterPlayer (S := S) q cs) hgoodF) :=
            muMarginal_skip_nonq_cond (S := S) mu hind c q hcq J hgood.1
              (FilterPlayer (S := S) q cs) hallF hgoodF' hgoodF

theorem FilterPlayer_path_eq_history
    (tRoot : GameTree S Outcome)
    (hpr : PerfectRecall tRoot)
    {q : S.Player}
    {J : S.Infoset q}
    {pi : DecPath S}
    (hreach : PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi J) :
    FilterPlayer (S := S) q pi = qHistoryList (S := S) (Outcome := Outcome) tRoot q J := by
  classical
  unfold qHistoryList
  have hEx : ∃ pi', PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi' J :=
    ⟨pi, hreach⟩
  simp only [hEx, ↓reduceDIte]
  -- Let pi0 be the canonical chosen path
  let pi0 : DecPath S := Classical.choose hEx
  have hpi0 : PathReachesInfoset (S := S) (Outcome := Outcome) tRoot pi0 J :=
    Classical.choose_spec hEx
  -- Extract SubtreeAt witnesses
  rcases hreach with ⟨next, hsub⟩
  rcases hpi0 with ⟨next0, hsub0⟩
  -- Convert to ReachBy with playerHistory
  rcases SubtreeAt_to_ReachBy_with_playerHistory (S := S) (Outcome := Outcome) hsub with
    ⟨h, hreach_h, hview⟩
  rcases SubtreeAt_to_ReachBy_with_playerHistory (S := S) (Outcome := Outcome) hsub0 with
    ⟨h0, hreach_h0, hview0⟩
  -- Apply PerfectRecall
  have hPR : playerHistory S q h = playerHistory S q h0 :=
    hpr h h0 J next next0 hreach_h hreach_h0
  -- Convert playerHistory to decPathPlayerView
  have hpv : decPathPlayerView (S := S) q pi = decPathPlayerView (S := S) q pi0 := by
    rw [← hview q, ← hview0 q, hPR]
  -- Convert decPathPlayerView to FilterPlayer via map_viewToConstraint_decPathPlayerView
  have := map_viewToConstraint_decPathPlayerView (S := S) q pi
  have := map_viewToConstraint_decPathPlayerView (S := S) q pi0
  -- FilterPlayer = map viewToConstraint (decPathPlayerView q ·)
  calc FilterPlayer (S := S) q pi
      = List.map (viewToConstraint (S := S) q) (decPathPlayerView (S := S) q pi) := by
        rw [map_viewToConstraint_decPathPlayerView]
    _ = List.map (viewToConstraint (S := S) q) (decPathPlayerView (S := S) q pi0) := by
        rw [hpv]
    _ = FilterPlayer (S := S) q pi0 := by
        rw [map_viewToConstraint_decPathPlayerView]

---
-- Behavioral Strategy Construction and Inductive Evaluation
--
-- `mixedToBehavioralRoot` defines the behavioral strategy: at each infoset,
-- condition the flat product measure on the canonical history, then take the
-- marginal. The main induction (`eval_subtree_correct`) shows that evaluating
-- any subtree under this behavioral strategy equals the conditional expectation
-- under the product measure.
---

/-- The behavioral strategy induced by a flat product measure. At infoset `I`,
condition on the canonical history of decisions leading to `I`, then take the
marginal at `I`. Falls back to the unconditional marginal when the history has
zero mass (unreachable infoset). -/
noncomputable def mixedToBehavioralRoot
    (mu : PMF (FlatProfile S)) (tRoot : GameTree S Outcome) :
    BehavioralProfile S :=
  fun q J => by
    classical
    let hlist := qHistoryList (S := S) (Outcome := Outcome) tRoot q J
    by_cases hgood : Nonempty (GoodPath (S := S) mu hlist)
    · exact muMarginal (S := S) J
        (muCondPath (S := S) mu hlist (Classical.choice hgood))
    · exact muMarginal (S := S) J mu

/-- Disintegration / law of total probability for muCond:
    Splitting a bind by the value at an infoset. -/
theorem muCond_disintegration
    {p : S.Player} (I : S.Infoset p)
    (mu : PMF (FlatProfile S))
    (f : FlatProfile S → PMF Outcome) (x : Outcome) :
    (mu.bind f) x =
    ∑ a : S.Act I,
      ∑ s : FlatProfile S,
        (if s ⟨p, I⟩ = a then mu s else 0) * (f s x) := by
  simpa using
    (Math.ProbabilityMassFunction.bind_apply_eq_sum_sum_fiber
      (μ := mu) (proj := fun s => s ⟨p, I⟩) (g := f) (x := x))

theorem mixedToBehavioral_context_eq
    (mu : PMF (FlatProfile S)) (tRoot : GameTree S Outcome)
    (hpr : PerfectRecall tRoot) (hind : PlayerIndep (S := S) mu)
    (pi : DecPath S) (hgood : GoodPath (S := S) mu pi)
    {pOwner : S.Player} {I0 : S.Infoset pOwner}
    (hreach : PathReachesInfoset (S := S) (Outcome := Outcome)
      tRoot pi I0) :
    mixedToBehavioralRoot (S := S) (Outcome := Outcome)
      mu tRoot pOwner I0 =
      muMarginal (S := S) I0
        (muCondPath (S := S) mu pi hgood) := by
  classical
  have h_hist :
      FilterPlayer (S := S) pOwner pi =
      qHistoryList (S := S) (Outcome := Outcome)
        tRoot pOwner I0 := by
    simpa using
      (FilterPlayer_path_eq_history (S := S) (Outcome := Outcome)
        (tRoot := tRoot) hpr (q := pOwner)
        (J := I0) (pi := pi) hreach)
  -- Derive GoodPath for the history list
  have hgoodF : GoodPath (S := S) mu (FilterPlayer (S := S) pOwner pi) :=
    goodPathFilter (S := S) mu pi hgood pOwner hind
  have hgoodHist : GoodPath (S := S) mu
      (qHistoryList (S := S) (Outcome := Outcome) tRoot pOwner I0) :=
    h_hist ▸ hgoodF
  -- Show mixedToBehavioralRoot takes the good branch
  have hne : Nonempty (GoodPath (S := S) mu
      (qHistoryList (S := S) (Outcome := Outcome) tRoot pOwner I0)) :=
    ⟨hgoodHist⟩
  -- Unfold and simplify
  unfold mixedToBehavioralRoot
  simp only [hne, ↓reduceDIte]
  -- The chosen GoodPath may differ from ours, but muCondPath is proof-irrelevant
  have hrw :
      muCondPath (S := S) mu
        (qHistoryList (S := S) (Outcome := Outcome) tRoot pOwner I0)
        (Classical.choice hne) =
      muCondPath (S := S) mu
        (FilterPlayer (S := S) pOwner pi) hgoodF := by
    revert hgoodF; rw [h_hist]; intro hgoodF
    exact muCondPath_irrel (S := S) mu _ _ _
  rw [hrw]
  exact (muMarginal_condPath_invariant_filter (S := S)
    mu pi hind hgood pOwner I0 hgoodF).symm

/-- If muMarginal I mu a = 0 then mu s = 0 for any s with s⟨p,I⟩=a. -/
theorem muMarginal_zero_of_coord
    {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (mu : PMF (FlatProfile S))
    (ha : muMarginal (S := S) I mu a = 0)
    (s : FlatProfile S) (hs : s ⟨p, I⟩ = a) :
    mu s = 0 := by
  have hpush :
      Math.ProbabilityMassFunction.pushforward
        mu (fun t : FlatProfile S => t ⟨p, I⟩) a = 0 := by
    simpa [muMarginal, Math.ProbabilityMassFunction.pushforward] using ha
  exact Math.ProbabilityMassFunction.eq_zero_of_pushforward_eq_zero
    (μ := mu) (proj := fun t : FlatProfile S => t ⟨p, I⟩) (b := a) hpush hs

/-- Mass times conditional = indicator times original. -/
theorem muMarginal_mul_muCond_apply
    {p : S.Player} (I : S.Infoset p) (a : S.Act I)
    (mu : PMF (FlatProfile S))
    (ha : muMarginal (S := S) I mu a ≠ 0)
    (s : FlatProfile S) :
    muMarginal (S := S) I mu a *
      muCond (S := S) I a mu ha s =
    if s ⟨p, I⟩ = a then mu s else 0 := by
  have hne_top : (muMarginal (S := S) I mu) a ≠ ⊤ :=
    PMF.apply_ne_top (muMarginal (S := S) I mu) a
  simp only [muCond_apply]
  split_ifs with hs
  · rw [mul_comm,
      ENNReal.div_mul_cancel ha hne_top]
  · simp

/-- The inductive step for decision nodes. -/
theorem eval_subtree_decision_step
    (tRoot : GameTree S Outcome)
    (hpr : PerfectRecall tRoot)
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu)
    {pOwner : S.Player} {I0 : S.Infoset pOwner}
    {next : S.Act I0 → GameTree S Outcome}
    {pi : DecPath S} (hgood : GoodPath (S := S) mu pi)
    (h_sub : SubtreeAt (S := S) (Outcome := Outcome)
      tRoot pi (.decision I0 next))
    (hreach : PathReachesInfoset (S := S) (Outcome := Outcome)
      tRoot pi I0)
    (ih : ∀ (a : S.Act I0)
        (hga : GoodPath (S := S) mu
          (pi ++ [{ p := pOwner, I := I0, a := a }])),
        SubtreeAt (S := S) (Outcome := Outcome)
          tRoot
          (pi ++ [{ p := pOwner, I := I0, a := a }])
          (next a) →
        (next a).evalDist
          (mixedToBehavioralRoot (S := S)
            (Outcome := Outcome) mu tRoot) =
        (muCondPath (S := S) mu
          (pi ++ [{ p := pOwner, I := I0, a := a }])
          hga).bind
          (fun s => (next a).evalFlat (S := S)
            (Outcome := Outcome) s)) :
    (GameTree.decision (S := S) (Outcome := Outcome)
      I0 next).evalDist
        (mixedToBehavioralRoot (S := S) (Outcome := Outcome)
          mu tRoot)
      =
    (muCondPath (S := S) mu pi hgood).bind
      (fun s =>
        (GameTree.decision (S := S) (Outcome := Outcome)
          I0 next).evalFlat (S := S)
            (Outcome := Outcome) s) := by
  simp only [evalDist_decision]
  have hctx :
      mixedToBehavioralRoot (S := S) (Outcome := Outcome)
        mu tRoot pOwner I0 =
      muMarginal (S := S) I0
        (muCondPath (S := S) mu pi hgood) :=
    mixedToBehavioral_context_eq (S := S) (Outcome := Outcome)
      mu tRoot hpr hind pi hgood hreach
  rw [hctx]
  conv_rhs =>
    rw [show
      (fun s =>
        (GameTree.decision (S := S) (Outcome := Outcome)
          I0 next).evalFlat (S := S)
            (Outcome := Outcome) s) =
      (fun s =>
        (next (s ⟨pOwner, I0⟩)).evalFlat (S := S)
          (Outcome := Outcome) s) from by
        funext s; simp [GameTree.evalFlat,
          evalDist_decision, flatToBehavioral,
          PMF.pure_bind]]
  -- Goal: (muMarginal I0 μ_pi).bind (fun a => evalDist σ (next a))
  --     = μ_pi.bind (fun s => (next (s⟨p,I0⟩)).evalFlat s)
  -- Prove pointwise
  set μ_pi := muCondPath (S := S) mu pi hgood with hμ_def
  ext x
  simp only [PMF.bind_apply, tsum_fintype]
  -- Split RHS sum by action at I0
  rw [show (∑ s : FlatProfile S, μ_pi s *
      ((next (s ⟨pOwner, I0⟩)).evalFlat (S := S)
        (Outcome := Outcome) s) x) =
    ∑ a : S.Act I0, ∑ s : FlatProfile S,
      if s ⟨pOwner, I0⟩ = a
      then μ_pi s *
        ((next a).evalFlat (S := S)
          (Outcome := Outcome) s) x
      else 0 from by
    rw [Finset.sum_comm]; congr 1; funext s; symm
    rw [Finset.sum_ite_eq]; simp [Finset.mem_univ]]
  -- Now both sides: ∑ a, f(a)
  congr 1; funext a
  -- Per-action identity
  by_cases ha :
      muMarginal (S := S) I0 μ_pi a = 0
  · -- Zero mass: both sides = 0
    simp only [ha, zero_mul]
    symm; apply Finset.sum_eq_zero
    intro s _
    split_ifs with hs
    · have : μ_pi s = 0 :=
        muMarginal_zero_of_coord (S := S) I0 a
          μ_pi ha s hs
      simp [this]
    · rfl
  · -- Nonzero mass: use IH
    have hga : GoodPath (S := S) mu
        (pi ++ [{ p := pOwner, I := I0, a := a }]) :=
      GoodPath.snoc (S := S) mu pi hgood
        { p := pOwner, I := I0, a := a } ha
    have hsub_a : SubtreeAt (S := S) (Outcome := Outcome)
        tRoot
        (pi ++ [{ p := pOwner, I := I0, a := a }])
        (next a) := h_sub.decision_child a
    have hih := ih a hga hsub_a
    -- Replace evalDist with bind of evalFlat via IH
    rw [show (GameTree.evalDist
        (mixedToBehavioralRoot (S := S) (Outcome := Outcome)
          mu tRoot) (next a)) x =
      ((muCondPath (S := S) mu
        (pi ++ [{ p := pOwner, I := I0, a := a }])
        hga).bind
        (fun s => (next a).evalFlat (S := S)
          (Outcome := Outcome) s)) x from by
      rw [← hih]]
    -- Rewrite muCondPath(pi++[c]) to muCond I0 a μ_pi
    rw [show muCondPath (S := S) mu
        (pi ++ [{ p := pOwner, I := I0, a := a }])
        hga =
      muCond (S := S) I0 a μ_pi ha from
      (muCondPath_irrel (S := S) mu _ hga
        (GoodPath.snoc (S := S) mu pi hgood
          { p := pOwner, I := I0, a := a } ha)).trans
      (muCondPath_step_eq_append (S := S) mu pi
        hgood
        { p := pOwner, I := I0, a := a } ha).symm]
    simp only [PMF.bind_apply, tsum_fintype]
    -- LHS: marginal(a) * ∑ s, muCond(s) * evalFlat(s)
    -- RHS: ∑ s, [s⟨p,I0⟩=a] * μ_pi(s) * evalFlat(s)
    rw [Finset.mul_sum]
    congr 1; funext s
    rw [← mul_assoc,
      muMarginal_mul_muCond_apply (S := S)
        I0 a μ_pi ha s]
    split_ifs <;> simp

theorem eval_subtree_correct
    (tRoot : GameTree S Outcome)
    (hpr : PerfectRecall tRoot)
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu) :
    ∀ (u : GameTree S Outcome) (pi : DecPath S)
      (hgood : GoodPath (S := S) mu pi),
      SubtreeAt (S := S) (Outcome := Outcome) tRoot pi u ->
      u.evalDist (mixedToBehavioralRoot (S := S) (Outcome := Outcome)
        mu tRoot) =
      (muCondPath (S := S) mu pi hgood).bind
        (fun s => u.evalFlat s) := by
  intro u
  induction u with
  | terminal z =>
    -- terminal: both sides = PMF.pure z
    intro pi hgood _
    simp only [evalDist_terminal]
    -- RHS: mu_pi.bind (fun _ => PMF.pure z) = PMF.pure z
    symm
    ext x
    simp only [GameTree.evalFlat, evalDist_terminal,
      PMF.bind_apply, PMF.pure_apply, tsum_fintype]
    have hsum : ∑ s : FlatProfile S,
        (muCondPath (S := S) mu pi hgood) s = 1 := by
      have := PMF.tsum_coe (muCondPath (S := S) mu pi hgood)
      rwa [tsum_fintype] at this
    split_ifs <;> simp [hsum]
  | chance k muC hk next ih_chance =>
    -- chance: swap bind order using Fubini, then apply IH per branch
    intro pi hgood hsub
    simp only [evalDist_chance]
    -- Unfold evalFlat on RHS to expose the inner structure
    change _ = (muCondPath (S := S) mu pi hgood).bind
      (fun s => muC.bind (fun b =>
        (next b).evalDist (flatToBehavioral (S := S) s)))
    -- Swap the bind order (Fubini)
    rw [PMF.bind_comm]
    -- Now both sides: muC.bind (fun b => ...)
    congr 1; funext b
    -- Get SubtreeAt tRoot pi (next b) via transitivity
    have hsub_b : SubtreeAt (S := S) (Outcome := Outcome)
        tRoot pi (next b) := by
      have := hsub.trans (SubtreeAt.chance (b := b)
        (SubtreeAt.refl (next b)))
      simpa using this
    exact ih_chance b pi hgood hsub_b
  | decision I0 next ih_dec =>
    -- decision: the core case, delegated to eval_subtree_decision_step
    intro pi hgood hsub
    have hreach : PathReachesInfoset (S := S) (Outcome := Outcome)
        tRoot pi I0 :=
      ⟨next, hsub⟩
    exact eval_subtree_decision_step (S := S) (Outcome := Outcome)
      tRoot hpr mu hind hgood hsub hreach
      (fun a hga hsub_a => ih_dec a _ hga hsub_a)

theorem rhs_eq_flat_bind (t : GameTree S Outcome) (muP : MixedProfile S) :
    (mixedProfileJoint (S := S) muP).bind
      (fun pi => t.evalDist (pureToBehavioral (S := S) pi)) =
    (pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)).bind
      (fun s => t.evalDist (flatToBehavioral s)) := by
  ext x
  simp only [PMF.bind_apply, tsum_fintype, pmfPureToFlat, PMF.bind_bind, PMF.pure_bind]
  refine Finset.sum_congr rfl ?_
  intro pi _
  have hflat :
      (flatProfileEquivPureProfile (S := S)).symm pi =
      (fun idx : FlatIdx S => pi idx.1 idx.2) := rfl
  have hprof :
      pureToBehavioral (S := S) pi =
      flatToBehavioral (S := S) (fun idx => pi idx.1 idx.2) := by
    funext p I
    rfl
  simp [hflat, hprof]

---
-- Main Theorem
---

/-- The behavioral strategy induced by a player-independent flat measure reproduces
the expected outcome: evaluating the whole tree under the behavioral strategy
equals the expectation under the flat product measure. -/
theorem mixed_to_behavioral_nplayer
    (t : GameTree S Outcome)
    (hpr : PerfectRecall t)
    (mu : PMF (FlatProfile S))
    (hind : PlayerIndep (S := S) mu) :
    t.evalDist (mixedToBehavioralRoot (S := S) (Outcome := Outcome)
      mu t) =
    mu.bind (fun s => t.evalFlat s) := by
  simpa using eval_subtree_correct (S := S) (Outcome := Outcome)
    t hpr mu hind t [] ⟨⟩ (SubtreeAt.refl t)

/-- **Kuhn's theorem.** For any game tree with perfect recall and any mixed strategy
profile, there exists a behavioral strategy profile that induces the same outcome
distribution. -/
theorem kuhn_mixed_to_behavioral
    (t : GameTree S Outcome)
    (hpr : PerfectRecall t)
    (muP : MixedProfile S) :
    ∃ sigma : BehavioralProfile S,
      t.evalDist sigma =
      (mixedProfileJoint (S := S) muP).bind
        (fun pi => t.evalDist
          (pureToBehavioral (S := S) pi)) := by
  let mu0 : PMF (FlatProfile S) :=
    pmfPureToFlat (S := S) (mixedProfileJoint (S := S) muP)
  refine ⟨mixedToBehavioralRoot (S := S) (Outcome := Outcome)
    mu0 t, ?_⟩
  calc
    t.evalDist (mixedToBehavioralRoot (S := S) (Outcome := Outcome)
      mu0 t)
      = mu0.bind (fun s => t.evalFlat s) := by
          exact mixed_to_behavioral_nplayer (S := S)
            (Outcome := Outcome) t hpr mu0
            (PlayerIndep_pmfPureToFlat (S := S) muP)
    _ = (mixedProfileJoint (S := S) muP).bind
          (fun pi => t.evalDist
            (pureToBehavioral (S := S) pi)) := by
        exact (rhs_eq_flat_bind (S := S)
          (Outcome := Outcome) t muP).symm

open GameTheory in
/-- Kuhn's theorem lifted to utility distributions (mixed → behavioral):
    For any EFG game with perfect recall, every mixed strategy profile has an
    equivalent behavioral profile that induces the same joint utility distribution. -/
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
