import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Constructions

import GameTheory.EFG
import GameTheory.PMFProduct

/-!
# Kuhn's Theorem — Behavioral ↔ Mixed Strategy Equivalence

Kuhn's theorem states that behavioral and mixed strategies are outcome-equivalent
in extensive-form games with perfect recall.

- **Behavioral→Mixed** (§5): The product PMF over independently sampled actions
  induces the same outcome. Requires `NoInfoSetRepeat` (no info set appears
  both at a decision node and in its subtrees), which follows from perfect recall.
- **Mixed→Behavioral** (§7): Requires perfect recall. The conditional behavioral
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

/-- Two flat profiles that agree on all infosets appearing in `t` produce
    the same evalDist when used as behavioral profiles. -/
theorem evalDist_pure_eq_of_agree (t : GameTree S Outcome)
    (s₁ s₂ : FlatProfile S)
    (h : ∀ {q} {J : S.Infoset q}, DecisionNodeIn J t → s₁ ⟨q, J⟩ = s₂ ⟨q, J⟩) :
    t.evalFlat s₁ = t.evalFlat s₂ := by
  simp only [GameTree.evalFlat]
  induction t with
  | terminal _ => rfl
  | chance _k _μ _hk next ih =>
    simp only [GameTree.evalDist]
    congr 1; funext b
    exact ih b (fun hdn => h (.in_chance _ _ _ _ b hdn))
  | decision I next ih =>
    simp only [GameTree.evalDist, flatToBehavioral]
    have hroot := h (DecisionNodeIn.root (I := I) next)
    simp only [hroot]
    congr 1; funext a
    exact ih a (fun hdn => h (.in_decision I next a hdn))

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
                  have h := PMF.tsum_coe μ
                  rwa [tsum_eq_sum (s := Finset.univ)
                    (fun x hx => absurd (Finset.mem_univ x) hx)] at h
          exact ENNReal.mul_inv_cancel hpR
            (ne_of_lt (lt_of_le_of_lt hpReach_le (by simp))))

-- ============================================================================
-- § 7b. Helper lemmas for mixed → behavioral
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
  have h := PMF.tsum_coe μ
  rwa [tsum_eq_sum (s := Finset.univ)
    (fun x hx => absurd (Finset.mem_univ x) hx)] at h

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
  μ.bind (fun s => PMF.pure (s ⟨p, I'⟩))

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
          simp only [μMarginal, PMF.bind_apply, PMF.pure_apply, mul_ite, mul_one, mul_zero]
          rw [tsum_fintype]; congr 1; funext s
          by_cases h : s ⟨p, I₀⟩ = a
          · rw [if_pos h, if_pos h.symm]
          · rw [if_neg h, if_neg (Ne.symm h)]
        rw [h_sum]
        exact ENNReal.mul_inv_cancel hp
          (ENNReal.ne_top_of_tsum_ne_top
            (PMF.tsum_coe (μMarginal I₀ μ) ▸ ENNReal.one_ne_top) a))

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
  ext x
  simp only [PMF.bind_apply, tsum_fintype]
  -- Push the marginal probability inside the inner sum
  simp_rw [Finset.mul_sum]
  -- Now the sums are strictly adjacent, so we can commute them
  rw [Finset.sum_comm]
  -- Re-associate the multiplication so it matches what we expect
  simp_rw [← mul_assoc]
  congr 1; funext s
  have h_single : (∑ a : S.Act I₀, μMarginal I₀ μ a * μCond I₀ a μ s * f s x) =
      μMarginal I₀ μ (s ⟨p, I₀⟩) * μCond I₀ (s ⟨p, I₀⟩) μ s * f s x := by
    apply Finset.sum_eq_single (s ⟨p, I₀⟩)
    · intro a _ hneq
      by_cases hp : μMarginal I₀ μ a = 0
      · simp [hp]
      · rw [μCond_apply I₀ a μ s hp, if_neg (Ne.symm hneq), mul_zero, zero_mul]
    · intro h_notin
      exact absurd (Finset.mem_univ (s ⟨p, I₀⟩)) h_notin
  rw [h_single]
  by_cases hp : μMarginal I₀ μ (s ⟨p, I₀⟩) = 0
  · have h_mu_s : μ s = 0 := by
      have h_sum : (∑ s_1 : FlatProfile S,
          if s_1 ⟨p, I₀⟩ = s ⟨p, I₀⟩ then (μ s_1 : ENNReal) else 0)
          = μMarginal I₀ μ (s ⟨p, I₀⟩) := by
        simp only [μMarginal, PMF.bind_apply, PMF.pure_apply, tsum_fintype,
          mul_ite, mul_one, mul_zero]
        grind only
      have h_le : (if s ⟨p, I₀⟩ = s ⟨p, I₀⟩ then (μ s : ENNReal) else 0) ≤
          ∑ s_1 : FlatProfile S, if s_1 ⟨p, I₀⟩ = s ⟨p, I₀⟩ then (μ s_1 : ENNReal) else 0 :=
        Finset.single_le_sum
          (f := fun s_1 => if s_1 ⟨p, I₀⟩ = s ⟨p, I₀⟩ then (μ s_1 : ENNReal) else 0)
          (fun _ _ => zero_le _)
          (Finset.mem_univ s)
      rw [h_sum, hp, if_pos rfl] at h_le
      exact le_antisymm h_le (zero_le _)
    simp [hp, h_mu_s]
  · rw [μCond_apply I₀ (s ⟨p, I₀⟩) μ s hp, if_pos rfl]
    have h_le_one : μMarginal I₀ μ (s ⟨p, I₀⟩) ≤ 1 := by
      calc μMarginal I₀ μ (s ⟨p, I₀⟩) ≤ ∑ a, μMarginal I₀ μ a :=
          Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ _)
        _ = 1 := by
          have h := PMF.tsum_coe (μMarginal I₀ μ)
          rwa [tsum_eq_sum (s := Finset.univ)
            (fun x hx => absurd (Finset.mem_univ x) hx)] at h
    have hp_top : μMarginal I₀ μ (s ⟨p, I₀⟩) ≠ ⊤ := ne_of_lt (lt_of_le_of_lt h_le_one (by simp))
    -- Algebraic cancellation: p_a * (μ s / p_a * f) = μ s * f
    rw [div_eq_mul_inv, mul_comm (μ s), ← mul_assoc]
    -- Algebraic cancellation: p_a * (μ s / p_a * f) = μ s * f
    -- Group the marginal probability with its inverse
    rw [mul_right_comm ((μMarginal I₀ μ) (s ⟨p, I₀⟩)) (μ s)]
    -- Now they are strictly adjacent, so the cancellation fires
    rw [ENNReal.mul_inv_cancel hp hp_top]
    -- Clean up the 1 and match the commutativity of the LHS
    rw [one_mul, mul_comm (μ s) ((f s) x)]


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

lemma ENNReal.div_div_div_cancel_right
    (X Y p_a : ENNReal) (hp0 : p_a ≠ 0) (hpt : p_a ≠ ⊤) :
    (X / p_a) / (Y / p_a) = X / Y := by
  simp only [div_eq_mul_inv, mul_assoc]
  have hp_inv_ne_top : p_a⁻¹ ≠ (⊤ : ENNReal) := by
    simpa [ENNReal.inv_ne_top] using hp0
  have hp_inv_ne_zero : p_a⁻¹ ≠ (0 : ENNReal) := by
    simpa [ENNReal.inv_ne_zero] using hpt
  have hinv : (Y * p_a⁻¹)⁻¹ = Y⁻¹ * (p_a⁻¹)⁻¹ := by
    simpa using
      (ENNReal.mul_inv (a := Y) (b := p_a⁻¹)
        (ha := Or.inr hp_inv_ne_top) (hb := Or.inr hp_inv_ne_zero))
  calc
    _   = X * p_a⁻¹ * (Y⁻¹ * (p_a⁻¹)⁻¹) := by
      simp [hinv]
      grind only
    _   = X * p_a⁻¹ * (Y⁻¹ * p_a) := by simp
    _   = X * (Y⁻¹ * (p_a⁻¹ * p_a)) := by
      simp [mul_assoc, mul_left_comm, mul_comm]
    _   = X * (Y⁻¹ * 1) := by
      simp [ENNReal.inv_mul_cancel hp0 hpt]
    _   = X / Y := by simp [div_eq_mul_inv]

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
    -- same pattern you used elsewhere
    exact ENNReal.ne_top_of_tsum_ne_top
      (PMF.tsum_coe (μMarginal I₀ μ) ▸ ENNReal.one_ne_top) a
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
  -- Now multiply by p_a and cancel p_a * (μ s / p_a) = μ s.
  -- Do it termwise inside the sum.
  have hterm :
      (p_a * (∑ s : FlatProfile S,
        if s ⟨p, I₀⟩ = a ∧ reachesFlat J s (next a) then (μ s / p_a) else 0))
        =
      (∑ s : FlatProfile S,
        if s ⟨p, I₀⟩ = a ∧ reachesFlat J s (next a) then (μ s : ENNReal) else 0) := by
    -- pull p_a into the sum and simplify
    simp only [div_eq_mul_inv, Finset.mul_sum, mul_ite, mul_zero]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : (s ⟨p, I₀⟩ = a ∧ reachesFlat J s (next a))
    · simp only [h, and_self, ↓reduceIte]
      -- p_a * (μ s * p_a⁻¹) = μ s * (p_a * p_a⁻¹) = μ s
      have : p_a * p_a⁻¹ = 1 := by
        -- ENNReal.mul_inv_cancel wants p_a≠0 and p_a≠⊤
        simpa [p_a] using (ENNReal.mul_inv_cancel (by simpa [p_a] using hpa) hpa_top)
      rw [mul_comm]
      rw [mul_assoc]
      rw [mul_comm] at this
      simp_all only [ne_eq, Finset.mem_univ, mul_one, p_a]
    · simp [h]
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
  simpa [hL] using (by
    simp_all only [ne_eq, p_a])


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
    exact ENNReal.ne_top_of_tsum_ne_top
      (PMF.tsum_coe (μMarginal I₀ μ) ▸ ENNReal.one_ne_top) a
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
  -- RHS:
  simp only  -- only to bring p_a into scope
  -- Direct termwise computation:
  -- p_a * (if reach∧sJ=b then μCond else 0)
  -- becomes (if sI0=a ∧ reach ∧ sJ=b then μ else 0).
  -- We do it as a sum_congr.
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hR : (reachesFlat J s (next a) ∧ s ⟨p, J⟩ = b)
  · have hr : reachesFlat J s (next a) := hR.1
    have hsb : s ⟨p, J⟩ = b := hR.2
    -- split on s(I₀)=a
    by_cases hsa : s ⟨p, I₀⟩ = a
    · -- then μCond = μ/p_a, and p_a * (μ/p_a) = μ
      simp only [hsa, hR, and_self, ↓reduceIte,
        μCond_apply (I₀ := I₀) (a := a) (μ := μ) (s := s) hpa, div_eq_mul_inv]
      have : p_a * p_a⁻¹ = 1 := by
        simpa [p_a] using (ENNReal.mul_inv_cancel (by simpa [p_a] using hpa) hpa_top)
      simp only [mul_comm]
      exact Eq.symm (ENNReal.mul_inv_cancel_left hpa hpa_top)
    · -- if s(I₀)≠a then μCond mass is 0, so RHS term is 0, and LHS indicator is false
      simp [hR, hsa, μCond_apply (I₀ := I₀) (a := a) (μ := μ) (s := s) hpa]
  · -- if reach∧sJ=b is false, RHS term is 0; LHS indicator also false
    simp only [hR, ↓reduceIte, ite_eq_right_iff, and_imp]
    intro a_2 a_3 a_4
    subst a_2 a_4
    simp_all only [ne_eq, Finset.mem_univ, and_self, not_true_eq_false, p_a]

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
    exact ENNReal.ne_top_of_tsum_ne_top
      (PMF.tsum_coe (μMarginal I₀ μ) ▸ ENNReal.one_ne_top) a
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
    have := ENNReal.div_div_div_cancel_right
      (X := (∑ s : FlatProfile S,
        if reachesFlat J s (next a) ∧ s ⟨p, J⟩ = b
        then (μCond I₀ a μ s : ENNReal) else 0))
      (Y := rR) (p_a := p_a) (hp0 := by simpa [p_a] using hpa) (hpt := hpa_top)
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
  simp only [PMF.ofFintype_apply, root_num_collapse, div_one,
    μMarginal, PMF.bind_apply, PMF.pure_apply, tsum_fintype]
  congr 1; funext s
  by_cases h : s ⟨p, I'⟩ = a
  · simp [h]
  · simp [h, Ne.symm h]

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
  | .terminal _, _, _, _, hr, _ => nomatch hr
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

/-- Two behavioral profiles agreeing on all infosets in `t` give the same `evalDist`. -/
theorem evalDist_eq_of_behavioral_agree (t : GameTree S Outcome)
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
    rw [h (.root next)]; congr 1; funext a
    exact ih a (fun hdn => h (.in_decision I next a hdn))

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
    have h_agree := evalDist_eq_of_behavioral_agree (next b)
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
      apply evalDist_eq_of_behavioral_agree
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

end EFG
