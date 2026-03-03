import GameTheory.ProtoZermelo
import Math.PMFProduct

/-!
# Kuhn's Theorem at the Protocol Level

Kuhn's theorem states that behavioral and mixed strategies are
outcome-equivalent in games with perfect recall.

## Key concepts

- **Mixed strategy**: `PMF (PureStrategy V A)` — a distribution over pure
  strategies. A mixed profile draws one pure strategy per player, then evaluates.
- **Behavioral strategy**: `V → PMF (Option A)` — independently randomizes at
  each view. Already defined in `SeqProto.lean`.
- **Perfect recall**: a player's view encodes their full history of past views
  and actions. Defined here as `Protocol.HasPerfectRecall`.
- **NoViewRepeat**: a player never sees the same view at two different rounds
  (along any play path). This is the Protocol analog of `NoInfoSetRepeat`
  in EFG, and follows from perfect recall.

## Main results

- `Protocol.kuhn_behavioral_to_mixed` — behavioral → mixed direction
- `Protocol.kuhn_mixed_to_behavioral` — mixed → behavioral direction
-/

namespace GameTheory
open Math.PMFProduct

variable {n : ℕ} {S V A Sig : Type}

-- ============================================================================
-- Mixed strategies and evaluation
-- ============================================================================

/-- A mixed strategy for one player: a distribution over pure strategies. -/
abbrev MixedStrategy (V A : Type) := PMF (PureStrategy V A)

/-- A mixed profile: one mixed strategy per player. -/
abbrev MixedProfile' (n : ℕ) (V A : Type) := Fin n → MixedStrategy V A

/-- Draw a joint pure profile from a mixed profile (independent per player). -/
noncomputable def mixedProfileJoint [Fintype (PureStrategy V A)]
    (μ : MixedProfile' n V A) : PMF (PureProfile n V A) :=
  pmfPi μ

/-- Evaluate the protocol under a mixed profile: draw a pure profile,
    then evaluate deterministically. -/
noncomputable def Protocol.evalMixedProfile [Fintype (PureStrategy V A)]
    (G : Protocol n S V A Sig)
    (μ : MixedProfile' n V A) : PMF S :=
  (mixedProfileJoint μ).bind G.eval

-- ============================================================================
-- Lift: pure → behavioral → mixed
-- ============================================================================

/-- Lift a pure strategy to a mixed strategy (point mass). -/
noncomputable def pureMixed (s : PureStrategy V A) : MixedStrategy V A :=
  PMF.pure s

/-- Lift a pure profile to a mixed profile. -/
noncomputable def pureToMixed (σ : PureProfile n V A) : MixedProfile' n V A :=
  fun i => pureMixed (σ i)

-- ============================================================================
-- Perfect recall
-- ============================================================================

/-- A protocol has perfect recall for player `i` if no two distinct rounds
    can produce the same view for that player (at any reachable states). -/
def Protocol.HasPerfectRecall (G : Protocol n S V A Sig) (i : Fin n) : Prop :=
  ∀ (j₁ j₂ : ℕ) (hj₁ : j₁ < G.rounds.length) (hj₂ : j₂ < G.rounds.length),
    j₁ ≠ j₂ →
    ∀ (s₁ s₂ : S) (sig₁ sig₂ : Fin n → Sig),
      G.rounds[j₁].view i s₁ (sig₁ i) = G.rounds[j₂].view i s₂ (sig₂ i) →
      False

/-- A protocol has perfect recall if it does for every player. -/
def Protocol.HasPerfectRecallAll (G : Protocol n S V A Sig) : Prop :=
  ∀ i, G.HasPerfectRecall i

/-- ViewSeparated implies perfect recall. -/
theorem Protocol.viewSeparated_hasPerfectRecall (G : Protocol n S V A Sig)
    (hVS : G.ViewSeparated) :
    G.HasPerfectRecallAll := by
  intro i j₁ j₂ hj₁ hj₂ hne s₁ s₂ sig₁ sig₂ hview
  exact absurd hview (hVS hj₁ hj₂ hne i s₁ s₂ sig₁ sig₂)

/-- No view repeats: the operational condition for Kuhn (behavioral → mixed). -/
def Protocol.NoViewRepeat (G : Protocol n S V A Sig) : Prop :=
  G.HasPerfectRecallAll

-- ============================================================================
-- Strong perfect recall (for Kuhn mixed → behavioral)
-- ============================================================================

/-- A consistent execution of a round list from initial state `s₀`:
    states evolve by applying the transition function at each round. -/
def ConsistentExec (rounds : List (Round n S V A Sig)) (s₀ : S)
    (states : ℕ → S) (acts : ℕ → (Fin n → Option A)) : Prop :=
  states 0 = s₀ ∧
  ∀ (j : ℕ) (hj : j < rounds.length),
    states (j + 1) = rounds[j].transition (states j) (acts j)

/-- Strong perfect recall for a round list: the view at round `k` determines
    the full player-`i` history (views and actions at all earlier rounds).

    Quantifies over all consistent executions (state-sequences related by
    transition) from a given initial state. Signals at each round are
    unconstrained — the condition holds for *all* signal realizations.

    This mirrors the EFG `PerfectRecall` condition (`playerHistory` equality)
    but in the Protocol setting. -/
def RoundsStrongRecall (rounds : List (Round n S V A Sig)) (s₀ : S)
    (i : Fin n) : Prop :=
  ∀ (k : ℕ) (hk : k < rounds.length)
    (st₁ st₂ : ℕ → S) (sig₁ sig₂ : ℕ → (Fin n → Sig))
    (acts₁ acts₂ : ℕ → (Fin n → Option A)),
    ConsistentExec rounds s₀ st₁ acts₁ →
    ConsistentExec rounds s₀ st₂ acts₂ →
    rounds[k].view i (st₁ k) (sig₁ k i) =
      rounds[k].view i (st₂ k) (sig₂ k i) →
    ∀ (j : ℕ), j < k → (hjL : j < rounds.length) →
      rounds[j].view i (st₁ j) (sig₁ j i) =
        rounds[j].view i (st₂ j) (sig₂ j i) ∧
      acts₁ j i = acts₂ j i

/-- Strong perfect recall for a protocol: views encode full player-`i` history
    along any consistent execution from the protocol's initial state.

    Includes `HasPerfectRecall` (no view repeats across rounds) as a conjunct. -/
def Protocol.StrongPerfectRecall (G : Protocol n S V A Sig) (i : Fin n) : Prop :=
  G.HasPerfectRecall i ∧ RoundsStrongRecall G.rounds G.init i

/-- Strong perfect recall for all players. -/
def Protocol.StrongPerfectRecallAll (G : Protocol n S V A Sig) : Prop :=
  ∀ i, G.StrongPerfectRecall i

/-- Strong perfect recall implies no view repeats. -/
theorem Protocol.strongPerfectRecall_noViewRepeat (G : Protocol n S V A Sig)
    (h : G.StrongPerfectRecallAll) : G.NoViewRepeat :=
  fun i => (h i).1

-- ============================================================================
-- Behavioral → Mixed lift
-- ============================================================================

open Classical in
/-- Lift a behavioral strategy to a mixed strategy via product distribution. -/
noncomputable def behavioralToMixed [Fintype V]
    [Fintype (Option A)]
    (σ : BehavioralStrategy V A) : MixedStrategy V A :=
  pmfPi σ

open Classical in
/-- Lift a behavioral profile to a mixed profile. -/
noncomputable def behavioralProfileToMixed [Fintype V]
    [Fintype (Option A)]
    (σ : BehavioralProfile n V A) : MixedProfile' n V A :=
  fun i => behavioralToMixed (σ i)

-- ============================================================================
-- evalRoundsMixed decomposition
-- ============================================================================

private theorem foldl_roundsMixed_eq_bind [Fintype (Option A)]
    (rounds : List (Round n S V A Sig))
    (σ : BehavioralProfile n V A) (μ : PMF S) :
    List.foldl (fun dist r => dist.bind (r.evalMixed σ)) μ rounds
    = μ.bind (evalRoundsMixed rounds σ) := by
  induction rounds generalizing μ with
  | nil => exact (PMF.bind_pure μ).symm
  | cons r rest ih =>
    simp only [List.foldl]
    rw [ih]
    rw [PMF.bind_bind]
    congr 1; funext s
    simp only [evalRoundsMixed, List.foldl, PMF.pure_bind]
    exact (ih (r.evalMixed σ s)).symm

@[simp]
theorem evalRoundsMixed_nil [Fintype (Option A)]
    (σ : BehavioralProfile n V A) (s : S) :
    evalRoundsMixed ([] : List (Round n S V A Sig)) σ s = PMF.pure s := rfl

theorem evalRoundsMixed_cons [Fintype (Option A)]
    (r : Round n S V A Sig) (rest : List (Round n S V A Sig))
    (σ : BehavioralProfile n V A) (s : S) :
    evalRoundsMixed (r :: rest) σ s = (r.evalMixed σ s).bind (evalRoundsMixed rest σ) := by
  simp only [evalRoundsMixed, List.foldl]
  rw [foldl_roundsMixed_eq_bind]
  exact congrArg (PMF.bind · (evalRoundsMixed rest σ)) (PMF.pure_bind s (r.evalMixed σ))

-- ============================================================================
-- View separation for round lists
-- ============================================================================

/-- Views at different positions in the round list are distinguishable. -/
def RoundsViewSep (rounds : List (Round n S V A Sig)) : Prop :=
  ∀ ⦃k₁ k₂ : ℕ⦄ (hk₁ : k₁ < rounds.length) (hk₂ : k₂ < rounds.length),
    k₁ ≠ k₂ →
    ∀ (i : Fin n) (s₁ s₂ : S) (sig₁ sig₂ : Fin n → Sig),
      rounds[k₁].view i s₁ (sig₁ i) ≠ rounds[k₂].view i s₂ (sig₂ i)

theorem RoundsViewSep_tail {r : Round n S V A Sig} {rest : List (Round n S V A Sig)}
    (h : RoundsViewSep (r :: rest)) : RoundsViewSep rest := by
  intro k₁ k₂ hk₁ hk₂ hne i s₁ s₂ sig₁ sig₂
  exact h (Nat.succ_lt_succ hk₁) (Nat.succ_lt_succ hk₂)
    (by omega) i s₁ s₂ sig₁ sig₂

theorem RoundsViewSep_head_vs_tail {r : Round n S V A Sig} {rest : List (Round n S V A Sig)}
    (h : RoundsViewSep (r :: rest))
    {k : ℕ} (hk : k < rest.length)
    (i : Fin n) (s₁ s₂ : S) (sig₁ sig₂ : Fin n → Sig) :
    r.view i s₁ (sig₁ i) ≠ rest[k].view i s₂ (sig₂ i) := by
  have := h (k₁ := 0) (k₂ := k + 1) (by simp) (by simpa using Nat.succ_lt_succ hk)
    (by omega) i s₁ s₂ sig₁ sig₂
  simpa using this

theorem RoundsViewSep_head_vs_mem {r : Round n S V A Sig} {rest : List (Round n S V A Sig)}
    (h : RoundsViewSep (r :: rest))
    {r' : Round n S V A Sig} (hr' : r' ∈ rest)
    (i : Fin n) (s₁ s₂ : S) (sig₁ sig₂ : Fin n → Sig) :
    r.view i s₁ (sig₁ i) ≠ r'.view i s₂ (sig₂ i) := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr'
  exact RoundsViewSep_head_vs_tail h hk i s₁ s₂ sig₁ sig₂

-- ============================================================================
-- Core lemma: pushforward of product through coordinate-wise function
-- ============================================================================

open Classical in
/-- The pushforward of a product PMF through a coordinate-wise function
    is the product of pushforwards. -/
theorem pmfPi_push_coordwise {ι : Type} [Fintype ι]
    {A : ι → Type} {B : ι → Type} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (μ : ∀ i, PMF (A i)) (g : ∀ i, A i → B i) :
    pushforward (pmfPi μ) (fun f => fun i => g i (f i))
    = pmfPi (fun i => pushforward (μ i) (g i)) := by
  classical
  ext b
  simp only [pushforward, PMF.bind_apply, PMF.pure_apply, pmfPi_apply, tsum_fintype]
  trans (∑ a : ∀ i, A i, ∏ i, ((μ i) (a i) * if b i = g i (a i) then 1 else 0))
  · apply Finset.sum_congr rfl; intro f _
    by_cases h : b = fun i => g i (f i)
    · subst h; simp
    · have ⟨i₀, hi₀⟩ : ∃ i₀, b i₀ ≠ g i₀ (f i₀) := by
        by_contra hall; push_neg at hall; exact h (funext hall)
      simp only [if_neg h, mul_zero]
      exact (Finset.prod_eq_zero (Finset.mem_univ i₀) (by rw [if_neg hi₀]; ring)).symm
  · exact (Fintype.prod_sum (fun i ai => (μ i) ai * if b i = g i ai then 1 else 0)).symm

-- ============================================================================
-- Core: single-round factoring
-- ============================================================================

set_option linter.unusedDecidableInType false in
open Classical in
/-- At a single round, behavioral evaluation = mixed evaluation. -/
theorem Round.evalMixed_eq_bind_eval [Fintype V]
    [Fintype (Option A)]
    [Fintype (PureStrategy V A)]
    (r : Round n S V A Sig) (σ : BehavioralProfile n V A) (s : S) :
    r.evalMixed σ s =
    (pmfPi (fun i => pmfPi (σ i))).bind (fun f => r.eval f s) := by
  simp only [Round.evalMixed, Round.eval]
  -- RHS: rewrite map as pushforward (bind + pure)
  -- Then commute product bind with signal bind (Fubini)
  have rhs_eq : (pmfPi fun i => pmfPi (σ i)).bind (fun f =>
      (r.signal s).map (fun sig => r.transition s (fun i => f i (r.view i s (sig i))))) =
    (r.signal s).bind (fun sig => (pmfPi fun i => pmfPi (σ i)).bind (fun f =>
      PMF.pure (r.transition s (fun i => f i (r.view i s (sig i)))))) := by
    change (pmfPi fun i => pmfPi (σ i)).bind (fun f =>
        (r.signal s).bind (fun sig =>
          PMF.pure (r.transition s (fun i => f i (r.view i s (sig i)))))) = _
    exact PMF.bind_comm _ _ _
  rw [rhs_eq]
  congr 1; funext sig
  -- For fixed sig, reduce to pushforward equality
  -- LHS = pushforward (pmfPi (fun i => σ i (v i))) T
  -- RHS = pushforward (pmfPi μ) (T ∘ proj) = pushforward (pushforward (pmfPi μ) proj) T
  -- where T acts = transition s acts, proj f i = f i (v i), μ i = pmfPi (σ i)
  show (pmfPi fun i => σ i (r.view i s (sig i))).map
      (fun acts => r.transition s acts)
    = (pmfPi fun i => pmfPi (σ i)).bind
      (fun f => PMF.pure (r.transition s (fun i => f i (r.view i s (sig i)))))
  -- Rewrite both as pushforward
  change pushforward (pmfPi fun i => σ i (r.view i s (sig i)))
      (fun acts => r.transition s acts)
    = pushforward (pmfPi fun i => pmfPi (σ i))
      (fun f => r.transition s (fun i => f i (r.view i s (sig i))))
  -- RHS = pushforward (pushforward ... proj) T by pushforward_comp
  rw [show (fun f : Fin n → V → Option A =>
        r.transition s (fun i => f i (r.view i s (sig i)))) =
      (fun acts => r.transition s acts) ∘ (fun f i => f i (r.view i s (sig i)))
    from rfl]
  rw [← Math.PMFProduct.pushforward_comp]
  -- Now need: pushforward (pmfPi μ) proj = pmfPi (fun i => σ i (v i))
  congr 1
  have : pushforward (pmfPi fun i => pmfPi (σ i)) (fun f i => f i (r.view i s (sig i)))
      = pmfPi (fun i => pushforward (pmfPi (σ i)) (fun fi => fi (r.view i s (sig i)))) :=
    pmfPi_push_coordwise (fun i => pmfPi (σ i))
      (fun (i : Fin n) (fi : V → Option A) => fi (r.view i s (sig i)))
  rw [this]; congr 1; funext i
  exact (pmfPi_push_coord (σ i) (r.view i s (sig i))).symm

-- ============================================================================
-- Core: continuation ignores current-round views
-- ============================================================================

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open Classical in
/-- If views at round `r` are disjoint from views at all rounds in `rest`,
    then `evalRounds rest` is invariant under changing the pure profile at
    the current round's views. -/
theorem evalRounds_ignores_view
    [Fintype V] [Fintype (Option A)]
    (r : Round n S V A Sig) (rest : List (Round n S V A Sig))
    (hsep : RoundsViewSep (r :: rest))
    (i : Fin n) (s : S) (sig : Fin n → Sig)
    (f : PureProfile n V A) (a : Option A) (s' : S) :
    evalRounds rest (Function.update f i
      (Function.update (f i) (r.view i s (sig i)) a)) s' =
    evalRounds rest f s' := by
  apply evalRounds_congr
  intro r' hr' j s₁ sig₁
  by_cases hji : j = i
  · subst hji
    simp only [Function.update_self]
    have hview := RoundsViewSep_head_vs_mem hsep hr' j s s₁ sig sig₁
    simp [Function.update_of_ne (Ne.symm hview)]
  · simp [Function.update_of_ne hji]

-- ============================================================================
-- Bridge: NoViewRepeat → RoundsViewSep
-- ============================================================================

theorem Protocol.noViewRepeat_roundsViewSep
    (G : Protocol n S V A Sig) (h : G.NoViewRepeat) :
    RoundsViewSep G.rounds := by
  intro k₁ k₂ hk₁ hk₂ hne i s₁ s₂ sig₁ sig₂ hview
  exact h i k₁ k₂ hk₁ hk₂ hne s₁ s₂ sig₁ sig₂ hview

-- ============================================================================
-- Flattening isomorphism: nested pmfPi ↔ flat pmfPi
-- ============================================================================

open Classical in
/-- Nested product equals the flat product mapped through curry. -/
theorem pmfPi_nested_eq_curry_flat
    [Fintype V]
    [Fintype (Option A)]
    (σ : Fin n → V → PMF (Option A)) :
    pmfPi (fun i => pmfPi (σ i)) =
    PMF.map Function.curry (pmfPi (fun p : Fin n × V => σ p.1 p.2)) := by
  ext f
  simp only [PMF.map_apply, pmfPi_apply]
  rw [tsum_fintype]
  -- Rewrite condition: f = curry b ↔ uncurry f = b
  simp_rw [show ∀ b : Fin n × V → Option A,
    (f = Function.curry b) = (Function.uncurry f = b) from fun b =>
      propext ⟨fun h => funext fun p => by subst h; rfl,
               fun h => by rw [← h, Function.curry_uncurry]⟩]
  rw [Fintype.sum_ite_eq]
  -- Now: ∏ x, ∏ v, σ x v (f x v) = ∏ p, σ p.1 p.2 (uncurry f p)
  simp only [Function.uncurry]
  exact (Fintype.prod_prod_type' (fun i v => (σ i v) (f i v))).symm

-- ============================================================================
-- Factoring lemma: independent coordinates under product measure
-- ============================================================================

set_option linter.unusedFintypeInType false in
open Classical in
/-- Under view separation, same draw = independent draws (via flat product). -/
theorem independent_factor
    [Fintype V] [Fintype S]
    [Fintype (Option A)]
    [Fintype (PureStrategy V A)]
    (r : Round n S V A Sig) (rest : List (Round n S V A Sig))
    (σ : BehavioralProfile n V A) (s : S)
    (hsep : RoundsViewSep (r :: rest)) :
    (pmfPi fun i => pmfPi (σ i)).bind (fun f =>
      (r.eval f s).bind (fun s' =>
        (pmfPi fun i => pmfPi (σ i)).bind (fun g =>
          evalRounds rest g s'))) =
    (pmfPi fun i => pmfPi (σ i)).bind (fun f =>
      (r.eval f s).bind (evalRounds rest f)) := by
  -- Flatten nested product to flat product over Fin n × V
  let flatσ : Fin n × V → PMF (Option A) := fun p => σ p.1 p.2
  have hflat : pmfPi (fun i => pmfPi (σ i)) =
      PMF.map Function.curry (pmfPi flatσ) := pmfPi_nested_eq_curry_flat σ
  rw [hflat]; simp only [PMF.bind_map]
  -- Apply pmfPi_bind_indep.symm on the flat product
  let J : Finset (Fin n × V) := Finset.univ.filter (fun p =>
    ∃ sig₀ : Sig, p.2 = r.view p.1 s sig₀)
  -- Helper: curry commutes with update at (i,v)
  have curry_update : ∀ (g : Fin n × V → Option A) (i : Fin n) (v : V) (a : Option A),
      Function.curry (Function.update g (i, v) a) =
        Function.update (Function.curry g) i
          (Function.update (Function.curry g i) v a) := by
    intro g i v a; ext j w
    simp only [Function.curry, Function.update]
    by_cases hjw : (j, w) = (i, v)
    · simp [(Prod.mk.inj hjw).1, (Prod.mk.inj hjw).2]
    · simp only [hjw, ↓reduceDIte]
      by_cases hj : j = i
      · subst hj
        have hw : w ≠ v := fun hw => hjw (by rw [hw])
        simp [hw]
      · simp [hj]
  exact (pmfPi_bind_indep flatσ
    (fun g => r.eval (Function.curry g) s)
    (fun s' g => evalRounds rest (Function.curry g) s')
    J
    -- hf: r.eval (curry g) s ignores flat coordinates ∉ J
    (fun ⟨i, v⟩ hJ => by
      intro g a
      simp only [Round.eval]
      congr 1; funext sig; congr 1; funext j
      simp only [Function.curry, Function.update_apply]
      rw [if_neg]
      intro heq
      have hji := (Prod.mk.inj heq).1; subst hji
      exact hJ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨sig j, (Prod.mk.inj heq).2.symm⟩⟩))
    -- hg: evalRounds rest (curry ·) s' ignores flat coordinates ∈ J
    (fun ⟨i, v⟩ hJ s' => by
      intro g a
      obtain ⟨sig₀, hv⟩ := (Finset.mem_filter.mp hJ).2
      dsimp only
      apply evalRounds_congr
      intro r' hr' j s₁ sig₁
      simp only [Function.curry, Function.update_apply]
      rw [if_neg]
      intro heq
      have hji := (Prod.mk.inj heq).1
      have hvw := (Prod.mk.inj heq).2; subst hji
      have hv' : v = r.view j s sig₀ := hv
      exact absurd (hv'.symm.trans hvw.symm)
        (show r.view j s sig₀ ≠ r'.view j s₁ (sig₁ j) from
          RoundsViewSep_head_vs_mem hsep hr' j s s₁ (fun _ => sig₀) sig₁))).symm

-- ============================================================================
-- Kuhn's theorem: behavioral → mixed
-- ============================================================================

set_option linter.unusedFintypeInType false in
open Classical in
/-- **Kuhn (Behavioral → Mixed)**: Under perfect recall, a behavioral profile
    and its corresponding mixed profile produce the same outcome distribution. -/
theorem Protocol.kuhn_behavioral_to_mixed
    [Fintype V] [Fintype S]
    [Fintype (Option A)]
    [Fintype (PureStrategy V A)]
    (G : Protocol n S V A Sig)
    (σ : BehavioralProfile n V A)
    (hNVR : G.NoViewRepeat) :
    G.evalMixed σ = G.evalMixedProfile (behavioralProfileToMixed σ) := by
  simp only [Protocol.evalMixed, Protocol.evalMixedProfile, mixedProfileJoint]
  suffices h : ∀ (rounds : List (Round n S V A Sig)) (s : S),
      RoundsViewSep rounds →
      evalRoundsMixed rounds σ s =
        (pmfPi fun i => pmfPi (σ i)).bind (fun f => evalRounds rounds f s) from
    h G.rounds G.init (G.noViewRepeat_roundsViewSep hNVR)
  intro rounds
  induction rounds with
  | nil =>
    intro s _
    simp only [evalRoundsMixed_nil, evalRounds_nil]
    ext x; simp
  | cons r rest ih =>
    intro s hsep
    rw [evalRoundsMixed_cons]
    simp_rw [evalRounds_cons]
    rw [Round.evalMixed_eq_bind_eval, PMF.bind_bind]
    -- LHS: Σ.bind (fun f => (r.eval f s).bind (evalRoundsMixed rest σ))
    -- RHS: Σ.bind (fun f => (r.eval f s).bind (evalRounds rest f))
    -- Use IH on continuation: replace evalRoundsMixed rest σ with pmfPi-based form
    have ih_sub : (fun a => (r.eval a s).bind (evalRoundsMixed rest σ)) =
        (fun a => (r.eval a s).bind (fun s' =>
          (pmfPi fun i => pmfPi (σ i)).bind (fun g => evalRounds rest g s'))) := by
      funext a; congr 1; funext s'; exact ih s' (RoundsViewSep_tail hsep)
    rw [ih_sub]
    -- Now use independent_factor
    exact independent_factor r rest σ s hsep

-- ============================================================================
-- Helpers for Kuhn mixed → behavioral
-- ============================================================================

open Classical in
/-- Conditional mixed strategy: condition μ on `f(v) = a`.
    Falls back to μ itself when the event has zero mass. -/
noncomputable def condMixed [Fintype (PureStrategy V A)]
    (μ : MixedStrategy V A) (v : V) (a : Option A) :
    MixedStrategy V A :=
  if h : pmfMass (μ := μ) (fun f => f v = a) ≠ 0 then
    pmfCond (μ := μ) (fun f => f v = a) h
  else μ

/-- Iterated conditioning: fold `condMixed` over a list of (view, action) pairs. -/
noncomputable def iterCondMixed [Fintype (PureStrategy V A)]
    (μ : MixedStrategy V A) : List (V × Option A) → MixedStrategy V A
  | [] => μ
  | (v, a) :: rest => iterCondMixed (condMixed μ v a) rest

@[simp]
theorem iterCondMixed_nil [Fintype (PureStrategy V A)]
    (μ : MixedStrategy V A) : iterCondMixed μ [] = μ := rfl

theorem iterCondMixed_cons [Fintype (PureStrategy V A)]
    (μ : MixedStrategy V A) (v : V) (a : Option A) (hist : List (V × Option A)) :
    iterCondMixed μ ((v, a) :: hist) = iterCondMixed (condMixed μ v a) hist := rfl

set_option linter.unusedFintypeInType false in
open Classical in
/-- Per-player law of total probability: drawing the marginal action then conditioning
    recovers the original distribution. -/
private theorem pushforward_bind_condMixed
    [Fintype (Option A)] [Fintype (PureStrategy V A)]
    (μ : MixedStrategy V A) (v : V) :
    (pushforward μ (· v)).bind (condMixed μ v) = μ := by
  -- Helper: push(a) = pmfMass μ {g | g v = a}
  have hpush_eq : ∀ a, (pushforward μ (· v)) a = pmfMass (μ := μ) (fun g => g v = a) := by
    intro a
    simp only [pushforward, PMF.bind_apply, PMF.pure_apply, tsum_fintype,
      pmfMass, pmfMask, mul_ite, mul_one, mul_zero]
    apply Finset.sum_congr rfl; intro g _
    by_cases hg : a = g v <;> by_cases hg' : g v = a <;> simp_all
  -- Helper: mass ≠ ⊤
  have hmass_ne_top : ∀ a, pmfMass (μ := μ) (fun g => g v = a) ≠ ⊤ := by
    intro a; apply ne_of_lt
    calc pmfMass (μ := μ) (fun g => g v = a)
        ≤ ∑ x : PureStrategy V A, μ x :=
          Finset.sum_le_sum (fun g _ => by simp only [pmfMask]; split_ifs <;> simp)
      _ = 1 := by simpa [tsum_fintype] using PMF.tsum_coe μ
      _ < ⊤ := ENNReal.one_lt_top
  ext f
  simp only [PMF.bind_apply, tsum_fintype]
  -- Only a = f v contributes
  rw [Finset.sum_eq_single (f v)
    (fun a _ hne => by
      rw [hpush_eq]
      by_cases hmass : pmfMass (μ := μ) (fun g => g v = a) ≠ 0
      · simp only [condMixed, dif_pos hmass, pmfCond_apply, pmfMask,
          show ¬(f v = a) from Ne.symm hne, ite_false]
        simp
      · rw [not_not.mp hmass, zero_mul])
    (fun h => absurd (Finset.mem_univ _) h)]
  -- push(f v) * condMixed(f v)(f) = μ(f)
  rw [hpush_eq]
  by_cases hmass : pmfMass (μ := μ) (fun g => g v = f v) = 0
  · -- mass = 0: μ f = 0 too
    have hμf : μ f = 0 := le_antisymm
      (calc μ f = pmfMask (μ := μ) (fun g => g v = f v) f := by simp [pmfMask]
        _ ≤ ∑ x, pmfMask (μ := μ) (fun g => g v = f v) x :=
            Finset.single_le_sum (fun x _ => by simp only [pmfMask]; split_ifs <;> simp)
              (Finset.mem_univ f)
        _ = _ := hmass) bot_le
    rw [hmass, zero_mul, hμf]
  · -- mass > 0: cancel mass with inverse
    simp only [condMixed, dif_pos hmass, pmfCond_apply, pmfMask, ite_true, div_eq_mul_inv]
    rw [mul_comm (μ f) _, ← mul_assoc, ENNReal.mul_inv_cancel hmass (hmass_ne_top _), one_mul]

set_option linter.unusedFintypeInType false in
open Classical in
/-- **Decompose a product-measure bind by "current views".**
    Drawing from `pmfPi μ` and applying `g` is the same as:
    1. Draw current actions `acts_i` from the marginal at `v i`
    2. Draw a fresh profile from the product of conditionals `condMixed`
    3. Apply `g` to the conditionally drawn profile.

    This combines the law of total probability per player with
    product-measure independence (conditional product = product of
    conditionals). -/
theorem pmfPi_bind_decompose_views
    [Fintype V] [Fintype (Option A)] [Fintype (PureStrategy V A)]
    (μ : MixedProfile' n V A) (v : Fin n → V)
    (g : PureProfile n V A → PMF S) :
    (pmfPi μ).bind g
    = (pmfPi (fun i => pushforward (μ i) (· (v i)))).bind (fun acts =>
        (pmfPi (fun i => condMixed (μ i) (v i) (acts i))).bind g) := by
  -- Key per-player fact from pushforward_bind_condMixed
  have hplayer : ∀ i f_i,
      ∑ a : Option A, (pushforward (μ i) (· (v i))) a * (condMixed (μ i) (v i) a) f_i
      = (μ i) f_i := by
    intro i f_i
    have h := pushforward_bind_condMixed (μ i) (v i)
    have := PMF.ext_iff.mp h f_i
    simp only [PMF.bind_apply, tsum_fintype] at this
    exact this
  ext y
  simp only [PMF.bind_apply, tsum_fintype, pmfPi_apply]
  -- LHS: Σ_f (∏_i μ_i(f_i)) * g(f)(y)
  -- RHS: Σ_acts (∏_i push_i(acts_i)) * (Σ_f (∏_i cond_i(acts_i)(f_i)) * g(f)(y))
  -- Transform RHS to match LHS
  symm
  -- Step 1: distribute product into inner sum
  simp_rw [Finset.mul_sum]
  -- Step 2: reassociate
  simp_rw [← mul_assoc]
  -- Step 3: combine products
  simp_rw [← Finset.prod_mul_distrib]
  -- Step 4: swap sums
  rw [Finset.sum_comm]
  -- Step 5: factor out g(f)(y) and use Fubini
  simp_rw [← Finset.sum_mul]
  congr 1; funext f
  congr 1
  -- Goal: ∑ acts, ∏ i, push(acts_i) * cond(acts_i)(f_i) = ∏ i, μ_i(f_i)
  rw [(Fintype.prod_sum (fun i a => (pushforward (μ i) (· (v i))) a *
    (condMixed (μ i) (v i) a) (f i))).symm]
  congr 1; funext i
  exact hplayer i (f i)

open Classical in
/-- Under condMixed with nonzero mass, the conditioned coordinate is fixed. -/
private theorem condMixed_coord [Fintype (PureStrategy V A)]
    (μ : MixedStrategy V A) (v : V) (a : Option A) (f : PureStrategy V A)
    (hmass : pmfMass (μ := μ) (fun g => g v = a) ≠ 0)
    (hf : condMixed μ v a f ≠ 0) : f v = a := by
  simp only [condMixed, dif_pos hmass, pmfCond_apply, pmfMask] at hf
  by_contra hne; simp [hne] at hf

open Classical in
/-- The product push(a) * condMixed(a)(f) is nonzero only when f v = a. -/
private theorem push_mul_condMixed_eq_zero [Fintype (PureStrategy V A)]
    (μ : MixedStrategy V A) (v : V) (a : Option A) (f : PureStrategy V A)
    (hne : f v ≠ a) :
    (pushforward μ (· v)) a * (condMixed μ v a) f = 0 := by
  by_cases hmass : pmfMass (μ := μ) (fun g => g v = a) ≠ 0
  · have : (condMixed μ v a) f = 0 := by
      simp only [condMixed, dif_pos hmass, pmfCond_apply, pmfMask, hne, ite_false]
      exact ENNReal.zero_div
    rw [this, mul_zero]
  · rw [not_not] at hmass
    have : (pushforward μ (· v)) a = 0 := by
      simp only [pushforward, PMF.bind_apply, PMF.pure_apply, tsum_fintype,
        pmfMass, pmfMask, mul_ite, mul_one, mul_zero] at hmass ⊢
      convert hmass using 1
      congr 1; ext g
      congr 1; ext; simp only [eq_comm (a := a)]
    rw [this, zero_mul]

/-- Strong recall for the tail of a round list, at a successor state. -/
theorem RoundsStrongRecall_tail (r : Round n S V A Sig) (rest : List (Round n S V A Sig))
    (s₀ : S) (acts₀ : Fin n → Option A) (i : Fin n)
    (h : RoundsStrongRecall (r :: rest) s₀ i) :
    RoundsStrongRecall rest (r.transition s₀ acts₀) i := by
  intro k hk st₁ st₂ sig₁ sig₂ a₁ a₂ hce₁ hce₂ hview j hj hjL
  -- Extend consistent executions of `rest` to consistent executions of `r :: rest`
  -- by prepending s₀ and acts₀
  let st₁' : ℕ → S := fun m => match m with | 0 => s₀ | m + 1 => st₁ m
  let st₂' : ℕ → S := fun m => match m with | 0 => s₀ | m + 1 => st₂ m
  let a₁' : ℕ → (Fin n → Option A) := fun m => match m with | 0 => acts₀ | m + 1 => a₁ m
  let a₂' : ℕ → (Fin n → Option A) := fun m => match m with | 0 => acts₀ | m + 1 => a₂ m
  let sig₁' : ℕ → (Fin n → Sig) := fun m => match m with | 0 => sig₁ 0 | m + 1 => sig₁ m
  let sig₂' : ℕ → (Fin n → Sig) := fun m => match m with | 0 => sig₂ 0 | m + 1 => sig₂ m
  have hce₁' : ConsistentExec (r :: rest) s₀ st₁' a₁' := by
    constructor
    · rfl
    · intro m hm
      match m with
      | 0 => simp only [st₁', a₁']; simpa using hce₁.1
      | m + 1 =>
        simp only [st₁', a₁', List.getElem_cons_succ]
        exact hce₁.2 m (by simpa using hm)
  have hce₂' : ConsistentExec (r :: rest) s₀ st₂' a₂' := by
    constructor
    · rfl
    · intro m hm
      match m with
      | 0 => simp only [st₂', a₂']; simpa using hce₂.1
      | m + 1 =>
        simp only [st₂', a₂', List.getElem_cons_succ]
        exact hce₂.2 m (by simpa using hm)
  -- Apply h at position k+1 in r :: rest
  have hkL : k + 1 < (r :: rest).length := by simp; omega
  have hjL' : j + 1 < (r :: rest).length := by simp; omega
  have hview' : ((r :: rest)[k + 1]'hkL).view i (st₁' (k + 1)) (sig₁' (k + 1) i) =
      ((r :: rest)[k + 1]'hkL).view i (st₂' (k + 1)) (sig₂' (k + 1) i) := by
    simp only [List.getElem_cons_succ, st₁', st₂', sig₁', sig₂']
    exact hview
  have result := h (k + 1) hkL st₁' st₂' sig₁' sig₂'
    a₁' a₂' hce₁' hce₂' hview' (j + 1) (by omega) hjL'
  simp only [List.getElem_cons_succ, st₁', st₂', sig₁', sig₂', a₁', a₂'] at result
  exact result

open Classical in
/-- Behavioral evaluation depends only on the behavioral strategy at views
    actually appearing in the round list. -/
theorem evalRoundsMixed_congr [Fintype (Option A)]
    (rounds : List (Round n S V A Sig))
    (σ₁ σ₂ : BehavioralProfile n V A)
    (h : ∀ r ∈ rounds, ∀ (i : Fin n) (s : S) (sig : Fin n → Sig),
      σ₁ i (r.view i s (sig i)) = σ₂ i (r.view i s (sig i)))
    (s : S) :
    evalRoundsMixed rounds σ₁ s = evalRoundsMixed rounds σ₂ s := by
  induction rounds generalizing s with
  | nil => rfl
  | cons r rest ih =>
    rw [evalRoundsMixed_cons, evalRoundsMixed_cons]
    have heval : r.evalMixed σ₁ s = r.evalMixed σ₂ s := by
      simp only [Round.evalMixed]
      congr 1; funext sig; congr 1; congr 1; funext i
      exact h r (.head rest) i s sig
    rw [heval]
    congr 1; funext s'
    exact ih (fun r' hr' => h r' (.tail r hr')) s'

open Classical in
/-- If σ₁ and σ₂ agree at head-round views from s, and their rest evaluations
    agree at all successor states, then the full evaluation agrees. -/
private theorem evalRoundsMixed_congr_at [Fintype (Option A)]
    (r : Round n S V A Sig) (rest : List (Round n S V A Sig))
    (σ₁ σ₂ : BehavioralProfile n V A) (s : S)
    (hhead : ∀ (i : Fin n) (sig : Fin n → Sig),
      σ₁ i (r.view i s (sig i)) = σ₂ i (r.view i s (sig i)))
    (hrest : ∀ (acts : Fin n → Option A),
      evalRoundsMixed rest σ₁ (r.transition s acts) =
        evalRoundsMixed rest σ₂ (r.transition s acts)) :
    evalRoundsMixed (r :: rest) σ₁ s = evalRoundsMixed (r :: rest) σ₂ s := by
  rw [evalRoundsMixed_cons, evalRoundsMixed_cons]
  have heval : r.evalMixed σ₁ s = r.evalMixed σ₂ s := by
    simp only [Round.evalMixed]
    congr 1; funext sig; congr 1; congr 1; funext i; exact hhead i sig
  rw [heval]
  -- Decompose: (signal.bind (pmfPi.map transition)).bind f
  -- = signal.bind (pmfPi.bind (fun acts => f (transition acts)))
  simp only [Round.evalMixed, PMF.bind_bind, PMF.bind_map]
  congr 1; funext sig; congr 1; funext acts
  exact hrest acts

-- ============================================================================
-- Canonical Kuhn behavioral strategy
-- ============================================================================

/-- Build the player-i history up to round `k`: a list of (view, action) pairs
    extracted from a consistent execution. -/
private noncomputable def buildHistory
    (rounds : List (Round n S V A Sig))
    (i : Fin n) (st : ℕ → S) (sig : ℕ → (Fin n → Sig))
    (acts : ℕ → (Fin n → Option A)) :
    (k : ℕ) → k ≤ rounds.length → List (V × Option A)
  | 0, _ => []
  | k + 1, hk =>
    buildHistory rounds i st sig acts k (by omega) ++
      [(rounds[k]'(by omega) |>.view i (st k) (sig k i), acts k i)]

/-- Construct a consistent state sequence from any initial state and action sequence. -/
private noncomputable def mkExecStates (rounds : List (Round n S V A Sig)) (s₀ : S)
    (acts : ℕ → (Fin n → Option A)) : ℕ → S
  | 0 => s₀
  | k + 1 => if hk : k < rounds.length
    then rounds[k].transition (mkExecStates rounds s₀ acts k) (acts k)
    else mkExecStates rounds s₀ acts k

private theorem mkExecStates_consistent (rounds : List (Round n S V A Sig)) (s₀ : S)
    (acts : ℕ → (Fin n → Option A)) :
    ConsistentExec rounds s₀ (mkExecStates rounds s₀ acts) acts :=
  ⟨rfl, fun j hj => by simp [mkExecStates, dif_pos hj]⟩

/-- Under StrongRecall, `buildHistory` is canonical: two consistent executions
    reaching the same view at round `k` produce the same history. -/
private theorem buildHistory_unique
    (rounds : List (Round n S V A Sig)) (s₀ : S) (i : Fin n)
    (hrecall : RoundsStrongRecall rounds s₀ i)
    (k : ℕ) (hk : k < rounds.length)
    (st₁ st₂ : ℕ → S) (sig₁ sig₂ : ℕ → (Fin n → Sig))
    (acts₁ acts₂ : ℕ → (Fin n → Option A))
    (hce₁ : ConsistentExec rounds s₀ st₁ acts₁)
    (hce₂ : ConsistentExec rounds s₀ st₂ acts₂)
    (hview : rounds[k].view i (st₁ k) (sig₁ k i) =
      rounds[k].view i (st₂ k) (sig₂ k i)) :
    buildHistory rounds i st₁ sig₁ acts₁ k (le_of_lt hk) =
      buildHistory rounds i st₂ sig₂ acts₂ k (le_of_lt hk) := by
  induction k with
  | zero => rfl
  | succ k ihk =>
    have hsr := hrecall (k + 1) hk st₁ st₂ sig₁ sig₂ acts₁ acts₂ hce₁ hce₂ hview
    have hk' : k < rounds.length := by omega
    have hview_k := (hsr k (by omega) hk').1
    have hact_k := (hsr k (by omega) hk').2
    simp only [buildHistory]
    congr 1
    · exact ihk hk' hview_k
    · exact List.cons_eq_cons.mpr ⟨Prod.ext hview_k hact_k, rfl⟩

open Classical in
/-- Canonical Kuhn behavioral strategy for the mixed → behavioral direction.

    At each view `w` for player `i`, extracts the player-i history
    (sequence of earlier views and actions) from a `StrongRecall` witness,
    applies iterated conditioning on `μ i`, and returns the conditional
    marginal at `w`.

    Under `StrongRecall`, the history is uniquely determined by `w`, so
    the `Classical.choice` of witness doesn't affect the result. -/
noncomputable def kuhnBehavioral
    [Fintype V] [Fintype (Option A)] [Fintype (PureStrategy V A)]
    (rounds : List (Round n S V A Sig))
    (s₀ : S)
    (μ : MixedProfile' n V A) :
    BehavioralProfile n V A := fun i w =>
  if h : ∃ (k : ℕ) (hk : k < rounds.length) (st : ℕ → S)
      (sig : ℕ → (Fin n → Sig)) (acts : ℕ → (Fin n → Option A)),
      ConsistentExec rounds s₀ st acts ∧
      rounds[k].view i (st k) (sig k i) = w
  then
    let k := h.choose
    let hk := h.choose_spec.choose
    let st := h.choose_spec.choose_spec.choose
    let sig := h.choose_spec.choose_spec.choose_spec.choose
    let acts := h.choose_spec.choose_spec.choose_spec.choose_spec.choose
    let hist := buildHistory rounds i st sig acts k (le_of_lt hk)
    pushforward (iterCondMixed (μ i) hist) (· w)
  else
    PMF.pure none

open Classical in
/-- At a view reachable at round `k`, `kuhnBehavioral` returns the conditioned
    pushforward using the history from ANY consistent execution reaching that view.
    StrongRecall ensures this is independent of which witness is chosen. -/
theorem kuhnBehavioral_eq
    [Fintype V] [Fintype (Option A)] [Fintype (PureStrategy V A)]
    (rounds : List (Round n S V A Sig)) (s₀ : S) (μ : MixedProfile' n V A)
    (hsep : RoundsViewSep rounds) (hrecall : ∀ i, RoundsStrongRecall rounds s₀ i)
    (i : Fin n) (k : ℕ) (hk : k < rounds.length)
    (st : ℕ → S) (sig : ℕ → (Fin n → Sig)) (acts : ℕ → (Fin n → Option A))
    (hce : ConsistentExec rounds s₀ st acts) :
    kuhnBehavioral rounds s₀ μ i (rounds[k].view i (st k) (sig k i)) =
      pushforward (iterCondMixed (μ i) (buildHistory rounds i st sig acts k (le_of_lt hk)))
        (· (rounds[k].view i (st k) (sig k i))) := by
  simp only [kuhnBehavioral]
  -- The view is reachable
  have hexists : ∃ (k' : ℕ) (_ : k' < rounds.length) (st' : ℕ → S)
      (sig' : ℕ → (Fin n → Sig)) (acts' : ℕ → (Fin n → Option A)),
      ConsistentExec rounds s₀ st' acts' ∧
      rounds[k'].view i (st' k') (sig' k' i) = rounds[k].view i (st k) (sig k i) :=
    ⟨k, hk, st, sig, acts, hce, rfl⟩
  rw [dif_pos hexists]
  -- Prove equality via a helper that universally quantifies over the chosen values
  -- (so subst can work on the round index equality)
  suffices aux : ∀ (k' : ℕ) (hk' : k' < rounds.length)
      (st' : ℕ → S) (sig' : ℕ → (Fin n → Sig)) (acts' : ℕ → (Fin n → Option A)),
      ConsistentExec rounds s₀ st' acts' →
      rounds[k'].view i (st' k') (sig' k' i) = rounds[k].view i (st k) (sig k i) →
      k' = k →
      pushforward (iterCondMixed (μ i) (buildHistory rounds i st' sig' acts' k' (le_of_lt hk')))
          (· (rounds[k].view i (st k) (sig k i))) =
        pushforward (iterCondMixed (μ i) (buildHistory rounds i st sig acts k (le_of_lt hk)))
          (· (rounds[k].view i (st k) (sig k i))) from
    aux hexists.choose hexists.choose_spec.choose
      hexists.choose_spec.choose_spec.choose
      hexists.choose_spec.choose_spec.choose_spec.choose
      hexists.choose_spec.choose_spec.choose_spec.choose_spec.choose
      hexists.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
      hexists.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2
      (by by_contra hne
          exact absurd
            hexists.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2
            (hsep hexists.choose_spec.choose hk hne i
              (hexists.choose_spec.choose_spec.choose hexists.choose)
              (st k)
              (hexists.choose_spec.choose_spec.choose_spec.choose hexists.choose)
              (fun _ => sig k i)))
  intro k' hk' st' sig' acts' hce' hview' hkk
  subst hkk
  congr 1; congr 1
  exact buildHistory_unique rounds s₀ i (hrecall i) k' hk' st' st sig' sig acts' acts
    hce' hce hview'

/-- buildHistory for `(r :: rest)` at round `k+1` decomposes as
    the head entry followed by buildHistory for `rest` at round `k`,
    when the state/signal/action sequences are shifted by 1. -/
private theorem buildHistory_cons_succ
    (r : Round n S V A Sig) (rest : List (Round n S V A Sig))
    (i : Fin n) (st : ℕ → S) (sig : ℕ → (Fin n → Sig)) (acts : ℕ → (Fin n → Option A))
    (k : ℕ) (hk : k + 1 ≤ (r :: rest).length) :
    buildHistory (r :: rest) i st sig acts (k + 1) hk =
      [(r.view i (st 0) (sig 0 i), acts 0 i)] ++
        buildHistory rest i (fun m => st (m + 1)) (fun m => sig (m + 1))
          (fun m => acts (m + 1)) k (by simp at hk; omega) := by
  induction k with
  | zero => simp [buildHistory]
  | succ k ihk =>
    have step1 : buildHistory (r :: rest) i st sig acts (k + 2) hk =
        buildHistory (r :: rest) i st sig acts (k + 1) (by omega) ++
          [((r :: rest)[k + 1]'(by omega) |>.view i (st (k + 1)) (sig (k + 1) i),
            acts (k + 1) i)] := rfl
    rw [step1, ihk (by omega)]
    simp only [List.append_assoc, List.getElem_cons_succ, buildHistory]

open Classical in
/-- At views reachable from `s₁ = r.transition s₀ acts₀` in `rest`,
    `kuhnBehavioral (r :: rest) s₀ μ` and `kuhnBehavioral rest s₁ μ'` agree,
    where `μ' i = condMixed (μ i) (r.view i s₀ (sig₀ i)) (acts₀ i)`. -/
private theorem kuhnBehavioral_tail_agree
    [Fintype V] [Fintype (Option A)] [Fintype (PureStrategy V A)]
    (r : Round n S V A Sig) (rest : List (Round n S V A Sig))
    (s₀ : S) (μ : MixedProfile' n V A)
    (hsep : RoundsViewSep (r :: rest))
    (hrecall : ∀ i, RoundsStrongRecall (r :: rest) s₀ i)
    (sig₀ : Fin n → Sig) (acts₀ : Fin n → Option A)
    (i : Fin n) (k : ℕ) (hk : k < rest.length)
    (st : ℕ → S) (sig : ℕ → (Fin n → Sig)) (acts : ℕ → (Fin n → Option A))
    (hce : ConsistentExec rest (r.transition s₀ acts₀) st acts) :
    kuhnBehavioral (r :: rest) s₀ μ i (rest[k].view i (st k) (sig k i)) =
      kuhnBehavioral rest (r.transition s₀ acts₀)
        (fun j => condMixed (μ j) (r.view j s₀ (sig₀ j)) (acts₀ j)) i
        (rest[k].view i (st k) (sig k i)) := by
  -- Extend the rest execution to a (r :: rest) execution by prepending round 0
  let ext_st : ℕ → S := fun m => match m with | 0 => s₀ | m + 1 => st m
  let ext_sig : ℕ → (Fin n → Sig) := fun m => match m with | 0 => sig₀ | m + 1 => sig m
  let ext_acts : ℕ → (Fin n → Option A) := fun m => match m with | 0 => acts₀ | m + 1 => acts m
  have hce_ext : ConsistentExec (r :: rest) s₀ ext_st ext_acts := by
    exact ⟨rfl, fun m hm => by match m with
      | 0 => simp [ext_st, ext_acts, hce.1]
      | m + 1 =>
        simp only [List.getElem_cons_succ, ext_st, ext_acts]
        exact hce.2 m (by simpa using hm)⟩
  -- LHS: apply kuhnBehavioral_eq for (r :: rest) at round k+1
  have hkL : k + 1 < (r :: rest).length := by simp; omega
  have lhs := kuhnBehavioral_eq (r :: rest) s₀ μ hsep hrecall i (k + 1) hkL
    ext_st ext_sig ext_acts hce_ext
  simp only [List.getElem_cons_succ, ext_st, ext_sig] at lhs
  -- Decompose buildHistory using buildHistory_cons_succ
  have hbh := buildHistory_cons_succ r rest i ext_st ext_sig ext_acts k (by omega)
  rw [hbh] at lhs
  simp only [List.singleton_append, iterCondMixed_cons] at lhs
  -- Now LHS = pushforward (iterCondMixed (condMixed ...) (buildHistory rest shifted k _)) (· w)
  -- RHS: apply kuhnBehavioral_eq for rest at round k
  have hsep_tail := RoundsViewSep_tail hsep
  have hrecall_tail : ∀ j, RoundsStrongRecall rest (r.transition s₀ acts₀) j :=
    fun j => RoundsStrongRecall_tail r rest s₀ acts₀ j (hrecall j)
  have rhs := kuhnBehavioral_eq rest (r.transition s₀ acts₀)
    (fun j => condMixed (μ j) (r.view j s₀ (sig₀ j)) (acts₀ j))
    hsep_tail hrecall_tail i k hk st sig acts hce
  rw [lhs, rhs]

/-- If two behavioral profiles agree at all views reachable from `s` via
    consistent executions, their evaluations are equal. -/
private theorem evalRoundsMixed_congr_reachable [Fintype (Option A)]
    (rounds : List (Round n S V A Sig))
    (σ₁ σ₂ : BehavioralProfile n V A) (s : S)
    (h : ∀ (k : ℕ) (_ : k < rounds.length) (st : ℕ → S) (sig : ℕ → (Fin n → Sig))
        (acts : ℕ → (Fin n → Option A)),
        ConsistentExec rounds s st acts →
        ∀ i, σ₁ i (rounds[k].view i (st k) (sig k i)) =
          σ₂ i (rounds[k].view i (st k) (sig k i))) :
    evalRoundsMixed rounds σ₁ s = evalRoundsMixed rounds σ₂ s := by
  induction rounds generalizing s with
  | nil => simp [evalRoundsMixed_nil]
  | cons r rest ih =>
    apply evalRoundsMixed_congr_at
    · intro i sig
      exact h 0 (by simp) (mkExecStates (r :: rest) s (fun _ _ => none))
        (fun _ => sig) (fun _ _ => none) (mkExecStates_consistent _ _ _) i
    · intro acts₀
      apply ih
      intro k hk st sig acts hce i
      -- Extend to (r :: rest) execution by prepending s and acts₀
      let ext_st : ℕ → S := fun m => match m with | 0 => s | m + 1 => st m
      let ext_acts : ℕ → (Fin n → Option A) :=
        fun m => match m with | 0 => acts₀ | m + 1 => acts m
      let ext_sig : ℕ → (Fin n → Sig) :=
        fun m => match m with | 0 => sig 0 | m + 1 => sig m
      have hce_ext : ConsistentExec (r :: rest) s ext_st ext_acts :=
        ⟨rfl, fun m hm => by match m with
          | 0 => simp [ext_st, ext_acts, hce.1]
          | m + 1 =>
            simp only [List.getElem_cons_succ, ext_st, ext_acts]
            exact hce.2 m (by simpa using hm)⟩
      exact h (k + 1) (by simp; omega) ext_st ext_sig ext_acts hce_ext i

set_option linter.unusedFintypeInType false in
open Classical in
/-- `kuhnBehavioral` is correct: its evaluation equals the mixed profile evaluation. -/
theorem kuhnBehavioral_correct
    [Fintype V] [Fintype S]
    [Fintype (Option A)]
    [Fintype (PureStrategy V A)]
    (rounds : List (Round n S V A Sig))
    (s₀ : S)
    (hsep : RoundsViewSep rounds)
    (hrecall : ∀ i, RoundsStrongRecall rounds s₀ i)
    (μ : MixedProfile' n V A) :
    evalRoundsMixed rounds (kuhnBehavioral rounds s₀ μ) s₀ =
      (pmfPi μ).bind (fun f => evalRounds rounds f s₀) := by
  induction rounds generalizing s₀ μ with
  | nil => simp [evalRoundsMixed_nil, evalRounds_nil]
  | cons r rest ih =>
    let σ := kuhnBehavioral (r :: rest) s₀ μ
    have hsep_tail := RoundsViewSep_tail hsep
    have hrt : ∀ (acts₀ : Fin n → Option A) (i : Fin n),
        RoundsStrongRecall rest (r.transition s₀ acts₀) i :=
      fun acts₀ i => RoundsStrongRecall_tail r rest s₀ acts₀ i (hrecall i)
    -- hhead: kuhnBehavioral at head-round views = pushforward μ
    have hhead : ∀ (i : Fin n) (sig : Fin n → Sig),
        σ i (r.view i s₀ (sig i)) = pushforward (μ i) (· (r.view i s₀ (sig i))) := by
      intro i sig
      have hce₀ := mkExecStates_consistent (r :: rest) s₀ (fun _ _ => none)
      have h := kuhnBehavioral_eq (r :: rest) s₀ μ hsep hrecall i 0 (by simp)
        (mkExecStates (r :: rest) s₀ (fun _ _ => none)) (fun _ => sig) (fun _ _ => none) hce₀
      simp only [List.getElem_cons_zero, mkExecStates, buildHistory, iterCondMixed_nil] at h
      exact h
    -- Unfold both sides through one round
    rw [evalRoundsMixed_cons]
    simp_rw [evalRounds_cons]
    -- Show head round evaluation equivalence
    have heval_head : r.evalMixed σ s₀ = r.evalMixed (fun i v => pushforward (μ i) (· v)) s₀ := by
      simp only [Round.evalMixed]
      congr 1; funext sig₀; congr 1; congr 1; funext i
      exact hhead i sig₀
    rw [heval_head]
    -- Unfold both sides to (signal s₀).bind (fun sig₀ => ...)
    simp only [Round.evalMixed, Round.eval, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    -- Swap pmfPi and signal on RHS
    conv_rhs => rw [PMF.bind_comm]
    -- Both sides: (signal s₀).bind (fun sig₀ => ...)
    congr 1; funext sig₀
    -- Apply pmfPi_bind_decompose_views on RHS
    rw [pmfPi_bind_decompose_views μ (fun i => r.view i s₀ (sig₀ i))]
    -- Both sides: push.bind (fun acts => INNER)
    -- Prove at the push-bind level so we can case-split on whether push weight is zero.
    suffices hinner : ∀ acts₀,
        (pmfPi (fun i => pushforward (μ i) (· (r.view i s₀ (sig₀ i))))) acts₀ ≠ 0 →
        evalRoundsMixed rest σ (r.transition s₀ acts₀) =
          (pmfPi (fun i => condMixed (μ i) (r.view i s₀ (sig₀ i)) (acts₀ i))).bind (fun f =>
            evalRounds rest f (r.transition s₀ (fun i => f i (r.view i s₀ (sig₀ i))))) by
      ext b; simp only [PMF.bind_apply]
      apply tsum_congr; intro acts₀
      by_cases hpush : (pmfPi (fun i => pushforward (μ i)
          (· (r.view i s₀ (sig₀ i))))) acts₀ = 0
      · simp [hpush]
      · rw [hinner acts₀ hpush]; simp only [PMF.bind_apply]
    -- Prove inner equality assuming push weight ≠ 0
    intro acts₀ hpush
    -- From nonzero push: all per-player masses are nonzero
    have hmass_ne : ∀ i, pmfMass (μ := μ i)
        (fun g => g (r.view i s₀ (sig₀ i)) = acts₀ i) ≠ 0 := by
      intro i hmz
      apply hpush; simp only [pmfPi_apply]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [pushforward, PMF.bind_apply, PMF.pure_apply, tsum_fintype,
        pmfMass, pmfMask, mul_ite, mul_one, mul_zero] at hmz ⊢
      convert hmz using 1; congr 1; ext g; congr 1; ext; simp [eq_comm]
    let s₁ := r.transition s₀ acts₀
    let μ' : MixedProfile' n V A :=
      fun i => condMixed (μ i) (r.view i s₀ (sig₀ i)) (acts₀ i)
    -- Step 3: Bridge σ with kuhnBehavioral rest + IH
    have hbridge : evalRoundsMixed rest σ s₁ =
        evalRoundsMixed rest (kuhnBehavioral rest s₁ μ') s₁ := by
      apply evalRoundsMixed_congr_reachable
      intro k hk st sig acts hce i
      exact kuhnBehavioral_tail_agree r rest s₀ μ hsep hrecall sig₀ acts₀
        i k hk st sig acts hce
    have hih := ih s₁ hsep_tail (hrt acts₀) μ'
    rw [hbridge, hih]
    -- Goal: (pmfPi μ').bind (evalRounds rest · s₁) =
    --       (pmfPi μ').bind (fun f => evalRounds rest f (r.transition s₀ (fun i => f i (v_i))))
    -- Step 4: condMixed coord fix (now all masses are nonzero)
    ext b; simp only [PMF.bind_apply]
    apply tsum_congr; intro f
    by_cases hf : (pmfPi μ') f = 0
    · have hf' : (pmfPi fun i => condMixed (μ i) (r.view i s₀ (sig₀ i)) (acts₀ i)) f = 0 := hf
      simp [hf, hf']
    · congr 1; congr 1; congr 1
      change r.transition s₀ acts₀ = r.transition s₀ (fun i => f i (r.view i s₀ (sig₀ i)))
      congr 1; funext i
      have hi : (μ' i) (f i) ≠ 0 := by
        intro heq; apply hf; simp only [pmfPi_apply]
        exact Finset.prod_eq_zero (Finset.mem_univ i) heq
      exact (condMixed_coord (μ i) _ (acts₀ i) (f i) (hmass_ne i) hi).symm

set_option linter.unusedFintypeInType false in
open Classical in
/-- Core inductive lemma for Kuhn mixed → behavioral. Under view separation and
    strong recall from `s₀`, every mixed profile has a behavioral profile giving
    the same evaluation from `s₀`. -/
theorem exists_behavioral_eq_mixed_rounds
    [Fintype V] [Fintype S]
    [Fintype (Option A)]
    [Fintype (PureStrategy V A)]
    (rounds : List (Round n S V A Sig))
    (s₀ : S)
    (hsep : RoundsViewSep rounds)
    (hrecall : ∀ i, RoundsStrongRecall rounds s₀ i)
    (μ : MixedProfile' n V A) :
    ∃ σ : BehavioralProfile n V A,
      evalRoundsMixed rounds σ s₀ =
        (pmfPi μ).bind (fun f => evalRounds rounds f s₀) :=
  ⟨kuhnBehavioral rounds s₀ μ, kuhnBehavioral_correct rounds s₀ hsep hrecall μ⟩

set_option linter.unusedFintypeInType false in
/-- **Kuhn (Mixed → Behavioral)**: Under strong perfect recall, for every mixed
    profile there exists a behavioral profile producing the same outcome
    distribution.

    The behavioral strategy at each view is the *conditional* distribution of
    the mixed strategy's action at that view, given the history of views and
    actions that leads to it. Under `StrongPerfectRecall`, the view at each
    round determines this history uniquely, so the conditional is well-defined
    as a function of the view alone.

    This is the hard direction of Kuhn's theorem. The easy direction
    (`kuhn_behavioral_to_mixed`) only needs `NoViewRepeat`. -/
theorem Protocol.kuhn_mixed_to_behavioral
    [Fintype V] [Fintype S]
    [Fintype (Option A)]
    [Fintype (PureStrategy V A)]
    (G : Protocol n S V A Sig)
    (hSPR : G.StrongPerfectRecallAll)
    (μ : MixedProfile' n V A) :
    ∃ σ : BehavioralProfile n V A,
      G.evalMixed σ = G.evalMixedProfile μ := by
  obtain ⟨σ, hσ⟩ := exists_behavioral_eq_mixed_rounds G.rounds G.init
    (G.noViewRepeat_roundsViewSep (G.strongPerfectRecall_noViewRepeat hSPR))
    (fun i => (hSPR i).2) μ
  exact ⟨σ, hσ⟩

end GameTheory
