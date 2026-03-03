import GameTheory.ProtoODP

/-!
# Zermelo's Theorem on Protocol

Zermelo's theorem: every finite, perfect-information, sequential, view-separated
protocol has a pure subgame-perfect equilibrium (constructible by backward induction).

## Main definitions

- `Protocol.IsSequential` — at most one player's action matters per state per round
- `Protocol.ViewSeparated` — views at different rounds are disjoint for each player
- `Protocol.zermelo` — Zermelo's theorem: finite PI sequential → ∃ pure SPE

## Design

The proof constructs a pure SPE by backward induction over rounds (last to first).
At each round and state, the active player chooses the action that maximizes their
continuation value. The PI condition ensures the view determines the state, so
the optimal action can be encoded as a memoryless strategy. The ViewSeparated
condition ensures that setting the strategy at one round's views doesn't conflict
with other rounds.

Requires `[Fintype S]`, `[Fintype A]`, `IsPerfectInfo`, `IsSequential`,
`ViewSeparated`.
-/

namespace GameTheory

variable {n : ℕ} {S V A Sig : Type}

-- ============================================================================
-- Sequential (one player acts at a time)
-- ============================================================================

open Classical in
/-- A protocol is sequential if at each round and state, at most one player's
    action affects the transition. -/
def Protocol.IsSequential (G : Protocol n S V A Sig) : Prop :=
  ∀ (r : Round n S V A Sig), r ∈ G.rounds →
    ∀ (s : S), ∃ (active : Fin n),
      ∀ (j : Fin n), j ≠ active → r.ActionIrrelevant j s

-- ============================================================================
-- Helper: ActionIrrelevant means r.eval is invariant
-- ============================================================================

open Classical in
/-- If player `i`'s action is irrelevant at state `s` in round `r`,
    then `r.eval` is unchanged when modifying player `i`'s strategy. -/
theorem Round.eval_actionIrrelevant (r : Round n S V A Sig)
    (σ : PureProfile n V A) (i : Fin n) (si' : PureStrategy V A) (s : S)
    (h : r.ActionIrrelevant i s) :
    r.eval σ s = r.eval (Function.update σ i si') s := by
  simp only [Round.eval]
  congr 1; funext sig
  have hact : (fun j => (Function.update σ i si') j (r.view j s (sig j)))
    = Function.update (fun j => σ j (r.view j s (sig j))) i
        (si' (r.view i s (sig i))) := by
    ext j; simp [Function.update]; split <;> simp_all
  rw [hact]
  exact (h sig (fun j => σ j (r.view j s (sig j)))
    (si' (r.view i s (sig i)))).symm

-- ============================================================================
-- Helper: expect monotonicity and map
-- ============================================================================

set_option linter.unusedFintypeInType false in
private theorem expect_le_expect [Fintype S]
    (μ : PMF S) (f g : S → ℝ) (h : ∀ s, f s ≤ g s) :
    expect μ f ≤ expect μ g := by
  simp only [expect_eq_sum]
  exact Finset.sum_le_sum (fun s _ =>
    mul_le_mul_of_nonneg_left (h s) ENNReal.toReal_nonneg)

set_option linter.unusedFintypeInType false in
private theorem expect_map [Fintype α] [Fintype β]
    (μ : PMF α) (f : α → β) (g : β → ℝ) :
    expect (μ.map f) g = expect μ (g ∘ f) := by
  rw [← PMF.bind_pure_comp, expect_bind]
  congr 1; ext a; simp [Function.comp, expect_pure]

open Classical in
/-- Under sequential play, the transition depends only on the active player's action. -/
private theorem transition_eq_active (r : Round n S V A Sig) (s : S)
    (active : Fin n) (sig : Fin n → Sig)
    (hseq : ∀ (j : Fin n), j ≠ active → r.ActionIrrelevant j s)
    (f : Fin n → Option A) :
    r.transition s f = r.transition s (fun _ => f active) := by
  suffices h : ∀ (T : Finset (Fin n)), (∀ j ∈ T, j ≠ active) →
      r.transition s (fun j => if j ∈ T then f j else f active) =
        r.transition s (fun _ => f active) by
    have h1 := h (Finset.univ.erase active) fun j hj => (Finset.mem_erase.mp hj).1
    have h2 : (fun j => if j ∈ Finset.univ.erase active then f j else f active) = f := by
      ext j; by_cases hj : j = active <;> simp [hj, Finset.mem_erase]
    rwa [h2] at h1
  intro T hT
  induction T using Finset.induction_on with
  | empty => rfl
  | @insert a T' ha ih =>
    have ha_ne := hT a (Finset.mem_insert_self a T')
    have hT' := fun j hj => hT j (Finset.mem_insert_of_mem hj)
    have hfun : (fun j => if j ∈ insert a T' then f j else f active) =
        Function.update (fun j => if j ∈ T' then f j else f active) a (f a) := by
      ext j; simp only [Finset.mem_insert, Function.update]
      by_cases hja : j = a
      · subst hja; simp [ha]
      · simp [hja]
    rw [hfun]
    exact ((hseq a ha_ne) sig _ (f a)).trans (ih hT')

-- ============================================================================
-- View disjointness
-- ============================================================================

-- ============================================================================
-- Backward induction: list-level SPE existence
-- ============================================================================

set_option linter.unusedFintypeInType false in
open Classical in
/-- Key backward induction lemma: for a list of rounds with PI, sequential,
    and pairwise view-disjoint conditions, there exists a pure profile that
    is Nash at every suffix-subgame. -/
private theorem exists_spe_rounds
    [Fintype S] [Fintype V] [Fintype A] [Fintype Sig]
    [Nonempty (Option A)]
    (rounds : List (Round n S V A Sig))
    (u : S → Fin n → ℝ)
    (hPI : ∀ r ∈ rounds, ∀ (i : Fin n) (s₁ s₂ : S) (sig₁ sig₂ : Fin n → Sig),
      r.view i s₁ (sig₁ i) = r.view i s₂ (sig₂ i) → s₁ = s₂)
    (hseq : ∀ r ∈ rounds, ∀ (s : S), ∃ (active : Fin n),
      ∀ (j : Fin n), j ≠ active → r.ActionIrrelevant j s)
    (hVD : ∀ (k : ℕ) (hk : k < rounds.length),
      viewDisjointFromList rounds[k] (rounds.drop (k + 1))) :
    ∃ σ : PureProfile n V A,
      ∀ (k : ℕ) (s : S) (i : Fin n) (si' : PureStrategy V A),
        expect (evalRounds (rounds.drop k) σ s) (fun s' => u s' i) ≥
        expect (evalRounds (rounds.drop k) (Function.update σ i si') s)
          (fun s' => u s' i) := by
  induction rounds with
  | nil =>
    exact ⟨fun _ _ => none, fun _ _ _ _ => by simp [evalRounds_nil]⟩
  | cons r rest ih =>
    have hPI_rest := fun r' (hr' : r' ∈ rest) => hPI r' (.tail r hr')
    have hseq_rest := fun r' (hr' : r' ∈ rest) => hseq r' (.tail r hr')
    have hVD_rest : ∀ (k : ℕ) (hk : k < rest.length),
        viewDisjointFromList rest[k] (rest.drop (k + 1)) := by
      intro k hk
      have hk' : k + 1 < (r :: rest).length := by simp; omega
      have := hVD (k + 1) hk'
      simp only [List.getElem_cons_succ, List.drop_succ_cons] at this
      exact this
    obtain ⟨σ₀, hσ₀⟩ := ih hPI_rest hseq_rest hVD_rest
    have hVD_head : viewDisjointFromList r rest := by
      have := hVD 0 (by simp)
      simpa [List.drop_succ_cons] using this
    -- Construct σ: override σ₀ at views from round r with argmax, keep σ₀ elsewhere.
    -- For each player i and view v from round r, choose the action maximizing
    -- the continuation value. Under PI, view determines state.
    --
    -- isFromR i v : whether v is produced by round r for player i
    -- stateOf i v : the unique state producing view v for player i (when isFromR)
    let isFromR : Fin n → V → Prop := fun j v =>
      ∃ (s₀ : S), ∃ (sig₀ : Sig), r.view j s₀ sig₀ = v
    -- stateOf is unused in the actual construction; σ uses Classical.choose h directly
    -- Continuation value: if player i plays action a at state s through round r
    let contVal : Fin n → S → Option A → ℝ := fun j s₀ a =>
      expect (evalRounds rest σ₀ (r.transition s₀ (fun _ => a))) (fun s' => u s' j)
    -- σ: on views from r, use argmax; on other views, use σ₀
    let σ : PureProfile n V A := fun j v =>
      if h : isFromR j v then
        let s₀ := Classical.choose h
        (Finite.exists_max (fun a => contVal j s₀ a)).choose
      else σ₀ j v
    -- Key: σ agrees with σ₀ on views from rest (by view disjointness)
    have hσ_eq : ∀ r' ∈ rest, ∀ (j : Fin n) (s' : S) (sig : Fin n → Sig),
        σ j (r'.view j s' (sig j)) = σ₀ j (r'.view j s' (sig j)) := by
      intro r' hr' j s' sig
      change (if h : isFromR j (r'.view j s' (sig j)) then _ else _) = _
      rw [dif_neg]
      intro ⟨s₂, sig₂, heq⟩
      exact hVD_head r' hr' j s₂ s' (fun _ => sig₂) sig heq
    refine ⟨σ, fun k s i si' => ?_⟩
    by_cases hk : k = 0
    · -- k = 0: head round r
      subst hk; simp only [List.drop_zero]
      rw [evalRounds_cons, evalRounds_cons, expect_bind, expect_bind]
      obtain ⟨active, hactive⟩ := hseq r (.head rest) s
      by_cases hi : i = active
      · -- i = active: optimized by argmax construction
        subst hi
        -- Rewrite r.eval using transition_eq_active (transition depends only on active)
        have heval_σ : r.eval σ s = (r.signal s).map (fun sg =>
            r.transition s (fun _ => σ i (r.view i s (sg i)))) := by
          simp only [Round.eval]; congr 1; funext sg
          exact transition_eq_active r s i sg hactive _
        have heval_upd : r.eval (Function.update σ i si') s = (r.signal s).map (fun sg =>
            r.transition s (fun _ => si' (r.view i s (sg i)))) := by
          simp only [Round.eval]; congr 1; funext sg
          rw [transition_eq_active r s i sg hactive]
          simp [Function.update_self]
        rw [heval_σ, heval_upd, expect_map, expect_map]
        -- Replace evalRounds rest σ → σ₀ and rest (upd σ i si') → (upd σ₀ i si')
        simp only [Function.comp_def]
        simp_rw [show ∀ s', evalRounds rest σ s' = evalRounds rest σ₀ s' from
          fun s' => evalRounds_congr rest σ σ₀ hσ_eq s']
        simp_rw [show ∀ s', evalRounds rest (Function.update σ i si') s' =
            evalRounds rest (Function.update σ₀ i si') s' from
          fun s' => evalRounds_congr rest _ _ (fun r' hr' j s'' sg => by
            by_cases hij : j = i
            · subst hij; simp [Function.update]
            · simp only [Function.update_of_ne hij]; exact hσ_eq r' hr' j s'' sg) s']
        -- Pointwise: for each signal, argmax + IH gives the bound
        apply expect_le_expect; intro sg
        -- PI: Classical.choose h = s for any h : isFromR i view
        have hfrom : isFromR i (r.view i s (sg i)) := ⟨s, sg i, rfl⟩
        have hchoose_eq : ∀ (h : isFromR i (r.view i s (sg i))),
            Classical.choose h = s := by
          intro h
          have ⟨sig₀, hsig₀⟩ := Classical.choose_spec h
          exact hPI r (.head rest) i _ s (fun _ => sig₀) sg hsig₀
        -- Argmax: σ i view maximizes contVal i s _
        have hargmax : contVal i s (si' (r.view i s (sg i))) ≤
            contVal i s (σ i (r.view i s (sg i))) := by
          have hσ_val : σ i (r.view i s (sg i)) =
              (Finite.exists_max (fun a => contVal i (Classical.choose hfrom) a)).choose := by
            change dite _ _ _ = _; rw [dif_pos hfrom]
          rw [hσ_val, show Classical.choose hfrom = s from hchoose_eq hfrom]
          exact (Finite.exists_max (fun a => contVal i s a)).choose_spec _
        -- IH: σ₀ at rest beats any deviation
        have hih := hσ₀ 0 (r.transition s (fun _ => si' (r.view i s (sg i)))) i si'
        simp only [List.drop_zero] at hih
        linarith
      · -- i ≠ active: r.eval unchanged (ActionIrrelevant)
        have hirr := hactive i hi
        have heval_eq : r.eval σ s = r.eval (Function.update σ i si') s :=
          Round.eval_actionIrrelevant r σ i si' s hirr
        rw [heval_eq]
        -- Need: E_s'[E[rest σ s'](u·i)] ≥ E_s'[E[rest (upd σ i si') s'](u·i)]
        -- This follows from the IH at k=0 on rest + σ/σ₀ congruence + monotonicity
        apply expect_le_expect
        intro s'
        -- evalRounds rest σ s' vs evalRounds rest (upd σ i si') s'
        -- σ agrees with σ₀ on rest, so evalRounds rest σ = evalRounds rest σ₀
        -- Similarly, upd σ i si' agrees with upd σ₀ i si' on rest
        rw [evalRounds_congr rest σ σ₀ (fun r' hr' j s'' sig =>
          hσ_eq r' hr' j s'' sig) s']
        rw [evalRounds_congr rest (Function.update σ i si') (Function.update σ₀ i si')
          (fun r' hr' j s'' sig => by
            by_cases hij : j = i
            · subst hij; simp [Function.update]
            · simp only [Function.update_of_ne hij]
              exact hσ_eq r' hr' j s'' sig) s']
        -- Now need: E[rest σ₀ s'](u·i) ≥ E[rest (upd σ₀ i si') s'](u·i)
        exact hσ₀ 0 s' i si'
    · -- k ≥ 1: in the tail, reduce to IH via congruence
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
      conv_lhs => rw [show k = (k - 1) + 1 from by omega]
      conv_rhs => rw [show k = (k - 1) + 1 from by omega]
      simp only [List.drop_succ_cons]
      -- σ ≡ σ₀ on rest views, and update σ i si' ≡ update σ₀ i si' on rest views
      have hcong : ∀ s', evalRounds (rest.drop (k - 1)) σ s' =
          evalRounds (rest.drop (k - 1)) σ₀ s' := fun s' =>
        evalRounds_congr _ σ σ₀ (fun r' hr' j s'' sig =>
          hσ_eq r' (List.mem_of_mem_drop hr') j s'' sig) s'
      have hcong_upd : ∀ s', evalRounds (rest.drop (k - 1))
            (Function.update σ i si') s' =
          evalRounds (rest.drop (k - 1)) (Function.update σ₀ i si') s' := fun s' =>
        evalRounds_congr _ _ _ (fun r' hr' j s'' sig => by
          by_cases hij : j = i
          · subst hij; simp [Function.update]
          · simp only [Function.update_of_ne hij]
            exact hσ_eq r' (List.mem_of_mem_drop hr') j s'' sig) s'
      simp_rw [hcong, hcong_upd]
      exact hσ₀ (k - 1) s i si'

-- ============================================================================
-- Zermelo's theorem
-- ============================================================================

set_option linter.unusedFintypeInType false in
/-- Zermelo's theorem: a finite, perfect-information, sequential, view-separated
    protocol has a pure subgame-perfect equilibrium.

    The SPE is constructed by backward induction: at each round and state,
    the active player picks the action maximizing their continuation value.
    ViewSeparated ensures different rounds' views don't collide, so the
    backward induction strategy can be encoded as a single memoryless profile. -/
theorem Protocol.zermelo (G : Protocol n S V A Sig)
    [Fintype S] [Fintype V] [Fintype A] [Fintype Sig]
    [Nonempty (Option A)]
    (u : S → Fin n → ℝ)
    (hPI : G.IsPerfectInfo)
    (hseq : G.IsSequential)
    (hVS : G.ViewSeparated) :
    ∃ σ : PureProfile n V A, G.IsSubgamePerfect u σ := by
  -- Translate ViewSeparated to list-level viewDisjointFromList
  have hVD_list : ∀ (k : ℕ) (hk : k < G.rounds.length),
      viewDisjointFromList G.rounds[k] (G.rounds.drop (k + 1)) := by
    intro k hk r' hr' i s₁ s₂ sig₁ sig₂
    have ⟨k', hk'mem⟩ := List.get_of_mem hr'
    have hk'bound : k + 1 + k'.val < G.rounds.length := by
      have := k'.isLt; simp [List.length_drop] at this; omega
    have hrw : r' = G.rounds[k + 1 + k'.val] := by
      conv_lhs => rw [← hk'mem]
      simp [List.get_eq_getElem, List.getElem_drop]
    rw [hrw]
    exact hVS hk hk'bound (by omega) i s₁ s₂ sig₁ sig₂
  -- exists_spe_rounds gives a profile that is Nash at every suffix-subgame.
  -- This is exactly IsSubgamePerfect (after unfolding).
  obtain ⟨σ, hσ⟩ := exists_spe_rounds G.rounds u
    (fun r hr => hPI r hr) (fun r hr => hseq r hr) hVD_list
  exact ⟨σ, fun k s i si' => hσ k s i si'⟩

end GameTheory
