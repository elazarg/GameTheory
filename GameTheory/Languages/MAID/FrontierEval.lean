import GameTheory.Languages.MAID.FrontierLemmas

/-!
# Frontier evaluation equals order-free evaluation

The main result is `frontierEval_eq_evalAssignDist`: parallel frontier
evaluation gives the same joint distribution as the Bayesian network
factorization (`evalAssignDist`).

## Proof structure

1. **Layer tracking**: `layerAssigned S k` gives the set of nodes assigned after
   `k` frontier iterations. `layerAssigned_n` shows all nodes are assigned after
   `n` steps (via `frontier_nonempty_of_ne_univ`).

2. **Compatible configs**: `cfgOfAssign S a A` builds the unique `FrontierCfg`
   compatible with total assignment `a` on assigned set `A`.

3. **Layer-by-layer product**: `iterDist_at_cfgOfAssign` shows the probability
   of the compatible config after `k` steps equals `∏_{nd ∈ layerAssigned k} (nodeDist nd a)(a nd)`.

4. **Conclusion**: at `k = n`, `layerAssigned = univ`, so the product is `assignProb a`.
-/

namespace MAID

open GameTheory Math

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

-- ============================================================================
-- Step 1: Frontier independence
-- ============================================================================

/-- Two distinct frontier nodes have no direct edge between them.  Frontier
membership requires all parents assigned; a frontier node is unassigned.
So a frontier node cannot be a parent of another frontier node. -/
theorem frontier_noDirectEdge (S : Struct Player n) (cfg : FrontierCfg S)
    (u v : Fin n) (hu : u ∈ frontier S cfg) (hv : v ∈ frontier S cfg)
    (_hne : u ≠ v) :
    NoDirectEdge S u v := by
  have heu : enabled S cfg u := by simpa [frontier] using hu
  have hev : enabled S cfg v := by simpa [frontier] using hv
  constructor
  · -- u ∉ S.parents v: if u were a parent of v, then u ∈ cfg.assigned
    -- (since v is enabled), contradicting u being unassigned (u is enabled)
    intro h; exact heu.1 (hev.2 h)
  · -- v ∉ S.parents u: symmetric argument
    intro h; exact hev.1 (heu.2 h)

-- ============================================================================
-- Step 2: One-step sequentialization
-- ============================================================================

/-- Lift `nodeDistPol` from a `FrontierCfg` to a `TAssign` by reading parent
values from `extractTAssign`. For frontier nodes, this equals `nodeDist`
because all parents are assigned and `extractTAssign` reads their values
correctly. -/
theorem nodeDistPol_eq_nodeDist_extractTAssign
    (S : Struct Player n) (sem : Sem S) (pol : Policy S) (cfg : FrontierCfg S)
    (nd : ↥(frontier S cfg)) :
    nodeDistPol S sem pol cfg nd =
      nodeDist S sem pol nd.1 (extractTAssign S cfg) := by
  have hEnabled : enabled S cfg nd.1 := enabled_of_mem_frontier nd.2
  -- Helper: restrictCfg on assigned parents = projCfg of extractTAssign
  have hrestr : ∀ (ps : Finset (Fin n)) (hps : ps ⊆ cfg.assigned),
      restrictCfg cfg ps hps = projCfg (extractTAssign S cfg) ps := by
    intro ps hps; funext ⟨p, hp⟩
    simp only [restrictCfg, projCfg, extractTAssign, dif_pos (hps hp)]
  -- Compare probabilities pointwise; split both matches on S.kind nd.1
  ext v; simp only [nodeDistPol, nodeDist]
  split <;> rename_i hk <;> split <;> rename_i hk' <;>
    simp only [hk] at hk'
  -- Close cross-cases (different constructors → contradiction)
  all_goals try (cases hk'; done)
  -- Diagonal cases remain
  · -- chance/chance
    congr 2; exact hrestr _ hEnabled.2
  · -- decision/decision
    cases hk'; congr 1; congr 1
    exact Sigma.ext rfl (heq_of_eq
      (hrestr _ (fun x hx => hEnabled.2 (S.obs_sub nd.1 hx))))
  · -- utility/utility
    cases hk'; rfl

-- ============================================================================
-- Compatibility and layer structure
-- ============================================================================

/-- A `FrontierCfg` is compatible with a total assignment `a` when every
assigned node has the same value as `a`. -/
def Compatible (S : Struct Player n) (cfg : FrontierCfg S) (a : TAssign S) : Prop :=
  ∀ nd (h : nd ∈ cfg.assigned), cfg.values ⟨nd, h⟩ = a nd

/-- `extractTAssign` of a fully-assigned compatible config equals `a`. -/
theorem extractTAssign_eq_of_compatible_univ
    (S : Struct Player n) (cfg : FrontierCfg S) (a : TAssign S)
    (hc : Compatible S cfg a) (hu : cfg.assigned = Finset.univ) :
    extractTAssign S cfg = a := by
  funext nd
  simp only [extractTAssign, dif_pos (hu ▸ Finset.mem_univ nd)]
  exact hc nd (hu ▸ Finset.mem_univ nd)

/-- The frontier as a function of just the assigned set. -/
noncomputable def frontierOfAssigned (S : Struct Player n)
    (A : Finset (Fin n)) : Finset (Fin n) :=
  Finset.filter (fun nd => nd ∉ A ∧ S.parents nd ⊆ A) Finset.univ

/-- `frontier` equals `frontierOfAssigned` applied to `cfg.assigned`. -/
theorem frontier_eq_frontierOfAssigned (S : Struct Player n) (cfg : FrontierCfg S) :
    frontier S cfg = frontierOfAssigned S cfg.assigned := by
  ext nd
  simp only [frontier, frontierOfAssigned, Finset.mem_filter, Finset.mem_univ, true_and, enabled]

/-- The assigned set after `k` frontier iterations. -/
noncomputable def layerAssigned (S : Struct Player n) : Nat → Finset (Fin n)
  | 0 => ∅
  | k + 1 => layerAssigned S k ∪ frontierOfAssigned S (layerAssigned S k)

/-- After `n` iterations, all nodes are assigned. -/
theorem layerAssigned_n (S : Struct Player n) :
    layerAssigned S n = Finset.univ := by
  -- Each step adds at least one node when not yet full.
  -- After n steps on an n-element set, we must have everything.
  suffices h : ∀ k, k ≤ n → k ≤ (layerAssigned S k).card by
    have hle := h n le_rfl
    have hle2 := Finset.card_le_univ (layerAssigned S n)
    rw [Fintype.card_fin] at hle2
    have hcard : (layerAssigned S n).card = Fintype.card (Fin n) := by
      rw [Fintype.card_fin]; exact le_antisymm hle2 hle
    exact Finset.eq_univ_of_card _ hcard
  intro k hk
  induction k with
  | zero => simp [layerAssigned]
  | succ k ih =>
    have ih' := ih (Nat.le_of_succ_le hk)
    by_cases heq : layerAssigned S k = Finset.univ
    · simp [layerAssigned, heq, frontierOfAssigned]
      omega
    · -- frontierOfAssigned adds at least one new node
      have hne : (frontierOfAssigned S (layerAssigned S k)).Nonempty := by
        -- Build a FrontierCfg with this assigned set to use frontier_nonempty_of_ne_univ
        have hne' : (Finset.univ \ layerAssigned S k).Nonempty := by
          rw [Finset.sdiff_nonempty]
          exact fun hsub => heq (Finset.eq_univ_of_forall (fun x => hsub (Finset.mem_univ x)))
        -- Use the same well-foundedness argument as frontier_nonempty_of_ne_univ
        have wf := S.acyclic.wellFounded
        set U := (Finset.univ \ layerAssigned S k : Finset (Fin n))
        have hne'' : (U : Set (Fin n)).Nonempty := Finset.coe_nonempty.mpr hne'
        set m := wf.min (U : Set (Fin n)) hne''
        have hm_mem : m ∈ U := wf.min_mem _ hne''
        have hm_min : ∀ y, y ∈ S.parents m → y ∉ U := by
          intro y hy hyU
          exact wf.not_lt_min _ hyU hy
        have hm_unassigned : m ∉ layerAssigned S k := by
          simp only [U, Finset.mem_sdiff, Finset.mem_univ, true_and] at hm_mem
          exact hm_mem
        have hm_parents : S.parents m ⊆ layerAssigned S k := by
          intro p hp
          by_contra h'
          exact hm_min p hp (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h'⟩)
        exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hm_unassigned, hm_parents⟩⟩⟩
      -- The new frontier is disjoint from the old assigned set
      have hdisj : Disjoint (layerAssigned S k) (frontierOfAssigned S (layerAssigned S k)) := by
        rw [Finset.disjoint_left]
        intro nd hnd hfr
        simp only [frontierOfAssigned, Finset.mem_filter, Finset.mem_univ, true_and] at hfr
        exact hfr.1 hnd
      simp only [layerAssigned]
      rw [Finset.card_union_of_disjoint hdisj]
      have : 0 < (frontierOfAssigned S (layerAssigned S k)).card :=
        Finset.Nonempty.card_pos hne
      omega

-- ============================================================================
-- Build a FrontierCfg from a total assignment restricted to a Finset
-- ============================================================================

/-- Restrict a total assignment to a `Finset`, producing a `FrontierCfg`. -/
def cfgOfAssign (S : Struct Player n) (a : TAssign S)
    (A : Finset (Fin n)) : FrontierCfg S where
  assigned := A
  values := fun ⟨nd, _⟩ => a nd

theorem cfgOfAssign_assigned (S : Struct Player n) (a : TAssign S) (A : Finset (Fin n)) :
    (cfgOfAssign S a A).assigned = A := rfl

theorem cfgOfAssign_compatible (S : Struct Player n) (a : TAssign S) (A : Finset (Fin n)) :
    Compatible S (cfgOfAssign S a A) a := by
  intro nd _; rfl

theorem extractTAssign_cfgOfAssign_univ (S : Struct Player n) (a : TAssign S) :
    extractTAssign S (cfgOfAssign S a Finset.univ) = a := by
  funext nd; simp [extractTAssign, cfgOfAssign, Finset.mem_univ]

-- ============================================================================
-- nodeDistPol on cfgOfAssign equals nodeDist
-- ============================================================================

/-- When a FrontierCfg is compatible with `a`, `extractTAssign` agrees with `a`
on all assigned nodes. -/
theorem extractTAssign_eq_on_assigned (S : Struct Player n)
    (cfg : FrontierCfg S) (a : TAssign S) (hc : Compatible S cfg a)
    (nd : Fin n) (h : nd ∈ cfg.assigned) :
    extractTAssign S cfg nd = a nd := by
  simp only [extractTAssign, dif_pos h]
  exact hc nd h

/-- `nodeDist` depends only on the values at parents (and obsParents for
decision nodes). When two total assignments agree on parents of `nd`, they
give the same `nodeDist`. -/
theorem nodeDist_eq_of_parent_agree (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (nd : Fin n) (a b : TAssign S)
    (hp : ∀ p ∈ S.parents nd, a p = b p) :
    nodeDist S sem pol nd a = nodeDist S sem pol nd b := by
  simp only [nodeDist]
  split
  · congr 1; ext ⟨p, hp'⟩; exact hp p hp'
  · congr 1; exact Sigma.ext rfl (heq_of_eq (by ext ⟨p, hp'⟩; exact hp p (S.obs_sub nd hp')))
  · rfl

/-- On a compatible config, `nodeDistPol` at a frontier node equals `nodeDist`
applied to `a`. -/
theorem nodeDistPol_cfgOfAssign_eq_nodeDist
    (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (a : TAssign S) (A : Finset (Fin n))
    (nd : ↥(frontier S (cfgOfAssign S a A))) :
    nodeDistPol S sem pol (cfgOfAssign S a A) nd =
      nodeDist S sem pol nd.1 a := by
  rw [nodeDistPol_eq_nodeDist_extractTAssign]
  apply nodeDist_eq_of_parent_agree
  intro p hp
  have hen := enabled_of_mem_frontier nd.2
  exact extractTAssign_eq_on_assigned S _ a (cfgOfAssign_compatible S a A) p (hen.2 hp)

-- ============================================================================
-- extendFrontier on cfgOfAssign
-- ============================================================================

/-- Extending `cfgOfAssign S a A` with values `vals` produces a config whose
assigned set is `A ∪ frontier` and whose values on `A` agree with `a`, and
whose values on the frontier are `vals`. -/
theorem extendFrontier_cfgOfAssign_assigned (S : Struct Player n) (a : TAssign S)
    (A : Finset (Fin n))
    (vals : FrontierValues S (cfgOfAssign S a A)) :
    (extendFrontier S (cfgOfAssign S a A) vals).assigned =
      A ∪ frontier S (cfgOfAssign S a A) := rfl

/-- Key: if `vals nd = a nd` for all frontier nodes, then extending `cfgOfAssign`
gives `cfgOfAssign` with the larger assigned set. -/
theorem extendFrontier_cfgOfAssign_eq
    (S : Struct Player n) (a : TAssign S)
    (A : Finset (Fin n))
    (vals : FrontierValues S (cfgOfAssign S a A))
    (hvals : ∀ nd : ↥(frontier S (cfgOfAssign S a A)), vals nd = a nd.1) :
    extendFrontier S (cfgOfAssign S a A) vals =
      cfgOfAssign S a (A ∪ frontier S (cfgOfAssign S a A)) := by
  set F := frontier S (cfgOfAssign S a A)
  change (⟨A ∪ F, fun nd =>
      if hOld : nd.1 ∈ A then a nd.1
      else vals ⟨nd.1,
        (Finset.mem_union.mp nd.2).resolve_left hOld⟩⟩ :
    FrontierCfg S) = ⟨A ∪ F, fun ⟨nd, _⟩ => a nd⟩
  congr 1
  funext ⟨nd, hnd⟩
  simp only
  split
  · rfl
  · exact hvals ⟨nd,
      (Finset.mem_union.mp hnd).resolve_left ‹_›⟩

-- ============================================================================
-- The iteration distribution
-- ============================================================================

/-- The PMF on `FrontierCfg S` after `k` frontier iteration steps. -/
noncomputable def iterDist (S : Struct Player n) (sem : Sem S)
    (pol : Policy S) (k : Nat) : PMF (FrontierCfg S) :=
  Nat.iterate (fun d => d.bind (frontierStepPol S sem pol)) k
    (PMF.pure (initialCfg S))

/-- `initialCfg S` equals `cfgOfAssign S a ∅` for any `a`. -/
theorem initialCfg_eq_cfgOfAssign (S : Struct Player n) (a : TAssign S) :
    initialCfg S = cfgOfAssign S a ∅ := by
  simp only [initialCfg, cfgOfAssign]
  congr 1
  funext ⟨nd, hnd⟩
  simp at hnd

/-- `layerAssigned` at step 0 is empty. -/
theorem layerAssigned_zero (S : Struct Player n) :
    layerAssigned S 0 = ∅ := rfl

/-- `layerAssigned` at step k+1 is layerAssigned k ∪ frontierOfAssigned S (layerAssigned S k). -/
theorem layerAssigned_succ (S : Struct Player n) (k : Nat) :
    layerAssigned S (k + 1) =
      layerAssigned S k ∪ frontierOfAssigned S (layerAssigned S k) := rfl

/-- Any `FrontierCfg` equals `cfgOfAssign` applied to its own `extractTAssign`
restricted to its assigned set. -/
theorem cfg_eq_cfgOfAssign_extractTAssign (S : Struct Player n)
    (cfg : FrontierCfg S) :
    cfg = cfgOfAssign S (extractTAssign S cfg) cfg.assigned := by
  change cfg = ⟨cfg.assigned, fun ⟨nd, h⟩ => extractTAssign S cfg nd⟩
  cases cfg with
  | mk A v =>
    simp only
    congr 1
    funext ⟨nd, hnd⟩
    simp [extractTAssign, hnd]

-- ============================================================================
-- frontierStepPol pointwise evaluation
-- ============================================================================

open Classical Math.ProbabilityMassFunction Math.PMFProduct in
/-- `frontierStepPol` at a specific output `cfg'`: sum over frontier values
that produce `cfg'`. Since `extendFrontier` is injective on values, this
is either a single product term or zero. -/
theorem frontierStepPol_apply
    (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (cfg cfg' : FrontierCfg S) :
    frontierStepPol S sem pol cfg cfg' =
      ∑' (vals : FrontierValues S cfg),
        if extendFrontier S cfg vals = cfg'
        then pmfPi (nodeDistPol S sem pol cfg) vals
        else 0 := by
  simp only [frontierStepPol, pushforward, PMF.bind_apply, PMF.pure_apply]
  congr 1
  ext vals
  split
  · next h => subst h; simp
  · next h =>
    push_neg at h
    rw [if_neg (Ne.symm h), mul_zero]

-- ============================================================================
-- Main invariant: iterDist characterization
-- ============================================================================

-- ============================================================================
-- frontierStepPol at cfgOfAssign
-- ============================================================================

open Classical Math.ProbabilityMassFunction Math.PMFProduct in
/-- `frontierStepPol` applied to `cfgOfAssign S a A` at
`cfgOfAssign S a (A ∪ frontier)` equals the product of `nodeDist`
over the frontier. -/
theorem frontierStepPol_cfgOfAssign
    (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (a : TAssign S) (A : Finset (Fin n)) :
    frontierStepPol S sem pol (cfgOfAssign S a A)
      (cfgOfAssign S a
        (A ∪ frontier S (cfgOfAssign S a A))) =
    ∏ nd ∈ frontier S (cfgOfAssign S a A),
      (nodeDist S sem pol nd a) (a nd) := by
  rw [frontierStepPol_apply]
  -- The sum has exactly one nonzero term: vals = fun nd => a nd.1
  set cfg := cfgOfAssign S a A
  set F := frontier S cfg
  set target := cfgOfAssign S a (A ∪ F)
  set vals₀ : FrontierValues S cfg := fun nd => a nd.1
  -- extendFrontier cfg vals₀ = target
  have hext : extendFrontier S cfg vals₀ = target :=
    extendFrontier_cfgOfAssign_eq S a A vals₀ (fun _ => rfl)
  -- Only vals₀ can produce target (by injectivity of extendFrontier)
  have honly : ∀ vals : FrontierValues S cfg,
      extendFrontier S cfg vals = target → vals = vals₀ := by
    intro vals heq
    have := extendFrontier_vals_injective S cfg vals vals₀
      (heq.trans hext.symm)
    exact this
  -- Collapse the tsum to the single term at vals₀
  rw [tsum_eq_single vals₀ (fun vals hne => by
    simp [show extendFrontier S cfg vals ≠ target from
      fun h => hne (honly vals h)])]
  simp only [hext, ite_true]
  -- pmfPi gives product: ∏ nd : ↥F, (nodeDistPol cfg nd)(vals₀ nd)
  rw [pmfPi_apply]
  -- Replace nodeDistPol with nodeDist and vals₀ with a
  have hterm : ∀ (nd : ↥F),
      (nodeDistPol S sem pol cfg nd) (vals₀ nd) =
      (nodeDist S sem pol nd.1 a) (a nd.1) := by
    intro nd
    rw [nodeDistPol_cfgOfAssign_eq_nodeDist S sem pol a A nd]
  simp_rw [hterm]
  -- ∏ i : ↥F, (nodeDist i.1 a)(a i.1) = ∏ nd ∈ F, (nodeDist nd a)(a nd)
  exact Finset.prod_coe_sort F
    (fun nd => (nodeDist S sem pol nd a) (a nd))

-- ============================================================================
-- extendFrontier does NOT produce cfgOfAssign when values differ
-- ============================================================================

/-- If `b ≠ a` on some node in `A`, then no extension of `cfgOfAssign S b A`
can equal `cfgOfAssign S a (A ∪ frontier)`. -/
theorem extendFrontier_ne_cfgOfAssign_of_ne
    (S : Struct Player n)
    (a b : TAssign S) (A : Finset (Fin n))
    (hne : ∃ nd ∈ A, b nd ≠ a nd)
    (vals : FrontierValues S (cfgOfAssign S b A)) :
    extendFrontier S (cfgOfAssign S b A) vals ≠
      cfgOfAssign S a
        (A ∪ frontier S (cfgOfAssign S b A)) := by
  obtain ⟨nd, hnd, hv⟩ := hne
  intro heq
  -- Read the value at nd from both sides via extractTAssign
  have hnd_mem : nd ∈
      (extendFrontier S (cfgOfAssign S b A) vals).assigned :=
    Finset.mem_union_left _ hnd
  have h1 : extractTAssign S
      (extendFrontier S (cfgOfAssign S b A) vals) nd = b nd := by
    simp only [extractTAssign, dif_pos hnd_mem]
    exact extendFrontier_preserves_old S _ vals nd hnd _
  have h2 : extractTAssign S
      (cfgOfAssign S a
        (A ∪ frontier S (cfgOfAssign S b A))) nd = a nd := by
    simp only [extractTAssign,
      dif_pos (Finset.mem_union_left _ hnd : nd ∈ _),
      cfgOfAssign]
  rw [heq] at h1
  exact hv (h1.symm.trans h2)

-- ============================================================================
-- Support lemma: iterDist is zero for wrong assigned set
-- ============================================================================

open Classical Math.ProbabilityMassFunction Math.PMFProduct in
/-- Configs in the support of `iterDist k` have
`assigned = layerAssigned S k`. -/
theorem iterDist_assigned (S : Struct Player n) (sem : Sem S)
    (pol : Policy S) (k : Nat) (hk : k ≤ n)
    (cfg : FrontierCfg S)
    (h : iterDist S sem pol k cfg ≠ 0) :
    cfg.assigned = layerAssigned S k := by
  induction k generalizing cfg with
  | zero =>
    simp only [iterDist, Nat.iterate, PMF.pure_apply] at h
    have : cfg = initialCfg S := by
      by_contra hne; exact h (if_neg hne)
    rw [this]; rfl
  | succ k ih =>
    -- iterDist (k+1) = (iterDist k).bind (frontierStepPol ...)
    have hrew : iterDist S sem pol (k + 1) =
        (iterDist S sem pol k).bind
          (frontierStepPol S sem pol) := by
      simp only [iterDist]
      rw [Function.iterate_succ_apply']
    rw [hrew] at h
    rw [PMF.bind_apply] at h
    -- Some term in the tsum is nonzero
    have hne := mt ENNReal.tsum_eq_zero.mpr h
    push_neg at hne
    obtain ⟨cfg', hcfg'⟩ := hne
    have h1 : iterDist S sem pol k cfg' ≠ 0 :=
      left_ne_zero_of_mul hcfg'
    have h2 : frontierStepPol S sem pol cfg' cfg ≠ 0 :=
      right_ne_zero_of_mul hcfg'
    have hassign' := ih (Nat.le_of_succ_le hk) cfg' h1
    -- frontierStepPol cfg' cfg ≠ 0 → ∃ vals, cfg = extend
    rw [frontierStepPol_apply] at h2
    have hne2 := mt ENNReal.tsum_eq_zero.mpr h2
    push_neg at hne2
    obtain ⟨vals, hvals⟩ := hne2
    split_ifs at hvals with heq
    · rw [← heq]
      simp only [extendFrontier, layerAssigned]
      rw [frontier_eq_frontierOfAssigned, hassign']
    · exact absurd rfl hvals

-- ============================================================================
-- Value at the specific config
-- ============================================================================

open Classical Math.ProbabilityMassFunction Math.PMFProduct in
/-- The probability of the specific compatible config at step k. -/
theorem iterDist_at_cfgOfAssign (S : Struct Player n) (sem : Sem S)
    (pol : Policy S) (a : TAssign S)
    (k : Nat) (hk : k ≤ n) :
    iterDist S sem pol k (cfgOfAssign S a (layerAssigned S k)) =
      ∏ nd ∈ layerAssigned S k,
        (nodeDist S sem pol nd a) (a nd) := by
  induction k with
  | zero =>
    simp only [layerAssigned, Finset.prod_empty]
    -- iterDist 0 = PMF.pure (initialCfg S)
    -- cfgOfAssign S a ∅ = initialCfg S
    change PMF.pure (initialCfg S) (cfgOfAssign S a ∅) = 1
    rw [PMF.pure_apply,
      if_pos (initialCfg_eq_cfgOfAssign S a).symm]
  | succ k ih =>
    -- iterDist (k+1) = (iterDist k).bind (frontierStepPol)
    have hrew : iterDist S sem pol (k + 1) =
        (iterDist S sem pol k).bind
          (frontierStepPol S sem pol) := by
      simp only [iterDist]
      rw [Function.iterate_succ_apply']
    rw [hrew, PMF.bind_apply]
    -- The tsum over cfg': only cfgOfAssign S a (layerAssigned S k) contributes
    set Lk := layerAssigned S k
    set Lk1 := layerAssigned S (k + 1)
    set cfg_k := cfgOfAssign S a Lk
    set cfg_k1 := cfgOfAssign S a Lk1
    -- Factor: tsum = iterDist k cfg_k * frontierStepPol cfg_k cfg_k1
    --   (all other terms are 0 because iterDist k is 0 there)
    have honly : ∀ cfg' : FrontierCfg S,
        cfg' ≠ cfg_k →
        iterDist S sem pol k cfg' *
          frontierStepPol S sem pol cfg' cfg_k1 = 0 := by
      intro cfg' hne
      by_cases h0 : iterDist S sem pol k cfg' = 0
      · simp [h0]
      · -- cfg'.assigned = Lk by iterDist_assigned
        have hassign := iterDist_assigned S sem pol k
          (Nat.le_of_succ_le hk) cfg' h0
        -- cfg' differs from cfg_k in values (same assigned set)
        -- Show: frontierStepPol cfg' cfg_k1 = 0
        -- because no extension of cfg' can equal cfg_k1
        suffices hstep : frontierStepPol S sem pol cfg' cfg_k1 = 0 by
          simp [hstep]
        -- cfg' = cfgOfAssign (extractTAssign cfg') Lk
        have hcfg'eq := cfg_eq_cfgOfAssign_extractTAssign S cfg'
        rw [hassign] at hcfg'eq
        set b := extractTAssign S cfg'
        -- b ≠ a on some node in Lk
        have hb_ne : ∃ nd ∈ Lk, b nd ≠ a nd := by
          by_contra hall
          push_neg at hall
          have : cfg' = cfg_k := by
            rw [hcfg'eq]; unfold cfg_k cfgOfAssign; congr 1
            funext ⟨nd, hnd⟩; exact hall nd hnd
          exact hne this
        -- Rewrite cfg' as cfgOfAssign S b Lk
        rw [hcfg'eq]
        -- frontierStepPol (cfgOfAssign b Lk) cfg_k1
        -- Every vals gives extendFrontier ≠ cfg_k1
        rw [frontierStepPol_apply]
        apply ENNReal.tsum_eq_zero.mpr
        intro vals
        split_ifs with heq
        · -- extendFrontier (cfgOfAssign b Lk) vals = cfg_k1
          -- but cfg_k1 = cfgOfAssign a Lk1
          -- frontier S (cfgOfAssign b Lk) = frontier S (cfgOfAssign a Lk)
          -- because both have assigned = Lk
          exfalso
          -- cfg_k1 = cfgOfAssign a Lk1 = cfgOfAssign a (Lk ∪ frontierOfAssigned Lk)
          -- frontier S (cfgOfAssign b Lk) = frontierOfAssigned Lk = frontier S (cfgOfAssign a Lk)
          have hfr_eq : frontier S (cfgOfAssign S b Lk) =
              frontierOfAssigned S Lk := by
            rw [frontier_eq_frontierOfAssigned]; rfl
          have hcfg_k1_eq : cfg_k1 =
              cfgOfAssign S a
                (Lk ∪ frontier S (cfgOfAssign S b Lk)) := by
            simp only [cfg_k1, Lk1, layerAssigned, hfr_eq]
            rfl
          rw [hcfg_k1_eq] at heq
          exact extendFrontier_ne_cfgOfAssign_of_ne S a b Lk
            hb_ne vals heq
        · rfl
    rw [tsum_eq_single cfg_k honly]
    -- Now simplify: iterDist k cfg_k * frontierStepPol cfg_k cfg_k1
    rw [ih (Nat.le_of_succ_le hk)]
    -- frontierStepPol cfg_k cfg_k1 = ∏_{nd ∈ frontier} (nodeDist nd a)(a nd)
    -- First, relate cfg_k1 to extension of cfg_k
    have hfr_eq : frontier S cfg_k = frontierOfAssigned S Lk := by
      rw [frontier_eq_frontierOfAssigned]; rfl
    have hcfg_k1_eq : cfg_k1 =
        cfgOfAssign S a (Lk ∪ frontier S cfg_k) := by
      simp only [cfg_k1, Lk1, layerAssigned, hfr_eq]; rfl
    rw [hcfg_k1_eq, frontierStepPol_cfgOfAssign]
    -- Product over Lk1 = Lk ∪ frontier
    -- Lk and frontier are disjoint
    have hdisj : Disjoint Lk (frontier S cfg_k) := by
      rw [hfr_eq, Finset.disjoint_left]
      intro nd hnd hfr
      simp only [frontierOfAssigned, Finset.mem_filter,
        Finset.mem_univ, true_and] at hfr
      exact hfr.1 hnd
    -- Lk1 = Lk ∪ frontier
    have hLk1 : Lk1 = Lk ∪ frontier S cfg_k := by
      simp only [Lk1, layerAssigned, hfr_eq]; rfl
    rw [hLk1, Finset.prod_union hdisj]

-- ============================================================================
-- Main theorem
-- ============================================================================

open Classical Math.ProbabilityMassFunction Math.PMFProduct in
theorem frontierEval_eq_evalAssignDist
    (S : Struct Player n) (sem : Sem S) (pol : Policy S) :
    frontierEval S sem pol = evalAssignDist S sem pol := by
  -- Rewrite frontierEval in terms of iterDist
  have hfe : frontierEval S sem pol =
      (iterDist S sem pol n).map (extractTAssign S) := by
    simp [frontierEval, iterDist]
  rw [hfe]
  ext a
  rw [PMF.map_apply]
  -- RHS: evalAssignDist a = assignProb a
  change _ = assignProb S sem pol a
  -- Setup
  set cfg₀ := cfgOfAssign S a (layerAssigned S n)
  have hlayer : layerAssigned S n = Finset.univ :=
    layerAssigned_n S
  have hcfg₀ : cfg₀ = cfgOfAssign S a Finset.univ := by
    simp only [cfg₀, hlayer]
  have hext₀ : extractTAssign S cfg₀ = a := by
    rw [hcfg₀]; exact extractTAssign_cfgOfAssign_univ S a
  have hval₀ : iterDist S sem pol n cfg₀ =
      ∏ nd ∈ layerAssigned S n,
        (nodeDist S sem pol nd a) (a nd) :=
    iterDist_at_cfgOfAssign S sem pol a n le_rfl
  have hprod : (∏ nd ∈ layerAssigned S n,
      (nodeDist S sem pol nd a) (a nd)) =
      assignProb S sem pol a := by
    rw [hlayer]; rfl
  -- Only cfg₀ has nonzero contribution to the tsum
  -- (when both extractTAssign = a AND iterDist ≠ 0)
  have hterms : ∀ cfg : FrontierCfg S, cfg ≠ cfg₀ →
      (if a = extractTAssign S cfg
      then iterDist S sem pol n cfg else 0) = 0 := by
    intro cfg hne
    by_cases h0 : iterDist S sem pol n cfg = 0
    · split_ifs <;> simp [h0]
    · -- cfg.assigned = univ, so cfg = cfgOfAssign (extractTAssign cfg) univ
      have hassign := iterDist_assigned S sem pol n le_rfl
        cfg h0
      -- If extractTAssign cfg = a, then cfg = cfgOfAssign a univ = cfg₀
      split_ifs with heq
      · exfalso; apply hne
        rw [cfg_eq_cfgOfAssign_extractTAssign S cfg,
          ← heq, hassign, hlayer, ← hcfg₀]
      · rfl
  -- Rewrite tsum to single term, handling Decidable instance mismatch
  have htsum : (∑' cfg, if a = extractTAssign S cfg
      then iterDist S sem pol n cfg else 0) =
      iterDist S sem pol n cfg₀ := by
    -- Rewrite as a sum with cfg = cfg₀ indicator
    have heq_terms :
        (fun cfg => if a = extractTAssign S cfg
          then iterDist S sem pol n cfg else 0) =
        (fun cfg => if cfg = cfg₀
          then iterDist S sem pol n cfg₀ else 0) := by
      ext cfg
      by_cases h : cfg = cfg₀
      · subst h
        rw [if_pos rfl, if_pos hext₀.symm]
      · rw [if_neg h, hterms cfg h]
    rw [heq_terms, tsum_ite_eq]
  convert htsum.symm ▸ (hval₀.trans hprod) using 1
  congr 1; ext cfg
  exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)

end MAID
