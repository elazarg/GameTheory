import GameTheory.Languages.MAID.CompileObs

/-!
# Frontier lemmas for MAIDs

Structural lemmas about MAID frontiers that support the adequacy proof
(`compiledPR_stepDist_eq_frontierStepPol`).

## Main results

- `frontier_unique_decision_per_player` : under perfect recall, at most one
  decision node per player is in the frontier
- `restrictCfg_proof_irrel` : `restrictCfg` is independent of the subset proof
- `infoset_eq_of_same_node` : two `Infoset` values built from the same node
  and configuration are equal
- `nodeDistPol_at_decision` : at a decision node, `nodeDistPol` equals the
  policy applied to the canonical infoset
-/

namespace MAID

open GameTheory

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

-- ============================================================================
-- Uniqueness of same-player frontier decision nodes
-- ============================================================================

/-- Under perfect recall, two decision nodes of the same player cannot both
be in the frontier. If `d₁ ≠ d₂` are both decision nodes of player `p` in
`frontier S cfg`, then one is an ancestor of the other (by PR condition 1),
and by PR condition 2 the ancestor is an obs-parent (hence parent) of the
descendant, so it must be assigned — contradicting frontier membership. -/
theorem frontier_unique_decision_per_player
    (S : Struct Player n) (hPR : S.PerfectRecall)
    (cfg : FrontierCfg S) (p : Player)
    (d₁ d₂ : Fin n)
    (hf₁ : d₁ ∈ frontier S cfg) (hf₂ : d₂ ∈ frontier S cfg)
    (hk₁ : S.kind d₁ = .decision p) (hk₂ : S.kind d₂ = .decision p) :
    d₁ = d₂ := by
  by_contra hne
  have hcomp := hPR.1 p d₁ d₂ hk₁ hk₂ hne
  have hen₁ : enabled S cfg d₁ := by
    simpa [frontier] using hf₁
  have hen₂ : enabled S cfg d₂ := by
    simpa [frontier] using hf₂
  rcases hcomp with hanc | hanc
  · have ⟨hobs, _⟩ := hPR.2 p d₁ d₂ hk₁ hk₂ hanc
    exact hen₁.1 (hen₂.2 (S.obs_sub d₂ hobs))
  · have ⟨hobs, _⟩ := hPR.2 p d₂ d₁ hk₂ hk₁ hanc
    exact hen₂.1 (hen₁.2 (S.obs_sub d₁ hobs))

-- ============================================================================
-- Proof irrelevance for restrictCfg
-- ============================================================================

/-- `restrictCfg` depends only on `cfg`, `ps`, and the values — not on the
proof that `ps ⊆ cfg.assigned`. -/
theorem restrictCfg_proof_irrel {S : Struct Player n}
    (cfg : FrontierCfg S) (ps : Finset (Fin n))
    (h₁ h₂ : ps ⊆ cfg.assigned) :
    restrictCfg cfg ps h₁ = restrictCfg cfg ps h₂ := by
  funext ⟨nd, hnd⟩
  simp only [restrictCfg]

-- ============================================================================
-- Infoset extensionality
-- ============================================================================

/-- Two `Infoset S p` values are equal when the underlying node is the same
and the observed-parent configuration uses the same `cfg`. The proofs
`hk₁`/`hk₂` and `h₁`/`h₂` may differ, but `restrictCfg` is proof-irrelevant
and `DecisionNode` is a subtype (proof-irrelevant first component). -/
theorem infoset_eq_of_same_node {S : Struct Player n} {p : Player}
    (cfg : FrontierCfg S) (nd : Fin n)
    (hk₁ hk₂ : S.kind nd = .decision p)
    (h₁ h₂ : S.obsParents nd ⊆ cfg.assigned) :
    (⟨⟨nd, hk₁⟩, restrictCfg cfg (S.obsParents nd) h₁⟩ : Infoset S p) =
    ⟨⟨nd, hk₂⟩, restrictCfg cfg (S.obsParents nd) h₂⟩ := by
  have hk_eq : hk₁ = hk₂ := Subsingleton.elim _ _
  subst hk_eq
  exact congrArg _ (restrictCfg_proof_irrel cfg _ h₁ h₂)

-- ============================================================================
-- nodeDistPol at decision nodes
-- ============================================================================

/-- Helper to extract `enabled` from frontier membership. -/
theorem enabled_of_mem_frontier {S : Struct Player n}
    {cfg : FrontierCfg S} {nd : Fin n} (h : nd ∈ frontier S cfg) :
    enabled S cfg nd := by
  simp only [frontier, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h

/-- At a decision node of player `p`, `nodeDistPol` equals the policy applied
to the canonical infoset built from `restrictCfg`. -/
theorem nodeDistPol_at_decision {S : Struct Player n} (sem : Sem S)
    (pol : Policy S) (cfg : FrontierCfg S)
    (nd : ↥(frontier S cfg)) (p : Player)
    (hk : S.kind nd.1 = .decision p) :
    ∀ (hk' : S.kind nd.1 = .decision p)
      (hobs : S.obsParents nd.1 ⊆ cfg.assigned),
    nodeDistPol S sem pol cfg nd =
      pol p ⟨⟨nd.1, hk'⟩, restrictCfg cfg (S.obsParents nd.1) hobs⟩ := by
  intro hk' hobs
  simp only [nodeDistPol]
  split
  · next hkc => exact absurd (hkc.symm.trans hk) nofun
  · next p' hkd =>
    have hp : p' = p := NodeKind.decision.inj (hkd.symm.trans hk)
    subst hp
    congr 1
  · next hku => exact absurd (hku.symm.trans hk) nofun

/-- If `nd` is a decision node of player `p` in the frontier, then
`frontierActiveInfoset S cfg p` returns `some I` with `I.1.val = nd`. -/
theorem frontierActiveInfoset_of_frontier_decision
    {S : Struct Player n} (hPR : S.PerfectRecall)
    {cfg : FrontierCfg S} {nd : Fin n}
    (hf : nd ∈ frontier S cfg) (p : Player)
    (hk : S.kind nd = .decision p) :
    ∃ I : Infoset S p,
      frontierActiveInfoset S cfg p = some I ∧
      I.1.val = nd := by
  have hen := enabled_of_mem_frontier hf
  let hObs : S.obsParents nd ⊆ cfg.assigned := fun x hx => hen.2 (S.obs_sub nd hx)
  let I₀ : Infoset S p := ⟨⟨nd, hk⟩, restrictCfg cfg _ hObs⟩
  have hMem : I₀ ∈ frontierInfosets S cfg p := by
    simp only [frontierInfosets, List.mem_filterMap]
    exact ⟨nd, Finset.mem_toList.mpr hf, by
      simp only [hf, dite_true]; split
      · next q hkq =>
        have : q = p := NodeKind.decision.inj (hkq.symm.trans hk)
        subst this
        simp [reduceDIte]
        simp_all only [I₀]
      · next h => exact absurd h (by rw [hk]; exact Not.imp (h p) fun a ↦ hk)⟩
  -- frontierInfosets is nonempty, so head? = some J for some J in the list
  simp only [frontierActiveInfoset]
  match hhead : (frontierInfosets S cfg p) with
  | [] =>
    exfalso
    simp_all only [List.not_mem_nil, I₀]
  | J :: _ =>
    exact ⟨J, rfl, by
      -- J ∈ frontierInfosets, extract that J.1.val is a decision node of p in frontier
      have hJmem : J ∈ frontierInfosets S cfg p := hhead ▸ List.mem_cons_self
      simp only [frontierInfosets, List.mem_filterMap] at hJmem
      obtain ⟨nd', hnd'_mem, hnd'_val⟩ := hJmem
      have hnd'_fr : nd' ∈ frontier S cfg := Finset.mem_toList.mp hnd'_mem
      simp only [hnd'_fr, dite_true] at hnd'_val
      revert hnd'_val; intro hnd'_val
      split at hnd'_val
      · next q hkq =>
        by_cases hq : q = p
        · simp only [hq, ↓reduceDIte] at hnd'_val
          have := (Option.some_injective _ hnd'_val).symm
          rw [show J.1.val = nd' from by rw [this]]
          exact frontier_unique_decision_per_player S hPR cfg p nd' nd
            hnd'_fr hf (hq ▸ hkq) hk
        · simp_all only [List.mem_cons, Finset.mem_toList, ↓reduceDIte, reduceCtorEq, I₀]
      · simp at hnd'_val⟩

/-- Stronger form: the active infoset is exactly the canonical one built from `restrictCfg`. -/
theorem frontierActiveInfoset_eq_canonical
    {S : Struct Player n} (hPR : S.PerfectRecall)
    {cfg : FrontierCfg S} {nd : Fin n}
    (hf : nd ∈ frontier S cfg) (p : Player)
    (hk : S.kind nd = .decision p)
    (hobs : S.obsParents nd ⊆ cfg.assigned) :
    frontierActiveInfoset S cfg p =
      some ⟨⟨nd, hk⟩, restrictCfg cfg (S.obsParents nd) hobs⟩ := by
  -- Build the canonical infoset
  set I_nd : Infoset S p := ⟨⟨nd, hk⟩, restrictCfg cfg (S.obsParents nd) hobs⟩
  -- Show I_nd ∈ frontierInfosets
  have hMem : I_nd ∈ frontierInfosets S cfg p := by
    simp only [frontierInfosets, List.mem_filterMap]
    exact ⟨nd, Finset.mem_toList.mpr hf, by
      simp only [hf, dite_true]; split
      · next q hkq =>
        have : q = p := NodeKind.decision.inj (hkq.symm.trans hk)
        subst this
        simp [reduceDIte]
        simp_all only [I_nd]
      · next h => exact absurd h (by rw [hk]; exact Not.imp (h p) fun a => hk)⟩
  -- frontierInfosets is nonempty, head? = some J for J in the list
  simp only [frontierActiveInfoset]
  match hhead : (frontierInfosets S cfg p) with
  | [] => exfalso; simp_all only [List.not_mem_nil, I_nd]
  | J :: _ =>
    -- J is the head, and under PR there's only one decision node of p
    -- So J.1.val = nd (by uniqueness), and J.2 = restrictCfg (from construction)
    have hJmem : J ∈ frontierInfosets S cfg p := hhead ▸ .head _
    simp only [frontierInfosets, List.mem_filterMap] at hJmem
    obtain ⟨nd', hnd'_mem, hnd'_val⟩ := hJmem
    have hnd'_fr : nd' ∈ frontier S cfg := Finset.mem_toList.mp hnd'_mem
    simp only [hnd'_fr, dite_true] at hnd'_val
    revert hnd'_val; intro hnd'_val
    split at hnd'_val
    · next q hkq =>
      by_cases hq : q = p
      · simp only [hq, ↓reduceDIte] at hnd'_val
        have hJeq := (Option.some_injective _ hnd'_val).symm
        -- J = ⟨⟨nd', hkq'⟩, restrictCfg cfg _ _⟩ (from the filterMap construction)
        -- J.1.val = nd' and nd' = nd (by uniqueness)
        have hnd'eq := frontier_unique_decision_per_player S hPR cfg p nd' nd
          hnd'_fr hf (hq ▸ hkq) hk
        -- J is constructed with restrictCfg at nd', which equals nd
        -- The returned infoset IS restrictCfg by construction
        -- J = ⟨⟨nd', hkq'⟩, restrictCfg ...⟩ from the filterMap
        -- nd' = nd by uniqueness. Both are restrictCfg so they match.
        subst hnd'eq; subst hJeq
        simp only [List.head?_cons, I_nd]
      · simp only [hq, ↓reduceDIte] at hnd'_val; exact absurd hnd'_val nofun
    · simp at hnd'_val

end MAID
