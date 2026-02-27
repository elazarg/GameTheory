import GameTheory.MAID
import GameTheory.EFG

/-!
# MAID → EFG Reduction

Converts a typed MAID (`GameTheory.MAID`) into an extensive-form game (`GameTheory.EFG`)
by unrolling the topological order into a game tree.

## Sections
- § 1. InfoStructure from MAID
- § 2. Tree construction
- § 3. EFGGame from MAID
- § 4. Strategy correspondence
- § 5. Evaluation equivalence
- § 6. KernelGame equivalence
- § 7. Perfect recall
-/

namespace MAID_EFG

open MAID EFG

-- ============================================================================
-- InfoStructure from MAID
-- ============================================================================

variable {m n : Nat}

/-- Build an `EFG.InfoStructure` from a MAID structure. -/
noncomputable def maidInfoS (S : MAID.Struct (Fin m) n) :
    EFG.InfoStructure where
  n := m
  Infoset := MAID.Infoset S
  arity := fun _ I => S.domainSize I.1.val
  arity_pos := fun _ I => S.dom_pos I.1.val

-- ============================================================================
-- Tree construction
-- ============================================================================

/-- Build a game tree by walking the MAID's topological order.
    - Chance nodes → `GameTree.chance`
    - Decision nodes → `GameTree.decision`
    - Utility nodes → skipped (domain size 1, assign 0) -/
noncomputable def buildTree (S : MAID.Struct (Fin m) n)
    (sem : MAID.Sem S) (pol : MAID.Policy S)
    (nodes : List (Fin n)) (assign : MAID.TAssign S) :
    EFG.GameTree (maidInfoS S) (MAID.TAssign S) :=
  match nodes with
  | [] => .terminal assign
  | nd :: rest =>
    match hk : S.kind nd with
    | .chance =>
      .chance (S.domainSize nd)
        (sem.chanceCPD ⟨nd, hk⟩ (MAID.projCfg assign (S.parents nd)))
        (S.dom_pos nd)
        (fun v => buildTree S sem pol rest (MAID.updateAssign assign nd v))
    | .decision p =>
      .decision (S := maidInfoS S) (p := p)
        (⟨⟨nd, hk⟩, MAID.projCfg assign (S.obsParents nd)⟩ : MAID.Infoset S p)
        (fun v => buildTree S sem pol rest (MAID.updateAssign assign nd v))
    | .utility _ =>
      buildTree S sem pol rest
        (MAID.updateAssign assign nd ⟨0, by rw [S.utility_domain nd _ hk]; exact Nat.one_pos⟩)

-- ============================================================================
-- EFGGame from MAID
-- ============================================================================

/-- Convert a MAID to an extensive-form game. -/
noncomputable def maidToEFG (S : MAID.Struct (Fin m) n) (sem : MAID.Sem S)
    (pol : MAID.Policy S) :
    EFG.EFGGame where
  inf := maidInfoS S
  Outcome := MAID.TAssign S
  tree := buildTree S sem pol S.topoOrder (MAID.defaultAssign S)
  utility := fun a => MAID.utilityOf S sem a

-- ============================================================================
-- Strategy correspondence
-- ============================================================================

/-- Convert a MAID policy to an EFG behavioral profile.
    After unification of `Infoset`, this is the identity. -/
noncomputable def toEFGProfile {S : MAID.Struct (Fin m) n}
    (pol : MAID.Policy S) : EFG.BehavioralProfile (maidInfoS S) :=
  fun p I => pol p I

/-- Convert an EFG behavioral profile back to a MAID policy.
    After unification of `Infoset`, this is the identity. -/
noncomputable def fromEFGProfile {S : MAID.Struct (Fin m) n}
    (σ : EFG.BehavioralProfile (maidInfoS S)) : MAID.Policy S :=
  fun p I => σ p I

theorem toFrom {S : MAID.Struct (Fin m) n}
    (σ : EFG.BehavioralProfile (maidInfoS S)) :
    toEFGProfile (fromEFGProfile σ) = σ := rfl

theorem fromTo {S : MAID.Struct (Fin m) n}
    (pol : MAID.Policy S) :
    fromEFGProfile (toEFGProfile pol) = pol := rfl

-- ============================================================================
-- Evaluation equivalence
-- ============================================================================

/-- `nodeDist` at a chance node. -/
private theorem nodeDist_chance {S : MAID.Struct (Fin m) n} (sem : MAID.Sem S)
    (pol : MAID.Policy S) (nd : Fin n) (assign : MAID.TAssign S)
    (hk : S.kind nd = .chance) :
    MAID.nodeDist S sem pol nd assign =
    sem.chanceCPD ⟨nd, hk⟩ (MAID.projCfg assign (S.parents nd)) := by
  unfold MAID.nodeDist
  split
  · rfl
  · next p hk' => exact nomatch hk.symm.trans hk'
  · next a hk' => exact nomatch hk.symm.trans hk'

/-- `nodeDist` at a decision node. -/
private theorem nodeDist_decision {S : MAID.Struct (Fin m) n} (sem : MAID.Sem S)
    (pol : MAID.Policy S) (nd : Fin n) (assign : MAID.TAssign S)
    (p : Fin m) (hk : S.kind nd = .decision p) :
    MAID.nodeDist S sem pol nd assign =
    pol p ⟨⟨nd, hk⟩, MAID.projCfg assign (S.obsParents nd)⟩ := by
  unfold MAID.nodeDist
  split
  · next hk' => exact nomatch hk.symm.trans hk'
  · next p' hk' =>
    have hp : p' = p := by injection hk'.symm.trans hk
    subst hp; rfl
  · next a hk' => exact nomatch hk.symm.trans hk'

/-- `nodeDist` at a utility node is a point mass at 0. -/
private theorem nodeDist_utility {S : MAID.Struct (Fin m) n} (sem : MAID.Sem S)
    (pol : MAID.Policy S) (nd : Fin n) (assign : MAID.TAssign S)
    (a : Fin m) (hk : S.kind nd = .utility a) :
    MAID.nodeDist S sem pol nd assign =
    PMF.pure ⟨0, by rw [S.utility_domain nd a hk]; exact Nat.one_pos⟩ := by
  unfold MAID.nodeDist
  split
  · next hk' => exact nomatch hk.symm.trans hk'
  · next p hk' => exact nomatch hk.symm.trans hk'
  · next a' hk' =>
    have ha : a' = a := by injection hk'.symm.trans hk
    subst ha; rfl

/-- `evalStep` on a `PMF.pure` reduces to `nodeDist.bind`. -/
private theorem evalStep_pure {S : MAID.Struct (Fin m) n} (sem : MAID.Sem S)
    (pol : MAID.Policy S) (assign : MAID.TAssign S) (nd : Fin n) :
    MAID.evalStep S sem pol (PMF.pure assign) nd =
    (MAID.nodeDist S sem pol nd assign).bind
      (fun v => PMF.pure (MAID.updateAssign assign nd v)) := by
  simp [MAID.evalStep]

/-- `evalStep` distributes over `PMF.bind`. -/
theorem evalStep_bind {S : MAID.Struct (Fin m) n} {α : Type}
    (sem : MAID.Sem S) (pol : MAID.Policy S)
    (d : PMF α) (f : α → PMF (MAID.TAssign S)) (nd : Fin n) :
    MAID.evalStep S sem pol (d.bind f) nd =
    d.bind (fun x => MAID.evalStep S sem pol (f x) nd) := by
  simp [MAID.evalStep, PMF.bind_bind]

/-- `foldl evalStep` distributes over `PMF.bind`. -/
theorem foldl_evalStep_bind {S : MAID.Struct (Fin m) n} {α : Type}
    (sem : MAID.Sem S) (pol : MAID.Policy S)
    (nodes : List (Fin n)) (d : PMF α) (f : α → PMF (MAID.TAssign S)) :
    nodes.foldl (MAID.evalStep S sem pol) (d.bind f) =
    d.bind (fun x => nodes.foldl (MAID.evalStep S sem pol) (f x)) := by
  induction nodes generalizing d f with
  | nil => simp
  | cons nd rest ih =>
    simp only [List.foldl_cons]
    rw [evalStep_bind]
    exact ih _ (fun x => MAID.evalStep S sem pol (f x) nd)

/-- Main lemma: tree `evalDist` equals MAID `foldl evalStep`. -/
theorem buildTree_evalDist {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S)
    (nodes : List (Fin n)) (assign : MAID.TAssign S) :
    (buildTree S sem pol nodes assign).evalDist (toEFGProfile pol) =
    nodes.foldl (MAID.evalStep S sem pol) (PMF.pure assign) := by
  induction nodes generalizing assign with
  | nil => simp [buildTree]
  | cons nd rest ih =>
    simp only [List.foldl_cons]
    unfold buildTree
    split
    · -- chance
      next hk =>
      simp only [EFG.evalDist_chance]
      rw [evalStep_pure, nodeDist_chance sem pol nd assign hk, foldl_evalStep_bind]
      congr 1
      funext v
      exact ih (MAID.updateAssign assign nd v)
    · -- decision p
      next p hk =>
      simp only [EFG.evalDist_decision]
      rw [evalStep_pure, nodeDist_decision sem pol nd assign p hk, foldl_evalStep_bind]
      congr 1
      funext v
      exact ih (MAID.updateAssign assign nd v)
    · -- utility
      next a hk =>
      rw [evalStep_pure, nodeDist_utility sem pol nd assign a hk, PMF.pure_bind]
      exact ih _

/-- Corollary: the EFG tree's outcome distribution matches the MAID's. -/
theorem maid_efg_evalDist {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S) :
    (maidToEFG S sem pol).tree.evalDist (toEFGProfile pol) =
    MAID.evalAssignDist S sem pol := by
  exact buildTree_evalDist sem pol S.topoOrder (MAID.defaultAssign S)

-- ============================================================================
-- KernelGame equivalence
-- ============================================================================

/-- The outcome kernels of the MAID and EFG KernelGames agree under strategy correspondence. -/
theorem maidToEFG_outcomeKernel {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S) :
    (maidToEFG S sem pol).toKernelGame.outcomeKernel (toEFGProfile pol) =
    (MAID.toKernelGame S sem).outcomeKernel pol := by
  simp only [EFG.EFGGame.toKernelGame, MAID.toKernelGame]
  exact maid_efg_evalDist sem pol

-- ============================================================================
-- Perfect recall
-- ============================================================================

/-- Stability: the info set's observation at `nd'` not in `nodes` equals `assign nd'`. -/
private theorem buildTree_obs_stable
    {S : MAID.Struct (Fin m) n} (sem : MAID.Sem S) (pol : MAID.Policy S)
    (nodes : List (Fin n)) (assign : MAID.TAssign S)
    {h : List (EFG.HistoryStep (maidInfoS S))}
    {p : Fin m} {I : MAID.Infoset S p}
    {next : (maidInfoS S).Act I → EFG.GameTree (maidInfoS S) (MAID.TAssign S)}
    (hr : EFG.ReachBy h (buildTree S sem pol nodes assign) (.decision I next))
    {nd' : Fin n} (hnd' : nd' ∈ S.obsParents I.1.val) (hnd'_not : nd' ∉ nodes) :
    I.2 ⟨nd', hnd'⟩ = assign nd' := by
  induction nodes generalizing assign h with
  | nil => simp only [buildTree] at hr; nomatch hr
  | cons nd rest ih =>
    have hnd'_ne : nd' ≠ nd := by
      intro heq; exact hnd'_not (List.mem_cons.mpr (.inl heq))
    have hnd'_rest : nd' ∉ rest := fun hmem =>
      hnd'_not (List.mem_cons.mpr (.inr hmem))
    unfold buildTree at hr
    split at hr
    · next hk =>
      obtain ⟨b, _, rfl, hr'⟩ := EFG.ReachBy_chance_inv' hr
      rw [ih (MAID.updateAssign assign nd b) hr' hnd'_rest,
          MAID.updateAssign_get_ne assign nd nd' b hnd'_ne]
    · next q hk =>
      cases EFG.ReachBy_decision_inv hr with
      | inl heq =>
        obtain ⟨_, hp, hI, _⟩ := heq; subst hp
        have hIeq := eq_of_heq hI; subst hIeq
        simp [MAID.projCfg]
      | inr hex =>
        obtain ⟨a, _, rfl, hr'⟩ := hex
        rw [ih (MAID.updateAssign assign nd a) hr' hnd'_rest,
            MAID.updateAssign_get_ne assign nd nd' a hnd'_ne]
    · next a hk =>
      rw [ih (MAID.updateAssign assign nd _) hr hnd'_rest,
          MAID.updateAssign_get_ne assign nd nd' _ hnd'_ne]

/-- If `ReachBy` reaches a decision node from `buildTree ... nodes ...`,
    then the decision node is in `nodes`. -/
private theorem buildTree_decNode_mem
    {S : MAID.Struct (Fin m) n} (sem : MAID.Sem S) (pol : MAID.Policy S)
    (nodes : List (Fin n)) (assign : MAID.TAssign S)
    {h : List (EFG.HistoryStep (maidInfoS S))}
    {p : Fin m} {I : MAID.Infoset S p}
    {next : (maidInfoS S).Act I → EFG.GameTree (maidInfoS S) (MAID.TAssign S)}
    (hr : EFG.ReachBy h (buildTree S sem pol nodes assign) (.decision I next)) :
    I.1.val ∈ nodes := by
  induction nodes generalizing assign h with
  | nil => simp only [buildTree] at hr; nomatch hr
  | cons nd rest ih =>
    unfold buildTree at hr
    split at hr
    · obtain ⟨_, _, rfl, hr'⟩ := EFG.ReachBy_chance_inv' hr
      exact List.mem_cons.mpr (.inr (ih _ hr'))
    · next q hk =>
      cases EFG.ReachBy_decision_inv hr with
      | inl heq =>
        obtain ⟨_, hp, hI, _⟩ := heq; subst hp
        have hIeq := eq_of_heq hI; subst hIeq
        exact List.mem_cons.mpr (.inl rfl)
      | inr hex =>
        obtain ⟨_, _, rfl, hr'⟩ := hex
        exact List.mem_cons.mpr (.inr (ih _ hr'))
    · exact List.mem_cons.mpr (.inr (ih _ hr))

/-- Transport `getElem` across a list equality. -/
private lemma getElem_eq_of_eq {α : Type*} {l₁ l₂ : List α} (h : l₁ = l₂)
    (i : Nat) (h₁ : i < l₁.length) (h₂ : i < l₂.length) :
    l₁[i]'h₁ = l₂[i]'h₂ := by subst h; rfl

/-- In a suffix `nd :: rest` of the topo order, `nd` precedes any `nd' ∈ rest`. -/
private theorem suffix_topo_order
    {S : MAID.Struct (Fin m) n}
    {nd : Fin n} {rest : List (Fin n)}
    (hsuffix : ∃ done, S.topoOrder = done ++ (nd :: rest))
    {nd' : Fin n} (hnd' : nd' ∈ rest) :
    ∃ i₁ i₂ : Fin S.topoOrder.length,
      S.topoOrder[i₁] = nd ∧ S.topoOrder[i₂] = nd' ∧ i₁.val < i₂.val := by
  obtain ⟨done, hsuf⟩ := hsuffix
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hnd'
  have hlen_eq := congr_arg List.length hsuf
  -- Element equalities on the concrete list
  have hlt1' : done.length < (done ++ nd :: rest).length := by simp
  have hlt2' : done.length + 1 + k.val < (done ++ nd :: rest).length := by
    simp; have := k.isLt; omega
  have he1 : (done ++ nd :: rest)[done.length]'hlt1' = nd := by
    simp [List.getElem_append_right (Nat.le_refl done.length)]
  have he2 : (done ++ nd :: rest)[done.length + 1 + k.val]'hlt2' = nd' := by
    simp only [List.getElem_append_right (show done.length ≤ done.length + 1 + k.val by omega)]
    simp only [show done.length + 1 + k.val - done.length = k.val + 1 from by omega,
               List.getElem_cons_succ]
    exact hk
  -- Bounds in S.topoOrder
  have hlt1 : done.length < S.topoOrder.length := by omega
  have hlt2 : done.length + 1 + k.val < S.topoOrder.length := by
    have := k.isLt; omega
  refine ⟨⟨done.length, hlt1⟩, ⟨done.length + 1 + k.val, hlt2⟩, ?_, ?_, by simp; omega⟩
  · exact (getElem_eq_of_eq hsuf _ hlt1 hlt1').trans he1
  · exact (getElem_eq_of_eq hsuf _ hlt2 hlt2').trans he2

/-- Obs parents of `nd` are not in the suffix `nd :: rest` of the topo order. -/
private theorem obsParents_not_in_suffix
    {S : MAID.Struct (Fin m) n}
    {nd : Fin n} {rest : List (Fin n)}
    (hsuffix : ∃ done, S.topoOrder = done ++ (nd :: rest)) :
    ∀ nd' ∈ S.obsParents nd, nd' ∉ (nd :: rest) := by
  intro nd' hnd'_obs hmem
  obtain ⟨done, hsuf⟩ := hsuffix
  have hnd'_par := S.obs_sub nd hnd'_obs
  have hnodup : (done ++ (nd :: rest)).Nodup := hsuf ▸ S.topo_nodup
  -- Index of nd in topoOrder is done.length
  have hlt_nd : done.length < S.topoOrder.length := by
    rw [congr_arg List.length hsuf]; simp
  have hlt_nd' : done.length < (done ++ (nd :: rest)).length := by simp
  have hnd_at : S.topoOrder[done.length]'hlt_nd = nd := by
    rw [getElem_eq_of_eq hsuf _ hlt_nd hlt_nd']
    simp [List.getElem_append_right (Nat.le_refl done.length)]
  -- topo_acyclic: nd' (a parent of nd) is at index j < done.length
  have hnd'_par' : nd' ∈ S.parents (S.topoOrder[done.length]'hlt_nd) := by
    rw [hnd_at]; exact hnd'_par
  obtain ⟨j, hj_lt, hj_eq⟩ := S.topo_acyclic ⟨done.length, hlt_nd⟩ nd' hnd'_par'
  have hj_done : j.val < done.length := hj_lt
  -- nd' is in done (at index j.val < done.length)
  have hnd'_eq : nd' = done[j.val]'hj_done := by
    have := calc done[j.val]'hj_done
        = (done ++ (nd :: rest))[j.val]'(by omega) := (List.getElem_append_left ..).symm
      _ = S.topoOrder[j.val]'j.isLt := (getElem_eq_of_eq hsuf _ j.isLt (by omega)).symm
      _ = nd' := hj_eq
    exact this.symm
  have hnd'_done : nd' ∈ done := hnd'_eq ▸ List.getElem_mem ..
  exact List.disjoint_of_nodup_append hnodup hnd'_done hmem

/-- Cross-tree player history agreement. -/
private theorem buildTree_playerHistory_eq
    {S : MAID.Struct (Fin m) n} (sem : MAID.Sem S) (pol : MAID.Policy S)
    (hpr : MAID.Struct.PerfectRecall S)
    (nodes : List (Fin n)) (hnodup : nodes.Nodup)
    (hsuffix : ∃ done, S.topoOrder = done ++ nodes)
    (assign₁ assign₂ : MAID.TAssign S)
    {p : Fin m} {I : MAID.Infoset S p}
    (hagree : ∀ nd', nd' ∉ nodes →
      nd' ∈ S.obsParents I.1.val → assign₁ nd' = assign₂ nd')
    {h₁ h₂ : List (EFG.HistoryStep (maidInfoS S))}
    {next₁ next₂ : (maidInfoS S).Act I → EFG.GameTree (maidInfoS S) (MAID.TAssign S)}
    (hr₁ : EFG.ReachBy h₁ (buildTree S sem pol nodes assign₁) (.decision I next₁))
    (hr₂ : EFG.ReachBy h₂ (buildTree S sem pol nodes assign₂) (.decision I next₂)) :
    EFG.playerHistory (maidInfoS S) p h₁ = EFG.playerHistory (maidInfoS S) p h₂ := by
  induction nodes generalizing assign₁ assign₂ h₁ h₂ next₁ next₂ with
  | nil => simp only [buildTree] at hr₁; nomatch hr₁
  | cons nd rest ih =>
    have hnd_nodup : nd ∉ rest := (List.nodup_cons.mp hnodup).1
    have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
    have hsuffix_rest : ∃ done, S.topoOrder = done ++ rest := by
      obtain ⟨done, hsuf⟩ := hsuffix
      exact ⟨done ++ [nd], by rw [hsuf]; simp [List.append_assoc]⟩
    -- Standard hagree transfer: when nd' = nd use stability, otherwise use hagree
    have mk_hagree' : ∀ (a₁ a₂ : MAID.Val S nd),
        (∀ {rh₁' rh₂' : List (EFG.HistoryStep (maidInfoS S))}
           {nx₁ nx₂ : (maidInfoS S).Act I →
             EFG.GameTree (maidInfoS S) (MAID.TAssign S)},
         EFG.ReachBy rh₁' (buildTree S sem pol rest
           (MAID.updateAssign assign₁ nd a₁))
           (.decision I nx₁) →
         EFG.ReachBy rh₂' (buildTree S sem pol rest
           (MAID.updateAssign assign₂ nd a₂))
           (.decision I nx₂) →
         EFG.playerHistory (maidInfoS S) p rh₁' =
           EFG.playerHistory (maidInfoS S) p rh₂') := by
      intro a₁ a₂ rh₁' rh₂' nx₁ nx₂ hrr₁ hrr₂
      apply ih hrest_nodup hsuffix_rest _ _ _ hrr₁ hrr₂
      intro nd' hnd'_rest hnd'_obs
      by_cases hne : nd' = nd
      · subst hne  -- nd is now nd'
        rw [MAID.updateAssign_get_self, MAID.updateAssign_get_self]
        have hstab₁ := buildTree_obs_stable sem pol rest
          (MAID.updateAssign assign₁ nd' a₁) hrr₁ hnd'_obs hnd'_rest
        have hstab₂ := buildTree_obs_stable sem pol rest
          (MAID.updateAssign assign₂ nd' a₂) hrr₂ hnd'_obs hnd'_rest
        rw [MAID.updateAssign_get_self] at hstab₁ hstab₂
        rw [← hstab₁, hstab₂]
      · rw [MAID.updateAssign_get_ne _ _ _ _ hne, MAID.updateAssign_get_ne _ _ _ _ hne]
        exact hagree nd' (fun h => (List.mem_cons.mp h).elim (fun e => hne e) hnd'_rest) hnd'_obs
    unfold buildTree at hr₁ hr₂
    split at hr₁ <;> [skip; skip; skip]
    · -- chance node
      next hk =>
      split at hr₂
      · obtain ⟨b₁, _, rfl, hr₁'⟩ := EFG.ReachBy_chance_inv' hr₁
        obtain ⟨b₂, _, rfl, hr₂'⟩ := EFG.ReachBy_chance_inv' hr₂
        simp only [EFG.playerHistory]
        exact mk_hagree' b₁ b₂ hr₁' hr₂'
      · next hk' => exact absurd hk (by rw [hk']; intro h; cases h)
      · next hk' => exact absurd hk (by rw [hk']; intro h; cases h)
    · -- decision node of player q
      next q hk =>
      split at hr₂
      · next hk' => exact absurd hk (by rw [hk']; intro h; cases h)
      · next q' hk' =>
        have hqq' : q = q' := by injection hk.symm.trans hk'
        subst hqq'
        cases EFG.ReachBy_decision_inv hr₁ with
        | inl heq₁ =>
          obtain ⟨rfl, hp₁, hI₁, _⟩ := heq₁
          cases EFG.ReachBy_decision_inv hr₂ with
          | inl heq₂ =>
            obtain ⟨rfl, _, _, _⟩ := heq₂; rfl
          | inr hex₂ =>
            obtain ⟨_, _, rfl, hr₂'⟩ := hex₂
            subst hp₁; have hI₁' := eq_of_heq hI₁; subst hI₁'
            -- After subst, I.1.val = nd, so I.1.val ∉ rest = hnd_nodup
            exact absurd (buildTree_decNode_mem sem pol rest _ hr₂') hnd_nodup
        | inr hex₁ =>
          obtain ⟨a₁, _, rfl, hr₁'⟩ := hex₁
          cases EFG.ReachBy_decision_inv hr₂ with
          | inl heq₂ =>
            obtain ⟨_, hp₂, hI₂, _⟩ := heq₂
            subst hp₂; have hI₂' := eq_of_heq hI₂; subst hI₂'
            exact absurd (buildTree_decNode_mem sem pol rest _ hr₁') hnd_nodup
          | inr hex₂ =>
            obtain ⟨a₂, _, rfl, hr₂'⟩ := hex₂
            simp only [EFG.playerHistory]
            split
            · -- q = p: player p's decision
              next hqp =>
              subst hqp
              -- PerfectRecall: nd (decision of p) precedes I.1.val in topo order
              have hI_rest : I.1.val ∈ rest := buildTree_decNode_mem sem pol rest _ hr₁'
              have htopo := suffix_topo_order hsuffix hI_rest
              have ⟨hnd_obs, hobs_sub⟩ := hpr _ nd I.1.val hk I.1.2 htopo
              -- Show a₁ = a₂ via stability
              have hstab₁ := buildTree_obs_stable sem pol rest
                (MAID.updateAssign assign₁ nd a₁) hr₁' hnd_obs hnd_nodup
              have hstab₂ := buildTree_obs_stable sem pol rest
                (MAID.updateAssign assign₂ nd a₂) hr₂' hnd_obs hnd_nodup
              rw [MAID.updateAssign_get_self] at hstab₁ hstab₂
              have ha : a₁ = a₂ := hstab₁.symm.trans hstab₂
              -- Show projCfg agree (info sets at nd are equal)
              have hcfg : MAID.projCfg assign₁ (S.obsParents nd) =
                           MAID.projCfg assign₂ (S.obsParents nd) := by
                funext ⟨nd', hnd'_obs_nd⟩
                simp only [MAID.projCfg]
                exact hagree nd'
                  (obsParents_not_in_suffix hsuffix nd' hnd'_obs_nd)
                  (hobs_sub hnd'_obs_nd)
              -- Rewrite to make both sides match, then use IH
              subst ha
              congr 1
              · exact Sigma.ext (Sigma.ext rfl (heq_of_eq hcfg)) HEq.rfl
              · exact mk_hagree' a₁ a₁ hr₁' hr₂'
            · -- q ≠ p: not player p's decision
              next hqp =>
              exact mk_hagree' a₁ a₂ hr₁' hr₂'
      · next hk' => exact absurd hk (by rw [hk']; intro h; cases h)
    · -- utility node
      next a hk =>
      split at hr₂
      · next hk' => exact absurd hk (by rw [hk']; intro h; cases h)
      · next hk' => exact absurd hk (by rw [hk']; intro h; cases h)
      · have hdom : 0 < S.domainSize nd := by rw [S.utility_domain nd a hk]; exact Nat.one_pos
        have hagree' : ∀ nd', nd' ∉ rest →
            nd' ∈ S.obsParents I.1.val →
            MAID.updateAssign assign₁ nd ⟨0, hdom⟩ nd' =
              MAID.updateAssign assign₂ nd ⟨0, hdom⟩ nd' := by
          intro nd' hnd'_rest hnd'_obs
          by_cases hne : nd' = nd
          · subst hne; rw [MAID.updateAssign_get_self, MAID.updateAssign_get_self]
          · rw [MAID.updateAssign_get_ne _ _ _ _ hne,
                MAID.updateAssign_get_ne _ _ _ _ hne]
            exact hagree nd'
              (fun h => (List.mem_cons.mp h).elim
                (fun e => hne e) hnd'_rest) hnd'_obs
        exact ih hrest_nodup hsuffix_rest _ _ hagree'
          hr₁ hr₂

/-- The EFG tree built from a MAID with perfect recall has EFG perfect recall. -/
theorem buildTree_perfectRecall {S : MAID.Struct (Fin m) n}
    (hpr : MAID.Struct.PerfectRecall S)
    (sem : MAID.Sem S) (pol : MAID.Policy S) :
    EFG.PerfectRecall (maidToEFG S sem pol).tree := by
  intro h₁ h₂ p I next₁ next₂ hr₁ hr₂
  exact buildTree_playerHistory_eq sem pol hpr S.topoOrder S.topo_nodup
    ⟨[], by simp⟩ (MAID.defaultAssign S) (MAID.defaultAssign S)
    (fun _ _ _ => rfl) hr₁ hr₂

end MAID_EFG
