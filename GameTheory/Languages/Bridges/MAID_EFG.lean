import GameTheory.Languages.MAID.Syntax
import GameTheory.Languages.EFG.Syntax
import GameTheory.Languages.EFG.Kuhn
import GameTheory.Core.GameSimulation
import Mathlib.Logic.Relation

/-!
# MAID → EFG Reduction

Converts a typed MAID (`GameTheory.Languages.MAID.Syntax`) into an extensive-form game
(`GameTheory.Languages.EFG.Syntax`) by unrolling the topological order into a game tree.

## Outline
- InfoStructure from MAID
- Tree construction
- `maidToEFGAt`: EFGGame from MAID at a given topological order
- `maidToEFG`: order-free variant (classically chosen order)
- Strategy correspondence
- Evaluation equivalence
- KernelGame equivalence (bisimulation)
- Order equivalence (`maidToEFGAt_order_bisimulation`)
- Perfect recall preservation
- Kuhn transfer theorems (order-specific and order-free)
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

/-- Convert a MAID to an extensive-form game at a given topological order. -/
noncomputable def maidToEFGAt (S : MAID.Struct (Fin m) n) (sem : MAID.Sem S)
    (pol : MAID.Policy S) (σ : MAID.TopologicalOrder S) :
    EFG.EFGGame where
  inf := maidInfoS S
  Outcome := MAID.TAssign S
  tree := buildTree S sem pol σ.order (MAID.defaultAssign S)
  utility := fun a => MAID.utilityOf S sem a

/-- Convert a MAID to an extensive-form game, using a classically-chosen topological order. -/
noncomputable def maidToEFG (S : MAID.Struct (Fin m) n) (sem : MAID.Sem S)
    (pol : MAID.Policy S) : EFG.EFGGame :=
  maidToEFGAt S sem pol (Classical.choice (MAID.topologicalOrder_exists S))

/-- Convert a MAID to an extensive-form game using an explicit node order.
No correctness assumptions on `order` are required to define it. -/
noncomputable def maidToEFGWithOrder (S : MAID.Struct (Fin m) n) (sem : MAID.Sem S)
    (pol : MAID.Policy S) (order : List (Fin n)) :
    EFG.EFGGame where
  inf := maidInfoS S
  Outcome := MAID.TAssign S
  tree := buildTree S sem pol order (MAID.defaultAssign S)
  utility := fun a => MAID.utilityOf S sem a

@[simp] theorem maidToEFGWithOrder_topoOrder
    (S : MAID.Struct (Fin m) n) (sem : MAID.Sem S) (pol : MAID.Policy S)
    (σ : MAID.TopologicalOrder S) :
    maidToEFGWithOrder S sem pol σ.order = maidToEFGAt S sem pol σ := by
  rfl

-- ============================================================================
-- Strategy correspondence
-- ============================================================================

/-- Sanity: MAID infosets are exactly the infosets used in the induced EFG. -/
@[simp] theorem maidInfoS_infoset_eq {S : MAID.Struct (Fin m) n} (p : Fin m) :
    (maidInfoS S).Infoset p = MAID.Infoset S p := rfl

/-- Sanity: EFG actions at a MAID infoset are exactly MAID node values. -/
@[simp] theorem maidInfoS_act_eq {S : MAID.Struct (Fin m) n}
    {p : Fin m} (I : MAID.Infoset S p) :
    (maidInfoS S).Act I = MAID.Val S I.1.val := rfl

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

/-- Policy spaces are definitionally equivalent under MAID→EFG. -/
noncomputable def policyBehavioralEquiv {S : MAID.Struct (Fin m) n} :
    MAID.Policy S ≃ EFG.BehavioralProfile (maidInfoS S) where
  toFun := toEFGProfile
  invFun := fromEFGProfile
  left_inv := fromTo
  right_inv := toFrom

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

/-- For any explicit node order, evaluating the induced EFG tree equals folding
`evalStep` along that order. -/
theorem maid_efg_evalDist_withOrder {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S) (order : List (Fin n)) :
    (maidToEFGWithOrder S sem pol order).tree.evalDist (toEFGProfile pol) =
      order.foldl (MAID.evalStep S sem pol) (PMF.pure (MAID.defaultAssign S)) := by
  simpa [maidToEFGWithOrder] using
    buildTree_evalDist sem pol order (MAID.defaultAssign S)

-- The following swap infrastructure gives an alternative, algebraic proof of
-- order independence via certified adjacent transpositions. The main order
-- equivalence result (`maidToEFGAt_order_bisimulation`) uses the bisimulation
-- approach instead, but these results are interesting in their own right.

/-- One certified adjacent swap step on node orders.
Swappable adjacent nodes must be distinct and have no direct edge either way. -/
def OrderSwapStep (S : MAID.Struct (Fin m) n) :
    List (Fin n) → List (Fin n) → Prop :=
  fun o o' =>
    ∃ (i : Nat) (hi : i + 1 < o.length) (a b : Fin n),
      o[i]'(by omega) = a ∧
      o[i + 1]'hi = b ∧
      a ≠ b ∧
      MAID.NoDirectEdge S a b ∧
      o' = MAID.swapAdj o i hi

/-- Reachability by repeated certified adjacent swaps. -/
abbrev OrderSwapReachable (S : MAID.Struct (Fin m) n) :
    List (Fin n) → List (Fin n) → Prop :=
  Relation.ReflTransGen (OrderSwapStep S)

/-- MAID fold semantics are invariant under one certified adjacent swap. -/
theorem evalFold_swap_adj_any_order {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S)
    (order : List (Fin n))
    (i : Nat) (hi : i + 1 < order.length) (a b : Fin n)
    (ha : order[i]'(by omega) = a)
    (hb : order[i + 1]'hi = b)
    (hne : a ≠ b)
    (hindep : MAID.NoDirectEdge S a b) :
    order.foldl (MAID.evalStep S sem pol) (PMF.pure (MAID.defaultAssign S)) =
      (MAID.swapAdj order i hi).foldl (MAID.evalStep S sem pol)
        (PMF.pure (MAID.defaultAssign S)) := by
  have hne' : (order[i]'(by omega)) ≠ (order[i + 1]'hi) := by
    simpa [ha, hb] using hne
  have hindep' : MAID.NoDirectEdge S (order[i]'(by omega)) (order[i + 1]'hi) := by
    simpa [ha, hb] using hindep
  exact MAID.foldl_swapAdj _ _ _ i hi
    (fun acc => MAID.evalStep_swap sem pol _ _ hne' hindep' acc)

/-- MAID fold semantics are invariant under any sequence of certified swaps. -/
theorem evalFold_orderSwapReachable {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S)
    {o₁ o₂ : List (Fin n)}
    (hreach : OrderSwapReachable S o₁ o₂) :
    o₁.foldl (MAID.evalStep S sem pol) (PMF.pure (MAID.defaultAssign S)) =
      o₂.foldl (MAID.evalStep S sem pol) (PMF.pure (MAID.defaultAssign S)) := by
  induction hreach with
  | refl =>
      rfl
  | tail hreach hstep ih =>
      rcases hstep with ⟨i, hi, a, b, ha, hb, hne, hindep, rfl⟩
      exact ih.trans (evalFold_swap_adj_any_order sem pol _ i hi a b ha hb hne hindep)

/-- EFG-with-order evaluation is invariant under any sequence of certified swaps. -/
theorem maid_efg_evalDist_orderSwapReachable {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S)
    {o₁ o₂ : List (Fin n)}
    (hreach : OrderSwapReachable S o₁ o₂) :
    (maidToEFGWithOrder S sem pol o₁).tree.evalDist (toEFGProfile pol) =
      (maidToEFGWithOrder S sem pol o₂).tree.evalDist (toEFGProfile pol) := by
  calc
    (maidToEFGWithOrder S sem pol o₁).tree.evalDist (toEFGProfile pol)
        = o₁.foldl (MAID.evalStep S sem pol) (PMF.pure (MAID.defaultAssign S)) := by
            exact maid_efg_evalDist_withOrder sem pol o₁
    _ = o₂.foldl (MAID.evalStep S sem pol) (PMF.pure (MAID.defaultAssign S)) :=
          evalFold_orderSwapReachable sem pol hreach
    _ = (maidToEFGWithOrder S sem pol o₂).tree.evalDist (toEFGProfile pol) := by
          symm
          exact maid_efg_evalDist_withOrder sem pol o₂

/-- Corollary: the EFG tree's outcome distribution matches the MAID's fold-based
evaluation along the same topological order. -/
theorem maid_efg_evalDist_fold_at {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S) (σ : MAID.TopologicalOrder S) :
    (maidToEFGAt S sem pol σ).tree.evalDist (toEFGProfile pol) =
    MAID.evalFold S sem pol σ := by
  exact buildTree_evalDist sem pol σ.order (MAID.defaultAssign S)

/-- The EFG tree's outcome distribution matches the MAID's canonical evaluation. -/
theorem maid_efg_evalDist_at {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S) (σ : MAID.TopologicalOrder S) :
    (maidToEFGAt S sem pol σ).tree.evalDist (toEFGProfile pol) =
    MAID.evalAssignDist S sem pol := by
  rw [MAID.evalAssignDist_eq_evalFold S sem pol σ]
  exact maid_efg_evalDist_fold_at sem pol σ

-- ============================================================================
-- KernelGame equivalence
-- ============================================================================

/-- `buildTree` is independent of the `pol` argument. -/
theorem buildTree_pol_irrel {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol₁ pol₂ : MAID.Policy S)
    (nodes : List (Fin n)) (assign : MAID.TAssign S) :
    buildTree S sem pol₁ nodes assign = buildTree S sem pol₂ nodes assign := by
  induction nodes generalizing assign with
  | nil =>
      simp [buildTree]
  | cons nd rest ih =>
      simp only [buildTree]
      split <;> simp [ih]

/-- `maidToEFGAt` is independent of the `pol` argument. -/
theorem maidToEFGAt_pol_irrel {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol₁ pol₂ : MAID.Policy S) (σ : MAID.TopologicalOrder S) :
    maidToEFGAt S sem pol₁ σ = maidToEFGAt S sem pol₂ σ := by
  refine congrArg
    (fun t => EFG.EFGGame.mk (maidInfoS S) (MAID.TAssign S) t (fun a => MAID.utilityOf S sem a))
    ?_
  exact buildTree_pol_irrel sem pol₁ pol₂ σ.order (MAID.defaultAssign S)

/-- The outcome kernels of the MAID and EFG KernelGames agree under strategy correspondence. -/
theorem maidToEFGAt_outcomeKernel {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S) (σ : MAID.TopologicalOrder S) :
    (maidToEFGAt S sem pol σ).toKernelGame.outcomeKernel (toEFGProfile pol) =
    (MAID.toKernelGame S sem).outcomeKernel pol := by
  simp only [EFG.EFGGame.toKernelGame, MAID.toKernelGame]
  exact maid_efg_evalDist_at sem pol σ

/-- MAID to EFG as a game bisimulation (distribution-preserving equivalence). -/
noncomputable def maidToEFGAt_bisimulation {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol₀ : MAID.Policy S) (σ : MAID.TopologicalOrder S) :
    GameTheory.KernelGame.Bisimulation (MAID.toKernelGame S sem)
      ((maidToEFGAt S sem pol₀ σ).toKernelGame) where
  stratEquiv := fun _ => Equiv.refl _
  udist_preserved := by
    intro pol
    have ht :
        buildTree S sem pol₀ σ.order (MAID.defaultAssign S) =
          buildTree S sem pol σ.order (MAID.defaultAssign S) :=
      buildTree_pol_irrel sem pol₀ pol σ.order (MAID.defaultAssign S)
    have hUd :
        (maidToEFGAt S sem pol₀ σ).toKernelGame.udist (fun i => pol i) =
          (maidToEFGAt S sem pol σ).toKernelGame.udist (toEFGProfile pol) := by
      have hUd' :
          (maidToEFGAt S sem pol₀ σ).toKernelGame.udist (fun i => pol i) =
            (maidToEFGAt S sem pol σ).toKernelGame.udist (fun i => pol i) := by
        simp [GameTheory.KernelGame.udist, EFG.EFGGame.toKernelGame, maidToEFGAt, ht]
      simpa [toEFGProfile] using hUd'
    calc
      (maidToEFGAt S sem pol₀ σ).toKernelGame.udist (fun i => pol i)
          = (maidToEFGAt S sem pol σ).toKernelGame.udist (toEFGProfile pol) := hUd
      _ = (MAID.toKernelGame S sem).udist pol := by
            have hBind := congrArg
              (fun d => d.bind (fun ω => PMF.pure (MAID.utilityOf S sem ω)))
              (maid_efg_evalDist_at sem pol σ)
            simpa [GameTheory.KernelGame.udist, EFG.EFGGame.toKernelGame,
              MAID.toKernelGame, toEFGProfile] using hBind

/-- Forward simulation induced by `maidToEFGAt_bisimulation`. -/
noncomputable def maidToEFGAt_simulation {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol₀ : MAID.Policy S) (σ : MAID.TopologicalOrder S) :
    GameTheory.KernelGame.Simulation (MAID.toKernelGame S sem)
      ((maidToEFGAt S sem pol₀ σ).toKernelGame) :=
  GameTheory.KernelGame.Bisimulation.toSimulation (maidToEFGAt_bisimulation sem pol₀ σ)

/-- The MAID and EFG KernelGames have the same joint utility distribution. -/
theorem maidToEFGAt_udist {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S) (σ : MAID.TopologicalOrder S) :
    (maidToEFGAt S sem pol σ).toKernelGame.udist (toEFGProfile pol) =
      (MAID.toKernelGame S sem).udist pol := by
  simpa [toEFGProfile] using (maidToEFGAt_bisimulation sem pol σ).udist_preserved pol

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
  | nil =>
      simp only [buildTree] at hr
      exact False.elim (EFG.ReachBy_terminal_absurd hr)
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
  | nil =>
      simp only [buildTree] at hr
      exact False.elim (EFG.ReachBy_terminal_absurd hr)
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


/-- The EFG tree built from a MAID with perfect recall has EFG perfect recall.

The proof proceeds by induction on the node list. At each node:
- **Chance/utility**: the player history is unaffected; recurse.
- **Decision (q ≠ p)**: not recorded in player p's history; recurse.
- **Decision (q = p)**: by the strengthened MAID perfect recall (decision ordering +
  observation), `nd` is an ancestor of the target info set's node, so `nd` is
  observed. `buildTree_obs_stable` pins down the action, forcing both paths to
  agree on the recorded (info-set, action) pair. -/
private theorem buildTree_playerHistory_eq
    {S : MAID.Struct (Fin m) n}
    (hpr : MAID.Struct.PerfectRecall S)
    (sem : MAID.Sem S) (pol : MAID.Policy S)
    (nodes : List (Fin n)) (hnodup : nodes.Nodup)
    (horder : ∀ (i j : Fin nodes.length),
      S.IsAncestor nodes[i] nodes[j] → i.val < j.val)
    (assign₁ assign₂ : MAID.TAssign S)
    (p : Fin m) (I : MAID.Infoset S p)
    {next₁ next₂ : (maidInfoS S).Act I → EFG.GameTree (maidInfoS S) (MAID.TAssign S)}
    {h₁ h₂ : List (EFG.HistoryStep (maidInfoS S))}
    (hassign : ∀ nd' ∈ S.obsParents I.1.val, assign₁ nd' = assign₂ nd')
    (hr₁ : EFG.ReachBy h₁ (buildTree S sem pol nodes assign₁) (.decision I next₁))
    (hr₂ : EFG.ReachBy h₂ (buildTree S sem pol nodes assign₂) (.decision I next₂)) :
    EFG.playerHistory (maidInfoS S) p h₁ = EFG.playerHistory (maidInfoS S) p h₂ := by
  induction nodes generalizing assign₁ assign₂ h₁ h₂ with
  | nil =>
    simp only [buildTree] at hr₁
    exact False.elim (EFG.ReachBy_terminal_absurd hr₁)
  | cons nd rest ih =>
    have hnd_notin : nd ∉ rest := (List.nodup_cons.mp hnodup).1
    have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
    have horder_rest : ∀ (i j : Fin rest.length),
        S.IsAncestor rest[i] rest[j] → i.val < j.val := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ hanc
      have hi1 : i + 1 < (nd :: rest).length := by simp [List.length_cons]; omega
      have hj1 : j + 1 < (nd :: rest).length := by simp [List.length_cons]; omega
      have hei : (nd :: rest)[i + 1]'hi1 = rest[i]'hi := List.getElem_cons_succ ..
      have hej : (nd :: rest)[j + 1]'hj1 = rest[j]'hj := List.getElem_cons_succ ..
      have hanc' : S.IsAncestor ((nd :: rest)[i + 1]'hi1) ((nd :: rest)[j + 1]'hj1) := by
        rw [hei, hej]; exact hanc
      have h := horder ⟨i + 1, hi1⟩ ⟨j + 1, hj1⟩ hanc'
      exact Nat.lt_of_succ_lt_succ h
    -- Unfold buildTree in hr₁ and case-split on S.kind nd
    unfold buildTree at hr₁; split at hr₁
    · -- chance node
      next hk =>
      -- Coerce hr₂ to the same match branch
      unfold buildTree at hr₂
      split at hr₂
      · -- chance (matching)
        obtain ⟨b₁, _, rfl, hr₁'⟩ := EFG.ReachBy_chance_inv' hr₁
        obtain ⟨b₂, _, rfl, hr₂'⟩ := EFG.ReachBy_chance_inv' hr₂
        simp only [EFG.playerHistory]
        -- Propagate hassign through updateAssign
        have hassign' : ∀ nd' ∈ S.obsParents I.1.val,
            MAID.updateAssign assign₁ nd b₁ nd' = MAID.updateAssign assign₂ nd b₂ nd' := by
          intro nd' hnd'
          by_cases hne : nd' = nd
          · subst hne
            exact (buildTree_obs_stable sem pol rest _ hr₁' hnd' hnd_notin).symm.trans
              (buildTree_obs_stable sem pol rest _ hr₂' hnd' hnd_notin)
          · rw [MAID.updateAssign_get_ne _ _ _ _ hne, MAID.updateAssign_get_ne _ _ _ _ hne]
            exact hassign nd' hnd'
        exact ih hrest_nodup horder_rest _ _ hassign' hr₁' hr₂'
      · next p' heq => exact nomatch hk.symm.trans heq
      · next a heq => exact nomatch hk.symm.trans heq
    · -- decision node for player q
      next q hk =>
      -- Coerce hr₂ to the same match branch
      unfold buildTree at hr₂
      split at hr₂
      · next heq => exact nomatch hk.symm.trans heq
      · next q' hk' =>
        -- decision (matching): unify q = q'
        have hqq : q = q' := by injection hk.symm.trans hk'
        subst hqq
        -- Invert both ReachBy from decision nodes
        cases EFG.ReachBy_decision_inv hr₁ with
        | inl heq₁ =>
          -- h₁ = []: current node IS info set I
          obtain ⟨rfl, hpq, hI₁, _⟩ := heq₁; subst hpq
          have hIeq := eq_of_heq hI₁; subst hIeq
          cases EFG.ReachBy_decision_inv hr₂ with
          | inl heq₂ => obtain ⟨rfl, _, _, _⟩ := heq₂; rfl
          | inr hex₂ =>
            -- h₂ continues past nd: I.1.val = nd but buildTree_decNode_mem says I.1.val ∈ rest
            obtain ⟨_, _, rfl, hr₂'⟩ := hex₂
            exfalso; exact hnd_notin (buildTree_decNode_mem sem pol rest _ hr₂')
        | inr hex₁ =>
          obtain ⟨a₁, _, rfl, hr₁'⟩ := hex₁
          cases EFG.ReachBy_decision_inv hr₂ with
          | inl heq₂ =>
            -- Symmetric contradiction
            obtain ⟨rfl, hpq, hI₂, _⟩ := heq₂; subst hpq
            have hIeq := eq_of_heq hI₂; subst hIeq
            exfalso; exact hnd_notin (buildTree_decNode_mem sem pol rest _ hr₁')
          | inr hex₂ =>
            -- Both paths take an action at nd and continue
            obtain ⟨a₂, _, rfl, hr₂'⟩ := hex₂
            simp only [EFG.playerHistory]
            split
            · -- q = p: this decision contributes to playerHistory
              next hp =>
              subst hp
              -- nd and I.1.val are both player q's decision nodes, nd ≠ I.1.val
              have hI_mem := buildTree_decNode_mem sem pol rest _ hr₁'
              have hI_ne : I.1.val ≠ nd := fun heq => hnd_notin (heq ▸ hI_mem)
              -- By decision ordering (PR.1), nd is an ancestor of I.1.val
              have hanc : S.IsAncestor nd I.1.val := by
                rcases hpr.1 q nd I.1.val hk I.1.2 hI_ne.symm with h | h
                · exact h
                · -- I.1.val ancestor of nd contradicts topo ordering
                  exfalso
                  obtain ⟨k, hk_lt, hk_eq⟩ := List.mem_iff_getElem.mp hI_mem
                  have hk1 : k + 1 < (nd :: rest).length := by
                    simp only [List.length_cons]; omega
                  have := horder ⟨k + 1, hk1⟩ ⟨0, by simp only [List.length_cons]; omega⟩
                    (by
                      change S.IsAncestor (nd :: rest)[k + 1] (nd :: rest)[0]
                      simp only [List.getElem_cons_succ, List.getElem_cons_zero, hk_eq]
                      exact h)
                  exact absurd this (Nat.not_lt_zero _)
              -- By PR.2, nd ∈ obsParents I.1.val and obsParents nd ⊆ obsParents I.1.val
              have ⟨hnd_obs, hobs_sub⟩ := hpr.2 q nd I.1.val hk I.1.2 hanc
              -- The info sets at nd match (obsParents nd ⊆ obsParents I.1.val, hassign)
              have hobs_eq : ∀ nd' ∈ S.obsParents nd, assign₁ nd' = assign₂ nd' :=
                fun nd' hnd' => hassign nd' (hobs_sub hnd')
              -- The actions match: obs_stable gives I.2 ⟨nd, hnd_obs⟩ = updateAssign ... nd = aᵢ
              have he₁ := buildTree_obs_stable sem pol rest _ hr₁' hnd_obs hnd_notin
              have he₂ := buildTree_obs_stable sem pol rest _ hr₂' hnd_obs hnd_notin
              have ha_eq : a₁ = a₂ := by
                have := he₁.symm.trans he₂
                rwa [MAID.updateAssign_get_self, MAID.updateAssign_get_self] at this
              subst ha_eq
              -- The info set entries match
              have hI_eq : (⟨⟨nd, hk⟩, MAID.projCfg assign₁ (S.obsParents nd)⟩ :
                  MAID.Infoset S q) =
                  ⟨⟨nd, hk⟩, MAID.projCfg assign₂ (S.obsParents nd)⟩ := by
                congr 1; ext ⟨nd', hnd'⟩; simp only [MAID.projCfg]
                exact congrArg _ (hobs_eq nd' hnd')
              simp only [maidInfoS_infoset_eq, maidInfoS_act_eq, List.cons.injEq,
                Sigma.mk.injEq, heq_eq_eq, and_true, true_and, hI_eq]
              -- Propagate hassign through updateAssign
              have hassign' : ∀ nd' ∈ S.obsParents I.1.val,
                  MAID.updateAssign assign₁ nd a₁ nd' =
                  MAID.updateAssign assign₂ nd a₁ nd' := by
                intro nd' hnd'
                by_cases hne : nd' = nd
                · subst hne; simp [MAID.updateAssign]
                · rw [MAID.updateAssign_get_ne _ _ _ _ hne,
                      MAID.updateAssign_get_ne _ _ _ _ hne]
                  exact hassign nd' hnd'
              exact ih hrest_nodup horder_rest _ _ hassign' hr₁' hr₂'
            · -- q ≠ p: no contribution to playerHistory, just recurse
              next hp =>
              -- Same hassign propagation
              have hassign' : ∀ nd' ∈ S.obsParents I.1.val,
                  MAID.updateAssign assign₁ nd a₁ nd' =
                  MAID.updateAssign assign₂ nd a₂ nd' := by
                intro nd' hnd'
                by_cases hne : nd' = nd
                · subst hne
                  exact (buildTree_obs_stable sem pol rest _ hr₁' hnd' hnd_notin).symm.trans
                    (buildTree_obs_stable sem pol rest _ hr₂' hnd' hnd_notin)
                · rw [MAID.updateAssign_get_ne _ _ _ _ hne,
                      MAID.updateAssign_get_ne _ _ _ _ hne]
                  exact hassign nd' hnd'
              exact ih hrest_nodup horder_rest _ _ hassign' hr₁' hr₂'
      · next a' heq => exact nomatch hk.symm.trans heq
    · -- utility node
      next a hk =>
      -- Coerce hr₂ to the same match branch
      unfold buildTree at hr₂
      split at hr₂
      · next heq => exact nomatch hk.symm.trans heq
      · next p' heq => exact nomatch hk.symm.trans heq
      · next a' hk' =>
        -- utility (matching): unify a = a'
        have haa : a = a' := by injection hk.symm.trans hk'
        subst haa
        have hassign' : ∀ nd' ∈ S.obsParents I.1.val,
            MAID.updateAssign assign₁ nd
              ⟨0, by rw [S.utility_domain nd a hk]; exact Nat.one_pos⟩ nd' =
            MAID.updateAssign assign₂ nd
              ⟨0, by rw [S.utility_domain nd a hk]; exact Nat.one_pos⟩ nd' := by
          intro nd' hnd'
          by_cases hne : nd' = nd
          · subst hne; simp [MAID.updateAssign]
          · rw [MAID.updateAssign_get_ne _ _ _ _ hne, MAID.updateAssign_get_ne _ _ _ _ hne]
            exact hassign nd' hnd'
        exact ih hrest_nodup horder_rest _ _ hassign' hr₁ hr₂

theorem buildTree_perfectRecall {S : MAID.Struct (Fin m) n}
    (hpr : MAID.Struct.PerfectRecall S)
    (sem : MAID.Sem S) (pol : MAID.Policy S) (σ : MAID.TopologicalOrder S) :
    EFG.PerfectRecall (maidToEFGAt S sem pol σ).tree := by
  intro h₁ h₂ p I next₁ next₂ hr₁ hr₂
  have horder : ∀ (i j : Fin σ.order.length),
      S.IsAncestor σ.order[i] σ.order[j] → i.val < j.val := by
    intro i j h
    exact σ.ancestor_lt h rfl rfl
  exact buildTree_playerHistory_eq hpr sem pol σ.order σ.nodup horder _ _ p I
    (fun _ _ => rfl) hr₁ hr₂

-- ============================================================================
-- Kuhn transfer (via MAID → EFG)
-- ============================================================================

open GameTheory in
/-- Kuhn (behavioral → mixed) transferred to MAID via the MAID→EFG bridge. -/
theorem kuhn_behavioral_to_mixed_udist_at
    {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S)
    (hpr : MAID.Struct.PerfectRecall S) (σ : MAID.TopologicalOrder S) :
    ∃ μ : PMF (EFG.FlatProfile (maidInfoS S)),
      (MAID.toKernelGame S sem).udist pol =
      μ.bind (fun s =>
        (maidToEFGAt S sem pol σ).toKernelGame.udist (EFG.flatToBehavioral s)) := by
  have hprEFG : EFG.PerfectRecall (maidToEFGAt S sem pol σ).tree :=
    buildTree_perfectRecall hpr sem pol σ
  obtain ⟨μ, hμ⟩ :=
    EFG.kuhn_behavioral_to_mixed_udist
      (G := maidToEFGAt S sem pol σ) (σ := toEFGProfile pol) hprEFG
  refine ⟨μ, ?_⟩
  calc
    (MAID.toKernelGame S sem).udist pol
        = (maidToEFGAt S sem pol σ).toKernelGame.udist (toEFGProfile pol) := by
            symm
            exact maidToEFGAt_udist sem pol σ
    _ = μ.bind (fun s =>
          (maidToEFGAt S sem pol σ).toKernelGame.udist (EFG.flatToBehavioral s)) := hμ.symm

open GameTheory in
/-- Kuhn (mixed → behavioral) transferred to MAID via the MAID→EFG bridge. -/
theorem kuhn_mixed_to_behavioral_udist_at
    {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S)
    (hpr : MAID.Struct.PerfectRecall S) (σ : MAID.TopologicalOrder S)
    (muP : EFG.MixedProfile (maidInfoS S)) :
    ∃ σ' : EFG.BehavioralProfile (maidInfoS S),
      (maidToEFGAt S sem pol σ).toKernelGame.udist σ' =
      (EFG.mixedProfileJoint (S := maidInfoS S) muP).bind
        (fun pi =>
          (maidToEFGAt S sem pol σ).toKernelGame.udist (EFG.pureToBehavioral pi)) := by
  have hprEFG : EFG.PerfectRecall (maidToEFGAt S sem pol σ).tree :=
    buildTree_perfectRecall hpr sem pol σ
  exact EFG.kuhn_mixed_to_behavioral_udist
    (G := maidToEFGAt S sem pol σ) hprEFG muP

-- ============================================================================
-- Order equivalence
-- ============================================================================

/-- Different topological orders produce bisimilar EFG games.
    Composed from the two bisimulations MAID ↔ EFG(σᵢ). -/
noncomputable def maidToEFGAt_order_bisimulation {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S)
    (σ₁ σ₂ : MAID.TopologicalOrder S) :
    GameTheory.KernelGame.Bisimulation
      ((maidToEFGAt S sem pol σ₁).toKernelGame)
      ((maidToEFGAt S sem pol σ₂).toKernelGame) :=
  GameTheory.KernelGame.Bisimulation.comp
    (maidToEFGAt_bisimulation sem pol σ₂)
    (GameTheory.KernelGame.Bisimulation.symm (maidToEFGAt_bisimulation sem pol σ₁))

-- ============================================================================
-- Order-free convenience theorems
-- ============================================================================

/-- MAID to EFG as a game bisimulation (order-free). -/
noncomputable def maidToEFG_bisimulation {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol₀ : MAID.Policy S) :
    GameTheory.KernelGame.Bisimulation (MAID.toKernelGame S sem)
      ((maidToEFG S sem pol₀).toKernelGame) :=
  maidToEFGAt_bisimulation sem pol₀ _

/-- The MAID and order-free EFG KernelGames have the same joint utility distribution. -/
theorem maidToEFG_udist {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S) :
    (maidToEFG S sem pol).toKernelGame.udist (toEFGProfile pol) =
      (MAID.toKernelGame S sem).udist pol :=
  maidToEFGAt_udist sem pol _

/-- The order-free EFG tree built from a MAID with perfect recall has EFG perfect recall. -/
theorem maidToEFG_perfectRecall {S : MAID.Struct (Fin m) n}
    (hpr : MAID.Struct.PerfectRecall S)
    (sem : MAID.Sem S) (pol : MAID.Policy S) :
    EFG.PerfectRecall (maidToEFG S sem pol).tree :=
  buildTree_perfectRecall hpr sem pol _

open GameTheory in
/-- Kuhn (behavioral → mixed) transferred to MAID via the order-free MAID→EFG bridge. -/
theorem kuhn_behavioral_to_mixed_udist
    {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S)
    (hpr : MAID.Struct.PerfectRecall S) :
    ∃ μ : PMF (EFG.FlatProfile (maidInfoS S)),
      (MAID.toKernelGame S sem).udist pol =
      μ.bind (fun s =>
        (maidToEFG S sem pol).toKernelGame.udist (EFG.flatToBehavioral s)) :=
  kuhn_behavioral_to_mixed_udist_at sem pol hpr _

open GameTheory in
/-- Kuhn (mixed → behavioral) transferred to MAID via the order-free MAID→EFG bridge. -/
theorem kuhn_mixed_to_behavioral_udist
    {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S)
    (hpr : MAID.Struct.PerfectRecall S)
    (muP : EFG.MixedProfile (maidInfoS S)) :
    ∃ σ' : EFG.BehavioralProfile (maidInfoS S),
      (maidToEFG S sem pol).toKernelGame.udist σ' =
      (EFG.mixedProfileJoint (S := maidInfoS S) muP).bind
        (fun pi =>
          (maidToEFG S sem pol).toKernelGame.udist (EFG.pureToBehavioral pi)) :=
  kuhn_mixed_to_behavioral_udist_at sem pol hpr _ muP

end MAID_EFG
