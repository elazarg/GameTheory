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
- § 7. Perfect recall (sorry)
-/

namespace MAID_EFG

open MAID EFG

-- ============================================================================
-- § 1. InfoStructure from MAID
-- ============================================================================

variable {m n : Nat}

/-- Fintype instance for `MAID.Cfg S ps` (dependent Pi over Finset subtype). -/
instance instFintypeCfg (S : MAID.Struct (Fin m) n) (ps : Finset (Fin n)) :
    Fintype (MAID.Cfg S ps) :=
  inferInstance

/-- DecidableEq instance for `MAID.Cfg S ps`. -/
instance instDecidableEqCfg (S : MAID.Struct (Fin m) n) (ps : Finset (Fin n)) :
    DecidableEq (MAID.Cfg S ps) :=
  inferInstanceAs (DecidableEq ((nd : ↥ps) → MAID.Val S nd.val))

/-- Info-set type for the EFG derived from a MAID:
    which decision node + what was observed. -/
def MaidInfoset (S : MAID.Struct (Fin m) n) (p : Fin m) :=
  Σ (d : MAID.DecisionNode S p), MAID.Cfg S (S.obsParents d.val)

instance instFintypeMaidInfoset (S : MAID.Struct (Fin m) n) (p : Fin m) :
    Fintype (MaidInfoset S p) :=
  Sigma.instFintype

instance instDecidableEqMaidInfoset (S : MAID.Struct (Fin m) n) (p : Fin m) :
    DecidableEq (MaidInfoset S p) :=
  inferInstanceAs (DecidableEq (Σ (d : MAID.DecisionNode S p), MAID.Cfg S (S.obsParents d.val)))

/-- Build an `EFG.InfoStructure` from a MAID structure. -/
noncomputable def maidInfoS (S : MAID.Struct (Fin m) n) :
    EFG.InfoStructure where
  n := m
  Infoset := fun p => MaidInfoset S p
  fInfo := fun p => instFintypeMaidInfoset S p
  dInfo := fun p => instDecidableEqMaidInfoset S p
  arity := fun _ ⟨d, _⟩ => S.domainSize d.val
  arity_pos := fun _ ⟨d, _⟩ => S.dom_pos d.val

-- ============================================================================
-- § 2. Tree construction
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
        (⟨⟨nd, hk⟩, MAID.projCfg assign (S.obsParents nd)⟩ : MaidInfoset S p)
        (fun v => buildTree S sem pol rest (MAID.updateAssign assign nd v))
    | .utility _ =>
      buildTree S sem pol rest
        (MAID.updateAssign assign nd ⟨0, by rw [S.utility_domain nd _ hk]; exact Nat.one_pos⟩)

-- ============================================================================
-- § 3. EFGGame from MAID
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
-- § 4. Strategy correspondence
-- ============================================================================

/-- Convert a MAID policy to an EFG behavioral profile. -/
noncomputable def toEFGProfile {S : MAID.Struct (Fin m) n}
    (pol : MAID.Policy S) : EFG.BehavioralProfile (maidInfoS S) :=
  fun p ⟨d, obs⟩ => pol p d obs

/-- Convert an EFG behavioral profile back to a MAID policy. -/
noncomputable def fromEFGProfile {S : MAID.Struct (Fin m) n}
    (σ : EFG.BehavioralProfile (maidInfoS S)) : MAID.Policy S :=
  fun p d obs => σ p ⟨d, obs⟩

theorem toFrom {S : MAID.Struct (Fin m) n}
    (σ : EFG.BehavioralProfile (maidInfoS S)) :
    toEFGProfile (fromEFGProfile σ) = σ := rfl

theorem fromTo {S : MAID.Struct (Fin m) n}
    (pol : MAID.Policy S) :
    fromEFGProfile (toEFGProfile pol) = pol := rfl

-- ============================================================================
-- § 5. Evaluation equivalence
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
    pol p ⟨nd, hk⟩ (MAID.projCfg assign (S.obsParents nd)) := by
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
-- § 6. KernelGame equivalence
-- ============================================================================

/-- The outcome kernels of the MAID and EFG KernelGames agree under strategy correspondence. -/
theorem maidToEFG_outcomeKernel {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S) :
    (maidToEFG S sem pol).toKernelGame.outcomeKernel (toEFGProfile pol) =
    (MAID.toKernelGame S sem).outcomeKernel pol := by
  simp only [EFG.EFGGame.toKernelGame, GameTree.evalDistProfile, MAID.toKernelGame]
  exact maid_efg_evalDist sem pol

-- ============================================================================
-- § 7. Perfect recall (sorry)
-- ============================================================================

/-- The EFG tree built from a MAID has perfect recall.
    (Proof deferred — this requires showing that the topological unrolling
    preserves the MAID's information structure.) -/
theorem buildTree_perfectRecall {S : MAID.Struct (Fin m) n}
    (sem : MAID.Sem S) (pol : MAID.Policy S) :
    EFG.PerfectRecall (maidToEFG S sem pol).tree := sorry

end MAID_EFG
