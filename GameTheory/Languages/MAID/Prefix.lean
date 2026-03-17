import GameTheory.Languages.MAID.Syntax

/-!
# Prefix Semantics for MAID

Prefix-indexed evaluation of a MAID along the natural order. Instead of
threading `PMF (TAssign S)` through every step, the assignment grows from
length 0 to length `n`, so "future nodes are irrelevant" is definitional.

## Main definitions

- `NaturalOrder S` — parents have smaller indices (identity = topo order)
- `PrefixAssign S k hk` — assignment to nodes `{0, ..., k-1}`
- `nodeDistPrefix` — `nodeDist` reading from a prefix
- `evalStepPrefix` / `evalFoldPrefix` — step and fold on prefix assignments
- `evalSegment` — fold over a sub-range `[k₀, k₁)`

## Main results

- `evalFoldPrefix_eq_evalAssignDist` — prefix fold = canonical Bayesian product
-/

namespace MAID

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

-- ============================================================================
-- Natural order
-- ============================================================================

/-- A MAID has **natural order** when node indices respect the DAG: every parent
of node `k` has index `< k`. Equivalent to the identity permutation being a
valid topological order. -/
def Struct.NaturalOrder (S : Struct Player n) : Prop :=
  ∀ (nd : Fin n), ∀ p ∈ S.parents nd, p.val < nd.val

theorem Struct.NaturalOrder.parents_lt {S : Struct Player n} (h : S.NaturalOrder)
    {nd p : Fin n} (hp : p ∈ S.parents nd) : p.val < nd.val :=
  h nd p hp

theorem Struct.NaturalOrder.obsParents_lt {S : Struct Player n} (h : S.NaturalOrder)
    {nd p : Fin n} (hp : p ∈ S.obsParents nd) : p.val < nd.val :=
  h nd p (S.obs_sub nd hp)

-- ============================================================================
-- Prefix assignment
-- ============================================================================

/-- Assignment to a prefix of nodes. `PrefixAssign S k` assigns a value to each
node in `{0, ..., k-1}`, where `k ≤ n`. -/
def PrefixAssign (S : Struct Player n) (k : Nat) (hk : k ≤ n) :=
  (i : Fin k) → Val S (Fin.castLE hk i)

instance (S : Struct Player n) (k : Nat) (hk : k ≤ n) :
    Fintype (PrefixAssign S k hk) := Pi.instFintype

instance (S : Struct Player n) (k : Nat) (hk : k ≤ n) :
    DecidableEq (PrefixAssign S k hk) :=
  inferInstanceAs (DecidableEq ((i : Fin k) → Val S (Fin.castLE hk i)))

instance (S : Struct Player n) (k : Nat) (hk : k ≤ n) :
    Nonempty (PrefixAssign S k hk) :=
  ⟨fun _ => ⟨0, S.dom_pos _⟩⟩

/-- The empty prefix assignment (`k = 0`). -/
def PrefixAssign.empty (S : Struct Player n) : PrefixAssign S 0 (Nat.zero_le n) :=
  fun i => i.elim0

/-- Read a value from a prefix assignment at a node known to be in the prefix. -/
def PrefixAssign.get {S : Struct Player n} {k : Nat} {hk : k ≤ n}
    (a : PrefixAssign S k hk) (nd : Fin n) (h : nd.val < k) : Val S nd :=
  have heq : Fin.castLE hk ⟨nd.val, h⟩ = nd := Fin.ext rfl
  heq ▸ a ⟨nd.val, h⟩

/-- Extend a prefix assignment by one value at node `k`. -/
def PrefixAssign.snoc {S : Struct Player n} {k : Nat} {hk : k < n}
    (a : PrefixAssign S k (le_of_lt hk)) (v : Val S ⟨k, hk⟩) :
    PrefixAssign S (k + 1) hk :=
  fun i =>
    if h : i.val < k then
      have : Fin.castLE hk i = Fin.castLE (le_of_lt hk) ⟨i.val, h⟩ := Fin.ext rfl
      this ▸ a ⟨i.val, h⟩
    else
      have : Fin.castLE hk i = ⟨k, hk⟩ := Fin.ext (show i.val = k by omega)
      this ▸ v

/-- Convert a full prefix assignment to a total assignment. -/
def PrefixAssign.toTAssign {S : Struct Player n}
    (a : PrefixAssign S n (le_refl n)) : TAssign S :=
  fun nd =>
    have : Fin.castLE (le_refl n) ⟨nd.val, nd.isLt⟩ = nd := Fin.ext rfl
    this ▸ a ⟨nd.val, nd.isLt⟩

/-- Extend a prefix to a total assignment, filling unassigned nodes with
default values (0). -/
def PrefixAssign.extend {S : Struct Player n} {k : Nat} {hk : k ≤ n}
    (a : PrefixAssign S k hk) : TAssign S :=
  fun nd => if h : nd.val < k then a.get nd h else ⟨0, S.dom_pos nd⟩

theorem PrefixAssign.extend_get {S : Struct Player n} {k : Nat} {hk : k ≤ n}
    (a : PrefixAssign S k hk) (nd : Fin n) (h : nd.val < k) :
    a.extend nd = a.get nd h := by
  simp only [extend, h, ↓reduceDIte]

theorem PrefixAssign.extend_default {S : Struct Player n} {k : Nat} {hk : k ≤ n}
    (a : PrefixAssign S k hk) (nd : Fin n) (h : ¬(nd.val < k)) :
    a.extend nd = ⟨0, S.dom_pos nd⟩ := by
  simp only [extend, h, ↓reduceDIte]

theorem PrefixAssign.extend_agree {S : Struct Player n} {k : Nat} {hk : k ≤ n}
    (a : PrefixAssign S k hk) (i : Fin k) :
    a.extend (Fin.castLE hk i) = a i := by
  rw [extend_get a (Fin.castLE hk i) (show (Fin.castLE hk i).val < k from i.isLt)]
  simp [get]

theorem PrefixAssign.empty_extend {S : Struct Player n} :
    (PrefixAssign.empty S).extend = defaultAssign S := by
  ext nd
  simp [extend, show ¬(nd.val < 0) from by omega, defaultAssign]

theorem PrefixAssign.snoc_extend {S : Struct Player n} {k : Nat} {hk : k < n}
    (a : PrefixAssign S k (le_of_lt hk)) (v : Val S ⟨k, hk⟩) :
    (a.snoc v).extend = updateAssign a.extend ⟨k, hk⟩ v := by
  funext nd
  simp only [extend, snoc, get, updateAssign]
  by_cases hlt : nd.val < k
  · -- nd.val < k: both sides give a ⟨nd.val, hlt⟩
    have hne : ¬(nd = ⟨k, hk⟩) := by
      intro h; subst h; exact absurd hlt (lt_irrefl _)
    have hlt1 : nd.val < k + 1 := by omega
    simp only [hlt1, ↓reduceDIte, hlt, hne]
  · by_cases heq : nd.val = k
    · -- nd.val = k: both sides give v
      have hnd : nd = ⟨k, hk⟩ := Fin.ext heq
      subst hnd
      simp only [show k < k + 1 from by omega, ↓reduceDIte,
        show ¬(k < k) from lt_irrefl k]
    · -- nd.val ≥ k+1: both sides give default
      have hne : ¬(nd = ⟨k, hk⟩) := by
        intro h; subst h; exact heq rfl
      have hge : ¬(nd.val < k + 1) := by omega
      simp only [hge, ↓reduceDIte, hlt, hne]

theorem PrefixAssign.toTAssign_eq_extend {S : Struct Player n}
    (a : PrefixAssign S n (le_refl n)) :
    a.toTAssign = a.extend := by
  ext nd
  rw [extend_get a nd nd.isLt]
  simp [toTAssign, get]

-- ============================================================================
-- Prefix projection
-- ============================================================================

/-- Project a prefix assignment to a configuration on a subset, given that all
elements of the subset are in the prefix. -/
def projPrefixCfg {S : Struct Player n} {k : Nat} {hk : k ≤ n}
    (a : PrefixAssign S k hk) (ps : Finset (Fin n))
    (h : ∀ p ∈ ps, p.val < k) : Cfg S ps :=
  fun ⟨p, hp⟩ => a.get p (h p hp)

-- ============================================================================
-- Prefix nodeDist
-- ============================================================================

/-- Distribution at a node, reading parent values from a prefix assignment.
Equivalent to `nodeDist S sem pol nd (extend a)` for any compatible total
extension. -/
noncomputable def nodeDistPrefix (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    {k : Nat} {hk : k ≤ n} (nd : Fin n)
    (a : PrefixAssign S k hk)
    (hparents : ∀ p ∈ S.parents nd, p.val < k)
    (hobs : ∀ p ∈ S.obsParents nd, p.val < k) :
    PMF (Val S nd) :=
  match hkind : S.kind nd with
  | .chance => sem.chanceCPD ⟨nd, hkind⟩ (projPrefixCfg a (S.parents nd) hparents)
  | .decision p => pol p ⟨⟨nd, hkind⟩, projPrefixCfg a (S.obsParents nd) hobs⟩
  | .utility _ => PMF.pure ⟨0, by rw [S.utility_domain nd _ hkind]; exact Nat.one_pos⟩

-- ============================================================================
-- Prefix step and fold
-- ============================================================================

/-- Extend a prefix assignment by drawing a value at node `k`. -/
noncomputable def evalStepPrefix (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    {k : Nat} {hk : k < n}
    (acc : PMF (PrefixAssign S k (le_of_lt hk)))
    (hparents : ∀ p ∈ S.parents ⟨k, hk⟩, p.val < k)
    (hobs : ∀ p ∈ S.obsParents ⟨k, hk⟩, p.val < k) :
    PMF (PrefixAssign S (k + 1) hk) :=
  acc.bind (fun a =>
    (nodeDistPrefix S sem pol ⟨k, hk⟩ a hparents hobs).map (a.snoc ·))

/-- Fold over the natural order `[0, 1, ..., n-1]` using prefix assignments. -/
noncomputable def evalFoldPrefix (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (hnat : S.NaturalOrder) : PMF (PrefixAssign S n (le_refl n)) :=
  go 0 (Nat.zero_le n) (PMF.pure (PrefixAssign.empty S))
where
  /-- Inner recursion: fold from `k` to `n`. -/
  go (k : Nat) (hk : k ≤ n) (acc : PMF (PrefixAssign S k hk)) :
      PMF (PrefixAssign S n (le_refl n)) :=
    if hlt : k < n then
      have hparents : ∀ p ∈ S.parents ⟨k, hlt⟩, p.val < k :=
        fun p hp => hnat ⟨k, hlt⟩ p hp
      have hobs : ∀ p ∈ S.obsParents ⟨k, hlt⟩, p.val < k :=
        fun p hp => hnat ⟨k, hlt⟩ p (S.obs_sub _ hp)
      have : n - (k + 1) < n - k := by omega
      go (k + 1) hlt
        (evalStepPrefix S sem pol acc hparents hobs)
    else
      have : k = n := by omega
      this ▸ acc
  termination_by n - k

-- ============================================================================
-- Segment fold
-- ============================================================================

/-- Fold over a segment `[k₀, k₁)` of the natural order, extending a prefix
from length `k₀` to length `k₁`. Defined by direct recursion (no where-clause)
so that unfolding and concatenation proofs are straightforward. -/
noncomputable def evalSegment (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (hnat : S.NaturalOrder)
    (k₀ k₁ : Nat) (hk₀ : k₀ ≤ k₁) (hk₁ : k₁ ≤ n)
    (acc : PMF (PrefixAssign S k₀ (le_trans hk₀ hk₁))) :
    PMF (PrefixAssign S k₁ hk₁) :=
  if hlt : k₀ < k₁ then
    have hk_n : k₀ < n := Nat.lt_of_lt_of_le hlt hk₁
    have hparents : ∀ p ∈ S.parents ⟨k₀, hk_n⟩, p.val < k₀ :=
      fun p hp => hnat ⟨k₀, hk_n⟩ p hp
    have hobs : ∀ p ∈ S.obsParents ⟨k₀, hk_n⟩, p.val < k₀ :=
      fun p hp => hnat ⟨k₀, hk_n⟩ p (S.obs_sub _ hp)
    have : k₁ - (k₀ + 1) < k₁ - k₀ := by omega
    evalSegment S sem pol hnat (k₀ + 1) k₁ hlt hk₁
      (evalStepPrefix S sem pol acc hparents hobs)
  else
    have : k₀ = k₁ := by omega
    this ▸ acc
termination_by k₁ - k₀

-- ============================================================================
-- Bridge theorems
-- ============================================================================

/-- Projecting from a prefix agrees with projecting from any total assignment
that extends it. -/
theorem projPrefixCfg_eq_projCfg {S : Struct Player n} {k : Nat} {hk : k ≤ n}
    (a : PrefixAssign S k hk) (ext : TAssign S)
    (hagree : ∀ (i : Fin k), ext (Fin.castLE hk i) = a i)
    (ps : Finset (Fin n)) (hps : ∀ p ∈ ps, p.val < k) :
    projPrefixCfg a ps hps = projCfg ext ps := by
  ext ⟨p, hp⟩
  simp only [projPrefixCfg, PrefixAssign.get, projCfg]
  exact congr_arg Fin.val (hagree ⟨p.val, hps p hp⟩).symm

/-- `nodeDistPrefix` agrees with `nodeDist` for any compatible total extension. -/
theorem nodeDistPrefix_eq_nodeDist {S : Struct Player n}
    (sem : Sem S) (pol : Policy S)
    {k : Nat} {hk : k ≤ n} (nd : Fin n)
    (a : PrefixAssign S k hk)
    (ext : TAssign S)
    (hagree : ∀ (i : Fin k), ext (Fin.castLE hk i) = a i)
    (hparents : ∀ p ∈ S.parents nd, p.val < k)
    (hobs : ∀ p ∈ S.obsParents nd, p.val < k) :
    nodeDistPrefix S sem pol nd a hparents hobs = nodeDist S sem pol nd ext := by
  have hproj := projPrefixCfg_eq_projCfg a ext hagree (S.parents nd) hparents
  have hobs_proj := projPrefixCfg_eq_projCfg a ext hagree (S.obsParents nd) hobs
  -- Both nodeDistPrefix and nodeDist dispatch on S.kind nd; rewrite to a common form.
  have : nodeDistPrefix S sem pol nd a hparents hobs =
      match hkind : S.kind nd with
      | .chance => sem.chanceCPD ⟨nd, hkind⟩ (projPrefixCfg a (S.parents nd) hparents)
      | .decision p => pol p ⟨⟨nd, hkind⟩, projPrefixCfg a (S.obsParents nd) hobs⟩
      | .utility _ => PMF.pure ⟨0, by rw [S.utility_domain nd _ hkind]; exact Nat.one_pos⟩ :=
    rfl
  rw [this, hproj, hobs_proj]
  rfl

/-- Natural order yields a topological order: `[0, 1, ..., n-1]`. -/
def Struct.NaturalOrder.toTopologicalOrder {S : Struct Player n} (hnat : S.NaturalOrder) :
    TopologicalOrder S where
  order := List.finRange n
  nodup := List.nodup_finRange n
  length := List.length_finRange
  respects := by
    intro idx p hp
    have hi : idx.val < n := by
      have := idx.isLt; simp only [List.length_finRange] at this; exact this
    have hp' : p ∈ S.parents ⟨idx.val, hi⟩ := by
      have : (List.finRange n)[idx] = ⟨idx.val, hi⟩ := by
        simp [List.getElem_finRange, Fin.ext_iff]
      rwa [this] at hp
    have hplt := hnat ⟨idx.val, hi⟩ p hp'
    have hplen : p.val < (List.finRange n).length := by simp
    refine ⟨⟨p.val, hplen⟩, hplt, ?_⟩
    simp [List.getElem_finRange]

/-- `evalStepPrefix` maps to `evalStep` via `extend`. -/
private theorem evalStepPrefix_map_extend (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    {k : Nat} {hk : k < n}
    (acc : PMF (PrefixAssign S k (le_of_lt hk)))
    (hparents : ∀ p ∈ S.parents ⟨k, hk⟩, p.val < k)
    (hobs : ∀ p ∈ S.obsParents ⟨k, hk⟩, p.val < k) :
    (evalStepPrefix S sem pol acc hparents hobs).map PrefixAssign.extend =
      evalStep S sem pol (acc.map PrefixAssign.extend) ⟨k, hk⟩ := by
  simp only [evalStepPrefix, evalStep]
  -- LHS: (acc.bind (fun a => (nodeDistPrefix ...).map (a.snoc ·))).map extend
  rw [PMF.map_bind]
  -- LHS: acc.bind (fun a => ((nodeDistPrefix ... a ...).map (a.snoc ·)).map extend)
  -- Rewrite RHS using bind_map to pull extend inside
  rw [PMF.bind_map]
  congr 1; funext a
  -- LHS: ((nodeDistPrefix ...).map (a.snoc ·)).map extend
  rw [PMF.map_comp]
  -- LHS: (nodeDistPrefix ...).map (extend ∘ a.snoc)
  --     = (nodeDistPrefix ...).map (fun v => (a.snoc v).extend)
  --     = (nodeDistPrefix ...).map (fun v => updateAssign a.extend ⟨k,hk⟩ v)
  -- RHS: (nodeDist ... a.extend).bind (fun v => pure (updateAssign a.extend ⟨k,hk⟩ v))
  --     = (nodeDist ... a.extend).map (fun v => updateAssign a.extend ⟨k,hk⟩ v)
  simp only [Function.comp_def]
  -- LHS: (nodeDistPrefix ...).map (fun v => (a.snoc v).extend)
  -- RHS: (nodeDist ... a.extend).bind (fun v => pure (updateAssign a.extend ⟨k,hk⟩ v))
  -- Rewrite RHS bind-pure to map
  conv_rhs => rw [show (fun v => PMF.pure (updateAssign a.extend ⟨k, hk⟩ v)) =
    PMF.pure ∘ (fun v => updateAssign a.extend ⟨k, hk⟩ v) from rfl]
  rw [PMF.bind_pure_comp]
  -- Now both sides are: PMF.map (fun v => ...) (dist)
  have hdist := nodeDistPrefix_eq_nodeDist sem pol ⟨k, hk⟩ a a.extend
    (fun i => a.extend_agree i) hparents hobs
  rw [hdist]
  congr 1; funext v
  exact PrefixAssign.snoc_extend a v

/-- Simulation: the prefix fold's inner loop maps to a `List.foldl` of `evalStep`. -/
private theorem evalFoldPrefix_go_map_extend (S : Struct Player n) (sem : Sem S)
    (pol : Policy S) (hnat : S.NaturalOrder)
    (k : Nat) (hk : k ≤ n) (acc : PMF (PrefixAssign S k hk)) :
    (evalFoldPrefix.go S sem pol hnat k hk acc).map PrefixAssign.extend =
      ((List.finRange n).drop k).foldl (evalStep S sem pol)
        (acc.map PrefixAssign.extend) := by
  -- Induction on the distance to n (decreasing)
  induction h : n - k using Nat.strongRecOn generalizing k with
  | _ d ih =>
    by_cases hlt : k < n
    · -- Recursive case: unfold one step
      conv_lhs => rw [evalFoldPrefix.go]; simp only [hlt, ↓reduceDIte]
      have hstep := evalStepPrefix_map_extend S sem pol acc
        (fun p hp => hnat ⟨k, hlt⟩ p hp)
        (fun p hp => hnat ⟨k, hlt⟩ p (S.obs_sub _ hp))
      rw [ih (n - (k + 1)) (by omega) (k + 1) hlt _ rfl]
      rw [hstep]
      -- Drop k of finRange n = ⟨k, hlt⟩ :: drop (k+1)
      have hdrop : (List.finRange n).drop k =
          ⟨k, hlt⟩ :: (List.finRange n).drop (k + 1) := by
        rw [← List.cons_getElem_drop_succ
          (h := by simp only [List.length_finRange]; exact hlt)]
        congr 1; simp [List.getElem_finRange]
      rw [hdrop, List.foldl_cons]
    · -- Base case: k = n, go returns (cast of) acc
      have hkn : k = n := by omega
      subst hkn
      conv_lhs => rw [evalFoldPrefix.go]; simp only [lt_irrefl, ↓reduceDIte]
      have hdrop : (List.finRange k).drop k = [] :=
        List.drop_eq_nil_of_le (by simp)
      rw [hdrop, List.foldl_nil]

/-- The prefix fold equals the canonical order-free evaluation. -/
theorem evalFoldPrefix_eq_evalAssignDist (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (hnat : S.NaturalOrder) :
    (evalFoldPrefix S sem pol hnat).map PrefixAssign.toTAssign =
      evalAssignDist S sem pol := by
  -- Step 1: toTAssign = extend for full prefix
  have hconv : (evalFoldPrefix S sem pol hnat).map PrefixAssign.toTAssign =
      (evalFoldPrefix S sem pol hnat).map PrefixAssign.extend := by
    congr 1; funext a; exact a.toTAssign_eq_extend
  rw [hconv]
  -- Step 2: Use the simulation lemma
  have hsim := evalFoldPrefix_go_map_extend S sem pol hnat 0 (Nat.zero_le n)
    (PMF.pure (PrefixAssign.empty S))
  simp only [evalFoldPrefix] at hsim ⊢
  rw [hsim]
  -- Step 3: Simplify the initial accumulator
  have hinit : PMF.map PrefixAssign.extend (PMF.pure (PrefixAssign.empty S)) =
      PMF.pure (defaultAssign S) := by
    rw [PMF.pure_map]; exact congrArg PMF.pure PrefixAssign.empty_extend
  rw [hinit, List.drop_zero]
  -- Step 4: This is evalFold with the natural topological order
  rw [evalAssignDist_eq_evalFold S sem pol hnat.toTopologicalOrder]
  rfl

/-- `evalFoldPrefix.go` from `m` equals `evalSegment` from `m` to `n`. -/
private theorem evalFoldPrefix_go_eq_evalSegment (S : Struct Player n) (sem : Sem S)
    (pol : Policy S) (hnat : S.NaturalOrder)
    (m : Nat) (hm : m ≤ n) (acc : PMF (PrefixAssign S m hm)) :
    evalFoldPrefix.go S sem pol hnat m hm acc =
      evalSegment S sem pol hnat m n hm (le_refl n) acc := by
  induction h : n - m using Nat.strongRecOn generalizing m acc with
  | _ d ih =>
    by_cases hlt : m < n
    · conv_lhs => rw [evalFoldPrefix.go]; simp only [hlt, ↓reduceDIte]
      conv_rhs => rw [evalSegment]; simp only [hlt, ↓reduceDIte]
      exact ih (n - (m + 1)) (by omega) (m + 1) hlt _ rfl
    · have hmn : m = n := by omega
      subst hmn
      conv_lhs => rw [evalFoldPrefix.go]; simp only [lt_irrefl, ↓reduceDIte]
      conv_rhs => rw [evalSegment]; simp only [lt_irrefl, ↓reduceDIte]

/-- `evalFoldPrefix` equals `evalSegment` from `0` to `n`. -/
private theorem evalFoldPrefix_eq_evalSegment_full (S : Struct Player n) (sem : Sem S)
    (pol : Policy S) (hnat : S.NaturalOrder) :
    evalFoldPrefix S sem pol hnat =
      evalSegment S sem pol hnat 0 n (Nat.zero_le n) (le_refl n)
        (PMF.pure (PrefixAssign.empty S)) := by
  exact evalFoldPrefix_go_eq_evalSegment S sem pol hnat 0 (Nat.zero_le n) _

/-- Segment concatenation: `evalSegment [k₀,k₁) = evalSegment [m,k₁) ∘ evalSegment [k₀,m)`. -/
private theorem evalSegment_concat (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (hnat : S.NaturalOrder)
    (k₀ m k₁ : Nat) (hk₀m : k₀ ≤ m) (hmk₁ : m ≤ k₁) (hk₁ : k₁ ≤ n)
    (acc : PMF (PrefixAssign S k₀ (le_trans hk₀m (le_trans hmk₁ hk₁)))) :
    evalSegment S sem pol hnat m k₁ hmk₁ hk₁
      (evalSegment S sem pol hnat k₀ m hk₀m (le_trans hmk₁ hk₁) acc) =
    evalSegment S sem pol hnat k₀ k₁ (le_trans hk₀m hmk₁) hk₁ acc := by
  induction h : m - k₀ using Nat.strongRecOn generalizing k₀ acc with
  | _ d ih =>
    by_cases hlt : k₀ < m
    · -- Unfold inner segment (k₀ to m) one step at k₀
      have inner_step : evalSegment S sem pol hnat k₀ m hk₀m (le_trans hmk₁ hk₁) acc =
          evalSegment S sem pol hnat (k₀ + 1) m hlt (le_trans hmk₁ hk₁)
            (evalStepPrefix S sem pol acc
              (fun p hp => hnat ⟨k₀, Nat.lt_of_lt_of_le hlt (le_trans hmk₁ hk₁)⟩ p hp)
              (fun p hp => hnat ⟨k₀, Nat.lt_of_lt_of_le hlt (le_trans hmk₁ hk₁)⟩ p
                (S.obs_sub _ hp))) := by
        conv_lhs => rw [evalSegment]; simp only [hlt, ↓reduceDIte]
      rw [inner_step]
      -- Unfold full segment (k₀ to k₁) one step at k₀
      have hlt' : k₀ < k₁ := Nat.lt_of_lt_of_le hlt hmk₁
      conv_rhs => rw [evalSegment]; simp only [hlt', ↓reduceDIte]
      -- Both stepped at k₀; apply IH with k₀+1
      exact ih (m - (k₀ + 1)) (by omega) (k₀ + 1) hlt _ rfl
    · -- Base: k₀ = m, inner segment is identity
      have hk₀m_eq : k₀ = m := by omega
      subst hk₀m_eq
      -- evalSegment k₀ k₀ ... acc: k₀ < k₀ is false → returns (cast of) acc
      suffices hseg : evalSegment S sem pol hnat k₀ k₀ hk₀m (le_trans hmk₁ hk₁) acc = acc by
        rw [hseg]
      rw [evalSegment]; simp only [lt_irrefl, ↓reduceDIte]

/-- The full fold decomposes into consecutive segments. -/
theorem evalFoldPrefix_eq_segment (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (hnat : S.NaturalOrder)
    (k : Nat) (hk : k ≤ n) :
    evalFoldPrefix S sem pol hnat =
      evalSegment S sem pol hnat k n hk (le_refl n)
        (evalSegment S sem pol hnat 0 k (Nat.zero_le k) hk
          (PMF.pure (PrefixAssign.empty S))) := by
  rw [evalFoldPrefix_eq_evalSegment_full]
  exact (evalSegment_concat S sem pol hnat 0 k n (Nat.zero_le k) hk (le_refl n)
    (PMF.pure (PrefixAssign.empty S))).symm

end MAID
