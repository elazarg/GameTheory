import GameTheory.Languages.Intrinsic.Compile
import Math.ProbabilityMassFunction

/-!
# Perfect Recall and Kuhn's Equivalence Theorem for W-Games

Following Section 4 of Heymann–De Lara–Chancelier (2020).

## Perfect recall (Definition 14)

A player `p` enjoys perfect recall if, for any ordering prefix `κ` whose
last agent `κ⋆` belongs to player `p`, agent `κ⋆` knows at least what
did and knew those of their predecessors that also belong to player `p`.

## Kuhn's equivalence statement (Theorem 16 shape)

The paper's target equivalence says that, under causality and perfect recall,
for any mixed strategy there exists a product-mixed strategy with the same full
outcome distribution against every opponent mixed profile. This file proves the
player-local conditional chain identity and combines it with the outcome-kernel
expansion.

## Main definitions

- `choiceEquiv` — the join of information and decision: `Cₐ = Uₐ ∨ Iₐ`
- `PerfectRecall` — the perfect recall property for a player
- `mixedToBehavioral` — conditional mixed → behavioral construction
- `kuhn_equivalence` — the paper-faithful outcome-law equivalence statement
-/

namespace Intrinsic

open Math.ProbabilityMassFunction

-- ============================================================================
-- Choice fields (equation 27)
-- ============================================================================

/-- The choice equivalence relation for agent `a`: two configurations are
    choice-equivalent iff they are info-equivalent AND the agent made the
    same decision. This corresponds to the choice field `Cₐ = Uₐ ∨ Iₐ`
    (equation 27). -/
def choiceEquiv (M : WModel) (a : M.A) : Setoid M.H where
  r h h' := (M.info a).r h h' ∧ h.decision a = h'.decision a
  iseqv := {
    refl := fun h => ⟨(M.info a).iseqv.refl h, rfl⟩
    symm := fun ⟨hi, hd⟩ => ⟨(M.info a).iseqv.symm hi, hd.symm⟩
    trans := fun ⟨hi₁, hd₁⟩ ⟨hi₂, hd₂⟩ =>
      ⟨(M.info a).iseqv.trans hi₁ hi₂, hd₁.trans hd₂⟩
  }

/-- The join of choice fields for agents in a set `B` belonging to
    player `p`: two configurations are equivalent iff they are
    choice-equivalent for ALL agents in `B ∩ Aₚ` (equation 28b). -/
def playerChoiceEquiv (G : WGame) (B : Finset G.A) (p : G.P) :
    Setoid G.toWModel.H where
  r h h' := ∀ a ∈ B, G.owner a = p → (choiceEquiv G.toWModel a).r h h'
  iseqv := {
    refl := fun h a _ _ => (choiceEquiv G.toWModel a).iseqv.refl h
    symm := fun hr a ha hp => (choiceEquiv G.toWModel a).iseqv.symm (hr a ha hp)
    trans := fun hr₁ hr₂ a ha hp =>
      (choiceEquiv G.toWModel a).iseqv.trans (hr₁ a ha hp) (hr₂ a ha hp)
  }

-- ============================================================================
-- Perfect recall (Definition 14)
-- ============================================================================

/-- A player `p` enjoys **perfect recall** in a causal W-game with
    configuration-ordering `ϕ` if, for any ordering prefix `κ` whose
    last agent belongs to `p`, the current information atom is contained in
    the realized prefix cell and refines the choice field of predecessors
    belonging to `p` (Definition 14). In finite setoid terms this is the
    paper's condition `H^ϕ_κ ∩ H ∈ I_{κ⋆}` for every past-choice event `H`. -/
def PerfectRecall (G : WGame) (ϕ : ConfigOrdering G.toWModel)
    (p : G.P) : Prop :=
  ∀ (κ : OrderingPrefix G.toWModel) (hne : κ.val ≠ []),
    let last := κ.last hne
    G.owner last = p →
    let predecessors : Finset G.A := κ.predecessors
    ∀ h h' : G.toWModel.H,
      h ∈ configSet G.toWModel ϕ κ →
      (G.toWModel.info last).r h h' →
      h' ∈ configSet G.toWModel ϕ κ ∧
        (playerChoiceEquiv G predecessors p).r h h'

-- ============================================================================
-- Conditional Mixed → Behavioral (Proposition 15)
-- ============================================================================

open Classical in
/-- The agents preceding `a` in the ordering selected at configuration `h`. -/
noncomputable def predecessorsInOrdering (M : WModel) (ϕ : ConfigOrdering M)
    (a : M.A) (h : M.H) : Finset M.A :=
  ((ϕ h).val.take ((ϕ h).val.idxOf a)).toFinset

open Classical in
/-- The realized ordering prefix ending at `a` for configuration `h`. -/
noncomputable def prefixThroughInOrdering (M : WModel) (ϕ : ConfigOrdering M)
    (a : M.A) (h : M.H) : OrderingPrefix M :=
  ⟨(ϕ h).val.take ((ϕ h).val.idxOf a + 1),
    (List.take_sublist ((ϕ h).val.idxOf a + 1) (ϕ h).val).nodup (ϕ h).property.1⟩

theorem prefixThroughInOrdering_idx_lt (M : WModel) (ϕ : ConfigOrdering M)
    (a : M.A) (h : M.H) :
    (ϕ h).val.idxOf a < (ϕ h).val.length := by
  exact List.idxOf_lt_length_of_mem ((ϕ h).property.2 a)

theorem prefixThroughInOrdering_val_eq (M : WModel) (ϕ : ConfigOrdering M)
    (a : M.A) (h : M.H) :
    (prefixThroughInOrdering M ϕ a h).val =
      (ϕ h).val.take ((ϕ h).val.idxOf a) ++ [a] := by
  classical
  have hidx := prefixThroughInOrdering_idx_lt M ϕ a h
  change (ϕ h).val.take ((ϕ h).val.idxOf a + 1) =
    (ϕ h).val.take ((ϕ h).val.idxOf a) ++ [a]
  rw [← List.take_append_getElem hidx]
  congr
  exact List.getElem_idxOf hidx

theorem prefixThroughInOrdering_ne_nil (M : WModel) (ϕ : ConfigOrdering M)
    (a : M.A) (h : M.H) :
    (prefixThroughInOrdering M ϕ a h).val ≠ [] := by
  classical
  rw [prefixThroughInOrdering_val_eq]
  simp

theorem prefixThroughInOrdering_last (M : WModel) (ϕ : ConfigOrdering M)
    (a : M.A) (h : M.H)
    (hne : (prefixThroughInOrdering M ϕ a h).val ≠ []) :
    (prefixThroughInOrdering M ϕ a h).last hne = a := by
  classical
  simp [OrderingPrefix.last, prefixThroughInOrdering_val_eq]

theorem prefixThroughInOrdering_mem_configSet (M : WModel)
    (ϕ : ConfigOrdering M) (a : M.A) (h : M.H) :
    h ∈ configSet M ϕ (prefixThroughInOrdering M ϕ a h) := by
  classical
  have hidx := prefixThroughInOrdering_idx_lt M ϕ a h
  simp [configSet, prefixThroughInOrdering, List.length_take,
    Nat.min_eq_left (Nat.succ_le_of_lt hidx)]

theorem prefixThroughInOrdering_predecessors (M : WModel)
    (ϕ : ConfigOrdering M) (a : M.A) (h : M.H) :
    (prefixThroughInOrdering M ϕ a h).predecessors =
      predecessorsInOrdering M ϕ a h := by
  classical
  have hidx := prefixThroughInOrdering_idx_lt M ϕ a h
  simp [OrderingPrefix.predecessors, predecessorsInOrdering,
    prefixThroughInOrdering, ← List.take_append_getElem hidx]

theorem prefixThroughInOrdering_eq_of_configSet_last (M : WModel)
    (ϕ : ConfigOrdering M) (κ : OrderingPrefix M) (hne : κ.val ≠ [])
    {a : M.A} {h : M.H}
    (hmem : h ∈ configSet M ϕ κ) (hlast : κ.last hne = a) :
    prefixThroughInOrdering M ϕ a h = κ := by
  classical
  apply Subtype.ext
  have hprefix : κ.val <+: (ϕ h).val := by
    rw [← hmem]
    exact List.take_prefix κ.val.length (ϕ h).val
  have haκ : a ∈ κ.val := by
    rw [← hlast]
    exact List.getLast_mem hne
  have hidxTotal : (ϕ h).val.idxOf a = κ.val.idxOf a :=
    (hprefix.idxOf_eq_of_mem haκ).symm
  have hlast_not_mem : κ.val.getLast hne ∉ κ.val.dropLast := by
    have hnodup' : (κ.val.dropLast ++ [κ.val.getLast hne]).Nodup := by
      simpa [List.dropLast_append_getLast hne] using κ.property
    have hsplit :
        (κ.val.dropLast).Nodup ∧
          ∀ a ∈ κ.val.dropLast, ¬ a = κ.val.getLast hne := by
      simpa [List.nodup_append] using hnodup'
    intro hmemLast
    exact hsplit.2 (κ.val.getLast hne) hmemLast rfl
  have hidxK : κ.val.idxOf a = κ.val.length - 1 := by
    rw [← hlast]
    exact List.idxOf_getLast hne hlast_not_mem
  have hidx : (ϕ h).val.idxOf a + 1 = κ.val.length := by
    rw [hidxTotal, hidxK]
    exact Nat.succ_pred_eq_of_pos (List.length_pos_of_ne_nil hne)
  change (ϕ h).val.take ((ϕ h).val.idxOf a + 1) = κ.val
  rw [hidx]
  exact hmem

/-- Compatibility between a configuration-dependent ordering and information:
    an agent's information atom cannot distinguish configurations with different
    realized prefixes ending at that agent. This is retained as a useful
    standalone structural predicate; the paper-strength `PerfectRecall` below
    implies it for the relevant player's agents. -/
def OrderInfoCompatibleWith (M : WModel) (ϕ : ConfigOrdering M) : Prop :=
  ∀ (a : M.A) (h h' : M.H),
    (M.info a).r h h' →
      prefixThroughInOrdering M ϕ a h = prefixThroughInOrdering M ϕ a h'

theorem predecessorsInOrdering_eq_of_info (M : WModel) (ϕ : ConfigOrdering M)
    (hcompat : OrderInfoCompatibleWith M ϕ) {a : M.A} {h h' : M.H}
    (hinfo : (M.info a).r h h') :
    predecessorsInOrdering M ϕ a h = predecessorsInOrdering M ϕ a h' := by
  have hp := hcompat a h h' hinfo
  have := congrArg OrderingPrefix.predecessors hp
  simpa [prefixThroughInOrdering_predecessors] using this

theorem prefixThroughInOrdering_mem_configSet_of_info (M : WModel)
    (ϕ : ConfigOrdering M) (hcompat : OrderInfoCompatibleWith M ϕ)
    {a : M.A} {h h' : M.H} (hinfo : (M.info a).r h h') :
    h' ∈ configSet M ϕ (prefixThroughInOrdering M ϕ a h) := by
  have hp := hcompat a h h' hinfo
  rw [hp]
  exact prefixThroughInOrdering_mem_configSet M ϕ a h'

theorem prefixThroughInOrdering_eq_of_info_of_perfectRecall (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P) (hpr : PerfectRecall G ϕ p)
    (a : G.agents p) {h h' : G.toWModel.H}
    (hinfo : (G.toWModel.info (a : G.A)).r h h') :
    prefixThroughInOrdering G.toWModel ϕ (a : G.A) h =
      prefixThroughInOrdering G.toWModel ϕ (a : G.A) h' := by
  classical
  let κ : OrderingPrefix G.toWModel :=
    prefixThroughInOrdering G.toWModel ϕ (a : G.A) h
  have hne : κ.val ≠ [] :=
    prefixThroughInOrdering_ne_nil G.toWModel ϕ (a : G.A) h
  have hlast : κ.last hne = (a : G.A) :=
    prefixThroughInOrdering_last G.toWModel ϕ (a : G.A) h hne
  have haowner : G.owner (a : G.A) = p :=
    (Finset.mem_filter.mp a.property).2
  have hmem : h ∈ configSet G.toWModel ϕ κ :=
    prefixThroughInOrdering_mem_configSet G.toWModel ϕ (a : G.A) h
  have hinfoLast : (G.toWModel.info (κ.last hne)).r h h' := by
    rw [hlast]
    exact hinfo
  have hmem' : h' ∈ configSet G.toWModel ϕ κ :=
    (hpr κ hne (by simpa [hlast] using haowner) h h' hmem hinfoLast).1
  have hpref' :
      prefixThroughInOrdering G.toWModel ϕ (a : G.A) h' = κ :=
    prefixThroughInOrdering_eq_of_configSet_last G.toWModel ϕ κ hne hmem' hlast
  exact hpref'.symm

theorem orderInfoCompatibleWith_of_forall_perfectRecall (G : WGame)
    (ϕ : ConfigOrdering G.toWModel)
    (hpr : ∀ p : G.P, PerfectRecall G ϕ p) :
    OrderInfoCompatibleWith G.toWModel ϕ := by
  classical
  intro a h h' hinfo
  let ap : G.agents (G.owner a) := ⟨a, by simp [WGame.agents]⟩
  simpa [ap] using
    prefixThroughInOrdering_eq_of_info_of_perfectRecall G ϕ (G.owner a)
      (hpr (G.owner a)) ap hinfo

open Classical in
/-- Filter a raw agent list to the agents owned by player `p`, retaining order
    and packaging the ownership proof in the subtype. -/
noncomputable def ownedAgentsInList (G : WGame) (p : G.P) :
    List G.A → List (G.agents p)
  | [] => []
  | a :: rest =>
      if howner : G.owner a = p then
        (⟨a, by simp [WGame.agents, howner]⟩ : G.agents p) ::
          ownedAgentsInList G p rest
      else
        ownedAgentsInList G p rest

theorem mem_ownedAgentsInList_iff (G : WGame) (p : G.P)
    (l : List G.A) (a : G.agents p) :
    a ∈ ownedAgentsInList G p l ↔ (a : G.A) ∈ l := by
  classical
  induction l with
  | nil =>
      simp [ownedAgentsInList]
  | cons b rest ih =>
      by_cases hb : G.owner b = p
      · by_cases hba : b = (a : G.A)
        · subst hba
          simp [ownedAgentsInList, hb]
        · have hneq : (⟨b, by simp [WGame.agents, hb]⟩ : G.agents p) ≠ a := by
            intro h
            exact hba (congrArg Subtype.val h)
          have hneq' : a ≠ (⟨b, by simp [WGame.agents, hb]⟩ : G.agents p) :=
            Ne.symm hneq
          have hraw : (a : G.A) ≠ b := by
            intro h
            exact hba h.symm
          simp [ownedAgentsInList, hb, hneq', ih, hraw]
      · have hba : b ≠ (a : G.A) := by
          intro h
          subst h
          exact hb ((Finset.mem_filter.mp a.property).2)
        have hraw : (a : G.A) ≠ b := by
          intro h
          exact hba h.symm
        simp [ownedAgentsInList, hb, ih, hraw]

theorem ownedAgentsInList_nodup (G : WGame) (p : G.P)
    {l : List G.A} (hnodup : l.Nodup) :
    (ownedAgentsInList G p l).Nodup := by
  classical
  induction l with
  | nil =>
      simp [ownedAgentsInList]
  | cons a rest ih =>
      rw [List.nodup_cons] at hnodup
      by_cases ha : G.owner a = p
      · rw [show ownedAgentsInList G p (a :: rest) =
            (⟨a, by simp [WGame.agents, ha]⟩ : G.agents p) ::
              ownedAgentsInList G p rest by
            simp [ownedAgentsInList, ha]]
        rw [List.nodup_cons]
        constructor
        · intro hmem
          have hraw : a ∈ rest := by
            simpa [mem_ownedAgentsInList_iff] using hmem
          exact hnodup.1 hraw
        · exact ih hnodup.2
      · simpa [ownedAgentsInList, ha] using ih hnodup.2

theorem ownedAgentsInList_toFinset_of_mem_all (G : WGame) (p : G.P)
    (l : List G.A) (hmem : ∀ a : G.agents p, (a : G.A) ∈ l) :
    (ownedAgentsInList G p l).toFinset = Finset.univ := by
  classical
  ext a
  simp [mem_ownedAgentsInList_iff, hmem]

theorem ownedAgentsInList_append_singleton_of_not_owner (G : WGame) (p : G.P)
    (pref : List G.A) {a : G.A} (ha : G.owner a ≠ p) :
    ownedAgentsInList G p (pref ++ [a]) = ownedAgentsInList G p pref := by
  classical
  induction pref with
  | nil =>
      simp [ownedAgentsInList, ha]
  | cons b rest ih =>
      by_cases hb : G.owner b = p
      · simp [ownedAgentsInList, hb, ih]
      · simp [ownedAgentsInList, hb, ih]

theorem ownedAgentsInList_append (G : WGame) (p : G.P)
    (l r : List G.A) :
    ownedAgentsInList G p (l ++ r) =
      ownedAgentsInList G p l ++ ownedAgentsInList G p r := by
  classical
  induction l with
  | nil =>
      simp [ownedAgentsInList]
  | cons a rest ih =>
      by_cases ha : G.owner a = p
      · simp [ownedAgentsInList, ha, ih]
      · simp [ownedAgentsInList, ha, ih]

theorem ownedAgentsInList_append_singleton_of_owner (G : WGame) (p : G.P)
    (pref : List G.A) {a : G.A} (ha : G.owner a = p) :
    ownedAgentsInList G p (pref ++ [a]) =
      ownedAgentsInList G p pref ++
        [((⟨a, by simp [WGame.agents, ha]⟩ : G.agents p))] := by
  classical
  induction pref with
  | nil =>
      simp [ownedAgentsInList, ha]
  | cons b rest ih =>
      by_cases hb : G.owner b = p
      · simp [ownedAgentsInList, hb, ih]
      · simp [ownedAgentsInList, hb, ih]

/-- Player `p`'s agents listed in the realized order at configuration `h`. -/
noncomputable def playerAgentsInOrdering (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P) (h : G.toWModel.H) :
    List (G.agents p) :=
  ownedAgentsInList G p (ϕ h).val

theorem playerAgentsInOrdering_nodup (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P) (h : G.toWModel.H) :
    (playerAgentsInOrdering G ϕ p h).Nodup := by
  classical
  exact ownedAgentsInList_nodup G p (ϕ h).property.1

theorem playerAgentsInOrdering_mem (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P) (h : G.toWModel.H)
    (a : G.agents p) :
    a ∈ playerAgentsInOrdering G ϕ p h := by
  classical
  simp [playerAgentsInOrdering, mem_ownedAgentsInList_iff, (ϕ h).property.2 (a : G.A)]

theorem playerAgentsInOrdering_toFinset (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P) (h : G.toWModel.H) :
    (playerAgentsInOrdering G ϕ p h).toFinset = Finset.univ := by
  classical
  exact ownedAgentsInList_toFinset_of_mem_all G p (ϕ h).val
    (fun a => (ϕ h).property.2 (a : G.A))

theorem playerAgentsInOrdering_prod_eq_univ (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P) (h : G.toWModel.H)
    (f : G.agents p → ENNReal) :
    (List.map f (playerAgentsInOrdering G ϕ p h)).prod =
      ∏ a : G.agents p, f a := by
  classical
  calc
    (List.map f (playerAgentsInOrdering G ϕ p h)).prod
        = (playerAgentsInOrdering G ϕ p h).toFinset.prod f :=
          (List.prod_toFinset f (playerAgentsInOrdering_nodup G ϕ p h)).symm
    _ = ∏ a : G.agents p, f a := by
          rw [playerAgentsInOrdering_toFinset]

open Classical in
/-- Player `p`'s agents preceding `a` in the realized prefix at `h`. -/
noncomputable def playerPastAgentsInOrdering (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P)
    (a : G.agents p) (h : G.toWModel.H) : List (G.agents p) :=
  ownedAgentsInList G p
    ((prefixThroughInOrdering G.toWModel ϕ (a : G.A) h).val.dropLast)

theorem mem_playerPastAgentsInOrdering_predecessors (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P)
    (a b : G.agents p) (h : G.toWModel.H)
    (hb : b ∈ playerPastAgentsInOrdering G ϕ p a h) :
    (b : G.A) ∈
      (prefixThroughInOrdering G.toWModel ϕ (a : G.A) h).predecessors := by
  classical
  simpa [playerPastAgentsInOrdering, OrderingPrefix.predecessors,
    mem_ownedAgentsInList_iff] using hb

theorem mem_playerPastAgentsInOrdering_iff (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P)
    (a b : G.agents p) (h : G.toWModel.H) :
    b ∈ playerPastAgentsInOrdering G ϕ p a h ↔
      (b : G.A) ∈
        (prefixThroughInOrdering G.toWModel ϕ (a : G.A) h).predecessors := by
  classical
  simp [playerPastAgentsInOrdering, OrderingPrefix.predecessors,
    mem_ownedAgentsInList_iff]

theorem playerPastAgentsInOrdering_mem_iff_of_info (G : WGame)
    (ϕ : ConfigOrdering G.toWModel)
    (p : G.P) (hpr : PerfectRecall G ϕ p)
    (a b : G.agents p) {h h' : G.toWModel.H}
    (hinfo : (G.toWModel.info (a : G.A)).r h h') :
    b ∈ playerPastAgentsInOrdering G ϕ p a h ↔
      b ∈ playerPastAgentsInOrdering G ϕ p a h' := by
  classical
  rw [mem_playerPastAgentsInOrdering_iff, mem_playerPastAgentsInOrdering_iff]
  have hp :=
    congrArg OrderingPrefix.predecessors
      (prefixThroughInOrdering_eq_of_info_of_perfectRecall G ϕ p hpr a hinfo)
  exact ⟨fun hb => by
      rwa [← hp],
    fun hb => by
      rwa [hp]⟩

open Classical in
/-- If a total order decomposes as `pref ++ a :: rest`, then the owned agents
    in `pref` are exactly player `p`'s past agents before `a`. -/
theorem ownedAgentsInList_eq_past_of_decomp (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P)
    (h : G.toWModel.H) (pref rest : List G.A) (a : G.agents p)
    (hdecomp : pref ++ (a : G.A) :: rest = (ϕ h).val) :
    ownedAgentsInList G p pref = playerPastAgentsInOrdering G ϕ p a h := by
  classical
  have hnodup : (pref ++ (a : G.A) :: rest).Nodup := by
    simpa [hdecomp] using (ϕ h).property.1
  have hanot : (a : G.A) ∉ pref := by
    rw [List.nodup_append] at hnodup
    intro ha
    exact (hnodup.2.2 (a : G.A) ha (a : G.A) (by simp)) rfl
  have hidx :
      (ϕ h).val.idxOf (a : G.A) = pref.length := by
    rw [← hdecomp, List.idxOf_append]
    simp [hanot, List.idxOf_cons_self]
  have hpref :
      (prefixThroughInOrdering G.toWModel ϕ (a : G.A) h).val.dropLast = pref := by
    rw [prefixThroughInOrdering_val_eq, hidx]
    simp [← hdecomp]
  simp [playerPastAgentsInOrdering, hpref]

open Classical in
/-- The event that a player's pure strategy is consistent with the decisions
    already made by that player before agent `a` at configuration `h`. -/
def playerPastConsistent (G : WGame) (ϕ : ConfigOrdering G.toWModel)
    (p : G.P) (a : G.agents p) (h : G.toWModel.H)
    (strat : PlayerStrategySpace G p) : Prop :=
  ∀ b : G.agents p,
    b ∈ playerPastAgentsInOrdering G ϕ p a h →
      (strat b).act h = h.decision b

/-- The event that a player's local pure strategy for agent `a` chooses the
    decision specified by configuration `h`. -/
def playerAgentSolutionEvent (G : WGame) (p : G.P)
    (h : G.toWModel.H) (a : G.agents p)
    (strat : PlayerStrategySpace G p) : Prop :=
  h.decision a = (strat a).act h

open Classical in
/-- Player `p`'s solution events listed in the realized order at `h`. -/
noncomputable def playerSolutionEventsInOrdering (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P) (h : G.toWModel.H) :
    List (PlayerStrategySpace G p → Prop) :=
  (playerAgentsInOrdering G ϕ p h).map
    (fun a => playerAgentSolutionEvent G p h a)

theorem allEvents_playerSolutionEventsInOrdering_iff (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P) (h : G.toWModel.H)
    (strat : PlayerStrategySpace G p) :
    allEvents (playerSolutionEventsInOrdering G ϕ p h) strat ↔
      playerSolutionEvent G p h.nature h.decision strat := by
  classical
  constructor
  · intro hall a ha
    let ap : G.agents p := ⟨a, by simp [WGame.agents, ha]⟩
    have happ : playerAgentSolutionEvent G p h ap ∈
        playerSolutionEventsInOrdering G ϕ p h := by
      unfold playerSolutionEventsInOrdering
      exact List.mem_map.2 ⟨ap, playerAgentsInOrdering_mem G ϕ p h ap, rfl⟩
    exact hall (playerAgentSolutionEvent G p h ap) happ
  · intro hsol E hE
    unfold playerSolutionEventsInOrdering at hE
    rcases List.mem_map.1 hE with ⟨a, _ha, rfl⟩
    exact hsol (a : G.A) ((Finset.mem_filter.mp a.property).2)

theorem allEvents_playerSolutionEventsInOrdering_eq (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P) (h : G.toWModel.H) :
    allEvents (playerSolutionEventsInOrdering G ϕ p h) =
      playerSolutionEvent G p h.nature h.decision := by
  funext strat
  exact propext (allEvents_playerSolutionEventsInOrdering_iff G ϕ p h strat)

theorem allEvents_ownedAgentsInList_eq_playerPastConsistent (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P)
    (h : G.toWModel.H) (pref rest : List G.A) (a : G.agents p)
    (hdecomp : pref ++ (a : G.A) :: rest = (ϕ h).val) :
    allEvents ((ownedAgentsInList G p pref).map
      (fun b => playerAgentSolutionEvent G p h b)) =
        playerPastConsistent G ϕ p a h := by
  classical
  have hlist :
      ownedAgentsInList G p pref = playerPastAgentsInOrdering G ϕ p a h :=
    ownedAgentsInList_eq_past_of_decomp G ϕ p h pref rest a hdecomp
  funext strat
  apply propext
  constructor
  · intro hall b hb
    have hbpref : b ∈ ownedAgentsInList G p pref := by
      simpa [hlist] using hb
    have hevent :
        playerAgentSolutionEvent G p h b strat := by
      exact hall (playerAgentSolutionEvent G p h b)
        (List.mem_map.2 ⟨b, hbpref, rfl⟩)
    exact hevent.symm
  · intro hpast E hE
    rcases List.mem_map.1 hE with ⟨b, hb, rfl⟩
    have hbPast : b ∈ playerPastAgentsInOrdering G ϕ p a h := by
      simpa [← hlist] using hb
    exact (hpast b hbPast).symm

open Classical in
noncomputable def playerChainFallback (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P)
    (fallback : BehavioralStrategy G p) (h : G.toWModel.H) :
    List (PlayerStrategySpace G p → Prop) →
      (PlayerStrategySpace G p → Prop) → ENNReal :=
  fun pref _event =>
    match (playerAgentsInOrdering G ϕ p h).drop pref.length with
    | [] => 0
    | a :: _ => (fallback a).kernel h (h.decision a)

theorem playerAgentsInOrdering_decomp_of_raw_decomp (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P)
    (h : G.toWModel.H) (pref rest : List G.A) (a : G.agents p)
    (hdecomp : pref ++ (a : G.A) :: rest = (ϕ h).val) :
    playerAgentsInOrdering G ϕ p h =
      ownedAgentsInList G p pref ++ a :: ownedAgentsInList G p rest := by
  classical
  have haowner : G.owner (a : G.A) = p :=
    (Finset.mem_filter.mp a.property).2
  unfold playerAgentsInOrdering
  rw [← hdecomp, ownedAgentsInList_append]
  simp [ownedAgentsInList, haowner]

theorem playerChainFallback_eq_current (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P)
    (fallback : BehavioralStrategy G p) (h : G.toWModel.H)
    (pref rest : List G.A) (a : G.agents p)
    (hdecomp : pref ++ (a : G.A) :: rest = (ϕ h).val) :
    playerChainFallback G ϕ p fallback h
        ((ownedAgentsInList G p pref).map
          (fun b => playerAgentSolutionEvent G p h b))
        (playerAgentSolutionEvent G p h a) =
      (fallback a).kernel h (h.decision a) := by
  classical
  have hagents :=
    playerAgentsInOrdering_decomp_of_raw_decomp G ϕ p h pref rest a hdecomp
  unfold playerChainFallback
  rw [hagents]
  simp

open Classical in
theorem playerSolutionEvent_mass_eq_chainProduct (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P)
    (μp : MixedStrategy G p) (h : G.toWModel.H)
    (fallback : List (PlayerStrategySpace G p → Prop) →
      (PlayerStrategySpace G p → Prop) → ENNReal) :
    pmfMass (μ := μp) (playerSolutionEvent G p h.nature h.decision) =
      condEventChainProduct μp (fun _ : PlayerStrategySpace G p => True)
        (playerSolutionEventsInOrdering G ϕ p h) fallback := by
  rw [← allEvents_playerSolutionEventsInOrdering_eq G ϕ p h]
  exact pmfMass_event_chain μp (playerSolutionEventsInOrdering G ϕ p h) fallback

theorem playerPastConsistent_eq_of_info (G : WGame)
    (ϕ : ConfigOrdering G.toWModel)
    (p : G.P) (hpr : PerfectRecall G ϕ p)
    (a : G.agents p) {h h' : G.toWModel.H}
    (hinfo : (G.toWModel.info (a : G.A)).r h h') :
    playerPastConsistent G ϕ p a h =
      playerPastConsistent G ϕ p a h' := by
  classical
  funext strat
  apply propext
  let κ : OrderingPrefix G.toWModel :=
    prefixThroughInOrdering G.toWModel ϕ (a : G.A) h
  have hne : κ.val ≠ [] :=
    prefixThroughInOrdering_ne_nil G.toWModel ϕ (a : G.A) h
  have hlast : κ.last hne = (a : G.A) :=
    prefixThroughInOrdering_last G.toWModel ϕ (a : G.A) h hne
  have haowner : G.owner (a : G.A) = p :=
    (Finset.mem_filter.mp a.property).2
  have hmem : h ∈ configSet G.toWModel ϕ κ :=
    prefixThroughInOrdering_mem_configSet G.toWModel ϕ (a : G.A) h
  have hinfoLast : (G.toWModel.info (κ.last hne)).r h h' := by
    rw [hlast]
    exact hinfo
  have hpr_at := hpr κ hne (by simpa [hlast] using haowner) h h' hmem hinfoLast
  have hmem' : h' ∈ configSet G.toWModel ϕ κ := hpr_at.1
  have hrec :
      (playerChoiceEquiv G κ.predecessors p).r h h' :=
    hpr_at.2
  have hpastMem : ∀ b : G.agents p,
      b ∈ playerPastAgentsInOrdering G ϕ p a h ↔
        b ∈ playerPastAgentsInOrdering G ϕ p a h' :=
    fun b => playerPastAgentsInOrdering_mem_iff_of_info G ϕ p hpr a b hinfo
  constructor
  · intro hpast b hbpred'
    have hbpred : b ∈ playerPastAgentsInOrdering G ϕ p a h := by
      exact (hpastMem b).2 hbpred'
    have hbκ : (b : G.A) ∈ κ.predecessors := by
      exact mem_playerPastAgentsInOrdering_predecessors G ϕ p a b h hbpred
    have hbowner : G.owner (b : G.A) = p :=
      (Finset.mem_filter.mp b.property).2
    have hbchoice := hrec (b : G.A) hbκ hbowner
    calc
      (strat b).act h' = (strat b).act h :=
        ((strat b).meas h h' hbchoice.1).symm
      _ = h.decision b := hpast b hbpred
      _ = h'.decision b := hbchoice.2
  · intro hpast b hbpred
    have hbpred' : b ∈ playerPastAgentsInOrdering G ϕ p a h' := by
      exact (hpastMem b).1 hbpred
    have hbκ : (b : G.A) ∈ κ.predecessors := by
      exact mem_playerPastAgentsInOrdering_predecessors G ϕ p a b h hbpred
    have hbowner : G.owner (b : G.A) = p :=
      (Finset.mem_filter.mp b.property).2
    have hbchoice := hrec (b : G.A) hbκ hbowner
    calc
      (strat b).act h = (strat b).act h' :=
        (strat b).meas h h' hbchoice.1
      _ = h'.decision b := hpast b hbpred'
      _ = h.decision b := hbchoice.2.symm

open Classical in
/-- The conditional behavioral kernel at a representative configuration. If
    the conditioning event has zero mixed-strategy mass, the supplied fallback
    behavioral strategy is used at that information class. -/
noncomputable def mixedToBehavioralKernelAt (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P) (μ : MixedStrategy G p)
    (fallback : BehavioralStrategy G p) (a : G.agents p)
    (h : G.toWModel.H) : PMF (G.U a) :=
  if hden : pmfMass (μ := μ) (playerPastConsistent G ϕ p a h) ≠ 0 then
    (pmfCond (μ := μ) (playerPastConsistent G ϕ p a h) hden).map
      (fun strat => (strat a).act h)
  else
    (fallback a).kernel h

/-- Measurability obligation for the conditional mixed-to-behavioral kernel. -/
def MixedToBehavioralMeasurable (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P) (μ : MixedStrategy G p)
    (fallback : BehavioralStrategy G p) : Prop :=
  ∀ (a : G.agents p) (h h' : G.toWModel.H),
    (G.toWModel.info a).r h h' →
      mixedToBehavioralKernelAt G ϕ p μ fallback a h =
        mixedToBehavioralKernelAt G ϕ p μ fallback a h'

theorem mixedToBehavioralMeasurable_of_perfectRecall (G : WGame)
    (ϕ : ConfigOrdering G.toWModel)
    (p : G.P) (hpr : PerfectRecall G ϕ p)
    (μ : MixedStrategy G p) (fallback : BehavioralStrategy G p) :
    MixedToBehavioralMeasurable G ϕ p μ fallback := by
  classical
  intro a h h' hinfo
  have hpast :
      playerPastConsistent G ϕ p a h =
        playerPastConsistent G ϕ p a h' :=
    playerPastConsistent_eq_of_info G ϕ p hpr a hinfo
  have hact : ∀ strat : PlayerStrategySpace G p,
      (strat a).act h = (strat a).act h' := by
    intro strat
    exact (strat a).meas h h' hinfo
  unfold mixedToBehavioralKernelAt
  by_cases hden : pmfMass (μ := μ) (playerPastConsistent G ϕ p a h) ≠ 0
  · have hden' :
        pmfMass (μ := μ) (playerPastConsistent G ϕ p a h') ≠ 0 := by
      rwa [← hpast]
    simp only [dif_pos hden, dif_pos hden']
    have hcond :
        pmfCond (μ := μ) (playerPastConsistent G ϕ p a h') hden' =
          pmfCond (μ := μ) (playerPastConsistent G ϕ p a h) hden := by
      ext strat
      simp [pmfCond_apply, pmfMask, hpast]
    rw [hcond]
    congr 1
    funext strat
    exact hact strat
  · have hden' :
        ¬ pmfMass (μ := μ) (playerPastConsistent G ϕ p a h') ≠ 0 := by
      rwa [← hpast]
    simp only [dif_neg hden, dif_neg hden']
    exact (fallback a).meas h h' hinfo

open Classical in
/-- **Proposition 15 construction**: a mixed strategy induces a behavioral
    strategy by conditioning on the player's own past-consistency event from
    formula (29). Zero-denominator classes use the supplied measurable
    fallback. -/
noncomputable def mixedToBehavioral (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P) (μ : MixedStrategy G p)
    (fallback : BehavioralStrategy G p)
    (hmeas : MixedToBehavioralMeasurable G ϕ p μ fallback) :
    BehavioralStrategy G p :=
  fun a => {
    kernel := fun h => mixedToBehavioralKernelAt G ϕ p μ fallback a h
    meas := fun h h' hequiv => hmeas a h h' hequiv
  }

open Classical in
theorem condEventFactor_playerPast_eq_kernel (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P)
    (μp : MixedStrategy G p) (fallback : BehavioralStrategy G p)
    (hmeas : MixedToBehavioralMeasurable G ϕ p μp fallback)
    (h : G.toWModel.H) (a : G.agents p) :
    condEventFactor μp (playerPastConsistent G ϕ p a h)
        (playerAgentSolutionEvent G p h a)
        ((fallback a).kernel h (h.decision a)) =
      ((mixedToBehavioral G ϕ p μp fallback hmeas) a).kernel h (h.decision a) := by
  classical
  unfold condEventFactor mixedToBehavioral mixedToBehavioralKernelAt
  by_cases hden : pmfMass (μ := μp) (playerPastConsistent G ϕ p a h) ≠ 0
  · simp only [dif_pos hden]
    rw [show
        PMF.map (fun strat : PlayerStrategySpace G p => (strat a).act h)
            (pmfCond μp (playerPastConsistent G ϕ p a h) hden) =
          pushforward
            (pmfCond μp (playerPastConsistent G ϕ p a h) hden)
            (fun strat : PlayerStrategySpace G p => (strat a).act h) by
        rfl]
    rw [pushforward_apply_eq_pmfMass]
    apply congrArg (pmfMass (μ := pmfCond μp (playerPastConsistent G ϕ p a h) hden))
    funext strat
    exact propext ⟨fun hs => hs.symm, fun hs => hs.symm⟩
  · simp only [dif_neg hden]

open Classical in
/-- A constant fallback behavioral strategy used on zero-denominator
    information classes. -/
noncomputable def defaultBehavioralStrategy (G : WGame) (p : G.P) :
    BehavioralStrategy G p :=
  fun a => {
    kernel := fun _ => PMF.pure (Classical.choice (inferInstance : Nonempty (G.U a)))
    meas := fun _ _ _ => rfl
  }

open Classical in
theorem mixedToBehavioral_chainProduct_aux (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P)
    (μp : MixedStrategy G p) (fallback : BehavioralStrategy G p)
    (hmeas : MixedToBehavioralMeasurable G ϕ p μp fallback)
    (h : G.toWModel.H) (pref rest : List G.A)
    (hdecomp : pref ++ rest = (ϕ h).val) :
    pmfMass (μ := μp)
        (allEvents ((ownedAgentsInList G p pref).map
          (fun a => playerAgentSolutionEvent G p h a))) *
      condEventChainProduct μp
        (allEvents ((ownedAgentsInList G p pref).map
          (fun a => playerAgentSolutionEvent G p h a)))
        ((ownedAgentsInList G p rest).map
          (fun a => playerAgentSolutionEvent G p h a))
        (fun relPref E =>
          playerChainFallback G ϕ p fallback h
            (((ownedAgentsInList G p pref).map
              (fun a => playerAgentSolutionEvent G p h a)) ++ relPref) E) =
    pmfMass (μ := μp)
        (allEvents ((ownedAgentsInList G p pref).map
          (fun a => playerAgentSolutionEvent G p h a))) *
      (List.map
        (fun a =>
          ((mixedToBehavioral G ϕ p μp fallback hmeas) a).kernel h
            (h.decision a))
        (ownedAgentsInList G p rest)).prod := by
  classical
  induction rest generalizing pref with
  | nil =>
      simp [ownedAgentsInList, condEventChainProduct]
  | cons x xs ih =>
      by_cases hx : G.owner x = p
      · let ax : G.agents p := ⟨x, by simp [WGame.agents, hx]⟩
        have hdecomp_ax : pref ++ (ax : G.A) :: xs = (ϕ h).val := by
          simpa [ax] using hdecomp
        have hdecomp_tail : (pref ++ [x]) ++ xs = (ϕ h).val := by
          simpa [List.append_assoc] using hdecomp
        have hprefix_append :
            ownedAgentsInList G p (pref ++ [x]) =
              ownedAgentsInList G p pref ++ [ax] := by
          simpa [ax] using ownedAgentsInList_append_singleton_of_owner G p pref hx
        have hpastEq :
            allEvents ((ownedAgentsInList G p pref).map
              (fun a => playerAgentSolutionEvent G p h a)) =
              playerPastConsistent G ϕ p ax h :=
          allEvents_ownedAgentsInList_eq_playerPastConsistent G ϕ p h pref xs ax
            hdecomp_ax
        have hfallback :
            playerChainFallback G ϕ p fallback h
                ((ownedAgentsInList G p pref).map
                  (fun a => playerAgentSolutionEvent G p h a))
                (playerAgentSolutionEvent G p h ax) =
              (fallback ax).kernel h (h.decision ax) :=
          playerChainFallback_eq_current G ϕ p fallback h pref xs ax hdecomp_ax
        have hfactor :
            condEventFactor μp
                (allEvents ((ownedAgentsInList G p pref).map
                  (fun a => playerAgentSolutionEvent G p h a)))
                (playerAgentSolutionEvent G p h ax)
                (playerChainFallback G ϕ p fallback h
                  ((ownedAgentsInList G p pref).map
                    (fun a => playerAgentSolutionEvent G p h a))
                  (playerAgentSolutionEvent G p h ax)) =
              ((mixedToBehavioral G ϕ p μp fallback hmeas) ax).kernel h
                (h.decision ax) := by
          rw [hpastEq, hfallback]
          exact condEventFactor_playerPast_eq_kernel G ϕ p μp fallback hmeas h ax
        have hih := ih (pref ++ [x]) hdecomp_tail
        by_cases hpast_ne :
            pmfMass (μ := μp)
                (allEvents ((ownedAgentsInList G p pref).map
                  (fun a => playerAgentSolutionEvent G p h a))) ≠ 0
        · have hstep :
              pmfMass (μ := μp)
                  (allEvents ((ownedAgentsInList G p (pref ++ [x])).map
                    (fun a => playerAgentSolutionEvent G p h a))) =
                pmfMass (μ := μp)
                    (allEvents ((ownedAgentsInList G p pref).map
                      (fun a => playerAgentSolutionEvent G p h a))) *
                  condEventFactor μp
                    (allEvents ((ownedAgentsInList G p pref).map
                      (fun a => playerAgentSolutionEvent G p h a)))
                    (playerAgentSolutionEvent G p h ax)
                    (playerChainFallback G ϕ p fallback h
                      ((ownedAgentsInList G p pref).map
                        (fun a => playerAgentSolutionEvent G p h a))
                      (playerAgentSolutionEvent G p h ax)) := by
            rw [hprefix_append, List.map_append]
            simp only [List.map_cons, List.map_nil]
            rw [allEvents_append_singleton]
            rw [pmfMass_and_eq_mul_cond μp
              (allEvents ((ownedAgentsInList G p pref).map
                (fun a => playerAgentSolutionEvent G p h a)))
              (playerAgentSolutionEvent G p h ax) hpast_ne]
            simp [condEventFactor, hpast_ne]
          exact calc
          pmfMass (μ := μp)
              (allEvents ((ownedAgentsInList G p pref).map
                (fun a => playerAgentSolutionEvent G p h a))) *
            condEventChainProduct μp
              (allEvents ((ownedAgentsInList G p pref).map
                (fun a => playerAgentSolutionEvent G p h a)))
              ((ownedAgentsInList G p (x :: xs)).map
                (fun a => playerAgentSolutionEvent G p h a))
              (fun relPref E =>
                playerChainFallback G ϕ p fallback h
                  (((ownedAgentsInList G p pref).map
                    (fun a => playerAgentSolutionEvent G p h a)) ++ relPref) E)
              =
            (pmfMass (μ := μp)
                (allEvents ((ownedAgentsInList G p pref).map
                  (fun a => playerAgentSolutionEvent G p h a))) *
              condEventFactor μp
                (allEvents ((ownedAgentsInList G p pref).map
                  (fun a => playerAgentSolutionEvent G p h a)))
                (playerAgentSolutionEvent G p h ax)
                (playerChainFallback G ϕ p fallback h
                  ((ownedAgentsInList G p pref).map
                    (fun a => playerAgentSolutionEvent G p h a))
                  (playerAgentSolutionEvent G p h ax))) *
              condEventChainProduct μp
                (fun strat =>
                  allEvents ((ownedAgentsInList G p pref).map
                    (fun a => playerAgentSolutionEvent G p h a)) strat ∧
                    playerAgentSolutionEvent G p h ax strat)
                ((ownedAgentsInList G p xs).map
                  (fun a => playerAgentSolutionEvent G p h a))
                (fun relPref E =>
                  playerChainFallback G ϕ p fallback h
                    (((ownedAgentsInList G p pref).map
                      (fun a => playerAgentSolutionEvent G p h a)) ++
                        playerAgentSolutionEvent G p h ax :: relPref) E) := by
              simp [ownedAgentsInList, hx, ax, condEventChainProduct, mul_assoc]
          _ =
            pmfMass (μ := μp)
                (allEvents ((ownedAgentsInList G p (pref ++ [x])).map
                  (fun a => playerAgentSolutionEvent G p h a))) *
              condEventChainProduct μp
                (allEvents ((ownedAgentsInList G p (pref ++ [x])).map
                  (fun a => playerAgentSolutionEvent G p h a)))
                ((ownedAgentsInList G p xs).map
                  (fun a => playerAgentSolutionEvent G p h a))
                (fun relPref E =>
                  playerChainFallback G ϕ p fallback h
                    (((ownedAgentsInList G p (pref ++ [x])).map
                      (fun a => playerAgentSolutionEvent G p h a)) ++ relPref) E) := by
              rw [hstep]
              rw [hprefix_append, List.map_append]
              simp [allEvents_append_singleton, List.append_assoc, mul_assoc]
          _ =
            pmfMass (μ := μp)
                (allEvents ((ownedAgentsInList G p (pref ++ [x])).map
                  (fun a => playerAgentSolutionEvent G p h a))) *
              (List.map
                (fun a =>
                  ((mixedToBehavioral G ϕ p μp fallback hmeas) a).kernel h
                    (h.decision a))
                (ownedAgentsInList G p xs)).prod := hih
          _ =
            (pmfMass (μ := μp)
                (allEvents ((ownedAgentsInList G p pref).map
                  (fun a => playerAgentSolutionEvent G p h a))) *
              ((mixedToBehavioral G ϕ p μp fallback hmeas) ax).kernel h
                (h.decision ax)) *
              (List.map
                (fun a =>
                  ((mixedToBehavioral G ϕ p μp fallback hmeas) a).kernel h
                    (h.decision a))
                (ownedAgentsInList G p xs)).prod := by
              rw [hstep, hfactor]
          _ =
            pmfMass (μ := μp)
                (allEvents ((ownedAgentsInList G p pref).map
                  (fun a => playerAgentSolutionEvent G p h a))) *
              (List.map
                (fun a =>
                  ((mixedToBehavioral G ϕ p μp fallback hmeas) a).kernel h
                    (h.decision a))
                (ownedAgentsInList G p (x :: xs))).prod := by
              simp [ownedAgentsInList, hx, ax, mul_assoc]
        · have hpast_zero :
              pmfMass (μ := μp)
                  (allEvents ((ownedAgentsInList G p pref).map
                    (fun a => playerAgentSolutionEvent G p h a))) = 0 :=
            not_ne_iff.mp hpast_ne
          simp [ownedAgentsInList, hx, hpast_zero]
      · have hdecomp_tail : (pref ++ [x]) ++ xs = (ϕ h).val := by
          simpa [List.append_assoc] using hdecomp
        have hpref :
            ownedAgentsInList G p (pref ++ [x]) = ownedAgentsInList G p pref :=
          ownedAgentsInList_append_singleton_of_not_owner G p pref hx
        have hih := ih (pref ++ [x]) hdecomp_tail
        simpa [ownedAgentsInList, hx, hpref] using hih

-- ============================================================================
-- Kuhn's equivalence statement (Theorem 16)
-- ============================================================================

/-- Event-mass realization of a mixed strategy by a product-mixed strategy.
    This is the player-local proof obligation left after the general
    outcome-kernel expansion. -/
def KuhnEventRealizable (G : WGame) (p : G.P)
    (μp : MixedStrategy G p) : Prop :=
  ∃ πp : ProductMixedStrategy G p, PlayerEventMassEquivalent G p μp πp

/-- The player-local chain identity delivered by the mixed-to-behavioral
    construction. This is the remaining substantive identity needed for the
    hard direction of Kuhn's theorem. -/
def MixedToBehavioralEventMassIdentity (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P)
    (μp : MixedStrategy G p) (fallback : BehavioralStrategy G p)
    (hmeas : MixedToBehavioralMeasurable G ϕ p μp fallback) : Prop :=
  ∀ (ω : G.Ω) (u : ∀ a : G.A, G.U a),
    pmfMass (μ := μp) (playerSolutionEvent G p ω u) =
      ∏ a : G.agents p,
        ((mixedToBehavioral G ϕ p μp fallback hmeas) a).kernel ⟨ω, u⟩ (u a)

open Classical in
theorem mixedToBehavioral_eventMassIdentity (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P)
    (μp : MixedStrategy G p) (fallback : BehavioralStrategy G p)
    (hmeas : MixedToBehavioralMeasurable G ϕ p μp fallback) :
    MixedToBehavioralEventMassIdentity G ϕ p μp fallback hmeas := by
  classical
  intro ω u
  let h : G.toWModel.H := ⟨ω, u⟩
  have hdecomp : ([] : List G.A) ++ (ϕ h).val = (ϕ h).val := by simp
  have hchain :=
    mixedToBehavioral_chainProduct_aux G ϕ p μp fallback hmeas h []
      (ϕ h).val hdecomp
  have hchain' :
      condEventChainProduct μp (fun _ : PlayerStrategySpace G p => True)
          (playerSolutionEventsInOrdering G ϕ p h)
          (playerChainFallback G ϕ p fallback h) =
        (List.map
          (fun a =>
            ((mixedToBehavioral G ϕ p μp fallback hmeas) a).kernel h
              (h.decision a))
          (playerAgentsInOrdering G ϕ p h)).prod := by
    simpa [playerSolutionEventsInOrdering, playerAgentsInOrdering,
      ownedAgentsInList, pmfMass_true, condEventChainProduct] using hchain
  calc
    pmfMass (μ := μp) (playerSolutionEvent G p ω u)
        = condEventChainProduct μp (fun _ : PlayerStrategySpace G p => True)
            (playerSolutionEventsInOrdering G ϕ p h)
            (playerChainFallback G ϕ p fallback h) := by
          simpa [h] using
            playerSolutionEvent_mass_eq_chainProduct G ϕ p μp h
              (playerChainFallback G ϕ p fallback h)
    _ = (List.map
          (fun a =>
            ((mixedToBehavioral G ϕ p μp fallback hmeas) a).kernel h
              (h.decision a))
          (playerAgentsInOrdering G ϕ p h)).prod := hchain'
    _ = ∏ a : G.agents p,
          ((mixedToBehavioral G ϕ p μp fallback hmeas) a).kernel ⟨ω, u⟩
            (u a) := by
          simpa [h] using
            playerAgentsInOrdering_prod_eq_univ G ϕ p h
              (fun a =>
                ((mixedToBehavioral G ϕ p μp fallback hmeas) a).kernel h
                  (h.decision a))

/-- A behavioral strategy whose one-shot kernels satisfy the player-local
    event-mass identity yields a product-mixed strategy realizing the same
    event masses. -/
theorem kuhn_event_realizable_of_behavioral_event_mass (G : WGame)
    (p : G.P) (μp : MixedStrategy G p) (β : BehavioralStrategy G p)
    (hβ : ∀ (ω : G.Ω) (u : ∀ a : G.A, G.U a),
      pmfMass (μ := μp) (playerSolutionEvent G p ω u) =
        ∏ a : G.agents p, (β a).kernel ⟨ω, u⟩ (u a)) :
    KuhnEventRealizable G p μp := by
  classical
  rcases behavioral_realizes_productMixed G p β with ⟨πp, hπp⟩
  refine ⟨πp, ?_⟩
  intro ω u
  rw [hβ ω u, productMixed_playerSolutionEvent_mass_eq_prod G p πp ω u]
  apply Finset.prod_congr rfl
  intro a _ha
  simpa [eq_comm] using (hπp a ⟨ω, u⟩ (u a)).symm

/-- The mixed-to-behavioral construction realizes the required product-mixed
    strategy once its conditional chain identity is proved. -/
theorem kuhn_event_realizable_of_mixedToBehavioral_identity (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P)
    (μp : MixedStrategy G p) (fallback : BehavioralStrategy G p)
    (hmeas : MixedToBehavioralMeasurable G ϕ p μp fallback)
    (hid : MixedToBehavioralEventMassIdentity G ϕ p μp fallback hmeas) :
    KuhnEventRealizable G p μp := by
  exact kuhn_event_realizable_of_behavioral_event_mass G p μp
    (mixedToBehavioral G ϕ p μp fallback hmeas) hid

/-- Outcome-law equivalence from the player-local event-mass realization
    condition. -/
theorem kuhn_equivalence_of_event_realizable (G : WGame)
    (hsolv : Solvable G.toWModel)
    (p : G.P) (μp : MixedStrategy G p)
    (hreal : KuhnEventRealizable G p μp) :
    ∃ πp : ProductMixedStrategy G p,
      KuhnOutcomeEquivalent G hsolv p μp πp := by
  rcases hreal with ⟨πp, hπp⟩
  exact ⟨πp, kuhn_equivalence_of_player_event_mass G hsolv p μp πp hπp⟩

/-- **Kuhn's equivalence statement for W-games** (Theorem 16 shape).

    This is the paper's outcome-law equivalence, not a behavioral marginal
    equality: replacing player `p`'s mixed strategy by the product-mixed
    strategy must preserve the full distribution over all agents' decisions
    against every opponent mixed profile, pointwise in nature. -/
theorem kuhn_equivalence (G : WGame) (hsolv : Solvable G.toWModel)
    (ϕ : ConfigOrdering G.toWModel) (_hcausal : CausalWith G.toWModel ϕ)
    (p : G.P) (hpr : PerfectRecall G ϕ p) (μp : MixedStrategy G p) :
    ∃ πp : ProductMixedStrategy G p,
      KuhnOutcomeEquivalent G hsolv p μp πp := by
  classical
  let fallback := defaultBehavioralStrategy G p
  let hmeas :=
    mixedToBehavioralMeasurable_of_perfectRecall G ϕ p hpr μp fallback
  have hid :
      MixedToBehavioralEventMassIdentity G ϕ p μp fallback hmeas :=
    mixedToBehavioral_eventMassIdentity G ϕ p μp fallback hmeas
  have hreal :
      KuhnEventRealizable G p μp :=
    kuhn_event_realizable_of_mixedToBehavioral_identity G ϕ p μp fallback hmeas hid
  exact kuhn_equivalence_of_event_realizable G hsolv p μp hreal

/-- Kuhn outcome equivalence from the concrete mixed-to-behavioral chain
    identity. Perfect recall supplies measurability of the conditional
    behavioral strategy; the remaining identity is the finite chain-rule
    calculation over the realized player order. -/
theorem kuhn_equivalence_of_mixedToBehavioral_identity
    (G : WGame) (hsolv : Solvable G.toWModel)
    (ϕ : ConfigOrdering G.toWModel) (_hcausal : CausalWith G.toWModel ϕ)
    (p : G.P) (hpr : PerfectRecall G ϕ p) (μp : MixedStrategy G p)
    (fallback : BehavioralStrategy G p)
    (hid : MixedToBehavioralEventMassIdentity G ϕ p μp fallback
      (mixedToBehavioralMeasurable_of_perfectRecall G ϕ p hpr μp fallback)) :
    ∃ πp : ProductMixedStrategy G p,
      KuhnOutcomeEquivalent G hsolv p μp πp := by
  let hmeas :=
    mixedToBehavioralMeasurable_of_perfectRecall G ϕ p hpr μp fallback
  have hreal :
      KuhnEventRealizable G p μp :=
    kuhn_event_realizable_of_mixedToBehavioral_identity G ϕ p μp fallback hmeas hid
  exact kuhn_equivalence_of_event_realizable G hsolv p μp hreal

end Intrinsic
