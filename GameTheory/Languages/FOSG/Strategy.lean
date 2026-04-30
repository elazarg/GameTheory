import GameTheory.Languages.FOSG.Information

/-!
# GameTheory.Languages.FOSG.Strategy

Strategy objects for FOSGs.

This file follows the paper's strategy shape up to a Lean-friendly adaptation:

- a player's legal moves are derived from the current history endpoint
- legality at an information state is expressed via an explicit invariance
  predicate `LegalObservable`
- strategies choose optional moves `Option (Act i)`, with `none` representing
  inactivity
- behavioral strategies are functions from information states to
  `PMF (Option (Act i))` together with a support constraint, rather than
  dependent codomains

The final section keeps a state-based legal-joint policy semantics as an
explicitly auxiliary construction.
-/

namespace GameTheory

open Math.Probability

namespace FOSG

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

/-- The set of optional moves available to player `i` at world state `w`. This
adds `none` exactly when player `i` is inactive at `w`. -/
def availableMovesAtState
    (G : FOSG ι W Act PrivObs PubObs)
    (w : W) (i : ι) : Set (Option (Act i)) :=
  { oi | G.locallyLegalAtState w i oi }

theorem mem_availableMovesAtState_iff
    {G : FOSG ι W Act PrivObs PubObs}
    {w : W} {i : ι} {oi : Option (Act i)} :
    oi ∈ G.availableMovesAtState w i ↔
      G.locallyLegalAtState w i oi := by
  rfl

/-- The set of actions available to player `i` at the endpoint of history `h`. -/
def availableActionsAtHistory
    (G : FOSG ι W Act PrivObs PubObs)
    (h : G.History) (i : ι) : Set (Act i) :=
  if i ∈ G.active h.lastState then G.availableActions h.lastState i else ∅

theorem mem_availableActionsAtHistory_iff
    {G : FOSG ι W Act PrivObs PubObs}
    {h : G.History} {i : ι} {ai : Act i} :
    ai ∈ G.availableActionsAtHistory h i ↔
      i ∈ G.active h.lastState ∧ ai ∈ G.availableActions h.lastState i := by
  simp [availableActionsAtHistory]

theorem availableActionsAtHistory_eq_availableActionsAtState_of_mem_active
    {G : FOSG ι W Act PrivObs PubObs}
    (h : G.History) (i : ι) (hi : i ∈ G.active h.lastState) :
    G.availableActionsAtHistory h i = G.availableActionsAtState h.lastState i := by
  simp [availableActionsAtHistory, hi]

theorem availableActionsAtHistory_eq_empty_of_not_mem_active
    {G : FOSG ι W Act PrivObs PubObs}
    (h : G.History) {i : ι} (hi : i ∉ G.active h.lastState) :
    G.availableActionsAtHistory h i = ∅ := by
  simp [availableActionsAtHistory, hi]

/-- The set of optional moves available to player `i` at the endpoint of
history `h`. -/
def availableMoves
    (G : FOSG ι W Act PrivObs PubObs)
    (h : G.History) (i : ι) : Set (Option (Act i)) :=
  G.availableMovesAtState h.lastState i

theorem mem_availableMoves_iff
    {G : FOSG ι W Act PrivObs PubObs}
    {h : G.History} {i : ι} {oi : Option (Act i)} :
    oi ∈ G.availableMoves h i ↔
      G.locallyLegalAtState h.lastState i oi := by
  simp [availableMoves, availableMovesAtState]

theorem availableMoves_eq_availableMovesAtState
    {G : FOSG ι W Act PrivObs PubObs}
    (h : G.History) (i : ι) :
    G.availableMoves h i = G.availableMovesAtState h.lastState i := by
  rfl

theorem availableMoves_eq_singleton_none_of_not_mem_active
    {G : FOSG ι W Act PrivObs PubObs}
    (h : G.History) {i : ι} (hi : i ∉ G.active h.lastState) :
    G.availableMoves h i = {none} := by
  ext oi
  cases oi with
  | none =>
      simp [availableMoves, availableMovesAtState, locallyLegalAtState, hi]
  | some ai =>
      simp [availableMoves, availableMovesAtState, locallyLegalAtState, hi]

/-- Lean-facing form of the paper's assumption that legal actions are
deducible from the player's information state. -/
def LegalObservable (G : FOSG ι W Act PrivObs PubObs) : Prop :=
  ∀ (i : ι) {h h' : G.History},
    h.playerView i = h'.playerView i →
    G.availableMoves h i = G.availableMoves h' i

theorem availableMoves_eq_of_playerView_eq
    {G : FOSG ι W Act PrivObs PubObs}
    (hLeg : G.LegalObservable) (i : ι)
    {h h' : G.History}
    (hInfo : h.playerView i = h'.playerView i) :
    G.availableMoves h i = G.availableMoves h' i :=
  hLeg i hInfo

theorem availableActions_eq_of_playerView_eq
    {G : FOSG ι W Act PrivObs PubObs}
    (hLeg : G.LegalObservable) (i : ι)
    {h h' : G.History}
    (hInfo : h.playerView i = h'.playerView i) :
    G.availableActionsAtHistory h i = G.availableActionsAtHistory h' i := by
  ext ai
  have hEq := G.availableMoves_eq_of_playerView_eq hLeg i hInfo
  have hmoves : some ai ∈ G.availableMoves h i ↔ some ai ∈ G.availableMoves h' i := by
    simp [hEq]
  rw [show ai ∈ G.availableActionsAtHistory h i ↔ some ai ∈ G.availableMoves h i by
      simp [availableActionsAtHistory, availableMoves, availableMovesAtState,
        locallyLegalAtState]]
  rw [show ai ∈ G.availableActionsAtHistory h' i ↔ some ai ∈ G.availableMoves h' i by
      simp [availableActionsAtHistory, availableMoves, availableMovesAtState,
        locallyLegalAtState]]
  exact hmoves

/-- The legal optional moves associated with an information state, defined as
the common move set across all realizing histories when `LegalObservable`
holds. -/
def availableMovesAtInfoState
    (G : FOSG ι W Act PrivObs PubObs)
    (i : ι) (s : G.InfoState i) : Set (Option (Act i)) :=
  { oi | ∃ h : G.History, h.playerView i = s ∧ oi ∈ G.availableMoves h i }

theorem mem_availableMovesAtInfoState_iff
    {G : FOSG ι W Act PrivObs PubObs}
    {i : ι} {s : G.InfoState i} {oi : Option (Act i)} :
    oi ∈ G.availableMovesAtInfoState i s ↔
      ∃ h : G.History, h.playerView i = s ∧ oi ∈ G.availableMoves h i := by
  rfl

theorem mem_availableMovesAtInfoState_of_history
    {G : FOSG ι W Act PrivObs PubObs}
    {i : ι} (h : G.History) {oi : Option (Act i)}
    (hoi : oi ∈ G.availableMoves h i) :
    oi ∈ G.availableMovesAtInfoState i (h.playerView i) := by
  exact ⟨h, rfl, hoi⟩

theorem availableMovesAtInfoState_eq_of_history
    {G : FOSG ι W Act PrivObs PubObs}
    (hLeg : G.LegalObservable) (i : ι) (h : G.History) :
    G.availableMovesAtInfoState i (h.playerView i) = G.availableMoves h i := by
  ext oi
  constructor
  · intro hoi
    rcases hoi with ⟨h', hh', hoi'⟩
    have hEq : G.availableMoves h' i = G.availableMoves h i :=
      G.availableMoves_eq_of_playerView_eq hLeg i hh'
    exact hEq ▸ hoi'
  · intro hoi
    exact G.mem_availableMovesAtInfoState_of_history h hoi

/-- The legal actual actions associated with an information state. -/
def availableActionsAtInfoState
    (G : FOSG ι W Act PrivObs PubObs)
    (i : ι) (s : G.InfoState i) : Set (Act i) :=
  { ai | some ai ∈ G.availableMovesAtInfoState i s }

theorem availableActionsAtInfoState_eq_of_history
    {G : FOSG ι W Act PrivObs PubObs}
    (hLeg : G.LegalObservable) (i : ι) (h : G.History) :
    G.availableActionsAtInfoState i (h.playerView i) = G.availableActionsAtHistory h i := by
  ext ai
  rw [show ai ∈ G.availableActionsAtInfoState i (h.playerView i) ↔
      some ai ∈ G.availableMovesAtInfoState i (h.playerView i) by rfl]
  rw [show ai ∈ G.availableActionsAtHistory h i ↔ some ai ∈ G.availableMoves h i by
      simp [availableActionsAtHistory, availableMoves, availableMovesAtState,
        locallyLegalAtState]]
  simp [availableMovesAtInfoState_eq_of_history hLeg i h]

/-- Pure strategy for player `i`: choose an optional move from each information
state. `none` represents inactivity. -/
abbrev PureStrategy (G : FOSG ι W Act PrivObs PubObs) (i : ι) : Type :=
  G.InfoState i → Option (Act i)

/-- Behavioral strategy for player `i`: a distribution over optional moves from
each information state. `none` represents inactivity. -/
abbrev BehavioralStrategy (G : FOSG ι W Act PrivObs PubObs) (i : ι) : Type :=
  G.InfoState i → PMF (Option (Act i))

/-- Joint pure strategy profile. -/
abbrev PureProfile (G : FOSG ι W Act PrivObs PubObs) : Type :=
  ∀ i, PureStrategy G i

/-- Joint behavioral strategy profile. -/
abbrev BehavioralProfile (G : FOSG ι W Act PrivObs PubObs) : Type :=
  ∀ i, BehavioralStrategy G i

namespace PureStrategy

variable {G : FOSG ι W Act PrivObs PubObs} {i : ι}

/-- Build a pure strategy from the latest private/public observation in the
information state, using `fallback` before any observation has been seen. -/
def ofLatestObservation
    (fallback : Option (Act i))
    (policy : PrivObs i × PubObs → Option (Act i)) :
    G.PureStrategy i :=
  fun s =>
    match InfoState.latestObservation? s with
    | none => fallback
    | some obs => policy obs

@[simp] theorem ofLatestObservation_nil
    (fallback : Option (Act i))
    (policy : PrivObs i × PubObs → Option (Act i)) :
    ofLatestObservation (G := G) (i := i) fallback policy [] = fallback := rfl

theorem ofLatestObservation_eq_policy
    {fallback : Option (Act i)}
    {policy : PrivObs i × PubObs → Option (Act i)}
    {s : G.InfoState i} {obs : PrivObs i × PubObs}
    (hobs : InfoState.latestObservation? s = some obs) :
    ofLatestObservation (G := G) (i := i) fallback policy s =
      policy obs := by
  simp [ofLatestObservation, hobs]

end PureStrategy

namespace BehavioralStrategy

variable {G : FOSG ι W Act PrivObs PubObs} {i : ι}

/-- Build a behavioral strategy from the latest private/public observation in
the information state, using `fallback` before any observation has been seen. -/
def ofLatestObservation
    (fallback : PMF (Option (Act i)))
    (policy : PrivObs i × PubObs → PMF (Option (Act i))) :
    G.BehavioralStrategy i :=
  fun s =>
    match InfoState.latestObservation? s with
    | none => fallback
    | some obs => policy obs

@[simp] theorem ofLatestObservation_nil
    (fallback : PMF (Option (Act i)))
    (policy : PrivObs i × PubObs → PMF (Option (Act i))) :
    ofLatestObservation (G := G) (i := i) fallback policy [] = fallback := rfl

theorem ofLatestObservation_eq_policy
    {fallback : PMF (Option (Act i))}
    {policy : PrivObs i × PubObs → PMF (Option (Act i))}
    {s : G.InfoState i} {obs : PrivObs i × PubObs}
    (hobs : InfoState.latestObservation? s = some obs) :
    ofLatestObservation (G := G) (i := i) fallback policy s =
      policy obs := by
  simp [ofLatestObservation, hobs]

end BehavioralStrategy

namespace PureProfile

variable {G : FOSG ι W Act PrivObs PubObs}

/-- Build a pure profile from player-indexed latest-observation policies. -/
def ofLatestObservation
    (fallback : ∀ i, Option (Act i))
    (policy : ∀ i, PrivObs i × PubObs → Option (Act i)) :
    G.PureProfile :=
  fun i =>
    PureStrategy.ofLatestObservation
      (G := G) (i := i) (fallback i) (policy i)

@[simp] theorem ofLatestObservation_nil
    (fallback : ∀ i, Option (Act i))
    (policy : ∀ i, PrivObs i × PubObs → Option (Act i))
    (i : ι) :
    ofLatestObservation (G := G) fallback policy i [] = fallback i := rfl

end PureProfile

namespace BehavioralProfile

variable {G : FOSG ι W Act PrivObs PubObs}

/-- Build a behavioral profile from player-indexed latest-observation
policies. -/
def ofLatestObservation
    (fallback : ∀ i, PMF (Option (Act i)))
    (policy : ∀ i, PrivObs i × PubObs → PMF (Option (Act i))) :
    G.BehavioralProfile :=
  fun i =>
    BehavioralStrategy.ofLatestObservation
      (G := G) (i := i) (fallback i) (policy i)

@[simp] theorem ofLatestObservation_nil
    (fallback : ∀ i, PMF (Option (Act i)))
    (policy : ∀ i, PrivObs i × PubObs → PMF (Option (Act i)))
    (i : ι) :
    ofLatestObservation (G := G) fallback policy i [] = fallback i := rfl

end BehavioralProfile

/-- A pure strategy is legal if at every realized history it chooses an
available move. -/
def IsLegalPureStrategy
    (G : FOSG ι W Act PrivObs PubObs)
    (i : ι) (σ : PureStrategy G i) : Prop :=
  ∀ h : G.History, σ (h.playerView i) ∈ G.availableMoves h i

/-- A behavioral strategy is legal if its support stays within the available
move set at every realized history. -/
def IsLegalBehavioralStrategy
    (G : FOSG ι W Act PrivObs PubObs)
    (i : ι) (σ : BehavioralStrategy G i) : Prop :=
  ∀ (h : G.History) {oi : Option (Act i)},
    oi ∈ (σ (h.playerView i)).support →
    oi ∈ G.availableMoves h i

/-- A pure profile is legal if every player's strategy is legal. -/
def IsLegalPureProfile
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : PureProfile G) : Prop :=
  ∀ i, G.IsLegalPureStrategy i (σ i)

/-- A behavioral profile is legal if every player's strategy is legal. -/
def IsLegalBehavioralProfile
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : BehavioralProfile G) : Prop :=
  ∀ i, G.IsLegalBehavioralStrategy i (σ i)

theorem legalBehavioralStrategy_eq_pure_none_of_not_mem_active
    {G : FOSG ι W Act PrivObs PubObs}
    {i : ι} {σ : BehavioralStrategy G i}
    (hσ : G.IsLegalBehavioralStrategy i σ)
    (h : G.History) (hi : i ∉ G.active h.lastState) :
    σ (h.playerView i) = PMF.pure none := by
  let p := σ (h.playerView i)
  have hsubset : p.support ⊆ ({none} : Set (Option (Act i))) := by
    intro oi hoi
    have hlegal : oi ∈ G.availableMoves h i := hσ h hoi
    simpa [G.availableMoves_eq_singleton_none_of_not_mem_active h hi] using hlegal
  have hnone : (none : Option (Act i)) ∈ p.support := by
    rcases p.support_nonempty with ⟨oi, hoi⟩
    have hoiNone : oi = none := by
      simpa using hsubset hoi
    simpa [hoiNone] using hoi
  have hsupport : p.support = ({none} : Set (Option (Act i))) := by
    refine Set.Subset.antisymm hsubset ?_
    intro oi hoi
    have hoi' : oi = none := by
      simpa using hoi
    subst oi
    exact hnone
  apply PMF.ext
  intro oi
  cases oi with
  | none =>
      simpa [p] using (PMF.apply_eq_one_iff p none).2 hsupport
  | some ai =>
      simpa using
        (PMF.apply_eq_zero_iff p (some ai)).2 (by simp [hsupport])

/-- The subtype of legal pure strategies for player `i`. -/
abbrev LegalPureStrategy
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) : Type :=
  { σ : PureStrategy G i // G.IsLegalPureStrategy i σ }

/-- The subtype of legal behavioral strategies for player `i`. -/
abbrev LegalBehavioralStrategy
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) : Type :=
  { σ : BehavioralStrategy G i // G.IsLegalBehavioralStrategy i σ }

/-- A profile of legal pure strategies. -/
abbrev LegalPureProfile
    (G : FOSG ι W Act PrivObs PubObs) : Type :=
  ∀ i, G.LegalPureStrategy i

/-- A profile of legal behavioral strategies. -/
abbrev LegalBehavioralProfile
    (G : FOSG ι W Act PrivObs PubObs) : Type :=
  ∀ i, G.LegalBehavioralStrategy i

/-- Forget the legality proofs on a legal pure profile. -/
abbrev LegalPureProfile.toProfile
    {G : FOSG ι W Act PrivObs PubObs}
    (σ : G.LegalPureProfile) : G.PureProfile :=
  fun i => (σ i).1

/-- Forget the legality proofs on a legal behavioral profile. -/
abbrev LegalBehavioralProfile.toProfile
    {G : FOSG ι W Act PrivObs PubObs}
    (σ : G.LegalBehavioralProfile) : G.BehavioralProfile :=
  fun i => (σ i).1

@[simp] theorem legalPureProfile_toProfile_apply
    {G : FOSG ι W Act PrivObs PubObs}
    (σ : G.LegalPureProfile) (i : ι) :
    σ.toProfile i = (σ i).1 := rfl

@[simp] theorem legalBehavioralProfile_toProfile_apply
    {G : FOSG ι W Act PrivObs PubObs}
    (σ : G.LegalBehavioralProfile) (i : ι) :
    σ.toProfile i = (σ i).1 := rfl

/-- Information states that are realized by at least one FOSG history. -/
def ReachableInfoState
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) : Type :=
  { s : G.InfoState i // ∃ h : G.History, h.playerView i = s }

/-- The reachable information state induced by a realized history. -/
def reachableInfoStateOfHistory
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) (h : G.History) :
    G.ReachableInfoState i :=
  ⟨h.playerView i, h, rfl⟩

@[simp] theorem reachableInfoStateOfHistory_val
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) (h : G.History) :
    (G.reachableInfoStateOfHistory i h).1 = h.playerView i := rfl

noncomputable instance instFintypeReachableInfoState
    (G : FOSG ι W Act PrivObs PubObs) [Fintype G.History] (i : ι) :
    Fintype (G.ReachableInfoState i) := by
  classical
  let f : G.History → G.ReachableInfoState i := fun h =>
    G.reachableInfoStateOfHistory i h
  have hf : Function.Surjective f := by
    intro s
    rcases s.2 with ⟨h, hs⟩
    refine ⟨h, ?_⟩
    apply Subtype.ext
    exact hs
  haveI : Finite (G.ReachableInfoState i) := Finite.of_surjective f hf
  exact Fintype.ofFinite (G.ReachableInfoState i)

/-- Pure strategy over reachable information states. -/
abbrev ReachablePureStrategy
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) : Type :=
  G.ReachableInfoState i → Option (Act i)

/-- Behavioral strategy over reachable information states. -/
abbrev ReachableBehavioralStrategy
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) : Type :=
  G.ReachableInfoState i → PMF (Option (Act i))

/-- Joint reachable pure strategy profile. -/
abbrev ReachablePureProfile (G : FOSG ι W Act PrivObs PubObs) : Type :=
  ∀ i, G.ReachablePureStrategy i

/-- Joint reachable behavioral strategy profile. -/
abbrev ReachableBehavioralProfile (G : FOSG ι W Act PrivObs PubObs) : Type :=
  ∀ i, G.ReachableBehavioralStrategy i

noncomputable instance instFintypeReachablePureStrategy
    (G : FOSG ι W Act PrivObs PubObs) [Fintype G.History]
    (i : ι) [Fintype (Option (Act i))] :
    Fintype (G.ReachablePureStrategy i) := by
  classical
  dsimp [ReachablePureStrategy]
  infer_instance

noncomputable instance instFintypeReachablePureProfile
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [Fintype G.History] [∀ i, Fintype (Option (Act i))] :
    Fintype G.ReachablePureProfile := by
  classical
  dsimp [ReachablePureProfile, ReachablePureStrategy]
  infer_instance

/-- A reachable pure strategy is legal if it chooses an available move at every
realizing history. -/
def IsLegalReachablePureStrategy
    (G : FOSG ι W Act PrivObs PubObs)
    (i : ι) (σ : G.ReachablePureStrategy i) : Prop :=
  ∀ h : G.History, σ (G.reachableInfoStateOfHistory i h) ∈ G.availableMoves h i

/-- A reachable behavioral strategy is legal if its support stays within the
available move set at every realizing history. -/
def IsLegalReachableBehavioralStrategy
    (G : FOSG ι W Act PrivObs PubObs)
    (i : ι) (σ : G.ReachableBehavioralStrategy i) : Prop :=
  ∀ (h : G.History) {oi : Option (Act i)},
    oi ∈ (σ (G.reachableInfoStateOfHistory i h)).support →
      oi ∈ G.availableMoves h i

/-- The subtype of legal reachable pure strategies for player `i`. -/
abbrev ReachableLegalPureStrategy
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) : Type :=
  { σ : G.ReachablePureStrategy i // G.IsLegalReachablePureStrategy i σ }

/-- The subtype of legal reachable behavioral strategies for player `i`. -/
abbrev ReachableLegalBehavioralStrategy
    (G : FOSG ι W Act PrivObs PubObs) (i : ι) : Type :=
  { σ : G.ReachableBehavioralStrategy i // G.IsLegalReachableBehavioralStrategy i σ }

/-- A profile of legal reachable pure strategies. -/
abbrev ReachableLegalPureProfile (G : FOSG ι W Act PrivObs PubObs) : Type :=
  ∀ i, G.ReachableLegalPureStrategy i

/-- A profile of legal reachable behavioral strategies. -/
abbrev ReachableLegalBehavioralProfile (G : FOSG ι W Act PrivObs PubObs) : Type :=
  ∀ i, G.ReachableLegalBehavioralStrategy i

/-- Forget the legality proofs on a legal reachable pure profile. -/
abbrev ReachableLegalPureProfile.toProfile
    {G : FOSG ι W Act PrivObs PubObs}
    (σ : G.ReachableLegalPureProfile) : G.ReachablePureProfile :=
  fun i => (σ i).1

/-- Forget the legality proofs on a legal reachable behavioral profile. -/
abbrev ReachableLegalBehavioralProfile.toProfile
    {G : FOSG ι W Act PrivObs PubObs}
    (σ : G.ReachableLegalBehavioralProfile) : G.ReachableBehavioralProfile :=
  fun i => (σ i).1

/-- Restrict a global pure strategy to reachable information states. -/
def PureStrategy.restrictReachable
    {G : FOSG ι W Act PrivObs PubObs} {i : ι}
    (σ : G.PureStrategy i) : G.ReachablePureStrategy i :=
  fun s => σ s.1

/-- Restrict a global behavioral strategy to reachable information states. -/
def BehavioralStrategy.restrictReachable
    {G : FOSG ι W Act PrivObs PubObs} {i : ι}
    (σ : G.BehavioralStrategy i) : G.ReachableBehavioralStrategy i :=
  fun s => σ s.1

/-- Restrict a legal global pure strategy to reachable information states. -/
def LegalPureStrategy.restrictReachable
    {G : FOSG ι W Act PrivObs PubObs} {i : ι}
    (σ : G.LegalPureStrategy i) : G.ReachableLegalPureStrategy i :=
  ⟨σ.1.restrictReachable, by intro h; exact σ.2 h⟩

/-- Restrict a legal global behavioral strategy to reachable information states. -/
def LegalBehavioralStrategy.restrictReachable
    {G : FOSG ι W Act PrivObs PubObs} {i : ι}
    (σ : G.LegalBehavioralStrategy i) : G.ReachableLegalBehavioralStrategy i :=
  ⟨σ.1.restrictReachable, by intro h oi hoi; exact σ.2 h hoi⟩

/-- Extend a reachable pure strategy to the global information-state type using
`none` on unreachable states. -/
noncomputable def ReachablePureStrategy.extend
    {G : FOSG ι W Act PrivObs PubObs} {i : ι}
    (σ : G.ReachablePureStrategy i) : G.PureStrategy i := by
  classical
  exact fun s =>
    if h : ∃ h' : G.History, h'.playerView i = s then σ ⟨s, h⟩ else none

/-- Extend a reachable behavioral strategy to the global information-state type
using `PMF.pure none` on unreachable states. -/
noncomputable def ReachableBehavioralStrategy.extend
    {G : FOSG ι W Act PrivObs PubObs} {i : ι}
    (σ : G.ReachableBehavioralStrategy i) : G.BehavioralStrategy i := by
  classical
  exact fun s =>
    if h : ∃ h' : G.History, h'.playerView i = s then σ ⟨s, h⟩ else PMF.pure none

@[simp] theorem ReachablePureStrategy.extend_apply_history
    {G : FOSG ι W Act PrivObs PubObs} {i : ι}
    (σ : G.ReachablePureStrategy i) (h : G.History) :
    σ.extend (h.playerView i) = σ (G.reachableInfoStateOfHistory i h) := by
  classical
  unfold ReachablePureStrategy.extend
  rw [dif_pos (show ∃ h' : G.History, h'.playerView i = h.playerView i from ⟨h, rfl⟩)]
  apply congrArg σ
  apply Subtype.ext
  rfl

@[simp] theorem ReachableBehavioralStrategy.extend_apply_history
    {G : FOSG ι W Act PrivObs PubObs} {i : ι}
    (σ : G.ReachableBehavioralStrategy i) (h : G.History) :
    σ.extend (h.playerView i) = σ (G.reachableInfoStateOfHistory i h) := by
  classical
  unfold ReachableBehavioralStrategy.extend
  rw [dif_pos (show ∃ h' : G.History, h'.playerView i = h.playerView i from ⟨h, rfl⟩)]
  apply congrArg σ
  apply Subtype.ext
  rfl

/-- Extend a reachable pure profile to the global information-state type. -/
noncomputable def ReachablePureProfile.extend
    {G : FOSG ι W Act PrivObs PubObs}
    (σ : G.ReachablePureProfile) : G.PureProfile :=
  fun i => (σ i).extend

/-- Extend a reachable behavioral profile to the global information-state type. -/
noncomputable def ReachableBehavioralProfile.extend
    {G : FOSG ι W Act PrivObs PubObs}
    (σ : G.ReachableBehavioralProfile) : G.BehavioralProfile :=
  fun i => (σ i).extend

theorem ReachablePureStrategy.isLegal_extend
    {G : FOSG ι W Act PrivObs PubObs} {i : ι}
    {σ : G.ReachablePureStrategy i}
    (hσ : G.IsLegalReachablePureStrategy i σ) :
    G.IsLegalPureStrategy i σ.extend := by
  intro h
  simpa using hσ h

theorem ReachableBehavioralStrategy.isLegal_extend
    {G : FOSG ι W Act PrivObs PubObs} {i : ι}
    {σ : G.ReachableBehavioralStrategy i}
    (hσ : G.IsLegalReachableBehavioralStrategy i σ) :
    G.IsLegalBehavioralStrategy i σ.extend := by
  intro h oi hoi
  exact hσ h (by simpa using hoi)

/-- Extend a legal reachable pure profile to a legal global pure profile. -/
noncomputable def ReachableLegalPureProfile.extend
    {G : FOSG ι W Act PrivObs PubObs}
    (σ : G.ReachableLegalPureProfile) : G.LegalPureProfile :=
  fun i => ⟨(σ.toProfile i).extend,
    ReachablePureStrategy.isLegal_extend (G := G) (i := i) (σ := σ.toProfile i) (σ i).2⟩

/-- Extend a legal reachable behavioral profile to a legal global behavioral
profile. -/
noncomputable def ReachableLegalBehavioralProfile.extend
    {G : FOSG ι W Act PrivObs PubObs}
    (σ : G.ReachableLegalBehavioralProfile) : G.LegalBehavioralProfile :=
  fun i => ⟨(σ.toProfile i).extend,
    ReachableBehavioralStrategy.isLegal_extend (G := G) (i := i) (σ := σ.toProfile i) (σ i).2⟩

/-- Lift a pure profile to a behavioral one. -/
noncomputable def pureToBehavioral
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : PureProfile G) : BehavioralProfile G :=
  fun i s => PMF.pure (σ i s)

@[simp] theorem pureToBehavioral_apply
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : PureProfile G) (i : ι) (s : G.InfoState i) :
    G.pureToBehavioral σ i s = PMF.pure (σ i s) := rfl

theorem legalBehavioral_of_legalPure
    {G : FOSG ι W Act PrivObs PubObs}
    (σ : PureProfile G)
    (hσ : G.IsLegalPureProfile σ) :
    G.IsLegalBehavioralProfile (G.pureToBehavioral σ) := by
  intro i h ai hai
  rw [pureToBehavioral_apply] at hai
  rw [PMF.support_pure, Set.mem_singleton_iff] at hai
  subst hai
  exact hσ i h

/-- Lift a legal pure profile to a legal behavioral profile. -/
noncomputable def legalPureToBehavioral
    (G : FOSG ι W Act PrivObs PubObs)
    (σ : G.LegalPureProfile) : G.LegalBehavioralProfile :=
  fun i => ⟨G.pureToBehavioral σ.toProfile i, (G.legalBehavioral_of_legalPure σ.toProfile
    (by
      intro j h
      exact (σ j).2 h)) i⟩

namespace Auxiliary

/-- Auxiliary state-based legal joint-action policy. This is not the paper's
main strategy notion; it is kept only as a simple execution gadget. -/
abbrev MarkovJointPolicy (G : FOSG ι W Act PrivObs PubObs) : Type :=
  ∀ w, PMF (G.LegalAction w)

/-- Deterministic auxiliary state-based legal joint-action policy. -/
abbrev PureMarkovJointPolicy (G : FOSG ι W Act PrivObs PubObs) : Type :=
  ∀ w, G.LegalAction w

/-- Lift a pure legal-joint policy to a stochastic one. -/
noncomputable def pureMarkovToBehavioral
    (G : FOSG ι W Act PrivObs PubObs)
    (π : PureMarkovJointPolicy G) : MarkovJointPolicy G :=
  fun w => PMF.pure (π w)

@[simp] theorem pureMarkovToBehavioral_apply
    (G : FOSG ι W Act PrivObs PubObs)
    (π : PureMarkovJointPolicy G) (w : W) :
    pureMarkovToBehavioral G π w = PMF.pure (π w) := rfl

/-- Probability of a realized step under an auxiliary state-based policy. -/
noncomputable def stepProb
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G) (e : G.Step) : ENNReal :=
  (π e.src) e.act * (G.transition e.src e.act) e.dst

/-- Path probability of a list of realized steps under an auxiliary policy. -/
noncomputable def pathProb
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G) : List G.Step → ENNReal
  | [] => 1
  | e :: es => stepProb π e * pathProb π es

/-- Path probability of a realized history under an auxiliary policy. -/
noncomputable def prob
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G) (h : G.History) : ENNReal :=
  pathProb π h.steps

@[simp] theorem pathProb_nil
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G) :
    pathProb π [] = 1 := rfl

@[simp] theorem pathProb_cons
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G) (e : G.Step) (es : List G.Step) :
    pathProb π (e :: es) = stepProb π e * pathProb π es := rfl

@[simp] theorem prob_nil
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G) :
    prob π (History.nil G) = 1 := rfl

theorem pathProb_append_singleton
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G) (es : List G.Step) (e : G.Step) :
    pathProb π (es ++ [e]) = pathProb π es * stepProb π e := by
  induction es with
  | nil =>
      simp [pathProb, stepProb]
  | cons e₀ es ih =>
      simp [pathProb, stepProb, ih, mul_assoc]

@[simp] theorem prob_snoc
    {G : FOSG ι W Act PrivObs PubObs}
    (π : MarkovJointPolicy G)
    (h : G.History) (a : G.LegalAction h.lastState)
    (dst : W) (support : G.transition h.lastState a dst ≠ 0) :
    prob π (h.snoc a dst support) =
      prob π h * stepProb π ⟨h.lastState, a, dst, support⟩ := by
  simpa [prob, History.snoc] using
    pathProb_append_singleton π h.steps ⟨h.lastState, a, dst, support⟩

end Auxiliary

end FOSG

end GameTheory
