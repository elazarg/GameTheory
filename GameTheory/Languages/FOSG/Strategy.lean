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

/-- The set of actions available to player `i` at world state `w`. -/
def availableActionsAtState
    (G : FOSG ι W Act PrivObs PubObs)
    (w : W) (i : ι) : Set (Act i) :=
  { ai | ∃ a : G.LegalAction w, a.1 i = some ai }

theorem mem_availableActionsAtState_iff
    {G : FOSG ι W Act PrivObs PubObs}
    {w : W} {i : ι} {ai : Act i} :
    ai ∈ G.availableActionsAtState w i ↔
      ∃ a : G.LegalAction w, a.1 i = some ai := by
  rfl

/-- Local legality of one player's optional action at world state `w`. -/
def locallyLegalAtState
    (G : FOSG ι W Act PrivObs PubObs)
    (w : W) (i : ι) : Option (Act i) → Prop
  | some ai => ai ∈ G.availableActionsAtState w i
  | none => i ∉ G.active w

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

theorem locallyLegalAtState_of_legal
    {G : FOSG ι W Act PrivObs PubObs}
    {w : W} {a : G.LegalAction w} (i : ι) :
    G.locallyLegalAtState w i (a.1 i) := by
  cases h : a.1 i with
  | none =>
      exact by
        intro hi
        rcases G.active_has_some (a := a) hi with ⟨ai, hai⟩
        simp [h] at hai
  | some ai =>
      exact ⟨a, h⟩

/-- Paper-facing factorization condition: a joint action is legal whenever each
player's local component is legal at the current world state. -/
def LegalityFactorizes
    (G : FOSG ι W Act PrivObs PubObs) : Prop :=
  ∀ {w : W} {a : JointAction Act},
    (∀ i, G.locallyLegalAtState w i (a i)) →
    G.legal w a

/-- The set of actions available to player `i` at the endpoint of history `h`. -/
def availableActions
    (G : FOSG ι W Act PrivObs PubObs)
    (h : G.History) (i : ι) : Set (Act i) :=
  { ai | ∃ a : G.LegalAction h.lastState, a.1 i = some ai }

theorem mem_availableActions_iff
    {G : FOSG ι W Act PrivObs PubObs}
    {h : G.History} {i : ι} {ai : Act i} :
    ai ∈ G.availableActions h i ↔
      ∃ a : G.LegalAction h.lastState, a.1 i = some ai := by
  rfl

theorem availableActions_eq_availableActionsAtState
    {G : FOSG ι W Act PrivObs PubObs}
    (h : G.History) (i : ι) :
    G.availableActions h i = G.availableActionsAtState h.lastState i := by
  rfl

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

theorem not_mem_availableActions_of_not_mem_active
    {G : FOSG ι W Act PrivObs PubObs}
    (h : G.History) {i : ι} (hi : i ∉ G.active h.lastState) :
    G.availableActions h i = ∅ := by
  ext ai
  constructor
  · intro hai
    rcases hai with ⟨a, ha⟩
    have hnone : a.1 i = none := G.inactive_eq_none (a := a) hi
    simp [hnone] at ha
  · intro hai
    simp at hai

theorem not_mem_availableActionsAtState_of_not_mem_active
    {G : FOSG ι W Act PrivObs PubObs}
    {w : W} {i : ι} (hi : i ∉ G.active w) :
    G.availableActionsAtState w i = ∅ := by
  ext ai
  constructor
  · intro hai
    rcases hai with ⟨a, ha⟩
    have hnone : a.1 i = none := G.inactive_eq_none (a := a) hi
    simp [hnone] at ha
  · intro hai
    simp at hai

theorem availableMoves_eq_singleton_none_of_not_mem_active
    {G : FOSG ι W Act PrivObs PubObs}
    (h : G.History) {i : ι} (hi : i ∉ G.active h.lastState) :
    G.availableMoves h i = {none} := by
  ext oi
  cases oi with
  | none =>
      simp [availableMoves, availableMovesAtState, locallyLegalAtState, hi]
  | some ai =>
      have hnone : G.availableActionsAtState h.lastState i = ∅ :=
        G.not_mem_availableActionsAtState_of_not_mem_active hi
      simp [availableMoves, availableMovesAtState, locallyLegalAtState, hnone]

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
    G.availableActions h i = G.availableActions h' i := by
  ext ai
  have hEq := G.availableMoves_eq_of_playerView_eq hLeg i hInfo
  have hmoves : some ai ∈ G.availableMoves h i ↔ some ai ∈ G.availableMoves h' i := by
    simp [hEq]
  rw [show ai ∈ G.availableActions h i ↔ some ai ∈ G.availableMoves h i by
      simp [availableActions, availableMoves, availableMovesAtState,
        locallyLegalAtState, availableActionsAtState]]
  rw [show ai ∈ G.availableActions h' i ↔ some ai ∈ G.availableMoves h' i by
      simp [availableActions, availableMoves, availableMovesAtState,
        locallyLegalAtState, availableActionsAtState]]
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
    G.availableActionsAtInfoState i (h.playerView i) = G.availableActions h i := by
  ext ai
  rw [show ai ∈ G.availableActionsAtInfoState i (h.playerView i) ↔
      some ai ∈ G.availableMovesAtInfoState i (h.playerView i) by rfl]
  rw [show ai ∈ G.availableActions h i ↔ some ai ∈ G.availableMoves h i by
      simp [availableActions, availableMoves, availableMovesAtState,
        locallyLegalAtState, availableActionsAtState]]
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
