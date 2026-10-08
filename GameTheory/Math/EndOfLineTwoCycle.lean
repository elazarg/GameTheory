import GameTheory.Math.EndOfLine

/-! Reciprocal pointers whose predecessor and successor coincide off the diagonal
form isolated two-cycles. Removing these components preserves every endpoint
and makes the two active neighbors of each remaining internal node distinct. -/

namespace GameTheory.Math.EndOfLine

variable {α : Type*} [DecidableEq α] (P S : α → α)

/-- Suppress the incoming edge of a two-cycle, retaining every other pointer. -/
def eraseTwoCyclePredecessor (x : α) : α := if P x = S x then x else P x

/-- Suppress the outgoing edge of a two-cycle, retaining every other pointer. -/
def eraseTwoCycleSuccessor (x : α) : α := if P x = S x then x else S x

/-- A retained predecessor is nontrivial exactly when the original pointer is
nontrivial and differs from the successor. -/
theorem eraseTwoCycle_predecessor_ne_self_iff (x : α) :
    eraseTwoCyclePredecessor P S x ≠ x ↔ P x ≠ x ∧ P x ≠ S x := by
  by_cases he : P x = S x <;> simp [eraseTwoCyclePredecessor, he]

/-- A retained successor is nontrivial exactly when the original pointer is
nontrivial and differs from the predecessor. -/
theorem eraseTwoCycle_successor_ne_self_iff (x : α) :
    eraseTwoCycleSuccessor P S x ≠ x ↔ S x ≠ x ∧ P x ≠ S x := by
  by_cases he : P x = S x <;> simp [eraseTwoCycleSuccessor, he]

/-- Removing a two-cycle preserves reciprocity of all other incoming edges. -/
theorem eraseTwoCycle_predecessor_consistent
    (hP : ∀ x, P x ≠ x → S (P x) = x) (x : α)
    (h : eraseTwoCyclePredecessor P S x ≠ x) :
    eraseTwoCycleSuccessor P S (eraseTwoCyclePredecessor P S x) = x := by
  obtain ⟨hp, hx⟩ := (eraseTwoCycle_predecessor_ne_self_iff P S x).mp h
  have hnext : P (P x) ≠ S (P x) := by
    intro he
    have hpp : P (P x) = x := he.trans (hP x hp)
    have hne : P (P x) ≠ P x := by rw [hpp]; exact Ne.symm hp
    have hback : S x = P x := by
      simpa only [hpp] using hP (P x) hne
    exact hx hback.symm
  rw [eraseTwoCyclePredecessor, ite_eq_right hx, eraseTwoCycleSuccessor,
    ite_eq_right hnext]
  exact hP x hp

/-- Removing a two-cycle preserves reciprocity of all other outgoing edges. -/
theorem eraseTwoCycle_successor_consistent
    (hS : ∀ x, S x ≠ x → P (S x) = x) (x : α)
    (h : eraseTwoCycleSuccessor P S x ≠ x) :
    eraseTwoCyclePredecessor P S (eraseTwoCycleSuccessor P S x) = x := by
  obtain ⟨hs, hx⟩ := (eraseTwoCycle_successor_ne_self_iff P S x).mp h
  have hnext : P (S x) ≠ S (S x) := by
    intro he
    have hss : S (S x) = x := he.symm.trans (hS x hs)
    have hne : S (S x) ≠ S x := by rw [hss]; exact Ne.symm hs
    have hback : P x = S x := by
      simpa only [hss] using hS (S x) hne
    exact hx hback
  rw [eraseTwoCycleSuccessor, ite_eq_right hx, eraseTwoCyclePredecessor,
    ite_eq_right hnext]
  exact hS x hs


/-- Incoming roles are retained precisely outside the removed two-cycles. -/
theorem eraseTwoCycle_hasPredecessor_iff
    (hP : ∀ x, P x ≠ x → S (P x) = x) (x : α) :
    HasPredecessor (eraseTwoCyclePredecessor P S) (eraseTwoCycleSuccessor P S) x ↔
      HasPredecessor P S x ∧ P x ≠ S x := by
  constructor
  · intro h
    obtain ⟨hp, hx⟩ := (eraseTwoCycle_predecessor_ne_self_iff P S x).mp h.1
    exact ⟨⟨hp, hP x hp⟩, hx⟩
  · rintro ⟨h, hx⟩
    have hp := (eraseTwoCycle_predecessor_ne_self_iff P S x).mpr ⟨h.1, hx⟩
    exact ⟨hp, eraseTwoCycle_predecessor_consistent P S hP x hp⟩

/-- Outgoing roles are retained precisely outside the removed two-cycles. -/
theorem eraseTwoCycle_hasSuccessor_iff
    (hS : ∀ x, S x ≠ x → P (S x) = x) (x : α) :
    HasSuccessor (eraseTwoCyclePredecessor P S) (eraseTwoCycleSuccessor P S) x ↔
      HasSuccessor P S x ∧ P x ≠ S x := by
  constructor
  · intro h
    obtain ⟨hs, hx⟩ := (eraseTwoCycle_successor_ne_self_iff P S x).mp h.1
    exact ⟨⟨hs, hS x hs⟩, hx⟩
  · rintro ⟨h, hx⟩
    have hs := (eraseTwoCycle_successor_ne_self_iff P S x).mpr ⟨h.1, hx⟩
    exact ⟨hs, eraseTwoCycle_successor_consistent P S hS x hs⟩

/-- Removing reciprocal two-cycles preserves every endpoint, in every component. -/
theorem eraseTwoCycle_isEndpoint_iff
    (hP : ∀ x, P x ≠ x → S (P x) = x)
    (hS : ∀ x, S x ≠ x → P (S x) = x) (x : α) :
    IsEndpoint (eraseTwoCyclePredecessor P S) (eraseTwoCycleSuccessor P S) x ↔
      IsEndpoint P S x := by
  unfold IsEndpoint
  rw [eraseTwoCycle_hasPredecessor_iff P S hP,
    eraseTwoCycle_hasSuccessor_iff P S hS]
  by_cases he : P x = S x
  · have hroles : HasSuccessor P S x ↔ HasPredecessor P S x := by
      constructor
      · intro h
        have hp : P x ≠ x := by simpa only [he] using h.1
        exact ⟨hp, hP x hp⟩
      · intro h
        have hs : S x ≠ x := by simpa only [he] using h.1
        exact ⟨hs, hS x hs⟩
    simp [he, hroles]
  · simp [he]

/-- A retained incident edge makes the predecessor and successor ports distinct. -/
theorem eraseTwoCycle_distinct_neighbors (x : α)
    (h : eraseTwoCyclePredecessor P S x ≠ x ∨ eraseTwoCycleSuccessor P S x ≠ x) :
    eraseTwoCyclePredecessor P S x ≠ eraseTwoCycleSuccessor P S x := by
  have hx : P x ≠ S x := by
    rcases h with hp | hs
    · exact ((eraseTwoCycle_predecessor_ne_self_iff P S x).mp hp).2
    · exact ((eraseTwoCycle_successor_ne_self_iff P S x).mp hs).2
  simpa only [eraseTwoCyclePredecessor, eraseTwoCycleSuccessor, ite_eq_right hx] using hx

omit [DecidableEq α] in
/-- Original endpoint labels cannot belong to a reciprocal two-cycle. -/
theorem endpoint_neighbors_distinct
    (hP : ∀ x, P x ≠ x → S (P x) = x)
    (hS : ∀ x, S x ≠ x → P (S x) = x) {x : α} (he : IsEndpoint P S x) : P x ≠ S x := by
  intro hx
  rcases he with ⟨hs, hn⟩ | ⟨hp, hn⟩
  · apply hn
    have hp : P x ≠ x := by simpa only [hx] using hs.1
    exact ⟨hp, hP x hp⟩
  · apply hn
    have hs : S x ≠ x := by simpa only [hx] using hp.1
    exact ⟨hs, hS x hs⟩

/-- Removing two-cycles preserves the known-source pointer promises. -/
theorem eraseTwoCycle_source
    (hS : ∀ x, S x ≠ x → P (S x) = x) (origin : α)
    (hp : P origin = origin) (hs : S origin ≠ origin) :
    eraseTwoCyclePredecessor P S origin = origin ∧
      eraseTwoCycleSuccessor P S origin ≠ origin ∧
      eraseTwoCyclePredecessor P S (eraseTwoCycleSuccessor P S origin) = origin := by
  have hx : P origin ≠ S origin := by rw [hp]; exact Ne.symm hs
  have hnext := (eraseTwoCycle_successor_ne_self_iff P S origin).mpr ⟨hs, hx⟩
  refine ⟨?_, hnext, eraseTwoCycle_successor_consistent P S hS origin hnext⟩
  rw [eraseTwoCyclePredecessor, ite_eq_right hx, hp]

-- A reciprocal two-cycle has no endpoints, but its two ports coincide.
example :
    (∀ x : Bool, Bool.not (Bool.not x) = x) ∧
    (∀ x : Bool, HasPredecessor Bool.not Bool.not x ∧ HasSuccessor Bool.not Bool.not x) ∧
    (∀ x : Bool, ¬IsEndpoint Bool.not Bool.not x) ∧
    (∀ x : Bool, eraseTwoCyclePredecessor Bool.not Bool.not x = x ∧
      eraseTwoCycleSuccessor Bool.not Bool.not x = x) := by decide

-- A genuine source-to-sink edge survives cleanup in both directions.
example :
    (∀ x : Bool, eraseTwoCyclePredecessor (fun _ => false) (fun _ => true) x = false) ∧
    (∀ x : Bool, eraseTwoCycleSuccessor (fun _ => false) (fun _ => true) x = true) := by decide

end GameTheory.Math.EndOfLine

