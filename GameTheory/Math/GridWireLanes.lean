import GameTheory.Math.GridWire

/-! Private wire columns and separated horizontal lanes keep routed edges away
from unrelated graph vertices. Incoming hooks meet only their designated target. -/

namespace GameTheory.Math.GridWire

/-- Distinct graph vertices occupy distinct grid points. -/
theorem vertexPoint_injective : Function.Injective vertexPoint := by
  intro i j h
  have hy := congrArg Prod.snd h
  change 6 * i = 6 * j at hy
  omega

/-- A bounded second coordinate makes the ordered-pair column allocation injective. -/
theorem wireColumn_eq_iff {n i j k l : ℕ} (hj : j < n) (hl : l < n) :
    wireColumn n i j = wireColumn n k l ↔ i = k ∧ j = l := by
  constructor
  · intro h
    have hn : 0 < n := by omega
    have he : n * i + j = n * k + l := by unfold wireColumn at h; omega
    have hik : i = k := by
      have hd := congrArg (fun x => x / n) he
      simpa only [Nat.mul_add_div hn, Nat.div_eq_of_lt hj, Nat.div_eq_of_lt hl,
        Nat.add_zero] using hd
    rw [hik] at he
    exact ⟨hik, by omega⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Bounded vertex pairs use columns below the quadratic routing bound. -/
theorem wireColumn_lt {n i j : ℕ} (hi : i < n) (hj : j < n) :
    wireColumn n i j < 3 * (n * n) := by
  have hm := Nat.mul_le_mul_left n (show i + 1 ≤ n by omega)
  simp only [Nat.mul_add, Nat.mul_one] at hm
  unfold wireColumn
  omega

/-- Distinct allocated columns have at least three grid units between them. -/
theorem wireColumn_separated {n i j k l : ℕ} (hj : j < n) (hl : l < n)
    (hne : (i, j) ≠ (k, l)) :
    wireColumn n i j + 3 ≤ wireColumn n k l ∨
      wireColumn n k l + 3 ≤ wireColumn n i j := by
  have hc : wireColumn n i j ≠ wireColumn n k l := by
    intro h
    obtain ⟨hik, hjl⟩ := (wireColumn_eq_iff hj hl).mp h
    exact hne (Prod.ext hik hjl)
  unfold wireColumn at hc ⊢
  omega

/-- Outgoing rows never coincide with incoming rows. -/
theorem input_output_rows_ne (i j : ℕ) : 6 * i ≠ 6 * j + 3 := by omega

/-- Outgoing and incoming routing rows remain at least three grid units apart. -/
theorem input_output_rows_separated (i j : ℕ) :
    6 * i + 3 ≤ 6 * j + 3 ∨ (6 * j + 3) + 3 ≤ 6 * i := by omega

/-- An incoming horizontal lane contains no original graph vertex. -/
theorem incomingRow_ne_vertexPoint (j k x : ℕ) : (x, 6 * j + 3) ≠ vertexPoint k := by
  intro h
  have hy := congrArg Prod.snd h
  change 6 * j + 3 = 6 * k at hy
  omega

/-- The short incoming hook meets the row of exactly its target vertex. -/
theorem vertexPoint_on_hook_iff (j k : ℕ) :
    (6 * j ≤ (vertexPoint k).2 ∧ (vertexPoint k).2 ≤ 6 * j + 3) ↔ k = j := by
  simp only [vertexPoint]
  omega

/-- A routed non-loop edge visits no original vertices except its two endpoints. -/
theorem onWire_vertexPoint_iff {n i j : ℕ} (hi : i < n) (hne : i ≠ j) (k : ℕ) :
    onWire n i j (vertexPoint k) ↔ k = i ∨ k = j := by
  have hc := wireColumn_pos hi hne
  simp only [onWire, vertexPoint]
  constructor
  · rintro (hinput | hcolumn | hincoming | hhook)
    · left; omega
    · omega
    · omega
    · right; omega
  · rintro (rfl | rfl) <;> simp

end GameTheory.Math.GridWire
