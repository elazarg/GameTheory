import GameTheory.Math.GridWireBounds

/-! A linear coordinate width leaves an inactive collar around the shifted,
size-six routed coloring. The collar separates its paths from the canonical
outer Sperner boundary. -/

namespace GameTheory.Math.GridWire

/-- Two original label widths and eight extra bits contain the scaled routing
rectangle with a full inactive macrotile margin. -/
theorem gridSpernerRouting_capacity (b : ℕ) :
    6 * (3 * (2 ^ b) * (2 ^ b) + 2) < 2 ^ (2 * b + 8) ∧
      6 * (6 * (2 ^ b) + 2) < 2 ^ (2 * b + 8) := by
  have hn : 1 ≤ 2 ^ b := by have h := Nat.two_pow_pos b; omega
  have hnn : 2 ^ b ≤ (2 ^ b) * (2 ^ b) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2 ^ b) hn
  have he : 2 ^ (2 * b + 8) = 256 * ((2 ^ b) * (2 ^ b)) := by
    have hb : 2 * b + 8 = b + b + 8 := by omega
    rw [hb]
    simp [pow_add, Nat.mul_assoc, Nat.mul_comm]
  rw [he, Nat.mul_assoc]
  omega

end GameTheory.Math.GridWire
