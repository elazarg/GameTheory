import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-! Shared wire allocation for jittered two-coordinate color evaluation and cyclic feedback.
Every sample owns extraction, corner increments, interpolation, color circuits and weighted
indicators. The output count is a multiple of one hundred twenty-three for exact mean scaling. -/
namespace GameTheory.Complexity.Backend.BrouwerNashLayout

/-- Number of dyadic halving steps for jitter spacing and feedback scale. -/
def precision (b : ℕ) : ℕ := 5 * (b + 10)
/-- Two extended coordinate fields supplied to a color circuit. -/
def arity (b : ℕ) : ℕ := 2 * (b + 1)
/-- Shared coordinate, constant, scaling, averaging and feedback wires. -/
def globalCount (b : ℕ) : ℕ := 3 * precision b + 11
/-- Per-corner input copies and both scalar color circuits. -/
def cornerWidth (b ell₀ ell₁ : ℕ) : ℕ := 2 * arity b + ell₀ + ell₁
/-- All wires allocated to one jitter sample. -/
def sampleWidth (b ell₀ ell₁ : ℕ) : ℕ := 26 + 12 * b + 4 * cornerWidth b ell₀ ell₁
/-- Allocated wires, with one spare unit before integer scaling. -/
def units (b ell₀ ell₁ : ℕ) : ℕ := globalCount b + 41 * sampleWidth b ell₀ ell₁ + 1
/-- Pair-block dimension; unused blocks are assigned the affine zero gate. -/
def dimension (b ell₀ ell₁ : ℕ) : ℕ := 123 * units b ell₀ ell₁
/-- Coordinate wires are the two cyclic feedback outputs. -/
def coordinate (axis : Fin 2) : ℕ := axis.val
/-- A constant-one wire, followed by a constant-zero wire. -/
def one : ℕ := 2
/-- Constant-zero wire. -/
def zero : ℕ := 3
/-- The alpha chain starts at the shared one wire. -/
def alpha (j : ℕ) : ℕ := if j = 0 then one else 3 + j
/-- Positive feedback equals one third of the final dyadic scale. -/
def positive (b : ℕ) : ℕ := precision b + 4
/-- The two negative color-component means. -/
def average (b : ℕ) (axis : Fin 2) : ℕ := precision b + 5 + axis.val
/-- Each negative feedback mean has its own dyadic chain. -/
def negative (b : ℕ) (axis : Fin 2) (j : ℕ) : ℕ :=
  if j = 0 then average b axis else precision b + 7 + axis.val * precision b + (j - 1)
/-- Half-scale positive addition in the feedback cycle. -/
def feedbackHalf (b : ℕ) (axis : Fin 2) : ℕ := 3 * precision b + 7 + 2 * axis.val
/-- Negative subtraction precedes the final doubling into the coordinate wire. -/
def feedbackSub (b : ℕ) (axis : Fin 2) : ℕ := feedbackHalf b axis + 1
/-- Beginning of one sample's contiguous region. -/
def sampleBase (b ell₀ ell₁ : ℕ) (t : Fin 41) : ℕ :=
  globalCount b + t.val * sampleWidth b ell₀ ell₁
/-- Local jittered coordinate wires. -/
def jitter (axis : Fin 2) : ℕ := axis.val
/-- Extraction alternates a digit and the next remainder for each coordinate. -/
def digit (b : ℕ) (axis : Fin 2) (j : ℕ) : ℕ := 2 + 2 * b * axis.val + 2 * j
/-- The initial jitter input or a remainder after the requested number of extracted digits. -/
def remainder (b : ℕ) (axis : Fin 2) (j : ℕ) : ℕ :=
  if j = 0 then jitter axis else 3 + 2 * b * axis.val + 2 * (j - 1)
/-- Four Boolean gates per incremented bit: two literal conjunctions, OR and carry. -/
def incrementBase (b : ℕ) (axis : Fin 2) : ℕ := 2 + 4 * b + 4 * b * axis.val
/-- One of the four Boolean stages for a little-endian incremented bit. -/
def increment (b : ℕ) (axis : Fin 2) (j : ℕ) (stage : Fin 4) : ℕ :=
  incrementBase b axis + 4 * j + stage.val
/-- Eight affine gates implement the four canonical interpolation weights. -/
def weightBase (b : ℕ) : ℕ := 2 + 12 * b
/-- The complementary fractional coordinate for a selected axis. -/
def complement (b : ℕ) (axis : Fin 2) : ℕ := weightBase b + axis.val
/-- The intermediate clipped subtraction for a diagonal corner weight. -/
def weightTemporary (b : ℕ) (diagonal : Bool) : ℕ :=
  weightBase b + if diagonal then 4 else 2
/-- The final interpolation weight, ordered00,11,10,01. -/
def weight (b : ℕ) (corner : Fin 4) : ℕ :=
  weightBase b + (![3, 5, 6, 7] : Fin 4 → ℕ) corner
/-- Color input-copy and evaluation regions follow the interpolation gates. -/
def colorBase (b : ℕ) : ℕ := weightBase b + 8
/-- The start of the coordinate-copy region for a corner and color flag. -/
def colorInput (b ell₀ ell₁ : ℕ) (corner : Fin 4) (flag : Fin 2) : ℕ :=
  colorBase b + corner.val * cornerWidth b ell₀ ell₁ +
    (if flag.val = 0 then 0 else arity b + ell₀)
/-- The first compiled color gate following that flag’s copied coordinates. -/
def colorGate (b ell₀ ell₁ : ℕ) (corner : Fin 4) (flag : Fin 2) : ℕ :=
  colorInput b ell₀ ell₁ corner flag + arity b
/-- Each weighted color flag uses two clipped subtractions. -/
def minimumBase (b ell₀ ell₁ : ℕ) : ℕ := colorBase b + 4 * cornerWidth b ell₀ ell₁
/-- The intermediate clipped subtraction for a weighted corner color. -/
def minimumTemporary (b ell₀ ell₁ : ℕ) (corner : Fin 4) (flag : Fin 2) : ℕ :=
  minimumBase b ell₀ ell₁ + 2 * (2 * corner.val + flag.val)
/-- The final minimum of a corner weight and color indicator. -/
def minimum (b ell₀ ell₁ : ℕ) (corner : Fin 4) (flag : Fin 2) : ℕ :=
  minimumTemporary b ell₀ ell₁ corner flag + 1

/-- The source-independent spare padding guarantees positive dimension. -/
theorem dimension_pos (b ell₀ ell₁ : ℕ) : 0 < dimension b ell₀ ell₁ := by
  simp only [dimension, units]
  omega

/-- Exact divisibility is available for both third and forty-one-sample scaling. -/
theorem dimension_div (b ell₀ ell₁ : ℕ) :
    dimension b ell₀ ell₁ / 123 = units b ell₀ ell₁ := by
  simp [dimension]

/-- The allocated prefix fits strictly inside the game dimension. -/
theorem allocated_lt_dimension (b ell₀ ell₁ : ℕ) :
    globalCount b + 41 * sampleWidth b ell₀ ell₁ < dimension b ell₀ ell₁ := by
  simp only [dimension, units]
  omega

/-- Any shared wire has a canonical bounded index. -/
def globalSlot (b ell₀ ell₁ i : ℕ) (hi : i < globalCount b) :
    Fin (dimension b ell₀ ell₁) :=
  ⟨i, hi.trans_le ((Nat.le_add_right _ _).trans (allocated_lt_dimension b ell₀ ell₁).le)⟩

/-- Any local sample wire has a canonical bounded index. -/
theorem sample_lt_dimension (b ell₀ ell₁ : ℕ) (t : Fin 41) (i : ℕ)
    (hi : i < sampleWidth b ell₀ ell₁) :
    sampleBase b ell₀ ell₁ t + i < dimension b ell₀ ell₁ := by
  have ht : t.val + 1 ≤ 41 := by have hh := t.isLt; omega
  have hm := Nat.mul_le_mul_right (sampleWidth b ell₀ ell₁) ht
  have hs : t.val * sampleWidth b ell₀ ell₁ + i < 41 * sampleWidth b ell₀ ell₁ := by
    calc
      _ < t.val * sampleWidth b ell₀ ell₁ + sampleWidth b ell₀ ell₁ :=
        Nat.add_lt_add_left hi _
      _ = (t.val + 1) * sampleWidth b ell₀ ell₁ := by rw [Nat.add_mul]; simp
      _ ≤ _ := hm
  simpa only [sampleBase, Nat.add_assoc] using
    (Nat.add_lt_add_left hs (globalCount b)).trans (allocated_lt_dimension b ell₀ ell₁)

/-- Embed a local wire while preserving its explicit natural-number position. -/
def sampleSlot (b ell₀ ell₁ : ℕ) (t : Fin 41) (i : ℕ)
    (hi : i < sampleWidth b ell₀ ell₁) : Fin (dimension b ell₀ ell₁) :=
  ⟨sampleBase b ell₀ ell₁ t + i, sample_lt_dimension b ell₀ ell₁ t i hi⟩

end GameTheory.Complexity.Backend.BrouwerNashLayout
