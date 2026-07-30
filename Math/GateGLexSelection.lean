import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Algebra.Ring.Real

set_option autoImplicit false

noncomputable section

open Set

namespace Math
namespace GateGLexSelection

/--
On a nonempty compact set, a finite family of continuous real coordinates
admits a point which is successively minimal: after fixing all preceding
coordinates to their selected values, the next coordinate is minimal.
-/
theorem exists_lexMinOn
    {E : Type*} [TopologicalSpace E]
    (S : Set E) (hS : IsCompact S) (hne : S.Nonempty)
    (n : ℕ) (c : Fin n → E → ℝ)
    (hc : ∀ i, Continuous (c i)) :
    ∃ y ∈ S,
      ∀ (k : Fin n) (z : E), z ∈ S →
        (∀ j : Fin n, j < k → c j z = c j y) →
        c k y ≤ c k z := by
  induction n generalizing S with
  | zero =>
      obtain ⟨y, hy⟩ := hne
      exact ⟨y, hy, fun k => Fin.elim0 k⟩
  | succ n ih =>
      obtain ⟨y₀, hy₀S, hy₀⟩ :=
        hS.exists_isMinOn hne (hc 0).continuousOn
      rw [isMinOn_iff] at hy₀
      have hlevel_closed :
          IsClosed {x : E | c 0 x = c 0 y₀} :=
        isClosed_eq (hc 0) continuous_const
      let T : Set E := S ∩ {x : E | c 0 x = c 0 y₀}
      have hT : IsCompact T := hS.inter_right hlevel_closed
      have hy₀T : y₀ ∈ T := ⟨hy₀S, rfl⟩
      have hTne : T.Nonempty := ⟨y₀, hy₀T⟩
      obtain ⟨y, hyT, hy⟩ :=
        ih T hT hTne (fun j => c j.succ) (fun j => hc j.succ)
      have hyT' :
          y ∈ S ∩ {x : E | c 0 x = c 0 y₀} := by
        simpa [T] using hyT
      refine ⟨y, hyT.1, ?_⟩
      intro k z hz hprefix
      revert hprefix
      refine Fin.cases ?_ (fun k' hprefix => ?_) k
      · intro _
        exact hyT'.2.trans_le (hy₀ z hz)
      · have hzT : z ∈ T := by
          refine ⟨hz, ?_⟩
          calc
            c 0 z = c 0 y := hprefix 0 (by simp)
            _ = c 0 y₀ := hyT'.2
        apply hy k' z hzT
        intro j hj
        exact hprefix j.succ (by simpa using hj)

/--
First maximize a continuous score on a compact set, then choose a
lexicographically minimal point of the maximizing locus.
-/
theorem exists_lexMinOn_maximizers
    {E : Type*} [TopologicalSpace E]
    (S : Set E) (hS : IsCompact S) (hne : S.Nonempty)
    (score : E → ℝ) (hscore : Continuous score)
    (n : ℕ) (c : Fin n → E → ℝ)
    (hc : ∀ i, Continuous (c i)) :
    ∃ y ∈ S,
      (∀ z : E, z ∈ S → score z ≤ score y) ∧
      (∀ (k : Fin n) (z : E), z ∈ S →
        score z = score y →
        (∀ j : Fin n, j < k → c j z = c j y) →
        c k y ≤ c k z) := by
  obtain ⟨y₀, hy₀S, hy₀⟩ :=
    hS.exists_isMaxOn hne hscore.continuousOn
  rw [isMaxOn_iff] at hy₀
  have hlevel_closed :
      IsClosed {x : E | score x = score y₀} :=
    isClosed_eq hscore continuous_const
  let T : Set E := S ∩ {x : E | score x = score y₀}
  have hT : IsCompact T := hS.inter_right hlevel_closed
  have hy₀T : y₀ ∈ T := ⟨hy₀S, rfl⟩
  obtain ⟨y, hyT, hy⟩ :=
    exists_lexMinOn T hT ⟨y₀, hy₀T⟩ n c hc
  refine ⟨y, hyT.1, ?_, ?_⟩
  · intro z hz
    rw [hyT.2]
    exact hy₀ z hz
  · intro k z hz hscore_eq hprefix
    apply hy k z
    · exact ⟨hz, hscore_eq.trans hyT.2⟩
    · exact hprefix

/--
Maximizing the square of a score preserves nonvanishing whenever the compact
set contains one point at which the score is nonzero.
-/
theorem score_ne_zero_of_exists_nonzero_of_lexMinOn_maximizers
    {E : Type*} [TopologicalSpace E]
    (S : Set E) (hS : IsCompact S)
    (score : E → ℝ) (hscore : Continuous score)
    (n : ℕ) (c : Fin n → E → ℝ)
    (hc : ∀ i, Continuous (c i))
    {w : E} (hwS : w ∈ S) (hw : score w ≠ 0) :
    ∃ y ∈ S,
      score y ≠ 0 ∧
      (∀ z : E, z ∈ S → score z ^ 2 ≤ score y ^ 2) ∧
      (∀ (k : Fin n) (z : E), z ∈ S →
        score z ^ 2 = score y ^ 2 →
        (∀ j : Fin n, j < k → c j z = c j y) →
        c k y ≤ c k z) := by
  have hsq : Continuous (fun x => score x ^ 2) := hscore.pow 2
  obtain ⟨y, hyS, hymax, hylex⟩ :=
    exists_lexMinOn_maximizers
      S hS ⟨w, hwS⟩ (fun x => score x ^ 2) hsq n c hc
  refine ⟨y, hyS, ?_, hymax, hylex⟩
  intro hy
  have hle := hymax w hwS
  rw [hy] at hle
  have hwzero : score w = 0 := by
    nlinarith [sq_nonneg (score w)]
  exact hw hwzero

end GateGLexSelection
end Math
